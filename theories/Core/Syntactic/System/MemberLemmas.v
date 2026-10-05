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

(** A self slot under the operations: the body it holds is moved, under
    no binder of its own. *)
Lemma self_ent_wk : forall Φ φ, centry_wk (self_ent Φ) φ = self_ent (gmod_wk Φ φ).
Proof. reflexivity. Qed.

Lemma self_ent_sub : forall Φ σ, centry_sub (self_ent Φ) σ = self_ent (gmod_sub Φ σ).
Proof. reflexivity. Qed.

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
  | me_unit _ | me_var _ | me_lit _ => True
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

Lemma me_mems_app : forall pre1 pre2 H, me_mems H (pre1 ++ pre2) = me_mems (me_mems H pre1) pre2.
Proof. induction pre1; intros; cbn; auto. Qed.



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

Lemma self_ent_scoped : forall Φ n, gmod_scoped n Φ -> ce_scoped n (self_ent Φ).
Proof. intros; cbn; rewrite gunit_scoped_mk; cbn; auto. Qed.

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

(** ** Arities

    [tele_view] is read on the reversed telescope; these lemmas move the
    operations through the reversal, an entry at a time from the outside. *)

Lemma ctx_pi_app : forall T Δ A, ctx_pi (T ++ Δ) A = ctx_pi Δ (ctx_pi T A).
Proof. induction T as [| [] T IH]; intros; cbn; auto. Qed.

Lemma ctx_pi_rev_cons : forall e R A,
    ctx_pi (rev (e :: R)) A =
    match e with
    | ce_ass B => a_pi B (ctx_pi (rev R) A)
    | ce_def B N => a_let (b_def (Some B) N) (ctx_pi (rev R) A)
    | ce_mod U => a_let (b_mod U) (ctx_pi (rev R) A)
    end.
Proof. intros; cbn [rev]; rewrite ctx_pi_app; destruct e; reflexivity. Qed.

(** The [Π] the arity type of a telescope is, is its outermost parameter. *)
Lemma tele_view_pi : forall T,
    pi_view (ctx_pi T a_True) = option_map (fun BT => (fst BT, ctx_pi (snd BT) a_True)) (tele_view T).
Proof.
  intros T; unfold tele_view; rewrite <- (rev_involutive T) at 1; generalize (rev T) as R; clear T.
  induction R as [| [B | B N | U] R IH]; [ reflexivity | | |]; rewrite ctx_pi_rev_cons; cbn [pi_view tele_open].
  - reflexivity.
  - rewrite IH; destruct (tele_open R) as [[B' T'] |]; cbn; [ rewrite ctx_pi_sub; reflexivity | reflexivity ].
  - rewrite IH; destruct (tele_open R) as [[B' T'] |]; cbn; [ rewrite ctx_pi_sub; reflexivity | reflexivity ].
Qed.

Lemma tele_wk_rev_cons : forall e R φ,
    tele_wk (rev (e :: R)) φ = rev (centry_wk e φ :: rev (tele_wk (rev R) (wk_q φ))).
Proof.
  intros; cbn [rev]; rewrite tele_wk_app, rev_involutive; cbn; reflexivity.
Qed.

Lemma tele_sub_rev_cons : forall e R σ,
    tele_sub (rev (e :: R)) σ = rev (centry_sub e σ :: rev (tele_sub (rev R) (q σ))).
Proof.
  intros; cbn [rev]; rewrite tele_sub_app, rev_involutive; cbn; reflexivity.
Qed.

Lemma tele_view_wk : forall T φ,
    tele_view (tele_wk T φ) = option_map (fun BT => ((fst BT)[φ]ʷ, tele_wk (snd BT) (wk_q φ))) (tele_view T).
Proof.
  intros T; unfold tele_view; rewrite <- (rev_involutive T); generalize (rev T) as R; clear T.
  induction R as [| [B | B N | U] R IH]; intros φ; [ reflexivity | | |];
    rewrite tele_wk_rev_cons, !rev_involutive; cbn [centry_wk tele_open].
  - rewrite rev_involutive; reflexivity.
  - specialize (IH (wk_q φ)); rewrite rev_involutive in IH; rewrite IH.
    destruct (tele_open R) as [[B' T'] |]; cbn; [| reflexivity ].
    f_equal; f_equal.
    + symmetry; apply exp_wk_sub_extend.
    + rewrite tele_wk_sub, <- tele_sub_of_wk, tele_sub_sub; apply tele_sub_sb_eq.
      intros [| [| x]]; reduce_index; try reflexivity.
      cbn; f_equal; symmetry; apply exp_wk_shift_wk_q.
  - specialize (IH (wk_q φ)); rewrite rev_involutive in IH; rewrite IH.
    destruct (tele_open R) as [[B' T'] |]; cbn; [| reflexivity ].
    f_equal; f_equal.
    + rewrite exp_wk_sub, exp_sub_wk; apply exp_sub_sb_eq; intros [| x]; reduce_index; reflexivity.
    + rewrite tele_wk_sub, <- tele_sub_of_wk, tele_sub_sub; apply tele_sub_sb_eq.
      intros [| [| x]]; reduce_index; try reflexivity.
      cbn; f_equal; f_equal; symmetry; apply gunit_wk_shift_wk_q.
Qed.

Lemma tele_view_sub : forall T σ,
    tele_view (tele_sub T σ) = option_map (fun BT => ((fst BT)[σ], tele_sub (snd BT) (q σ))) (tele_view T).
Proof.
  intros T; unfold tele_view; rewrite <- (rev_involutive T); generalize (rev T) as R; clear T.
  induction R as [| [B | B N | U] R IH]; intros σ; [ reflexivity | | |];
    rewrite tele_sub_rev_cons, !rev_involutive; cbn [centry_sub tele_open].
  - rewrite rev_involutive; reflexivity.
  - specialize (IH (q σ)); rewrite rev_involutive in IH; rewrite IH.
    destruct (tele_open R) as [[B' T'] |]; cbn; [| reflexivity ].
    f_equal; f_equal; rewrite ?exp_sub_sub, ?tele_sub_sub; [ apply exp_sub_sb_eq | apply tele_sub_sb_eq ].
    + intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
    + rewrite !sb_q_compose; apply sb_q_cong.
      intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
  - specialize (IH (q σ)); rewrite rev_involutive in IH; rewrite IH.
    destruct (tele_open R) as [[B' T'] |]; cbn; [| reflexivity ].
    f_equal; f_equal; rewrite ?exp_sub_sub, ?tele_sub_sub; [ apply exp_sub_sb_eq | apply tele_sub_sb_eq ].
    + intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
    + rewrite !sb_q_compose; apply sb_q_cong.
      intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
Qed.

Lemma ctx_scoped_rev_cons : forall e R n,
    ctx_scoped n (rev (e :: R)) <-> ce_scoped n e /\ ctx_scoped (S n) (rev R).
Proof. intros; cbn [rev]; rewrite ctx_scoped_app; cbn; tauto. Qed.

Lemma tele_view_scoped : forall T B T' n,
    tele_view T = Some (B, T') -> ctx_scoped n T -> exp_scoped n B /\ ctx_scoped (S n) T'.
Proof.
  intros T; unfold tele_view; rewrite <- (rev_involutive T); generalize (rev T) as R; clear T.
  intros R; rewrite rev_involutive; induction R as [| [B0 | B0 N | U] R IH]; intros * Hv HT; cbn [tele_open] in Hv; [ discriminate | | |];
    apply ctx_scoped_rev_cons in HT as [He HR]; cbn in He; destruct_all.
  - injection Hv as <- <-; auto.
  - destruct (tele_open R) as [[B' T0] |] eqn:E; [| discriminate ]; injection Hv as <- <-.
    destruct (IH _ _ _ eq_refl HR) as [HB HT0]; split.
    + apply exp_scoped_sub1; assumption.
    + eapply tele_sub_scoped; [ eassumption |].
      apply sb_q_bound; intros [| x] ?; cbn; auto; lia.
  - destruct (tele_open R) as [[B' T0] |] eqn:E; [| discriminate ]; injection Hv as <- <-.
    destruct (IH _ _ _ eq_refl HR) as [HB HT0]; split.
    + apply exp_scoped_sub1_mod; cbn; assumption.
    + eapply tele_sub_scoped; [ eassumption |].
      apply sb_q_bound; intros [| x] ?; cbn; auto; lia.
Qed.

(** *** Member Types *)

Definition mres_scoped (n : nat) (R : mres) : Prop :=
  match R with
  | mr_term A => exp_scoped n A
  | mr_mod T => ctx_scoped n T
  end.

Lemma mres_ty_scoped : forall R n, mres_scoped n R -> exp_scoped n (mres_ty R).
Proof. intros [A | T] n H; cbn in *; [ exact H | apply ctx_pi_scoped; [ exact H | exact I ] ]. Qed.

Lemma mres_gen_scoped : forall Δ R n,
    ctx_scoped n Δ -> mres_scoped (length Δ + n) R -> mres_scoped n (mres_gen Δ R).
Proof.
  intros Δ [A | T] n HΔ HR; cbn in *; [ apply ctx_pi_scoped; assumption | apply ctx_scoped_app; auto ].
Qed.

Lemma mres_app_scoped : forall R N R' n,
    mres_app R N = Some R' -> mres_scoped n R -> exp_scoped n N -> mres_scoped n R'.
Proof.
  intros [A | T] * Ha HR HN; cbn in *.
  - destruct (pi_view A) as [[B C] |] eqn:E; [| discriminate ]; injection Ha as <-; cbn.
    destruct (pi_view_scoped _ _ _ _ E HR) as [_ HC]; apply exp_scoped_sub1; assumption.
  - unfold tele_inst in Ha; destruct (tele_view T) as [[B T'] |] eqn:E; [| discriminate ]; injection Ha as <-; cbn.
    destruct (tele_view_scoped _ _ _ _ E HR) as [_ HT']; eapply tele_sub_scoped; [ eassumption |].
    intros [| x] ?; cbn; auto; lia.
Qed.

Lemma mres_closed_wk : forall R φ, mres_scoped 0 R -> mres_wk R φ = R.
Proof. intros [A | T] φ H; cbn in *; [ rewrite exp_closed_wk | rewrite tele_closed_wk ]; auto. Qed.

Lemma mres_closed_sub : forall R σ, mres_scoped 0 R -> mres_sub R σ = R.
Proof. intros [A | T] σ H; cbn in *; [ rewrite exp_closed_sub | rewrite tele_closed_sub ]; auto. Qed.

Lemma mres_kind_gen : forall Δ R, mres_kind (mres_gen Δ R) = mres_kind R.
Proof. intros Δ []; reflexivity. Qed.

Lemma mres_kind_wk : forall R φ, mres_kind (mres_wk R φ) = mres_kind R.
Proof. intros []; reflexivity. Qed.

Lemma mres_kind_sub : forall R σ, mres_kind (mres_sub R σ) = mres_kind R.
Proof. intros []; reflexivity. Qed.

Lemma mres_ty_gen : forall Δ R, mres_ty (mres_gen Δ R) = ctx_pi Δ (mres_ty R).
Proof. intros Δ [A | T]; cbn; [ reflexivity | apply ctx_pi_app ]. Qed.

Lemma mres_ty_wk : forall R φ, mres_ty (mres_wk R φ) = (mres_ty R)[φ]ʷ.
Proof. intros [A | T] φ; cbn; [ reflexivity | rewrite ctx_pi_wk; reflexivity ]. Qed.

Lemma mres_ty_sub : forall R σ, mres_ty (mres_sub R σ) = (mres_ty R)[σ].
Proof. intros [A | T] σ; cbn; [ reflexivity | rewrite ctx_pi_sub; reflexivity ]. Qed.

Lemma mres_gen_wk : forall Δ R φ,
    mres_wk (mres_gen Δ R) φ = mres_gen (tele_wk Δ φ) (mres_wk R (wk_qn (length Δ) φ)).
Proof. intros Δ [A | T] φ; cbn; [ rewrite ctx_pi_wk | rewrite tele_wk_app ]; reflexivity. Qed.

Lemma mres_gen_sub : forall Δ R σ,
    mres_sub (mres_gen Δ R) σ = mres_gen (tele_sub Δ σ) (mres_sub R (sb_qn (length Δ) σ)).
Proof. intros Δ [A | T] σ; cbn; [ rewrite ctx_pi_sub | rewrite tele_sub_app ]; reflexivity. Qed.

Lemma mres_gen_app : forall Ψ Δ R, mres_gen (Ψ ++ Δ) R = mres_gen Δ (mres_gen Ψ R).
Proof. intros Ψ Δ [A | T]; cbn; [ rewrite ctx_pi_app | rewrite app_assoc ]; reflexivity. Qed.

Lemma mres_gen_nil : forall R, mres_gen nil R = R.
Proof. intros [A | T]; cbn; [| rewrite app_nil_r ]; reflexivity. Qed.

(** Applying a member type is applying its type. *)
Lemma mres_app_ty : forall R N R', mres_app R N = Some R' ->
    exists B C, pi_view (mres_ty R) = Some (B, C) /\ mres_ty R' = C[Id,,N] /\ mres_kind R' = mres_kind R.
Proof.
  intros [A | T] * Ha; cbn in *.
  - destruct (pi_view A) as [[B C] |] eqn:E; [| discriminate ]; injection Ha as <-; eauto.
  - unfold tele_inst in Ha; destruct (tele_view T) as [[B T'] |] eqn:E; [| discriminate ]; injection Ha as <-.
    exists B, (ctx_pi T' a_True); rewrite tele_view_pi, E; cbn.
    rewrite ctx_pi_sub; auto.
Qed.

Lemma mres_app_of_pi : forall R N B C, pi_view (mres_ty R) = Some (B, C) ->
    exists R', mres_app R N = Some R'.
Proof.
  intros [A | T] * Hp; cbn in *.
  - rewrite Hp; eauto.
  - rewrite tele_view_pi in Hp; unfold tele_inst.
    destruct (tele_view T) as [[B0 T0] |]; cbn in *; [ eauto | discriminate ].
Qed.

Lemma mres_app_wk : forall R N R' φ, mres_app R N = Some R' ->
    mres_app (mres_wk R φ) N[φ]ʷ = Some (mres_wk R' φ).
Proof.
  intros [A | T] * Ha; cbn in *.
  - destruct (pi_view A) as [[B C] |] eqn:E; [| discriminate ]; injection Ha as <-.
    rewrite (pi_view_wk _ _ _ _ E); cbn; rewrite exp_wk_sub_extend; reflexivity.
  - unfold tele_inst in *; rewrite tele_view_wk.
    destruct (tele_view T) as [[B T'] |] eqn:E; [| discriminate ]; injection Ha as <-; cbn.
    f_equal; f_equal.
    rewrite tele_wk_sub, <- tele_sub_of_wk, tele_sub_sub; apply tele_sub_sb_eq.
    intros [| x]; reduce_index; reflexivity.
Qed.

Lemma mres_app_sub : forall R N R' σ, mres_app R N = Some R' ->
    mres_app (mres_sub R σ) N[σ] = Some (mres_sub R' σ).
Proof.
  intros [A | T] * Ha; cbn in *.
  - destruct (pi_view A) as [[B C] |] eqn:E; [| discriminate ]; injection Ha as <-.
    rewrite (pi_view_sub _ _ _ _ E); cbn; rewrite exp_sub_extend_comm; reflexivity.
  - unfold tele_inst in *; rewrite tele_view_sub.
    destruct (tele_view T) as [[B T'] |] eqn:E; [| discriminate ]; injection Ha as <-; cbn.
    f_equal; f_equal.
    rewrite !tele_sub_sub; apply tele_sub_sb_eq.
    intros [| x]; reduce_index; [ reflexivity |].
    rewrite sentry_sub_shift_extend; apply sentry_sub_id.
Qed.

Lemma ctx_scoped_closed : forall T n, ctx_scoped 0 T -> ctx_scoped n T.
Proof.
  intros * HT; rewrite <- (tele_closed_wk T (fun x => x) HT).
  eapply tele_wk_scoped; [ exact HT | lia ].
Qed.

Lemma mres_scoped_closed : forall R n, mres_scoped 0 R -> mres_scoped n R.
Proof.
  intros [A | T] n H; cbn in *; [ eapply exp_scoped_mono; [| exact H ]; lia | apply ctx_scoped_closed; exact H ].
Qed.


Lemma member_type_scoped : forall Θ,
    gctx_closed Θ ->
    (forall Γ H ch R, member_type Θ Γ H ch R ->
       ctx_scoped 0 Γ -> modexp_scoped (length Γ) H -> mres_scoped (length Γ) R) /\
    (forall Γ U ch R, unit_member_type Θ Γ U ch R ->
       ctx_scoped 0 Γ -> gunit_scoped (length Γ) U -> mres_scoped (length Γ) R).
Proof.
  intros Θ Hc; apply member_type_both_ind; intros; cbn [mres_scoped modexp_scoped length] in *.
  - apply mres_scoped_closed; match goal with IH : _ -> _ -> mres_scoped 0 _ |- _ => apply IH end;
      [ exact I | eapply gctx_closed_unit_lookup; eassumption ].
  - match goal with IH : _ -> gunit_scoped _ ?U -> _, Hl : _ ∋ # _ ⇒ₘ ?U, HΓ : ctx_scoped 0 _ |- _ =>
      apply IH; [ assumption |]; pose proof (ctx_scoped_lookup_mod _ _ _ _ HΓ Hl) as HU; rewrite Nat.add_0_r in HU; exact HU end.
  - auto.
  - match goal with IH : _ -> _ -> _ |- _ => apply IH; assumption end.
  - cbn in *; destruct_all; eapply mres_app_scoped; [ eassumption | | assumption ].
    match goal with IH : _ -> _ -> _ |- _ => apply IH; assumption end.
  - rewrite gunit_scoped_mk in *; destruct_all; assumption.
  - rewrite gunit_scoped_mk in *; destruct_all; cbn in *.
    match goal with Hp : gm_prefix_upto _ _ = _, HΦ : gmod_scoped _ ?Φ |- _ => pose proof (gm_prefix_upto_scoped _ _ _ _ Hp HΦ) as HΦ' end; cbn in HΦ'; destruct_all.
    apply ctx_pi_scoped; [ assumption | cbn; split; [ exact (self_ent_scoped _ _ H2) | assumption ] ].
  - rewrite gunit_scoped_mk in *; destruct_all; cbn in *.
    match goal with Hp : gm_prefix_upto _ _ = _, HΦ : gmod_scoped _ ?Φ |- _ => pose proof (gm_prefix_upto_scoped _ _ _ _ Hp HΦ) as HΦ' end; cbn in HΦ'; destruct_all.
    apply mres_gen_scoped; [ cbn; split; [ apply self_ent_scoped; assumption | assumption ] |].
    cbn [length]; replace (S (length Δ) + length Γ) with (length (self_ent Φ' :: Δ ++ Γ)) by (cbn; rewrite length_app; lia).
    match goal with IH : _ -> _ -> mres_scoped _ ?R |- mres_scoped _ ?R => apply IH end.
    + cbn; split; [ rewrite length_app, Nat.add_0_r; apply self_ent_scoped; assumption | apply ctx_scoped_app_iff; split; assumption ].
    + cbn; rewrite length_app; assumption.
  - rewrite gunit_scoped_mk in *; destruct_all; cbn in *.
    apply mres_gen_scoped; [ assumption |].
    rewrite <- length_app; match goal with IH : _ -> _ -> mres_scoped _ ?R |- mres_scoped _ ?R => apply IH end;
      [ apply ctx_scoped_app_iff; split; assumption | rewrite length_app; assumption ].
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
    gm_prefix_upto (gmod_wk Φ φ) x = Some (gm_ext (gmod_wk Φ' φ) x (gentry_wk E (wk_q φ))).
Proof. intros * H; rewrite gm_prefix_upto_wk, H; reflexivity. Qed.

(** The self telescope of an entry after a weakening of its unit. *)
Lemma tele_wk_self : forall Φ' Δ φ,
    tele_wk (self_ent Φ' :: Δ) φ = self_ent (gmod_wk Φ' (wk_qn (length Δ) φ)) :: tele_wk Δ φ.
Proof. reflexivity. Qed.

Lemma member_type_wk : forall Θ,
    gctx_closed Θ ->
    (forall Δ H ch R, member_type Θ Δ H ch R ->
       forall Γ φ, wk_mod_compat φ Γ Δ -> member_type Θ Γ (modexp_wk H φ) ch (mres_wk R φ)) /\
    (forall Δ U ch R, unit_member_type Θ Δ U ch R ->
       forall Γ φ, wk_mod_compat φ Γ Δ -> unit_member_type Θ Γ (gunit_wk U φ) ch (mres_wk R φ)).
Proof.
  intros Θ Hc; apply member_type_both_ind; intros; cbn [modexp_wk].
  - pose proof (gctx_closed_unit_lookup _ _ _ Hc e) as HU.
    rewrite mres_closed_wk; [ eapply mt_unit; eassumption |].
    exact (proj2 (member_type_scoped Θ Hc) nil U ch R u I HU).
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; [ rewrite mres_kind_wk; assumption | eauto ].
  - econstructor; [ eauto | apply mres_app_wk; eassumption ].
  - rewrite gunit_wk_mk; cbn; constructor.
  - rewrite gunit_wk_mk; cbn [mres_wk moddef_wk]; rewrite ctx_pi_wk, tele_wk_self; cbn [length wk_qn].
    eapply umt_def; rewrite (gm_prefix_upto_ext_wk _ _ _ _ _ e); reflexivity.
  - rewrite gunit_wk_mk, mres_gen_wk, tele_wk_self; cbn [moddef_wk length wk_qn].
    eapply umt_mod; [ rewrite mres_kind_wk; assumption | rewrite (gm_prefix_upto_ext_wk _ _ _ _ _ e); reflexivity |].
    match goal with IH : forall _ _, _ -> _ |- _ => apply IH end.
    apply (wk_mod_compat_q _ _ _ (self_ent Φ')), wk_mod_compat_ext; assumption.
  - rewrite gunit_wk_mk, mres_gen_wk; cbn; constructor.
    match goal with IH : forall _ _, _ -> _ |- _ => apply IH end; apply wk_mod_compat_ext; assumption.
Qed.

Corollary member_type_wk_term : forall Θ, gctx_closed Θ ->
    forall Δ H ch A, member_type Θ Δ H ch (mr_term A) ->
    forall Γ φ, wk_mod_compat φ Γ Δ -> member_type Θ Γ (modexp_wk H φ) ch (mr_term A[φ]ʷ).
Proof. intros * Hc * Hm * Hφ; exact (proj1 (member_type_wk _ Hc) _ _ _ _ Hm _ _ Hφ). Qed.

Corollary member_type_wk_mod : forall Θ, gctx_closed Θ ->
    forall Δ H ch T, member_type Θ Δ H ch (mr_mod T) ->
    forall Γ φ, wk_mod_compat φ Γ Δ -> member_type Θ Γ (modexp_wk H φ) ch (mr_mod (tele_wk T φ)).
Proof. intros * Hc * Hm * Hφ; exact (proj1 (member_type_wk _ Hc) _ _ _ _ Hm _ _ Hφ). Qed.

Corollary tele_view_wk_some : forall T B T1 φ, tele_view T = Some (B, T1) ->
    tele_view (tele_wk T φ) = Some (B[φ]ʷ, tele_wk T1 (wk_q φ)).
Proof. intros * Hv; rewrite tele_view_wk, Hv; reflexivity. Qed.

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

Lemma gm_prefix_upto_ext_sub : forall Φ x Φ' E σ,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x E) ->
    gm_prefix_upto (gmod_sub Φ σ) x = Some (gm_ext (gmod_sub Φ' σ) x (gentry_sub E (q σ))).
Proof. intros * H; rewrite gm_prefix_upto_sub, H; reflexivity. Qed.

Lemma tele_sub_self : forall Φ' Δ σ,
    tele_sub (self_ent Φ' :: Δ) σ = self_ent (gmod_sub Φ' (sb_qn (length Δ) σ)) :: tele_sub Δ σ.
Proof. reflexivity. Qed.

Lemma member_type_sub : forall Θ,
    gctx_closed Θ ->
    (forall Δ H ch R, member_type Θ Δ H ch R ->
       forall Γ σ, sub_mod_compat σ Γ Δ -> member_type Θ Γ H[σ]ᵐ ch (mres_sub R σ)) /\
    (forall Δ U ch R, unit_member_type Θ Δ U ch R ->
       forall Γ σ, sub_mod_compat σ Γ Δ -> unit_member_type Θ Γ U[σ]ᵘ ch (mres_sub R σ)).
Proof.
  intros Θ Hc; apply member_type_both_ind; intros; cbn [modexp_sub].
  - pose proof (gctx_closed_unit_lookup _ _ _ Hc e) as HU.
    rewrite mres_closed_sub; [ eapply mt_unit; eassumption |].
    exact (proj2 (member_type_scoped Θ Hc) nil U ch R u I HU).
  - destruct (H0 _ _ c) as [-> | (y & -> & Hy)]; cbn [sentry_modexp].
    + eapply mt_lit; eauto.
    + eapply mt_var; eauto.
  - econstructor; eauto.
  - econstructor; [ rewrite mres_kind_sub; assumption | eauto ].
  - econstructor; [ eauto | apply mres_app_sub; eassumption ].
  - rewrite gunit_sub_mk; cbn; constructor.
  - rewrite gunit_sub_mk; cbn [mres_sub moddef_sub]; rewrite ctx_pi_sub, tele_sub_self; cbn [length sb_qn].
    eapply umt_def; rewrite (gm_prefix_upto_ext_sub _ _ _ _ _ e); reflexivity.
  - rewrite gunit_sub_mk, mres_gen_sub, tele_sub_self; cbn [moddef_sub length sb_qn].
    eapply umt_mod; [ rewrite mres_kind_sub; assumption | rewrite (gm_prefix_upto_ext_sub _ _ _ _ _ e); reflexivity |].
    match goal with IH : forall _ _, _ -> _ |- _ => apply IH end.
    apply (sub_mod_compat_q _ _ _ (self_ent Φ')), sub_mod_compat_ext; assumption.
  - rewrite gunit_sub_mk, mres_gen_sub; cbn; constructor.
    match goal with IH : forall _ _, _ -> _ |- _ => apply IH end; apply sub_mod_compat_ext; assumption.
Qed.

Corollary member_type_sub_term : forall Θ, gctx_closed Θ ->
    forall Δ H ch A, member_type Θ Δ H ch (mr_term A) ->
    forall Γ σ, sub_mod_compat σ Γ Δ -> member_type Θ Γ H[σ]ᵐ ch (mr_term A[σ]).
Proof. intros * Hc * Hm * Hσ; exact (proj1 (member_type_sub _ Hc) _ _ _ _ Hm _ _ Hσ). Qed.

Corollary member_type_sub_mod : forall Θ, gctx_closed Θ ->
    forall Δ H ch T, member_type Θ Δ H ch (mr_mod T) ->
    forall Γ σ, sub_mod_compat σ Γ Δ -> member_type Θ Γ H[σ]ᵐ ch (mr_mod (tele_sub T σ)).
Proof. intros * Hc * Hm * Hσ; exact (proj1 (member_type_sub _ Hc) _ _ _ _ Hm _ _ Hσ). Qed.

Corollary tele_view_sub_some : forall T B T1 σ, tele_view T = Some (B, T1) ->
    tele_view (tele_sub T σ) = Some (B[σ], tele_sub T1 (q σ)).
Proof. intros * Hv; rewrite tele_view_sub, Hv; reflexivity. Qed.

(** ** Expansions and δ-Reducts under the Operations *)

(** The three forms an expansion takes. *)
Lemma member_expansion_inv : forall U ch M,
    member_expansion U ch = Some M ->
    (exists Δ E, U = gu_mk Δ (md_alias E) /\ ch <> nil /\ M = ctx_fn Δ (member_ref E ch)) \/
    (exists Δ Φ x Φ' pv A M0, U = gu_body Δ Φ /\ ch = x :: nil /\
       gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def pv A (Some M0))) /\
       M = ctx_fn (self_ent Φ' :: Δ) M0) \/
    (exists Δ Φ y ch' Φ' pm Uy, U = gu_body Δ Φ /\ ch = y :: ch' /\ ch' <> nil /\
       gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) /\
       M = ctx_fn (self_ent Φ' :: Δ) (member_ref (me_lit Uy) ch')).
Proof.
  intros [Δ [Φ | E]] [| x ch'] M H; unfold member_expansion in H; try discriminate.
  - right.
    destruct (gm_prefix_upto Φ x) as [Φx |] eqn:Ex; [| discriminate ].
    destruct (gm_prefix_upto_ext _ _ _ Ex) as (Φ' & E & ->).
    destruct E as [pv A [M0 |] | pm Uy]; destruct ch' as [| z ch'']; try discriminate; injection H as <-.
    + left; do 7 eexists; repeat split; eassumption.
    + right; do 7 eexists; repeat split; try eassumption; discriminate.
  - left; injection H as <-; do 2 eexists; repeat split; discriminate.
Qed.

Lemma member_expansion_alias : forall Δ E ch,
    ch <> nil -> member_expansion (gu_mk Δ (md_alias E)) ch = Some (ctx_fn Δ (member_ref E ch)).
Proof. intros * Hch; destruct ch; [ contradiction | reflexivity ]. Qed.

Lemma member_expansion_def : forall Δ Φ x Φ' pv A M,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def pv A (Some M))) ->
    member_expansion (gu_body Δ Φ) (x :: nil) = Some (ctx_fn (self_ent Φ' :: Δ) M).
Proof. intros * H; unfold member_expansion; rewrite H; reflexivity. Qed.

Lemma member_expansion_mod : forall Δ Φ y ch' Φ' pm Uy,
    ch' <> nil ->
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
    member_expansion (gu_body Δ Φ) (y :: ch') =
    Some (ctx_fn (self_ent Φ' :: Δ) (member_ref (me_lit Uy) ch')).
Proof. intros * Hch H; unfold member_expansion; rewrite H; destruct ch'; [ contradiction | reflexivity ]. Qed.

Lemma member_expansion_wk : forall U ch M φ,
    member_expansion U ch = Some M ->
    member_expansion (gunit_wk U φ) ch = Some M[φ]ʷ.
Proof.
  intros * H; apply member_expansion_inv in H as
    [(Δ & E & -> & Hch & ->) | [(Δ & Φ & x & Φ' & pv & A & M0 & -> & -> & Hp & ->) | (Δ & Φ & y & ch' & Φ' & pm & Uy & -> & -> & Hch & Hp & ->)]];
    rewrite gunit_wk_mk; cbn [moddef_wk].
  - rewrite member_expansion_alias by assumption; rewrite ctx_fn_wk, member_ref_wk; reflexivity.
  - pose proof (gm_prefix_upto_ext_wk _ _ _ _ (wk_qn (length Δ) φ) Hp) as Hp'; cbn [gentry_wk] in Hp'.
    erewrite member_expansion_def by exact Hp'.
    rewrite ctx_fn_wk; reflexivity.
  - pose proof (gm_prefix_upto_ext_wk _ _ _ _ (wk_qn (length Δ) φ) Hp) as Hp'; cbn [gentry_wk] in Hp'.
    erewrite member_expansion_mod by first [ assumption | exact Hp' ].
    rewrite ctx_fn_wk, member_ref_wk; reflexivity.
Qed.

Lemma member_expansion_sub : forall U ch M σ,
    member_expansion U ch = Some M ->
    member_expansion U[σ]ᵘ ch = Some M[σ].
Proof.
  intros * H; apply member_expansion_inv in H as
    [(Δ & E & -> & Hch & ->) | [(Δ & Φ & x & Φ' & pv & A & M0 & -> & -> & Hp & ->) | (Δ & Φ & y & ch' & Φ' & pm & Uy & -> & -> & Hch & Hp & ->)]];
    rewrite gunit_sub_mk; cbn [moddef_sub].
  - rewrite member_expansion_alias by assumption; rewrite ctx_fn_sub, member_ref_sub; reflexivity.
  - pose proof (gm_prefix_upto_ext_sub _ _ _ _ (sb_qn (length Δ) σ) Hp) as Hp'; cbn [gentry_sub] in Hp'.
    erewrite member_expansion_def by exact Hp'.
    rewrite ctx_fn_sub; reflexivity.
  - pose proof (gm_prefix_upto_ext_sub _ _ _ _ (sb_qn (length Δ) σ) Hp) as Hp'; cbn [gentry_sub] in Hp'.
    erewrite member_expansion_mod by first [ assumption | exact Hp' ].
    rewrite ctx_fn_sub, member_ref_sub; reflexivity.
Qed.

Lemma member_ref_scoped : forall ch H n, modexp_scoped n H -> exp_scoped n (member_ref H ch).
Proof. induction ch as [| x [| y ch] IH]; intros; cbn; auto. apply IH; cbn; assumption. Qed.

Lemma member_expansion_scoped : forall U ch M n,
    member_expansion U ch = Some M -> gunit_scoped n U -> exp_scoped n M.
Proof.
  intros * H HU; apply member_expansion_inv in H as
    [(Δ & E & -> & Hch & ->) | [(Δ & Φ & x & Φ' & pv & A & M0 & -> & -> & Hp & ->) | (Δ & Φ & y & ch' & Φ' & pm & Uy & -> & -> & Hch & Hp & ->)]];
    rewrite gunit_scoped_mk in HU; destruct HU as [HΔ HD]; cbn in HD.
  - apply ctx_fn_scoped; [ assumption | apply member_ref_scoped; assumption ].
  - pose proof (gm_prefix_upto_scoped _ _ _ _ Hp HD) as HΦ; cbn in HΦ; destruct_all.
    apply ctx_fn_scoped; cbn; [ split; [ apply self_ent_scoped |]; assumption | assumption ].
  - pose proof (gm_prefix_upto_scoped _ _ _ _ Hp HD) as HΦ; cbn in HΦ; destruct_all.
    apply ctx_fn_scoped; cbn; [ split; [ apply self_ent_scoped |]; assumption |].
    apply member_ref_scoped; cbn; assumption.
Qed.

(** The δ-reduct of a chain from a unit is closed: the unit is. *)
Lemma member_unfold_unit_closed : forall Θ Γ fp ch M,
    gctx_closed Θ -> member_unfold_ch Θ Γ (me_unit fp) ch = Some M -> exp_scoped 0 M.
Proof.
  intros * Hc H; cbn in H.
  destruct (gc_unit Θ fp) as [U |] eqn:EU; [| discriminate ].
  eapply member_expansion_scoped; [ eassumption | eapply gctx_closed_unit_lookup; eassumption ].
Qed.

Lemma member_unfold_wk : forall Θ,
    gctx_closed Θ ->
    forall H Δ ch M Γ φ,
      wk_mod_compat φ Γ Δ ->
      member_unfold_ch Θ Δ H ch = Some M ->
      member_unfold_ch Θ Γ (modexp_wk H φ) ch = Some M[φ]ʷ.
Proof.
  intros Θ Hc; induction H as [fp | x | H IH y | H IH N | U]; intros * Hφ HM.
  - rewrite exp_closed_wk; [ cbn in *; exact HM |].
    eapply member_unfold_unit_closed; eassumption.
  - cbn in HM |- *.
    destruct (ctx_find_mod Δ x) as [U |] eqn:EU; [| discriminate ].
    apply ctx_find_mod_spec, Hφ, ctx_find_mod_spec in EU; rewrite EU.
    apply member_expansion_wk; assumption.
  - cbn in *; eauto.
  - cbn in *; destruct (member_unfold_ch Θ Δ H ch) as [M0 |] eqn:E0; [| discriminate ].
    injection HM as <-; erewrite IH by eassumption; reflexivity.
  - cbn in *; apply member_expansion_wk; assumption.
Qed.

Lemma member_unfold_sub : forall Θ,
    gctx_closed Θ ->
    forall H Δ ch M Γ σ,
      sub_mod_compat σ Γ Δ ->
      member_unfold_ch Θ Δ H ch = Some M ->
      member_unfold_ch Θ Γ H[σ]ᵐ ch = Some M[σ].
Proof.
  intros Θ Hc; induction H as [fp | x | H IH y | H IH N | U]; intros * Hσ HM.
  - rewrite exp_closed_sub; [ cbn in *; exact HM |].
    eapply member_unfold_unit_closed; eassumption.
  - cbn in HM |- *.
    destruct (ctx_find_mod Δ x) as [U |] eqn:EU; [| discriminate ].
    apply ctx_find_mod_spec in EU; destruct (Hσ _ _ EU) as [-> | (y & -> & Hy)]; cbn.
    + apply member_expansion_sub; assumption.
    + apply ctx_find_mod_spec in Hy; rewrite Hy; apply member_expansion_sub; assumption.
  - cbn in *; eauto.
  - cbn in *; destruct (member_unfold_ch Θ Δ H ch) as [M0 |] eqn:E0; [| discriminate ].
    injection HM as <-; erewrite IH by eassumption; reflexivity.
  - cbn in *; apply member_expansion_sub; assumption.
Qed.

(** ** Member Types as the Global Context Grows *)

Lemma member_type_gc_sub : forall Θ1 Θ2,
    Θ1 ⊑ Θ2 ->
    (forall Γ H ch R, member_type Θ1 Γ H ch R -> member_type Θ2 Γ H ch R) /\
    (forall Γ U ch R, unit_member_type Θ1 Γ U ch R -> unit_member_type Θ2 Γ U ch R).
Proof.
  intros * Hs; apply member_type_both_ind; intros; econstructor; eauto using gc_sub_unit.
Qed.

Lemma member_unfold_gc_sub : forall Θ1 Θ2,
    Θ1 ⊑ Θ2 ->
    forall H Γ ch M, member_unfold_ch Θ1 Γ H ch = Some M -> member_unfold_ch Θ2 Γ H ch = Some M.
Proof.
  intros * Hs; induction H as [fp | x | H IH y | H IH N | U]; intros * HM; cbn in *; auto.
  - destruct (gc_unit Θ1 fp) as [U |] eqn:Er; [| discriminate ].
    rewrite (gc_sub_unit _ _ _ _ Hs Er); exact HM.
  - destruct (member_unfold_ch Θ1 Γ H ch) eqn:E; [| discriminate ].
    rewrite (IH _ _ _ E); exact HM.
Qed.

(** ** Member Types Are Functional *)

Lemma member_type_functional : forall Θ,
    (forall Γ H ch R, member_type Θ Γ H ch R -> forall R', member_type Θ Γ H ch R' -> R = R') /\
    (forall Γ U ch R, unit_member_type Θ Γ U ch R -> forall R', unit_member_type Θ Γ U ch R' -> R = R').
Proof.
  intros Θ; apply member_type_both_ind.
  all: intros *; intros; match goal with H' : _ _ _ _ _ ?A' |- _ = ?A' => inversion H'; subst end;
    try congruence;
    try solve [ match goal with Hl : _ ∋ # _ ⇒ₘ _, Hl' : _ ∋ # _ ⇒ₘ _ |- _ =>
                  pose proof (ctx_lookup_mod_functional _ _ _ _ Hl Hl'); subst; eauto end ];
    eauto.
  - match goal with E1 : gc_unit _ ?p = _, E2 : gc_unit _ ?p = _ |- _ =>
      rewrite E1 in E2; injection E2; intros; subst end; eauto.
  - match goal with IH : forall R', member_type _ _ ?H _ R' -> _ = R', Hm : member_type _ _ ?H _ _ |- _ =>
      apply IH in Hm; subst end; congruence.
  - match goal with E1 : gm_prefix_upto _ _ = _, E2 : gm_prefix_upto _ _ = _ |- _ =>
      rewrite E1 in E2; injection E2; intros; subst end.
    f_equal; eauto.
  - f_equal; eauto.
Qed.
