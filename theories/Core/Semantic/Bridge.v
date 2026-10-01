(** * From the Syntactic Readings of Globals and Parameters to Evaluation

    The typing judgments read a global or a parameter through module
    substitutions ([gc_lookup], [wf_param]); evaluation reads the raw entry
    where it was checked.  This file relates the two, independently of any
    semantic model: the evaluation of the substituted term at the top level is
    simulated ([Simulation]) by the evaluation of the raw one at the place it
    stands for. *)

From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Semantic Require Import Evaluation Readback Simulation.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Weakening, module substitution and substitution as one replacement *)

Definition ts_of (φ : wk) (μ : msub) (σ : sub) : tsub :=
  ts_mk (fun x => σ (φ x)) (fun lp => (ms_param μ lp)[σ]) (fun p => (ms_glob μ p)[σ]).

Lemma ts_of_q : forall φ μ σ, ts_eq (ts_of (wk_q φ) (ms_q μ) (q σ)) (ts_q (ts_of φ μ σ)).
Proof.
  intros; repeat split; intros; cbn.
  - destruct x; reflexivity.
  - rewrite exp_wk_shift_sub_q; reflexivity.
  - rewrite exp_wk_shift_sub_q; reflexivity.
Qed.

Lemma ts_eq_trans : forall θ1 θ2 θ3, ts_eq θ1 θ2 -> ts_eq θ2 θ3 -> ts_eq θ1 θ3.
Proof. intros * (A1 & A2 & A3) (B1 & B2 & B3); repeat split; intros; congruence. Qed.

Lemma exp_tsub_of : forall M φ μ σ, M[φ]ʷ[μ]ᵐ[σ] = exp_tsub (ts_of φ μ σ) M.
Proof.
  induction M; intros; cbn; try reflexivity; f_equal; eauto.
  all: try (rewrite IHM2; apply exp_tsub_ext, ts_of_q).
  all: try (rewrite IHM1; apply exp_tsub_ext, ts_of_q).
  all: try (rewrite IHM3; apply exp_tsub_ext;
            eapply ts_eq_trans; [ apply ts_of_q | apply ts_q_eq, ts_of_q ]).
Qed.

Corollary exp_tsub_of_msub : forall M μ, M[μ]ᵐ = exp_tsub (ts_of wk_id μ Id) M.
Proof.
  intros; rewrite <- exp_tsub_of, exp_wk_id, exp_sub_id; reflexivity.
Qed.

(** ** Scoping *)

Lemma exp_scoped_ok : forall M n cs, exp_scoped n cs M -> exp_ok n (fun _ => True) (fun _ => True) M.
Proof. induction M; intros; cbn in *; intuition eauto. Qed.

(** ** Telescopes *)

Lemma ctx_lookup_nth : forall Γ k T, Γ ∋ #k : T ->
    exists A, List.nth_error Γ k = Some A /\ T = A[wk_shiftn (S k)]ʷ.
Proof.
  induction 1.
  - eexists; split; [ reflexivity |]; apply exp_wk_wk_eq; intros x; cbn; lia.
  - destruct IHctx_lookup as (A0 & HA0 & ->); exists A0; split; [ assumption |].
    rewrite exp_wk_wk; apply exp_wk_wk_eq; intros x; cbn; lia.
Qed.

Lemma ctx_lookup_det : forall Γ k T T', Γ ∋ #k : T -> Γ ∋ #k : T' -> T = T'.
Proof.
  intros * H H'; destruct (ctx_lookup_nth _ _ _ H) as (A & HA & ->), (ctx_lookup_nth _ _ _ H') as (A' & HA' & ->).
  rewrite HA in HA'; injection HA' as <-; reflexivity.
Qed.

Lemma skipn_nth : forall (Γ : ctx) k A, List.nth_error Γ k = Some A ->
    List.skipn k Γ = A :: List.skipn (S k) Γ.
Proof.
  induction Γ as [| B Γ IH]; intros [| k] A H; cbn in *; try discriminate.
  - injection H as ->; reflexivity.
  - apply IH; assumption.
Qed.

Lemma env_var_skipn : forall (ρ : env) x v ρ', List.skipn x ρ = v :: ρ' -> ρ x = v.
Proof.
  induction ρ as [| d ρ IH]; intros [| x] * H; cbn in *; try discriminate.
  - injection H as -> ->; reflexivity.
  - eapply IH; eassumption.
Qed.

Lemma ctx_scoped_nth : forall Γ cs k A, ctx_scoped 0 cs Γ -> List.nth_error Γ k = Some A ->
    exp_scoped (List.length Γ - S k) cs A.
Proof.
  induction Γ as [| B Γ IH]; intros cs [| k] A Hsc HA; cbn in *; try discriminate; destruct Hsc as [HB HΓ].
  - injection HA as ->; rewrite Nat.add_0_r in HB; rewrite Nat.sub_0_r; exact HB.
  - apply IH; assumption.
Qed.

Section Raw.
  Variables (Θ : gdeps) (Ξ : gstack).

  Lemma eval_ptele_skipn : forall κ j c Γ ρ,
      eval_ptele Θ Ξ κ j c Γ ρ -> forall x, eval_ptele Θ Ξ κ j c (List.skipn x Γ) (List.skipn x ρ).
  Proof.
    induction 1; intros [| x]; cbn; try constructor; auto; econstructor; eassumption.
  Qed.

  (** *** Parameters of open frames

      [T[↑ₘ (S n)]ᵐ[sb_params n]], the type [wf_param] gives [$[n, k]] with [T]
      the [k]-th binding of frame [n]'s telescope weakened past the ones after
      it, is the raw binding with its variables read as the frame's
      parameters and everything else moved [S n] frames out. *)
  Definition θp (n k : nat) : tsub :=
    ts_mk (fun x => $[n, x + S k]) (fun lp => $[S n + lp_mod lp, lp_param lp])
          (fun p => a_glob p[p_rel (S n) nil]ᵖ).

  Lemma param_type_tsub : forall n k A,
      A[wk_shiftn (S k)]ʷ[↑ₘ (S n)]ᵐ[sb_params n] = exp_tsub (θp n k) A.
  Proof.
    intros; rewrite exp_tsub_of; apply exp_tsub_ext; repeat split; intros; reflexivity.
  Qed.

  Lemma path_open_rel_nil : forall j m ip, (p_rel m ip)[p_rel j nil]ᵖ = p_rel (j + m) ip.
  Proof. intros; cbn; rewrite ?Nat.sub_0_r, ?List.firstn_nil; reflexivity. Qed.

  Lemma path_open_abs_nil : forall j fp ip, (p_abs fp ip)[p_rel j nil]ᵖ = p_abs fp ip.
  Proof. reflexivity. Qed.

  (** The configuration of a parameter's type: at the top level on the left,
      where its variables are the frame's parameters, and on the right in the
      environment of those parameters' values, where the frame was checked. *)
  Lemma ptele_cfg : forall n U k ρ,
      List.nth_error Ξ n = Some U ->
      eval_ptele Θ Ξ (me_base (S n)) n (List.length (gu_params U)) (List.skipn (S k) (gu_params U)) ρ ->
      cfg Θ Ξ (θp n k) (List.length (gu_params U) - S k) (fun _ => True) (fun _ => True)
        me_top nil (me_base (S n)) ρ.
  Proof.
    intros * Hn Hρ; constructor; cbn; auto.
    - intros x v Hx Hev; inversion Hev; subst; cbn [lp_mod lp_param] in *;
        rewrite me_drop_base in *; [ discriminate |].
      match goal with H : me_base _ = me_base _ |- _ => injection H as <- end.
      rewrite Nat.add_0_r in *.
      match goal with H : List.nth_error Ξ n = Some _ |- _ => rewrite Hn in H; injection H as <- end.
      pose proof (eval_ptele_skipn _ _ _ _ _ Hρ x) as Hx'.
      rewrite List.skipn_skipn in Hx'.
      match goal with H : eval_ptele _ _ _ _ _ (List.skipn (x + S k) _) (_ :: _) |- _ =>
        pose proof (functional_eval_ptele _ _ _ _ _ _ H Hx') as Heq end.
      replace (ρ x) with v by (symmetry; eapply env_var_skipn; symmetry; exact Heq).
      apply vs_refl.
    - intros [m k0] v _ Hev; inversion Hev; subst; cbn [lp_mod lp_param] in *;
        rewrite me_drop_base in *; [ discriminate |].
      match goal with H : me_base _ = me_base _ |- _ => injection H as <- end.
      eexists; split; [| apply vs_refl ].
      assert (Hd : me_drop m (me_base (S n)) = me_base (S (n + m + 0))) by (rewrite me_drop_base; f_equal; lia).
      eapply eval_exp_param_open; [ exact Hd | eassumption | eassumption ].
    - intros [[fp | m] ip] _; (eapply gl_struct; [ reflexivity |]).
      + rewrite path_open_abs_nil; apply st_abs.
      + rewrite path_open_rel_nil; apply st_rel.
        rewrite !me_drop_base; replace (m + S n) with (S n + m + 0) by lia; apply mesim_refl.
  Qed.

  (** The telescope of an open frame evaluates, as far as the types of its
      parameters do at the top level. *)
  Lemma ptele_exists : forall n U cs,
      List.nth_error Ξ n = Some U ->
      ctx_scoped 0 cs (gu_params U) ->
      forall m k, k + m = List.length (gu_params U) ->
      (forall k' A, k <= k' -> List.nth_error (gu_params U) k' = Some A ->
         exists t, eval_exp Θ Ξ me_top (exp_tsub (θp n k') A) nil t) ->
      exists ρ, eval_ptele Θ Ξ (me_base (S n)) n (List.length (gu_params U)) (List.skipn k (gu_params U)) ρ.
  Proof.
    intros * Hn Hsc; induction m as [| m IH]; intros k Hkm Hall.
    - exists nil; rewrite List.skipn_all2 by lia; constructor.
    - assert (Hk : k < List.length (gu_params U)) by lia.
      destruct (List.nth_error (gu_params U) k) as [A |] eqn:HA;
        [| apply List.nth_error_None in HA; lia ].
      destruct (IH (S k) ltac:(lia) ltac:(intros; apply Hall; [ lia | assumption ])) as [ρ Hρ].
      destruct (Hall k A ltac:(lia) HA) as [t Ht].
      assert (HsA : exp_scoped (List.length (gu_params U) - S k) cs A).
      { eapply ctx_scoped_nth; eassumption. }
      destruct (sim_eval_exp _ _ _ _ _ _ _ _ _ _ _ _ Ht (exp_scoped_ok _ _ _ HsA) (ptele_cfg _ _ _ _ Hn Hρ))
        as (a & Ha & _).
      eexists; rewrite (skipn_nth _ _ _ HA); econstructor; eassumption.
  Qed.

  (** The value of the parameter, and its type against the one at the top
      level. *)
  Lemma param_value : forall n U k A ρ t,
      List.nth_error Ξ n = Some U ->
      List.nth_error (gu_params U) k = Some A ->
      exp_ok (List.length (gu_params U) - S k) (fun _ => True) (fun _ => True) A ->
      eval_ptele Θ Ξ (me_base (S n)) n (List.length (gu_params U)) (List.skipn k (gu_params U)) ρ ->
      eval_exp Θ Ξ me_top (exp_tsub (θp n k) A) nil t ->
      exists a, eval_exp Θ Ξ me_top $[n, k] nil (⇑ a (d_param (lp_mk n k))) /\ vsim Θ Ξ t a.
  Proof.
    intros * Hn HA Hok Hρ Ht.
    rewrite (skipn_nth _ _ _ HA) in Hρ.
    remember (List.skipn (S k) (gu_params U)) as Γ' eqn:HΓ'.
    inversion Hρ as [| ? ? ? Γ ρ' T a Hρ' Ha]; subst Γ T ρ.
    rewrite HΓ' in Hρ'.
    destruct (sim_eval_exp _ _ _ _ _ _ _ _ _ _ _ _ Ht Hok (ptele_cfg _ _ _ _ Hn Hρ')) as (a' & Ha' & Hs).
    pose proof (functional_eval_exp _ _ _ _ _ Ha Ha') as <-.
    exists a; split; [| exact Hs ].
    assert (Hidx : List.length (gu_params U) - S (List.length Γ') = k).
    { rewrite HΓ', List.length_skipn.
      assert (k < List.length (gu_params U)) by (apply List.nth_error_Some; congruence); lia. }
    rewrite Hidx in Hρ.
    eapply eval_exp_param_open with (j := n); [ cbn [lp_mod]; rewrite me_drop_base, Nat.add_0_r; reflexivity | eassumption |].
    cbn [lp_param]; rewrite (skipn_nth _ _ _ HA), <- HΓ'; exact Hρ.
  Qed.
End Raw.
