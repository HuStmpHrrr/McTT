(** * A Declaration the Classifier Accepts Runs

    The commands a declaration generates ([ind_mod_cmds], [rec_cmds]) are
    definitions and modules of definitions, each of the type it is
    declared at where it runs: the constructors at the module's
    parameters ([con_gen_typed]), the recursor [X.rec] of a one-member
    group ([rec_typed]), and the functions of the recursor module [Rec]
    ([grec_fn_typed]).  Each is a term of a [Π] over a telescope applied
    to the telescope's variables ([wf_apps_vars]), under [λ]s over the
    recursor's telescope.  So a declaration that meets the premises
    [run_cmd_ind_case] checks before its members runs, whatever it generates
    ([run_cmd_ind_runs]). *)

From Stdlib Require Import Lia List PeanoNat.
From Stdlib Require Import String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import SystemOpt.
From Mctt.Core.Syntactic.System Require Import Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing Syntax.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas.
From Mctt.Core.Syntactic.System Require Import Command.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Applying to the Variables of a Telescope *)

Lemma wf_app_var0 : forall Θ Ξ Γ A B M i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Π A B ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M[↑]ʷ $ #0 : B.
Proof.
  intros.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A) by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ʷ ↑ : Γ) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ exp_wk M ↑ : exp_wk (Π A B) ↑) as H'
      by (eapply wk_preserves_exp; eassumption).
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M[↑]ʷ : Π A[↑]ʷ B[wk_q ↑]ʷ) by exact H'.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ A[↑]ʷ : Typeω@i) by (eapply wk_preserves_typ; eassumption).
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ #0 : A[↑]ʷ) by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ▹ A[↑]ʷ ⊢ B[wk_q ↑]ʷ : Typeω@i)
      by (eapply wk_preserves_typ; [ eassumption | eapply wf_wk_q'; eassumption ]).
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M[↑]ʷ $ #0 : B[wk_q ↑]ʷ[Id,,#0]) by (eapply wf_app; eassumption).
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B[wk_q ↑]ʷ[Id,,#0] ≈ B : Typeω@i).
  { rewrite <- (exp_wk_q_shift_single B) at 2.
    eapply (sub_eq_preserves_typ _ _ _ _ _ _ _ i); [ eassumption | eapply wf_sub_eq_var_zero; eassumption ]. }
  eapply wf_exp_subtyp'; [ eassumption |].
  eapply wf_subtyp_refl; [ eassumption | eassumption ].
Qed.

(** A term of a [Π] over a telescope, moved under it and applied to its
    variables, is of the [Π]'s body. *)
Lemma wf_apps_vars : forall Θ Ξ Δ Γ B M i,
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ B : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ctx_pi Δ B ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ apps M[wk_shiftn (List.length Δ)]ʷ (vars_from 0 (List.length Δ)) : B.
Proof.
  induction Δ as [| e Δ IH] using List.rev_ind; intros * Hass HΔ HB HM.
  - cbn in *; rewrite exp_wk_id_ext by (intros x; cbn; lia); exact HM.
  - unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A ->] _].
    rewrite ctx_pi_snoc in HM; rewrite <- List.app_assoc in HΔ, HB; cbn [List.app] in HΔ, HB.
    destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ [k HA]].
    destruct (ctx_pi_wf _ _ _ _ _ _ HΔ HB) as [j HPi].
    assert (H0 : Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M[↑]ʷ $ #0 : ctx_pi Δ B)
      by (eapply wf_app_var0 with (i := max k j);
          [ eapply lift_exp_max_left; exact HA | eapply lift_exp_max_right; exact HPi | exact HM ]).
    pose proof (IH _ _ _ _ Hass HΔ HB H0) as H.
    rewrite <- List.app_assoc; cbn [List.app].
    rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r, vars_from_S; cbn [apps_exp].
    replace (M[wk_shiftn (S (List.length Δ))]ʷ $ #(0 + List.length Δ))
      with ((M[↑]ʷ $ #0)[wk_shiftn (List.length Δ)]ʷ); [ exact H |].
    cbn [exp_wk]; f_equal; rewrite exp_wk_wk; apply exp_wk_wk_eq; intros x; cbn; lia.
Qed.

Lemma lookup_mid : forall E T Γ,
    E ++ ce_ass T :: Γ ∋ #(List.length E) : T[wk_shiftn (S (List.length E))]ʷ.
Proof.
  intros; pose proof (ctx_lookup_app_r E (ce_ass T :: Γ) 0 T[↑]ʷ ltac:(constructor)) as H.
  cbn [Nat.add] in H; rewrite exp_wk_wk in H.
  erewrite exp_wk_wk_eq; [ exact H |]; intros x; cbn; lia.
Qed.


Lemma rec_btys_app : forall p D M k cs1 cs2,
    rec_btys p D M k (cs1 ++ cs2) = rec_btys p D M k cs1 ++ rec_btys p D M (k + List.length cs1) cs2.
Proof.
  intros p D M k cs1; revert k; induction cs1 as [| [c gs] cs1 IH]; intros; cbn [List.app rec_btys List.length];
    [ rewrite Nat.add_0_r; reflexivity |].
  rewrite IH; do 3 f_equal; lia.
Qed.

Lemma length_rec_btys : forall p D M k cs, List.length (rec_btys p D M k cs) = List.length cs.
Proof. intros p D M k cs; revert k; induction cs as [| [] cs IH]; intros; cbn; auto. Qed.

Lemma rec_brs_in : forall M K cs j c n B,
    In (c, n, B) (rec_brs M K j cs) ->
    exists cs1 gs cs2, cs = cs1 ++ (c, gs) :: cs2 /\ n = (im_nn M + List.length gs + cargs_nrec gs)%nat /\
      B = apps (a_var (n + S (im_nn M) + (K - 1 - (j + List.length cs1)))) (vars_from 0 n).
Proof.
  induction cs as [| [c' gs'] cs IH]; intros * Hin; cbn in Hin; [ destruct Hin |].
  destruct Hin as [[= <- <- <-] | Hin].
  - exists nil, gs', cs; cbn; rewrite Nat.add_0_r; auto.
  - destruct (IH _ _ _ _ Hin) as (cs1 & gs & cs2 & -> & -> & ->).
    exists ((c', gs') :: cs1), gs, cs2; cbn [List.app List.length]; split; [ reflexivity | split; [ reflexivity |] ].
    do 3 f_equal; lia.
Qed.

Lemma rec_brs_names : forall M K j cs, List.map fst cs = List.map (fun b => fst (fst b)) (rec_brs M K j cs).
Proof. intros M K j cs; revert j; induction cs as [| [c gs] cs IH]; intros; cbn; [ reflexivity | rewrite (IH (S j)); reflexivity ]. Qed.

Lemma nodup_in_fst : forall {X Y : Type} (l : list (X * Y)) x y y',
    NoDup (List.map fst l) -> In (x, y) l -> In (x, y') l -> y = y'.
Proof.
  induction l as [| [a b] l IH]; intros * Hnd H1 H2; [ destruct H1 |].
  inversion Hnd as [| ? ? Hn Hnd']; subst.
  destruct H1 as [[= <- <-] | H1], H2 as [[= <-] | H2]; auto.
  - exfalso; apply Hn; apply (List.in_map fst) in H2; exact H2.
  - exfalso; apply Hn; apply (List.in_map fst) in H1; exact H1.
  - eapply IH; eassumption.
Qed.

(** ** The Recursor's Telescope

    Over the uniform parameters [Γ0]: the level, the motive at it, then the
    branch arguments, the [k]-th under the [k] before it. *)

(** The type of the recursor's motive: over the member's non-uniform
    parameters and a scrutinee, the universe at the level argument. *)
Definition rec_mty (p : qname) (D : ind_decl) (M : imember) : typ :=
  ctx_pi (elim_mctx p D 0 M (vars_from 1 (ind_nu D))) (a_univ (a_var (S (im_nn M)))).

Lemma rec_tele_eq : forall p D M Γ,
    rec_tele p D M ++ Γ = List.rev (rec_btys p D M 0 (im_cons M)) ++ ce_ass (rec_mty p D M) :: ce_ass (a_level 0) :: Γ.
Proof. intros; unfold rec_tele; rewrite <- List.app_assoc; reflexivity. Qed.

Lemma rec_motive_wk : forall M k m,
    (rec_motive M k)[wk_qn (S (im_nn M)) (wk_shiftn m)]ʷ = rec_motive M (k + m).
Proof.
  intros; unfold rec_motive; rewrite apps_exp_wk; cbn [exp_wk]; rewrite wk_qn_ge by lia.
  f_equal; [ cbn; f_equal; lia |].
  unfold vars_from; rewrite List.map_map; apply List.map_ext_in; intros x Hx.
  apply List.in_rev, List.in_seq in Hx; cbn [exp_wk]; rewrite wk_qn_lt by lia; reflexivity.
Qed.

Lemma rec_uvars_wk : forall D k m,
    List.map (fun U => U[wk_shiftn m]ʷ) (rec_uvars D k) = rec_uvars D (k + m).
Proof. intros; unfold rec_uvars; rewrite vars_from_wk_shiftn; f_equal; lia. Qed.

(** The eliminator's motive, at the scrutinee's parameters and the
    scrutinee, is the recursor's codomain. *)
Lemma rec_motive_inst : forall M K,
    (rec_motive M (S (im_nn M) + K))[sb_of_list Id (vars_from 1 (im_nn M) ++ #0 :: nil)] = rec_motive M K.
Proof.
  intros.
  assert (Hv : vars_from 1 (im_nn M) ++ #0 :: nil = vars_from 0 (S (im_nn M))).
  { replace (S (im_nn M)) with (im_nn M + 1) by lia; rewrite <- (vars_from_app 0 (im_nn M) 1); reflexivity. }
  rewrite Hv; unfold rec_motive; rewrite apps_exp_sub; cbn [exp_sub].
  f_equal.
  - replace (S (im_nn M) + (S (im_nn M) + K)) with (List.length (vars_from 0 (S (im_nn M))) + (S (im_nn M) + K))
      by (rewrite length_vars_from; reflexivity).
    rewrite sb_of_list_ge; reflexivity.
  - pose proof (vars_from_sb_of_list (vars_from 0 (S (im_nn M))) Id) as H.
    rewrite length_vars_from in H; exact H.
Qed.

(** ** The Recursor of a One-Member Group

    The group [D] at [p] of the only member [M], declared. *)
Section RecTyped.
  Variables (Θ : gdeps) (Ξ : gstack) (p : qname) (D : ind_decl) (M : imember) (pm : qname).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.
  Hypothesis Hds : decls_typed Θ Ξ.
  Hypothesis HD : decl_typed Θ Ξ D.
  Hypothesis Hc : decl_closed D.
  Hypothesis Hl : ind_lookup Θ Ξ p = Some D.
  Hypothesis Hone : ind_members D = M :: nil.
  Hypothesis Hh : im_head M = mh_decl pm.
  Hypothesis HU : ⊢ Θ ⍮ Ξ ⍮ ind_uparams D.

  #[local] Abbreviation Γ0 := (ind_uparams D).
  #[local] Abbreviation nn := (im_nn M).
  #[local] Abbreviation nu := (ind_nu D).
  #[local] Abbreviation Lm := (ce_ass (rec_mty p D M) :: ce_ass (a_level 0) :: ind_uparams D).

  Lemma HM : ind_member D 0 = Some M.
  Proof. unfold ind_member; rewrite Hone; reflexivity. Qed.

  Lemma member_0 : forall j Mj, ind_member D j = Some Mj -> j = 0 /\ Mj = M.
  Proof.
    intros j Mj H; unfold ind_member in H; rewrite Hone in H.
    destruct j as [| [| j]]; cbn in H; [ injection H as <-; auto | discriminate | destruct j; discriminate ].
  Qed.

  (** The variables of the uniform parameters, under [Φ]. *)
  Lemma uvars_typed : forall Φ, ⊢ Θ ⍮ Ξ ⍮ Φ ++ Γ0 ->
      forall k U T, List.nth_error (vars_from (List.length Φ) nu) k = Some U ->
        List.nth_error (tele_insts Γ0 Id (vars_from (List.length Φ) nu)) k = Some T ->
        Θ ⍮ Ξ ⍮ Φ ++ Γ0 ⊢ U : T.
  Proof.
    intros Φ HΦ.
    apply wf_vars_tele; [ apply (decl_uparams_ass D Hc) | apply (decl_uparams_closed D Hc)
                        | apply (decl_uparams_mvc _ _ _ HD) | exact HΦ ].
  Qed.

  Lemma uvars_sub : forall Φ, ⊢ Θ ⍮ Ξ ⍮ Φ ++ Γ0 ->
      Θ ⍮ Ξ ⍮ Φ ++ Γ0 ⊢ˢ sb_of_list Id (vars_from (List.length Φ) nu) : Γ0 ++ Φ ++ Γ0.
  Proof.
    intros Φ HΦ; apply (wf_sub_uparams _ _ _ HD Hc); [ exact HΦ | apply length_vars_from | apply uvars_typed, HΦ ].
  Qed.

  Lemma uvars_mctx : forall Φ, ⊢ Θ ⍮ Ξ ⍮ Φ ++ Γ0 -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D 0 M (vars_from (List.length Φ) nu) ++ Φ ++ Γ0.
  Proof.
    intros Φ HΦ; eapply elim_mctx_wf; [ exact Hg | exact Hds | exact Hl | exact HM | exact HΦ | apply length_vars_from
                                      | apply uvars_typed, HΦ ].
  Qed.

  Lemma level_var : forall E Γ, ⊢ Θ ⍮ Ξ ⍮ E ++ ce_ass (a_level 0) :: Γ ->
      Θ ⍮ Ξ ⍮ E ++ ce_ass (a_level 0) :: Γ ⊢ #(List.length E) : Level@0.
  Proof.
    intros * HE; pose proof (lookup_mid E (a_level 0) Γ) as H; cbn in H.
    apply wf_vlookup; [ exact HE | exact H ].
  Qed.

  Lemma univ_large : forall Γ L i, Θ ⍮ Ξ ⍮ Γ ⊢ L : Level@0 -> Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨L⟩ : Typeω@i.
  Proof.
    intros * HL; eapply (wf_exp_suniv_large (n := 0)); [ apply wf_succl; exact HL | eapply wf_univ; exact HL ].
  Qed.

  Lemma L1_wf : ⊢ Θ ⍮ Ξ ⍮ ce_ass (a_level 0) :: Γ0.
  Proof. eapply wf_ctx_extend; apply (wf_level_large (i := 0)); exact HU. Qed.

  Lemma Lm_wf : ⊢ Θ ⍮ Ξ ⍮ Lm.
  Proof.
    pose proof (uvars_mctx (ce_ass (a_level 0) :: nil) L1_wf) as HMc; cbn [List.length List.app] in HMc.
    assert (Hb : Θ ⍮ Ξ ⍮ elim_mctx p D 0 M (vars_from 1 nu) ++ ce_ass (a_level 0) :: Γ0 ⊢ a_univ (a_var (S nn)) : Typeω@0).
    { apply univ_large; rewrite <- (length_elim_mctx p D 0 M (vars_from 1 nu)); apply level_var; exact HMc. }
    destruct (ctx_pi_wf _ _ _ _ _ _ HMc Hb) as [j Hj].
    eapply wf_ctx_extend; exact Hj.
  Qed.

  (** The motive, under [k] branch arguments and then the motive's context
      at the uniform parameters' variables. *)
  Lemma motive_at : forall E, ⊢ Θ ⍮ Ξ ⍮ E ++ Lm ->
      ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D 0 M (rec_uvars D (List.length E)) ++ E ++ Lm /\
      forall i, Θ ⍮ Ξ ⍮ elim_mctx p D 0 M (rec_uvars D (List.length E)) ++ E ++ Lm ⊢ rec_motive M (List.length E) : Typeω@i.
  Proof.
    intros E HE.
    assert (HΦ : ⊢ Θ ⍮ Ξ ⍮ (E ++ ce_ass (rec_mty p D M) :: ce_ass (a_level 0) :: nil) ++ Γ0)
      by (rewrite <- List.app_assoc; exact HE).
    pose proof (uvars_mctx _ HΦ) as HMc.
    rewrite <- List.app_assoc in HMc; cbn [List.app] in HMc.
    replace (vars_from (List.length (E ++ ce_ass (rec_mty p D M) :: ce_ass (a_level 0) :: nil)) nu)
      with (rec_uvars D (List.length E)) in HMc
      by (unfold rec_uvars; rewrite List.length_app; cbn [List.length]; f_equal; lia).
    split; [ exact HMc |].
    intros i.
    (* the motive's variable, of the motive's type moved past [E] *)
    assert (Hv : Θ ⍮ Ξ ⍮ E ++ Lm ⊢ #(List.length E)
                   : ctx_pi (elim_mctx p D 0 M (rec_uvars D (List.length E)))
                       (a_univ (a_var (S nn + S (List.length E))))).
    { pose proof (lookup_mid E (rec_mty p D M) (ce_ass (a_level 0) :: Γ0)) as H.
      unfold rec_mty in H; rewrite ctx_pi_wk in H.
      rewrite elim_mctx_wk, vars_from_wk_shiftn in H by (first [ exact Hc | exact HM | apply length_vars_from ]).
      rewrite length_elim_mctx in H; cbn [exp_wk] in H; rewrite wk_qn_ge in H by lia.
      replace (1 + S (List.length E)) with (2 + List.length E) in H by lia.
      replace (wk_shiftn (S (List.length E)) (S nn - S nn) + S nn) with (S nn + S (List.length E)) in H
        by (cbn; lia).
      apply wf_vlookup; [ exact HE | exact H ]. }
    assert (Hlv : Θ ⍮ Ξ ⍮ elim_mctx p D 0 M (rec_uvars D (List.length E)) ++ E ++ Lm
                    ⊢ a_var (S nn + S (List.length E)) : Level@0).
    { replace (elim_mctx p D 0 M (rec_uvars D (List.length E)) ++ E ++ Lm)
        with ((elim_mctx p D 0 M (rec_uvars D (List.length E)) ++ E ++ ce_ass (rec_mty p D M) :: nil) ++ ce_ass (a_level 0) :: Γ0)
        by (rewrite <- !List.app_assoc; reflexivity).
      replace (S nn + S (List.length E))
        with (List.length (elim_mctx p D 0 M (rec_uvars D (List.length E)) ++ E ++ ce_ass (rec_mty p D M) :: nil))
        by (rewrite !List.length_app, length_elim_mctx; cbn; lia).
      apply level_var; rewrite <- !List.app_assoc; exact HMc. }
    pose proof (wf_apps_vars _ _ _ _ _ _ _ (elim_mctx_ass p D 0 M _ Hc HM) HMc (univ_large _ _ i Hlv) Hv) as H.
    rewrite length_elim_mctx in H; cbn [exp_wk] in H.
    unfold rec_motive.
    replace (a_var (S nn + List.length E)) with (a_var (wk_shiftn (S nn) (List.length E))) by (cbn; f_equal; lia).
    eapply (wf_exp_suniv_large (n := 0)); [ exact Hlv | exact H ].
  Qed.

  Lemma uvars_at : forall E, ⊢ Θ ⍮ Ξ ⍮ E ++ Lm ->
      (forall k U T, List.nth_error (rec_uvars D (List.length E)) k = Some U ->
         List.nth_error (tele_insts Γ0 Id (rec_uvars D (List.length E))) k = Some T ->
         Θ ⍮ Ξ ⍮ E ++ Lm ⊢ U : T) /\
      Θ ⍮ Ξ ⍮ E ++ Lm ⊢ˢ sb_of_list Id (rec_uvars D (List.length E)) : Γ0 ++ E ++ Lm.
  Proof.
    intros E HE.
    assert (HΦ : ⊢ Θ ⍮ Ξ ⍮ (E ++ ce_ass (rec_mty p D M) :: ce_ass (a_level 0) :: nil) ++ Γ0)
      by (rewrite <- List.app_assoc; exact HE).
    assert (Hu : rec_uvars D (List.length E) = vars_from (List.length (E ++ ce_ass (rec_mty p D M) :: ce_ass (a_level 0) :: nil)) nu)
      by (unfold rec_uvars; rewrite List.length_app; cbn [List.length]; f_equal; lia).
    pose proof (uvars_typed _ HΦ) as H1; pose proof (uvars_sub _ HΦ) as H2.
    rewrite <- Hu in H1, H2; rewrite <- List.app_assoc in H1, H2; cbn [List.app] in H1, H2.
    split; [ exact H1 | exact H2 ].
  Qed.

  Lemma motives_one : forall Γ Us A i,
      Θ ⍮ Ξ ⍮ elim_mctx p D 0 M Us ++ Γ ⊢ A : Typeω@i -> motives_typed Θ Ξ Γ p D Us (A :: nil) i.
  Proof. intros * HA j Mj HMj; destruct (member_0 _ _ HMj) as [-> ->]; exact HA. Qed.

  Lemma mctxs_one : forall Γ Us, ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D 0 M Us ++ Γ ->
      forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj Us ++ Γ.
  Proof. intros * H j Mj HMj; destruct (member_0 _ _ HMj) as [-> ->]; exact H. Qed.

  (** A branch's context and type, at the motive under [k] branch arguments. *)
  Lemma branch_at : forall E c gs, ⊢ Θ ⍮ Ξ ⍮ E ++ Lm -> ind_con M c = Some gs ->
      ⊢ Θ ⍮ Ξ ⍮ elim_bctx p D M gs (rec_motive M (List.length E) :: nil) (rec_uvars D (List.length E)) ++ E ++ Lm /\
      forall i, Θ ⍮ Ξ ⍮ elim_bctx p D M gs (rec_motive M (List.length E) :: nil) (rec_uvars D (List.length E)) ++ E ++ Lm
        ⊢ elim_bty p 0 M c gs (rec_motive M (List.length E)) (rec_uvars D (List.length E)) : Typeω@i.
  Proof.
    intros * HE Hcon.
    destruct (motive_at _ HE) as [HMc HA].
    destruct (uvars_at _ HE) as [HUs Hσ].
    assert (Hlu : List.length (rec_uvars D (List.length E)) = nu) by apply length_vars_from.
    pose proof (elim_bctx_wf _ _ _ _ _ _ _ _ _ 0 c gs Hg Hds Hl HM HE Hlu Hσ (mctxs_one _ _ HMc) (motives_one _ _ _ _ (HA 0)) Hcon)
      as HB.
    split; [ exact HB |].
    intros i.
    pose proof (wf_bty_sub _ _ _ _ _ _ _ _ _ i c gs Hg Hds Hl HM HE Hlu HUs (mctxs_one _ _ HMc) (motives_one _ _ _ _ (HA i)) Hcon)
      as Hs.
    exact (sub_preserves_exp _ _ _ _ _ _ _ (HA i) Hs).
  Qed.

  Lemma branch_ty_at : forall E c gs, ⊢ Θ ⍮ Ξ ⍮ E ++ Lm -> ind_con M c = Some gs ->
      exists j, Θ ⍮ Ξ ⍮ E ++ Lm
        ⊢ ctx_pi (elim_bctx p D M gs (rec_motive M (List.length E) :: nil) (rec_uvars D (List.length E)))
            (elim_bty p 0 M c gs (rec_motive M (List.length E)) (rec_uvars D (List.length E))) : Typeω@j.
  Proof.
    intros * HE Hcon; destruct (branch_at _ _ _ HE Hcon) as [HB Hty].
    eapply ctx_pi_wf; [ exact HB | exact (Hty 0) ].
  Qed.

  Lemma btys_wf : forall cs E, (forall c gs, In (c, gs) cs -> ind_con M c = Some gs) ->
      ⊢ Θ ⍮ Ξ ⍮ E ++ Lm -> ⊢ Θ ⍮ Ξ ⍮ List.rev (rec_btys p D M (List.length E) cs) ++ E ++ Lm.
  Proof.
    induction cs as [| [c gs] cs IH]; intros E Hcs HE; cbn [rec_btys List.rev List.app]; [ exact HE |].
    rewrite <- List.app_assoc; cbn [List.app].
    destruct (branch_ty_at E c gs HE (Hcs _ _ (or_introl eq_refl))) as [j Hj].
    apply (IH (_ :: E)); [ intros; apply Hcs; right; assumption |].
    eapply wf_ctx_extend; exact Hj.
  Qed.

  #[local] Abbreviation K := (List.length (im_cons M)).
  #[local] Abbreviation EK := (List.rev (rec_btys p D M 0 (im_cons M))).

  Lemma cons_con : forall c gs, In (c, gs) (im_cons M) -> ind_con M c = Some gs.
  Proof. intros; apply cons_lookup_nodup; [ exact (decl_typed_nodup _ _ _ HD _ _ HM) | assumption ]. Qed.

  Lemma con_in : forall c gs gs', ind_con M c = Some gs -> In (c, gs') (im_cons M) -> gs = gs'.
  Proof.
    intros * Hcon Hin; apply cons_lookup_in in Hcon.
    pose proof (decl_typed_nodup _ _ _ HD _ _ HM) as Hnd.
    eapply nodup_in_fst; eassumption.
  Qed.

  Lemma length_EK : List.length EK = K.
  Proof. rewrite List.length_rev, length_rec_btys; reflexivity. Qed.

  Lemma EK_wf : ⊢ Θ ⍮ Ξ ⍮ EK ++ Lm.
  Proof. exact (btys_wf (im_cons M) nil cons_con Lm_wf). Qed.

  Lemma ndecl_pos : 0 < ind_ndecl D.
  Proof. unfold ind_ndecl; rewrite Hone; cbn; unfold im_is_decl; rewrite Hh; cbn; lia. Qed.

  Lemma ind_mty_0 : forall Us Ns, ind_mty p D 0 Us Ns = apps (a_ind p 0) (Us ++ Ns).
  Proof. intros; unfold ind_mty; rewrite HM; unfold im_ty_at, im_ref, im_pre; rewrite Hh; reflexivity. Qed.

  (** The eliminator, under the recursor's telescope and the motive's
      context at the module's uniform parameters. *)
  Lemma rec_elim_typed :
      Θ ⍮ Ξ ⍮ elim_mctx p D 0 M (rec_uvars D K) ++ EK ++ Lm
        ⊢ a_elim None (rec_uvars D (K + S nn)) 0 (eb_mk (S nn) None (rec_motive M (K + S nn)) (rec_brs M K 0 (im_cons M)) :: nil) (a_var 0)
        : rec_motive M K.
  Proof.
    destruct (motive_at _ EK_wf) as [HM2 HA2]; rewrite length_EK in HM2, HA2.
    set (E2 := elim_mctx p D 0 M (rec_uvars D K) ++ EK).
    assert (HE2 : ⊢ Θ ⍮ Ξ ⍮ E2 ++ Lm) by (unfold E2; rewrite <- List.app_assoc; exact HM2).
    assert (HlE2 : List.length E2 = S nn + K) by (unfold E2; rewrite List.length_app, length_elim_mctx, length_EK; reflexivity).
    destruct (motive_at _ HE2) as [HM3 HA3]; rewrite HlE2 in HM3, HA3.
    destruct (uvars_at _ HE2) as [HUs3 _]; rewrite HlE2 in HUs3.
    unfold E2 in HM3, HA3, HUs3; rewrite <- List.app_assoc in HM3, HA3, HUs3.
    set (Us := rec_uvars D K) in *.
    set (Us' := rec_uvars D (S nn + K)) in *.
    set (Ps := Us' ++ vars_from 1 nn).
    assert (HUl : List.length Us = nu) by apply length_vars_from.
    assert (HUl' : List.length Us' = nu) by apply length_vars_from.
    assert (HNl : List.length (vars_from 1 nn) = nn) by apply length_vars_from.
    assert (HUs'w : Us' = List.map (fun U => U[wk_shiftn (S nn)]ʷ) Us)
      by (unfold Us, Us'; rewrite rec_uvars_wk; f_equal; lia).
    assert (HF : List.firstn nu Ps = Us') by (unfold Ps; exact (firstn_app_len Us' (vars_from 1 nn) nu HUl')).
    assert (HS : List.skipn nu Ps = vars_from 1 nn) by (unfold Ps; exact (skipn_app_len Us' (vars_from 1 nn) nu HUl')).
    rewrite (Nat.add_comm K (S nn)).
    rewrite <- (rec_motive_inst M K), <- HS.
    eapply wf_elim with (i := 0) (Ps := Ps) (bm := eb_mk (S nn) None (rec_motive M (S nn + K)) (rec_brs M K 0 (im_cons M)));
      [ exact Hl | right; split; [ reflexivity | exact ndecl_pos ] | exact HM | reflexivity
      | rewrite Hone; reflexivity | | | | rewrite HF; reflexivity | | | | | | | | ].
    - (* the number of parameters *)
      unfold Ps, im_np; rewrite List.length_app, HUl', HNl; lia.
    - (* the parameters, at their types: the uniform ones the module's,
         the non-uniform ones the motive context's variables *)
      apply (params_typed_join _ _ _ Hc 0 M _ Us' (vars_from 1 nn) HM HUl'); [ exact HUs3 |].
      intros k N T HN HT.
      unfold elim_mctx.
      replace (vars_from 1 nn)
        with (vars_from (List.length (ce_ass (ind_mty p D 0 (List.map (fun U => U[wk_shiftn nn]ʷ) Us) (vars_from 0 nn)) :: nil))
                (List.length (im_nparams M))) in HN, HT
        by (rewrite length_im_nparams; reflexivity).
      eapply (wf_vars_tele_gen _ _ (ce_ass _ :: nil) (im_nparams M) (sb_of_list Id Us) _ (EK ++ Lm) nu);
        [ apply (decl_closed_nparams_ass D Hc 0 M HM) | apply (decl_nparams_mvc _ _ _ HD 0 M HM)
        | apply (decl_closed_nparams_scoped D Hc 0 M HM) | exact HM2 | | exact HN | exact HT ].
      intros y Hy; rewrite HUs'w, sb_of_list_map by lia; cbn [List.length]; rewrite length_im_nparams; reflexivity.
    - (* the scrutinee: the motive context's innermost variable *)
      rewrite HF, HS, ind_mty_0.
      assert (Heq : (ind_mty p D 0 (List.map (fun U => U[wk_shiftn nn]ʷ) Us) (vars_from 0 nn))[↑]ʷ
                    = apps (a_ind p 0) (Us' ++ vars_from 1 nn)).
      { rewrite ind_mty_0, apps_exp_wk, List.map_app, List.map_map; cbn [exp_wk]; f_equal; f_equal.
        - rewrite HUs'w; apply List.map_ext; intros U; rewrite exp_wk_wk; apply exp_wk_wk_eq; intros x; cbn; lia.
        - unfold vars_from; rewrite List.map_map; apply List.map_ext; intros x; cbn; f_equal; lia. }
      apply wf_vlookup; [ exact HM2 |].
      unfold elim_mctx; cbn [List.app]; rewrite <- Heq; constructor.
    - intros k Mk b HMk Hb; destruct (member_0 _ _ HMk) as [-> ->]; cbn in Hb; injection Hb as <-; reflexivity.
    - intros k Mk b Z HMk Hb Hz; destruct (member_0 _ _ HMk) as [-> ->]; cbn in Hb; injection Hb as <-; discriminate.
    - intros k Mk b HMk Hb; destruct (member_0 _ _ HMk) as [-> ->]; cbn in Hb; injection Hb as <-; cbn.
      rewrite HF; apply HA3.
    - intros k Mk HMk; destruct (member_0 _ _ HMk) as [-> ->]; rewrite HF.
      apply ctx_ext_refl; [ apply (elim_mctx_ass p D 0 M _ Hc HM) | exact HM3 ].
    - intros k Mk b HMk Hb; destruct (member_0 _ _ HMk) as [-> ->]; cbn in Hb; injection Hb as <-; apply rec_brs_names.
    - intros k Mk c gs HMk Hcon; destruct (member_0 _ _ HMk) as [-> ->]; rewrite HF; cbn [blocks_motives List.map eb_motive].
      destruct (branch_at _ _ _ HE2 Hcon) as [HB _]; rewrite HlE2 in HB; unfold E2 in HB; rewrite <- List.app_assoc in HB.
      fold Us' in HB.
      apply ctx_ext_refl; [ apply (elim_bctx_ass p D 0 M gs _ _ Hc HM) | exact HB ].
    - intros k Mk b c gs n B HMk Hb Hcon Hin; destruct (member_0 _ _ HMk) as [-> ->]; cbn in Hb; injection Hb as <-.
      destruct (rec_brs_in _ _ _ _ _ _ _ Hin) as (cs1 & gs' & cs2 & Hcs & -> & _).
      rewrite (con_in _ _ _ Hcon ltac:(rewrite Hcs; apply List.in_elt)); reflexivity.
    - (* a branch: its branch argument, applied to what the branch binds *)
      intros k Mk b c gs n B HMk Hb Hcon Hin; destruct (member_0 _ _ HMk) as [-> ->]; cbn in Hb; injection Hb as <-.
      cbn [eb_brs eb_motive blocks_motives List.map] in *.
      destruct (rec_brs_in _ _ _ _ _ _ _ Hin) as (cs1 & gs' & cs2 & Hcs & Hn & HB).
      assert (gs' = gs) as -> by (symmetry; apply (con_in _ _ _ Hcon); rewrite Hcs; apply List.in_elt).
      rewrite HF.
      set (i := List.length cs1) in *.
      set (bt := ctx_pi (elim_bctx p D M gs (rec_motive M i :: nil) (rec_uvars D i))
                   (elim_bty p 0 M c gs (rec_motive M i) (rec_uvars D i))).
      assert (HEK : List.rev (rec_btys p D M 0 (im_cons M))
                    = List.rev (rec_btys p D M (S i) cs2) ++ ce_ass bt :: List.rev (rec_btys p D M 0 cs1)).
      { rewrite Hcs, rec_btys_app; cbn [rec_btys]; rewrite List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity. }
      assert (HK : K = i + S (List.length cs2)) by (rewrite Hcs, List.length_app; reflexivity).
      pose proof (lookup_mid (elim_mctx p D 0 M Us ++ List.rev (rec_btys p D M (S i) cs2)) bt
                    (List.rev (rec_btys p D M 0 cs1) ++ Lm)) as Hlk.
      rewrite List.length_app, length_elim_mctx, List.length_rev, length_rec_btys in Hlk.
      rewrite <- !List.app_assoc in Hlk; cbn [List.app] in Hlk.
      replace (elim_mctx p D 0 M Us ++ List.rev (rec_btys p D M (S i) cs2) ++ ce_ass bt :: List.rev (rec_btys p D M 0 cs1) ++ Lm)
        with (elim_mctx p D 0 M Us ++ EK ++ Lm) in Hlk by (rewrite HEK, <- List.app_assoc; reflexivity).
      unfold bt in Hlk; rewrite ctx_pi_wk in Hlk.
      erewrite (elim_bctx_wk p D 0 M c gs (rec_motive M i :: nil) (rec_motive M (i + S (S nn + List.length cs2)) :: nil))
        in Hlk by (first [ exact Hc | exact HM | rewrite Hcs; apply List.in_elt | apply length_vars_from
                         | intros j Mj HMj; destruct (member_0 _ _ HMj) as [-> ->]; cbn [List.nth]; rewrite rec_motive_wk; reflexivity ]).
      rewrite length_elim_bctx in Hlk.
      replace (cargs_nrec gs + List.length gs + nn) with (nn + List.length gs + cargs_nrec gs) in Hlk by lia.
      rewrite (elim_bty_wk p D 0 M) in Hlk by (first [ exact Hc | exact HM | apply length_vars_from ]).
      rewrite rec_motive_wk, rec_uvars_wk in Hlk.
      replace (i + S (S nn + List.length cs2)) with (S nn + K) in Hlk by lia.
      fold Us' in Hlk.
      destruct (branch_at _ _ _ HE2 Hcon) as [HBc HBt]; rewrite HlE2 in HBc, HBt; unfold E2 in HBc, HBt;
        rewrite <- List.app_assoc in HBc, HBt.
      pose proof (wf_apps_vars _ _ _ _ _ _ _ (elim_bctx_ass p D 0 M gs _ Us' Hc HM) HBc (HBt 0)
                    (wf_vlookup _ _ _ _ _ HM2 Hlk)) as H.
      rewrite length_elim_bctx in H; cbn [exp_wk] in H.
      rewrite HB, Hn.
      replace (nn + List.length gs + cargs_nrec gs + S nn + (K - 1 - (0 + i)))
        with (wk_shiftn (cargs_nrec gs + List.length gs + nn) (S nn + List.length cs2)) by (cbn; lia).
      replace (nn + List.length gs + cargs_nrec gs) with (cargs_nrec gs + List.length gs + nn) by lia.
      exact H.
  Qed.

  (** The recursor is of its type over the module's parameters. *)
  Lemma rec_typed : Θ ⍮ Ξ ⍮ Γ0 ⊢ rec_fn p D M : rec_ty p D M.
  Proof.
    unfold rec_fn, rec_ty; cbv zeta.
    destruct (motive_at _ EK_wf) as [HM2 HA2]; rewrite length_EK in HM2, HA2.
    pose proof rec_elim_typed as He.
    rewrite <- rec_tele_eq in HM2, HA2, He.
    pose proof EK_wf as H1; rewrite <- rec_tele_eq in H1.
    destruct (ctx_pi_wf _ _ _ _ _ _ HM2 (HA2 0)) as [j Hj].
    eapply ctx_fn_wf; [ exact H1 | exact Hj |].
    eapply ctx_fn_wf; [ exact HM2 | exact (HA2 0) | exact He ].
  Qed.
End RecTyped.

(** ** The Constructors

    A constructor of a declared member [k], applied to the module's
    parameters, is of its type over the non-uniform ones. *)
Lemma con_gen_typed : forall Θ Ξ p D k Mk pm c gs, ⊢ᵍ Θ ⍮ Ξ -> decls_typed Θ Ξ -> decl_typed Θ Ξ D -> decl_closed D ->
    ind_lookup Θ Ξ p = Some D -> ind_member D k = Some Mk -> im_head Mk = mh_decl pm -> ⊢ Θ ⍮ Ξ ⍮ ind_uparams D ->
    ind_con Mk c = Some gs ->
    Θ ⍮ Ξ ⍮ ind_uparams D ⊢ apps (a_con p k c) (vars_from 0 (ind_nu D))
      : ctx_pi (im_nparams Mk) (ctx_pi (cargs_ctx p D Mk gs) (apps (a_ind p k) (ind_pvars D Mk (List.length gs)))).
Proof.
  intros * Hg Hds HD Hc Hl HMk Hh HU Hcon.
  pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
  destruct (con_cod_typed _ _ _ _ _ _ _ _ Hg Hds Hl HMk Hcon) as [j Hj].
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg Hds Hl HMk Hin gs nil (eq_sym (List.app_nil_r gs))) as (HΨ & _ & _).
  destruct (con_ty_typed0 _ _ _ _ _ _ _ _ Hg Hds Hl HMk Hcon) as [k0 Hk].
  assert (H0 : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; exact Hg).
  assert (HM0 : Θ ⍮ Ξ ⍮ ⋅ ⊢ a_con p k c : con_ty p D k Mk gs).
  { eapply wf_con; try eassumption.
    exact (shape_rest_wf' _ _ _ _ _ _ _ _ Hg Hds Hl HMk Hcon). }
  assert (Hty : ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk))
                = apps (a_ind p k) (ind_pvars D Mk (List.length gs))).
  { unfold ind_mty; rewrite HMk; unfold im_ty_at, im_ref, im_pre; rewrite Hh; cbn [fst snd].
    unfold ind_uvars, ind_pvars, im_np; f_equal.
    rewrite (vars_from_app (List.length gs) (ind_nu D) (im_nn Mk)); f_equal; lia. }
  unfold con_ty in HM0; rewrite Hty in HM0; unfold im_params in HM0; rewrite ctx_pi_app in HM0.
  rewrite Hty in Hj; unfold im_params in Hj, HΨ; rewrite List.app_assoc in Hj, HΨ.
  destruct (ctx_pi_wf _ _ _ _ _ _ HΨ Hj) as [j' Hj']; rewrite ctx_pi_app in Hj'.
  assert (HU0 : ⊢ Θ ⍮ Ξ ⍮ ind_uparams D ++ ⋅) by (rewrite List.app_nil_r; exact HU).
  assert (Hj0 : Θ ⍮ Ξ ⍮ ind_uparams D ++ ⋅
                  ⊢ ctx_pi (im_nparams Mk) (ctx_pi (cargs_ctx p D Mk gs) (apps (a_ind p k) (ind_pvars D Mk (List.length gs))))
                  : Typeω@j') by (rewrite List.app_nil_r; exact Hj').
  pose proof (wf_apps_vars _ _ _ _ _ _ _ (decl_uparams_ass D Hc) HU0 Hj0 HM0) as H.
  rewrite List.app_nil_r in H; exact H.
Qed.
