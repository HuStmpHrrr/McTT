(** * What a Declaration Generates Type-Checks

    The constructors and the recursor [X.rec] a declaration generates
    ([ind_gens]) are terms of the types they are declared at, in the
    module's frame: a run of an accepted declaration never fails at them
    ([ind_gens_run]).  Each is a term of a [Π] over a telescope applied to
    the telescope's variables ([wf_apps_vars]), under [λ]s over the
    recursor's telescope. *)

From Stdlib Require Import Lia List PeanoNat.
From Stdlib Require Import String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import SystemOpt.
From Mctt.Core.Syntactic.System Require Import Scoping GlobalPresup IndTyping IndSyntax MemberLemmas Command.
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
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢w ↑ : Γ) by mauto 2.
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

Lemma rec_btys_app : forall p D k cs1 cs2,
    rec_btys p D k (cs1 ++ cs2) = rec_btys p D k cs1 ++ rec_btys p D (k + List.length cs1) cs2.
Proof.
  intros p D k cs1; revert k; induction cs1 as [| [c gs] cs1 IH]; intros; cbn [List.app rec_btys List.length];
    [ rewrite Nat.add_0_r; reflexivity |].
  rewrite IH; do 3 f_equal; lia.
Qed.

Lemma length_rec_btys : forall p D k cs, List.length (rec_btys p D k cs) = List.length cs.
Proof. intros p D k cs; revert k; induction cs as [| [] cs IH]; intros; cbn; auto. Qed.

Lemma rec_brs_in : forall D K cs j c n B,
    In (c, n, B) (rec_brs D K j cs) ->
    exists cs1 gs cs2, cs = cs1 ++ (c, gs) :: cs2 /\ n = (ind_nn D + List.length gs + cargs_nrec gs)%nat /\
      B = apps (a_var (n + S (ind_nn D) + (K - 1 - (j + List.length cs1)))) (vars_from 0 n).
Proof.
  induction cs as [| [c' gs'] cs IH]; intros * Hin; cbn in Hin; [ destruct Hin |].
  destruct Hin as [[= <- <- <-] | Hin].
  - exists nil, gs', cs; cbn; rewrite Nat.add_0_r; auto.
  - destruct (IH _ _ _ _ Hin) as (cs1 & gs & cs2 & -> & -> & ->).
    exists ((c', gs') :: cs1), gs, cs2; cbn [List.app List.length]; split; [ reflexivity | split; [ reflexivity |] ].
    do 3 f_equal; lia.
Qed.

Lemma rec_brs_names : forall D K j cs, List.map fst cs = List.map (fun b => fst (fst b)) (rec_brs D K j cs).
Proof. intros D K j cs; revert j; induction cs as [| [c gs] cs IH]; intros; cbn; [ reflexivity | rewrite (IH (S j)); reflexivity ]. Qed.

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

Definition rec_mty (p : qname) (D : ind_decl) : typ :=
  ctx_pi (elim_mctx p D (vars_from 1 (ind_nu D))) (a_univ (a_var (S (ind_nn D)))).

Lemma rec_tele_eq : forall p D Γ,
    rec_tele p D ++ Γ = List.rev (rec_btys p D 0 (ind_cons D)) ++ ce_ass (rec_mty p D) :: ce_ass (a_level 0) :: Γ.
Proof. intros; unfold rec_tele; rewrite <- List.app_assoc; reflexivity. Qed.


Lemma rec_motive_wk : forall D k m,
    (rec_motive D k)[wk_qn (S (ind_nn D)) (wk_shiftn m)]ʷ = rec_motive D (k + m).
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
Lemma rec_motive_inst : forall D K,
    (rec_motive D (S (ind_nn D) + K))[sb_of_list Id (vars_from 1 (ind_nn D) ++ #0 :: nil)] = rec_motive D K.
Proof.
  intros.
  assert (Hv : vars_from 1 (ind_nn D) ++ #0 :: nil = vars_from 0 (S (ind_nn D))).
  { replace (S (ind_nn D)) with (ind_nn D + 1) by lia; rewrite <- (vars_from_app 0 (ind_nn D) 1); reflexivity. }
  rewrite Hv; unfold rec_motive; rewrite apps_exp_sub; cbn [exp_sub].
  f_equal.
  - replace (S (ind_nn D) + (S (ind_nn D) + K)) with (List.length (vars_from 0 (S (ind_nn D))) + (S (ind_nn D) + K))
      by (rewrite length_vars_from; reflexivity).
    rewrite sb_of_list_ge; reflexivity.
  - pose proof (vars_from_sb_of_list (vars_from 0 (S (ind_nn D))) Id) as H.
    rewrite length_vars_from in H; exact H.
Qed.

Section RecTyped.
  Variables (Θ : gdeps) (Ξ : gstack) (p : qname) (D : ind_decl).
  Hypothesis HD : decl_typed Θ Ξ D.
  Hypothesis Hc : decl_closed D.
  Hypothesis Hl : ind_lookup Θ Ξ p = Some D.
  Hypothesis HU : ⊢ Θ ⍮ Ξ ⍮ ind_uparams D.

  #[local] Abbreviation Γ0 := (ind_uparams D).
  #[local] Abbreviation nn := (ind_nn D).
  #[local] Abbreviation nu := (ind_nu D).
  #[local] Abbreviation Lm := (ce_ass (rec_mty p D) :: ce_ass (a_level 0) :: ind_uparams D).

  Lemma U_len : List.length Γ0 = nu.
  Proof. apply length_ind_uparams, decl_closed_nu, Hc. Qed.

  (** The variables of the uniform parameters, under [Φ]. *)
  Lemma uvars_typed : forall Φ, ⊢ Θ ⍮ Ξ ⍮ Φ ++ Γ0 ->
      forall k U T, List.nth_error (vars_from (List.length Φ) nu) k = Some U ->
        List.nth_error (tele_insts Γ0 Id (vars_from (List.length Φ) nu)) k = Some T ->
        Θ ⍮ Ξ ⍮ Φ ++ Γ0 ⊢ U : T.
  Proof.
    intros Φ HΦ; rewrite <- U_len.
    apply wf_vars_tele; [ apply (decl_uparams_ass D Hc) | apply (decl_uparams_closed D Hc)
                        | apply (decl_uparams_mvc _ _ _ HD) | exact HΦ ].
  Qed.

  Lemma uvars_sub : forall Φ, ⊢ Θ ⍮ Ξ ⍮ Φ ++ Γ0 ->
      Θ ⍮ Ξ ⍮ Φ ++ Γ0 ⊢s sb_of_list Id (vars_from (List.length Φ) nu) : Γ0 ++ Φ ++ Γ0.
  Proof.
    intros Φ HΦ; apply (wf_sub_uparams _ _ _ HD Hc); [ exact HΦ | apply length_vars_from | apply uvars_typed, HΦ ].
  Qed.

  Lemma uvars_mctx : forall Φ, ⊢ Θ ⍮ Ξ ⍮ Φ ++ Γ0 -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D (vars_from (List.length Φ) nu) ++ Φ ++ Γ0.
  Proof.
    intros Φ HΦ; eapply elim_mctx_wf; [ exact HD | exact Hc | exact Hl | exact HΦ | apply length_vars_from | apply uvars_typed, HΦ ].
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
    pose proof (uvars_mctx (ce_ass (a_level 0) :: nil) L1_wf) as HM; cbn [List.length List.app] in HM.
    assert (Hb : Θ ⍮ Ξ ⍮ elim_mctx p D (vars_from 1 nu) ++ ce_ass (a_level 0) :: Γ0 ⊢ a_univ (a_var (S nn)) : Typeω@0).
    { apply univ_large; rewrite <- (length_elim_mctx p D (vars_from 1 nu)); apply level_var; exact HM. }
    destruct (ctx_pi_wf _ _ _ _ _ _ HM Hb) as [j Hj].
    eapply wf_ctx_extend; exact Hj.
  Qed.

  (** The motive, under [k] branch arguments and then the motive's context
      at the uniform parameters' variables. *)
  Lemma motive_at : forall E, ⊢ Θ ⍮ Ξ ⍮ E ++ Lm ->
      ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D (rec_uvars D (List.length E)) ++ E ++ Lm /\
      forall i, Θ ⍮ Ξ ⍮ elim_mctx p D (rec_uvars D (List.length E)) ++ E ++ Lm ⊢ rec_motive D (List.length E) : Typeω@i.
  Proof.
    intros E HE.
    assert (HΦ : ⊢ Θ ⍮ Ξ ⍮ (E ++ ce_ass (rec_mty p D) :: ce_ass (a_level 0) :: nil) ++ Γ0)
      by (rewrite <- List.app_assoc; exact HE).
    pose proof (uvars_mctx _ HΦ) as HM.
    rewrite <- List.app_assoc in HM; cbn [List.app] in HM.
    replace (vars_from (List.length (E ++ ce_ass (rec_mty p D) :: ce_ass (a_level 0) :: nil)) nu)
      with (rec_uvars D (List.length E)) in HM
      by (unfold rec_uvars; rewrite List.length_app; cbn [List.length]; f_equal; lia).
    split; [ exact HM |].
    intros i.
    (* the motive's variable, of the motive's type moved past [E] *)
    assert (Hv : Θ ⍮ Ξ ⍮ E ++ Lm ⊢ #(List.length E)
                   : ctx_pi (elim_mctx p D (rec_uvars D (List.length E)))
                       (a_univ (a_var (S nn + S (List.length E))))).
    { pose proof (lookup_mid E (rec_mty p D) (ce_ass (a_level 0) :: Γ0)) as H.
      unfold rec_mty in H; rewrite ctx_pi_wk, elim_mctx_wk, vars_from_wk_shiftn in H
        by (first [ exact Hc | apply length_vars_from ]).
      rewrite length_elim_mctx in H; cbn [exp_wk] in H; rewrite wk_qn_ge in H by lia.
      replace (1 + S (List.length E)) with (2 + List.length E) in H by lia.
      replace (wk_shiftn (S (List.length E)) (S nn - S nn) + S nn) with (S nn + S (List.length E)) in H
        by (cbn; lia).
      apply wf_vlookup; [ exact HE | exact H ]. }
    assert (Hb : Θ ⍮ Ξ ⍮ elim_mctx p D (rec_uvars D (List.length E)) ++ E ++ Lm
                   ⊢ a_univ (a_var (S nn + S (List.length E))) : Typeω@i).
    { apply univ_large.
      replace (elim_mctx p D (rec_uvars D (List.length E)) ++ E ++ Lm)
        with ((elim_mctx p D (rec_uvars D (List.length E)) ++ E ++ ce_ass (rec_mty p D) :: nil) ++ ce_ass (a_level 0) :: Γ0)
        by (rewrite <- !List.app_assoc; reflexivity).
      replace (S nn + S (List.length E))
        with (List.length (elim_mctx p D (rec_uvars D (List.length E)) ++ E ++ ce_ass (rec_mty p D) :: nil))
        by (rewrite !List.length_app, length_elim_mctx; cbn; lia).
      apply level_var; rewrite <- !List.app_assoc; exact HM. }
    pose proof (wf_apps_vars _ _ _ _ _ _ _ (elim_mctx_ass p D _ Hc) HM Hb Hv) as H.
    rewrite length_elim_mctx in H; cbn [exp_wk] in H.
    unfold rec_motive.
    replace (a_var (S nn + List.length E)) with (a_var (wk_shiftn (S nn) (List.length E))) by (cbn; f_equal; lia).
    eapply (wf_exp_suniv_large (n := 0)); [| exact H ].
    replace (elim_mctx p D (rec_uvars D (List.length E)) ++ E ++ Lm)
      with ((elim_mctx p D (rec_uvars D (List.length E)) ++ E ++ ce_ass (rec_mty p D) :: nil) ++ ce_ass (a_level 0) :: Γ0)
      by (rewrite <- !List.app_assoc; reflexivity).
    replace (S nn + S (List.length E))
      with (List.length (elim_mctx p D (rec_uvars D (List.length E)) ++ E ++ ce_ass (rec_mty p D) :: nil))
      by (rewrite !List.length_app, length_elim_mctx; cbn; lia).
    apply level_var; rewrite <- !List.app_assoc; exact HM.
  Qed.

  Lemma uvars_at : forall E, ⊢ Θ ⍮ Ξ ⍮ E ++ Lm ->
      (forall k U T, List.nth_error (rec_uvars D (List.length E)) k = Some U ->
         List.nth_error (tele_insts Γ0 Id (rec_uvars D (List.length E))) k = Some T ->
         Θ ⍮ Ξ ⍮ E ++ Lm ⊢ U : T) /\
      Θ ⍮ Ξ ⍮ E ++ Lm ⊢s sb_of_list Id (rec_uvars D (List.length E)) : Γ0 ++ E ++ Lm.
  Proof.
    intros E HE.
    assert (HΦ : ⊢ Θ ⍮ Ξ ⍮ (E ++ ce_ass (rec_mty p D) :: ce_ass (a_level 0) :: nil) ++ Γ0)
      by (rewrite <- List.app_assoc; exact HE).
    assert (Hu : rec_uvars D (List.length E) = vars_from (List.length (E ++ ce_ass (rec_mty p D) :: ce_ass (a_level 0) :: nil)) nu)
      by (unfold rec_uvars; rewrite List.length_app; cbn [List.length]; f_equal; lia).
    pose proof (uvars_typed _ HΦ) as H1; pose proof (uvars_sub _ HΦ) as H2.
    rewrite <- Hu in H1, H2; rewrite <- List.app_assoc in H1, H2; cbn [List.app] in H1, H2.
    split; [ exact H1 | exact H2 ].
  Qed.

  (** A branch's context and type, at the motive under [k] branch arguments. *)
  Lemma branch_at : forall E c gs, ⊢ Θ ⍮ Ξ ⍮ E ++ Lm -> ind_con D c = Some gs ->
      ⊢ Θ ⍮ Ξ ⍮ elim_bctx p D gs (rec_motive D (List.length E)) (rec_uvars D (List.length E)) ++ E ++ Lm /\
      forall i, Θ ⍮ Ξ ⍮ elim_bctx p D gs (rec_motive D (List.length E)) (rec_uvars D (List.length E)) ++ E ++ Lm
        ⊢ elim_bty p D c gs (rec_motive D (List.length E)) (rec_uvars D (List.length E)) : Typeω@i.
  Proof.
    intros * HE Hcon.
    destruct (motive_at _ HE) as [HM HA].
    destruct (uvars_at _ HE) as [HUs Hσ].
    assert (Hlu : List.length (rec_uvars D (List.length E)) = nu) by apply length_vars_from.
    pose proof (elim_bctx_wf _ _ _ _ _ _ _ 0 c gs HD Hc Hl HE Hlu Hσ HM (HA 0) Hcon) as HB.
    split; [ exact HB |].
    intros i.
    pose proof (wf_bty_sub _ _ _ _ _ _ _ i c gs HD Hc Hl HE Hlu HUs HM (HA i) Hcon) as Hs.
    exact (sub_preserves_exp _ _ _ _ _ _ _ (HA i) Hs).
  Qed.

  Lemma branch_ty_at : forall E c gs, ⊢ Θ ⍮ Ξ ⍮ E ++ Lm -> ind_con D c = Some gs ->
      exists j, Θ ⍮ Ξ ⍮ E ++ Lm
        ⊢ ctx_pi (elim_bctx p D gs (rec_motive D (List.length E)) (rec_uvars D (List.length E)))
            (elim_bty p D c gs (rec_motive D (List.length E)) (rec_uvars D (List.length E))) : Typeω@j.
  Proof.
    intros * HE Hcon; destruct (branch_at _ _ _ HE Hcon) as [HB Hty].
    eapply ctx_pi_wf; [ exact HB | exact (Hty 0) ].
  Qed.

  Lemma btys_wf : forall cs E, (forall c gs, In (c, gs) cs -> ind_con D c = Some gs) ->
      ⊢ Θ ⍮ Ξ ⍮ E ++ Lm -> ⊢ Θ ⍮ Ξ ⍮ List.rev (rec_btys p D (List.length E) cs) ++ E ++ Lm.
  Proof.
    induction cs as [| [c gs] cs IH]; intros E Hcs HE; cbn [rec_btys List.rev List.app]; [ exact HE |].
    rewrite <- List.app_assoc; cbn [List.app].
    destruct (branch_ty_at E c gs HE (Hcs _ _ (or_introl eq_refl))) as [j Hj].
    apply (IH (_ :: E)); [ intros; apply Hcs; right; assumption |].
    eapply wf_ctx_extend; exact Hj.
  Qed.

  #[local] Abbreviation K := (List.length (ind_cons D)).
  #[local] Abbreviation EK := (List.rev (rec_btys p D 0 (ind_cons D))).

  Lemma cons_con : forall c gs, In (c, gs) (ind_cons D) -> ind_con D c = Some gs.
  Proof.
    intros; apply cons_lookup_nodup; [| assumption ].
    pose proof HD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnd & _); exact Hnd.
  Qed.

  Lemma con_in : forall c gs gs', ind_con D c = Some gs -> In (c, gs') (ind_cons D) -> gs = gs'.
  Proof.
    intros * Hcon Hin; apply cons_lookup_in in Hcon.
    pose proof HD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnd & _).
    eapply nodup_in_fst; eassumption.
  Qed.

  Lemma length_EK : List.length EK = K.
  Proof. rewrite List.length_rev, length_rec_btys; reflexivity. Qed.

  Lemma EK_wf : ⊢ Θ ⍮ Ξ ⍮ EK ++ Lm.
  Proof. exact (btys_wf (ind_cons D) nil cons_con Lm_wf). Qed.

  (** The eliminator, under the recursor's telescope and the motive's
      context at the module's uniform parameters. *)
  Lemma rec_elim_typed :
      Θ ⍮ Ξ ⍮ elim_mctx p D (rec_uvars D K) ++ EK ++ Lm
        ⊢ a_elim (S nn) (rec_motive D (K + S nn)) (rec_brs D K 0 (ind_cons D)) (a_var 0) : rec_motive D K.
  Proof.
    destruct (motive_at _ EK_wf) as [HM2 HA2]; rewrite length_EK in HM2, HA2.
    set (E2 := elim_mctx p D (rec_uvars D K) ++ EK).
    assert (HE2 : ⊢ Θ ⍮ Ξ ⍮ E2 ++ Lm) by (unfold E2; rewrite <- List.app_assoc; exact HM2).
    assert (HlE2 : List.length E2 = S nn + K) by (unfold E2; rewrite List.length_app, length_elim_mctx, length_EK; reflexivity).
    destruct (motive_at _ HE2) as [HM3 HA3]; rewrite HlE2 in HM3, HA3.
    destruct (uvars_at _ HE2) as [HUs3 _]; rewrite HlE2 in HUs3.
    unfold E2 in HM3, HA3, HUs3; rewrite <- List.app_assoc in HM3, HA3, HUs3.
    set (Us := rec_uvars D K) in *.
    set (Us' := rec_uvars D (S nn + K)) in *.
    set (Ps := Us' ++ vars_from 1 nn).
    pose proof (decl_closed_nu D Hc) as Hle.
    assert (HUl : List.length Us = nu) by apply length_vars_from.
    assert (HUl' : List.length Us' = nu) by apply length_vars_from.
    assert (HNl : List.length (vars_from 1 nn) = nn) by apply length_vars_from.
    assert (HUs'w : Us' = List.map (fun U => U[wk_shiftn (S nn)]ʷ) Us)
      by (unfold Us, Us'; rewrite rec_uvars_wk; f_equal; lia).
    rewrite (Nat.add_comm K (S nn)).
    rewrite <- (rec_motive_inst D K).
    rewrite <- (skipn_app_len Us' (vars_from 1 nn) nu HUl'); fold Ps.
    assert (HA3' : forall i, Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn nu Ps) ++ elim_mctx p D Us ++ EK ++ Lm
                               ⊢ rec_motive D (S nn + K) : Typeω@i)
      by (unfold Ps; rewrite (firstn_app_len Us' (vars_from 1 nn) nu HUl'); exact HA3).
    eapply wf_elim with (i := 0); [ exact Hl | | | | reflexivity | apply HA3' | | | | | ].
    - (* the number of parameters *)
      unfold Ps; rewrite List.length_app, HUl', HNl; unfold ind_nn, ind_np in *; lia.
    - (* the parameters, at their types: the uniform ones the module's,
         the non-uniform ones the motive context's variables *)
      assert (Hti' : tele_insts (ind_params D) Id Ps
                     = tele_insts (ind_uparams D) Id Us' ++ tele_insts (ind_nparams D) (sb_of_list Id Us') (vars_from 1 nn)).
      { unfold Ps; rewrite params_split; apply tele_insts_app;
          [ apply (decl_uparams_ass D Hc) | rewrite HUl', length_ind_uparams by exact Hle; reflexivity ]. }
      assert (Hl1 : List.length (tele_insts (ind_uparams D) Id Us') = nu)
        by (rewrite length_tele_insts by apply (decl_uparams_ass D Hc); rewrite HUl', length_ind_uparams by exact Hle; lia).
      intros k P T HP HT; rewrite Hti' in HT; unfold Ps in HP.
      destruct (Nat.lt_ge_cases k nu) as [Hk' | Hk'].
      + rewrite List.nth_error_app1 in HP, HT by lia; exact (HUs3 _ _ _ HP HT).
      + rewrite List.nth_error_app2 in HP, HT by lia; rewrite HUl' in HP; rewrite Hl1 in HT.
        unfold elim_mctx.
        replace (vars_from 1 nn)
          with (vars_from (List.length (ce_ass (apps (a_ind p) (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us ++ vars_from 0 (ind_nn D))) :: nil))
                  (List.length (ind_nparams D))) in HP, HT
          by (rewrite length_nparams; reflexivity).
        eapply (wf_vars_tele_gen _ _ (ce_ass _ :: nil) (ind_nparams D) (sb_of_list Id Us) _ (EK ++ Lm) nu);
          [ apply decl_closed_nparams_ass, Hc | apply (decl_nparams_mvc _ _ _ HD) | apply decl_closed_nparams_scoped, Hc
          | exact HM2 | | exact HP | exact HT ].
        intros y Hy; rewrite HUs'w, sb_of_list_map by lia; cbn [List.length]; rewrite length_nparams; reflexivity.
    - (* the scrutinee: the motive context's innermost variable *)
      assert (Heq : (apps (a_ind p) (List.map (fun U => U[wk_shiftn nn]ʷ) Us ++ vars_from 0 nn))[↑]ʷ = apps (a_ind p) Ps).
      { rewrite apps_exp_wk, List.map_app, List.map_map; cbn [exp_wk]; unfold Ps; f_equal; f_equal.
        - rewrite HUs'w; apply List.map_ext; intros U; rewrite exp_wk_wk; apply exp_wk_wk_eq; intros x; cbn; lia.
        - unfold vars_from; rewrite List.map_map; apply List.map_ext; intros x; cbn; f_equal; lia. }
      apply wf_vlookup; [ exact HM2 |].
      unfold elim_mctx; cbn [List.app]; rewrite <- Heq; constructor.
    - unfold Ps; rewrite (firstn_app_len Us' (vars_from 1 nn) nu HUl').
      apply ctx_ext_refl; [ apply elim_mctx_ass, Hc | exact HM3 ].
    - apply rec_brs_names.
    - intros c gs Hcon; unfold Ps; rewrite (firstn_app_len Us' (vars_from 1 nn) nu HUl').
      destruct (branch_at _ _ _ HE2 Hcon) as [HB _]; rewrite HlE2 in HB; unfold E2 in HB; rewrite <- List.app_assoc in HB.
      apply ctx_ext_refl; [ apply elim_bctx_ass, Hc | exact HB ].
    - intros c gs n B Hcon Hin.
      destruct (rec_brs_in _ _ _ _ _ _ _ Hin) as (cs1 & gs' & cs2 & Hcs & -> & _).
      rewrite (con_in _ _ _ Hcon ltac:(rewrite Hcs; apply List.in_elt)); reflexivity.
    - (* a branch: its branch argument, applied to what the branch binds *)
      intros c gs n B Hcon Hin.
      destruct (rec_brs_in _ _ _ _ _ _ _ Hin) as (cs1 & gs' & cs2 & Hcs & Hn & HB).
      assert (gs' = gs) as -> by (symmetry; apply (con_in _ _ _ Hcon); rewrite Hcs; apply List.in_elt).
      unfold Ps; rewrite (firstn_app_len Us' (vars_from 1 nn) nu HUl').
      set (i := List.length cs1) in *.
      set (bt := ctx_pi (elim_bctx p D gs (rec_motive D i) (rec_uvars D i)) (elim_bty p D c gs (rec_motive D i) (rec_uvars D i))).
      assert (HEK : List.rev (rec_btys p D 0 (ind_cons D))
                    = List.rev (rec_btys p D (S i) cs2) ++ ce_ass bt :: List.rev (rec_btys p D 0 cs1)).
      { rewrite Hcs, rec_btys_app; cbn [rec_btys]; rewrite List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity. }
      assert (HK : K = i + S (List.length cs2)) by (rewrite Hcs, List.length_app; reflexivity).
      pose proof (lookup_mid (elim_mctx p D Us ++ List.rev (rec_btys p D (S i) cs2)) bt (List.rev (rec_btys p D 0 cs1) ++ Lm)) as Hlk.
      rewrite List.length_app, length_elim_mctx, List.length_rev, length_rec_btys in Hlk.
      rewrite <- !List.app_assoc in Hlk; cbn [List.app] in Hlk.
      replace (elim_mctx p D Us ++ List.rev (rec_btys p D (S i) cs2) ++ ce_ass bt :: List.rev (rec_btys p D 0 cs1) ++ Lm)
        with (elim_mctx p D Us ++ EK ++ Lm) in Hlk by (rewrite HEK, <- List.app_assoc; reflexivity).
      unfold bt in Hlk; rewrite ctx_pi_wk in Hlk.
      erewrite elim_bctx_wk in Hlk by (first [ exact Hc | rewrite Hcs; apply List.in_elt | apply length_vars_from ]).
      rewrite length_elim_bctx in Hlk.
      replace (cargs_nrec gs + List.length gs + nn) with (nn + List.length gs + cargs_nrec gs) in Hlk by lia.
      rewrite elim_bty_wk, rec_motive_wk, rec_uvars_wk in Hlk.
      replace (i + S (S nn + List.length cs2)) with (S nn + K) in Hlk by lia.
      fold Us' in Hlk.
      destruct (branch_at _ _ _ HE2 Hcon) as [HBc HBt]; rewrite HlE2 in HBc, HBt; unfold E2 in HBc, HBt;
        rewrite <- List.app_assoc in HBc, HBt.
      pose proof (wf_apps_vars _ _ _ _ _ _ _ (elim_bctx_ass p D gs _ Us' Hc) HBc (HBt 0) (wf_vlookup _ _ _ _ _ HM2 Hlk)) as H.
      rewrite length_elim_bctx in H; cbn [exp_wk] in H.
      rewrite HB, Hn.
      replace (nn + List.length gs + cargs_nrec gs + S nn + (K - 1 - (0 + i)))
        with (wk_shiftn (cargs_nrec gs + List.length gs + nn) (S nn + List.length cs2)) by (cbn; lia).
      replace (nn + List.length gs + cargs_nrec gs) with (cargs_nrec gs + List.length gs + nn) by lia.
      exact H.
  Qed.

  (** The recursor is of its type over the module's parameters. *)
  Lemma rec_typed : Θ ⍮ Ξ ⍮ Γ0 ⊢ rec_fn p D : rec_ty p D.
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

  (** A constructor, applied to the module's parameters, is of its type
      over the non-uniform ones. *)
  Lemma con_gen_typed : forall c gs, ind_con D c = Some gs ->
      Θ ⍮ Ξ ⍮ Γ0 ⊢ apps (a_con p c) (vars_from 0 nu)
        : ctx_pi (ind_nparams D) (ctx_pi (cargs_ctx p D gs) (apps (a_ind p) (ind_pvars D (List.length gs)))).
  Proof.
    intros * Hcon.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    destruct (con_cod_typed _ _ _ _ _ _ HD Hc Hl Hcon) as [j Hj].
    destruct (cargs_ctx_wf _ _ _ _ _ _ HD Hc Hl Hin gs nil (eq_sym (List.app_nil_r gs))) as (HΨ & _ & _).
    destruct (con_ty_typed0 _ _ _ _ _ _ HD Hc Hl Hcon) as [k Hk].
    assert (H0 : ⊢ Θ ⍮ Ξ ⍮ ⋅) by exact (ctx_app_wf_tail _ _ _ _ (eq_ind _ (fun Γ => ⊢ Θ ⍮ Ξ ⍮ Γ) HU _ (eq_sym (List.app_nil_r _)))).
    pose proof (shape_rest_wf' _ _ _ _ _ _ HD Hc Hl Hcon) as Hsh0.
    assert (HM : Θ ⍮ Ξ ⍮ ⋅ ⊢ a_con p c : con_ty p D gs) by (eapply wf_con; eassumption).
    unfold con_ty in HM; rewrite params_split, ctx_pi_app in HM.
    rewrite params_split, List.app_assoc in Hj, HΨ.
    destruct (ctx_pi_wf _ _ _ _ _ _ HΨ Hj) as [j' Hj']; rewrite ctx_pi_app in Hj'.
    assert (HU0 : ⊢ Θ ⍮ Ξ ⍮ Γ0 ++ ⋅) by (rewrite List.app_nil_r; exact HU).
    assert (Hj0 : Θ ⍮ Ξ ⍮ Γ0 ++ ⋅
                    ⊢ ctx_pi (ind_nparams D) (ctx_pi (cargs_ctx p D gs) (apps (a_ind p) (ind_pvars D (List.length gs))))
                    : Typeω@j') by (rewrite List.app_nil_r; exact Hj').
    clear Hj'; rename Hj0 into Hj'.
    pose proof (wf_apps_vars _ _ _ _ _ _ _ (decl_uparams_ass D Hc) HU0 Hj' HM) as H.
    rewrite U_len, List.app_nil_r in H; exact H.
  Qed.
End RecTyped.

(** ** The Generated Definitions Type-Check

    The members are checked one after the other, each with the entry so far
    declared ([wf_gentry_ind_ext]); in the frame with that entry, the
    declaration is the type's, so the recursor and the constructors are of
    their types ([RecTyped]). *)

Section GensRun.
  Variables (Θ : gdeps) (mq : qname) (Δ : ctx) (Φ0 : gmod) (Ξ0 : gstack) (y : string) (pv : bool) (D : ind_decl).
  Hypothesis Hg : ⊢g Θ ⍮ (mq, gu_body Δ Φ0) :: Ξ0.
  Hypothesis Hy : gm_fresh y Φ0.

  #[local] Abbreviation p := (qname_in mq y).
  #[local] Abbreviation fr Φ := ((mq, gu_body Δ (Φ0 ⊳ y ↦ ge_ind pv D Φ)) :: Ξ0).

  Definition gens_inv (Φ : gmod) : Prop := Θ ⍮ (mq, gu_body Δ Φ0) :: Ξ0 ⍮ p ⊢e ge_ind pv D Φ.

  Lemma inv_typed : forall Φ, gens_inv Φ ->
      ind_lookup Θ (fr Φ) p = Some D /\ decl_typed Θ (fr Φ) D /\ decl_closed D /\ ⊢ Θ ⍮ fr Φ ⍮ ind_uparams D.
  Proof.
    intros Φ HE.
    pose proof (add_ind_wf _ ((mq, gu_body Δ Φ0) :: Ξ0) y pv D Φ Hg HE Hy) as Hg'.
    pose proof (ind_lookup_added Θ ((mq, gu_body Δ Φ0) :: Ξ0) y pv D Φ ltac:(discriminate)) as Hl.
    cbn [gs_path gs_add gu_params gu_mod] in Hl, Hg'.
    destruct (decl_of_lookup _ _ ⋅ _ _ ltac:(constructor; exact Hg') Hl) as [HD Hc].
    split; [ exact Hl | split; [ exact HD | split; [ exact Hc | exact (proj1 (decl_typed_uparams _ _ _ HD)) ] ] ].
  Qed.

  Lemma gens_inv_cons : forall cs Φ,
      (forall c gs, In (c, gs) cs -> ind_con D c = Some gs) ->
      NoDup (List.map fst cs) -> ~ In "rec"%string (List.map fst cs) ->
      gens_inv Φ -> (forall c, In c (List.map fst cs) -> gm_fresh c Φ) -> gm_fresh "rec" Φ ->
      gens_inv
        (gens_body Φ (ind_uparams D)
          (List.map (fun cg =>
                       ig_def (fst cg) false
                         (ctx_pi (ind_nparams D)
                            (ctx_pi (cargs_ctx p D (snd cg)) (apps (a_ind p) (ind_pvars D (List.length (snd cg))))))
                         (apps (a_con p (fst cg)) (vars_from 0 (ind_nu D))))
             cs ++ ig_def "rec" false (rec_ty p D) (rec_fn p D) :: nil)).
  Proof.
    induction cs as [| [c gs] cs IH]; intros Φ Hcs Hnd Hrec Hinv Hfr Hfrr; cbn [List.map List.app gens_body].
    - destruct (inv_typed _ Hinv) as (Hl & HD & Hc & HT).
      pose proof (rec_typed _ _ _ _ HD Hc Hl HT) as Hr.
      econstructor; [ exact Hinv | exact Hr | exact Hfrr ].
    - destruct (inv_typed _ Hinv) as (Hl & HD & Hc & HT).
      pose proof (con_gen_typed _ _ _ _ HD Hc Hl HT c gs (Hcs _ _ (or_introl eq_refl))) as Hcg.
      cbn [List.map fst] in Hnd, Hrec, Hfr; inversion Hnd as [| ? ? Hn Hnd']; subst.
      assert (Hfc : gm_fresh c Φ) by (apply Hfr; left; reflexivity).
      apply IH;
        [ intros; apply Hcs; right; assumption | exact Hnd' | intros H; apply Hrec; right; exact H
        | econstructor; [ exact Hinv | exact Hcg | exact Hfc ]
        | intros c' Hc'; unfold gm_fresh; cbn [gm_names fst]; intros [Heq | H]; [ subst c'; exact (Hn Hc') | exact (Hfr c' (or_intror Hc') H) ]
        | unfold gm_fresh; cbn [gm_names fst]; intros [H | H]; [ apply Hrec; left; exact H | exact (Hfrr H) ] ].
  Qed.
End GensRun.

(** What an accepted declaration generates type-checks: its constructors
    and its recursor, each with the members before it declared.  So no
    declaration the other premises of [rc_ind] accept is rejected by its
    generated members; the generated names are the constructors' and
    [rec], which the declaration's own names must leave free ([rec] is a
    keyword, so no source names a constructor so). *)
Theorem ind_gens_typed : forall Θ mq Δ Φ0 Ξ0 y pv D,
    ⊢g Θ ⍮ (mq, gu_body Δ Φ0) :: Ξ0 -> gm_fresh y Φ0 ->
    Θ ⍮ (mq, gu_body Δ Φ0) :: Ξ0 ⍮ qname_in mq y ⊢e ge_ind pv D ⋄ ->
    ~ In "rec"%string (List.map fst (ind_cons D)) ->
    Θ ⍮ (mq, gu_body Δ Φ0) :: Ξ0 ⍮ qname_in mq y ⊢e ge_ind pv D (gen_body (qname_in mq y) D).
Proof.
  intros * Hg Hy HE Hrec.
  destruct (inv_typed _ _ _ _ _ _ _ _ Hg Hy _ HE) as (_ & HD & _).
  pose proof HD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnd & _).
  exact (gens_inv_cons _ _ _ _ _ _ _ _ Hg Hy (ind_cons D) ⋄
           (fun c gs Hin => cons_lookup_nodup _ _ _ Hnd Hin) Hnd Hrec HE
           (fun c _ H => H) (fun H => H)).
Qed.

(** So a declaration whose arguments classify, and whose declaration is
    well formed where it is declared, is run. *)
Corollary rc_ind_runs : forall load_path read to_core ch B Θ Ξ x pv R cs,
    ⊢g Θ ⍮ Ξ -> cls_cons_in Θ Ξ R cs -> gs_fresh x Ξ ->
    Θ ⍮ Ξ ⍮ ind_qname Ξ x ⊢e ge_ind pv (gs_ind Ξ (rd_filed R cs)) ⋄ ->
    ~ In "rec"%string (List.map fst cs) ->
    exists Θ' Ξ', run_cmd load_path read to_core ch B Θ Ξ (cc_ind x pv R) B Θ' Ξ'.
Proof.
  intros * HΞ Hcls Hfr HE Hrec.
  destruct Ξ as [| [mq [Δ [Φ0 | E0]]] Ξ0]; [ contradiction | |].
  - do 2 eexists; eapply rc_ind; [ exact Hcls | exact Hfr |].
    apply ind_gens_typed; [ exact HΞ | exact Hfr | exact HE | exact Hrec ].
  - exfalso; destruct (wf_gstack_cons_inv _ _ _ _ HΞ) as (_ & (Δ' & Φ' & [=] & _) & _).
Qed.
