(** * What a Declaration Generates Type-Checks

    The constructors of each declared member, and the recursor [X.rec] of a
    one-member group, that a declaration generates ([ind_gens]) are terms
    of the types they are declared at, in the member's module's frame: a
    run of an accepted declaration never fails at them ([ind_gens_typed]).  Each is a term of a [Π] over a telescope applied to
    the telescope's variables ([wf_apps_vars]), under [λ]s over the
    recursor's telescope. *)

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
  Proof. intros; apply cons_lookup_nodup; [ exact (dt_nodup _ _ _ HD _ _ HM) | assumption ]. Qed.

  Lemma con_in : forall c gs gs', ind_con M c = Some gs -> In (c, gs') (im_cons M) -> gs = gs'.
  Proof.
    intros * Hcon Hin; apply cons_lookup_in in Hcon.
    pose proof (dt_nodup _ _ _ HD _ _ HM) as Hnd.
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

(** ** The Generated Definitions Type-Check

    The members are checked one after the other, each with the entry so far
    declared ([wf_gentry_ind_ext]); in the frame with that entry, the
    declaration is the type's, so the recursor and the constructors are of
    their types. *)


Section GensRun.
  Variables (Θ : gdeps) (mq : qname) (Δ : ctx) (Φ0 : gmod) (Ξ0 : gstack) (y : string) (pv : bool) (pq : qname)
    (k : nat) (D : ind_decl) (Mk : imember) (pm : qname).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ (mq, gu_body Δ Φ0) :: Ξ0.
  Hypothesis Hy : gm_fresh y Φ0.
  Hypothesis HMk : ind_member D k = Some Mk.
  Hypothesis Hh : im_head Mk = mh_decl pm.
  (** The group is found where its member's entry is filed. *)
  Hypothesis Hlk : forall Φ, ind_lookup Θ ((mq, gu_body Δ (Φ0 ⊳ y ↦ ge_ind pv pq k D Φ)) :: Ξ0) pq = Some D.

  #[local] Abbreviation fr Φ := ((mq, gu_body Δ (Φ0 ⊳ y ↦ ge_ind pv pq k D Φ)) :: Ξ0).

  (** The invariant of generating the member's body: the entry with body
      [Φ] is well formed where it is filed. *)
  Definition gens_inv (Φ : gmod) : Prop := Θ ⍮ (mq, gu_body Δ Φ0) :: Ξ0 ⍮ qname_in mq y ⊢ᵉ ge_ind pv pq k D Φ.

  Lemma inv_typed : forall Φ, gens_inv Φ ->
      ⊢ᵍ Θ ⍮ fr Φ /\ decls_typed Θ (fr Φ) /\ decl_typed Θ (fr Φ) D /\ decl_closed D /\ ⊢ Θ ⍮ fr Φ ⍮ ind_uparams D.
  Proof.
    intros Φ HE.
    pose proof (add_ind_wf _ ((mq, gu_body Δ Φ0) :: Ξ0) y pv pq k D Φ Hg HE Hy) as Hg'.
    cbn [gs_add] in Hg'.
    assert (H0 : ⊢ Θ ⍮ fr Φ ⍮ ⋅) by (constructor; exact Hg').
    destruct (decl_of_lookup _ _ ⋅ _ _ H0 (Hlk Φ)) as [HD Hc].
    exact (conj Hg' (conj (decls_of_ctx _ _ _ H0) (conj HD (conj Hc (proj1 (decl_typed_uparams _ _ _ HD)))))).
  Qed.

  (** The recursor, at a one-member group, after the constructors. *)
  Lemma gens_inv_rec : forall Φ, gens_inv Φ ->
      (ind_has_rec D = true -> gm_fresh "rec" Φ) ->
      gens_inv (gens_body Φ (ind_uparams D) (if ind_has_rec D then ig_def "rec" false (rec_ty pq D Mk) (rec_fn pq D Mk) :: nil else nil)).
  Proof.
    intros Φ Hinv Hfrr; destruct (ind_has_rec D) eqn:Hr; cbn [gens_body]; [| exact Hinv ].
    destruct (inv_typed _ Hinv) as (Hg' & Hds & HD & Hc & HT).
    assert (Hone : ind_members D = Mk :: nil).
    { unfold ind_has_rec in Hr; apply Nat.eqb_eq in Hr.
      unfold ind_member in HMk; destruct (ind_members D) as [| M0 [| M1 Ms]] eqn:Hm; cbn in Hr; try discriminate.
      destruct k as [| k']; cbn in HMk; [ injection HMk as <-; reflexivity | destruct k'; discriminate ]. }
    pose proof (rec_typed _ _ _ _ _ _ Hg' Hds HD Hc (Hlk Φ) Hone Hh HT) as HR.
    econstructor; [ exact Hinv | exact HR | exact (Hfrr eq_refl) ].
  Qed.

  Lemma gens_inv_cons : forall cs Φ,
      (forall c gs, In (c, gs) cs -> ind_con Mk c = Some gs) ->
      NoDup (List.map fst cs) -> (ind_has_rec D = true -> ~ In "rec"%string (List.map fst cs)) ->
      gens_inv Φ -> (forall c, In c (List.map fst cs) -> gm_fresh c Φ) -> (ind_has_rec D = true -> gm_fresh "rec" Φ) ->
      gens_inv
        (gens_body Φ (ind_uparams D)
          (List.map (fun cg =>
                       ig_def (fst cg) false
                         (ctx_pi (im_nparams Mk)
                            (ctx_pi (cargs_ctx pq D Mk (snd cg)) (apps (a_ind pq k) (ind_pvars D Mk (List.length (snd cg))))))
                         (apps (a_con pq k (fst cg)) (vars_from 0 (ind_nu D))))
             cs ++ (if ind_has_rec D then ig_def "rec" false (rec_ty pq D Mk) (rec_fn pq D Mk) :: nil else nil))).
  Proof.
    induction cs as [| [c gs] cs IH]; intros Φ Hcs Hnd Hrec Hinv Hfr Hfrr; cbn [List.map List.app].
    - exact (gens_inv_rec Φ Hinv Hfrr).
    - destruct (inv_typed _ Hinv) as (Hg' & Hds & HD & Hc & HT).
      pose proof (con_gen_typed _ _ _ _ _ _ _ _ _ Hg' Hds HD Hc (Hlk Φ) HMk Hh HT (Hcs _ _ (or_introl eq_refl))) as Hcg.
      cbn [List.map fst] in Hnd, Hrec, Hfr; inversion Hnd as [| ? ? Hn Hnd']; subst.
      assert (Hfc : gm_fresh c Φ) by (apply Hfr; left; reflexivity).
      cbn [gens_body]; apply IH;
        [ intros; apply Hcs; right; assumption | exact Hnd' | intros Hr H; apply (Hrec Hr); right; exact H
        | econstructor; [ exact Hinv | exact Hcg | exact Hfc ]
        | intros c' Hc'; unfold gm_fresh; cbn [gm_names fst]; intros [Heq | H]; [ subst c'; exact (Hn Hc') | exact (Hfr c' (or_intror Hc') H) ]
        | intros Hr; unfold gm_fresh; cbn [gm_names fst]; intros [H | H]; [ apply (Hrec Hr); left; exact H | exact (Hfrr Hr H) ] ].
  Qed.
End GensRun.

(** The group is found where the entry of a declared member is filed: at
    the first member, the entry itself; at a later one, the first member's
    entry before it. *)
Lemma gentry_ind_lookup : forall Θ mq Δ Φ0 Ξ0 y pv pq k D,
    ⊢ᵍ Θ ⍮ (mq, gu_body Δ Φ0) :: Ξ0 -> gm_fresh y Φ0 ->
    Θ ⍮ (mq, gu_body Δ Φ0) :: Ξ0 ⍮ qname_in mq y ⊢ᵉ ge_ind pv pq k D ⋄ ->
    forall Φ, ind_lookup Θ ((mq, gu_body Δ (Φ0 ⊳ y ↦ ge_ind pv pq k D Φ)) :: Ξ0) pq = Some D.
Proof.
  intros * Hg Hy HE Φ; inversion HE; subst.
  - change ((mq, gu_body Δ (Φ0 ⊳ y ↦ ge_ind pv (qname_in mq y) 0 D Φ)) :: Ξ0)
      with (gs_add y (ge_ind pv (qname_in (gs_path ((mq, gu_body Δ Φ0) :: Ξ0)) y) 0 D Φ) ((mq, gu_body Δ Φ0) :: Ξ0)).
    apply ind_lookup_added; discriminate.
  - eapply (ind_lookup_add _ ((mq, gu_body Δ Φ0) :: Ξ0) y); [ exact Hg | exact Hy | eassumption ].
Qed.

(** What an accepted declaration generates for each declared member
    type-checks: its constructors, and the recursor of a one-member group,
    each with the members before it declared.  The generated names are the
    constructors' and [rec], which the declaration's own names must leave
    free ([rec] is a keyword, so no source names a constructor so). *)
Theorem ind_gens_typed : forall Θ mq Δ Φ0 Ξ0 y pv pq k D Mk pm,
    ⊢ᵍ Θ ⍮ (mq, gu_body Δ Φ0) :: Ξ0 -> gm_fresh y Φ0 ->
    Θ ⍮ (mq, gu_body Δ Φ0) :: Ξ0 ⍮ qname_in mq y ⊢ᵉ ge_ind pv pq k D ⋄ ->
    ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
    (ind_has_rec D = true -> ~ In "rec"%string (List.map fst (im_cons Mk))) ->
    Θ ⍮ (mq, gu_body Δ Φ0) :: Ξ0 ⍮ qname_in mq y ⊢ᵉ ge_ind pv pq k D (gen_body pq D k Mk).
Proof.
  intros * Hg Hy HE HMk Hh Hrec.
  pose proof (gentry_ind_lookup _ _ _ _ _ _ _ _ _ _ Hg Hy HE) as Hlk.
  destruct (inv_typed _ _ _ _ _ _ _ _ _ _ Hg Hy Hlk _ HE) as (_ & _ & HD & _).
  pose proof (dt_nodup _ _ _ HD _ _ HMk) as Hnd.
  exact (gens_inv_cons _ _ _ _ _ _ _ _ _ _ _ _ Hg Hy HMk Hh Hlk (im_cons Mk) ⋄
           (fun c gs Hin => cons_lookup_nodup _ _ _ Hnd Hin) Hnd Hrec HE
           (fun c _ H => H) (fun _ H => H)).
Qed.

(** ** A Declaration Runs

    The declared members of a filed group are its first ones, each named
    after its raw member ([rms_filed]); the views after them. *)
Lemma rms_filed_heads : forall Ξ n Vs ms css Ms, rms_filed Ξ n Vs ms css = Some Ms ->
    List.length Ms = List.length ms /\
    forall i M, List.nth_error Ms i = Some M ->
      exists Mr, List.nth_error ms i = Some Mr /\ im_head M = mh_decl (ind_qname Ξ (rm_name Mr)).
Proof.
  induction ms as [| Mr ms IH]; intros [| cs css] Ms H; cbn in H; try discriminate.
  - injection H as <-; split; [ reflexivity | intros [] ? [=] ].
  - destruct (rcons_num n Vs cs) as [cs' |]; [| discriminate ].
    destruct (rms_filed Ξ n Vs ms css) as [Ms' |] eqn:E; [| discriminate ].
    injection H as <-; destruct (IH _ _ E) as [Hl Hh].
    split; [ cbn; rewrite Hl; reflexivity |].
    intros [| i] M HM; cbn in HM; [ injection HM as <-; exists Mr; split; reflexivity | exact (Hh _ _ HM) ].
Qed.

Lemma rvs_filed_views : forall Θ Ξ σ n Vs xs Ss css Nvs Ms, rvs_filed Θ Ξ σ n Vs xs Ss css Nvs = Some Ms ->
    forall M, In M Ms -> im_is_decl M = false.
Proof.
  induction xs as [| x xs IH]; intros [| ss Ss] [| cs css] [| Nv Nvs] Ms H; cbn in H; try discriminate.
  - injection H as <-; intros M [].
  - destruct (rv_filed Θ Ξ σ n Vs x ss cs Nv) as [M0 |] eqn:E0; [| discriminate ].
    destruct (rvs_filed Θ Ξ σ n Vs xs Ss css Nvs) as [Ms' |] eqn:E; [| discriminate ].
    injection H as <-; intros M [<- | HM]; [| exact (IH _ _ _ _ E _ HM) ].
    unfold rv_filed in E0; destruct x as [[qc k] Cs].
    destruct (ind_lookup Θ Ξ qc) as [D' |]; [| discriminate ].
    destruct (ind_member D' k), (rcons_num n Vs cs); try discriminate.
    injection E0 as <-; reflexivity.
Qed.


Lemma filter_all_true : forall {X} (f : X -> bool) l, (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof. induction l as [| x l IH]; intros H; cbn; [ reflexivity |]; rewrite (H x (or_introl eq_refl)), IH; auto with datatypes. Qed.

Lemma filter_all_false : forall {X} (f : X -> bool) l, (forall x, In x l -> f x = false) -> List.filter f l = nil.
Proof. induction l as [| x l IH]; intros H; cbn; [ reflexivity |]; rewrite (H x (or_introl eq_refl)), IH; auto with datatypes. Qed.

Lemma rd_filed_decl : forall Θ Ξ R Vs Ss csD csV Nvs D, rd_filed Θ Ξ R Vs Ss csD csV Nvs = Some D ->
    ind_ndecl D = List.length (rd_members R) /\
    forall i Mr, List.nth_error (rd_members R) i = Some Mr ->
      exists M, ind_member D i = Some M /\ im_head M = mh_decl (ind_qname Ξ (rm_name Mr)).
Proof.
  intros * H; unfold rd_filed in H; destruct (rd_members R) as [| Mr0 Mrs] eqn:HR; [ discriminate |].
  destruct (rms_filed _ _ _ _ _) as [Ms |] eqn:E1; [| discriminate ].
  destruct (rvs_filed _ _ _ _ _ _ _ _ _) as [Mv |] eqn:E2; [| discriminate ].
  injection H as <-; destruct (rms_filed_heads _ _ _ _ _ _ E1) as [Hl Hh].
  pose proof (rvs_filed_views _ _ _ _ _ _ _ _ _ _ E2) as Hv.
  split.
  - unfold ind_ndecl; cbn [ind_members]; rewrite List.filter_app, (filter_all_false _ Mv Hv), List.app_nil_r.
    rewrite filter_all_true; [ exact Hl |].
    intros M HM; destruct (List.In_nth_error _ _ HM) as [i Hi].
    destruct (Hh _ _ Hi) as (Mr & _ & Hhd); unfold im_is_decl; rewrite Hhd; reflexivity.
  - intros i Mr Hi.
    assert (Hlt : i < List.length Ms) by (rewrite Hl; apply List.nth_error_Some; congruence).
    destruct (List.nth_error Ms i) as [M |] eqn:HM; [| apply List.nth_error_None in HM; lia ].
    destruct (Hh _ _ HM) as (Mr' & Hi' & Hhd); rewrite Hi in Hi'; injection Hi' as <-.
    exists M; split; [ unfold ind_member; cbn [ind_members]; rewrite List.nth_error_app1 by exact Hlt; exact HM | exact Hhd ].
Qed.

(** The later declared members' entries, each after the ones before it,
    the first one's entry already filed in the frame. *)
Section EntriesRun.
  Variables (Θ : gdeps) (mq : qname) (Δ : ctx) (Ξ0 : gstack) (pv : bool) (y0 : string) (D : ind_decl) (Φm : gmod).
  #[local] Abbreviation pq := (qname_in mq y0).
  Hypothesis Hup : exists Δu, ind_uparams D = Δu ++ Δ ++ gs_tele Ξ0.
  Hypothesis Hass : tele_ass (ind_uparams D).

  Lemma entries_from : forall xs k Φ, ⊢ᵍ Θ ⍮ (mq, gu_body Δ Φ) :: Ξ0 -> 0 < k ->
      gm_entry Φ (y0 :: nil) = Some (ge_ind pv pq 0 D Φm) ->
      ind_lookup Θ ((mq, gu_body Δ Φ) :: Ξ0) pq = Some D ->
      List.NoDup xs -> ~ In y0 xs -> (forall x, In x xs -> gm_fresh x Φ) ->
      (forall i x, List.nth_error xs i = Some x ->
         exists Mi, ind_member D (k + i) = Some Mi /\ im_head Mi = mh_decl (qname_in mq x)) ->
      k + List.length xs <= ind_ndecl D ->
      exists Ξ', ind_entries_run Θ pv pq D k xs ((mq, gu_body Δ Φ) :: Ξ0) Ξ'.
  Proof.
    induction xs as [| x xs IH]; intros k Φ Hg Hk He Hl Hnd Hy0 Hfr Hm Hle; [ eexists; constructor |].
    inversion Hnd as [| ? ? Hnx Hnd']; subst.
    destruct (Hm 0 x eq_refl) as (Mi & HMi & Hhi); rewrite Nat.add_0_r in HMi.
    assert (Hfx : gm_fresh x Φ) by (apply Hfr; left; reflexivity).
    assert (HD : decl_typed Θ ((mq, gu_body Δ Φ) :: Ξ0) D)
      by (exact (proj1 (decl_of_lookup _ _ ⋅ _ _ ltac:(constructor; exact Hg) Hl))).
    destruct Hup as [Δu HΔu].
    assert (HB : Θ ⍮ (mq, gu_body Δ Φ) :: Ξ0 ⍮ qname_in mq x ⊢ᵉ ge_ind pv pq k D ⋄).
    { eapply wf_gentry_ind_mem_nil with (pv0 := pv) (Φm := Φm) (Δu := Δu);
        [ exact HΔu | exact Hass | exact (dt_uparams _ _ _ HD) | exact He | exact Hl | exact HMi | exact Hk
        | cbn in Hle; lia | exact Hhi ]. }
    assert (Hrec : ind_has_rec D = true -> ~ In "rec"%string (List.map fst (im_cons Mi))).
    { intros Hr; exfalso; unfold ind_has_rec in Hr; apply Nat.eqb_eq in Hr.
      unfold ind_member in HMi.
      assert (k < List.length (ind_members D)) by (apply List.nth_error_Some; congruence); lia. }
    pose proof (ind_gens_typed _ _ _ _ _ _ _ _ _ _ _ _ Hg Hfx HB HMi Hhi Hrec) as HE.
    pose proof (add_ind_wf _ ((mq, gu_body Δ Φ) :: Ξ0) x pv pq k D _ Hg HE Hfx) as Hg'; cbn [gs_add] in Hg'.
    destruct (IH (S k) (Φ ⊳ x ↦ ge_ind pv pq k D (gen_body pq D k Mi))) as (Ξ' & Hrun).
    { exact Hg'. }
    { lia. }
    { cbn; destruct (String.eqb_spec y0 x) as [-> | _]; [ exfalso; apply Hy0; left; reflexivity | exact He ]. }
    { exact (ind_lookup_add _ ((mq, gu_body Δ Φ) :: Ξ0) x _ _ _ Hg Hfx Hl). }
    { exact Hnd'. }
    { intros H; apply Hy0; right; exact H. }
    { intros x' Hx'; unfold gm_fresh; cbn [gm_names]; intros [Heq | Hin]; [ subst x'; exact (Hnx Hx') | exact (Hfr x' (or_intror Hx') Hin) ]. }
    { intros i x' Hi; destruct (Hm (S i) x' Hi) as (Mi' & H1 & H2); exists Mi'; split; [ rewrite <- H1; f_equal; lia | exact H2 ]. }
    { cbn in Hle; lia. }
    exists Ξ'; econstructor; [ exact HMi | exact Hfx | exact HE | exact Hrun ].
  Qed.
End EntriesRun.

(** The entries of a group filed ([rd_filed]) and well formed at its
    views' instances read back ([ind_nil_at]), each declared member's
    under its own fresh name, with its generated members: each is filed
    after the ones before it. *)
Lemma ind_entries_exist : forall Θ Ξ pv R Mr0 Mrs csD Vs Ss csV Nvs D,
    ⊢ᵍ Θ ⍮ Ξ ->
    rd_members R = Mr0 :: Mrs ->
    rd_filed Θ Ξ R Vs Ss csD csV Nvs = Some D ->
    List.NoDup (List.map rm_name (rd_members R)) ->
    Forall (fun Mr => gs_fresh (rm_name Mr) Ξ) (rd_members R) ->
    ind_nil_at Θ Ξ (ind_qname Ξ (rm_name Mr0)) D (grp_self_insts (ind_qname Ξ (rm_name Mr0)) D) ->
    (forall M, ind_member D 0 = Some M -> ind_has_rec D = true -> ~ In "rec"%string (List.map fst (im_cons M))) ->
    exists Ξ', ind_entries_run Θ pv (ind_qname Ξ (rm_name Mr0)) D 0 (List.map rm_name (rd_members R)) Ξ Ξ'.
Proof.
  intros * HΞ HR Hfil Hnd Hfr Hnil Hrec.
  pose proof (ind_nil_at_entry _ _ _ _ _ Hnil pv) as HE.
  destruct (rd_filed_decl _ _ _ _ _ _ _ _ _ Hfil) as [Hnde Hheads].
  destruct (Hheads 0 Mr0 ltac:(rewrite HR; reflexivity)) as (M0 & HM0 & Hh0).
  assert (Hfx0 : gs_fresh (rm_name Mr0) Ξ) by (rewrite HR in Hfr; inversion Hfr; assumption).
  destruct Ξ as [| [mq [Δ [sm Φ0 | E0]]] Ξ0]; [ cbn in Hfx0; contradiction | |].
  2: { exfalso; destruct (wf_gstack_cons_inv _ _ _ _ HΞ) as (_ & [Δ' Φ' [=] _] & _). }
  destruct (wf_gstack_cons_inv _ _ _ _ HΞ) as (_ & [Δ' Φ' Heq _] & _); injection Heq; intros; subst.
  rewrite HR in Hnd, Hfr; cbn [List.map] in Hnd; inversion Hnd as [| ? ? Hn0 Hnd']; subst.
  inversion Hfr as [| ? ? Hf0 Hfr']; subst.
  set (y0 := rm_name Mr0) in *.
  unfold ind_qname in *; cbn [gs_path] in *.
  pose proof (ind_gens_typed _ _ _ _ _ _ _ _ _ _ _ _ HΞ Hf0 HE HM0 Hh0 (Hrec M0 HM0)) as HE0.
  pose proof (add_ind_wf _ ((mq, gu_body Δ' Φ') :: Ξ0) y0 pv _ 0 D _ HΞ HE0 Hf0) as Hg1; cbn [gs_add] in Hg1.
  assert (Hup : exists Δu, ind_uparams D = Δu ++ Δ' ++ gs_tele Ξ0) by (inversion HE; subst; eexists; eassumption).
  assert (Hass : tele_ass (ind_uparams D)) by (inversion HE; subst; assumption).
  destruct (entries_from Θ mq Δ' Ξ0 pv y0 D (gen_body (qname_in mq y0) D 0 M0) Hup Hass (List.map rm_name Mrs) 1
              (Φ' ⊳ y0 ↦ ge_ind pv (qname_in mq y0) 0 D (gen_body (qname_in mq y0) D 0 M0)))
    as (Ξ' & Hrun).
  - exact Hg1.
  - lia.
  - cbn; rewrite String.eqb_refl; reflexivity.
  - change ((mq, gu_body Δ' (Φ' ⊳ y0 ↦ ge_ind pv (qname_in mq y0) 0 D (gen_body (qname_in mq y0) D 0 M0))) :: Ξ0)
      with (gs_add y0 (ge_ind pv (qname_in (gs_path ((mq, gu_body Δ' Φ') :: Ξ0)) y0) 0 D (gen_body (qname_in mq y0) D 0 M0))
              ((mq, gu_body Δ' Φ') :: Ξ0)).
    apply ind_lookup_added; discriminate.
  - exact Hnd'.
  - exact Hn0.
  - intros x Hx; apply List.in_map_iff in Hx as (Mr & <- & HMr).
    pose proof (proj1 (List.Forall_forall _ _) Hfr' Mr HMr) as Hf; cbn in Hf.
    unfold gm_fresh; cbn [gm_names]; intros [Heq0 | Hin]; [| exact (Hf Hin) ].
    apply Hn0; rewrite Heq0; apply List.in_map; exact HMr.
  - intros i x Hi; rewrite List.nth_error_map in Hi.
    destruct (List.nth_error Mrs i) as [Mr |] eqn:HMr; cbn in Hi; [ injection Hi as <- | discriminate ].
    destruct (Hheads (S i) Mr ltac:(rewrite HR; exact HMr)) as (Mi & HMi & Hhi).
    exists Mi; split; [ exact HMi | exact Hhi ].
  - rewrite Hnde, HR, List.length_map; cbn; lia.
  - eexists; rewrite HR; cbn [List.map]; unfold ind_qname; cbn [gs_path].
    econstructor; [ exact HM0 | exact Hf0 | exact HE0 | exact Hrun ].
Qed.

(** So a declaration whose members classify, whose views are found and
    classified, and whose group is well formed where it is declared, at
    its views' instances read back ([ind_nil_at]), is
    run: each declared member's entry, with its generated members, is
    filed after the ones before it.  The generated names are the
    constructors' and [rec], which the declaration's own names must leave
    free.  The recursor module of a [mutual T] group ([rec_cmds]), if it
    runs after the entries, completes the run. *)
Corollary rc_ind_runs : forall load_path read to_core ch B Rb Θ Ξ pv R Mr0 Mrs csD Vs Ss csV Nvs D,
    ⊢ᵍ Θ ⍮ Ξ ->
    rd_members R = Mr0 :: Mrs ->
    Forall (fun Mr => rm_sort Mr = rm_sort Mr0) Mrs ->
    Forall2 (rm_cls Θ Ξ R) (rd_members R) csD ->
    Forall2 (view_sibs Θ Ξ R) Vs Ss ->
    Forall2 (view_cls Θ Ξ R) Vs csV ->
    Forall2 (view_nps Θ Ξ R) Vs Nvs ->
    views_bfs (sibs_tbl Vs Ss) (meets_tbl Vs csV) nil (List.concat (List.map rcons_views csD)) Vs ->
    rd_filed Θ Ξ R Vs Ss csD csV Nvs = Some D ->
    List.NoDup (List.map rm_name (rd_members R)) ->
    Forall (fun Mr => gs_fresh (rm_name Mr) Ξ) (rd_members R) ->
    ind_nil_at Θ Ξ (ind_qname Ξ (rm_name Mr0)) D (grp_self_insts (ind_qname Ξ (rm_name Mr0)) D) ->
    (forall M, ind_member D 0 = Some M -> ind_has_rec D = true -> ~ In "rec"%string (List.map fst (im_cons M))) ->
    (forall Ξ', ind_entries_run Θ pv (ind_qname Ξ (rm_name Mr0)) D 0 (List.map rm_name (rd_members R)) Ξ Ξ' ->
       exists B' Rb' Θ' Ξ'',
         Θ ⍮ Ξ' ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ rec_cmds Θ Ξ' R (ind_qname Ξ (rm_name Mr0)) D ⇝* Θ' ⍮ Ξ'' ⍮ B' ⍮ Rb') ->
    exists B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_ind pv R ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'.
Proof.
  intros * HΞ HR Hsort Hcls Hsibs Hvcls Hvnps Hbfs Hfil Hnd Hfr Hnil Hrec Hrc.
  destruct (ind_entries_exist Θ Ξ pv R Mr0 Mrs csD Vs Ss csV Nvs D HΞ HR Hfil Hnd Hfr Hnil Hrec) as [Ξ' Hrun].
  destruct (Hrc _ Hrun) as (B' & Rb' & Θ' & Ξ'' & Hr).
  do 4 eexists; eapply rc_ind; eassumption.
Qed.
