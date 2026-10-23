(** * The Functions of a Recursor Module Type-Check

    The functions [rec_<member>] of the recursor module [Rec] a group
    generates ([grec_mod_cmd]) are of their types in the module's
    telescope ([grec_tele]): each is the group's eliminator at its member,
    at the motives, of branches that are the cases applied to what they
    bind ([grec_fn_typed]). *)

From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import SystemOpt.
From Mctt.Core.Syntactic.System Require Import Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing Syntax.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Core.Syntactic.System.Inductives Require Import Runs.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** The Telescope of a Recursor Module

    The group [D] at [p], its uniform parameters [Γ0].  Over [Γ0]: the
    level; one motive per member, the member [i]'s type [grec_mty i Mi]
    under the [i] motives before it; then one case per constructor of
    each member, the [k]-th under the [k] before it ([grec_case_tys]).
    The function of each member is the group's eliminator at it. *)
Section GrecTyped.
  Variables (Θ : gdeps) (Ξ : gstack) (p : qname) (D : ind_decl).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.
  Hypothesis Hds : decls_typed Θ Ξ.
  Hypothesis HD : decl_typed Θ Ξ D.
  Hypothesis Hc : decl_closed D.
  Hypothesis Hl : ind_lookup Θ Ξ p = Some D.
  Hypothesis HU : ⊢ Θ ⍮ Ξ ⍮ ind_uparams D.

  #[local] Abbreviation Γ0 := (ind_uparams D).
  #[local] Abbreviation nu := (ind_nu D).
  #[local] Abbreviation N := (List.length (ind_members D)).
  #[local] Abbreviation L1 := (ce_ass (a_level 0) :: ind_uparams D).

  (** The type of the motive of the member [i], [Mi], under the [i]
      motives before it and the level. *)
  Definition grec_mty (i : nat) (Mi : imember) : typ :=
    ctx_pi (elim_mctx p D i Mi (vars_from (S i) (ind_nu D))) (a_univ (a_var (S (im_nn Mi) + i))).

  Lemma guvars_mctx : forall j Mj Φ, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ Φ ++ Γ0 ->
      ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj (vars_from (List.length Φ) nu) ++ Φ ++ Γ0.
  Proof.
    intros * HMj HΦ; eapply elim_mctx_wf; [ exact Hg | exact Hds | exact Hl | exact HMj | exact HΦ | apply length_vars_from
                                           | apply (uvars_typed _ _ _ HD Hc), HΦ ].
  Qed.

  Lemma gmty_typed : forall i Mi E, ind_member D i = Some Mi -> List.length E = i -> ⊢ Θ ⍮ Ξ ⍮ E ++ L1 ->
      exists j, Θ ⍮ Ξ ⍮ E ++ L1 ⊢ grec_mty i Mi : Typeω@j.
  Proof.
    intros * HMi HE HEw.
    assert (HΦ : ⊢ Θ ⍮ Ξ ⍮ (E ++ ce_ass (a_level 0) :: nil) ++ Γ0) by (rewrite <- List.app_assoc; exact HEw).
    pose proof (guvars_mctx _ _ _ HMi HΦ) as HMc.
    rewrite <- List.app_assoc in HMc; cbn [List.app] in HMc.
    rewrite List.length_app, HE in HMc; cbn [List.length] in HMc; rewrite Nat.add_1_r in HMc.
    assert (Hb : Θ ⍮ Ξ ⍮ elim_mctx p D i Mi (vars_from (S i) nu) ++ E ++ L1 ⊢ a_univ (a_var (S (im_nn Mi) + i)) : Typeω@0).
    { apply univ_large.
      replace (S (im_nn Mi) + i) with (List.length (elim_mctx p D i Mi (vars_from (S i) nu) ++ E))
        by (rewrite List.length_app, length_elim_mctx, HE; reflexivity).
      rewrite List.app_assoc in HMc |- *; apply level_var; exact HMc. }
    destruct (ctx_pi_wf _ _ _ _ _ _ HMc Hb) as [j Hj]; exists j; exact Hj.
  Qed.

  (** The motives' types of the members [ms], from the member [a] on. *)
  Definition gmtys_from (a : nat) (ms : list imember) : ctx :=
    List.map (fun iM => ce_ass (grec_mty (fst iM) (snd iM))) (List.combine (List.seq a (List.length ms)) ms).

  Lemma grec_motive_tys_from : grec_motive_tys p D = gmtys_from 0 (ind_members D).
  Proof. reflexivity. Qed.

  Lemma gmtys_wf : forall ms a E, (forall j M, List.nth_error ms j = Some M -> ind_member D (a + j) = Some M) ->
      List.length E = a -> ⊢ Θ ⍮ Ξ ⍮ E ++ L1 -> ⊢ Θ ⍮ Ξ ⍮ List.rev (gmtys_from a ms) ++ E ++ L1.
  Proof.
    induction ms as [| M ms IH]; intros a E Hms HE HEw; [ exact HEw |].
    unfold gmtys_from; cbn [List.length List.seq List.combine List.map List.rev fst snd].
    rewrite <- List.app_assoc; cbn [List.app].
    destruct (gmty_typed a M E ltac:(rewrite <- (Nat.add_0_r a); exact (Hms 0 M eq_refl)) HE HEw) as [j Hj].
    apply (IH (S a) (ce_ass (grec_mty a M) :: E)); [| cbn; rewrite HE; reflexivity | eapply wf_ctx_extend; exact Hj ].
    intros j' M' Hj'; rewrite Nat.add_succ_comm; exact (Hms (S j') M' Hj').
  Qed.

  #[local] Abbreviation MT := (List.rev (grec_motive_tys p D) ++ L1).

  Lemma MT_wf : ⊢ Θ ⍮ Ξ ⍮ MT.
  Proof.
    rewrite grec_motive_tys_from; apply (gmtys_wf _ 0 nil); [ intros; assumption | reflexivity |].
    cbn; eapply wf_ctx_extend; apply (wf_level_large (i := 0)); exact HU.
  Qed.

  Lemma length_gmtys : forall a ms, List.length (gmtys_from a ms) = List.length ms.
  Proof. intros; unfold gmtys_from; rewrite List.length_map, List.length_combine, List.length_seq; lia. Qed.
  Lemma gmtys_split : forall ms a j Mj, List.nth_error ms j = Some Mj ->
      gmtys_from a ms = gmtys_from a (List.firstn j ms) ++ ce_ass (grec_mty (a + j) Mj) :: gmtys_from (S (a + j)) (List.skipn (S j) ms).
  Proof.
    induction ms as [| M ms IH]; intros a [| j] Mj Hj; cbn in Hj; try discriminate.
    - injection Hj as <-; unfold gmtys_from; cbn; rewrite Nat.add_0_r; reflexivity.
    - unfold gmtys_from in *; cbn [List.firstn List.skipn List.length List.seq List.combine List.map List.app].
      rewrite (IH (S a) j Mj Hj); rewrite Nat.add_succ_r; reflexivity.
  Qed.

  (** The motive of the member [j] in the motives' telescope, the [j]
      before it and the [N - 1 - j] after it. *)
  Lemma MT_split : forall j Mj, ind_member D j = Some Mj ->
      exists X Z, MT = Z ++ ce_ass (grec_mty j Mj) :: X ++ L1 /\ List.length X = j /\ List.length Z = N - 1 - j.
  Proof.
    intros * HMj; unfold ind_member in HMj.
    rewrite grec_motive_tys_from, (gmtys_split _ 0 j Mj HMj), List.rev_app_distr; cbn [List.rev].
    exists (List.rev (gmtys_from 0 (List.firstn j (ind_members D)))), (List.rev (gmtys_from (S j) (List.skipn (S j) (ind_members D)))).
    rewrite <- !List.app_assoc; cbn [List.app]; split; [ reflexivity |].
    assert (Hlt : j < N) by (apply List.nth_error_Some; congruence).
    rewrite !List.length_rev, !length_gmtys, List.length_firstn, List.length_skipn; split; lia.
  Qed.
  Lemma length_MT_motives : List.length (List.rev (grec_motive_tys p D)) = N.
  Proof. rewrite List.length_rev, grec_motive_tys_from, length_gmtys; reflexivity. Qed.

  (** The motive of the member [j], under [E] past the motives and the
      motive's own context at the group's uniform parameters. *)
  Lemma gmotive_at : forall E j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ E ++ MT ->
      ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj (grec_uvars D N (List.length E)) ++ E ++ MT /\
      forall i, Θ ⍮ Ξ ⍮ elim_mctx p D j Mj (grec_uvars D N (List.length E)) ++ E ++ MT
                  ⊢ grec_motive N j Mj (List.length E) : Typeω@i.
  Proof.
    intros E j Mj HMj HE.
    assert (HΦ : ⊢ Θ ⍮ Ξ ⍮ (E ++ List.rev (grec_motive_tys p D) ++ ce_ass (a_level 0) :: nil) ++ Γ0)
      by (rewrite <- !List.app_assoc; exact HE).
    pose proof (guvars_mctx _ _ _ HMj HΦ) as HMc.
    rewrite <- !List.app_assoc in HMc; cbn [List.app] in HMc.
    replace (vars_from (List.length (E ++ List.rev (grec_motive_tys p D) ++ ce_ass (a_level 0) :: nil)) nu)
      with (grec_uvars D N (List.length E)) in HMc
      by (unfold grec_uvars; rewrite !List.length_app, length_MT_motives; cbn [List.length]; f_equal; lia).
    split; [ exact HMc |].
    intros i.
    destruct (MT_split _ _ HMj) as (X & Z & HMT & HX & HZ).
    assert (Hlt : j < N) by (unfold ind_member in HMj; apply List.nth_error_Some; congruence).
    set (nn := im_nn Mj).
    (* the motive's variable, of the motive's type moved past [E] and the
       later motives *)
    assert (Hv : Θ ⍮ Ξ ⍮ E ++ MT ⊢ #(List.length E + (N - 1 - j))
                   : ctx_pi (elim_mctx p D j Mj (grec_uvars D N (List.length E)))
                       (a_univ (a_var (S nn + (List.length E + N))))).
    { pose proof (lookup_mid (E ++ Z) (grec_mty j Mj) (X ++ L1)) as H.
      unfold grec_mty in H; rewrite ctx_pi_wk in H.
      rewrite elim_mctx_wk, vars_from_wk_shiftn in H by (first [ exact Hc | exact HMj | apply length_vars_from ]).
      rewrite length_elim_mctx in H; cbn [exp_wk] in H; rewrite wk_qn_ge in H by lia.
      rewrite List.length_app, HZ in H.
      rewrite HMT, List.app_assoc.
      replace (S j + S (List.length E + (N - 1 - j))) with (List.length E + N + 1) in H by lia.
      replace (wk_shiftn (S (List.length E + (N - 1 - j))) (S nn + j - S nn) + S nn) with (S nn + (List.length E + N)) in H
        by (cbn; lia).
      subst nn.
      replace (wk_shiftn (S (List.length E + (N - 1 - j))) (S (im_nn Mj) + j - S (im_nn Mj)) + S (im_nn Mj))
        with (S (im_nn Mj) + (List.length E + N)) in H by (cbn; lia).
      apply wf_vlookup; [ rewrite <- List.app_assoc, <- HMT; exact HE | exact H ]. }
    assert (Hlv : Θ ⍮ Ξ ⍮ elim_mctx p D j Mj (grec_uvars D N (List.length E)) ++ E ++ MT
                    ⊢ a_var (S nn + (List.length E + N)) : Level@0).
    { replace (elim_mctx p D j Mj (grec_uvars D N (List.length E)) ++ E ++ MT)
        with ((elim_mctx p D j Mj (grec_uvars D N (List.length E)) ++ E ++ List.rev (grec_motive_tys p D)) ++ ce_ass (a_level 0) :: Γ0)
        by (rewrite <- !List.app_assoc; reflexivity).
      replace (S nn + (List.length E + N))
        with (List.length (elim_mctx p D j Mj (grec_uvars D N (List.length E)) ++ E ++ List.rev (grec_motive_tys p D)))
        by (rewrite !List.length_app, length_elim_mctx, length_MT_motives; cbn; lia).
      apply level_var; rewrite <- !List.app_assoc; exact HMc. }
    pose proof (wf_apps_vars _ _ _ _ _ _ _ (elim_mctx_ass p D j Mj _ Hc HMj) HMc (univ_large _ _ _ _ i Hlv) Hv) as H.
    rewrite length_elim_mctx in H; cbn [exp_wk] in H.
    unfold grec_motive.
    replace (a_var (S (im_nn Mj) + List.length E + (N - 1 - j))) with (a_var (wk_shiftn (S nn) (List.length E + (N - 1 - j))))
      by (cbn; f_equal; lia).
    eapply (wf_exp_suniv_large (n := 0)); [ exact Hlv | exact H ].
  Qed.
  Lemma nth_error_combine_seq : forall {X} (ms : list X) a j,
      List.nth_error (List.combine (List.seq a (List.length ms)) ms) j = option_map (fun M => (a + j, M)) (List.nth_error ms j).
  Proof.
    induction ms as [| M ms IH]; intros a [| j]; cbn; [ reflexivity | reflexivity | rewrite Nat.add_0_r; reflexivity |].
    rewrite IH; destruct (List.nth_error ms j); cbn; [ rewrite Nat.add_succ_r; reflexivity | reflexivity ].
  Qed.

  Lemma nth_grec_motives : forall k j Mj, ind_member D j = Some Mj -> List.nth j (grec_motives D k) a_True = grec_motive N j Mj k.
  Proof.
    intros * HMj; unfold grec_motives.
    apply List.nth_error_nth; rewrite List.nth_error_map, nth_error_combine_seq; unfold ind_member in HMj; rewrite HMj; reflexivity.
  Qed.

  Lemma length_grec_motives : forall k, List.length (grec_motives D k) = N.
  Proof. intros; unfold grec_motives; rewrite List.length_map, List.length_combine, List.length_seq; lia. Qed.

  (** The group's uniform parameters, under [E] past the motives. *)
  Lemma guvars_at : forall E, ⊢ Θ ⍮ Ξ ⍮ E ++ MT ->
      (forall k U T, List.nth_error (grec_uvars D N (List.length E)) k = Some U ->
         List.nth_error (tele_insts Γ0 Id (grec_uvars D N (List.length E))) k = Some T ->
         Θ ⍮ Ξ ⍮ E ++ MT ⊢ U : T) /\
      Θ ⍮ Ξ ⍮ E ++ MT ⊢ˢ sb_of_list Id (grec_uvars D N (List.length E)) : Γ0 ++ E ++ MT.
  Proof.
    intros E HE.
    assert (HΦ : ⊢ Θ ⍮ Ξ ⍮ (E ++ List.rev (grec_motive_tys p D) ++ ce_ass (a_level 0) :: nil) ++ Γ0)
      by (rewrite <- !List.app_assoc; exact HE).
    assert (Hu : grec_uvars D N (List.length E) = vars_from (List.length (E ++ List.rev (grec_motive_tys p D) ++ ce_ass (a_level 0) :: nil)) nu)
      by (unfold grec_uvars; rewrite !List.length_app, length_MT_motives; cbn [List.length]; f_equal; lia).
    pose proof (uvars_typed _ _ _ HD Hc _ HΦ) as H1; rewrite <- Hu in H1; rewrite <- !List.app_assoc in H1; cbn [List.app] in H1.
    split; [ exact H1 |].
    apply (wf_sub_uparams _ _ _ HD Hc); [ exact HE | unfold grec_uvars; apply length_vars_from | exact H1 ].
  Qed.

  (** All the motives, under [E] past the motives. *)
  Lemma gmotives_typed : forall E i, ⊢ Θ ⍮ Ξ ⍮ E ++ MT ->
      motives_typed Θ Ξ (E ++ MT) p D (grec_uvars D N (List.length E)) (grec_motives D (List.length E)) i.
  Proof.
    intros * HE j Mj HMj; rewrite (nth_grec_motives _ _ _ HMj); exact (proj2 (gmotive_at _ _ _ HMj HE) i).
  Qed.
  (** The case of the constructor [c] of the member [i], under [E] past
      the motives: its context and its type. *)
  Lemma gcase_at : forall E i Mi c gs, ind_member D i = Some Mi -> ind_con Mi c = Some gs -> ⊢ Θ ⍮ Ξ ⍮ E ++ MT ->
      ⊢ Θ ⍮ Ξ ⍮ elim_bctx p D Mi gs (grec_motives D (List.length E)) (grec_uvars D N (List.length E)) ++ E ++ MT /\
      forall i', Θ ⍮ Ξ ⍮ elim_bctx p D Mi gs (grec_motives D (List.length E)) (grec_uvars D N (List.length E)) ++ E ++ MT
        ⊢ elim_bty p i Mi c gs (grec_motive N i Mi (List.length E)) (grec_uvars D N (List.length E)) : Typeω@i'.
  Proof.
    intros * HMi Hcon HE.
    destruct (guvars_at _ HE) as [HUs Hσ].
    assert (Hlu : List.length (grec_uvars D N (List.length E)) = nu) by (unfold grec_uvars; apply length_vars_from).
    assert (Hmc : forall j Mj, ind_member D j = Some Mj -> ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D j Mj (grec_uvars D N (List.length E)) ++ E ++ MT)
      by (intros j Mj HMj; exact (proj1 (gmotive_at _ _ _ HMj HE))).
    split; [ exact (elim_bctx_wf _ _ _ _ _ _ _ _ _ 0 c gs Hg Hds Hl HMi HE Hlu Hσ Hmc (gmotives_typed _ 0 HE) Hcon) |].
    intros i'.
    pose proof (wf_bty_sub _ _ _ _ _ _ _ _ _ i' c gs Hg Hds Hl HMi HE Hlu HUs Hmc (gmotives_typed _ i' HE) Hcon) as Hs.
    exact (sub_preserves_exp _ _ _ _ _ _ _ (proj2 (gmotive_at _ _ _ HMi HE) i') Hs).
  Qed.

  (** The cases' types of the constructors [cs] of the member [i], the
      first under [k] cases before it. *)
  Fixpoint gcases (i : nat) (Mi : imember) (k : nat) (cs : list (string * list carg)) : ctx :=
    match cs with
    | nil => nil
    | (c, gs) :: cs' =>
        ce_ass (ctx_pi (elim_bctx p D Mi gs (grec_motives D k) (grec_uvars D N k))
                  (elim_bty p i Mi c gs (grec_motive N i Mi k) (grec_uvars D N k)))
        :: gcases i Mi (S k) cs'
    end.

  Lemma grec_case_tys_cons : forall i k Mi ms,
      grec_case_tys p D i k (Mi :: ms) = gcases i Mi k (im_cons Mi) ++ grec_case_tys p D (S i) (k + List.length (im_cons Mi)) ms.
  Proof.
    intros; cbn [grec_case_tys]; f_equal.
    generalize k; induction (im_cons Mi) as [| [c gs] cs IH]; intros k'; cbn; [ reflexivity | f_equal; apply IH ].
  Qed.

  Lemma length_gcases : forall i Mi k cs, List.length (gcases i Mi k cs) = List.length cs.
  Proof. intros i Mi k cs; revert k; induction cs as [| [c gs] cs IH]; intros; cbn; auto. Qed.

  Lemma gcases_wf : forall i Mi cs k E, ind_member D i = Some Mi ->
      (forall c gs, In (c, gs) cs -> ind_con Mi c = Some gs) -> List.length E = k -> ⊢ Θ ⍮ Ξ ⍮ E ++ MT ->
      ⊢ Θ ⍮ Ξ ⍮ List.rev (gcases i Mi k cs) ++ E ++ MT.
  Proof.
    intros i Mi; induction cs as [| [c gs] cs IH]; intros k E HMi Hcs HE HEw; [ exact HEw |].
    cbn [gcases List.rev]; rewrite <- List.app_assoc; cbn [List.app].
    pose proof (Hcs c gs (or_introl eq_refl)) as Hcon.
    destruct (gcase_at E _ _ _ _ HMi Hcon HEw) as [HB Hty]; rewrite HE in HB, Hty.
    destruct (ctx_pi_wf _ _ _ _ _ _ HB (Hty 0)) as [j Hj].
    apply (IH (S k) (_ :: E)); [ exact HMi | intros; apply Hcs; right; assumption | cbn; rewrite HE; reflexivity |].
    eapply wf_ctx_extend; exact Hj.
  Qed.

  Lemma gcase_tys_wf : forall ms i k E, (forall j M, List.nth_error ms j = Some M -> ind_member D (i + j) = Some M) ->
      List.length E = k -> ⊢ Θ ⍮ Ξ ⍮ E ++ MT -> ⊢ Θ ⍮ Ξ ⍮ List.rev (grec_case_tys p D i k ms) ++ E ++ MT.
  Proof.
    induction ms as [| M ms IH]; intros i k E Hms HE HEw; [ exact HEw |].
    rewrite grec_case_tys_cons, List.rev_app_distr, <- List.app_assoc.
    assert (HM : ind_member D i = Some M) by (rewrite <- (Nat.add_0_r i); exact (Hms 0 M eq_refl)).
    pose proof (gcases_wf _ _ (im_cons M) k E HM
                  (fun c gs Hin => cons_lookup_nodup _ _ _ (dt_nodup _ _ _ HD _ _ HM) Hin) HE HEw) as H1.
    pose proof (IH (S i) (k + List.length (im_cons M)) (List.rev (gcases i M k (im_cons M)) ++ E)
                  ltac:(intros j' M' Hj'; rewrite Nat.add_succ_comm; exact (Hms (S j') M' Hj'))
                  ltac:(rewrite List.length_app, List.length_rev, length_gcases, HE; lia)
                  ltac:(rewrite <- List.app_assoc; exact H1)) as H2.
    rewrite <- !List.app_assoc in H2; exact H2.
  Qed.

  #[local] Abbreviation CT := (List.rev (grec_case_tys p D 0 0 (ind_members D)) ++ MT).

  (** The module's whole telescope, over the uniform parameters. *)
  Lemma CT_wf : ⊢ Θ ⍮ Ξ ⍮ CT.
  Proof. apply (gcase_tys_wf _ 0 0 nil); [ intros; assumption | reflexivity | exact MT_wf ]. Qed.
  (** ** The Function of a Member *)

  (** The number of cases of the members [ms]. *)
  Definition ncases (ms : list imember) : nat := List.fold_right (fun Mi n => List.length (im_cons Mi) + n) 0 ms.

  Lemma grec_ncases_eq : grec_ncases D = ncases (ind_members D).
  Proof. reflexivity. Qed.

  Lemma length_grec_case_tys : forall ms i k, List.length (grec_case_tys p D i k ms) = ncases ms.
  Proof.
    induction ms as [| M ms IH]; intros; [ reflexivity |].
    rewrite grec_case_tys_cons, List.length_app, length_gcases, IH; reflexivity.
  Qed.

  Lemma grec_case_tys_app : forall ms1 ms2 i k,
      grec_case_tys p D i k (ms1 ++ ms2) = grec_case_tys p D i k ms1 ++ grec_case_tys p D (i + List.length ms1) (k + ncases ms1) ms2.
  Proof.
    induction ms1 as [| M ms1 IH]; intros; cbn [List.app List.length ncases List.fold_right].
    - rewrite !Nat.add_0_r; reflexivity.
    - rewrite !grec_case_tys_cons, IH, <- List.app_assoc; do 3 f_equal; unfold ncases; lia.
  Qed.

  (** The type of the case of the constructor [c] of the member [i] under
      [k] cases before it. *)
  Definition gcase_ty (i : nat) (Mi : imember) (c : string) (gs : list carg) (k : nat) : typ :=
    ctx_pi (elim_bctx p D Mi gs (grec_motives D k) (grec_uvars D N k))
      (elim_bty p i Mi c gs (grec_motive N i Mi k) (grec_uvars D N k)).

  Lemma gcases_app : forall i Mi k cs1 c gs cs2,
      gcases i Mi k (cs1 ++ (c, gs) :: cs2) =
        gcases i Mi k cs1 ++ ce_ass (gcase_ty i Mi c gs (k + List.length cs1)) :: gcases i Mi (S (k + List.length cs1)) cs2.
  Proof.
    intros i Mi k cs1; revert k; induction cs1 as [| [c' gs'] cs1 IH]; intros; cbn [List.app gcases List.length].
    - rewrite Nat.add_0_r; reflexivity.
    - rewrite IH; cbn [List.app]; rewrite Nat.add_succ_r; reflexivity.
  Qed.

  Lemma grec_brs_in : forall K nj Mi cs kc c n B,
      In (c, n, B) (grec_brs K nj kc Mi cs) ->
      exists cs1 gs cs2, cs = cs1 ++ (c, gs) :: cs2 /\ n = (im_nn Mi + List.length gs + cargs_nrec gs)%nat /\
        B = apps (a_var (n + nj + (K - 1 - (kc + List.length cs1)))) (vars_from 0 n).
  Proof.
    intros K nj Mi; induction cs as [| [c' gs'] cs IH]; intros * Hin; cbn in Hin; [ destruct Hin |].
    destruct Hin as [[= <- <- <-] | Hin].
    - exists nil, gs', cs; cbn; rewrite Nat.add_0_r; auto.
    - destruct (IH _ _ _ _ Hin) as (cs1 & gs & cs2 & -> & -> & ->).
      exists ((c', gs') :: cs1), gs, cs2; cbn [List.app List.length]; split; [ reflexivity | split; [ reflexivity |] ].
      do 3 f_equal; lia.
  Qed.

  Lemma grec_brs_names : forall K nj Mi cs kc, List.map fst cs = List.map (fun b => fst (fst b)) (grec_brs K nj kc Mi cs).
  Proof. intros K nj Mi cs; induction cs as [| [c gs] cs IH]; intros; cbn; [ reflexivity | rewrite (IH (S kc)); reflexivity ]. Qed.
  Lemma grec_motive_wk : forall i Mi k m,
      (grec_motive N i Mi k)[wk_qn (S (im_nn Mi)) (wk_shiftn m)]ʷ = grec_motive N i Mi (k + m).
  Proof.
    intros; unfold grec_motive; rewrite apps_exp_wk; cbn [exp_wk]; rewrite wk_qn_ge by lia.
    f_equal; [ cbn; f_equal; lia |].
    unfold vars_from; rewrite List.map_map; apply List.map_ext_in; intros x Hx.
    apply List.in_rev, List.in_seq in Hx; cbn [exp_wk]; rewrite wk_qn_lt by lia; reflexivity.
  Qed.

  Lemma grec_uvars_wk : forall k m, List.map (fun U => U[wk_shiftn m]ʷ) (grec_uvars D N k) = grec_uvars D N (k + m).
  Proof. intros; unfold grec_uvars; rewrite vars_from_wk_shiftn; f_equal; lia. Qed.

  (** The eliminator's motive, at the scrutinee's parameters and the
      scrutinee, is the function's codomain. *)
  Lemma grec_motive_inst : forall j Mj K,
      (grec_motive N j Mj (S (im_nn Mj) + K))[sb_of_list Id (vars_from 1 (im_nn Mj) ++ #0 :: nil)] = grec_motive N j Mj K.
  Proof.
    intros.
    assert (Hv : vars_from 1 (im_nn Mj) ++ #0 :: nil = vars_from 0 (S (im_nn Mj))).
    { replace (S (im_nn Mj)) with (im_nn Mj + 1) by lia; rewrite <- (vars_from_app 0 (im_nn Mj) 1); reflexivity. }
    rewrite Hv; unfold grec_motive; rewrite apps_exp_sub; cbn [exp_sub].
    f_equal.
    - replace (S (im_nn Mj) + (S (im_nn Mj) + K) + (N - 1 - j))
        with (List.length (vars_from 0 (S (im_nn Mj))) + (S (im_nn Mj) + K + (N - 1 - j)))
        by (rewrite length_vars_from; lia).
      rewrite sb_of_list_ge; reflexivity.
    - pose proof (vars_from_sb_of_list (vars_from 0 (S (im_nn Mj))) Id) as H.
      rewrite length_vars_from in H; exact H.
  Qed.

  Lemma length_grec_blocks : forall K nj ms i kc, List.length (grec_blocks D K nj i kc ms) = List.length ms.
  Proof. intros K nj; induction ms as [| M ms IH]; intros; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

  Lemma nth_grec_blocks : forall K nj ms i kc j Mj, List.nth_error ms j = Some Mj ->
      List.nth_error (grec_blocks D K nj i kc ms) j =
        Some (eb_mk (S (im_nn Mj)) None (grec_motive N (i + j) Mj (K + nj))
                (grec_brs K nj (kc + ncases (List.firstn j ms)) Mj (im_cons Mj))).
  Proof.
    intros K nj; induction ms as [| M ms IH]; intros i kc [| j] Mj Hj; cbn in Hj; try discriminate.
    - injection Hj as <-; cbn; rewrite !Nat.add_0_r; reflexivity.
    - cbn [grec_blocks List.nth_error]; rewrite (IH _ _ _ _ Hj); cbn [List.firstn ncases List.fold_right].
      rewrite Nat.add_succ_r, <- Nat.add_assoc; reflexivity.
  Qed.

  Lemma blocks_motives_grec : forall K nj ms i kc,
      blocks_motives (grec_blocks D K nj i kc ms) =
        List.map (fun iM => grec_motive N (fst iM) (snd iM) (K + nj)) (List.combine (List.seq i (List.length ms)) ms).
  Proof. intros K nj; induction ms as [| M ms IH]; intros; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

  (** The case of a constructor among all the cases. *)
  Lemma grec_case_tys_at : forall k Mk cs1 c gs cs2, ind_member D k = Some Mk -> im_cons Mk = cs1 ++ (c, gs) :: cs2 ->
      exists A B, grec_case_tys p D 0 0 (ind_members D) = A ++ ce_ass (gcase_ty k Mk c gs (List.length A)) :: B /\
        List.length A = ncases (List.firstn k (ind_members D)) + List.length cs1.
  Proof.
    intros * HMk Hcs; unfold ind_member in HMk.
    pose proof (List.nth_error_split _ _ HMk) as (l1 & l2 & Hsplit & Hl1).
    assert (Hf : List.firstn k (ind_members D) = l1)
      by (rewrite Hsplit, List.firstn_app, <- Hl1, Nat.sub_diag, List.firstn_O, List.app_nil_r, List.firstn_all; reflexivity).
    rewrite Hf.
    assert (Ht : grec_case_tys p D 0 0 (ind_members D) = grec_case_tys p D 0 0 (l1 ++ Mk :: l2)) by (f_equal; exact Hsplit).
    rewrite Ht, grec_case_tys_app, grec_case_tys_cons, Hcs, gcases_app, Hl1, Nat.add_0_l.
    exists (grec_case_tys p D 0 0 l1 ++ gcases k Mk (ncases l1) cs1).
    eexists; rewrite <- List.app_assoc; cbn [List.app].
    rewrite !Nat.add_0_l, !List.length_app, length_grec_case_tys, length_gcases, <- !List.app_assoc; cbn [List.app].
    split; reflexivity.
  Qed.
  (** The cases' types, innermost first, as they sit in the module's
      telescope, and their number. *)
  #[local] Abbreviation EK := (List.rev (grec_case_tys p D 0 0 (ind_members D))).
  #[local] Abbreviation K := (grec_ncases D).

  Lemma length_EK : List.length EK = K.
  Proof. rewrite List.length_rev, length_grec_case_tys, grec_ncases_eq; reflexivity. Qed.

  (** The eliminator in the body of the member [j]'s recursor, under its
      parameters and scrutinee, is of the motive. *)
  Lemma grec_elim_typed : forall j Mj, ind_member D j = Some Mj ->
      Θ ⍮ Ξ ⍮ elim_mctx p D j Mj (grec_uvars D N K) ++ CT
        ⊢ a_elim (Some p) (grec_uvars D N (K + S (im_nn Mj))) j (grec_blocks D K (S (im_nn Mj)) 0 0 (ind_members D)) (a_var 0)
        : grec_motive N j Mj K.
  Proof.
    intros j Mj HMj. set (nn := im_nn Mj).
    destruct (gmotive_at EK j Mj HMj CT_wf) as [HM2 HA2]; rewrite length_EK in HM2, HA2.
    set (E2 := elim_mctx p D j Mj (grec_uvars D N K) ++ EK).
    assert (HE2 : ⊢ Θ ⍮ Ξ ⍮ E2 ++ MT) by (unfold E2; rewrite <- List.app_assoc; exact HM2).
    assert (HlE2 : List.length E2 = K + S nn) by (unfold E2; rewrite List.length_app, length_elim_mctx, length_EK; lia).
    destruct (guvars_at _ HE2) as [HUs3 _]; rewrite HlE2 in HUs3.
    set (Us := grec_uvars D N K) in *.
    set (Us' := grec_uvars D N (K + S nn)) in *.
    set (Ps := Us' ++ vars_from 1 nn).
    assert (HUl : List.length Us = nu) by apply length_vars_from.
    assert (HUl' : List.length Us' = nu) by apply length_vars_from.
    assert (HNl : List.length (vars_from 1 nn) = nn) by apply length_vars_from.
    assert (HUs'w : Us' = List.map (fun U => U[wk_shiftn (S nn)]ʷ) Us) by (unfold Us, Us'; rewrite grec_uvars_wk; reflexivity).
    assert (HF : List.firstn nu Ps = Us') by (unfold Ps; exact (firstn_app_len Us' (vars_from 1 nn) nu HUl')).
    assert (HS : List.skipn nu Ps = vars_from 1 nn) by (unfold Ps; exact (skipn_app_len Us' (vars_from 1 nn) nu HUl')).
    set (Bks := grec_blocks D K (S nn) 0 0 (ind_members D)).
    assert (Hblk : forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
                     b = eb_mk (S (im_nn Mk)) None (grec_motive N k Mk (K + S nn))
                           (grec_brs K (S nn) (ncases (List.firstn k (ind_members D))) Mk (im_cons Mk))).
    { intros k Mk b HMk Hb; unfold Bks in Hb; rewrite (nth_grec_blocks _ _ _ _ _ _ _ HMk) in Hb; injection Hb as <-; reflexivity. }
    replace (grec_motive N j Mj K) with ((grec_motive N j Mj (K + S nn))[sb_of_list Id (List.skipn nu Ps ++ #0 :: nil)])
      by (rewrite HS, Nat.add_comm; apply grec_motive_inst).
    eapply wf_elim with (i := 0) (Ps := Ps)
      (bm := eb_mk (S nn) None (grec_motive N j Mj (K + S nn)) (grec_brs K (S nn) (ncases (List.firstn j (ind_members D))) Mj (im_cons Mj)));
      [ exact Hl | left; reflexivity | exact HMj | unfold Bks; exact (nth_grec_blocks _ _ _ _ _ _ _ HMj)
      | unfold Bks; rewrite length_grec_blocks; reflexivity | | | | rewrite HF; reflexivity | | | | | | | | ].
    - (* the number of parameters *)
      unfold Ps, im_np; rewrite List.length_app, HUl', HNl; lia.
    - (* the parameters: the uniform ones, then the scrutinee's *)
      unfold E2 in HUs3; rewrite <- List.app_assoc in HUs3.
      apply (params_typed_join _ _ _ Hc j Mj _ Us' (vars_from 1 nn) HMj HUl'); [ exact HUs3 |].
      intros k N0 T HN HT.
      unfold elim_mctx.
      replace (vars_from 1 nn)
        with (vars_from (List.length (ce_ass (ind_mty p D j (List.map (fun U => U[wk_shiftn nn]ʷ) Us) (vars_from 0 nn)) :: nil))
                (List.length (im_nparams Mj))) in HN, HT
        by (rewrite length_im_nparams; reflexivity).
      eapply (wf_vars_tele_gen _ _ (ce_ass _ :: nil) (im_nparams Mj) (sb_of_list Id Us) _ CT nu);
        [ apply (decl_closed_nparams_ass D Hc j Mj HMj) | apply (decl_nparams_mvc _ _ _ HD j Mj HMj)
        | apply (decl_closed_nparams_scoped D Hc j Mj HMj) | exact HM2 | | exact HN | exact HT ].
      intros y Hy; rewrite HUs'w, sb_of_list_map by lia; cbn [List.length]; rewrite length_im_nparams; reflexivity.
    - (* the scrutinee *)
      rewrite HF, HS.
      assert (Heq : (ind_mty p D j (List.map (fun U => U[wk_shiftn nn]ʷ) Us) (vars_from 0 nn))[↑]ʷ = ind_mty p D j Us' (vars_from 1 nn)).
      { rewrite ind_mty_wk by (first [ exact Hc | rewrite List.length_map; exact HUl ]).
        f_equal.
        - rewrite HUs'w, !List.map_map; apply List.map_ext; intros U; rewrite exp_wk_wk; apply exp_wk_wk_eq; intros x; cbn; lia.
        - unfold vars_from; rewrite List.map_map; apply List.map_ext; intros x; cbn; f_equal; lia. }
      apply wf_vlookup; [ exact HM2 |].
      unfold elim_mctx; cbn [List.app]; rewrite <- Heq; constructor.
    - (* each block binds its member's indices and the scrutinee *)
      intros k Mk b HMk Hb; rewrite (Hblk _ _ _ HMk Hb); reflexivity.
    - (* no block is annotated *)
      intros k Mk b Z HMk Hb Hz; rewrite (Hblk _ _ _ HMk Hb) in Hz; discriminate.
    - (* the motives *)
      intros k Mk b HMk Hb; rewrite (Hblk _ _ _ HMk Hb); cbn [eb_motive]; rewrite HF.
      pose proof (proj2 (gmotive_at E2 k Mk HMk HE2) 0) as H; rewrite HlE2 in H; unfold E2 in H; rewrite <- List.app_assoc in H; exact H.
    - (* the motives' contexts *)
      intros k Mk HMk; rewrite HF; apply ctx_ext_refl; [ apply (elim_mctx_ass p D k Mk _ Hc HMk) |].
      pose proof (proj1 (gmotive_at E2 k Mk HMk HE2)) as H; rewrite HlE2 in H; unfold E2 in H; rewrite <- List.app_assoc in H; exact H.
    - (* the branches' names *)
      intros k Mk b HMk Hb; rewrite (Hblk _ _ _ HMk Hb); apply grec_brs_names.
    - (* the branches' contexts *)
      intros k Mk c gs HMk Hcon; rewrite HF.
      assert (Hbm : blocks_motives Bks = grec_motives D (K + S nn)) by (unfold Bks; rewrite blocks_motives_grec; reflexivity).
      rewrite Hbm; apply ctx_ext_refl; [ apply (elim_bctx_ass p D k Mk gs _ _ Hc HMk) |].
      destruct (gcase_at E2 k Mk c gs HMk Hcon HE2) as [HB _]; rewrite HlE2 in HB; unfold E2 in HB; rewrite <- List.app_assoc in HB; exact HB.
    - (* the branches' arities *)
      intros k Mk b c gs n B HMk Hb Hcon Hin; rewrite (Hblk _ _ _ HMk Hb) in Hin; cbn [eb_brs] in Hin.
      destruct (grec_brs_in _ _ _ _ _ _ _ _ Hin) as (cs1 & gs' & cs2 & Hcs & -> & _).
      assert (gs' = gs) as -> by (symmetry; eapply nodup_in_fst; [ exact (dt_nodup _ _ _ HD _ _ HMk) | exact (cons_lookup_in _ _ _ Hcon) | rewrite Hcs; apply List.in_elt ]).
      reflexivity.
    - (* a branch: its case, applied to what the branch binds *)
      intros k Mk b c gs n B HMk Hb Hcon Hin; rewrite (Hblk _ _ _ HMk Hb) in Hin |- *; cbn [eb_brs eb_motive] in Hin |- *.
      destruct (grec_brs_in _ _ _ _ _ _ _ _ Hin) as (cs1 & gs' & cs2 & Hcs & Hn & HB).
      assert (gs' = gs) as -> by (symmetry; eapply nodup_in_fst; [ exact (dt_nodup _ _ _ HD _ _ HMk) | exact (cons_lookup_in _ _ _ Hcon) | rewrite Hcs; apply List.in_elt ]).
      assert (Hbm : blocks_motives Bks = grec_motives D (K + S nn)) by (unfold Bks; rewrite blocks_motives_grec; reflexivity).
      rewrite HF, Hbm.
      destruct (grec_case_tys_at _ _ _ _ _ _ HMk Hcs) as (A & B' & HA & HlA).
      assert (HK : List.length A + S (List.length B') = K).
      { rewrite <- length_EK, List.length_rev, HA, List.length_app; reflexivity. }
      pose proof (lookup_mid (elim_mctx p D j Mj Us ++ List.rev B') (gcase_ty k Mk c gs (List.length A)) (List.rev A ++ MT)) as Hlk.
      rewrite List.length_app, length_elim_mctx, List.length_rev in Hlk.
      replace ((elim_mctx p D j Mj Us ++ List.rev B') ++ ce_ass (gcase_ty k Mk c gs (List.length A)) :: List.rev A ++ MT)
        with (E2 ++ MT) in Hlk by (unfold E2; rewrite HA, List.rev_app_distr; cbn [List.rev]; rewrite <- !List.app_assoc; reflexivity).
      unfold gcase_ty in Hlk; rewrite ctx_pi_wk in Hlk.
      assert (Hm : List.length A + S (S (im_nn Mj) + List.length B') = K + S nn) by (fold nn; lia).
      erewrite (elim_bctx_wk p D k Mk c gs (grec_motives D (List.length A)) (grec_motives D (K + S nn)))
        in Hlk by (first [ exact Hc | exact HMk | rewrite Hcs; apply List.in_elt | unfold grec_uvars; apply length_vars_from
                         | intros j' Mj' HMj'; rewrite !(nth_grec_motives _ _ _ HMj'), grec_motive_wk, Hm; reflexivity ]).
      rewrite length_elim_bctx in Hlk.
      replace (cargs_nrec gs + List.length gs + im_nn Mk) with (im_nn Mk + List.length gs + cargs_nrec gs) in Hlk by lia.
      rewrite (elim_bty_wk p D k Mk) in Hlk by (first [ exact Hc | exact HMk | unfold grec_uvars; apply length_vars_from ]).
      rewrite grec_motive_wk, grec_uvars_wk, Hm in Hlk.
      fold Us' in Hlk.
      destruct (gcase_at E2 k Mk c gs HMk Hcon HE2) as [HBc HBt]; rewrite HlE2 in HBc, HBt.
      fold Us' in HBc, HBt.
      pose proof (wf_apps_vars _ _ _ _ _ _ _ (elim_bctx_ass p D k Mk gs _ Us' Hc HMk) HBc (HBt 0)
                    (wf_vlookup _ _ _ _ _ HE2 Hlk)) as H.
      rewrite length_elim_bctx in H; cbn [exp_wk] in H.
      unfold E2 in H; rewrite <- List.app_assoc in H.
      rewrite HB, Hn.
      replace (im_nn Mk + List.length gs + cargs_nrec gs + S nn + (K - 1 - (ncases (List.firstn k (ind_members D)) + List.length cs1)))
        with (wk_shiftn (cargs_nrec gs + List.length gs + im_nn Mk) (S (im_nn Mj) + List.length B')) by (cbn; fold nn; lia).
      replace (im_nn Mk + List.length gs + cargs_nrec gs) with (cargs_nrec gs + List.length gs + im_nn Mk) by lia.
      exact H.
  Qed.

  (** Each member's recursor is of its type over the module's telescope. *)
  Lemma grec_fn_typed : forall j Mj, ind_member D j = Some Mj -> Θ ⍮ Ξ ⍮ CT ⊢ grec_fn p D j Mj : grec_fn_ty p D j Mj.
  Proof.
    intros j Mj HMj; unfold grec_fn, grec_fn_ty; cbv zeta.
    destruct (gmotive_at EK j Mj HMj CT_wf) as [HM2 HA2]; rewrite length_EK in HM2, HA2.
    eapply ctx_fn_wf; [ exact HM2 | exact (HA2 0) | exact (grec_elim_typed j Mj HMj) ].
  Qed.
End GrecTyped.
