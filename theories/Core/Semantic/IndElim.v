(** * The Eliminator in the PER Model

    The eliminator of an inductive type relates related elements at a family
    of relations [Rel], given that its motives are related at [Rel] at
    related arguments ([Hmot]) and its branches are related at related
    arguments and recursive results ([Hbr]).  This is the semantic content
    of the eliminator's rule; the cases of the fundamental theorem
    instantiate it at the links of their four-value patterns.

    A stuck eliminator reads back its motive and branches under fresh
    variables of the types its scrutinee's uniform parameters give.  These
    parameters are admissible ([ind_adm]), so the variables of the two sides
    are related, and so are the motives and branches there
    ([per_bot_elim]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Inductives.
From Mctt.Core.Semantic Require Export PER Realizability.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

  Lemma brs_names_lookup : forall cs (Bs : list (String.string * nat * exp)) c gs, brs_names cs Bs ->
      cons_lookup cs c = Some gs -> exists n B, brs_lookup Bs c = Some (n, B) /\ In (c, n, B) Bs.
  Proof.
    induction cs as [| [c' gs'] cs IH]; intros [| [[c0 n0] B0] Bs] c gs Hn Hc; cbn in *; try discriminate.
    injection Hn as -> Hn.
    destruct (String.eqb c c0) eqn:E.
    - apply String.eqb_eq in E; subst; exists n0, B0; split; [ reflexivity | left; reflexivity ].
    - destruct (IH _ _ _ Hn Hc) as (n & B & HB & Hin); exists n, B; split; [ exact HB | right; exact Hin ].
  Qed.

  Lemma functional_fresh_tele : forall ρ T s vs vs', fresh_tele gc_deps gc_stack ρ T s vs ->
      fresh_tele gc_deps gc_stack ρ T s vs' -> vs = vs'.
  Proof.
    intros * H; revert vs'; induction H; intros vs' H'; inversion H'; subst; [ reflexivity |].
    functional_eval_rewrite_clear; f_equal; auto.
  Qed.

  Lemma cons_lookup_nodup_in : forall cs c gs, List.NoDup (List.map fst cs) -> In (c, gs) cs -> cons_lookup cs c = Some gs.
  Proof.
    induction cs as [| [c' gs'] cs IH]; cbn; intros c gs Hnd H; [ destruct H |].
    inversion Hnd as [| ? ? Hni Hnd']; subst.
    destruct (String.eqb_spec c c') as [-> | Hne].
    - destruct H as [H | H]; [ injection H as ->; reflexivity |].
      exfalso; apply Hni; apply List.in_map_iff; exists (c', gs); auto.
    - destruct H as [H | H]; [ injection H as -> ->; contradiction | eauto ].
  Qed.

  Lemma brs_lookup_nodup_in : forall (Bs : list (String.string * nat * exp)) c n B,
      List.NoDup (List.map (fun b => fst (fst b)) Bs) -> In (c, n, B) Bs -> brs_lookup Bs c = Some (n, B).
  Proof.
    induction Bs as [| [[c' n'] B'] Bs IH]; cbn; intros c n B Hnd H; [ destruct H |].
    inversion Hnd as [| ? ? Hni Hnd']; subst.
    destruct (String.eqb_spec c c') as [-> | Hne].
    - destruct H as [H | H]; [ injection H as -> ->; reflexivity |].
      exfalso; apply Hni; apply List.in_map_iff; exists (c', n, B); auto.
    - destruct H as [H | H]; [ injection H as -> -> ->; contradiction | eauto ].
  Qed.

  Section IndElim.
    #[local] Set Default Proof Using "All".
    Variable (p : qname) (D : ind_decl) (ups : list domain).
    Variable (nr : nat -> list domain -> relation domain).
    Variable (ar : list domain -> String.string -> nat -> list domain -> relation domain).
    Let T := List.rev (ind_nparams D).
    Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D).
    Hypothesis (Hass : tele_ass (ind_params D)).
    Hypothesis (HnP : forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_pre nr k vs vs' -> PER (nr k vs)).
    Hypothesis (HnI : forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_pre nr k vs vs' -> (nr k vs <~> nr k vs')).
    Hypothesis (HaP : forall ms ms' c gs k A vs vs', tele_full nr T ms ms' -> ind_con D c = Some gs ->
                      List.nth_error (cargs_nonrec gs) k = Some A -> tele_pre (ar ms c) k vs vs' -> PER (ar ms c k vs)).
    Hypothesis (HaI : forall ms ms' c gs k A vs vs', tele_full nr T ms ms' -> ind_con D c = Some gs ->
                      List.nth_error (cargs_nonrec gs) k = Some A -> tele_pre (ar ms c) k vs vs' ->
                      (ar ms c k vs <~> ar ms' c k vs')).
    Hypothesis (Had : ind_adm D ups nr ar ups).
    Hypothesis (Hle : ind_nu D <= ind_np D).

    Let tsym := tnr_sym p D ups nr ar Hass HnP HnI HaP HaI.
    Let ttrans := tnr_trans p D ups nr ar Hass HnP HnI HaP HaI.
    Let trefl := tnr_refl_l p D ups nr ar Hass HnP HnI HaP HaI.
    Let trefl_r := tnr_refl_r p D ups nr ar Hass HnP HnI HaP HaI.

    Lemma ind_rel_ns_refl : forall ns m m', ind_rel p D ups nr ar ns m m' -> tele_full nr T ns ns.
    Proof. intros * H; inversion H; subst; [ assumption | eapply trefl; eassumption ]. Qed.

    Lemma ind_rel_mv : forall ns ns1 m m', ind_rel p D ups nr ar ns m m' -> tele_full nr T ns ns1 ->
        ind_rel p D ups nr ar ns1 m m'.
    Proof. intros * H Hn; exact (proj1 (ind_rel_move p D ups nr ar Hass HnP HnI HaP HaI ups Had) _ _ _ H _ Hn). Qed.

    Lemma length_tnr : forall a b, tele_full nr T a b -> List.length a = ind_nn D /\ List.length b = ind_nn D.
    Proof. intros * H; rewrite tele_full_iff in H; destruct H as (H1 & H2 & _); unfold T in *; rewrite List.length_rev, length_nparams in *; lia. Qed.

    (** ** The Two Sides *)
    Variable (i : uidx) (nm : nat) (ρa ρb : env) (Aa Ab : exp) (Bsa Bsb : list (String.string * nat * exp)).
    Variable (Rel : list domain -> domain -> list domain -> domain -> relation domain).
    Hypothesis (Hnm : nm = S (ind_nn D)).
    Hypothesis (Hnd : List.NoDup (List.map fst (ind_cons D))).
    Hypothesis (Hna : brs_names (ind_cons D) Bsa) (Hnb : brs_names (ind_cons D) Bsb).
    Hypothesis (Hara : forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bsa ->
                        n = (ind_nn D + List.length gs + cargs_nrec gs)%nat).
    Hypothesis (Harb : forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bsb ->
                        n = (ind_nn D + List.length gs + cargs_nrec gs)%nat).
    Hypothesis (Hmot : forall ns ns' m m', tele_full nr T ns ns' -> ind_rel p D ups nr ar ns m m' ->
                   exists a a', ⟦ Aa ⟧ env_args ρa (ns ++ m :: nil) ↘ a /\ ⟦ Ab ⟧ env_args ρb (ns' ++ m' :: nil) ↘ a' /\
                     DF a ≈ a' ∈ per_univ_elem i ↘ (Rel ns m ns' m')).

    (** The recursive results of related arguments, related at the
        parameters the arguments are declared at. *)
    Inductive ihs_rel : env -> list carg -> list domain -> list domain -> list domain -> list domain -> Prop :=
    | ihs_rel_nil : forall ρ, ihs_rel ρ nil nil nil nil nil
    | ihs_rel_arg : forall ρ A gs v v' vs vs' ihs ihs',
        ihs_rel (ρ ↦ v) gs vs vs' ihs ihs' -> ihs_rel ρ (ca_arg A :: gs) (v :: vs) (v' :: vs') ihs ihs'
    | ihs_rel_rec : forall ρ (Ps : ptyp) gs v v' vs vs' bs ih ih' ihs ihs',
        eval_exps gc_deps gc_stack Ps ρ bs -> Rel bs v bs v' ih ih' ->
        ihs_rel ρ gs vs vs' ihs ihs' -> ihs_rel ρ (ca_rec Ps :: gs) (v :: vs) (v' :: vs') (ih :: ihs) (ih' :: ihs').

    Hypothesis (Hbr : forall c gs n Ba Bb, ind_con D c = Some gs ->
                   brs_lookup Bsa c = Some (n, Ba) -> brs_lookup Bsb c = Some (n, Bb) ->
                   forall ns bs bs' vs vs' ihs ihs',
                     tele_full nr T ns ns -> List.length bs = ind_np D -> List.length bs' = ind_np D ->
                     tele_full nr T ns (List.skipn (ind_nu D) bs) -> tele_full nr T ns (List.skipn (ind_nu D) bs') ->
                     tele_full (ar ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs') ->
                     ind_args_rel p D ups nr ar (env_args nil (ups ++ ns)) gs vs vs' ->
                     ihs_rel (env_args nil (ups ++ ns)) gs vs vs' ihs ihs' ->
                     exists r r', ⟦ Ba ⟧ env_args ρa (List.skipn (ind_nu D) bs ++ vs ++ ihs) ↘ r /\
                       ⟦ Bb ⟧ env_args ρb (List.skipn (ind_nu D) bs' ++ vs' ++ ihs') ↘ r' /\
                       Rel ns (d_con p c (bs ++ vs)) ns (d_con p c (bs' ++ vs')) r r').

    (** ** The Family Is Invariant *)

    Lemma Rel_right : forall ns m ns1 m1 ns2 m2, tele_full nr T ns ns1 -> tele_full nr T ns ns2 ->
        ind_rel p D ups nr ar ns m m1 -> ind_rel p D ups nr ar ns m m2 -> (Rel ns m ns1 m1 <~> Rel ns m ns2 m2).
    Proof.
      intros * H1 H2 Hm1 Hm2.
      destruct (Hmot _ _ _ _ H1 Hm1) as (a & a1 & Ea & Ea1 & HR1).
      destruct (Hmot _ _ _ _ H2 Hm2) as (b & a2 & Eb & Ea2 & HR2).
      assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
      eapply per_univ_elem_right_irrel; eassumption.
    Qed.

    Lemma Rel_left : forall ns1 m1 ns2 m2 ns' m', tele_full nr T ns1 ns' -> tele_full nr T ns2 ns' ->
        ind_rel p D ups nr ar ns1 m1 m' -> ind_rel p D ups nr ar ns2 m2 m' -> (Rel ns1 m1 ns' m' <~> Rel ns2 m2 ns' m').
    Proof.
      intros * H1 H2 Hm1 Hm2.
      destruct (Hmot _ _ _ _ H1 Hm1) as (a1 & a & Ea1 & Ea & HR1).
      destruct (Hmot _ _ _ _ H2 Hm2) as (a2 & b & Ea2 & Eb & HR2).
      assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
      eapply per_univ_elem_left_irrel; eassumption.
    Qed.

    Lemma ind_args_rel_length : forall ρ gs vs vs', ind_args_rel p D ups nr ar ρ gs vs vs' ->
        List.length vs = List.length gs /\ List.length vs' = List.length gs.
    Proof. induction 1; cbn; [ split; reflexivity | destruct IHind_args_rel; split; congruence | destruct IHind_args_rel; split; congruence ]. Qed.

    (** ** Fresh Variables

        The variables a stuck eliminator's readback makes at admissible
        uniform parameters: those of two such are related, through those at
        [ups]. *)
    Lemma fresh_np : forall ua, ind_adm D ups nr ar ua -> forall T' T0 vs vs' s, T = T0 ++ T' ->
        tele_pre nr (List.length T0) vs vs' ->
        exists ws ws', fresh_tele gc_deps gc_stack (env_args nil (ups ++ vs)) T' s ws /\
          fresh_tele gc_deps gc_stack (env_args nil (ua ++ vs')) T' s ws' /\
          tele_pre nr (List.length T) (vs ++ ws) (vs' ++ ws').
    Proof.
      intros ua (Hn & _ & _); induction T' as [| e T' IH]; intros T0 vs vs' s HT Hp.
      - exists nil, nil; rewrite !List.app_nil_r; rewrite HT, List.app_nil_r.
        split; [ constructor | split; [ constructor | exact Hp ] ].
      - assert (Hk : List.nth_error T (List.length T0) = Some e)
          by (rewrite HT, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
        assert (HA : exists A, List.nth_error T (List.length T0) = Some (ce_ass A)).
        { apply (nparams_lt_ass D); [ exact Hass |]. apply List.nth_error_Some; unfold T in Hk; congruence. }
        destruct HA as [A HA]; rewrite Hk in HA; injection HA as ->.
        destruct (Hn _ _ _ _ s Hk Hp) as (a & a' & Ea & Ea' & Hr).
        destruct (IH (T0 ++ ce_ass A :: nil) (vs ++ ⇑! a s :: nil) (vs' ++ ⇑! a' s :: nil) (S s)) as (ws & ws' & F & F' & Hp').
        { rewrite HT, <- List.app_assoc; reflexivity. }
        { rewrite List.length_app, Nat.add_comm; cbn; apply tele_pre_snoc; assumption. }
        exists (⇑! a s :: ws), (⇑! a' s :: ws'); split; [| split ].
        + econstructor; [ exact Ea |]; rewrite <- env_args_snoc, <- List.app_assoc; exact F.
        + econstructor; [ exact Ea' |]; rewrite <- env_args_snoc, <- List.app_assoc; exact F'.
        + rewrite <- !List.app_assoc in Hp'; exact Hp'.
    Qed.

    Lemma fresh_np2 : forall ua1 ua2 s, ind_adm D ups nr ar ua1 -> ind_adm D ups nr ar ua2 ->
        exists ns1 ns2, fresh_tele gc_deps gc_stack (env_args nil ua1) T s ns1 /\
          fresh_tele gc_deps gc_stack (env_args nil ua2) T s ns2 /\ tele_full nr T ns1 ns2.
    Proof.
      intros * H1 H2.
      destruct (fresh_np _ H1 T nil nil nil s eq_refl (tele_pre_nil _)) as (w0 & w1 & F0 & F1 & P1).
      destruct (fresh_np _ H2 T nil nil nil s eq_refl (tele_pre_nil _)) as (w0' & w2 & F0' & F2 & P2).
      pose proof (functional_fresh_tele _ _ _ _ _ F0 F0') as <-.
      rewrite List.app_nil_r in F1, F2; cbn in P1, P2.
      exists w1, w2; split; [ exact F1 | split; [ exact F2 |] ].
      apply tele_full_of_pre in P1, P2.
      exact (ttrans _ _ _ (tsym _ _ P1) P2).
    Qed.

    Lemma ind_rel_var : forall ns ua1 ua2 bs1 bs2 k, ind_adm D ups nr ar ua1 -> ind_adm D ups nr ar ua2 ->
        List.length ua1 = ind_nu D -> List.length ua2 = ind_nu D ->
        tele_full nr T ns bs1 -> tele_full nr T ns bs2 ->
        ind_rel p D ups nr ar ns (⇑! (d_ind p (ua1 ++ bs1)) k) (⇑! (d_ind p (ua2 ++ bs2)) k).
    Proof.
      intros * H1 H2 L1 L2 B1 B2.
      destruct (length_tnr _ _ B1) as [_ L1']; destruct (length_tnr _ _ B2) as [_ L2'].
      assert (Hnp : ind_nn D = ind_np D - ind_nu D) by reflexivity.
      apply ind_rel_neut.
      - rewrite List.length_app; lia.
      - rewrite List.length_app; lia.
      - rewrite firstn_app_exact by exact L1; exact H1.
      - rewrite firstn_app_exact by exact L2; exact H2.
      - rewrite skipn_app_exact by exact L1; exact B1.
      - rewrite skipn_app_exact by exact L2; exact B2.
      - apply var_per_bot.
    Qed.

    Let tprl := tar_pre_refl_l p D ups nr ar Hass HnP HnI HaP HaI.

    Lemma fresh_args : forall ua1 ua2 ns1 ns2 c gs, ind_adm D ups nr ar ua1 -> ind_adm D ups nr ar ua2 ->
        List.length ua1 = ind_nu D -> List.length ua2 = ind_nu D ->
        tele_full nr T ns1 ns2 -> ind_con D c = Some gs ->
        forall gs' gs1 ws1 ws2 s s2, gs = gs1 ++ gs' ->
        tele_pre (ar ns1 c) (List.length (cargs_nonrec gs1)) ws1 ws2 ->
        exists vs1 vs2 bss1 bss2 ihs1 ihs2,
          fresh_cargs gc_deps gc_stack p ua1 (env_args nil (ua1 ++ ns1 ++ ws1)) gs' s vs1 bss1 /\
          fresh_cargs gc_deps gc_stack p ua2 (env_args nil (ua2 ++ ns2 ++ ws2)) gs' s vs2 bss2 /\
          List.Forall (fun bs => List.length bs = ind_nn D) bss1 /\
          List.Forall (fun bs => List.length bs = ind_nn D) bss2 /\
          fresh_ihs gc_deps gc_stack ρa Aa gs' vs1 bss1 s2 ihs1 /\
          fresh_ihs gc_deps gc_stack ρb Ab gs' vs2 bss2 s2 ihs2 /\
          tele_pre (ar ns1 c) (List.length (cargs_nonrec gs)) (ws1 ++ nonrec_vals gs' vs1) (ws2 ++ nonrec_vals gs' vs2) /\
          ind_args_rel p D ups nr ar (env_args nil (ups ++ ns1 ++ ws1)) gs' vs1 vs2 /\
          ihs_rel (env_args nil (ups ++ ns1 ++ ws1)) gs' vs1 vs2 ihs1 ihs2.
    Proof.
      intros ua1 ua2 ns1 ns2 c gs Ha1 Ha2 L1 L2 H12 Hc.
      pose proof (trefl _ _ H12) as H11.
      pose proof Ha1 as (_ & Hn1 & Hc1); pose proof Ha2 as (_ & Hn2 & Hc2).
      induction gs' as [| g gs' IH]; intros gs1 ws1 ws2 s s2 Heq Hp.
      - exists nil, nil, nil, nil, nil, nil; cbn; rewrite !List.app_nil_r.
        rewrite Heq, List.app_nil_r.
        refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hp (conj _ _)))))))); constructor.
      - assert (Hk : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
          by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
        pose proof (tprl _ _ _ H11 Hc _ _ _ Hk Hp) as Hp11.
        destruct g as [A | Ps].
        + assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
            by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
          destruct (Hn1 _ _ _ _ _ _ _ _ s H11 Hc HA Hp11) as (a0 & a1 & E0 & E1 & R1).
          destruct (Hn2 _ _ _ _ _ _ _ _ s H12 Hc HA Hp) as (a0' & a2 & E0' & E2 & R2).
          pose proof (functional_eval_exp _ _ _ _ E0 E0') as <-.
          pose proof (HaP _ _ _ _ _ _ _ _ H12 Hc HA Hp) as HP.
          assert (R12 : ar ns1 c (List.length (cargs_nonrec gs1)) ws1 (⇑! a1 s) (⇑! a2 s))
            by (etransitivity; [ symmetry; exact R1 | exact R2 ]).
          destruct (IH (gs1 ++ ca_arg A :: nil) (ws1 ++ ⇑! a1 s :: nil) (ws2 ++ ⇑! a2 s :: nil) (S s) s2)
            as (vs1 & vs2 & bss1 & bss2 & ihs1 & ihs2 & F1 & F2 & B1 & B2 & I1 & I2 & P & Hia & Hir).
          { rewrite Heq, <- List.app_assoc; reflexivity. }
          { rewrite cargs_nonrec_app, List.length_app, Nat.add_comm; cbn; apply tele_pre_snoc; assumption. }
          exists (⇑! a1 s :: vs1), (⇑! a2 s :: vs2), bss1, bss2, ihs1, ihs2.
          rewrite <- !List.app_assoc in P; cbn in P.
          refine (conj _ (conj _ (conj B1 (conj B2 (conj _ (conj _ (conj P (conj _ _)))))))).
          * econstructor; [ exact E1 |]; rewrite <- env_args_snoc, <- !List.app_assoc; exact F1.
          * econstructor; [ exact E2 |]; rewrite <- env_args_snoc, <- !List.app_assoc; exact F2.
          * constructor; exact I1.
          * constructor; exact I2.
          * constructor; rewrite <- env_args_snoc, <- !List.app_assoc; exact Hia.
          * constructor; rewrite <- env_args_snoc, <- !List.app_assoc; exact Hir.
        + destruct (Hc1 _ _ _ _ _ _ _ _ _ H11 Hc Heq Hp11) as (b0 & b1 & E0 & E1 & R1).
          destruct (Hc2 _ _ _ _ _ _ _ _ _ H12 Hc Heq Hp) as (b0' & b2 & E0' & E2 & R2).
          pose proof (functional_eval_exps' _ _ _ _ E0 E0') as <-.
          pose proof (ind_rel_var _ _ _ _ _ s Ha1 Ha2 L1 L2 R1 R2) as Hv.
          pose proof (ind_rel_var _ _ _ _ _ s Ha1 Ha1 L1 L1 R1 R1) as Hv1.
          pose proof (ttrans _ _ _ (tsym _ _ R1) R2) as R12.
          pose proof (ind_rel_mv _ _ _ _ Hv R1) as Hvb.
          destruct (Hmot _ _ _ _ R12 Hvb) as (t1 & t2 & T1 & T2 & HR).
          pose proof (var_per_elem s2 HR) as Hih.
          assert (Hih' : Rel b0 (⇑! (d_ind p (ua1 ++ b1)) s) b0 (⇑! (d_ind p (ua2 ++ b2)) s) (⇑! t1 s2) (⇑! t2 s2)).
          { apply (Rel_left _ _ _ _ _ _ (tsym _ _ R1) (trefl _ _ R1) Hvb Hv).
            apply (Rel_right _ _ _ _ _ _ R12 (tsym _ _ R1) Hvb Hvb); exact Hih. }
          destruct (IH (gs1 ++ ca_rec Ps :: nil) ws1 ws2 (S s) (S s2))
            as (vs1 & vs2 & bss1 & bss2 & ihs1 & ihs2 & F1 & F2 & B1 & B2 & I1 & I2 & P & Hia & Hir).
          { rewrite Heq, <- List.app_assoc; reflexivity. }
          { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact Hp. }
          exists (⇑! (d_ind p (ua1 ++ b1)) s :: vs1), (⇑! (d_ind p (ua2 ++ b2)) s :: vs2), (b1 :: bss1), (b2 :: bss2),
            (⇑! t1 s2 :: ihs1), (⇑! t2 s2 :: ihs2).
          refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj P (conj _ _)))))))).
          * econstructor; eassumption.
          * econstructor; eassumption.
          * constructor; [ exact (proj2 (length_tnr _ _ R1)) | exact B1 ].
          * constructor; [ exact (proj2 (length_tnr _ _ R2)) | exact B2 ].
          * econstructor; eassumption.
          * econstructor; eassumption.
          * econstructor; eassumption.
          * econstructor; eassumption.
    Qed.

    (** ** The Stuck Eliminator *)
    Lemma read_brs_rel : forall ua1 ua2 s ns1 ns2, ind_adm D ups nr ar ua1 -> ind_adm D ups nr ar ua2 ->
        List.length ua1 = ind_nu D -> List.length ua2 = ind_nu D ->
        fresh_tele gc_deps gc_stack (env_args nil ua1) T s ns1 ->
        fresh_tele gc_deps gc_stack (env_args nil ua2) T s ns2 -> tele_full nr T ns1 ns2 ->
        forall cs Bs1 Bs2, (forall c gs, In (c, gs) cs -> ind_con D c = Some gs) ->
        (forall c n B, In (c, n, B) Bs1 -> brs_lookup Bsa c = Some (n, B) /\ In (c, n, B) Bsa) ->
        (forall c n B, In (c, n, B) Bs2 -> brs_lookup Bsb c = Some (n, B) /\ In (c, n, B) Bsb) ->
        brs_names cs Bs1 -> brs_names cs Bs2 ->
        exists Bs', read_brs gc_deps gc_stack s ρa Aa p D ua1 cs Bs1 Bs' /\ read_brs gc_deps gc_stack s ρb Ab p D ua2 cs Bs2 Bs'.
    Proof.
      intros ua1 ua2 s ns1 ns2 Ha1 Ha2 L1 L2 F1 F2 H12.
      pose proof (trefl _ _ H12) as H11.
      induction cs as [| [c gs] cs IH]; intros [| [[c1 n1] B1] Bs1] [| [[c2 n2] B2] Bs2] Hcs HB1 HB2 Hn1 Hn2;
        cbn in Hn1, Hn2; try discriminate.
      - exists nbrs_nil; split; constructor.
      - injection Hn1 as <- Hn1; injection Hn2 as <- Hn2.
        assert (Hc : ind_con D c = Some gs) by (apply Hcs; left; reflexivity).
        destruct (HB1 c n1 B1 ltac:(left; reflexivity)) as [HL1 HI1].
        destruct (HB2 c n2 B2 ltac:(left; reflexivity)) as [HL2 HI2].
        pose proof (Hara _ _ _ _ Hc HI1) as Hn1e; pose proof (Harb _ _ _ _ Hc HI2) as Hn2e.
        assert (n2 = n1) as -> by lia.
        destruct (fresh_args _ _ _ _ _ _ Ha1 Ha2 L1 L2 H12 Hc gs nil nil nil (s + ind_nn D) (s + ind_nn D + List.length gs) eq_refl (tele_pre_nil _))
          as (vs1 & vs2 & bss1 & bss2 & ihs1 & ihs2 & C1 & C2 & B1l & B2l & I1 & I2 & P & Hia & Hir).
        rewrite !List.app_nil_r in C1, C2, Hia, Hir; cbn in P.
        destruct (length_tnr _ _ H12) as [Ln1 Ln2].
        assert (Hlen : forall ua ns : list domain, List.length ua = ind_nu D -> List.length ns = ind_nn D -> List.length (ua ++ ns) = ind_np D)
          by (intros; rewrite List.length_app; unfold ind_nn in *; lia).
        assert (Hm : ind_rel p D ups nr ar ns1 (d_con p c (ua1 ++ ns1 ++ vs1)) (d_con p c (ua2 ++ ns2 ++ vs2))).
        { rewrite !List.app_assoc; econstructor; [ exact H11 | exact Hc | apply Hlen; assumption | apply Hlen; assumption
            | rewrite skipn_app_exact by exact L1; exact H11 | rewrite skipn_app_exact by exact L2; exact H12
            | apply tele_full_of_pre; exact P | exact Hia ]. }
        destruct (Hbr _ _ _ _ _ Hc HL1 HL2 ns1 (ua1 ++ ns1) (ua2 ++ ns2) vs1 vs2 ihs1 ihs2 H11
                    (Hlen _ _ L1 Ln1) (Hlen _ _ L2 Ln2)
                    ltac:(rewrite skipn_app_exact by exact L1; exact H11) ltac:(rewrite skipn_app_exact by exact L2; exact H12)
                    (tele_full_of_pre _ _ _ _ P) Hia Hir) as (r1 & r2 & Er1 & Er2 & Hrr).
        rewrite !skipn_app_exact in Er1, Er2 by assumption.
        rewrite <- !List.app_assoc in Hrr.
        destruct (Hmot _ _ _ _ H12 Hm) as (t1 & t2 & T1 & T2 & HR).
        assert (Hrr' : Rel ns1 (d_con p c (ua1 ++ ns1 ++ vs1)) ns2 (d_con p c (ua2 ++ ns2 ++ vs2)) r1 r2)
          by (apply (Rel_right _ _ _ _ _ _ H11 H12 Hm Hm); exact Hrr).
        destruct (per_elem_then_per_top HR Hrr' (s + n1)) as (B' & RB1 & RB2).
        destruct (IH Bs1 Bs2) as (Bs' & RBs1 & RBs2).
        { intros c' gs' Hin; apply Hcs; right; exact Hin. }
        { intros c' n' Bx Hin; apply HB1; right; exact Hin. }
        { intros c' n' Bx Hin; apply HB2; right; exact Hin. }
        { exact Hn1. }
        { exact Hn2. }
        exists (nbrs_cons c n1 B' Bs'); split; econstructor; eassumption.
    Qed.

    Lemma per_bot_elim : forall ns as1 as2 e e',
        List.length as1 = ind_np D -> List.length as2 = ind_np D ->
        ind_adm D ups nr ar (List.firstn (ind_nu D) as1) -> ind_adm D ups nr ar (List.firstn (ind_nu D) as2) ->
        tele_full nr T ns (List.skipn (ind_nu D) as1) -> tele_full nr T ns (List.skipn (ind_nu D) as2) ->
        Dom e ≈ e' ∈ per_bot ->
        Dom d_elim ρa nm Aa Bsa p as1 e ≈ d_elim ρb nm Ab Bsb p as2 e' ∈ per_bot.
    Proof.
      intros * L1 L2 Ha1 Ha2 _ _ He s.
      destruct (He s) as (M & RM1 & RM2).
      assert (Lu1 : List.length (List.firstn (ind_nu D) as1) = ind_nu D) by (rewrite List.length_firstn; lia).
      assert (Lu2 : List.length (List.firstn (ind_nu D) as2) = ind_nu D) by (rewrite List.length_firstn; lia).
      destruct (fresh_np2 _ _ s Ha1 Ha2) as (ns1 & ns2 & F1 & F2 & H12).
      pose proof (ind_rel_var _ _ _ _ _ (s + ind_nn D) Ha1 Ha2 Lu1 Lu2 (trefl _ _ H12) H12) as Hv.
      destruct (Hmot _ _ _ _ H12 Hv) as (a1 & a2 & E1 & E2 & HR).
      destruct (per_univ_then_per_top_typ HR (S (s + ind_nn D))) as (A' & RA1 & RA2).
      assert (HndB : forall Bs, brs_names (ind_cons D) Bs -> List.NoDup (List.map (fun b => fst (fst b)) Bs))
        by (intros Bs HB; unfold brs_names in HB; rewrite <- HB; exact Hnd).
      destruct (read_brs_rel _ _ _ _ _ Ha1 Ha2 Lu1 Lu2 F1 F2 H12 (ind_cons D) Bsa Bsb) as (Bs' & RB1 & RB2).
      { intros c gs Hin; apply cons_lookup_nodup_in; assumption. }
      { intros c n B Hin; split; [ apply brs_lookup_nodup_in; [ apply HndB; exact Hna | exact Hin ] | exact Hin ]. }
      { intros c n B Hin; split; [ apply brs_lookup_nodup_in; [ apply HndB; exact Hnb | exact Hin ] | exact Hin ]. }
      { exact Hna. }
      { exact Hnb. }
      exists (ne_elim nm A' Bs' M); split; econstructor; eassumption.
    Qed.

    (** ** Related Elements Eliminate to Related Values *)
    Lemma per_ind_elim_all :
      (forall ns m m', ind_rel p D ups nr ar ns m m' -> forall ns', tele_full nr T ns ns' ->
         exists r r', eval_elim gc_deps gc_stack ρa nm Aa Bsa m r /\ eval_elim gc_deps gc_stack ρb nm Ab Bsb m' r' /\
           Rel ns m ns' m' r r') /\
      (forall ρ gs vs vs', ind_args_rel p D ups nr ar ρ gs vs vs' ->
         exists ihs ihs', eval_ihs gc_deps gc_stack ρa nm Aa Bsa gs vs ihs /\ eval_ihs gc_deps gc_stack ρb nm Ab Bsb gs vs' ihs' /\
           ihs_rel ρ gs vs vs' ihs ihs').
    Proof.
      apply ind_rel_mut_ind_all.
      - intros ns c gs bs bs' vs vs' Hns Hc Hb Hb' Hs Hs' Ha Hia IH ns' Hns'.
        destruct IH as (ihs & ihs' & Ei & Ei' & Hir).
        destruct (brs_names_lookup _ _ _ _ Hna Hc) as (n & Ba & HBa & HinA).
        destruct (brs_names_lookup _ _ _ _ Hnb Hc) as (n' & Bb & HBb & HinB).
        pose proof (Hara _ _ _ _ Hc HinA) as Hn; pose proof (Harb _ _ _ _ Hc HinB) as Hn'.
        assert (n' = n) as -> by lia.
        destruct (Hbr _ _ _ _ _ Hc HBa HBb _ _ _ _ _ _ _ Hns Hb Hb' Hs Hs' Ha Hia Hir) as (r & r' & Er & Er' & Hrr).
        destruct (ind_args_rel_length _ _ _ _ Hia) as [Hlv Hlv'].
        assert (Hm : ind_rel p D ups nr ar ns (d_con p c (bs ++ vs)) (d_con p c (bs' ++ vs'))) by (econstructor; eassumption).
        exists r, r'; split; [| split ].
        + eapply eval_elim_con; [ exact Hl | exact Hc | rewrite List.length_app; lia | exact HBa | exact Hn | |].
          * rewrite skipn_app_exact by exact Hb; exact Ei.
          * rewrite firstn_app_exact, skipn_app_exact by exact Hb; exact Er.
        + eapply eval_elim_con; [ exact Hl | exact Hc | rewrite List.length_app; lia | exact HBb | exact Hn | |].
          * rewrite skipn_app_exact by exact Hb'; exact Ei'.
          * rewrite firstn_app_exact, skipn_app_exact by exact Hb'; exact Er'.
        + apply (Rel_right _ _ _ _ _ _ Hns Hns' Hm Hm); exact Hrr.
      - intros as1 as2 ns e e' Hl1 Hl2 Ha1 Ha2 Hs1 Hs2 He ns' Hns'.
        assert (Hm : ind_rel p D ups nr ar ns (⇑ (d_ind p as1) e) (⇑ (d_ind p as2) e')) by (econstructor; eassumption).
        assert (H12 : tele_full nr T (List.skipn (ind_nu D) as1) (List.skipn (ind_nu D) as2)) by exact (ttrans _ _ _ (tsym _ _ Hs1) Hs2).
        pose proof (ind_rel_mv _ _ _ _ Hm Hs1) as Hm1.
        destruct (Hmot _ _ _ _ H12 Hm1) as (a1 & a2 & Ea1 & Ea2 & HR).
        exists (⇑ a1 (d_elim ρa nm Aa Bsa p as1 e)), (⇑ a2 (d_elim ρb nm Ab Bsb p as2 e')).
        split; [ eapply eval_elim_neut; eassumption | split; [ eapply eval_elim_neut; eassumption |] ].
        pose proof (per_bot_then_per_elem HR (per_bot_elim _ _ _ _ _ Hl1 Hl2 Ha1 Ha2 Hs1 Hs2 He)) as Hrr.
        apply (Rel_right _ _ _ _ _ _ Hs2 Hns' Hm Hm).
        apply (Rel_left _ _ _ _ _ _ H12 Hs2 Hm1 Hm); exact Hrr.
      - intros ρ; exists nil, nil; split; [ constructor | split; [ constructor | constructor ] ].
      - intros ρ A gs v v' vs vs' Hia (ihs & ihs' & Ei & Ei' & Hir).
        exists ihs, ihs'; split; [ constructor; exact Ei | split; [ constructor; exact Ei' | constructor; exact Hir ] ].
      - intros Ps ρ bs v v' gs vs vs' Hb Hr IHr Hia (ihs & ihs' & Ei & Ei' & Hir).
        destruct (IHr bs (ind_rel_ns_refl _ _ _ Hr)) as (ih & ih' & Eh & Eh' & Hhh).
        exists (ih :: ihs), (ih' :: ihs'); split; [ econstructor; eassumption | split; [ econstructor; eassumption |] ].
        econstructor; eassumption.
    Qed.

  End IndElim.
End Fixed_GCtx.
