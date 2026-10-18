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
    Variable (dr : list domain -> exp -> relation domain).
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
    Hypothesis (HdP : forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_full nr T ms ms' ->
                      ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                      tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
                      List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr dr ms ws (ptyp_doms t)) k ys ys' ->
                      PER (dr (ms ++ ws ++ ys) B)).
    Hypothesis (HdI : forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_full nr T ms ms' ->
                      ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                      tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
                      List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr dr ms ws (ptyp_doms t)) k ys ys' ->
                      (dr (ms ++ ws ++ ys) B <~> dr (ms' ++ ws' ++ ys') B)).
    Hypothesis (Had : ind_adm D ups nr ar dr ups).
    Hypothesis (Hle : ind_nu D <= ind_np D).
    Hypothesis (Hsimple : forall c gs gs1 t gs2, ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 -> ptyp_simple t = true).
    Hypothesis (Hplen : forall c gs gs1 t gs2, ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                  List.length (ptyp_ps t) = ind_nn D).

    Let tsym := tnr_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI.
    Let ttrans := tnr_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI.
    Let trefl := tnr_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI.
    Let trefl_r := tnr_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI.

    Lemma ind_rel_ns_refl : forall ns m m', ind_rel p D ups nr ar dr ns m m' -> tele_full nr T ns ns.
    Proof. intros * H; inversion H; subst; [ assumption | eapply trefl; eassumption ]. Qed.

    Lemma ind_rel_mv : forall ns ns1 m m', ind_rel p D ups nr ar dr ns m m' -> tele_full nr T ns ns1 ->
        ind_rel p D ups nr ar dr ns1 m m'.
    Proof. intros * H Hn; exact (proj1 (ind_rel_move p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups Had) _ _ _ H _ Hn). Qed.

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
    Hypothesis (Hmot : forall ns ns' m m', tele_full nr T ns ns' -> ind_rel p D ups nr ar dr ns m m' ->
                   exists a a', ⟦ Aa ⟧ env_args ρa (ns ++ m :: nil) ↘ a /\ ⟦ Ab ⟧ env_args ρb (ns' ++ m' :: nil) ↘ a' /\
                     DF a ≈ a' ∈ per_univ_elem i ↘ (Rel ns m ns' m')).

    (** The recursive result of a recursive argument [v] of shape [t], after
        the values [pre] of the shape's components: at the end, related at
        [Rel] at the parameters the shape evaluates to, and at a domain,
        pointwise. *)
    Fixpoint ih_rel (pre : list domain) (t : ptyp) (v v' ih ih' : domain) : Prop :=
      match t with
      | pt_self _ Ps => exists bs, eval_exps gc_deps gc_stack Ps (env_args nil (ups ++ pre)) bs /\ Rel bs v bs v' ih ih'
      | pt_aux _ _ => False
      | pt_pi B t => forall c c', dr pre B c c' ->
          exists fc fc' r r', $| v & c | gc_deps ⍮ gc_stack ↘ fc /\ $| v' & c' | gc_deps ⍮ gc_stack ↘ fc' /\
            $| ih & c | gc_deps ⍮ gc_stack ↘ r /\ $| ih' & c' | gc_deps ⍮ gc_stack ↘ r' /\
            ih_rel (pre ++ c :: nil) t fc fc' r r'
      end.

    (** The recursive results of related arguments, after the values [pre]
        of the non-uniform parameters and the non-recursive arguments before
        them. *)
    Inductive ihs_rel : list domain -> list carg -> list domain -> list domain -> list domain -> list domain -> Prop :=
    | ihs_rel_nil : forall pre, ihs_rel pre nil nil nil nil nil
    | ihs_rel_arg : forall pre A gs v v' vs vs' ihs ihs',
        ihs_rel (pre ++ v :: nil) gs vs vs' ihs ihs' -> ihs_rel pre (ca_arg A :: gs) (v :: vs) (v' :: vs') ihs ihs'
    | ihs_rel_rec : forall pre t gs v v' vs vs' ih ih' ihs ihs',
        ih_rel pre t v v' ih ih' ->
        ihs_rel pre gs vs vs' ihs ihs' -> ihs_rel pre (ca_rec t :: gs) (v :: vs) (v' :: vs') (ih :: ihs) (ih' :: ihs').

    Hypothesis (Hbr : forall c gs n Ba Bb, ind_con D c = Some gs ->
                   brs_lookup Bsa c = Some (n, Ba) -> brs_lookup Bsb c = Some (n, Bb) ->
                   forall ns bs bs' vs vs' ihs ihs',
                     tele_full nr T ns ns -> List.length bs = ind_np D -> List.length bs' = ind_np D ->
                     tele_full nr T ns (List.skipn (ind_nu D) bs) -> tele_full nr T ns (List.skipn (ind_nu D) bs') ->
                     tele_full (ar ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs') ->
                     ind_args_rel p D ups nr ar dr ns gs vs vs' ->
                     ihs_rel ns gs vs vs' ihs ihs' ->
                     exists r r', ⟦ Ba ⟧ env_args ρa (List.skipn (ind_nu D) bs ++ vs ++ ihs) ↘ r /\
                       ⟦ Bb ⟧ env_args ρb (List.skipn (ind_nu D) bs' ++ vs' ++ ihs') ↘ r' /\
                       Rel ns (d_con p c (bs ++ vs)) ns (d_con p c (bs' ++ vs')) r r').

    (** ** The Family Is Invariant *)

    Lemma Rel_right : forall ns m ns1 m1 ns2 m2, tele_full nr T ns ns1 -> tele_full nr T ns ns2 ->
        ind_rel p D ups nr ar dr ns m m1 -> ind_rel p D ups nr ar dr ns m m2 -> (Rel ns m ns1 m1 <~> Rel ns m ns2 m2).
    Proof.
      intros * H1 H2 Hm1 Hm2.
      destruct (Hmot _ _ _ _ H1 Hm1) as (a & a1 & Ea & Ea1 & HR1).
      destruct (Hmot _ _ _ _ H2 Hm2) as (b & a2 & Eb & Ea2 & HR2).
      assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
      eapply per_univ_elem_right_irrel; eassumption.
    Qed.

    Lemma Rel_left : forall ns1 m1 ns2 m2 ns' m', tele_full nr T ns1 ns' -> tele_full nr T ns2 ns' ->
        ind_rel p D ups nr ar dr ns1 m1 m' -> ind_rel p D ups nr ar dr ns2 m2 m' -> (Rel ns1 m1 ns' m' <~> Rel ns2 m2 ns' m').
    Proof.
      intros * H1 H2 Hm1 Hm2.
      destruct (Hmot _ _ _ _ H1 Hm1) as (a1 & a & Ea1 & Ea & HR1).
      destruct (Hmot _ _ _ _ H2 Hm2) as (a2 & b & Ea2 & Eb & HR2).
      assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
      eapply per_univ_elem_left_irrel; eassumption.
    Qed.

    Lemma ind_args_rel_length : forall pre gs vs vs', ind_args_rel p D ups nr ar dr pre gs vs vs' ->
        List.length vs = List.length gs /\ List.length vs' = List.length gs.
    Proof. induction 1; cbn; [ split; reflexivity | destruct IHind_args_rel; split; congruence | destruct IHind_args_rel; split; congruence ]. Qed.

    (** ** Fresh Variables

        The variables a stuck eliminator's readback makes at admissible
        uniform parameters: those of two such are related, through those at
        [ups]. *)
    Lemma fresh_np : forall ua, ind_adm D ups nr ar dr ua -> forall T' T0 vs vs' s, T = T0 ++ T' ->
        tele_pre nr (List.length T0) vs vs' ->
        exists ws ws', fresh_tele gc_deps gc_stack (env_args nil (ups ++ vs)) T' s ws /\
          fresh_tele gc_deps gc_stack (env_args nil (ua ++ vs')) T' s ws' /\
          tele_pre nr (List.length T) (vs ++ ws) (vs' ++ ws').
    Proof.
      intros ua [Hn _ _ _]; induction T' as [| e T' IH]; intros T0 vs vs' s HT Hp.
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

    Lemma fresh_np2 : forall ua1 ua2 s, ind_adm D ups nr ar dr ua1 -> ind_adm D ups nr ar dr ua2 ->
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

    Lemma ind_rel_neut' : forall ns ua1 ua2 bs1 bs2 m m', ind_adm D ups nr ar dr ua1 -> ind_adm D ups nr ar dr ua2 ->
        List.length ua1 = ind_nu D -> List.length ua2 = ind_nu D ->
        tele_full nr T ns bs1 -> tele_full nr T ns bs2 -> Dom m ≈ m' ∈ per_bot ->
        ind_rel p D ups nr ar dr ns (⇑ (d_ind p (ua1 ++ bs1)) m) (⇑ (d_ind p (ua2 ++ bs2)) m').
    Proof.
      intros * H1 H2 L1 L2 B1 B2 Hm.
      destruct (length_tnr _ _ B1) as [_ L1']; destruct (length_tnr _ _ B2) as [_ L2'].
      assert (Hnp : ind_nn D = ind_np D - ind_nu D) by reflexivity.
      apply ind_rel_neut.
      - rewrite List.length_app; lia.
      - rewrite List.length_app; lia.
      - rewrite firstn_app_exact by exact L1; exact H1.
      - rewrite firstn_app_exact by exact L2; exact H2.
      - rewrite skipn_app_exact by exact L1; exact B1.
      - rewrite skipn_app_exact by exact L2; exact B2.
      - exact Hm.
    Qed.

    Lemma ind_rel_var : forall ns ua1 ua2 bs1 bs2 k, ind_adm D ups nr ar dr ua1 -> ind_adm D ups nr ar dr ua2 ->
        List.length ua1 = ind_nu D -> List.length ua2 = ind_nu D ->
        tele_full nr T ns bs1 -> tele_full nr T ns bs2 ->
        ind_rel p D ups nr ar dr ns (⇑! (d_ind p (ua1 ++ bs1)) k) (⇑! (d_ind p (ua2 ++ bs2)) k).
    Proof. intros; apply ind_rel_neut'; try assumption; apply var_per_bot. Qed.

    Let tprl := tar_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI.

    Lemma per_bot_app : forall m m' n n', Dom m ≈ m' ∈ per_bot -> Dom n ≈ n' ∈ per_top -> Dom m $ᵈ n ≈ m' $ᵈ n' ∈ per_bot.
    Proof.
      intros * Hm Hn s; destruct (Hm s) as (M & HM & HM'); destruct (Hn s) as (N & HN & HN').
      exists (M $ⁿ N); split; constructor; assumption.
    Qed.

    (** The type of an argument of a simple shape is defined at an admissible
        base, after related domains. *)
    Lemma shty_exists : forall ua, ind_adm D ups nr ar dr ua ->
        forall ns1 ns2 c gs1 t0 gs2 ws1 ws2, tele_full nr T ns1 ns2 -> ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
        tele_pre (ar ns1 c) (List.length (cargs_nonrec gs1)) ws1 ws2 ->
        forall k ys1 ys2, k <= List.length (ptyp_doms t0) -> tele_pre (shape_tr dr ns1 ws1 (ptyp_doms t0)) k ys1 ys2 ->
          exists a, eval_shty gc_deps gc_stack p ua (env_args nil (ua ++ ns2 ++ ws2 ++ ys2)) (ptyp_skip k t0) a.
    Proof.
      intros ua [_ _ Hcl Hdt] * H12 Hc Hw k ys1 ys2 Hk Hy.
      pose proof (Hsimple _ _ _ _ _ Hc eq_refl) as Hs0.
      destruct (Nat.eq_dec k (List.length (ptyp_doms t0))) as [-> | Hne].
      - rewrite (ptyp_skip_end _ Hs0).
        assert (Hyf : tele_full (shape_tr dr ns1 ws1 (ptyp_doms t0)) (ptyp_doms t0) ys1 ys2)
          by (destruct Hy as [Hyl Hya]; split; [ exact Hyl | exact Hya ]).
        destruct (Hcl _ _ _ _ _ _ _ _ _ _ _ H12 Hc eq_refl Hw Hyf) as [bs bs' _ E' _].
        eexists; econstructor; exact E'.
      - destruct (ptyp_skip_lt k t0 ltac:(lia)) as (B & HB & Hs); rewrite Hs.
        destruct (Hdt _ _ _ _ _ _ _ _ _ _ _ _ _ H12 Hc eq_refl Hw HB Hy) as (b & b' & _ & Eb' & _).
        eexists; econstructor; exact Eb'.
    Qed.

    (** A neutral of the type of an argument of a shape at two admissible
        bases, after related domains, is related by the shape. *)
    Lemma shape_neut : forall ua1 ua2, ind_adm D ups nr ar dr ua1 -> ind_adm D ups nr ar dr ua2 ->
        List.length ua1 = ind_nu D -> List.length ua2 = ind_nu D ->
        forall ns1 ns2 c gs1 t0 gs2 ws1 ws2, tele_full nr T ns1 ns2 -> ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
        tele_pre (ar ns1 c) (List.length (cargs_nonrec gs1)) ws1 ws2 ->
        forall n k ys1 ys2 a1 a2 m m', k + n = List.length (ptyp_doms t0) ->
          tele_pre (shape_tr dr ns1 ws1 (ptyp_doms t0)) k ys1 ys2 ->
          eval_shty gc_deps gc_stack p ua1 (env_args nil (ua1 ++ ns1 ++ ws1 ++ ys1)) (ptyp_skip k t0) a1 ->
          eval_shty gc_deps gc_stack p ua2 (env_args nil (ua2 ++ ns2 ++ ws2 ++ ys2)) (ptyp_skip k t0) a2 ->
          Dom m ≈ m' ∈ per_bot ->
          ind_shape_rel p D ups nr ar dr (ns1 ++ ws1 ++ ys1) (ptyp_skip k t0) (⇑ a1 m) (⇑ a2 m').
    Proof.
      intros ua1 ua2 Ha1 Ha2 L1 L2 ns1 ns2 c gs1 t0 gs2 ws1 ws2 H12 Hc Hw.
      pose proof (trefl _ _ H12) as H11.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
        by (rewrite cargs_nonrec_app, List.length_app; lia).
      pose proof (tprl _ _ _ H11 Hc _ _ _ HK Hw) as Hww.
      pose proof (iad_recs _ _ _ _ _ _ Ha1) as Hcl1; pose proof (iad_recs _ _ _ _ _ _ Ha2) as Hcl2.
      pose proof (iad_doms _ _ _ _ _ _ (adm_base p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ Ha1 Ha2)) as Hd12.
      induction n as [| n IH]; intros k ys1 ys2 a1 a2 m m' Hkn Hy E1 E2 Hm.
      - destruct (ptyp_skip k t0) as [j Ps | j Ps | B t] eqn:Hs.
        + destruct (ptyp_skip_self _ _ _ _ Hs) as [Hkd HPs].
          inversion E1; subst a1.
          match goal with H : ⟦ _ ⟧* _ ⍮ _ ⍮ env_args nil (ua1 ++ _) ↘ ?b |- _ => rename H into Ebs1; rename b into bs1 end.
          inversion E2; subst a2.
          match goal with H : ⟦ _ ⟧* _ ⍮ _ ⍮ env_args nil (ua2 ++ _) ↘ ?b |- _ => rename H into Ebs2; rename b into bs2 end.
          assert (Hyf : tele_full (shape_tr dr ns1 ws1 (ptyp_doms t0)) (ptyp_doms t0) ys1 ys2)
            by (destruct Hy as [Hyl Hya]; split; [ lia | exact Hya ]).
          assert (Hyy : tele_full (shape_tr dr ns1 ws1 (ptyp_doms t0)) (ptyp_doms t0) ys1 ys1).
          { apply tele_full_of_pre.
            eapply (tsh_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ns1 c _ gs1 t0 gs2 ws1 H11 Hc eq_refl Hww);
              [ lia | apply tele_full_pre; exact Hyf ]. }
          destruct (Hcl1 _ _ _ _ _ _ _ _ _ _ _ H11 Hc eq_refl Hww Hyy) as [b0 b1 F0 F1 R1].
          destruct (Hcl2 _ _ _ _ _ _ _ _ _ _ _ H12 Hc eq_refl Hw Hyf) as [b0' b2 F0' F2 R2].
          rewrite HPs in F0, F1, F0', F2.
          pose proof (functional_eval_exps' _ _ _ _ F0 F0') as <-.
          pose proof (functional_eval_exps' _ _ _ _ F1 Ebs1) as <-.
          pose proof (functional_eval_exps' _ _ _ _ F2 Ebs2) as <-.
          econstructor; [ exact F0 | exact (ind_rel_neut' _ _ _ _ _ _ _ Ha1 Ha2 L1 L2 R1 R2 Hm) ].
        + inversion E1.
        + destruct (ptyp_skip_pi _ _ _ _ Hs) as [HB _].
          assert (k < List.length (ptyp_doms t0)) by (apply List.nth_error_Some; congruence); lia.
      - destruct (ptyp_skip k t0) as [j Ps | j Ps | B t] eqn:Hs.
        + destruct (ptyp_skip_self _ _ _ _ Hs) as [Hkd _]; lia.
        + inversion E1.
        + destruct (ptyp_skip_pi _ _ _ _ Hs) as [HB Hs'].
          assert (Hkl : k < List.length (ptyp_doms t0)) by (apply List.nth_error_Some; congruence).
          inversion E1; subst a1.
          match goal with H : ⟦ B ⟧ _ ⍮ _ ⍮ env_args nil (ua1 ++ _) ↘ ?b |- _ => rename H into Eb1; rename b into b1 end.
          inversion E2; subst a2.
          match goal with H : ⟦ B ⟧ _ ⍮ _ ⍮ env_args nil (ua2 ++ _) ↘ ?b |- _ => rename H into Eb2; rename b into b2 end.
          destruct (Hd12 _ _ _ _ _ _ _ _ _ _ _ _ _ H12 Hc eq_refl Hw HB Hy) as (b1' & b2' & Eb1' & Eb2' & Htop).
          assert (b1' = b1) as -> by (eapply functional_eval_exp; eassumption).
          assert (b2' = b2) as -> by (eapply functional_eval_exp; eassumption).
          pose proof (tsh_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ns1 c _ gs1 t0 gs2 ws1 H11 Hc eq_refl Hww k ys1 ys2
                        ltac:(lia) Hy) as Hyy.
          pose proof (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ H11 Hc eq_refl Hww HB Hyy) as HPd.
          constructor; intros c0 c0' Hcc.
          assert (Hcc0 : dr (ns1 ++ ws1 ++ ys1) B c0 c0) by (etransitivity; [ exact Hcc | symmetry; exact Hcc ]).
          assert (Hy' : tele_pre (shape_tr dr ns1 ws1 (ptyp_doms t0)) (S k) (ys1 ++ c0 :: nil) (ys2 ++ c0' :: nil))
            by (apply tele_pre_snoc; [ exact Hy | unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HB); exact Hcc ]).
          assert (Hyy' : tele_pre (shape_tr dr ns1 ws1 (ptyp_doms t0)) (S k) (ys1 ++ c0 :: nil) (ys1 ++ c0 :: nil))
            by (apply tele_pre_snoc; [ exact Hyy | unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HB); exact Hcc0 ]).
          destruct (shty_exists _ Ha1 _ _ _ _ _ _ _ _ H11 Hc Hww (S k) _ _ ltac:(lia) Hyy') as [a1' Ea1'].
          destruct (shty_exists _ Ha2 _ _ _ _ _ _ _ _ H12 Hc Hw (S k) _ _ ltac:(lia) Hy') as [a2' Ea2'].
          rewrite Hs' in Ea1', Ea2'.
          econstructor; [ eapply eval_app_neut, eval_fam_cod_shfam; rewrite <- env_args_snoc3; exact Ea1'
                        | eapply eval_app_neut, eval_fam_cod_shfam; rewrite <- env_args_snoc3; exact Ea2' |].
          replace ((ns1 ++ ws1 ++ ys1) ++ c0 :: nil) with (ns1 ++ ws1 ++ (ys1 ++ c0 :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
          rewrite <- Hs'.
          apply (IH (S k) _ _ _ _ _ _ ltac:(lia) Hy'); [ rewrite Hs'; exact Ea1' | rewrite Hs'; exact Ea2' |].
          apply per_bot_app; [ exact Hm | exact (Htop _ _ Hcc) ].
    Qed.

    (** A neutral of the type of the recursive result of such a neutral is
        related to the other's. *)
    Lemma ih_neut : forall ua1 ua2, ind_adm D ups nr ar dr ua1 -> ind_adm D ups nr ar dr ua2 ->
        List.length ua1 = ind_nu D -> List.length ua2 = ind_nu D ->
        forall ns1 ns2 c gs1 t0 gs2 ws1 ws2, tele_full nr T ns1 ns2 -> ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
        tele_pre (ar ns1 c) (List.length (cargs_nonrec gs1)) ws1 ws2 ->
        forall n k ys1 ys2 a1 a2 m m' e e', k + n = List.length (ptyp_doms t0) ->
          tele_pre (shape_tr dr ns1 ws1 (ptyp_doms t0)) k ys1 ys2 ->
          eval_shty gc_deps gc_stack p ua1 (env_args nil (ua1 ++ ns1 ++ ws1 ++ ys1)) (ptyp_skip k t0) a1 ->
          eval_shty gc_deps gc_stack p ua2 (env_args nil (ua2 ++ ns2 ++ ws2 ++ ys2)) (ptyp_skip k t0) a2 ->
          Dom m ≈ m' ∈ per_bot -> Dom e ≈ e' ∈ per_bot ->
          exists h1 h2, eval_ihty gc_deps gc_stack ρa Aa (env_args nil (ua1 ++ ns1 ++ ws1 ++ ys1)) (ptyp_skip k t0) (⇑ a1 m) h1 /\
            eval_ihty gc_deps gc_stack ρb Ab (env_args nil (ua2 ++ ns2 ++ ws2 ++ ys2)) (ptyp_skip k t0) (⇑ a2 m') h2 /\
            ih_rel (ns1 ++ ws1 ++ ys1) (ptyp_skip k t0) (⇑ a1 m) (⇑ a2 m') (⇑ h1 e) (⇑ h2 e').
    Proof.
      intros ua1 ua2 Ha1 Ha2 L1 L2 ns1 ns2 c gs1 t0 gs2 ws1 ws2 H12 Hc Hw.
      pose proof (trefl _ _ H12) as H11.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
        by (rewrite cargs_nonrec_app, List.length_app; lia).
      pose proof (tprl _ _ _ H11 Hc _ _ _ HK Hw) as Hww.
      pose proof (iad_recs _ _ _ _ _ _ Ha1) as Hcl1; pose proof (iad_recs _ _ _ _ _ _ Ha2) as Hcl2.
      pose proof (iad_doms _ _ _ _ _ _ (adm_base p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ Ha1 Ha2)) as Hd12.
      induction n as [| n IH]; intros k ys1 ys2 a1 a2 m m' e e' Hkn Hy E1 E2 Hm He.
      - destruct (ptyp_skip k t0) as [j Ps | j Ps | B t] eqn:Hs.
        + destruct (ptyp_skip_self _ _ _ _ Hs) as [Hkd HPs].
          inversion E1; subst a1.
          match goal with H : ⟦ _ ⟧* _ ⍮ _ ⍮ env_args nil (ua1 ++ _) ↘ ?b |- _ => rename H into Ebs1; rename b into bs1 end.
          inversion E2; subst a2.
          match goal with H : ⟦ _ ⟧* _ ⍮ _ ⍮ env_args nil (ua2 ++ _) ↘ ?b |- _ => rename H into Ebs2; rename b into bs2 end.
          assert (Hyf : tele_full (shape_tr dr ns1 ws1 (ptyp_doms t0)) (ptyp_doms t0) ys1 ys2)
            by (destruct Hy as [Hyl Hya]; split; [ lia | exact Hya ]).
          assert (Hyy : tele_full (shape_tr dr ns1 ws1 (ptyp_doms t0)) (ptyp_doms t0) ys1 ys1).
          { apply tele_full_of_pre.
            eapply (tsh_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ns1 c _ gs1 t0 gs2 ws1 H11 Hc eq_refl Hww);
              [ lia | apply tele_full_pre; exact Hyf ]. }
          destruct (Hcl1 _ _ _ _ _ _ _ _ _ _ _ H11 Hc eq_refl Hww Hyy) as [b0 b1 F0 F1 R1].
          destruct (Hcl2 _ _ _ _ _ _ _ _ _ _ _ H12 Hc eq_refl Hw Hyf) as [b0' b2 F0' F2 R2].
          rewrite HPs in F0, F1, F0', F2.
          pose proof (functional_eval_exps' _ _ _ _ F0 F0') as <-.
          pose proof (functional_eval_exps' _ _ _ _ F1 Ebs1) as <-.
          pose proof (functional_eval_exps' _ _ _ _ F2 Ebs2) as <-.
          pose proof (ind_rel_neut' _ _ _ _ _ _ _ Ha1 Ha2 L1 L2 R1 R2 Hm) as Hv.
          pose proof (ttrans _ _ _ (tsym _ _ R1) R2) as R12.
          pose proof (ind_rel_mv _ _ _ _ Hv R1) as Hvb.
          destruct (Hmot _ _ _ _ R12 Hvb) as (h1 & h2 & T1 & T2 & HR).
          exists h1, h2; split; [ econstructor; eassumption | split; [ econstructor; eassumption |] ].
          exists b0; split; [ exact F0 |].
          pose proof (per_bot_then_per_elem HR He) as Hih.
          apply (Rel_left _ _ _ _ _ _ (tsym _ _ R1) (trefl _ _ R1) Hvb Hv).
          apply (Rel_right _ _ _ _ _ _ R12 (tsym _ _ R1) Hvb Hvb); exact Hih.
        + inversion E1.
        + destruct (ptyp_skip_pi _ _ _ _ Hs) as [HB _].
          assert (k < List.length (ptyp_doms t0)) by (apply List.nth_error_Some; congruence); lia.
      - destruct (ptyp_skip k t0) as [j Ps | j Ps | B t] eqn:Hs.
        + destruct (ptyp_skip_self _ _ _ _ Hs) as [Hkd _]; lia.
        + inversion E1.
        + destruct (ptyp_skip_pi _ _ _ _ Hs) as [HB Hs'].
          assert (Hkl : k < List.length (ptyp_doms t0)) by (apply List.nth_error_Some; congruence).
          inversion E1; subst a1.
          match goal with H : ⟦ B ⟧ _ ⍮ _ ⍮ env_args nil (ua1 ++ _) ↘ ?b |- _ => rename H into Eb1; rename b into b1 end.
          inversion E2; subst a2.
          match goal with H : ⟦ B ⟧ _ ⍮ _ ⍮ env_args nil (ua2 ++ _) ↘ ?b |- _ => rename H into Eb2; rename b into b2 end.
          destruct (Hd12 _ _ _ _ _ _ _ _ _ _ _ _ _ H12 Hc eq_refl Hw HB Hy) as (b1' & b2' & Eb1' & Eb2' & Htop).
          assert (b1' = b1) as -> by (eapply functional_eval_exp; eassumption).
          assert (b2' = b2) as -> by (eapply functional_eval_exp; eassumption).
          pose proof (tsh_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ns1 c _ gs1 t0 gs2 ws1 H11 Hc eq_refl Hww k ys1 ys2
                        ltac:(lia) Hy) as Hyy.
          exists (Πᵈ b1 (nil ↦ d_ihfam ρa Aa (env_args nil (ua1 ++ ns1 ++ ws1 ++ ys1)) t (⇑ (Πᵈ b1 (nil ↦ d_shfam p ua1 (env_args nil (ua1 ++ ns1 ++ ws1 ++ ys1)) t) fam_cod) m)) fam_cod),
            (Πᵈ b2 (nil ↦ d_ihfam ρb Ab (env_args nil (ua2 ++ ns2 ++ ws2 ++ ys2)) t (⇑ (Πᵈ b2 (nil ↦ d_shfam p ua2 (env_args nil (ua2 ++ ns2 ++ ws2 ++ ys2)) t) fam_cod) m')) fam_cod).
          split; [ econstructor; exact Eb1 | split; [ econstructor; exact Eb2 |] ].
          cbn [ih_rel]; intros c0 c0' Hcc.
          assert (Hcc0 : dr (ns1 ++ ws1 ++ ys1) B c0 c0)
            by (pose proof (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ H11 Hc eq_refl Hww HB Hyy) as HPd;
                etransitivity; [ exact Hcc | symmetry; exact Hcc ]).
          assert (Hy' : tele_pre (shape_tr dr ns1 ws1 (ptyp_doms t0)) (S k) (ys1 ++ c0 :: nil) (ys2 ++ c0' :: nil))
            by (apply tele_pre_snoc; [ exact Hy | unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HB); exact Hcc ]).
          assert (Hyy' : tele_pre (shape_tr dr ns1 ws1 (ptyp_doms t0)) (S k) (ys1 ++ c0 :: nil) (ys1 ++ c0 :: nil))
            by (apply tele_pre_snoc; [ exact Hyy | unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HB); exact Hcc0 ]).
          destruct (shty_exists _ Ha1 _ _ _ _ _ _ _ _ H11 Hc Hww (S k) _ _ ltac:(lia) Hyy') as [a1' Ea1'].
          destruct (shty_exists _ Ha2 _ _ _ _ _ _ _ _ H12 Hc Hw (S k) _ _ ltac:(lia) Hy') as [a2' Ea2'].
          pose proof (per_bot_app _ _ _ _ Hm (Htop _ _ Hcc)) as Hm'.
          pose proof (per_bot_app _ _ _ _ He (Htop _ _ Hcc)) as He'.
          destruct (IH (S k) _ _ _ _ _ _ _ _ ltac:(lia) Hy' Ea1' Ea2' Hm' He') as (h1 & h2 & G1 & G2 & Hih).
          rewrite Hs' in Ea1', Ea2', G1, G2, Hih.
          assert (Ap1 : $| ⇑ (Πᵈ b1 (nil ↦ d_shfam p ua1 (env_args nil (ua1 ++ ns1 ++ ws1 ++ ys1)) t) fam_cod) m & c0 | gc_deps ⍮ gc_stack
                          ↘ ⇑ a1' (m $ᵈ ⇓ b1 c0))
            by (eapply eval_app_neut, eval_fam_cod_shfam; rewrite <- env_args_snoc3; exact Ea1').
          assert (Ap2 : $| ⇑ (Πᵈ b2 (nil ↦ d_shfam p ua2 (env_args nil (ua2 ++ ns2 ++ ws2 ++ ys2)) t) fam_cod) m' & c0' | gc_deps ⍮ gc_stack
                          ↘ ⇑ a2' (m' $ᵈ ⇓ b2 c0'))
            by (eapply eval_app_neut, eval_fam_cod_shfam; rewrite <- env_args_snoc3; exact Ea2').
          exists (⇑ a1' (m $ᵈ ⇓ b1 c0)), (⇑ a2' (m' $ᵈ ⇓ b2 c0')), (⇑ h1 (e $ᵈ ⇓ b1 c0)), (⇑ h2 (e' $ᵈ ⇓ b2 c0')).
          split; [ exact Ap1 | split; [ exact Ap2 | split; [| split ] ] ].
          * eapply eval_app_neut, eval_fam_cod_ihfam; [ exact Ap1 | rewrite <- env_args_snoc3; exact G1 ].
          * eapply eval_app_neut, eval_fam_cod_ihfam; [ exact Ap2 | rewrite <- env_args_snoc3; exact G2 ].
          * replace ((ns1 ++ ws1 ++ ys1) ++ c0 :: nil) with (ns1 ++ ws1 ++ (ys1 ++ c0 :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
            exact Hih.
    Qed.

    Lemma fresh_args : forall ua1 ua2 ns1 ns2 c gs, ind_adm D ups nr ar dr ua1 -> ind_adm D ups nr ar dr ua2 ->
        List.length ua1 = ind_nu D -> List.length ua2 = ind_nu D ->
        tele_full nr T ns1 ns2 -> ind_con D c = Some gs ->
        forall gs' gs1 ws1 ws2 s s2, gs = gs1 ++ gs' ->
        tele_pre (ar ns1 c) (List.length (cargs_nonrec gs1)) ws1 ws2 ->
        exists vs1 vs2 ihs1 ihs2,
          fresh_cargs gc_deps gc_stack p ua1 (env_args nil (ua1 ++ ns1 ++ ws1)) gs' s vs1 /\
          fresh_cargs gc_deps gc_stack p ua2 (env_args nil (ua2 ++ ns2 ++ ws2)) gs' s vs2 /\
          fresh_ihs gc_deps gc_stack ρa Aa (env_args nil (ua1 ++ ns1 ++ ws1)) gs' vs1 s2 ihs1 /\
          fresh_ihs gc_deps gc_stack ρb Ab (env_args nil (ua2 ++ ns2 ++ ws2)) gs' vs2 s2 ihs2 /\
          tele_pre (ar ns1 c) (List.length (cargs_nonrec gs)) (ws1 ++ nonrec_vals gs' vs1) (ws2 ++ nonrec_vals gs' vs2) /\
          ind_args_rel p D ups nr ar dr (ns1 ++ ws1) gs' vs1 vs2 /\
          ihs_rel (ns1 ++ ws1) gs' vs1 vs2 ihs1 ihs2.
    Proof.
      intros ua1 ua2 ns1 ns2 c gs Ha1 Ha2 L1 L2 H12 Hc.
      pose proof (trefl _ _ H12) as H11.
      pose proof (iad_args _ _ _ _ _ _ Ha1) as Hn1; pose proof (iad_args _ _ _ _ _ _ Ha2) as Hn2.
      induction gs' as [| g gs' IH]; intros gs1 ws1 ws2 s s2 Heq Hp.
      - exists nil, nil, nil, nil; cbn; rewrite !List.app_nil_r.
        rewrite Heq, List.app_nil_r.
        refine (conj _ (conj _ (conj _ (conj _ (conj Hp (conj _ _)))))); constructor.
      - assert (Hk : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
          by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
        pose proof (tprl _ _ _ H11 Hc _ _ _ Hk Hp) as Hp11.
        destruct g as [A | t].
        + assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
            by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
          destruct (Hn1 _ _ _ _ _ _ _ _ s H11 Hc HA Hp11) as (a0 & a1 & E0 & E1 & R1).
          destruct (Hn2 _ _ _ _ _ _ _ _ s H12 Hc HA Hp) as (a0' & a2 & E0' & E2 & R2).
          pose proof (functional_eval_exp _ _ _ _ E0 E0') as <-.
          pose proof (HaP _ _ _ _ _ _ _ _ H12 Hc HA Hp) as HP.
          assert (R12 : ar ns1 c (List.length (cargs_nonrec gs1)) ws1 (⇑! a1 s) (⇑! a2 s))
            by (etransitivity; [ symmetry; exact R1 | exact R2 ]).
          destruct (IH (gs1 ++ ca_arg A :: nil) (ws1 ++ ⇑! a1 s :: nil) (ws2 ++ ⇑! a2 s :: nil) (S s) s2)
            as (vs1 & vs2 & ihs1 & ihs2 & F1 & F2 & I1 & I2 & P & Hia & Hir).
          { rewrite Heq, <- List.app_assoc; reflexivity. }
          { rewrite cargs_nonrec_app, List.length_app, Nat.add_comm; cbn; apply tele_pre_snoc; assumption. }
          exists (⇑! a1 s :: vs1), (⇑! a2 s :: vs2), ihs1, ihs2.
          rewrite <- !List.app_assoc in P; cbn in P.
          refine (conj _ (conj _ (conj _ (conj _ (conj P (conj _ _)))))).
          * econstructor; [ exact E1 |]; rewrite <- env_args_snoc, <- !List.app_assoc; exact F1.
          * econstructor; [ exact E2 |]; rewrite <- env_args_snoc, <- !List.app_assoc; exact F2.
          * constructor; rewrite <- env_args_snoc, <- !List.app_assoc; exact I1.
          * constructor; rewrite <- env_args_snoc, <- !List.app_assoc; exact I2.
          * constructor; rewrite <- !List.app_assoc; exact Hia.
          * constructor; rewrite <- !List.app_assoc; exact Hir.
        + subst gs.
          destruct (shty_exists _ Ha1 _ _ _ _ _ _ _ _ H11 Hc Hp11 0 nil nil ltac:(lia) (tele_pre_nil _)) as [a1 Ea1].
          destruct (shty_exists _ Ha2 _ _ _ _ _ _ _ _ H12 Hc Hp 0 nil nil ltac:(lia) (tele_pre_nil _)) as [a2 Ea2].
          cbn [ptyp_skip] in Ea1, Ea2; rewrite List.app_nil_r in Ea1, Ea2.
          pose proof (shape_neut _ _ Ha1 Ha2 L1 L2 _ _ _ _ _ _ _ _ H12 Hc Hp (List.length (ptyp_doms t)) 0 nil nil a1 a2
                        (d_var s) (d_var s) eq_refl (tele_pre_nil _)
                        ltac:(rewrite List.app_nil_r; exact Ea1) ltac:(rewrite List.app_nil_r; exact Ea2) var_per_bot) as Hsh.
          destruct (ih_neut _ _ Ha1 Ha2 L1 L2 _ _ _ _ _ _ _ _ H12 Hc Hp (List.length (ptyp_doms t)) 0 nil nil a1 a2
                        (d_var s) (d_var s) (d_var s2) (d_var s2) eq_refl (tele_pre_nil _)
                        ltac:(rewrite List.app_nil_r; exact Ea1) ltac:(rewrite List.app_nil_r; exact Ea2) var_per_bot var_per_bot)
            as (h1 & h2 & G1 & G2 & Hih).
          cbn [ptyp_skip] in Hsh, G1, G2, Hih; rewrite List.app_nil_r in Hsh, G1, G2, Hih.
          destruct (IH (gs1 ++ ca_rec t :: nil) ws1 ws2 (S s) (S s2))
            as (vs1 & vs2 & ihs1 & ihs2 & F1 & F2 & I1 & I2 & P & Hia & Hir).
          { rewrite <- List.app_assoc; reflexivity. }
          { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact Hp. }
          exists (⇑! a1 s :: vs1), (⇑! a2 s :: vs2), (⇑! h1 s2 :: ihs1), (⇑! h2 s2 :: ihs2).
          refine (conj _ (conj _ (conj _ (conj _ (conj P (conj _ _)))))).
          * econstructor; eassumption.
          * econstructor; eassumption.
          * econstructor; eassumption.
          * econstructor; eassumption.
          * econstructor; eassumption.
          * econstructor; eassumption.
    Qed.

    (** ** The Stuck Eliminator *)
    Lemma read_brs_rel : forall ua1 ua2 s ns1 ns2, ind_adm D ups nr ar dr ua1 -> ind_adm D ups nr ar dr ua2 ->
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
          as (vs1 & vs2 & ihs1 & ihs2 & C1 & C2 & I1 & I2 & P & Hia & Hir).
        rewrite !List.app_nil_r in C1, C2, I1, I2, Hia, Hir; cbn in P.
        destruct (length_tnr _ _ H12) as [Ln1 Ln2].
        assert (Hlen : forall ua ns : list domain, List.length ua = ind_nu D -> List.length ns = ind_nn D -> List.length (ua ++ ns) = ind_np D)
          by (intros; rewrite List.length_app; unfold ind_nn in *; lia).
        assert (Hm : ind_rel p D ups nr ar dr ns1 (d_con p c (ua1 ++ ns1 ++ vs1)) (d_con p c (ua2 ++ ns2 ++ vs2))).
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
        exists (nbrs_cons c n1 B' Bs'); split; econstructor; try eassumption; intros gs1' t' gs2' E; exact (Hplen _ _ _ _ _ Hc E).
    Qed.

    Lemma per_bot_elim : forall ns as1 as2 e e',
        List.length as1 = ind_np D -> List.length as2 = ind_np D ->
        ind_adm D ups nr ar dr (List.firstn (ind_nu D) as1) -> ind_adm D ups nr ar dr (List.firstn (ind_nu D) as2) ->
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
      (forall ns m m', ind_rel p D ups nr ar dr ns m m' -> forall ns', tele_full nr T ns ns' ->
         exists r r', eval_elim gc_deps gc_stack ρa nm Aa Bsa m r /\ eval_elim gc_deps gc_stack ρb nm Ab Bsb m' r' /\
           Rel ns m ns' m' r r') /\
      (forall pre gs vs vs', ind_args_rel p D ups nr ar dr pre gs vs vs' ->
         exists ihs ihs', eval_ihs gc_deps gc_stack ρa nm Aa Bsa gs vs ihs /\ eval_ihs gc_deps gc_stack ρb nm Ab Bsb gs vs' ihs' /\
           ihs_rel pre gs vs vs' ihs ihs') /\
      (forall pre t v v', ind_shape_rel p D ups nr ar dr pre t v v' ->
         exists ih ih', eval_ih gc_deps gc_stack ρa nm Aa Bsa t v ih /\ eval_ih gc_deps gc_stack ρb nm Ab Bsb t v' ih' /\
           ih_rel pre t v v' ih ih') /\
      (forall pre t f c f' c', ind_app_rel p D ups nr ar dr pre t f c f' c' ->
         exists fc fc' r r', $| f & c | gc_deps ⍮ gc_stack ↘ fc /\ $| f' & c' | gc_deps ⍮ gc_stack ↘ fc' /\
           eval_ih gc_deps gc_stack ρa nm Aa Bsa t fc r /\ eval_ih gc_deps gc_stack ρb nm Ab Bsb t fc' r' /\
           ih_rel pre t fc fc' r r').
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
        assert (Hm : ind_rel p D ups nr ar dr ns (d_con p c (bs ++ vs)) (d_con p c (bs' ++ vs'))) by (econstructor; eassumption).
        exists r, r'; split; [| split ].
        + eapply eval_elim_con; [ exact Hl | exact Hc | rewrite List.length_app; lia | exact HBa | exact Hn | |].
          * rewrite skipn_app_exact by exact Hb; exact Ei.
          * rewrite firstn_app_exact, skipn_app_exact by exact Hb; exact Er.
        + eapply eval_elim_con; [ exact Hl | exact Hc | rewrite List.length_app; lia | exact HBb | exact Hn | |].
          * rewrite skipn_app_exact by exact Hb'; exact Ei'.
          * rewrite firstn_app_exact, skipn_app_exact by exact Hb'; exact Er'.
        + apply (Rel_right _ _ _ _ _ _ Hns Hns' Hm Hm); exact Hrr.
      - intros as1 as2 ns e e' Hl1 Hl2 Ha1 Ha2 Hs1 Hs2 He ns' Hns'.
        assert (Hm : ind_rel p D ups nr ar dr ns (⇑ (d_ind p as1) e) (⇑ (d_ind p as2) e')) by (econstructor; eassumption).
        assert (H12 : tele_full nr T (List.skipn (ind_nu D) as1) (List.skipn (ind_nu D) as2)) by exact (ttrans _ _ _ (tsym _ _ Hs1) Hs2).
        pose proof (ind_rel_mv _ _ _ _ Hm Hs1) as Hm1.
        destruct (Hmot _ _ _ _ H12 Hm1) as (a1 & a2 & Ea1 & Ea2 & HR).
        exists (⇑ a1 (d_elim ρa nm Aa Bsa p as1 e)), (⇑ a2 (d_elim ρb nm Ab Bsb p as2 e')).
        split; [ eapply eval_elim_neut; eassumption | split; [ eapply eval_elim_neut; eassumption |] ].
        pose proof (per_bot_then_per_elem HR (per_bot_elim _ _ _ _ _ Hl1 Hl2 Ha1 Ha2 Hs1 Hs2 He)) as Hrr.
        apply (Rel_right _ _ _ _ _ _ Hs2 Hns' Hm Hm).
        apply (Rel_left _ _ _ _ _ _ H12 Hs2 Hm1 Hm); exact Hrr.
      - intros pre; exists nil, nil; split; [ constructor | split; [ constructor | constructor ] ].
      - intros * Hia (ihs & ihs' & Ei & Ei' & Hir).
        exists ihs, ihs'; split; [ constructor; exact Ei | split; [ constructor; exact Ei' | constructor; exact Hir ] ].
      - intros * Hsh (ih & ih' & Eh & Eh' & Hhh) Hia (ihs & ihs' & Ei & Ei' & Hir).
        exists (ih :: ihs), (ih' :: ihs'); split; [ econstructor; eassumption | split; [ econstructor; eassumption |] ].
        econstructor; eassumption.
      - intros * Hb Hr IHr.
        destruct (IHr _ (ind_rel_ns_refl _ _ _ Hr)) as (ih & ih' & Eh & Eh' & Hhh).
        exists ih, ih'; split; [ constructor; exact Eh | split; [ constructor; exact Eh' |] ].
        cbn [ih_rel]; eexists; split; eassumption.
      - intros pre B t f f' Hf IH.
        exists (d_ihfn ρa nm Aa Bsa t f), (d_ihfn ρb nm Ab Bsb t f').
        split; [ constructor | split; [ constructor |] ].
        cbn [ih_rel]; intros c c' Hcc.
        destruct (IH c c' Hcc) as (fc & fc' & r & r' & Ef & Ef' & Er & Er' & Hrr).
        exists fc, fc', r, r'; split; [ exact Ef | split; [ exact Ef' | split; [| split; [| exact Hrr ] ] ] ];
          econstructor; eassumption.
      - intros f c r f' c' r' pre t Ef Ef' Hsh (ih & ih' & Eh & Eh' & Hhh).
        exists r, r', ih, ih'; repeat split; assumption.
    Qed.
  End IndElim.
End Fixed_GCtx.
