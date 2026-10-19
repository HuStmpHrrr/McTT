(** * The Eliminator in the PER Model

    The eliminator of an inductive type relates related elements at a family
    of relations [Rel], given that its motives are related at [Rel] at
    related arguments ([Hmot]) and its branches are related at related
    arguments and recursive results ([Hbr]).  This is the semantic content
    of the eliminator's rule; the cases of the fundamental theorem
    instantiate it at the links of their four-value patterns.

    The elements are related at their own parameters ([ind_rel]); so are
    the recursive results ([rec_result_rel]) and the branches ([Hbr]), each side at
    its own.  The uniform parameters of the elements are admissible ([adm]),
    which the eliminator's base [ups] makes concrete ([HOk]).

    A stuck eliminator reads back its motive and branches under fresh
    variables of the types its scrutinee's uniform parameters give.  These
    parameters are admissible, so the variables of the two sides are
    related, and so are the motives and branches there ([per_bot_elim]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
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

  Lemma functional_fresh_tele : forall ρ T s vs vs', Ftele T in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ vs ->
      Ftele T in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ vs' -> vs = vs'.
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
    Variable (nparams_rel : nat -> list domain -> relation domain).
    Variable (args_rel : list domain -> String.string -> nat -> list domain -> relation domain).
    Variable (doms_rel : list domain -> exp -> relation domain).
    Let T := List.rev (ind_nparams D).
    Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D).
    Hypothesis (Hass : tele_ass (ind_params D)).
    Hypothesis (HnP : forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_prefix_rel nparams_rel k vs vs' -> PER (nparams_rel k vs)).
    Hypothesis (HnI : forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_prefix_rel nparams_rel k vs vs' -> (nparams_rel k vs <~> nparams_rel k vs')).
    Hypothesis (HaP : forall ms ms' c gs k A vs vs', tele_rel nparams_rel T ms ms' -> ind_con D c = Some gs ->
                      List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (args_rel ms c) k vs vs' -> PER (args_rel ms c k vs)).
    Hypothesis (HaI : forall ms ms' c gs k A vs vs', tele_rel nparams_rel T ms ms' -> ind_con D c = Some gs ->
                      List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (args_rel ms c) k vs vs' ->
                      (args_rel ms c k vs <~> args_rel ms' c k vs')).
    Hypothesis (HdP : forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_rel nparams_rel T ms ms' ->
                      ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                      tele_prefix_rel (args_rel ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
                      List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel doms_rel ms ws (ptyp_doms t)) k ys ys' ->
                      PER (doms_rel (ms ++ ws ++ ys) B)).
    Hypothesis (HdI : forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_rel nparams_rel T ms ms' ->
                      ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                      tele_prefix_rel (args_rel ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
                      List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel doms_rel ms ws (ptyp_doms t)) k ys ys' ->
                      (doms_rel (ms ++ ws ++ ys) B <~> doms_rel (ms' ++ ws' ++ ys') B)).
    (** The admissible uniform parameters, admissible beside [ups]. *)
    Variable (adm : list domain -> Prop).
    Hypothesis (HOk : forall u, adm u -> adm_uparams D ups nparams_rel args_rel doms_rel u).
    Hypothesis (Hle : ind_nu D <= ind_np D).
    Hypothesis (Hsimple : forall c gs gs1 t gs2, ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 -> ptyp_simple t = true).
    Hypothesis (Hplen : forall c gs gs1 t gs2, ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                  List.length (ptyp_ps t) = ind_nn D).

    Let tsym := nparams_rel_sym p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI.
    Let ttrans := nparams_rel_trans p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI.
    Let trefl := nparams_rel_refl_l p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI.
    Let trefl_r := nparams_rel_refl_r p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI.
    Let tprl := args_rel_pre_refl_l p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI.
    Let idx := ind_rel_idx p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI adm.

    Lemma length_tnr : forall a b, tele_rel nparams_rel T a b -> List.length a = ind_nn D /\ List.length b = ind_nn D.
    Proof. intros * H; rewrite tele_rel_iff in H; destruct H as (H1 & H2 & _); unfold T in *; rewrite List.length_rev, length_nparams in *; lia. Qed.

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
    (** The motives, at the two sides' indices of related elements. *)
    Hypothesis (Hmot : forall ns ns' m m', ind_rel p D adm nparams_rel args_rel doms_rel ns ns' m m' ->
                   exists a a', ⟦ Aa ⟧ env_args ρa (ns ++ m :: nil) ↘ a /\ ⟦ Ab ⟧ env_args ρb (ns' ++ m' :: nil) ↘ a' /\
                     DF a ≈ a' ∈ per_univ_elem i ↘ (Rel ns m ns' m')).

    (** The recursive results of recursive arguments [v] and [v'] of shape
        [t], after the values [pre] and [pre'] of the shape's components on
        each side, the uniform parameters [u] and [u'] apart: at the end,
        related at [Rel] at the parameters the shape evaluates to on each
        side, and at a domain, pointwise. *)
    Fixpoint rec_result_rel (u u' pre pre' : list domain) (t : ptyp) (v v' ih ih' : domain) : Prop :=
      match t with
      | pt_self _ Ps => rel_evals Ps (env_args nil (u ++ pre)) (env_args nil (u' ++ pre')) (fun bs bs' => Rel bs v bs' v' ih ih')
      | pt_aux _ _ => False
      | pt_pi B t => forall c c', doms_rel pre B c c' ->
          exists fc fc' r r', $| v & c | gc_deps ⍮ gc_stack ↘ fc /\ $| v' & c' | gc_deps ⍮ gc_stack ↘ fc' /\
            $| ih & c | gc_deps ⍮ gc_stack ↘ r /\ $| ih' & c' | gc_deps ⍮ gc_stack ↘ r' /\
            rec_result_rel u u' (pre ++ c :: nil) (pre' ++ c' :: nil) t fc fc' r r'
      end.

    (** The recursive results of related arguments, after the values [pre]
        and [pre'] of the non-uniform parameters and the non-recursive
        arguments before them on each side. *)
    Inductive rec_results_rel (u u' : list domain)
      : list domain -> list domain -> list carg -> list domain -> list domain -> list domain -> list domain -> Prop :=
    | rec_results_rel_nil : forall pre pre', rec_results_rel u u' pre pre' nil nil nil nil nil
    | rec_results_rel_arg : forall pre pre' A gs v v' vs vs' ihs ihs',
        rec_results_rel u u' (pre ++ v :: nil) (pre' ++ v' :: nil) gs vs vs' ihs ihs' ->
        rec_results_rel u u' pre pre' (ca_arg A :: gs) (v :: vs) (v' :: vs') ihs ihs'
    | rec_results_rel_rec : forall pre pre' t gs v v' vs vs' ih ih' ihs ihs',
        rec_result_rel u u' pre pre' t v v' ih ih' ->
        rec_results_rel u u' pre pre' gs vs vs' ihs ihs' ->
        rec_results_rel u u' pre pre' (ca_rec t :: gs) (v :: vs) (v' :: vs') (ih :: ihs) (ih' :: ihs').

    (** The branches, at two constructors related at their own parameters
        [bs] and [bs'], and at related recursive results. *)
    Hypothesis (Hbr : forall c gs n Ba Bb, ind_con D c = Some gs ->
                   brs_lookup Bsa c = Some (n, Ba) -> brs_lookup Bsb c = Some (n, Bb) ->
                   forall bs bs' vs vs' ihs ihs',
                     List.length bs = ind_np D -> List.length bs' = ind_np D ->
                     adm (List.firstn (ind_nu D) bs) -> adm (List.firstn (ind_nu D) bs') ->
                     tele_rel nparams_rel T (List.skipn (ind_nu D) bs) (List.skipn (ind_nu D) bs') ->
                     tele_rel (args_rel (List.skipn (ind_nu D) bs) c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') ->
                     con_args_rel p D adm nparams_rel args_rel doms_rel (List.firstn (ind_nu D) bs) (List.firstn (ind_nu D) bs')
                       (List.skipn (ind_nu D) bs) (List.skipn (ind_nu D) bs') gs vs vs' ->
                     rec_results_rel (List.firstn (ind_nu D) bs) (List.firstn (ind_nu D) bs')
                       (List.skipn (ind_nu D) bs) (List.skipn (ind_nu D) bs') gs vs vs' ihs ihs' ->
                     exists r r', ⟦ Ba ⟧ env_args ρa (List.skipn (ind_nu D) bs ++ vs ++ ihs) ↘ r /\
                       ⟦ Bb ⟧ env_args ρb (List.skipn (ind_nu D) bs' ++ vs' ++ ihs') ↘ r' /\
                       Rel (List.skipn (ind_nu D) bs) (d_con p c (bs ++ vs)) (List.skipn (ind_nu D) bs') (d_con p c (bs' ++ vs')) r r').

    (** ** The Family Is Invariant *)

    Lemma motive_rel_right : forall ns m ns1 m1 ns2 m2,
        ind_rel p D adm nparams_rel args_rel doms_rel ns ns1 m m1 -> ind_rel p D adm nparams_rel args_rel doms_rel ns ns2 m m2 -> (Rel ns m ns1 m1 <~> Rel ns m ns2 m2).
    Proof.
      intros * Hm1 Hm2.
      destruct (Hmot _ _ _ _ Hm1) as (a & a1 & Ea & Ea1 & HR1).
      destruct (Hmot _ _ _ _ Hm2) as (b & a2 & Eb & Ea2 & HR2).
      assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
      eapply per_univ_elem_right_irrel; eassumption.
    Qed.

    Lemma motive_rel_left : forall ns1 m1 ns2 m2 ns' m',
        ind_rel p D adm nparams_rel args_rel doms_rel ns1 ns' m1 m' -> ind_rel p D adm nparams_rel args_rel doms_rel ns2 ns' m2 m' -> (Rel ns1 m1 ns' m' <~> Rel ns2 m2 ns' m').
    Proof.
      intros * Hm1 Hm2.
      destruct (Hmot _ _ _ _ Hm1) as (a1 & a & Ea1 & Ea & HR1).
      destruct (Hmot _ _ _ _ Hm2) as (a2 & b & Ea2 & Eb & HR2).
      assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
      eapply per_univ_elem_left_irrel; eassumption.
    Qed.

    (** The family at related elements does not depend on the indices. *)
    Lemma motive_rel_move : forall ns ns' m m' ns1 ns1', ind_rel p D adm nparams_rel args_rel doms_rel ns ns' m m' ->
        tele_rel nparams_rel T ns ns1 -> tele_rel nparams_rel T ns' ns1' -> (Rel ns m ns' m' <~> Rel ns1 m ns1' m').
    Proof.
      intros * Hm H1 H1'.
      pose proof (idx _ _ _ _ _ _ Hm (trefl _ _ H1) H1') as Hmid.
      pose proof (idx _ _ _ _ _ _ Hm H1 H1') as Hm1.
      etransitivity; [ exact (motive_rel_right _ _ _ _ _ _ Hm Hmid) | exact (motive_rel_left _ _ _ _ _ _ Hmid Hm1) ].
    Qed.

    Lemma con_args_rel_length : forall u u' pre pre' gs vs vs', con_args_rel p D adm nparams_rel args_rel doms_rel u u' pre pre' gs vs vs' ->
        List.length vs = List.length gs /\ List.length vs' = List.length gs.
    Proof. induction 1; cbn; [ split; reflexivity | destruct IHcon_args_rel; split; congruence | destruct IHcon_args_rel; split; congruence ]. Qed.

    (** ** Fresh Variables

        The variables a stuck eliminator's readback makes at admissible
        uniform parameters: those of two such are related, through those at
        [ups]. *)
    Lemma fresh_nparams : forall ua, adm_uparams D ups nparams_rel args_rel doms_rel ua -> forall T' T0 vs vs' s, T = T0 ++ T' ->
        tele_prefix_rel nparams_rel (List.length T0) vs vs' ->
        exists ws ws', Ftele T' in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ vs) ⍮ s ↘ ws /\
          Ftele T' in gc_deps ⍮ gc_stack ⍮ env_args nil (ua ++ vs') ⍮ s ↘ ws' /\
          tele_prefix_rel nparams_rel (List.length T) (vs ++ ws) (vs' ++ ws').
    Proof.
      intros ua [Hn _ _ _]; induction T' as [| e T' IH]; intros T0 vs vs' s HT Hp.
      - exists nil, nil; rewrite !List.app_nil_r; rewrite HT, List.app_nil_r.
        split; [ constructor | split; [ constructor | exact Hp ] ].
      - assert (Hk : List.nth_error T (List.length T0) = Some e)
          by (rewrite HT, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
        assert (HA : exists A, List.nth_error T (List.length T0) = Some (ce_ass A)).
        { apply (nparams_lt_ass D); [ exact Hass |]. apply List.nth_error_Some; unfold T in Hk; congruence. }
        destruct HA as [A HA]; rewrite Hk in HA; injection HA as ->.
        destruct (Hn _ _ _ _ s Hk Hp) as [a a' Ea Ea' Hr].
        destruct (IH (T0 ++ ce_ass A :: nil) (vs ++ ⇑! a s :: nil) (vs' ++ ⇑! a' s :: nil) (S s)) as (ws & ws' & F & F' & Hp').
        { rewrite HT, <- List.app_assoc; reflexivity. }
        { rewrite List.length_app, Nat.add_comm; cbn; apply tele_prefix_rel_snoc; assumption. }
        exists (⇑! a s :: ws), (⇑! a' s :: ws'); split; [| split ].
        + econstructor; [ exact Ea |]; rewrite <- env_args_snoc, <- List.app_assoc; exact F.
        + econstructor; [ exact Ea' |]; rewrite <- env_args_snoc, <- List.app_assoc; exact F'.
        + rewrite <- !List.app_assoc in Hp'; exact Hp'.
    Qed.

    Lemma fresh_nparams_pair : forall ua1 ua2 s, adm_uparams D ups nparams_rel args_rel doms_rel ua1 -> adm_uparams D ups nparams_rel args_rel doms_rel ua2 ->
        exists ns1 ns2, Ftele T in gc_deps ⍮ gc_stack ⍮ env_args nil ua1 ⍮ s ↘ ns1 /\
          Ftele T in gc_deps ⍮ gc_stack ⍮ env_args nil ua2 ⍮ s ↘ ns2 /\ tele_rel nparams_rel T ns1 ns2.
    Proof.
      intros * H1 H2.
      destruct (fresh_nparams _ H1 T nil nil nil s eq_refl (tele_prefix_rel_nil _)) as (w0 & w1 & F0 & F1 & P1).
      destruct (fresh_nparams _ H2 T nil nil nil s eq_refl (tele_prefix_rel_nil _)) as (w0' & w2 & F0' & F2 & P2).
      pose proof (functional_fresh_tele _ _ _ _ _ F0 F0') as <-.
      rewrite List.app_nil_r in F1, F2; cbn in P1, P2.
      exists w1, w2; split; [ exact F1 | split; [ exact F2 |] ].
      apply tele_rel_of_pre in P1, P2.
      exact (ttrans _ _ _ (tsym _ _ P1) P2).
    Qed.

    (** Neutrals at admissible bases and at parameters related to the two
        indices. *)
    Lemma ind_rel_neut_at : forall ns ns' ua1 ua2 bs1 bs2 m m', adm ua1 -> adm ua2 ->
        List.length ua1 = ind_nu D -> List.length ua2 = ind_nu D ->
        tele_rel nparams_rel T ns ns' -> tele_rel nparams_rel T ns bs1 -> tele_rel nparams_rel T ns' bs2 -> Dom m ≈ m' ∈ per_bot ->
        ind_rel p D adm nparams_rel args_rel doms_rel ns ns' (⇑ (d_ind p (ua1 ++ bs1)) m) (⇑ (d_ind p (ua2 ++ bs2)) m').
    Proof.
      intros * H1 H2 L1 L2 Hn B1 B2 Hm.
      destruct (length_tnr _ _ B1) as [_ L1']; destruct (length_tnr _ _ B2) as [_ L2'].
      assert (Hnp : ind_nn D = ind_np D - ind_nu D) by reflexivity.
      apply ind_rel_neut.
      - exact Hn.
      - rewrite List.length_app; lia.
      - rewrite List.length_app; lia.
      - rewrite firstn_app_exact by exact L1; exact H1.
      - rewrite firstn_app_exact by exact L2; exact H2.
      - rewrite skipn_app_exact by exact L1; exact B1.
      - rewrite skipn_app_exact by exact L2; exact B2.
      - exact Hm.
    Qed.

    Lemma ind_rel_var : forall ns ns' ua1 ua2 bs1 bs2 k, adm ua1 -> adm ua2 ->
        List.length ua1 = ind_nu D -> List.length ua2 = ind_nu D ->
        tele_rel nparams_rel T ns ns' -> tele_rel nparams_rel T ns bs1 -> tele_rel nparams_rel T ns' bs2 ->
        ind_rel p D adm nparams_rel args_rel doms_rel ns ns' (⇑! (d_ind p (ua1 ++ bs1)) k) (⇑! (d_ind p (ua2 ++ bs2)) k).
    Proof. intros; apply ind_rel_neut_at; try assumption; apply var_per_bot. Qed.

    Lemma per_bot_app : forall m m' n n', Dom m ≈ m' ∈ per_bot -> Dom n ≈ n' ∈ per_top -> Dom m $ᵈ n ≈ m' $ᵈ n' ∈ per_bot.
    Proof.
      intros * Hm Hn s; destruct (Hm s) as (M & HM & HM'); destruct (Hn s) as (N & HN & HN').
      exists (M $ⁿ N); split; constructor; assumption.
    Qed.

    (** The type of an argument of a simple shape is defined at an admissible
        base, after related domains. *)
    Lemma shape_type_exists : forall ua, adm_uparams D ups nparams_rel args_rel doms_rel ua ->
        forall ns1 ns2 c gs1 t0 gs2 ws1 ws2, tele_rel nparams_rel T ns1 ns2 -> ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
        tele_prefix_rel (args_rel ns1 c) (List.length (cargs_nonrec gs1)) ws1 ws2 ->
        forall k ys1 ys2, k <= List.length (ptyp_doms t0) -> tele_prefix_rel (shape_doms_rel doms_rel ns1 ws1 (ptyp_doms t0)) k ys1 ys2 ->
          exists a, ⟦shty ptyp_skip k t0 of p ua ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ua ++ ns2 ++ ws2 ++ ys2) ↘ a.
    Proof.
      intros ua [_ _ Hcl Hdt] * H12 Hc Hw k ys1 ys2 Hk Hy.
      pose proof (Hsimple _ _ _ _ _ Hc eq_refl) as Hs0.
      destruct (Nat.eq_dec k (List.length (ptyp_doms t0))) as [-> | Hne].
      - rewrite (ptyp_skip_end _ Hs0).
        assert (Hyf : tele_rel (shape_doms_rel doms_rel ns1 ws1 (ptyp_doms t0)) (ptyp_doms t0) ys1 ys2)
          by (destruct Hy as [Hyl Hya]; split; [ exact Hyl | exact Hya ]).
        destruct (Hcl _ _ _ _ _ _ _ _ _ _ _ H12 Hc eq_refl Hw Hyf) as [bs bs' _ E' _].
        eexists; econstructor; exact E'.
      - destruct (ptyp_skip_lt k t0 ltac:(lia)) as (B & HB & Hs); rewrite Hs.
        destruct (Hdt _ _ _ _ _ _ _ _ _ _ _ _ _ H12 Hc eq_refl Hw HB Hy) as [b b' _ Eb' _].
        eexists; econstructor; exact Eb'.
    Qed.

    (** A neutral of the type of an argument of a shape at two admissible
        bases, after related domains, is related by the shape, each side at
        its own base: the two bases are admissible beside each other
        ([adm_base]), so the parameters at the end of the shape are related,
        with no detour through [ups]. *)
    Lemma shape_neut : forall ua1 ua2, adm ua1 -> adm ua2 ->
        List.length ua1 = ind_nu D -> List.length ua2 = ind_nu D ->
        forall ns1 ns2 c gs1 t0 gs2 ws1 ws2, tele_rel nparams_rel T ns1 ns2 -> ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
        tele_prefix_rel (args_rel ns1 c) (List.length (cargs_nonrec gs1)) ws1 ws2 ->
        forall n k ys1 ys2 a1 a2 m m', k + n = List.length (ptyp_doms t0) ->
          tele_prefix_rel (shape_doms_rel doms_rel ns1 ws1 (ptyp_doms t0)) k ys1 ys2 ->
          ⟦shty ptyp_skip k t0 of p ua1 ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ua1 ++ ns1 ++ ws1 ++ ys1) ↘ a1 ->
          ⟦shty ptyp_skip k t0 of p ua2 ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ua2 ++ ns2 ++ ws2 ++ ys2) ↘ a2 ->
          Dom m ≈ m' ∈ per_bot ->
          rec_arg_rel p D adm nparams_rel args_rel doms_rel ua1 ua2 (ns1 ++ ws1 ++ ys1) (ns2 ++ ws2 ++ ys2) (ptyp_skip k t0) (⇑ a1 m) (⇑ a2 m').
    Proof.
      intros ua1 ua2 Ha1 Ha2 L1 L2 ns1 ns2 c gs1 t0 gs2 ws1 ws2 H12 Hc Hw.
      pose proof (trefl _ _ H12) as H11.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
        by (rewrite cargs_nonrec_app, List.length_app; lia).
      pose proof (tprl _ _ _ H11 Hc _ _ _ HK Hw) as Hww.
      pose proof (adm_base p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI _ _ (HOk _ Ha1) (HOk _ Ha2)) as Had12.
      pose proof (adm_rec_params _ _ _ _ _ _ Had12) as Hcl12.
      pose proof (adm_shape_doms _ _ _ _ _ _ Had12) as Hd12.
      induction n as [| n IH]; intros k ys1 ys2 a1 a2 m m' Hkn Hy E1 E2 Hm.
      - destruct (ptyp_skip k t0) as [j Ps | j Ps | B t] eqn:Hs.
        + (** The end of the shape: the neutral's own parameters are the
              ones the shape evaluates to, literally. *)
          destruct (ptyp_skip_self _ _ _ _ Hs) as [Hkd HPs].
          inversion E1; subst a1.
          match goal with H : ⟦ _ ⟧* _ ⍮ _ ⍮ env_args nil (ua1 ++ _) ↘ ?b |- _ => rename H into Ebs1; rename b into bs1 end.
          inversion E2; subst a2.
          match goal with H : ⟦ _ ⟧* _ ⍮ _ ⍮ env_args nil (ua2 ++ _) ↘ ?b |- _ => rename H into Ebs2; rename b into bs2 end.
          assert (Hyf : tele_rel (shape_doms_rel doms_rel ns1 ws1 (ptyp_doms t0)) (ptyp_doms t0) ys1 ys2)
            by (destruct Hy as [Hyl Hya]; split; [ lia | exact Hya ]).
          destruct (Hcl12 _ _ _ _ _ _ _ _ _ _ _ H12 Hc eq_refl Hw Hyf) as [b1 b2 F1 F2 R12].
          rewrite HPs in F1, F2.
          pose proof (functional_eval_exps' _ _ _ _ F1 Ebs1) as <-.
          pose proof (functional_eval_exps' _ _ _ _ F2 Ebs2) as <-.
          econstructor; [ exact F1 | exact F2 |].
          exact (ind_rel_neut_at _ _ _ _ _ _ _ _ Ha1 Ha2 L1 L2 R12 (trefl _ _ R12) (trefl_r _ _ R12) Hm).
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
          destruct (Hd12 _ _ _ _ _ _ _ _ _ _ _ _ _ H12 Hc eq_refl Hw HB Hy) as [b1' b2' Eb1' Eb2' Htop].
          assert (b1' = b1) as -> by (eapply functional_eval_exp; eassumption).
          assert (b2' = b2) as -> by (eapply functional_eval_exp; eassumption).
          pose proof (doms_rel_refl_l p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI ns1 c _ gs1 t0 gs2 ws1 H11 Hc eq_refl Hww k ys1 ys2
                        ltac:(lia) Hy) as Hyy.
          pose proof (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ H11 Hc eq_refl Hww HB Hyy) as HPd.
          constructor; intros c0 c0' Hcc.
          assert (Hcc0 : doms_rel (ns1 ++ ws1 ++ ys1) B c0 c0) by (etransitivity; [ exact Hcc | symmetry; exact Hcc ]).
          assert (Hy' : tele_prefix_rel (shape_doms_rel doms_rel ns1 ws1 (ptyp_doms t0)) (S k) (ys1 ++ c0 :: nil) (ys2 ++ c0' :: nil))
            by (apply tele_prefix_rel_snoc; [ exact Hy | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hcc ]).
          assert (Hyy' : tele_prefix_rel (shape_doms_rel doms_rel ns1 ws1 (ptyp_doms t0)) (S k) (ys1 ++ c0 :: nil) (ys1 ++ c0 :: nil))
            by (apply tele_prefix_rel_snoc; [ exact Hyy | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hcc0 ]).
          destruct (shape_type_exists _ (HOk _ Ha1) _ _ _ _ _ _ _ _ H11 Hc Hww (S k) _ _ ltac:(lia) Hyy') as [a1' Ea1'].
          destruct (shape_type_exists _ (HOk _ Ha2) _ _ _ _ _ _ _ _ H12 Hc Hw (S k) _ _ ltac:(lia) Hy') as [a2' Ea2'].
          rewrite Hs' in Ea1', Ea2'.
          econstructor; [ eapply eval_app_neut, eval_fam_cod_shfam; rewrite <- env_args_snoc3; exact Ea1'
                        | eapply eval_app_neut, eval_fam_cod_shfam; rewrite <- env_args_snoc3; exact Ea2' |].
          replace ((ns1 ++ ws1 ++ ys1) ++ c0 :: nil) with (ns1 ++ ws1 ++ (ys1 ++ c0 :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
          replace ((ns2 ++ ws2 ++ ys2) ++ c0' :: nil) with (ns2 ++ ws2 ++ (ys2 ++ c0' :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
          rewrite <- Hs'.
          apply (IH (S k) _ _ _ _ _ _ ltac:(lia) Hy'); [ rewrite Hs'; exact Ea1' | rewrite Hs'; exact Ea2' |].
          apply per_bot_app; [ exact Hm | exact (Htop _ _ Hcc) ].
    Qed.

    (** A neutral of the type of the recursive result of such a neutral is
        related to the other's. *)
    Lemma ih_neut : forall ua1 ua2, adm ua1 -> adm ua2 ->
        List.length ua1 = ind_nu D -> List.length ua2 = ind_nu D ->
        forall ns1 ns2 c gs1 t0 gs2 ws1 ws2, tele_rel nparams_rel T ns1 ns2 -> ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
        tele_prefix_rel (args_rel ns1 c) (List.length (cargs_nonrec gs1)) ws1 ws2 ->
        forall n k ys1 ys2 a1 a2 m m' e e', k + n = List.length (ptyp_doms t0) ->
          tele_prefix_rel (shape_doms_rel doms_rel ns1 ws1 (ptyp_doms t0)) k ys1 ys2 ->
          ⟦shty ptyp_skip k t0 of p ua1 ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ua1 ++ ns1 ++ ws1 ++ ys1) ↘ a1 ->
          ⟦shty ptyp_skip k t0 of p ua2 ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ua2 ++ ns2 ++ ws2 ++ ys2) ↘ a2 ->
          Dom m ≈ m' ∈ per_bot -> Dom e ≈ e' ∈ per_bot ->
          exists h1 h2, ⟦ihty ⇑ a1 m of ptyp_skip k t0 under ρa Aa ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ua1 ++ ns1 ++ ws1 ++ ys1) ↘ h1 /\
            ⟦ihty ⇑ a2 m' of ptyp_skip k t0 under ρb Ab ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ua2 ++ ns2 ++ ws2 ++ ys2) ↘ h2 /\
            rec_result_rel ua1 ua2 (ns1 ++ ws1 ++ ys1) (ns2 ++ ws2 ++ ys2) (ptyp_skip k t0) (⇑ a1 m) (⇑ a2 m') (⇑ h1 e) (⇑ h2 e').
    Proof.
      intros ua1 ua2 Ha1 Ha2 L1 L2 ns1 ns2 c gs1 t0 gs2 ws1 ws2 H12 Hc Hw.
      pose proof (trefl _ _ H12) as H11.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
        by (rewrite cargs_nonrec_app, List.length_app; lia).
      pose proof (tprl _ _ _ H11 Hc _ _ _ HK Hw) as Hww.
      pose proof (adm_base p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI _ _ (HOk _ Ha1) (HOk _ Ha2)) as Had12.
      pose proof (adm_rec_params _ _ _ _ _ _ Had12) as Hcl12.
      pose proof (adm_shape_doms _ _ _ _ _ _ Had12) as Hd12.
      induction n as [| n IH]; intros k ys1 ys2 a1 a2 m m' e e' Hkn Hy E1 E2 Hm He.
      - destruct (ptyp_skip k t0) as [j Ps | j Ps | B t] eqn:Hs.
        + destruct (ptyp_skip_self _ _ _ _ Hs) as [Hkd HPs].
          inversion E1; subst a1.
          match goal with H : ⟦ _ ⟧* _ ⍮ _ ⍮ env_args nil (ua1 ++ _) ↘ ?b |- _ => rename H into Ebs1; rename b into bs1 end.
          inversion E2; subst a2.
          match goal with H : ⟦ _ ⟧* _ ⍮ _ ⍮ env_args nil (ua2 ++ _) ↘ ?b |- _ => rename H into Ebs2; rename b into bs2 end.
          assert (Hyf : tele_rel (shape_doms_rel doms_rel ns1 ws1 (ptyp_doms t0)) (ptyp_doms t0) ys1 ys2)
            by (destruct Hy as [Hyl Hya]; split; [ lia | exact Hya ]).
          destruct (Hcl12 _ _ _ _ _ _ _ _ _ _ _ H12 Hc eq_refl Hw Hyf) as [b1 b2 F1 F2 R12].
          rewrite HPs in F1, F2.
          pose proof (functional_eval_exps' _ _ _ _ F1 Ebs1) as <-.
          pose proof (functional_eval_exps' _ _ _ _ F2 Ebs2) as <-.
          pose proof (ind_rel_neut_at _ _ _ _ _ _ _ _ Ha1 Ha2 L1 L2 R12 (trefl _ _ R12) (trefl_r _ _ R12) Hm) as Hv.
          destruct (Hmot _ _ _ _ Hv) as (h1 & h2 & T1 & T2 & HR).
          exists h1, h2; split; [ econstructor; eassumption | split; [ econstructor; eassumption |] ].
          cbn [rec_result_rel]; exists b1 b2; [ exact F1 | exact F2 | exact (per_bot_then_per_elem HR He) ].
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
          destruct (Hd12 _ _ _ _ _ _ _ _ _ _ _ _ _ H12 Hc eq_refl Hw HB Hy) as [b1' b2' Eb1' Eb2' Htop].
          assert (b1' = b1) as -> by (eapply functional_eval_exp; eassumption).
          assert (b2' = b2) as -> by (eapply functional_eval_exp; eassumption).
          pose proof (doms_rel_refl_l p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI ns1 c _ gs1 t0 gs2 ws1 H11 Hc eq_refl Hww k ys1 ys2
                        ltac:(lia) Hy) as Hyy.
          exists (Πᵈ b1 (nil ↦ d_ihfam ρa Aa (env_args nil (ua1 ++ ns1 ++ ws1 ++ ys1)) t (⇑ (Πᵈ b1 (nil ↦ d_shfam p ua1 (env_args nil (ua1 ++ ns1 ++ ws1 ++ ys1)) t) fam_cod) m)) fam_cod),
            (Πᵈ b2 (nil ↦ d_ihfam ρb Ab (env_args nil (ua2 ++ ns2 ++ ws2 ++ ys2)) t (⇑ (Πᵈ b2 (nil ↦ d_shfam p ua2 (env_args nil (ua2 ++ ns2 ++ ws2 ++ ys2)) t) fam_cod) m')) fam_cod).
          split; [ econstructor; exact Eb1 | split; [ econstructor; exact Eb2 |] ].
          cbn [rec_result_rel]; intros c0 c0' Hcc.
          assert (Hcc0 : doms_rel (ns1 ++ ws1 ++ ys1) B c0 c0)
            by (pose proof (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ H11 Hc eq_refl Hww HB Hyy) as HPd;
                etransitivity; [ exact Hcc | symmetry; exact Hcc ]).
          assert (Hy' : tele_prefix_rel (shape_doms_rel doms_rel ns1 ws1 (ptyp_doms t0)) (S k) (ys1 ++ c0 :: nil) (ys2 ++ c0' :: nil))
            by (apply tele_prefix_rel_snoc; [ exact Hy | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hcc ]).
          assert (Hyy' : tele_prefix_rel (shape_doms_rel doms_rel ns1 ws1 (ptyp_doms t0)) (S k) (ys1 ++ c0 :: nil) (ys1 ++ c0 :: nil))
            by (apply tele_prefix_rel_snoc; [ exact Hyy | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hcc0 ]).
          destruct (shape_type_exists _ (HOk _ Ha1) _ _ _ _ _ _ _ _ H11 Hc Hww (S k) _ _ ltac:(lia) Hyy') as [a1' Ea1'].
          destruct (shape_type_exists _ (HOk _ Ha2) _ _ _ _ _ _ _ _ H12 Hc Hw (S k) _ _ ltac:(lia) Hy') as [a2' Ea2'].
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
            replace ((ns2 ++ ws2 ++ ys2) ++ c0' :: nil) with (ns2 ++ ws2 ++ (ys2 ++ c0' :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
            exact Hih.
    Qed.

    Lemma fresh_args : forall ua1 ua2 ns1 ns2 c gs, adm ua1 -> adm ua2 ->
        List.length ua1 = ind_nu D -> List.length ua2 = ind_nu D ->
        tele_rel nparams_rel T ns1 ns2 -> ind_con D c = Some gs ->
        forall gs' gs1 ws1 ws2 s s2, gs = gs1 ++ gs' ->
        tele_prefix_rel (args_rel ns1 c) (List.length (cargs_nonrec gs1)) ws1 ws2 ->
        exists vs1 vs2 ihs1 ihs2,
          Fcargs gs' of p ua1 in gc_deps ⍮ gc_stack ⍮ env_args nil (ua1 ++ ns1 ++ ws1) ⍮ s ↘ vs1 /\
          Fcargs gs' of p ua2 in gc_deps ⍮ gc_stack ⍮ env_args nil (ua2 ++ ns2 ++ ws2) ⍮ s ↘ vs2 /\
          Fihs vs1 at gs' under ρa Aa in gc_deps ⍮ gc_stack ⍮ env_args nil (ua1 ++ ns1 ++ ws1) ⍮ s2 ↘ ihs1 /\
          Fihs vs2 at gs' under ρb Ab in gc_deps ⍮ gc_stack ⍮ env_args nil (ua2 ++ ns2 ++ ws2) ⍮ s2 ↘ ihs2 /\
          tele_prefix_rel (args_rel ns1 c) (List.length (cargs_nonrec gs)) (ws1 ++ nonrec_arg_vals gs' vs1) (ws2 ++ nonrec_arg_vals gs' vs2) /\
          con_args_rel p D adm nparams_rel args_rel doms_rel ua1 ua2 (ns1 ++ ws1) (ns2 ++ ws2) gs' vs1 vs2 /\
          rec_results_rel ua1 ua2 (ns1 ++ ws1) (ns2 ++ ws2) gs' vs1 vs2 ihs1 ihs2.
    Proof.
      intros ua1 ua2 ns1 ns2 c gs Ha1 Ha2 L1 L2 H12 Hc.
      pose proof (trefl _ _ H12) as H11.
      pose proof (adm_arg_vars _ _ _ _ _ _ (HOk _ Ha1)) as Hn1; pose proof (adm_arg_vars _ _ _ _ _ _ (HOk _ Ha2)) as Hn2.
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
          destruct (Hn1 _ _ _ _ _ _ _ _ s H11 Hc HA Hp11) as [a0 a1 E0 E1 R1].
          destruct (Hn2 _ _ _ _ _ _ _ _ s H12 Hc HA Hp) as [a0' a2 E0' E2 R2].
          pose proof (functional_eval_exp _ _ _ _ E0 E0') as <-.
          pose proof (HaP _ _ _ _ _ _ _ _ H12 Hc HA Hp) as HP.
          assert (R12 : args_rel ns1 c (List.length (cargs_nonrec gs1)) ws1 (⇑! a1 s) (⇑! a2 s))
            by (etransitivity; [ symmetry; exact R1 | exact R2 ]).
          destruct (IH (gs1 ++ ca_arg A :: nil) (ws1 ++ ⇑! a1 s :: nil) (ws2 ++ ⇑! a2 s :: nil) (S s) s2)
            as (vs1 & vs2 & ihs1 & ihs2 & F1 & F2 & I1 & I2 & P & Hia & Hir).
          { rewrite Heq, <- List.app_assoc; reflexivity. }
          { rewrite cargs_nonrec_app, List.length_app, Nat.add_comm; cbn; apply tele_prefix_rel_snoc; assumption. }
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
          destruct (shape_type_exists _ (HOk _ Ha1) _ _ _ _ _ _ _ _ H11 Hc Hp11 0 nil nil ltac:(lia) (tele_prefix_rel_nil _)) as [a1 Ea1].
          destruct (shape_type_exists _ (HOk _ Ha2) _ _ _ _ _ _ _ _ H12 Hc Hp 0 nil nil ltac:(lia) (tele_prefix_rel_nil _)) as [a2 Ea2].
          cbn [ptyp_skip] in Ea1, Ea2; rewrite List.app_nil_r in Ea1, Ea2.
          pose proof (shape_neut _ _ Ha1 Ha2 L1 L2 _ _ _ _ _ _ _ _ H12 Hc Hp (List.length (ptyp_doms t)) 0 nil nil a1 a2
                        (d_var s) (d_var s) eq_refl (tele_prefix_rel_nil _)
                        ltac:(rewrite List.app_nil_r; exact Ea1) ltac:(rewrite List.app_nil_r; exact Ea2) var_per_bot) as Hsh.
          destruct (ih_neut _ _ Ha1 Ha2 L1 L2 _ _ _ _ _ _ _ _ H12 Hc Hp (List.length (ptyp_doms t)) 0 nil nil a1 a2
                        (d_var s) (d_var s) (d_var s2) (d_var s2) eq_refl (tele_prefix_rel_nil _)
                        ltac:(rewrite List.app_nil_r; exact Ea1) ltac:(rewrite List.app_nil_r; exact Ea2) var_per_bot var_per_bot)
            as (h1 & h2 & G1 & G2 & Hih).
          cbn [ptyp_skip] in Hsh, G1, G2, Hih.
          repeat rewrite List.app_nil_r in Hsh; repeat rewrite List.app_nil_r in Hih; rewrite List.app_nil_r in G1, G2.
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
    Lemma read_brs_rel : forall ua1 ua2 s ns1 ns2, adm ua1 -> adm ua2 ->
        List.length ua1 = ind_nu D -> List.length ua2 = ind_nu D ->
        Ftele T in gc_deps ⍮ gc_stack ⍮ env_args nil ua1 ⍮ s ↘ ns1 ->
        Ftele T in gc_deps ⍮ gc_stack ⍮ env_args nil ua2 ⍮ s ↘ ns2 -> tele_rel nparams_rel T ns1 ns2 ->
        forall cs Bs1 Bs2, (forall c gs, In (c, gs) cs -> ind_con D c = Some gs) ->
        (forall c n B, In (c, n, B) Bs1 -> brs_lookup Bsa c = Some (n, B) /\ In (c, n, B) Bsa) ->
        (forall c n B, In (c, n, B) Bs2 -> brs_lookup Bsb c = Some (n, B) /\ In (c, n, B) Bsb) ->
        brs_names cs Bs1 -> brs_names cs Bs2 ->
        exists Bs', Rbrs Bs1 at cs of p D ua1 under Aa in gc_deps ⍮ gc_stack ⍮ ρa ⍮ s ↘ Bs' /\ Rbrs Bs2 at cs of p D ua2 under Ab in gc_deps ⍮ gc_stack ⍮ ρb ⍮ s ↘ Bs'.
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
        destruct (fresh_args _ _ _ _ _ _ Ha1 Ha2 L1 L2 H12 Hc gs nil nil nil (s + ind_nn D) (s + ind_nn D + List.length gs) eq_refl (tele_prefix_rel_nil _))
          as (vs1 & vs2 & ihs1 & ihs2 & C1 & C2 & I1 & I2 & P & Hia & Hir).
        rewrite !List.app_nil_r in C1, C2, I1, I2; cbn in P.
        repeat rewrite List.app_nil_r in Hia; repeat rewrite List.app_nil_r in Hir.
        destruct (length_tnr _ _ H12) as [Ln1 Ln2].
        assert (Hlen : forall ua ns : list domain, List.length ua = ind_nu D -> List.length ns = ind_nn D -> List.length (ua ++ ns) = ind_np D)
          by (intros; rewrite List.length_app; unfold ind_nn in *; lia).
        assert (Hm : ind_rel p D adm nparams_rel args_rel doms_rel ns1 ns2 (d_con p c ((ua1 ++ ns1) ++ vs1)) (d_con p c ((ua2 ++ ns2) ++ vs2))).
        { apply ind_rel_con with (gs := gs); rewrite ?firstn_app_exact, ?skipn_app_exact by assumption;
            [ exact H12 | exact Hc | apply Hlen; assumption | apply Hlen; assumption | exact Ha1 | exact Ha2
            | exact H11 | exact (trefl_r _ _ H12) | apply tele_rel_of_pre; exact P | exact Hia ]. }
        pose proof (Hbr _ _ _ _ _ Hc HL1 HL2 (ua1 ++ ns1) (ua2 ++ ns2) vs1 vs2 ihs1 ihs2) as HB.
        rewrite !firstn_app_exact, !skipn_app_exact in HB by assumption.
        destruct (HB (Hlen _ _ L1 Ln1) (Hlen _ _ L2 Ln2) Ha1 Ha2 H12 (tele_rel_of_pre _ _ _ _ P) Hia Hir)
          as (r1 & r2 & Er1 & Er2 & Hrr).
        destruct (Hmot _ _ _ _ Hm) as (t1 & t2 & T1 & T2 & HR).
        destruct (per_elem_then_per_top HR Hrr (s + n1)) as (B' & RB1 & RB2).
        rewrite <- !List.app_assoc in T1, T2.
        destruct (IH Bs1 Bs2) as (Bs' & RBs1 & RBs2).
        { intros c' gs' Hin; apply Hcs; right; exact Hin. }
        { intros c' n' Bx Hin; apply HB1; right; exact Hin. }
        { intros c' n' Bx Hin; apply HB2; right; exact Hin. }
        { exact Hn1. }
        { exact Hn2. }
        exists (nbrs_cons c n1 B' Bs'); split; econstructor; try eassumption; intros gs1' t' gs2' E; exact (Hplen _ _ _ _ _ Hc E).
    Qed.

    Lemma per_bot_elim : forall as1 as2 e e',
        List.length as1 = ind_np D -> List.length as2 = ind_np D ->
        adm (List.firstn (ind_nu D) as1) -> adm (List.firstn (ind_nu D) as2) ->
        Dom e ≈ e' ∈ per_bot ->
        Dom d_elim ρa nm Aa Bsa p as1 e ≈ d_elim ρb nm Ab Bsb p as2 e' ∈ per_bot.
    Proof.
      intros * L1 L2 Ha1 Ha2 He s.
      destruct (He s) as (M & RM1 & RM2).
      assert (Lu1 : List.length (List.firstn (ind_nu D) as1) = ind_nu D) by (rewrite List.length_firstn; lia).
      assert (Lu2 : List.length (List.firstn (ind_nu D) as2) = ind_nu D) by (rewrite List.length_firstn; lia).
      destruct (fresh_nparams_pair _ _ s (HOk _ Ha1) (HOk _ Ha2)) as (ns1 & ns2 & F1 & F2 & H12).
      pose proof (ind_rel_var _ _ _ _ _ _ (s + ind_nn D) Ha1 Ha2 Lu1 Lu2 H12 (trefl _ _ H12) (trefl_r _ _ H12)) as Hv.
      destruct (Hmot _ _ _ _ Hv) as (a1 & a2 & E1 & E2 & HR).
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
      (forall ns ns' m m', ind_rel p D adm nparams_rel args_rel doms_rel ns ns' m m' ->
         exists r r', ⟦elim m under nm Aa Bsa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ r /\ ⟦elim m' under nm Ab Bsb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ r' /\
           Rel ns m ns' m' r r') /\
      (forall u u' pre pre' gs vs vs', con_args_rel p D adm nparams_rel args_rel doms_rel u u' pre pre' gs vs vs' ->
         exists ihs ihs', ⟦ihs vs of gs under nm Aa Bsa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ ihs /\ ⟦ihs vs' of gs under nm Ab Bsb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ ihs' /\
           rec_results_rel u u' pre pre' gs vs vs' ihs ihs') /\
      (forall u u' pre pre' t v v', rec_arg_rel p D adm nparams_rel args_rel doms_rel u u' pre pre' t v v' ->
         exists ih ih', ⟦ih v of t under nm Aa Bsa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ ih /\ ⟦ih v' of t under nm Ab Bsb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ ih' /\
           rec_result_rel u u' pre pre' t v v' ih ih') /\
      (forall u u' pre pre' t f c f' c', rec_arg_app_rel p D adm nparams_rel args_rel doms_rel u u' pre pre' t f c f' c' ->
         exists fc fc' r r', $| f & c | gc_deps ⍮ gc_stack ↘ fc /\ $| f' & c' | gc_deps ⍮ gc_stack ↘ fc' /\
           ⟦ih fc of t under nm Aa Bsa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ r /\ ⟦ih fc' of t under nm Ab Bsb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ r' /\
           rec_result_rel u u' pre pre' t fc fc' r r').
    Proof.
      apply ind_rel_mut_ind_all.
      - (** A constructor: the branches at its own parameters, moved to the
            indices ([motive_rel_move]). *)
        intros ns ns' c gs bs bs' vs vs' Hn Hc Hb Hb' Ho Ho' Hs Hs' Ha Hia IH.
        destruct IH as (ihs & ihs' & Ei & Ei' & Hir).
        destruct (brs_names_lookup _ _ _ _ Hna Hc) as (n & Ba & HBa & HinA).
        destruct (brs_names_lookup _ _ _ _ Hnb Hc) as (n' & Bb & HBb & HinB).
        pose proof (Hara _ _ _ _ Hc HinA) as Hn0; pose proof (Harb _ _ _ _ Hc HinB) as Hn0'.
        assert (n' = n) as -> by lia.
        assert (H12 : tele_rel nparams_rel T (List.skipn (ind_nu D) bs) (List.skipn (ind_nu D) bs'))
          by exact (ttrans _ _ _ (ttrans _ _ _ (tsym _ _ Hs) Hn) Hs').
        destruct (Hbr _ _ _ _ _ Hc HBa HBb _ _ _ _ _ _ Hb Hb' Ho Ho' H12 Ha Hia Hir) as (r & r' & Er & Er' & Hrr).
        destruct (con_args_rel_length _ _ _ _ _ _ _ Hia) as [Hlv Hlv'].
        assert (Hm : ind_rel p D adm nparams_rel args_rel doms_rel ns ns' (d_con p c (bs ++ vs)) (d_con p c (bs' ++ vs'))) by (econstructor; eassumption).
        exists r, r'; split; [| split ].
        + eapply eval_elim_con; [ exact Hl | exact Hc | rewrite List.length_app; lia | exact HBa | exact Hn0 | |].
          * rewrite skipn_app_exact by exact Hb; exact Ei.
          * rewrite firstn_app_exact, skipn_app_exact by exact Hb; exact Er.
        + eapply eval_elim_con; [ exact Hl | exact Hc | rewrite List.length_app; lia | exact HBb | exact Hn0 | |].
          * rewrite skipn_app_exact by exact Hb'; exact Ei'.
          * rewrite firstn_app_exact, skipn_app_exact by exact Hb'; exact Er'.
        + apply (motive_rel_move _ _ _ _ _ _ Hm Hs Hs'); exact Hrr.
      - (** A neutral: the motive at its own parameters. *)
        intros ns ns' as1 as2 e e' Hn Hl1 Hl2 Ha1 Ha2 Hs1 Hs2 He.
        assert (Hm : ind_rel p D adm nparams_rel args_rel doms_rel ns ns' (⇑ (d_ind p as1) e) (⇑ (d_ind p as2) e')) by (econstructor; eassumption).
        pose proof (idx _ _ _ _ _ _ Hm Hs1 Hs2) as Hm1.
        destruct (Hmot _ _ _ _ Hm1) as (a1 & a2 & Ea1 & Ea2 & HR).
        exists (⇑ a1 (d_elim ρa nm Aa Bsa p as1 e)), (⇑ a2 (d_elim ρb nm Ab Bsb p as2 e')).
        split; [ eapply eval_elim_neut; eassumption | split; [ eapply eval_elim_neut; eassumption |] ].
        pose proof (per_bot_then_per_elem HR (per_bot_elim _ _ _ _ Hl1 Hl2 Ha1 Ha2 He)) as Hrr.
        apply (motive_rel_move _ _ _ _ _ _ Hm Hs1 Hs2); exact Hrr.
      - intros; exists nil, nil; split; [ constructor | split; [ constructor | constructor ] ].
      - intros * Hia (ihs & ihs' & Ei & Ei' & Hir).
        exists ihs, ihs'; split; [ constructor; exact Ei | split; [ constructor; exact Ei' | constructor; exact Hir ] ].
      - intros * Hsh (ih & ih' & Eh & Eh' & Hhh) Hia (ihs & ihs' & Ei & Ei' & Hir).
        exists (ih :: ihs), (ih' :: ihs'); split; [ econstructor; eassumption | split; [ econstructor; eassumption |] ].
        econstructor; eassumption.
      - intros * Hb Hb' Hr (ih & ih' & Eh & Eh' & Hhh).
        exists ih, ih'; split; [ constructor; exact Eh | split; [ constructor; exact Eh' |] ].
        cbn [rec_result_rel]; exists bs bs'; [ exact Hb | exact Hb' | exact Hhh ].
      - intros pre B u u' pre' t f f' Hf IH.
        exists (d_ihfn ρa nm Aa Bsa t f), (d_ihfn ρb nm Ab Bsb t f').
        split; [ constructor | split; [ constructor |] ].
        cbn [rec_result_rel]; intros c c' Hcc.
        destruct (IH c c' Hcc) as (fc & fc' & r & r' & Ef & Ef' & Er & Er' & Hrr).
        exists fc, fc', r, r'; split; [ exact Ef | split; [ exact Ef' | split; [| split; [| exact Hrr ] ] ] ];
          econstructor; eassumption.
      - intros f c r f' c' r' u u' pre pre' t Ef Ef' Hsh (ih & ih' & Eh & Eh' & Hhh).
        exists r, r', ih, ih'; repeat split; assumption.
    Qed.
  End IndElim.

  (** ** Recursive Results at Other Prefixes

      The recursive results of a recursive argument at other bases and
      related prefixes ([rec_arg_rel_rebase]), for a family [Rel] that does
      not depend on the indices of related elements. *)
  Section IhRebase.
    #[local] Set Default Proof Using "All".
    Variable (p : qname) (D : ind_decl) (ups : list domain).
    Variable (nparams_rel : nat -> list domain -> relation domain).
    Variable (args_rel : list domain -> String.string -> nat -> list domain -> relation domain).
    Variable (doms_rel : list domain -> exp -> relation domain).
    Let T := List.rev (ind_nparams D).
    Hypothesis (Hass : tele_ass (ind_params D)).
    Hypothesis (HnP : forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_prefix_rel nparams_rel k vs vs' -> PER (nparams_rel k vs)).
    Hypothesis (HnI : forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_prefix_rel nparams_rel k vs vs' -> (nparams_rel k vs <~> nparams_rel k vs')).
    Hypothesis (HaP : forall ms ms' c gs k A vs vs', tele_rel nparams_rel T ms ms' -> ind_con D c = Some gs ->
                      List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (args_rel ms c) k vs vs' -> PER (args_rel ms c k vs)).
    Hypothesis (HaI : forall ms ms' c gs k A vs vs', tele_rel nparams_rel T ms ms' -> ind_con D c = Some gs ->
                      List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (args_rel ms c) k vs vs' ->
                      (args_rel ms c k vs <~> args_rel ms' c k vs')).
    Hypothesis (HdP : forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_rel nparams_rel T ms ms' ->
                      ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                      tele_prefix_rel (args_rel ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
                      List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel doms_rel ms ws (ptyp_doms t)) k ys ys' ->
                      PER (doms_rel (ms ++ ws ++ ys) B)).
    Hypothesis (HdI : forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_rel nparams_rel T ms ms' ->
                      ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                      tele_prefix_rel (args_rel ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
                      List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel doms_rel ms ws (ptyp_doms t)) k ys ys' ->
                      (doms_rel (ms ++ ws ++ ys) B <~> doms_rel (ms' ++ ws' ++ ys') B)).
    Variable (adm : list domain -> Prop).
    Variable (Rel : list domain -> domain -> list domain -> domain -> relation domain).
    Hypothesis (HRel : forall ns ns' m m' ns1 ns1', ind_rel p D adm nparams_rel args_rel doms_rel ns ns' m m' ->
                   tele_rel nparams_rel T ns ns1 -> tele_rel nparams_rel T ns' ns1' -> (Rel ns m ns' m' <~> Rel ns1 m ns1' m')).
    Let nsa := nonrec_arg_vals_snoc_arg p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI.
    Let nsr := nonrec_arg_vals_snoc_rec p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI.

    Lemma rec_result_rel_rebase :
        (forall u1 u1' pre1 pre1' t v v', rec_arg_rel p D adm nparams_rel args_rel doms_rel u1 u1' pre1 pre1' t v v' ->
           forall ih ih', rec_result_rel doms_rel Rel u1 u1' pre1 pre1' t v v' ih ih' ->
           forall u2 u2' ms1 ms1' ms2 ms2' c gs1 t0 gs2 ws1 ws1' ws2 ws2' k ys1 ys1' ys2 ys2',
             pre1 = ms1 ++ ws1 ++ ys1 -> pre1' = ms1' ++ ws1' ++ ys1' ->
             adm_uparams D u1 nparams_rel args_rel doms_rel u2 -> adm_uparams D u1' nparams_rel args_rel doms_rel u2' ->
             ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
             tele_rel nparams_rel T ms1 ms1' -> tele_rel nparams_rel T ms1 ms2 -> tele_rel nparams_rel T ms1' ms2' ->
             tele_prefix_rel (args_rel ms1 c) (List.length (cargs_nonrec gs1)) ws1 ws1' ->
             tele_prefix_rel (args_rel ms1 c) (List.length (cargs_nonrec gs1)) ws1 ws2 ->
             tele_prefix_rel (args_rel ms1' c) (List.length (cargs_nonrec gs1)) ws1' ws2' ->
             ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
             tele_prefix_rel (shape_doms_rel doms_rel ms1 ws1 (ptyp_doms t0)) k ys1 ys1' ->
             tele_prefix_rel (shape_doms_rel doms_rel ms1 ws1 (ptyp_doms t0)) k ys1 ys2 ->
             tele_prefix_rel (shape_doms_rel doms_rel ms1' ws1' (ptyp_doms t0)) k ys1' ys2' ->
             rec_result_rel doms_rel Rel u2 u2' (ms2 ++ ws2 ++ ys2) (ms2' ++ ws2' ++ ys2') t v v' ih ih').
    Proof.
      enough (H : (forall ns ns' x y, ind_rel p D adm nparams_rel args_rel doms_rel ns ns' x y -> True) /\
                  (forall u u' pre pre' gs vs vs', con_args_rel p D adm nparams_rel args_rel doms_rel u u' pre pre' gs vs vs' -> True) /\
                  (forall u1 u1' pre1 pre1' t v v', rec_arg_rel p D adm nparams_rel args_rel doms_rel u1 u1' pre1 pre1' t v v' ->
                     forall ih ih', rec_result_rel doms_rel Rel u1 u1' pre1 pre1' t v v' ih ih' ->
                     forall u2 u2' ms1 ms1' ms2 ms2' c gs1 t0 gs2 ws1 ws1' ws2 ws2' k ys1 ys1' ys2 ys2',
                       pre1 = ms1 ++ ws1 ++ ys1 -> pre1' = ms1' ++ ws1' ++ ys1' ->
                       adm_uparams D u1 nparams_rel args_rel doms_rel u2 -> adm_uparams D u1' nparams_rel args_rel doms_rel u2' ->
                       ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
                       tele_rel nparams_rel T ms1 ms1' -> tele_rel nparams_rel T ms1 ms2 -> tele_rel nparams_rel T ms1' ms2' ->
                       tele_prefix_rel (args_rel ms1 c) (List.length (cargs_nonrec gs1)) ws1 ws1' ->
                       tele_prefix_rel (args_rel ms1 c) (List.length (cargs_nonrec gs1)) ws1 ws2 ->
                       tele_prefix_rel (args_rel ms1' c) (List.length (cargs_nonrec gs1)) ws1' ws2' ->
                       ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
                       tele_prefix_rel (shape_doms_rel doms_rel ms1 ws1 (ptyp_doms t0)) k ys1 ys1' ->
                       tele_prefix_rel (shape_doms_rel doms_rel ms1 ws1 (ptyp_doms t0)) k ys1 ys2 ->
                       tele_prefix_rel (shape_doms_rel doms_rel ms1' ws1' (ptyp_doms t0)) k ys1' ys2' ->
                       rec_result_rel doms_rel Rel u2 u2' (ms2 ++ ws2 ++ ys2) (ms2' ++ ws2' ++ ys2') t v v' ih ih') /\
                  (forall u1 u1' pre1 pre1' t f a f' a', rec_arg_app_rel p D adm nparams_rel args_rel doms_rel u1 u1' pre1 pre1' t f a f' a' ->
                     forall fa fa' ih ih', $| f & a | gc_deps ⍮ gc_stack ↘ fa -> $| f' & a' | gc_deps ⍮ gc_stack ↘ fa' ->
                     rec_result_rel doms_rel Rel u1 u1' pre1 pre1' t fa fa' ih ih' ->
                     forall u2 u2' ms1 ms1' ms2 ms2' c gs1 t0 gs2 ws1 ws1' ws2 ws2' k ys1 ys1' ys2 ys2',
                       pre1 = ms1 ++ ws1 ++ ys1 -> pre1' = ms1' ++ ws1' ++ ys1' ->
                       adm_uparams D u1 nparams_rel args_rel doms_rel u2 -> adm_uparams D u1' nparams_rel args_rel doms_rel u2' ->
                       ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
                       tele_rel nparams_rel T ms1 ms1' -> tele_rel nparams_rel T ms1 ms2 -> tele_rel nparams_rel T ms1' ms2' ->
                       tele_prefix_rel (args_rel ms1 c) (List.length (cargs_nonrec gs1)) ws1 ws1' ->
                       tele_prefix_rel (args_rel ms1 c) (List.length (cargs_nonrec gs1)) ws1 ws2 ->
                       tele_prefix_rel (args_rel ms1' c) (List.length (cargs_nonrec gs1)) ws1' ws2' ->
                       ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
                       tele_prefix_rel (shape_doms_rel doms_rel ms1 ws1 (ptyp_doms t0)) k ys1 ys1' ->
                       tele_prefix_rel (shape_doms_rel doms_rel ms1 ws1 (ptyp_doms t0)) k ys1 ys2 ->
                       tele_prefix_rel (shape_doms_rel doms_rel ms1' ws1' (ptyp_doms t0)) k ys1' ys2' ->
                       rec_result_rel doms_rel Rel u2 u2' (ms2 ++ ws2 ++ ys2) (ms2' ++ ws2' ++ ys2') t fa fa' ih ih'))
        by exact (proj1 (proj2 (proj2 H))).
      pose proof (nparams_rel_sym p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI) as tsym.
      pose proof (nparams_rel_trans p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI) as ttrans.
      apply ind_rel_mut_ind_all; try (intros; exact I).
      - (** The end of the shape: the parameters at the new bases, and the
            family moved to them. *)
        intros Ps u1 pre1 bs u1' pre1' bs' v v' k0 E E' Hr _ ih ih' Hih
          u2 u2' ms1 ms1' ms2 ms2' c gs1 t0 gs2 ws1 ws1' ws2 ws2' k ys1 ys1' ys2 ys2'
          Hρ Hρ' Ha Ha' Hc H11' H12 H12' Hw11' Hw12 Hw12' Hs Hk Hy11' Hy12 Hy12'.
        destruct (ptyp_skip_self _ _ _ _ Hs) as [Hkd HPs].
        cbn [rec_result_rel] in Hih |- *; destruct Hih as [b0 b0' F0 F0' Hrr].
        pose proof (functional_eval_exps' _ _ _ _ F0 E) as ->.
        pose proof (functional_eval_exps' _ _ _ _ F0' E') as ->.
        assert (Hyf : tele_rel (shape_doms_rel doms_rel ms1 ws1 (ptyp_doms t0)) (ptyp_doms t0) ys1 ys2)
          by (destruct Hy12 as [Hyl Hya]; split; [ lia | exact Hya ]).
        assert (Hyf' : tele_rel (shape_doms_rel doms_rel ms1' ws1' (ptyp_doms t0)) (ptyp_doms t0) ys1' ys2')
          by (destruct Hy12' as [Hyl Hya]; split; [ lia | exact Hya ]).
        destruct (adm_rec_params _ _ _ _ _ _ Ha _ _ _ _ _ _ _ _ _ _ _ H12 Hc eq_refl Hw12 Hyf) as [b1 b2 F1 F2 R12].
        destruct (adm_rec_params _ _ _ _ _ _ Ha' _ _ _ _ _ _ _ _ _ _ _ H12' Hc eq_refl Hw12' Hyf') as [b1' b2' F1' F2' R12'].
        rewrite HPs in F1, F2, F1', F2'; subst pre1 pre1'.
        pose proof (functional_eval_exps' _ _ _ _ F1 E) as ->.
        pose proof (functional_eval_exps' _ _ _ _ F1' E') as ->.
        exists b2 b2'; [ exact F2 | exact F2' | exact (proj1 (HRel _ _ _ _ _ _ Hr R12 R12' _ _) Hrr) ].
      - (** A domain: an argument of the new domain is one of the old. *)
        intros pre1 B u1 u1' pre1' t f f' Hf IH ih ih' Hih
          u2 u2' ms1 ms1' ms2 ms2' c gs1 t0 gs2 ws1 ws1' ws2 ws2' k ys1 ys1' ys2 ys2'
          Hρ Hρ' Ha Ha' Hc H11' H12 H12' Hw11' Hw12 Hw12' Hs Hk Hy11' Hy12 Hy12'.
        subst pre1 pre1'.
        pose proof (nparams_rel_refl_l p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI _ _ H11') as H11.
        pose proof (nparams_rel_refl_r p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI _ _ H11') as H1'1'.
        assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
          by (rewrite cargs_nonrec_app, List.length_app; lia).
        pose proof (args_rel_pre_refl_l p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI _ _ _ H11 Hc _ _ _ HK Hw12) as Hw11.
        pose proof (args_rel_pre_refl_l p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI _ _ _ H1'1' Hc _ _ _ HK Hw12') as Hw1'1'.
        pose proof (doms_rel_refl_l p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ H11 Hc eq_refl Hw11 _ _ _ Hk Hy12) as Hy11.
        pose proof (doms_rel_refl_l p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ H1'1' Hc eq_refl Hw1'1' _ _ _ Hk Hy12') as Hy1'1'.
        destruct (shape_pi_step p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ H11 Hc Hw11 Hs Hy11)
          as (HB & Hs' & Hk' & HP & _).
        destruct (shape_pi_step p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ H1'1' Hc Hw1'1' Hs Hy1'1')
          as (_ & _ & _ & HP' & _).
        pose proof (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ H12 Hc eq_refl Hw12 HB Hy12) as E12.
        pose proof (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ H11' Hc eq_refl Hw11' HB Hy11') as E11'.
        cbn [rec_result_rel] in Hih |- *; intros a a' Haa.
        pose proof (proj2 (E12 _ _) Haa) as Haa1.
        assert (Ha1 : doms_rel (ms1 ++ ws1 ++ ys1) B a a) by (etransitivity; [ exact Haa1 | symmetry; exact Haa1 ]).
        assert (Ha1' : doms_rel (ms1' ++ ws1' ++ ys1') B a' a').
        { apply (proj1 (E11' _ _)) in Haa1.
          etransitivity; [ symmetry; exact Haa1 | exact Haa1 ]. }
        destruct (Hih a a' Haa1) as (fc & fc' & r & r' & Efc & Efc' & Er & Er' & Hih').
        exists fc, fc', r, r'; split; [ exact Efc | split; [ exact Efc' | split; [ exact Er | split; [ exact Er' |] ] ] ].
        replace ((ms2 ++ ws2 ++ ys2) ++ a :: nil) with (ms2 ++ ws2 ++ (ys2 ++ a :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
        replace ((ms2' ++ ws2' ++ ys2') ++ a' :: nil) with (ms2' ++ ws2' ++ (ys2' ++ a' :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
        eapply (IH a a' Haa1 fc fc' r r' Efc Efc' Hih' u2 u2' ms1 ms1' ms2 ms2' c gs1 t0 gs2 ws1 ws1' ws2 ws2' (S k)
                  (ys1 ++ a :: nil) (ys1' ++ a' :: nil) (ys2 ++ a :: nil) (ys2' ++ a' :: nil));
          [ rewrite <- !List.app_assoc; reflexivity | rewrite <- !List.app_assoc; reflexivity
          | exact Ha | exact Ha' | exact Hc | exact H11' | exact H12 | exact H12' | exact Hw11' | exact Hw12 | exact Hw12'
          | exact Hs' | exact Hk' | | |];
          (apply tele_prefix_rel_snoc; [ eassumption | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB) ]);
          [ exact Haa1 | exact Ha1 | exact Ha1' ].
      - intros f a r f' a' r' u1 u1' pre1 pre1' t Ef Ef' Hsh IH fa fa' ih ih' Efa Efa' Hih; intros.
        pose proof (functional_eval_app _ _ _ _ Efa Ef) as ->.
        pose proof (functional_eval_app _ _ _ _ Efa' Ef') as ->.
        eapply IH; eassumption.
    Qed.

    (** The recursive results of related arguments, likewise. *)
    Lemma rec_results_rel_rebase : forall u1 u1' pre1 pre1' gs vs vs', con_args_rel p D adm nparams_rel args_rel doms_rel u1 u1' pre1 pre1' gs vs vs' ->
        forall ihs ihs', rec_results_rel doms_rel Rel u1 u1' pre1 pre1' gs vs vs' ihs ihs' ->
        forall u2 u2' ms1 ms1' ms2 ms2' c gsf gs1 vp vp',
          pre1 = ms1 ++ nonrec_arg_vals gs1 vp -> pre1' = ms1' ++ nonrec_arg_vals gs1 vp' ->
          List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
          adm_uparams D u1 nparams_rel args_rel doms_rel u2 -> adm_uparams D u1' nparams_rel args_rel doms_rel u2' ->
          ind_con D c = Some gsf -> gsf = gs1 ++ gs ->
          tele_rel nparams_rel T ms1 ms1' -> tele_rel nparams_rel T ms1 ms2 -> tele_rel nparams_rel T ms1' ms2' ->
          tele_rel (args_rel ms1 c) (cargs_nonrec gsf) (nonrec_arg_vals gsf (vp ++ vs)) (nonrec_arg_vals gsf (vp' ++ vs')) ->
          rec_results_rel doms_rel Rel u2 u2' (ms2 ++ nonrec_arg_vals gs1 vp) (ms2' ++ nonrec_arg_vals gs1 vp') gs vs vs' ihs ihs'.
    Proof.
      intros u1 u1' pre1 pre1' gs vs vs' H.
      induction H as [u1 u1' pre1 pre1' | u1 u1' pre1 v pre1' v' gs vs vs' A Hia IH
                     | u1 u1' pre1 pre1' t v v' gs vs vs' Hsh Hia IH];
        intros ihs ihs' Hir u2 u2' ms1 ms1' ms2 ms2' c gsf gs1 vp vp' Hρ Hρ' Hl Hl' Ha Ha' Hc Heq H11' H12 H12' Har;
        inversion Hir; subst.
      - constructor.
      - constructor.
        rewrite <- !List.app_assoc, <- (nsa gs1 vp A v Hl), <- (nsa gs1 vp' A v' Hl').
        apply (IH ihs ihs' ltac:(assumption) u2 u2' ms1 ms1' ms2 ms2' c (gs1 ++ ca_arg A :: gs) (gs1 ++ ca_arg A :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil));
          [ rewrite nsa, List.app_assoc by assumption; reflexivity
          | rewrite nsa, List.app_assoc by assumption; reflexivity
          | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | exact Ha | exact Ha' | exact Hc
          | rewrite <- List.app_assoc; reflexivity | exact H11' | exact H12 | exact H12' | rewrite <- !List.app_assoc; exact Har ].
      - pose proof (nparams_rel_refl_l p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI _ _ H11') as H11.
        pose proof (nonrec_prefix p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ H11 Hc eq_refl Hl Hl' Har) as Hw11'.
        assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t :: gs)))
          by (rewrite cargs_nonrec_app, List.length_app; lia).
        pose proof (args_rel_pre_refl_l p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI _ _ _ H11 Hc _ _ _ HK Hw11') as Hw11.
        pose proof (args_prefix_rel_refl_r p D ups nparams_rel args_rel doms_rel Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ H11' Hc HK Hw11') as Hw1'1'.
        constructor.
        + rewrite <- (List.app_nil_r (nonrec_arg_vals gs1 vp)), <- (List.app_nil_r (nonrec_arg_vals gs1 vp')).
          match goal with H : rec_result_rel _ _ _ _ _ _ t v v' _ _ |- _ => rename H into Hih end.
          apply (rec_result_rel_rebase _ _ _ _ _ _ _ Hsh _ _ Hih u2 u2' ms1 ms1' ms2 ms2' c gs1 t gs
                   (nonrec_arg_vals gs1 vp) (nonrec_arg_vals gs1 vp') (nonrec_arg_vals gs1 vp) (nonrec_arg_vals gs1 vp') 0 nil nil nil nil);
            [ rewrite List.app_nil_r; reflexivity | rewrite List.app_nil_r; reflexivity | exact Ha | exact Ha' | exact Hc
            | exact H11' | exact H12 | exact H12' | exact Hw11' | exact Hw11 | exact Hw1'1' | reflexivity | lia
            | apply tele_prefix_rel_nil | apply tele_prefix_rel_nil | apply tele_prefix_rel_nil ].
        + rewrite <- (nsr gs1 vp t v Hl), <- (nsr gs1 vp' t v' Hl').
          apply (IH _ _ ltac:(eassumption) u2 u2' ms1 ms1' ms2 ms2' c (gs1 ++ ca_rec t :: gs) (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil));
            [ rewrite nsr by assumption; reflexivity
            | rewrite nsr by assumption; reflexivity
            | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | exact Ha | exact Ha' | exact Hc
            | rewrite <- List.app_assoc; reflexivity | exact H11' | exact H12 | exact H12' | rewrite <- !List.app_assoc; exact Har ].
    Qed.
  End IhRebase.
End Fixed_GCtx.
