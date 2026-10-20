(** * The Eliminator in the PER Model

    The eliminator of a group of inductive types relates related elements
    at a family of relations, given that its motives are related at
    related arguments and its branches at related arguments and recursive
    results.  This is the semantic content of the eliminator's rule; the
    cases of the fundamental theorem instantiate it.

    The elements are related at their own parameters ([ind_rel]), under
    model L: a recursive argument's index is admissible at the element's own
    prefix ([okr_at]), and a neutral's uniform parameters at the fresh
    variables ([adm_fresh]).  A stuck eliminator reads back its motives and
    branches under fresh variables of the types the scrutinee's uniform
    parameters give; the fresh variables at two admissible bases are related
    through those at the type's base [ups], and the indices of recursive
    arguments made of them are admissible by the recursive-index field of
    [adm_fresh] and the type-level admissibility [Hcd]. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Export PER Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER.
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

  Lemma per_bot_app : forall m m' n n', Dom m ≈ m' ∈ per_bot -> Dom n ≈ n' ∈ per_top -> Dom m $ᵈ n ≈ m' $ᵈ n' ∈ per_bot.
  Proof.
    intros * Hm Hn s; destruct (Hm s) as (M & HM & HM'); destruct (Hn s) as (N & HN & HN').
    exists (M $ⁿ N); split; constructor; assumption.
  Qed.

  (** A declared member of a group is itself at the group's uniform
      parameters. *)
  Lemma mref_decl_inv : forall p D j Mj pm ups r, ind_lookup gc_deps gc_stack p = Some D ->
      ind_member D j = Some Mj -> im_head Mj = mh_decl pm ->
      ⟦mref j of p ups ⟧ gc_deps ⍮ gc_stack ↘ r -> r = (p, j, ups).
  Proof.
    intros * Hl HM Hh H; inversion H; subst; [ reflexivity |].
    match goal with H1 : ind_lookup _ _ p = Some _, H2 : ind_member _ j = Some _, H3 : im_head _ = mh_view _ _ _ _ |- _ =>
      rewrite Hl in H1; injection H1 as <-; rewrite HM in H2; injection H2 as <-; rewrite Hh in H3; discriminate end.
  Qed.

  Lemma eval_exps_length : forall Ms ρ vs, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ vs -> List.length vs = List.length Ms.
  Proof. induction Ms as [| M Ms IH]; intros ρ vs H; inversion H; subst; cbn; [ reflexivity | f_equal; eauto ]. Qed.

  (** A view member of a group is the container's member at the view's
      arguments. *)
  Lemma mref_view_inv : forall pq Dq i Mi qv kv Is vm Y r, ind_lookup gc_deps gc_stack pq = Some Dq ->
      ind_member Dq i = Some Mi -> im_head Mi = mh_view qv kv Is vm ->
      ⟦mref i of pq Y ⟧ gc_deps ⍮ gc_stack ↘ r -> exists py, r = (qv, kv, py) /\ ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil Y ↘ py.
  Proof.
    intros * Hq HM Hh H; inversion H; subst.
    - match goal with H1 : ind_lookup _ _ pq = Some _, H2 : ind_member _ i = Some _, H3 : im_head _ = mh_decl _ |- _ =>
        rewrite Hq in H1; injection H1 as <-; rewrite HM in H2; injection H2 as <-; rewrite Hh in H3; discriminate end.
    - match goal with H1 : ind_lookup _ _ pq = Some _, H2 : ind_member _ i = Some _, H3 : im_head _ = mh_view _ _ _ _ |- _ =>
        rewrite Hq in H1; injection H1 as <-; rewrite HM in H2; injection H2 as <-; rewrite Hh in H3; injection H3 as <- <- <- <- end.
      eexists; split; [ reflexivity | eassumption ].
  Qed.

  (** The codomain of the type of an argument of a function shape, at an
      argument, is the type of the rest of the shape. *)
  Lemma fam_cod_shfam_inv : forall p ups ρ t x a,
      ⟦ fam_cod ⟧ nil ↦ d_shfam p ups ρ t ↦ x ↘ a -> ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↦ x ↘ a.
  Proof.
    intros * H; unfold fam_cod in H; inversion H; subst.
    match goal with H1 : ⟦ #1 ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H1; subst end.
    match goal with H0 : ⟦ #0 ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H0; subst end.
    match goal with Ha : $| _ & _ | _ ⍮ _ ↘ _ |- _ => cbn in Ha; inversion Ha; subst; assumption end.
  Qed.

  (** Applications that read back alike have arguments that do. *)
  Lemma per_bot_app_inv : forall m m' n n', Dom m $ᵈ n ≈ m' $ᵈ n' ∈ per_bot -> Dom n ≈ n' ∈ per_top.
  Proof.
    intros * H s; destruct (H s) as (M & H1 & H2).
    inversion H1; subst; inversion H2; subst.
    eexists; split; eassumption.
  Qed.

  Lemma nth_blocks_motives : forall Bks j b, List.nth_error Bks j = Some b ->
      List.nth j (blocks_motives Bks) a_True = eb_motive b.
  Proof.
    intros * H; unfold blocks_motives.
    apply List.nth_error_nth; rewrite List.nth_error_map, H; reflexivity.
  Qed.

  Lemma nth_motives_sel_view : forall vm Bks j' v b, List.nth_error vm j' = Some v -> List.nth_error Bks v = Some b ->
      List.nth j' (motives_sel (Some vm) (blocks_motives Bks)) a_True = eb_motive b.
  Proof.
    intros * Hv Hb; cbn.
    apply List.nth_error_nth; rewrite List.nth_error_map, Hv; cbn.
    f_equal; exact (nth_blocks_motives _ _ _ Hb).
  Qed.

  Lemma cargs_corr_length : forall vm gs' gs, cargs_corr vm gs' gs -> List.length gs' = List.length gs.
  Proof.
    induction gs' as [| [A' | t'] gs' IH]; intros [| [A | t] gs] H; cbn in H |- *; try contradiction; try reflexivity.
    - f_equal; exact (IH _ H).
    - f_equal; exact (IH _ H).
    - f_equal; exact (IH _ (proj2 (proj2 H))).
  Qed.

  Lemma tele_rel_len : forall {X Y : Type} tr (T : list X) (T' : list Y) a b, List.length T = List.length T' ->
      tele_rel tr T a b -> tele_rel tr T' a b.
  Proof. intros * HT [Hl Hr]; split; [ congruence | exact Hr ]. Qed.

  Lemma cons_lookup_names : forall cs c, In c (List.map fst cs) -> exists gs, cons_lookup cs c = Some gs.
  Proof.
    induction cs as [| [c' gs'] cs IH]; cbn; intros c H; [ destruct H |].
    destruct (String.eqb_spec c c') as [-> | Hne]; [ eauto |].
    destruct H as [H | H]; [ congruence | exact (IH _ H) ].
  Qed.

  (** ** Fresh Variables of a Group *)
  Section ElimGroup.
    #[local] Set Default Proof Using "All".
    Variable (p : qname) (D : ind_decl) (ups : list domain).
    Variable (nr : nat -> nat -> list domain -> relation domain).
    Variable (ar : nat -> list domain -> String.string -> nat -> list domain -> relation domain).
    Variable (dr : nat -> list domain -> exp -> relation domain).
    Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (Hass : grp_tele_ass D).
    Hypothesis (HnP : nparams_per D nr) (HnI : nparams_inv D nr).
    Hypothesis (HaP : args_per D nr ar) (HaI : args_inv D nr ar).
    Hypothesis (HdP : doms_per D nr ar dr) (HdI : doms_inv D nr ar dr).
    (** The type's uniform parameters, admissible beside themselves at every
        related prefix. *)
    Hypothesis (Hcd : adm_uparams D ups nr ar dr ups).

    (** *** The Ends of Shapes at the Views

        A neutral's type at the end of a shape, by the form [view_fresh]
        gives it: a member's type of the group, its uniform parameters
        admissible for the member. *)
    #[warnings="-cannot-define-projection"]
    Record end_adm (j : nat) (hd : qname) (k : nat) (py : list domain) : Prop := mk_end_adm
      { ea_Mj : imember
      ; ea_member : ind_member D j = Some ea_Mj
      ; ea_ref : im_ref p j ea_Mj = (hd, k)
      ; ea_adm : grp_adm p D ups nr ar dr j py
      ; ea_len : List.length py = im_unu D ea_Mj }.

    Lemma mref_at_end_adm : forall X, adm_fresh p D ups nr ar dr X -> List.length X = ind_nu D ->
        forall j hd k py, mref_at p X j hd k py -> end_adm j hd k py.
    Proof.
      intros X HX LX j hd k py Hm; inversion Hm as [p0 D0 j0 Mj pm X0 Hl0 HMj Hh | p0 D0 j0 Mj qc kc Is vm X0 cups Hl0 HMj Hh E]; subst.
      - rewrite Hl in Hl0; injection Hl0 as <-.
        exists Mj; [ exact HMj | unfold im_ref; rewrite Hh; reflexivity | unfold grp_adm; rewrite HMj, Hh; exact HX
                   | unfold im_unu; rewrite Hh; exact LX ].
      - rewrite Hl in Hl0; injection Hl0 as <-.
        exists Mj; [ exact HMj | unfold im_ref; rewrite Hh; reflexivity
                   | unfold grp_adm; rewrite HMj, Hh;
                     exact (view_fresh_of_adm p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI X j Mj hd k Is vm py HX HMj Hh E)
                   | unfold im_unu; rewrite Hh; exact (eval_exps_length _ _ _ E) ].
    Qed.

    Lemma view_rec_end_adm : forall qc Is Y, view_fresh p D ups nr ar dr qc Is Y -> List.length Y = List.length Is ->
        forall j hd k py, view_rec_end p D ups nr ar dr qc Is Y j hd k py -> end_adm j hd k py.
    Proof.
      intros qc Is Y HY LY j hd k py H.
      destruct H as [qc0 Is0 Y0 j0 Mj kc vm' HMj Hh | qc0 Is0 Y0 j0 Mj qc' kc' Is' vm' py0 HMj Hh Lp Hw].
      - exists Mj; [ exact HMj | unfold im_ref; rewrite Hh; reflexivity | unfold grp_adm; rewrite HMj, Hh; exact HY
                   | unfold im_unu; rewrite Hh; exact LY ].
      - exists Mj; [ exact HMj | unfold im_ref; rewrite Hh; reflexivity
                   | unfold grp_adm; rewrite HMj, Hh; exact Hw
                   | unfold im_unu; rewrite Hh; exact Lp ].
    Qed.

    (** The end of a position a view nests through: its member's type at
        uniform parameters admissible for it. *)
    Lemma end_ok_adm : forall j hd k py, end_ok p D ups nr ar dr j hd k py -> end_adm j hd k py.
    Proof.
      intros j hd k py H.
      destruct H as [j0 Mj pm py0 HMj Hh Lp Ha | j0 Mj qv kv Is' vm' py0 HMj Hh Lp Hw].
      - exists Mj; [ exact HMj | unfold im_ref; rewrite Hh; reflexivity | unfold grp_adm; rewrite HMj, Hh; exact Ha
                   | unfold im_unu; rewrite Hh; exact Lp ].
      - exists Mj; [ exact HMj | unfold im_ref; rewrite Hh; reflexivity | unfold grp_adm; rewrite HMj, Hh; exact Hw
                   | unfold im_unu; rewrite Hh; exact Lp ].
    Qed.

    (** The type of an argument of a shape after related domains, at a base
        whose fresh variables are related to those at [ups]: it is defined. *)
    Lemma shape_type_exists : forall ua m Mm c gs1 t0 gs2 nsu ns wsu ws,
        ind_member D m = Some Mm -> ind_con Mm c = Some (gs1 ++ ca_rec t0 :: gs2) ->
        (exists r, ⟦mref ptyp_mem t0 of p ua ⟧ gc_deps ⍮ gc_stack ↘ r) ->
        (forall ys ys', tele_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) (ptyp_doms t0) ys ys' ->
           rel_evals (ptyp_ps t0) (env_args nil (ups ++ nsu ++ wsu ++ ys)) (env_args nil (ua ++ ns ++ ws ++ ys'))
             (ntele_rel D nr (ptyp_mem t0))) ->
        (forall j B ys ys', List.nth_error (ptyp_doms t0) j = Some B ->
           tele_prefix_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) j ys ys' ->
           rel_dom_apps B (env_args nil (ups ++ nsu ++ wsu ++ ys)) (env_args nil (ua ++ ns ++ ws ++ ys'))
             (dr m (nsu ++ wsu ++ ys) B)) ->
        forall k ysu ys, k <= List.length (ptyp_doms t0) ->
          tele_prefix_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) k ysu ys ->
          exists a, ⟦shty ptyp_skip k t0 of p ua ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ua ++ ns ++ ws ++ ys) ↘ a.
    Proof.
      intros * HM Hc [[[pc km] pre] Em] HR HD k ysu ys Hk Hy.
      destruct (Nat.eq_dec k (List.length (ptyp_doms t0))) as [-> | Hne].
      - rewrite ptyp_skip_end.
        assert (Hyf : tele_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) (ptyp_doms t0) ysu ys)
          by (destruct Hy as [Hyl Hya]; split; [ exact Hyl | exact Hya ]).
        destruct (HR _ _ Hyf) as [bs bs' _ E' _].
        eexists; econstructor; [ exact E' | exact Em ].
      - destruct (ptyp_skip_lt k t0 ltac:(lia)) as (B & HB & Hs); rewrite Hs.
        destruct (HD _ _ _ _ HB Hy) as [b b' _ Eb' _].
        eexists; econstructor; exact Eb'.
    Qed.

    (** A neutral of the type of an argument of a shape, at two bases
        admissible at the fresh variables, after fresh prefixes [ns1 ++ ws1]
        and [ns2 ++ ws2] related to the ones at [ups] ([nsu ++ wsu]) and
        related domains [ys1] and [ys2]: related by the shape, each side at
        its own base.  At the end of the shape, the index is admissible at
        the element's own prefix ([okr_at]): through the index at [ups]'s
        fresh prefix, by the recursive-index field of the fresh
        admissibility ([HR1], [HR2]), and from there to [ups] at the
        element's prefix by [Hcd].  The shape ends in a declared member,
        whose neutrals the group relation has; the neutrals of a view's
        type are not part of this file yet. *)
    Lemma shape_neut : forall ua1 ua2 m Mm c gs1 t0 gs2 nsu ns1 ns2 wsu ws1 ws2,
        adm_fresh p D ups nr ar dr ua1 -> adm_fresh p D ups nr ar dr ua2 ->
        List.length ua1 = ind_nu D -> List.length ua2 = ind_nu D ->
        ind_member D m = Some Mm -> ind_con Mm c = Some (gs1 ++ ca_rec t0 :: gs2) ->
        (exists r, ⟦mref ptyp_mem t0 of p ua1 ⟧ gc_deps ⍮ gc_stack ↘ r) ->
        (exists r, ⟦mref ptyp_mem t0 of p ua2 ⟧ gc_deps ⍮ gc_stack ↘ r) ->
        tele_rel (nr m) (List.rev (im_nparams Mm)) nsu ns1 -> tele_rel (nr m) (List.rev (im_nparams Mm)) nsu ns2 ->
        tele_prefix_rel (ar m nsu c) (List.length (cargs_nonrec gs1)) wsu ws1 ->
        tele_prefix_rel (ar m nsu c) (List.length (cargs_nonrec gs1)) wsu ws2 ->
        (forall ys ys', tele_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) (ptyp_doms t0) ys ys' ->
           rel_evals (ptyp_ps t0) (env_args nil (ups ++ nsu ++ wsu ++ ys)) (env_args nil (ua1 ++ ns1 ++ ws1 ++ ys'))
             (ntele_rel D nr (ptyp_mem t0))) ->
        (forall ys ys', tele_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) (ptyp_doms t0) ys ys' ->
           rel_evals (ptyp_ps t0) (env_args nil (ups ++ nsu ++ wsu ++ ys)) (env_args nil (ua2 ++ ns2 ++ ws2 ++ ys'))
             (ntele_rel D nr (ptyp_mem t0))) ->
        (forall j B ys ys', List.nth_error (ptyp_doms t0) j = Some B ->
           tele_prefix_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) j ys ys' ->
           rel_dom_apps B (env_args nil (ups ++ nsu ++ wsu ++ ys)) (env_args nil (ua1 ++ ns1 ++ ws1 ++ ys'))
             (dr m (nsu ++ wsu ++ ys) B)) ->
        (forall j B ys ys', List.nth_error (ptyp_doms t0) j = Some B ->
           tele_prefix_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) j ys ys' ->
           rel_dom_apps B (env_args nil (ups ++ nsu ++ wsu ++ ys)) (env_args nil (ua2 ++ ns2 ++ ws2 ++ ys'))
             (dr m (nsu ++ wsu ++ ys) B)) ->
        forall n k ysu ys1 ys2 a1 a2 e e', k + n = List.length (ptyp_doms t0) ->
          tele_prefix_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) k ysu ys1 ->
          tele_prefix_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) k ysu ys2 ->
          ⟦shty ptyp_skip k t0 of p ua1 ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ua1 ++ ns1 ++ ws1 ++ ys1) ↘ a1 ->
          ⟦shty ptyp_skip k t0 of p ua2 ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ua2 ++ ns2 ++ ws2 ++ ys2) ↘ a2 ->
          Dom e ≈ e' ∈ per_bot ->
          rec_arg_rel p D (grp_adm p D ups nr ar dr) (okr_at D ups nr) nr ar dr m ua1 ua2
            (ns1 ++ ws1 ++ ys1) (ns2 ++ ws2 ++ ys2) (ptyp_skip k t0) (⇑ a1 e) (⇑ a2 e').
    Proof.
      intros ua1 ua2 m Mm c gs1 t0 gs2 nsu ns1 ns2 wsu ws1 ws2 Ha1 Ha2 L1 L2 HM Hc Hme1 Hme2
        Hn1 Hn2 Hw1 Hw2 HR1 HR2 HD1 HD2.
      pose proof (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tsym.
      pose proof (nparams_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as ttrans.
      pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl.
      pose proof (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl_r.
      pose proof (ntele_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as ntsym.
      pose proof (ntele_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as nttrans.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
        by (rewrite cargs_nonrec_app, List.length_app; lia).
      pose proof (trefl _ _ HM _ _ Hn1) as Huu.
      pose proof (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM nsu c _ Huu Hc _ _ _ HK Hw1)
        as Hwuu.
      (** A side's prefix seen from that side: its relation to [ups]'s, in
          the other direction. *)
      assert (Hside : forall nsi wsi ysi k, tele_rel (nr m) (List.rev (im_nparams Mm)) nsu nsi ->
                 tele_prefix_rel (ar m nsu c) (List.length (cargs_nonrec gs1)) wsu wsi ->
                 k <= List.length (ptyp_doms t0) ->
                 forall ysu, tele_prefix_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) k ysu ysi ->
                 tele_rel (nr m) (List.rev (im_nparams Mm)) nsi nsu /\
                 tele_prefix_rel (ar m nsi c) (List.length (cargs_nonrec gs1)) wsi wsu /\
                 tele_prefix_rel (shape_doms_rel (dr m) nsi wsi (ptyp_doms t0)) k ysi ysu).
      { intros nsi wsi ysi k Hni Hwi Hk ysu Hyi.
        pose proof (tsym _ _ HM _ _ Hni) as Hin.
        assert (Hwi' : tele_prefix_rel (ar m nsi c) (List.length (cargs_nonrec gs1)) wsi wsu).
        { eapply (args_prefix_rel_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM); [ exact Hni | exact Hc | exact HK |].
          eapply (args_prefix_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM); [ exact Huu | exact Hc | exact HK | exact Hwi ]. }
        split; [ exact Hin | split; [ exact Hwi' |] ].
        eapply (doms_rel_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM); [ exact Hni | exact Hc | reflexivity | exact Hwi | exact Hk |].
        eapply (doms_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM nsu c _ gs1 t0 gs2 wsu Huu Hc eq_refl Hwuu);
          [ exact Hk | exact Hyi ]. }
      induction n as [| n IH]; intros k ysu ys1 ys2 a1 a2 e e' Hkn Hy1 Hy2 E1 E2 He.
      - destruct (ptyp_skip k t0) as [j Ps | B t] eqn:Hs.
        + (** The end of the shape. *)
          destruct (ptyp_skip_self _ _ _ _ Hs) as (Hkd & Hj & HPs).
          inversion E1 as [Ps0 ρ0 bs1 j0 pc1 k1 pre1 ? ? Ebs1 Em1 | ]; subst.
          inversion E2 as [Ps0 ρ0 bs2 j0 pc2 k2 pre2 ? ? Ebs2 Em2 | ]; subst.
          destruct (mref_at_end_adm ua1 Ha1 L1 _ _ _ _ Em1) as [Mj HMj Href1 Hadm1 Hlen1].
          destruct (mref_at_end_adm ua2 Ha2 L2 _ _ _ _ Em2) as [Mj' HMj' Href2 Hadm2 Hlen2].
          rewrite HMj in HMj'; injection HMj' as <-; rewrite Href1 in Href2; injection Href2 as <- <-.
          assert (Hyf1 : tele_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) (ptyp_doms t0) ysu ys1)
            by (destruct Hy1 as [Hyl Hya]; split; [ lia | exact Hya ]).
          assert (Hyf2 : tele_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) (ptyp_doms t0) ysu ys2)
            by (destruct Hy2 as [Hyl Hya]; split; [ lia | exact Hya ]).
          destruct (HR1 _ _ Hyf1) as [b0 b1 F0 F1 R1].
          destruct (HR2 _ _ Hyf2) as [b0' b2 F0' F2 R2].
          pose proof (functional_eval_exps' _ _ _ _ F0 F0') as <-.
          pose proof (functional_eval_exps' _ _ _ _ F1 Ebs1) as <-.
          pose proof (functional_eval_exps' _ _ _ _ F2 Ebs2) as <-.
          (** Each index admissible at its element's own prefix. *)
          assert (Hokr : forall nsi wsi ysi bsi, tele_rel (nr m) (List.rev (im_nparams Mm)) nsu nsi ->
                     tele_prefix_rel (ar m nsu c) (List.length (cargs_nonrec gs1)) wsu wsi ->
                     tele_prefix_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) k ysu ysi ->
                     ntele_rel D nr (ptyp_mem t0) b0 bsi ->
                     okr_at D ups nr (ptyp_mem t0) (nsi ++ wsi ++ ysi) (ptyp_ps t0) bsi).
          { intros nsi wsi ysi bsi Hni Hwi Hyi Rb.
            destruct (Hside nsi wsi ysi k Hni Hwi ltac:(lia) ysu Hyi) as (Hin & Hwi' & Hyi').
            assert (Hyif : tele_rel (shape_doms_rel (dr m) nsi wsi (ptyp_doms t0)) (ptyp_doms t0) ysi ysu)
              by (destruct Hyi' as [Hyl Hya]; split; [ lia | exact Hya ]).
            destruct (adm_rec_params _ _ _ _ _ _ Hcd m Mm nsi nsu c _ gs1 t0 gs2 wsi wsu ysi ysu HM Hin Hc eq_refl Hwi' Hyif)
              as [i1 i0 G1 G0 Ri].
            pose proof (functional_eval_exps' _ _ _ _ G0 F0) as ->.
            exists i1; [ exact G1 | exact (nttrans _ _ _ _ Ri Rb) ]. }
          pose proof (nttrans _ _ _ _ (ntsym _ _ _ R1) R2) as R12.
          destruct (ntele_rel_member p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ R12) as (Mj' & HMj' & H12).
          rewrite HMj in HMj'; injection HMj' as <-.
          pose proof H12 as Hl12; rewrite tele_rel_iff in Hl12; destruct Hl12 as (Lb1 & Lb2 & _).
          rewrite List.length_rev in Lb1, Lb2.
          econstructor; [ exact Ebs1 | exact Ebs2 | exact (Hokr _ _ _ _ Hn1 Hw1 Hy1 R1) | exact (Hokr _ _ _ _ Hn2 Hw2 Hy2 R2) |].
          eapply ind_rel_neut; [ exact HMj | exact Href1 | exact H12 | | | | | | | exact He ].
          * rewrite List.length_app, Hlen1; unfold im_np, im_nn; lia.
          * rewrite List.length_app, Hlen2; unfold im_np, im_nn; lia.
          * rewrite firstn_app_exact by exact Hlen1; exact Hadm1.
          * rewrite firstn_app_exact by exact Hlen2; exact Hadm2.
          * rewrite skipn_app_exact by exact Hlen1; exact (trefl _ _ HMj _ _ H12).
          * rewrite skipn_app_exact by exact Hlen2; exact (trefl_r _ _ HMj _ _ H12).
        + destruct (ptyp_skip_pi _ _ _ _ Hs) as [HB _].
          assert (k < List.length (ptyp_doms t0)) by (apply List.nth_error_Some; congruence); lia.
      - destruct (ptyp_skip k t0) as [j Ps | B t] eqn:Hs.
        + destruct (ptyp_skip_self _ _ _ _ Hs) as (Hkd & _ & _); lia.
        + destruct (ptyp_skip_pi _ _ _ _ Hs) as [HB Hs'].
          assert (Hkl : k < List.length (ptyp_doms t0)) by (apply List.nth_error_Some; congruence).
          inversion E1 as [| B0 ρ0 b1 t1 ? ? Eb1]; subst.
          inversion E2 as [| B0 ρ0 b2 t1 ? ? Eb2]; subst.
          destruct (HD1 _ _ _ _ HB Hy1) as [bu b1' Ebu Eb1' Htop1].
          destruct (HD2 _ _ _ _ HB Hy2) as [bu' b2' Ebu' Eb2' Htop2].
          pose proof (functional_eval_exp _ _ _ _ Ebu Ebu') as <-.
          pose proof (functional_eval_exp _ _ _ _ Eb1 Eb1') as <-.
          pose proof (functional_eval_exp _ _ _ _ Eb2 Eb2') as <-.
          pose proof (doms_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM nsu c _ gs1 t0 gs2 wsu Huu Hc eq_refl
                        Hwuu k ysu ys1 ltac:(lia) Hy1) as Hyuu.
          pose proof (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Huu Hc eq_refl Hwuu HB Hyuu) as HPd.
          pose proof (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hn1 Hc eq_refl Hw1 HB Hy1) as HI1.
          constructor; intros c0 c0' Hcc.
          (** The argument of the domain, at [ups]'s prefix. *)
          apply (proj2 (HI1 _ _)) in Hcc.
          assert (Hcc0 : dr m (nsu ++ wsu ++ ysu) B c0 c0) by (etransitivity; [ exact Hcc | symmetry; exact Hcc ]).
          assert (Hy1' : tele_prefix_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) (S k) (ysu ++ c0 :: nil) (ys1 ++ c0 :: nil))
            by (apply tele_prefix_rel_snoc; [ exact Hy1 | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hcc0 ]).
          assert (Hy2' : tele_prefix_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) (S k) (ysu ++ c0 :: nil) (ys2 ++ c0' :: nil))
            by (apply tele_prefix_rel_snoc; [ exact Hy2 | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hcc ]).
          destruct (shape_type_exists ua1 m Mm c gs1 t0 gs2 nsu ns1 wsu ws1 HM Hc Hme1 HR1 HD1 (S k) _ _ ltac:(lia) Hy1')
            as [a1' Ea1'].
          destruct (shape_type_exists ua2 m Mm c gs1 t0 gs2 nsu ns2 wsu ws2 HM Hc Hme2 HR2 HD2 (S k) _ _ ltac:(lia) Hy2')
            as [a2' Ea2'].
          change (ptyp_skip (S k) t0) with (ptyp_skip (S k) t0) in E2 |- *.
          econstructor; [ eapply eval_app_neut, eval_fam_cod_shfam; rewrite <- env_args_snoc3; exact Ea1'
                        | eapply eval_app_neut, eval_fam_cod_shfam; rewrite <- env_args_snoc3; exact Ea2' |].
          replace ((ns1 ++ ws1 ++ ys1) ++ c0 :: nil) with (ns1 ++ ws1 ++ (ys1 ++ c0 :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
          replace ((ns2 ++ ws2 ++ ys2) ++ c0' :: nil) with (ns2 ++ ws2 ++ (ys2 ++ c0' :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
          apply (IH (S k) _ _ _ _ _ _ _ ltac:(lia) Hy1' Hy2'); [ exact Ea1' | exact Ea2' |].
          apply per_bot_app; [ exact He |].
          exact (per_top_trans' _ _ _ (per_top_sym' _ _ (Htop1 _ _ Hcc0)) (Htop2 _ _ Hcc)).
    Qed.
    (** A neutral of the type the container's evaluation gives at a
        position the group's member [v] takes as recursive, on two sides
        whose fresh variables are related to the reference ones
        ([vshape_rel], the reference value [a0] shared): related by the
        shape, at the type's uniform parameters [ups] on both sides. *)
    Lemma vshape_neut : forall v Mv c gs1 t0 gs2 nsu ns1 ns2 wvu ws1 ws2 (Q1 Q2 : nat -> qname -> nat -> list domain -> Prop),
        ind_member D v = Some Mv -> ind_con Mv c = Some (gs1 ++ ca_rec t0 :: gs2) ->
        tele_rel (nr v) (List.rev (im_nparams Mv)) nsu ns1 -> tele_rel (nr v) (List.rev (im_nparams Mv)) nsu ns2 ->
        tele_prefix_rel (ar v nsu c) (List.length (cargs_nonrec gs1)) wvu ws1 ->
        tele_prefix_rel (ar v nsu c) (List.length (cargs_nonrec gs1)) wvu ws2 ->
        (forall j hd k py, Q1 j hd k py -> end_adm j hd k py) -> (forall j hd k py, Q2 j hd k py -> end_adm j hd k py) ->
        forall n kk ysu ys1 ys2 a0 a1 a2 e e', kk + n = List.length (ptyp_doms t0) ->
          tele_prefix_rel (shape_doms_rel (dr v) nsu wvu (ptyp_doms t0)) kk ysu ys1 ->
          tele_prefix_rel (shape_doms_rel (dr v) nsu wvu (ptyp_doms t0)) kk ysu ys2 ->
          vshape_rel p D ups nr (dr v) Q1 (nsu ++ wvu ++ ysu) (ptyp_skip kk t0) a0 a1 ->
          vshape_rel p D ups nr (dr v) Q2 (nsu ++ wvu ++ ysu) (ptyp_skip kk t0) a0 a2 ->
          Dom e ≈ e' ∈ per_bot ->
          rec_arg_rel p D (grp_adm p D ups nr ar dr) (okr_at D ups nr) nr ar dr v ups ups
            (ns1 ++ ws1 ++ ys1) (ns2 ++ ws2 ++ ys2) (ptyp_skip kk t0) (⇑ a1 e) (⇑ a2 e').
    Proof.
      intros v Mv c gs1 t0 gs2 nsu ns1 ns2 wvu ws1 ws2 Q1 Q2 HM Hc Hn1 Hn2 Hw1 Hw2 HQ1 HQ2.
      pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl.
      pose proof (ntele_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as ntsym.
      pose proof (ntele_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as nttrans.
      pose proof (ntele_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as ntrefl.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
        by (rewrite cargs_nonrec_app, List.length_app; lia).
      pose proof (trefl _ _ HM _ _ Hn1) as Huu.
      pose proof (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI v Mv HM nsu c _ Huu Hc _ _ _ HK Hw1) as Hwuu.
      induction n as [| n IH]; intros kk ysu ys1 ys2 a0 a1 a2 e e' Hkn Hy1 Hy2 V1 V2 He.
      - rewrite Nat.add_0_r in Hkn; subst kk; rewrite ptyp_skip_end in V1, V2 |- *.
        inversion V1 as [Ps pre bs j hd k py1 i0 i1 pu Eb HQ R0 R1 | ]; subst.
        inversion V2 as [Ps pre bs2 j hd2 k2 py2 i02 i2 pu2 Eb2 HQ' R02 R2 | ]; subst.
        pose proof (functional_eval_exps' _ _ _ _ Eb Eb2) as <-.
        destruct (HQ1 _ _ _ _ HQ) as [Mj HMj Href Hadm1 Hlen1].
        destruct (HQ2 _ _ _ _ HQ') as [Mj' HMj' Href' Hadm2 Hlen2].
        rewrite HMj in HMj'; injection HMj' as <-.
        assert (Hyf1 : tele_rel (shape_doms_rel (dr v) nsu wvu (ptyp_doms t0)) (ptyp_doms t0) ysu ys1)
          by (destruct Hy1 as [Hyl Hya]; split; [ exact Hyl | exact Hya ]).
        assert (Hyf2 : tele_rel (shape_doms_rel (dr v) nsu wvu (ptyp_doms t0)) (ptyp_doms t0) ysu ys2)
          by (destruct Hy2 as [Hyl Hya]; split; [ exact Hyl | exact Hya ]).
        destruct (adm_rec_params _ _ _ _ _ _ Hcd v Mv nsu ns1 c _ gs1 t0 gs2 wvu ws1 ysu ys1 HM Hn1 Hc eq_refl Hw1 Hyf1)
          as [b0 b1 F0 F1 Rb1].
        destruct (adm_rec_params _ _ _ _ _ _ Hcd v Mv nsu ns2 c _ gs1 t0 gs2 wvu ws2 ysu ys2 HM Hn2 Hc eq_refl Hw2 Hyf2)
          as [b0' b2 F0' F2 Rb2].
        pose proof (functional_eval_exps' _ _ _ _ F0 Eb) as ->.
        pose proof (functional_eval_exps' _ _ _ _ F0' Eb) as ->.
        destruct (ntele_rel_member p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ R1) as (Mj0 & HMj0 & Hl1).
        rewrite HMj in HMj0; injection HMj0 as <-.
        destruct (ntele_rel_member p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ R2) as (Mj0 & HMj0 & Hl2).
        rewrite HMj in HMj0; injection HMj0 as <-.
        pose proof Hl1 as L1; rewrite tele_rel_iff in L1; destruct L1 as (_ & L1 & _).
        pose proof Hl2 as L2; rewrite tele_rel_iff in L2; destruct L2 as (_ & L2 & _).
        rewrite List.length_rev in L1, L2.
        pose proof (nttrans _ _ _ _ (ntsym _ _ _ Rb1) Rb2) as R12.
        destruct (ntele_rel_member p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ R12) as (Mj0 & HMj0 & H12).
        rewrite HMj in HMj0; injection HMj0 as <-.
        destruct (ntele_rel_member p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ (nttrans _ _ _ _ (ntsym _ _ _ Rb1) R1))
          as (Mj0 & HMj0 & H1i).
        rewrite HMj in HMj0; injection HMj0 as <-.
        destruct (ntele_rel_member p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ (nttrans _ _ _ _ (ntsym _ _ _ Rb2) R2))
          as (Mj0 & HMj0 & H2i).
        rewrite HMj in HMj0; injection HMj0 as <-.
        econstructor; [ exact F1 | exact F2 | exists b1; [ exact F1 | exact (ntrefl _ _ _ Rb1) ]
                      | exists b2; [ exact F2 | exact (ntrefl _ _ _ Rb2) ] |].
        eapply ind_rel_neut; [ exact HMj | exact Href | exact H12 | | | | | | | exact He ].
        + rewrite List.length_app, Hlen1; unfold im_nn; lia.
        + rewrite List.length_app, Hlen2; unfold im_nn; lia.
        + rewrite firstn_app_exact by exact Hlen1; exact Hadm1.
        + rewrite firstn_app_exact by exact Hlen2; exact Hadm2.
        + rewrite skipn_app_exact by exact Hlen1; exact H1i.
        + rewrite skipn_app_exact by exact Hlen2; exact H2i.
      - destruct (ptyp_skip_lt kk t0 ltac:(lia)) as (B & HB & Hs); rewrite Hs in V1, V2 |- *.
        remember (ptyp_skip (S kk) t0) as t eqn:Ht.
        inversion V1 as [| pre1 B1 b0 b1 F0 ρ0 F1 ρ1 t1 Htop1 Ex01 Ex1 Hst1]; subst.
        inversion V2 as [| pre2 B2 b0' b2 F0' ρ0' F2 ρ2 t2 Htop2 Ex02 Ex2 Hst2]; subst.
        (** The side's prefixes against the reference one. *)
        assert (Hside : forall nsi wsi ysi, tele_rel (nr v) (List.rev (im_nparams Mv)) nsu nsi ->
                   tele_prefix_rel (ar v nsu c) (List.length (cargs_nonrec gs1)) wvu wsi ->
                   tele_prefix_rel (shape_doms_rel (dr v) nsu wvu (ptyp_doms t0)) kk ysu ysi ->
                   (dr v (nsu ++ wvu ++ ysu) B <~> dr v (nsi ++ wsi ++ ysi) B))
          by (intros; eapply HdI; [ exact HM | eassumption | exact Hc | reflexivity | eassumption | exact HB | eassumption ]).
        pose proof (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Huu Hc eq_refl Hwuu HB
                      (doms_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI v Mv HM nsu c _ gs1 t0 gs2 wvu Huu Hc eq_refl
                         Hwuu kk ysu ys1 ltac:(lia) Hy1)) as HPd.
        constructor; intros c1 c2 Hcc.
        apply (proj2 (Hside _ _ _ Hn1 Hw1 Hy1 _ _)) in Hcc.
        assert (Hcc0 : dr v (nsu ++ wvu ++ ysu) B c1 c1) by (etransitivity; [ exact Hcc | symmetry; exact Hcc ]).
        destruct (Ex01 _ _ Hcc0) as [a01 E01]; destruct (Ex1 _ _ Hcc0) as [a1' E1].
        destruct (Ex2 _ _ Hcc) as [a2' E2].
        pose proof (Hst1 _ _ _ _ Hcc0 E01 E1) as W1.
        pose proof (Hst2 _ _ _ _ Hcc E01 E2) as W2.
        econstructor; [ eapply eval_app_neut; exact E1 | eapply eval_app_neut; exact E2 |].
        replace ((ns1 ++ ws1 ++ ys1) ++ c1 :: nil) with (ns1 ++ ws1 ++ (ys1 ++ c1 :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
        replace ((ns2 ++ ws2 ++ ys2) ++ c2 :: nil) with (ns2 ++ ws2 ++ (ys2 ++ c2 :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
        rewrite <- !List.app_assoc in W1, W2.
        apply (IH (S kk) (ysu ++ c1 :: nil) _ _ a01 _ _ _ _ ltac:(lia));
          [ apply tele_prefix_rel_snoc; [ exact Hy1 | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hcc0 ]
          | apply tele_prefix_rel_snoc; [ exact Hy2 | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hcc ]
          | exact W1 | exact W2 |].
        apply per_bot_app; [ exact He |].
        exact (per_top_trans' _ _ _ (per_top_sym' _ _ (Htop1 _ _ Hcc0)) (Htop2 _ _ Hcc)).
    Qed.

    Lemma mref_fresh_exists : forall X j Mj, adm_fresh p D ups nr ar dr X -> ind_member D j = Some Mj ->
        exists r, ⟦mref j of p X ⟧ gc_deps ⍮ gc_stack ↘ r.
    Proof.
      intros X j Mj HX HMj; destruct (im_head Mj) as [pm | qc kc Is vm] eqn:Hh.
      - eexists; eapply eval_mref_decl; eassumption.
      - destruct (vfr_evals _ _ _ _ _ _ _ (afr_views _ _ _ _ _ _ _ HX) j Mj qc kc Is vm HMj Hh) as (cups & Y & _ & EY).
        eexists; eapply eval_mref_view; eassumption.
    Qed.

    (** The domains of two types of the same shape [t] of the member [k],
        after [pre]: at related arguments, read back alike, at every
        domain. *)
    Inductive shape_tops (k : nat) : list domain -> ptyp -> domain -> domain -> Prop :=
    | shape_tops_self : forall pre j Ps a a', shape_tops k pre (pt_self j Ps) a a'
    | shape_tops_pi : forall pre B t b ρ F b' ρ' F',
        (forall c c', dr k pre B c c' -> Dom ⇓ b c ≈ ⇓ b' c' ∈ per_top) ->
        (forall c c' x x', dr k pre B c c' ->
           ⟦ F ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↦ c ↘ x -> ⟦ F' ⟧ gc_deps ⍮ gc_stack ⍮ ρ' ↦ c' ↘ x' ->
           shape_tops k (pre ++ c :: nil) t x x') ->
        shape_tops k pre (pt_pi B t) (Πᵈ b ρ F) (Πᵈ b' ρ' F').

    (** The types of an argument of a shape at two bases, after prefixes
        related to the ones at [ups], as [shape_neut] has them. *)
    Lemma shape_tops_fresh : forall ua1 ua2 m Mm c gs1 t0 gs2 nsu ns1 ns2 wsu ws1 ws2,
        ind_member D m = Some Mm -> ind_con Mm c = Some (gs1 ++ ca_rec t0 :: gs2) ->
        (exists r, ⟦mref ptyp_mem t0 of p ua1 ⟧ gc_deps ⍮ gc_stack ↘ r) ->
        (exists r, ⟦mref ptyp_mem t0 of p ua2 ⟧ gc_deps ⍮ gc_stack ↘ r) ->
        tele_rel (nr m) (List.rev (im_nparams Mm)) nsu ns1 -> tele_rel (nr m) (List.rev (im_nparams Mm)) nsu ns2 ->
        tele_prefix_rel (ar m nsu c) (List.length (cargs_nonrec gs1)) wsu ws1 ->
        tele_prefix_rel (ar m nsu c) (List.length (cargs_nonrec gs1)) wsu ws2 ->
        (forall ys ys', tele_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) (ptyp_doms t0) ys ys' ->
           rel_evals (ptyp_ps t0) (env_args nil (ups ++ nsu ++ wsu ++ ys)) (env_args nil (ua1 ++ ns1 ++ ws1 ++ ys'))
             (ntele_rel D nr (ptyp_mem t0))) ->
        (forall ys ys', tele_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) (ptyp_doms t0) ys ys' ->
           rel_evals (ptyp_ps t0) (env_args nil (ups ++ nsu ++ wsu ++ ys)) (env_args nil (ua2 ++ ns2 ++ ws2 ++ ys'))
             (ntele_rel D nr (ptyp_mem t0))) ->
        (forall j B ys ys', List.nth_error (ptyp_doms t0) j = Some B ->
           tele_prefix_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) j ys ys' ->
           rel_dom_apps B (env_args nil (ups ++ nsu ++ wsu ++ ys)) (env_args nil (ua1 ++ ns1 ++ ws1 ++ ys'))
             (dr m (nsu ++ wsu ++ ys) B)) ->
        (forall j B ys ys', List.nth_error (ptyp_doms t0) j = Some B ->
           tele_prefix_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) j ys ys' ->
           rel_dom_apps B (env_args nil (ups ++ nsu ++ wsu ++ ys)) (env_args nil (ua2 ++ ns2 ++ ws2 ++ ys'))
             (dr m (nsu ++ wsu ++ ys) B)) ->
        forall n k ysu ys1 ys2 a1 a2, k + n = List.length (ptyp_doms t0) ->
          tele_prefix_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) k ysu ys1 ->
          tele_prefix_rel (shape_doms_rel (dr m) nsu wsu (ptyp_doms t0)) k ysu ys2 ->
          ⟦shty ptyp_skip k t0 of p ua1 ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ua1 ++ ns1 ++ ws1 ++ ys1) ↘ a1 ->
          ⟦shty ptyp_skip k t0 of p ua2 ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ua2 ++ ns2 ++ ws2 ++ ys2) ↘ a2 ->
          shape_tops m (ns1 ++ ws1 ++ ys1) (ptyp_skip k t0) a1 a2.
    Proof.
      intros ua1 ua2 m Mm c gs1 t0 gs2 nsu ns1 ns2 wsu ws1 ws2 HM Hc Hme1 Hme2 Hn1 Hn2 Hw1 Hw2 HR1 HR2 HD1 HD2.
      pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
        by (rewrite cargs_nonrec_app, List.length_app; lia).
      pose proof (trefl _ _ HM _ _ Hn1) as Huu.
      pose proof (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM nsu c _ Huu Hc _ _ _ HK Hw1)
        as Hwuu.
      induction n as [| n IH]; intros k ysu ys1 ys2 a1 a2 Hkn Hy1 Hy2 E1 E2.
      - rewrite Nat.add_0_r in Hkn; subst k; rewrite ptyp_skip_end; constructor.
      - destruct (ptyp_skip_lt k t0 ltac:(lia)) as (B & HB & Hs); rewrite Hs in E1, E2 |- *.
        inversion E1 as [| B0 ρ0 b1 t1 ? ? Eb1]; subst.
        inversion E2 as [| B0 ρ0 b2 t1 ? ? Eb2]; subst.
        destruct (HD1 _ _ _ _ HB Hy1) as [bu b1' Ebu Eb1' Htop1].
        destruct (HD2 _ _ _ _ HB Hy2) as [bu' b2' Ebu' Eb2' Htop2].
        pose proof (functional_eval_exp _ _ _ _ Ebu Ebu') as <-.
        pose proof (functional_eval_exp _ _ _ _ Eb1 Eb1') as <-.
        pose proof (functional_eval_exp _ _ _ _ Eb2 Eb2') as <-.
        pose proof (doms_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM nsu c _ gs1 t0 gs2 wsu Huu Hc eq_refl
                      Hwuu k ysu ys1 ltac:(lia) Hy1) as Hyuu.
        pose proof (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Huu Hc eq_refl Hwuu HB Hyuu) as HPd.
        pose proof (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hn1 Hc eq_refl Hw1 HB Hy1) as HI1.
        assert (Hcc0 : forall c0 c0', dr m (ns1 ++ ws1 ++ ys1) B c0 c0' ->
                   dr m (nsu ++ wsu ++ ysu) B c0 c0' /\ dr m (nsu ++ wsu ++ ysu) B c0 c0).
        { intros c0 c0' Hcc; apply (proj2 (HI1 _ _)) in Hcc; split; [ exact Hcc |].
          etransitivity; [ exact Hcc | symmetry; exact Hcc ]. }
        constructor.
        + intros c0 c0' Hcc; destruct (Hcc0 _ _ Hcc) as [Hu Huu0].
          exact (per_top_trans' _ _ _ (per_top_sym' _ _ (Htop1 _ _ Huu0)) (Htop2 _ _ Hu)).
        + intros c0 c0' x x' Hcc Ex Ex'; destruct (Hcc0 _ _ Hcc) as [Hu Huu0].
          apply fam_cod_shfam_inv in Ex, Ex'.
          rewrite <- env_args_snoc3 in Ex, Ex'.
          replace ((ns1 ++ ws1 ++ ys1) ++ c0 :: nil) with (ns1 ++ ws1 ++ (ys1 ++ c0 :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
          apply (IH (S k) (ysu ++ c0 :: nil) _ (ys2 ++ c0' :: nil) _ _ ltac:(lia));
            [ apply tele_prefix_rel_snoc; [ exact Hy1 | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Huu0 ]
            | apply tele_prefix_rel_snoc; [ exact Hy2 | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hu ]
            | exact Ex | exact Ex' ].
    Qed.

    (** The types the container's evaluation gives at a position this
        group's member [v] takes as recursive, on two sides, as
        [vshape_neut] has them. *)
    Lemma vshape_tops : forall v Mv c gs1 t0 gs2 nsu ns1 ns2 wvu ws1 ws2 (Q1 Q2 : nat -> qname -> nat -> list domain -> Prop),
        ind_member D v = Some Mv -> ind_con Mv c = Some (gs1 ++ ca_rec t0 :: gs2) ->
        tele_rel (nr v) (List.rev (im_nparams Mv)) nsu ns1 -> tele_rel (nr v) (List.rev (im_nparams Mv)) nsu ns2 ->
        tele_prefix_rel (ar v nsu c) (List.length (cargs_nonrec gs1)) wvu ws1 ->
        tele_prefix_rel (ar v nsu c) (List.length (cargs_nonrec gs1)) wvu ws2 ->
        forall n kk ysu ys1 ys2 a0 a1 a2, kk + n = List.length (ptyp_doms t0) ->
          tele_prefix_rel (shape_doms_rel (dr v) nsu wvu (ptyp_doms t0)) kk ysu ys1 ->
          tele_prefix_rel (shape_doms_rel (dr v) nsu wvu (ptyp_doms t0)) kk ysu ys2 ->
          vshape_rel p D ups nr (dr v) Q1 (nsu ++ wvu ++ ysu) (ptyp_skip kk t0) a0 a1 ->
          vshape_rel p D ups nr (dr v) Q2 (nsu ++ wvu ++ ysu) (ptyp_skip kk t0) a0 a2 ->
          shape_tops v (ns1 ++ ws1 ++ ys1) (ptyp_skip kk t0) a1 a2.
    Proof.
      intros v Mv c gs1 t0 gs2 nsu ns1 ns2 wvu ws1 ws2 Q1 Q2 HM Hc Hn1 Hn2 Hw1 Hw2.
      pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
        by (rewrite cargs_nonrec_app, List.length_app; lia).
      pose proof (trefl _ _ HM _ _ Hn1) as Huu.
      pose proof (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI v Mv HM nsu c _ Huu Hc _ _ _ HK Hw1) as Hwuu.
      induction n as [| n IH]; intros kk ysu ys1 ys2 a0 a1 a2 Hkn Hy1 Hy2 V1 V2.
      - rewrite Nat.add_0_r in Hkn; subst kk; rewrite ptyp_skip_end in V1, V2 |- *; constructor.
      - destruct (ptyp_skip_lt kk t0 ltac:(lia)) as (B & HB & Hs); rewrite Hs in V1, V2 |- *.
        inversion V1 as [| pre1 B1 b0 b1 F0 ρ0 F1 ρ1 t1 Htop1 Ex01 Ex1 Hst1]; subst.
        inversion V2 as [| pre2 B2 b0' b2 F0' ρ0' F2 ρ2 t2 Htop2 Ex02 Ex2 Hst2]; subst.
        pose proof (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Huu Hc eq_refl Hwuu HB
                      (doms_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI v Mv HM nsu c _ gs1 t0 gs2 wvu Huu Hc eq_refl
                         Hwuu kk ysu ys1 ltac:(lia) Hy1)) as HPd.
        pose proof (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hn1 Hc eq_refl Hw1 HB Hy1) as HI1.
        assert (Hcc0 : forall c1 c2, dr v (ns1 ++ ws1 ++ ys1) B c1 c2 ->
                   dr v (nsu ++ wvu ++ ysu) B c1 c2 /\ dr v (nsu ++ wvu ++ ysu) B c1 c1).
        { intros c1 c2 Hcc; apply (proj2 (HI1 _ _)) in Hcc; split; [ exact Hcc |].
          etransitivity; [ exact Hcc | symmetry; exact Hcc ]. }
        constructor.
        + intros c1 c2 Hcc; destruct (Hcc0 _ _ Hcc) as [Hu Huu0].
          exact (per_top_trans' _ _ _ (per_top_sym' _ _ (Htop1 _ _ Huu0)) (Htop2 _ _ Hu)).
        + intros c1 c2 x x' Hcc Ex Ex'; destruct (Hcc0 _ _ Hcc) as [Hu Huu0].
          destruct (Ex01 _ _ Huu0) as [a01 E01].
          pose proof (Hst1 _ _ _ _ Huu0 E01 Ex) as W1.
          pose proof (Hst2 _ _ _ _ Hu E01 Ex') as W2.
          rewrite <- !List.app_assoc in W1, W2.
          replace ((ns1 ++ ws1 ++ ys1) ++ c1 :: nil) with (ns1 ++ ws1 ++ (ys1 ++ c1 :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
          apply (IH (S kk) (ysu ++ c1 :: nil) _ (ys2 ++ c2 :: nil) a01 _ _ ltac:(lia));
            [ apply tele_prefix_rel_snoc; [ exact Hy1 | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Huu0 ]
            | apply tele_prefix_rel_snoc; [ exact Hy2 | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hu ]
            | exact W1 | exact W2 ].
    Qed.

    (** ** The Eliminator at Related Elements

        Two eliminators of the group, their blocks [Bksa] and [Bksb]
        closures in [ρa] and [ρb], the family [Rel j] of each member's
        motives.  Their motives are related at related elements, and their
        branches at related constructors and related recursive results. *)
    Section ElimRel.
      Variable (i : uidx) (ρa ρb : env) (Bksa Bksb : list eblock).
      Variable (Rel : nat -> list domain -> domain -> list domain -> domain -> relation domain).
      Hypothesis (HbA : forall j Mj, ind_member D j = Some Mj -> exists b, List.nth_error Bksa j = Some b)
        (HbB : forall j Mj, ind_member D j = Some Mj -> exists b, List.nth_error Bksb j = Some b).
      Hypothesis (HnmA : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bksa j = Some b -> eb_nm b = S (im_nn Mj))
        (HnmB : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bksb j = Some b -> eb_nm b = S (im_nn Mj)).
      Hypothesis (HnaA : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bksa j = Some b -> brs_names (im_cons Mj) (eb_brs b))
        (HnaB : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bksb j = Some b -> brs_names (im_cons Mj) (eb_brs b)).
      Hypothesis (HarA : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bksa j = Some b ->
                    ind_con Mj c = Some gs -> In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec gs)%nat)
        (HarB : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bksb j = Some b ->
                    ind_con Mj c = Some gs -> In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec gs)%nat).
      Hypothesis (Hnd : forall j Mj, ind_member D j = Some Mj -> List.NoDup (List.map fst (im_cons Mj))).
      (** The motives, at the two sides' indices of related elements. *)
      Hypothesis (Hmot : forall j Mj ba bb u u' ns ns' m m', ind_member D j = Some Mj ->
                    List.nth_error Bksa j = Some ba -> List.nth_error Bksb j = Some bb ->
                    grp_rel p D ups nr ar dr j u u' ns ns' m m' ->
                    exists a a', ⟦ eb_motive ba ⟧ env_args ρa (ns ++ m :: nil) ↘ a /\
                      ⟦ eb_motive bb ⟧ env_args ρb (ns' ++ m' :: nil) ↘ a' /\
                      DF a ≈ a' ∈ per_univ_elem i ↘ Rel j ns m ns' m').

      (** The recursive results of recursive arguments [v] and [v'] of shape
          [t] of the member [k], after the values [pre] and [pre'] of the
          shape's components on each side, the bases [u] and [u'] apart: at
          the end, related at [Rel] at the parameters the shape evaluates to
          on each side, and at a domain, pointwise. *)
      Inductive rec_result_rel (k : nat) (u u' : list domain) :
          list domain -> list domain -> ptyp -> domain -> domain -> domain -> domain -> Prop :=
      | rec_result_self : forall pre pre' j Ps bs bs' v v' ih ih',
          ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (u ++ pre) ↘ bs ->
          ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (u' ++ pre') ↘ bs' ->
          Rel j bs v bs' v' ih ih' ->
          rec_result_rel k u u' pre pre' (pt_self j Ps) v v' ih ih'
      | rec_result_pi : forall pre pre' B t v v' ih ih',
          (forall c c', dr k pre B c c' -> rec_result_app_rel k u u' (pre ++ c :: nil) (pre' ++ c' :: nil) t v c v' c' ih ih') ->
          rec_result_rel k u u' pre pre' (pt_pi B t) v v' ih ih'
      with rec_result_app_rel (k : nat) (u u' : list domain) :
          list domain -> list domain -> ptyp -> domain -> domain -> domain -> domain -> domain -> domain -> Prop :=
      | rec_result_app_mk : forall pre pre' t v c v' c' ih ih' fc fc' r r',
          $| v & c | gc_deps ⍮ gc_stack ↘ fc -> $| v' & c' | gc_deps ⍮ gc_stack ↘ fc' ->
          $| ih & c | gc_deps ⍮ gc_stack ↘ r -> $| ih' & c' | gc_deps ⍮ gc_stack ↘ r' ->
          rec_result_rel k u u' pre pre' t fc fc' r r' ->
          rec_result_app_rel k u u' pre pre' t v c v' c' ih ih'.

      (** The recursive results of related arguments, after the values
          [pre] and [pre'] of the non-uniform parameters and the
          non-recursive arguments before them on each side. *)
      Inductive rec_results_rel (k : nat) (u u' : list domain) :
          list domain -> list domain -> list carg -> list domain -> list domain -> list domain -> list domain -> Prop :=
      | rec_results_nil : forall pre pre', rec_results_rel k u u' pre pre' nil nil nil nil nil
      | rec_results_arg : forall pre pre' A gs v v' vs vs' ihs ihs',
          rec_results_rel k u u' (pre ++ v :: nil) (pre' ++ v' :: nil) gs vs vs' ihs ihs' ->
          rec_results_rel k u u' pre pre' (ca_arg A :: gs) (v :: vs) (v' :: vs') ihs ihs'
      | rec_results_rec : forall pre pre' t gs v v' vs vs' ih ih' ihs ihs',
          rec_result_rel k u u' pre pre' t v v' ih ih' ->
          rec_results_rel k u u' pre pre' gs vs vs' ihs ihs' ->
          rec_results_rel k u u' pre pre' (ca_rec t :: gs) (v :: vs) (v' :: vs') (ih :: ihs) (ih' :: ihs').

      (** The branches, at two related constructors and related recursive
          results. *)
      Hypothesis (Hbr : forall j Mj ba bb c gs n Ba Bb u u' bs bs' vs vs' ihs ihs' hd k', ind_member D j = Some Mj ->
                    List.nth_error Bksa j = Some ba -> List.nth_error Bksb j = Some bb -> ind_con Mj c = Some gs ->
                    brs_lookup (eb_brs ba) c = Some (n, Ba) -> brs_lookup (eb_brs bb) c = Some (n, Bb) ->
                    grp_rel p D ups nr ar dr j u u' (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs')
                      (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs' ++ vs')) ->
                    rec_results_rel j u u'
                      (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs') gs vs vs' ihs ihs' ->
                    exists r r', ⟦ Ba ⟧ env_args ρa (List.skipn (im_unu D Mj) bs ++ vs ++ ihs) ↘ r /\
                      ⟦ Bb ⟧ env_args ρb (List.skipn (im_unu D Mj) bs' ++ vs' ++ ihs') ↘ r' /\
                      Rel j (List.skipn (im_unu D Mj) bs) (d_con hd k' c (bs ++ vs))
                        (List.skipn (im_unu D Mj) bs') (d_con hd k' c (bs' ++ vs')) r r').

      (** *** The Family Is Invariant *)
      Lemma motive_rel_right : forall j Mj u1 u1' u2 u2' ns m ns1 m1 ns2 m2, ind_member D j = Some Mj ->
          grp_rel p D ups nr ar dr j u1 u1' ns ns1 m m1 -> grp_rel p D ups nr ar dr j u2 u2' ns ns2 m m2 ->
          (Rel j ns m ns1 m1 <~> Rel j ns m ns2 m2).
      Proof.
        intros * HM Hm1 Hm2.
        destruct (HbA _ _ HM) as [ba Ha]; destruct (HbB _ _ HM) as [bb Hb].
        destruct (Hmot _ _ _ _ _ _ _ _ _ _ HM Ha Hb Hm1) as (a & a1 & Ea & Ea1 & HR1).
        destruct (Hmot _ _ _ _ _ _ _ _ _ _ HM Ha Hb Hm2) as (b & a2 & Eb & Ea2 & HR2).
        pose proof (functional_eval_exp _ _ _ _ Ea Eb) as <-.
        eapply per_univ_elem_right_irrel; eassumption.
      Qed.

      Lemma motive_rel_left : forall j Mj u1 u1' u2 u2' ns1 m1 ns2 m2 ns' m', ind_member D j = Some Mj ->
          grp_rel p D ups nr ar dr j u1 u1' ns1 ns' m1 m' -> grp_rel p D ups nr ar dr j u2 u2' ns2 ns' m2 m' ->
          (Rel j ns1 m1 ns' m' <~> Rel j ns2 m2 ns' m').
      Proof.
        intros * HM Hm1 Hm2.
        destruct (HbA _ _ HM) as [ba Ha]; destruct (HbB _ _ HM) as [bb Hb].
        destruct (Hmot _ _ _ _ _ _ _ _ _ _ HM Ha Hb Hm1) as (a1 & a & Ea1 & Ea & HR1).
        destruct (Hmot _ _ _ _ _ _ _ _ _ _ HM Ha Hb Hm2) as (a2 & b & Ea2 & Eb & HR2).
        pose proof (functional_eval_exp _ _ _ _ Ea Eb) as <-.
        eapply per_univ_elem_left_irrel; eassumption.
      Qed.

      (** The family at related elements does not depend on the indices. *)
      Lemma motive_rel_move : forall j Mj u u' ns ns' m m' ns1 ns1', ind_member D j = Some Mj ->
          grp_rel p D ups nr ar dr j u u' ns ns' m m' ->
          tele_rel (nr j) (List.rev (im_nparams Mj)) ns ns1 -> tele_rel (nr j) (List.rev (im_nparams Mj)) ns' ns1' ->
          (Rel j ns m ns' m' <~> Rel j ns1 m ns1' m').
      Proof.
        intros * HM Hm H1 H1'.
        pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ H1) as H0.
        pose proof (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ HM Hm H0 H1') as Hmid.
        pose proof (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ HM Hm H1 H1') as Hm1.
        etransitivity; [ exact (motive_rel_right _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hmid)
                       | exact (motive_rel_left _ _ _ _ _ _ _ _ _ _ _ _ HM Hmid Hm1) ].
      Qed.

      (** The member of a group a member is at: the member itself, or the
          container's at a view. *)
      Lemma im_ref_target : forall j Mj hd k', ind_member D j = Some Mj -> im_ref p j Mj = (hd, k') ->
          exists Dq Mk, ind_lookup gc_deps gc_stack hd = Some Dq /\ ind_member Dq k' = Some Mk /\
            im_nn Mk = im_nn Mj /\ ind_nu Dq = im_unu D Mj.
      Proof.
        intros * HM Hr; unfold im_ref in Hr; destruct (im_head Mj) as [pm | qc kc Is vm] eqn:Hh; injection Hr as <- <-.
        - exists D, Mj; unfold im_unu; rewrite Hh; auto.
        - destruct (gta_views _ Hass j Mj qc kc Is vm HM Hh) as (Dq & Mc & Hq & HMc & Hnn & HIs).
          exists Dq, Mc; unfold im_unu; rewrite Hh; auto.
      Qed.

      (** A stuck eliminator at related neutrals of a member, when the stuck
          eliminators read back alike: related at the motive. *)
      Lemma neut_elim_rel : forall j Mj u u' ns ns' hd k' as1 as2 e e', ind_member D j = Some Mj ->
          grp_rel p D ups nr ar dr j u u' ns ns' (⇑ (d_ind hd k' as1) e) (⇑ (d_ind hd k' as2) e') ->
          Dom d_elim ρa Bksa p j as1 e ≈ d_elim ρb Bksb p j as2 e' ∈ per_bot ->
          exists r r', ⟦elim ⇑ (d_ind hd k' as1) e at j of p Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ r /\
            ⟦elim ⇑ (d_ind hd k' as2) e' at j of p Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ r' /\
            Rel j ns (⇑ (d_ind hd k' as1) e) ns' (⇑ (d_ind hd k' as2) e') r r'.
      Proof.
        intros * HM Hm Hb.
        pose proof Hm as Hm0.
        inversion Hm0 as [| j0 Mj0 hd0 k0 ns0 ns0' as1' as2' e0 e0' u0 u0' HM0 Hr Hn L1 L2 O1 O2 Hs1 Hs2 He]; subst.
        rewrite HM in HM0; injection HM0 as <-.
        destruct (im_ref_target _ _ _ _ HM Hr) as (Dq & Mk & Hq & HMk & Hnn & Hnu).
        destruct (HbA _ _ HM) as [ba Ha]; destruct (HbB _ _ HM) as [bb Hb'].
        pose proof (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hs1 Hs2) as Hm1.
        destruct (Hmot _ _ _ _ _ _ _ _ _ _ HM Ha Hb' Hm1) as (a & a' & Ea & Ea' & HR).
        exists (⇑ a (d_elim ρa Bksa p j as1 e)), (⇑ a' (d_elim ρb Bksb p j as2 e')); split; [| split ].
        - eapply eval_elim_neut; [ exact Hl | exact HM | exact Hr | exact Hq | exact HMk | | exact Ha
                                 | rewrite (HnmA _ _ _ HM Ha), Hnn; reflexivity | rewrite Hnu; exact Ea ].
          rewrite L1; unfold im_np; lia.
        - eapply eval_elim_neut; [ exact Hl | exact HM | exact Hr | exact Hq | exact HMk | | exact Hb'
                                 | rewrite (HnmB _ _ _ HM Hb'), Hnn; reflexivity | rewrite Hnu; exact Ea' ].
          rewrite L2; unfold im_np; lia.
        - apply (motive_rel_move _ _ _ _ _ _ _ _ _ _ HM Hm Hs1 Hs2).
          exact (per_bot_then_per_elem HR Hb).
      Qed.

      (** *** The Fresh Recursive Results

          A recursive argument, a neutral of the type of the shape [t'] the
          group read by the eliminator gives it (its own, or the
          container's), related by the shape [t] of this group: the types
          of its recursive results by the motives [As1] and [As2] of the
          blocks read are defined, and neutrals of them are related as
          recursive results, by the motive of the member [t] ends in. *)
      Lemma ih_fresh : forall t t' k u u' pre pre' pc1 X1 pc2 X2 ρ1 ρ2 a1 a2 e e' As1 As2,
          rec_arg_rel p D (grp_adm p D ups nr ar dr) (okr_at D ups nr) nr ar dr k u u' pre pre' t (⇑ a1 e) (⇑ a2 e') ->
          shape_tops k pre t a1 a2 -> ptyp_depth t' = ptyp_depth t ->
          ⟦shty t' of pc1 X1 ⟧ gc_deps ⍮ gc_stack ⍮ ρ1 ↘ a1 -> ⟦shty t' of pc2 X2 ⟧ gc_deps ⍮ gc_stack ⍮ ρ2 ↘ a2 ->
          (forall Mj, ind_member D (ptyp_mem t) = Some Mj -> List.length (ptyp_ps t') = im_nn Mj) ->
          (forall b, List.nth_error Bksa (ptyp_mem t) = Some b -> List.nth (ptyp_mem t') As1 a_True = eb_motive b) ->
          (forall b, List.nth_error Bksb (ptyp_mem t) = Some b -> List.nth (ptyp_mem t') As2 a_True = eb_motive b) ->
          exists h1 h2, ⟦ihty ⇑ a1 e of t' under ρa As1 ⟧ gc_deps ⍮ gc_stack ⍮ ρ1 ↘ h1 /\
            ⟦ihty ⇑ a2 e' of t' under ρb As2 ⟧ gc_deps ⍮ gc_stack ⍮ ρ2 ↘ h2 /\
            forall e2 e2', Dom e2 ≈ e2' ∈ per_bot ->
              rec_result_rel k u u' pre pre' t (⇑ a1 e) (⇑ a2 e') (⇑ h1 e2) (⇑ h2 e2').
      Proof.
        induction t as [j Ps | B t IH]; intros [j' Ps' | B' t'] * H Ht Hd E1 E2 Hpl HA1 HA2;
          unfold ptyp_depth in Hd; cbn in Hd; try discriminate.
        - (** The end: the motive of the member, at the neutral's own
              indices. *)
          inversion E1 as [Ps0 ρ0 bs1 j0 hd1 k1 pre1 ? ? Ebs1 Em1 |]; subst.
          inversion E2 as [Ps0 ρ0 bs2 j0 hd2 k2 pre2 ? ? Ebs2 Em2 |]; subst.
          destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (bs & bs' & Eb & Eb' & _ & _ & Hr).
          pose proof Hr as Hr0.
          inversion Hr0 as [| jx Mj hdx kx nsx nsx' as1 as2 ex ex' ux ux' HM Href Hn L1 L2 O1 O2 Hs1 Hs2 He]; subst.
          cbn in Hpl, HA1, HA2.
          assert (Lb1 : List.length bs1 = im_nn Mj) by (rewrite (eval_exps_length _ _ _ Ebs1); exact (Hpl _ HM)).
          assert (Lb2 : List.length bs2 = im_nn Mj) by (rewrite (eval_exps_length _ _ _ Ebs2); exact (Hpl _ HM)).
          rewrite List.length_app in L1, L2.
          rewrite skipn_app_exact in Hs1 by lia; rewrite skipn_app_exact in Hs2 by lia.
          destruct (HbA _ _ HM) as [ba Ha]; destruct (HbB _ _ HM) as [bb Hb].
          pose proof (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ HM Hr Hs1 Hs2) as Hm1.
          destruct (Hmot _ _ _ _ _ _ _ _ _ _ HM Ha Hb Hm1) as (h1 & h2 & Eh1 & Eh2 & HR).
          exists h1, h2; split; [| split ].
          + econstructor; [ exact Ebs1 | rewrite (HA1 _ Ha); exact Eh1 ].
          + econstructor; [ exact Ebs2 | rewrite (HA2 _ Hb); exact Eh2 ].
          + intros e2 e2' He2; econstructor; [ exact Eb | exact Eb' |].
            apply (motive_rel_move _ _ _ _ _ _ _ _ _ _ HM Hr Hs1 Hs2).
            exact (per_bot_then_per_elem HR He2).
        - (** Under a domain: the families at related arguments. *)
          inversion E1 as [| B0 ρ0 b1 t0 ? ? Eb1]; subst.
          inversion E2 as [| B0 ρ0 b2 t0 ? ? Eb2]; subst.
          inversion Ht as [| pre0 B0 t0 b0 ρ0 F0 b0' ρ0' F0' Htop Hnext]; subst.
          exists (Πᵈ b1 (nil ↦ d_ihfam ρa As1 ρ1 t' (⇑ (Πᵈ b1 (nil ↦ d_shfam pc1 X1 ρ1 t') fam_cod) e)) fam_cod),
            (Πᵈ b2 (nil ↦ d_ihfam ρb As2 ρ2 t' (⇑ (Πᵈ b2 (nil ↦ d_shfam pc2 X2 ρ2 t') fam_cod) e')) fam_cod).
          split; [ econstructor; exact Eb1 | split; [ econstructor; exact Eb2 |] ].
          intros e2 e2' He2; constructor; intros c c' Hcc.
          destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H c c' Hcc) as (r & r' & Ea & Ea' & Hr).
          inversion Ea; subst.
          match goal with Ex0 : ⟦ fam_cod ⟧ _ ⍮ _ ⍮ _ ↦ c ↘ _ |- _ => rename Ex0 into Ex end.
          inversion Ea'; subst.
          match goal with Ex0 : ⟦ fam_cod ⟧ _ ⍮ _ ⍮ _ ↦ c' ↘ _ |- _ => rename Ex0 into Ex' end.
          pose proof (fam_cod_shfam_inv _ _ _ _ _ _ Ex) as Sx.
          pose proof (fam_cod_shfam_inv _ _ _ _ _ _ Ex') as Sx'.
          destruct (IH t' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ As1 As2 Hr (Hnext _ _ _ _ Hcc Ex Ex') ltac:(unfold ptyp_depth; lia)
                      Sx Sx' Hpl HA1 HA2) as (h1 & h2 & I1 & I2 & HI).
          econstructor; [ exact Ea | exact Ea'
                        | eapply eval_app_neut, eval_fam_cod_ihfam; [ exact Ea | exact I1 ]
                        | eapply eval_app_neut, eval_fam_cod_ihfam; [ exact Ea' | exact I2 ] |].
          apply HI, per_bot_app; [ exact He2 | exact (Htop _ _ Hcc) ].
      Qed.

      (** A recursive argument the view nests through, a neutral related
          by the shape [t]: its recursive results by the eliminator are
          defined and related, when the stuck eliminators at the member [t]
          ends in read back alike. *)
      Lemma ih_neut_rel : forall t k u u' pre pre' a1 a2 e e',
          rec_arg_rel p D (grp_adm p D ups nr ar dr) (okr_at D ups nr) nr ar dr k u u' pre pre' t (⇑ a1 e) (⇑ a2 e') ->
          (forall Mj hd k' as1 as2 e1 e1' w w' ns ns', ind_member D (ptyp_mem t) = Some Mj ->
             grp_rel p D ups nr ar dr (ptyp_mem t) w w' ns ns' (⇑ (d_ind hd k' as1) e1) (⇑ (d_ind hd k' as2) e1') ->
             Dom d_elim ρa Bksa p (ptyp_mem t) as1 e1 ≈ d_elim ρb Bksb p (ptyp_mem t) as2 e1' ∈ per_bot) ->
          exists ih ih', ⟦ih ⇑ a1 e of t under p Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ ih /\
            ⟦ih ⇑ a2 e' of t under p Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ ih' /\
            rec_result_rel k u u' pre pre' t (⇑ a1 e) (⇑ a2 e') ih ih'.
      Proof.
        induction t as [j Ps | B t IH]; intros * H Hbot.
        - destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (bs & bs' & Eb & Eb' & _ & _ & Hr).
          pose proof Hr as Hr0.
          inversion Hr0 as [| jx Mj hdx kx nsx nsx' as1 as2 ex ex' ux ux' HM Href Hn L1 L2 O1 O2 Hs1 Hs2 He]; subst.
          destruct (neut_elim_rel _ _ _ _ _ _ _ _ _ _ _ _ HM Hr (Hbot _ _ _ _ _ _ _ _ _ _ _ HM Hr)) as (r & r' & Er & Er' & HR).
          exists r, r'; split; [ constructor; exact Er | split; [ constructor; exact Er' |] ].
          econstructor; [ exact Eb | exact Eb' | exact HR ].
        - exists (d_ihfn ρa Bksa p t (⇑ a1 e)), (d_ihfn ρb Bksb p t (⇑ a2 e')).
          split; [ constructor | split; [ constructor |] ].
          constructor; intros c c' Hcc.
          destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H c c' Hcc) as (r & r' & Ea & Ea' & Hr).
          inversion Ea; subst; inversion Ea'; subst.
          destruct (IH _ _ _ _ _ _ _ _ _ Hr Hbot) as (ih & ih' & I1 & I2 & HI).
          econstructor; [ exact Ea | exact Ea' | econstructor; [ exact Ea | exact I1 ] | econstructor; [ exact Ea' | exact I2 ] | exact HI ].
      Qed.

      (** *** Reading the Blocks of a Stuck Eliminator

          What the two readbacks of a stuck eliminator need of a branch:
          the constructor [c] of the member [Mi] of the group read (kinds
          [gs']), the branch's member [v] of this group (kinds [gs]), its
          fresh arguments and recursive results on each side, the
          constructor at them related at [v], with related recursive
          results. *)
      #[warnings="-cannot-define-projection"]
      Record brs_pair (s : nat) (pc : qname) (Xa Xb : list domain) (sel : option (list nat)) (v : nat) (Mv Mi : imember)
          (hd : qname) (k : nat) (prea preb nsa nsb ua ub : list domain) (c : String.string) (gs' gs : list carg) : Prop :=
        mk_brs_pair
        { bp_vsa : list domain
        ; bp_vsb : list domain
        ; bp_ihsa : list domain
        ; bp_ihsb : list domain
        ; bp_wa : list domain
        ; bp_wb : list domain
        ; bp_Fa : Fcargs gs' of pc Xa in gc_deps ⍮ gc_stack ⍮ env_args nil (Xa ++ nsa) ⍮ (s + im_nn Mi)%nat ↘ bp_vsa
        ; bp_Fb : Fcargs gs' of pc Xb in gc_deps ⍮ gc_stack ⍮ env_args nil (Xb ++ nsb) ⍮ (s + im_nn Mi)%nat ↘ bp_vsb
        ; bp_Ia : Fihs bp_vsa at gs' under ρa (motives_sel sel (blocks_motives Bksa))
            in gc_deps ⍮ gc_stack ⍮ env_args nil (Xa ++ nsa) ⍮ (s + im_nn Mi + List.length gs')%nat ↘ bp_ihsa
        ; bp_Ib : Fihs bp_vsb at gs' under ρb (motives_sel sel (blocks_motives Bksb))
            in gc_deps ⍮ gc_stack ⍮ env_args nil (Xb ++ nsb) ⍮ (s + im_nn Mi + List.length gs')%nat ↘ bp_ihsb
        ; bp_Wa : ⟦wihs bp_vsa of gs' gs with bp_ihsa under p Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ bp_wa
        ; bp_Wb : ⟦wihs bp_vsb of gs' gs with bp_ihsb under p Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ bp_wb
        ; bp_rel : grp_rel p D ups nr ar dr v ua ub nsa nsb (d_con hd k c (prea ++ nsa ++ bp_vsa)) (d_con hd k c (preb ++ nsb ++ bp_vsb))
        ; bp_recs : rec_results_rel v ua ub nsa nsb gs
            bp_vsa bp_vsb bp_wa bp_wb }.

      Lemma read_brs_rel : forall s pc Dq Xa Xb sel v Mv Mi hd k prea preb nsa nsb ua ub ba bb,
          ind_lookup gc_deps gc_stack pc = Some Dq -> ind_member D v = Some Mv ->
          List.nth_error Bksa v = Some ba -> List.nth_error Bksb v = Some bb -> im_nn Mv = im_nn Mi ->
          List.length prea = im_unu D Mv -> List.length preb = im_unu D Mv ->
          Ftele List.rev (im_nparams Mi) in gc_deps ⍮ gc_stack ⍮ env_args nil Xa ⍮ s ↘ nsa ->
          Ftele List.rev (im_nparams Mi) in gc_deps ⍮ gc_stack ⍮ env_args nil Xb ⍮ s ↘ nsb ->
          forall cs Bs1 Bs2,
          (forall c gs', List.In (c, gs') cs -> cargs_plen Dq gs' /\
             exists gs, ind_con Mv c = Some gs /\ List.length gs = List.length gs' /\
               brs_pair s pc Xa Xb sel v Mv Mi hd k prea preb nsa nsb ua ub c gs' gs) ->
          (forall c n B, List.In (c, n, B) Bs1 -> brs_lookup (eb_brs ba) c = Some (n, B) /\ List.In (c, n, B) (eb_brs ba)) ->
          (forall c n B, List.In (c, n, B) Bs2 -> brs_lookup (eb_brs bb) c = Some (n, B) /\ List.In (c, n, B) (eb_brs bb)) ->
          brs_names cs Bs1 -> brs_names cs Bs2 ->
          exists Bs', Rbrs Bs1 at cs of Mi (hd, k, prea) pc Xa from p Bksa sel Mv (eb_motive ba)
                        in gc_deps ⍮ gc_stack ⍮ ρa ⍮ s ↘ Bs' /\
            Rbrs Bs2 at cs of Mi (hd, k, preb) pc Xb from p Bksb sel Mv (eb_motive bb) in gc_deps ⍮ gc_stack ⍮ ρb ⍮ s ↘ Bs'.
      Proof.
        intros s pc Dq Xa Xb sel v Mv Mi hd k prea preb nsa nsb ua ub ba bb Hq HM Ha Hb Hnn La Lb Fa Fb.
        induction cs as [| [c gs'] cs IH]; intros [| [[c1 n1] B1] Bs1] [| [[c2 n2] B2] Bs2] Hcs HB1 HB2 Hn1 Hn2;
          cbn in Hn1, Hn2; try discriminate.
        - exists nbrs_nil; split; constructor.
        - injection Hn1 as <- Hn1; injection Hn2 as <- Hn2.
          destruct (Hcs c gs' ltac:(left; reflexivity)) as (Hpl & gs & Hc & Lg & BP).
          destruct (HB1 c n1 B1 ltac:(left; reflexivity)) as [HL1 HI1].
          destruct (HB2 c n2 B2 ltac:(left; reflexivity)) as [HL2 HI2].
          pose proof (HarA _ _ _ _ _ _ _ HM Ha Hc HI1) as Hn1e; pose proof (HarB _ _ _ _ _ _ _ HM Hb Hc HI2) as Hn2e.
          assert (n2 = n1) as -> by lia.
          destruct BP as [vsa vsb ihsa ihsb wa wb Ca Cb Ia Ib Wa Wb Rel0 Recs].
          pose proof Rel0 as Rel1; rewrite !List.app_assoc in Rel1.
          pose proof (Hbr v Mv ba bb c gs n1 B1 B2 ua ub (prea ++ nsa) (preb ++ nsb) vsa vsb wa wb hd k HM Ha Hb Hc HL1 HL2)
            as HB.
          rewrite !skipn_app_exact in HB by assumption.
          destruct (HB Rel1 Recs) as (r1 & r2 & Er1 & Er2 & Hrr).
          destruct (Hmot _ _ _ _ _ _ _ _ _ _ HM Ha Hb Rel0) as (t1 & t2 & T1 & T2 & HR).
          rewrite <- !List.app_assoc in Hrr.
          destruct (per_elem_then_per_top HR Hrr (s + (im_nn Mi + List.length gs' + cargs_nrec gs'))) as (B' & RB1 & RB2).
          destruct (IH Bs1 Bs2) as (Bs' & RBs1 & RBs2).
          { intros c' gs0 Hin; apply Hcs; right; exact Hin. }
          { intros c' n' Bx Hin; apply HB1; right; exact Hin. }
          { intros c' n' Bx Hin; apply HB2; right; exact Hin. }
          { exact Hn1. }
          { exact Hn2. }
          exists (nbrs_cons c (im_nn Mi + List.length gs' + cargs_nrec gs') B' Bs'); split.
          + eapply read_brs_cons; [ exact Hc | lia | reflexivity | exact Hq | exact Hpl | exact Fa | exact Ca | exact Ia | exact Wa
                                  | exact Er1 | exact T1 | exact RB1 | exact RBs1 ].
          + eapply read_brs_cons; [ exact Hc | lia | reflexivity | exact Hq | exact Hpl | exact Fb | exact Cb | exact Ib | exact Wb
                                  | exact Er2 | exact T2 | exact RB2 | exact RBs2 ].
      Qed.

      (** What the two readbacks need of a block: the one of the member
          [Mi] of the group read, the block of [elim_src sel i]: its type at
          the two sides' parameters, the fresh variables of its non-uniform
          parameters, the neutral at them related at the block's member, and
          each branch. *)
      #[warnings="-cannot-define-projection"]
      Record member_pair (s : nat) (pc : qname) (Dq : ind_decl) (Xa Xb : list domain) (sel : option (list nat))
          (ua ub : list domain) (i : nat) (Mi : imember) : Prop := mk_member_pair
        { mp_Mv : imember
        ; mp_member : ind_member D (elim_src sel i) = Some mp_Mv
        ; mp_nn : im_nn mp_Mv = im_nn Mi
        ; mp_hd : qname
        ; mp_k : nat
        ; mp_prea : list domain
        ; mp_preb : list domain
        ; mp_refa : ⟦mref i of pc Xa ⟧ gc_deps ⍮ gc_stack ↘ (mp_hd, mp_k, mp_prea)
        ; mp_refb : ⟦mref i of pc Xb ⟧ gc_deps ⍮ gc_stack ↘ (mp_hd, mp_k, mp_preb)
        ; mp_lena : List.length mp_prea = im_unu D mp_Mv
        ; mp_lenb : List.length mp_preb = im_unu D mp_Mv
        ; mp_nsa : list domain
        ; mp_nsb : list domain
        ; mp_Fa : Ftele List.rev (im_nparams Mi) in gc_deps ⍮ gc_stack ⍮ env_args nil Xa ⍮ s ↘ mp_nsa
        ; mp_Fb : Ftele List.rev (im_nparams Mi) in gc_deps ⍮ gc_stack ⍮ env_args nil Xb ⍮ s ↘ mp_nsb
        ; mp_neut : grp_rel p D ups nr ar dr (elim_src sel i) ua ub mp_nsa mp_nsb
            (⇑! (d_ind mp_hd mp_k (mp_prea ++ mp_nsa)) ((s + im_nn Mi)%nat))
            (⇑! (d_ind mp_hd mp_k (mp_preb ++ mp_nsb)) ((s + im_nn Mi)%nat))
        ; mp_names : List.map fst (im_cons Mi) = List.map fst (im_cons mp_Mv)
        ; mp_brs : forall c gs', List.In (c, gs') (im_cons Mi) -> cargs_plen Dq gs' /\
            exists gs, ind_con mp_Mv c = Some gs /\ List.length gs = List.length gs' /\
              brs_pair s pc Xa Xb sel (elim_src sel i) mp_Mv Mi mp_hd mp_k mp_prea mp_preb mp_nsa mp_nsb ua ub c gs' gs }.

      Lemma read_blocks_rel : forall s pc Dq Xa Xb sel ua ub Ms i, ind_lookup gc_deps gc_stack pc = Some Dq ->
          (forall n Mi, List.nth_error Ms n = Some Mi -> member_pair s pc Dq Xa Xb sel ua ub (i + n) Mi) ->
          exists NBks, Rblks i Ms of pc Xa from p Bksa sel in gc_deps ⍮ gc_stack ⍮ ρa ⍮ s ↘ NBks /\
            Rblks i Ms of pc Xb from p Bksb sel in gc_deps ⍮ gc_stack ⍮ ρb ⍮ s ↘ NBks.
      Proof.
        intros s pc Dq Xa Xb sel ua ub Ms; induction Ms as [| Mi Ms IH]; intros i0 Hq HMs.
        - exists nblocks_nil; split; constructor.
        - destruct (HMs 0 Mi eq_refl) as [Mv HM Hnn hd k prea preb Ra Rb La Lb nsa nsb Fa Fb Hne Hnames Hbrs].
          rewrite Nat.add_0_r in *.
          destruct (HbA _ _ HM) as [ba Ha]; destruct (HbB _ _ HM) as [bb Hb].
          destruct (Hmot _ _ _ _ _ _ _ _ _ _ HM Ha Hb Hne) as (a1 & a2 & Ea1 & Ea2 & HR).
          destruct (per_univ_then_per_top_typ HR (S (s + im_nn Mi))) as (A' & RA1 & RA2).
          assert (Hnd' : List.NoDup (List.map (fun b0 => fst (fst b0)) (eb_brs ba)))
            by (rewrite <- (HnaA _ _ _ HM Ha); exact (Hnd _ _ HM)).
          assert (Hnd'' : List.NoDup (List.map (fun b0 => fst (fst b0)) (eb_brs bb)))
            by (rewrite <- (HnaB _ _ _ HM Hb); exact (Hnd _ _ HM)).
          destruct (read_brs_rel s pc Dq Xa Xb sel _ Mv Mi hd k prea preb nsa nsb ua ub ba bb Hq HM Ha Hb Hnn La Lb Fa Fb
                      (im_cons Mi) (eb_brs ba) (eb_brs bb) Hbrs) as (Bs' & RB1 & RB2).
          { intros c n B Hin; split; [ apply brs_lookup_nodup_in; assumption | exact Hin ]. }
          { intros c n B Hin; split; [ apply brs_lookup_nodup_in; assumption | exact Hin ]. }
          { unfold brs_names; rewrite Hnames; exact (HnaA _ _ _ HM Ha). }
          { unfold brs_names; rewrite Hnames; exact (HnaB _ _ _ HM Hb). }
          destruct (IH (S i0) Hq) as (NBks & RN1 & RN2).
          { intros n Mi' Hn; replace (S i0 + n) with (i0 + S n) by lia; exact (HMs (S n) Mi' Hn). }
          exists (nblocks_cons (S (im_nn Mi)) A' Bs' NBks); split.
          + eapply read_blocks_cons; [ exact Hl | exact HM | exact Ha | rewrite (HnmA _ _ _ HM Ha), Hnn; reflexivity
                                     | exact Ra | exact Fa | exact Ea1 | exact RA1 | exact RB1 | exact RN1 ].
          + eapply read_blocks_cons; [ exact Hl | exact HM | exact Hb | rewrite (HnmB _ _ _ HM Hb), Hnn; reflexivity
                                     | exact Rb | exact Fb | exact Ea2 | exact RA2 | exact RB2 | exact RN2 ].
      Qed.

      (** *** The Blocks at a Declared Member

          A stuck eliminator at a declared member is read as its own group's,
          at the uniform parameters [Xa] and [Xb] of the scrutinee's types,
          admissible at the fresh variables: the fresh variables of each
          member's telescopes at them are related to those at [ups].  A
          branch's recursive results are its own group's. *)
      Lemma wihs_same : forall ρm As ρ1 gs vs s ihs, Fihs vs at gs under ρm As in gc_deps ⍮ gc_stack ⍮ ρ1 ⍮ s ↘ ihs ->
          forall ρ Bks, ⟦wihs vs of gs gs with ihs under p Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs.
      Proof. induction 1; intros; econstructor; eauto. Qed.

      Lemma fresh_args_decl : forall Xa Xb m Mm c gs nsu nsa nsb,
          adm_fresh p D ups nr ar dr Xa -> adm_fresh p D ups nr ar dr Xb ->
          List.length Xa = ind_nu D -> List.length Xb = ind_nu D ->
          ind_member D m = Some Mm -> ind_con Mm c = Some gs -> cargs_plen D gs ->
          tele_rel (nr m) (List.rev (im_nparams Mm)) nsu nsa -> tele_rel (nr m) (List.rev (im_nparams Mm)) nsu nsb ->
          forall gs2 gs1 wsu wsa wsb s s2, gs = gs1 ++ gs2 ->
          fresh_cargs_rel D ups Xa nr (ar m nsu c) (dr m) nsu nsa (List.length (cargs_nonrec gs1)) wsu wsa s gs2 ->
          fresh_cargs_rel D ups Xb nr (ar m nsu c) (dr m) nsu nsb (List.length (cargs_nonrec gs1)) wsu wsb s gs2 ->
          tele_prefix_rel (ar m nsu c) (List.length (cargs_nonrec gs1)) wsu wsa ->
          tele_prefix_rel (ar m nsu c) (List.length (cargs_nonrec gs1)) wsu wsb ->
          exists vsa vsb ihsa ihsb wfu,
            Fcargs gs2 of p Xa in gc_deps ⍮ gc_stack ⍮ env_args nil (Xa ++ nsa ++ wsa) ⍮ s ↘ vsa /\
            Fcargs gs2 of p Xb in gc_deps ⍮ gc_stack ⍮ env_args nil (Xb ++ nsb ++ wsb) ⍮ s ↘ vsb /\
            Fihs vsa at gs2 under ρa (blocks_motives Bksa) in gc_deps ⍮ gc_stack ⍮ env_args nil (Xa ++ nsa ++ wsa) ⍮ s2 ↘ ihsa /\
            Fihs vsb at gs2 under ρb (blocks_motives Bksb) in gc_deps ⍮ gc_stack ⍮ env_args nil (Xb ++ nsb ++ wsb) ⍮ s2 ↘ ihsb /\
            tele_prefix_rel (ar m nsu c) (List.length (cargs_nonrec gs)) wfu (wsa ++ nonrec_arg_vals gs2 vsa) /\
            tele_prefix_rel (ar m nsu c) (List.length (cargs_nonrec gs)) wfu (wsb ++ nonrec_arg_vals gs2 vsb) /\
            con_args_rel p D (grp_adm p D ups nr ar dr) (okr_at D ups nr) nr ar dr m Xa Xb (nsa ++ wsa) (nsb ++ wsb) gs2 vsa vsb /\
            rec_results_rel m Xa Xb (nsa ++ wsa) (nsb ++ wsb) gs2 vsa vsb ihsa ihsb.
      Proof.
        intros Xa Xb m Mm c gs nsu nsa nsb Ha Hb La Lb HM Hc Hpl Hn1 Hn2.
        induction gs2 as [| g gs2 IH]; intros gs1 wsu wsa wsb s s2 Heq C1 C2 Hw1 Hw2.
        - exists nil, nil, nil, nil, wsu; rewrite !List.app_nil_r.
          rewrite Heq, List.app_nil_r.
          refine (conj _ (conj _ (conj _ (conj _ (conj Hw1 (conj Hw2 (conj _ _))))))); constructor.
        - destruct g as [A | t].
          + inversion C1 as [| k0 ws0 ws0' s0 A0 gs0 a0 a1 E0 E1 R1 C1' |]; subst.
            inversion C2 as [| k0 ws0 ws0' s0 A0 gs0 a0' a2 E0' E2 R2 C2' |]; subst.
            pose proof (functional_eval_exp _ _ _ _ E0 E0') as <-.
            assert (Hk : List.length (cargs_nonrec (gs1 ++ ca_arg A :: nil)) = S (List.length (cargs_nonrec gs1)))
              by (rewrite cargs_nonrec_app, List.length_app; cbn; lia).
            destruct (IH (gs1 ++ ca_arg A :: nil) (wsu ++ ⇑! a0 s :: nil) (wsa ++ ⇑! a1 s :: nil) (wsb ++ ⇑! a2 s :: nil) (S s) s2)
              as (vsa & vsb & ihsa & ihsb & wfu & F1 & F2 & I1 & I2 & P1 & P2 & Hia & Hir).
            { rewrite <- List.app_assoc; reflexivity. }
            { rewrite Hk; exact C1'. }
            { rewrite Hk; exact C2'. }
            { rewrite Hk; apply tele_prefix_rel_snoc; assumption. }
            { rewrite Hk; apply tele_prefix_rel_snoc; assumption. }
            exists (⇑! a1 s :: vsa), (⇑! a2 s :: vsb), ihsa, ihsb, wfu.
            rewrite <- !List.app_assoc in P1, P2; cbn in P1, P2.
            refine (conj _ (conj _ (conj _ (conj _ (conj P1 (conj P2 (conj _ _))))))).
            * econstructor; [ exact E1 |]; rewrite <- env_args_snoc, <- !List.app_assoc; exact F1.
            * econstructor; [ exact E2 |]; rewrite <- env_args_snoc, <- !List.app_assoc; exact F2.
            * constructor; rewrite <- env_args_snoc, <- !List.app_assoc; exact I1.
            * constructor; rewrite <- env_args_snoc, <- !List.app_assoc; exact I2.
            * constructor; rewrite <- !List.app_assoc; exact Hia.
            * constructor; rewrite <- !List.app_assoc; exact Hir.
          + inversion C1 as [| | k0 ws0 ws0' s0 t0 gs0 HR1 HD1 C1']; subst.
            inversion C2 as [| | k0 ws0 ws0' s0 t0 gs0 HR2 HD2 C2']; subst.
            assert (Hc' : ind_con Mm c = Some (gs1 ++ ca_rec t :: gs2)) by exact Hc.
            destruct (Hpl gs1 t gs2 eq_refl) as (Mj & HMj & HPj).
            pose proof (mref_fresh_exists _ _ _ Ha HMj) as Me1; pose proof (mref_fresh_exists _ _ _ Hb HMj) as Me2.
            destruct (shape_type_exists Xa m Mm c gs1 t gs2 nsu nsa wsu wsa HM Hc' Me1 HR1 HD1 0 nil nil ltac:(lia)
                        (tele_prefix_rel_nil _)) as [a1 Ea1].
            destruct (shape_type_exists Xb m Mm c gs1 t gs2 nsu nsb wsu wsb HM Hc' Me2 HR2 HD2 0 nil nil ltac:(lia)
                        (tele_prefix_rel_nil _)) as [a2 Ea2].
            pose proof (shape_neut Xa Xb m Mm c gs1 t gs2 nsu nsa nsb wsu wsa wsb Ha Hb La Lb HM Hc' Me1 Me2 Hn1 Hn2 Hw1 Hw2
                          HR1 HR2 HD1 HD2 (List.length (ptyp_doms t)) 0 nil nil nil a1 a2 (d_var s) (d_var s) eq_refl
                          (tele_prefix_rel_nil _) (tele_prefix_rel_nil _) Ea1 Ea2 var_per_bot) as Hsh.
            pose proof (shape_tops_fresh Xa Xb m Mm c gs1 t gs2 nsu nsa nsb wsu wsa wsb HM Hc' Me1 Me2 Hn1 Hn2 Hw1 Hw2
                          HR1 HR2 HD1 HD2 (List.length (ptyp_doms t)) 0 nil nil nil a1 a2 eq_refl
                          (tele_prefix_rel_nil _) (tele_prefix_rel_nil _) Ea1 Ea2) as Hts.
            cbn [ptyp_skip] in Ea1, Ea2, Hsh, Hts.
            destruct (ih_fresh t t m Xa Xb (nsa ++ wsa ++ nil) (nsb ++ wsb ++ nil) p Xa p Xb _ _ a1 a2 (d_var s) (d_var s)
                        (blocks_motives Bksa) (blocks_motives Bksb) Hsh Hts eq_refl Ea1 Ea2)
              as (h1 & h2 & G1 & G2 & Hih).
            { intros Mj' HMj'; rewrite HMj in HMj'; injection HMj' as <-; exact HPj. }
            { intros b Hb0; exact (nth_blocks_motives _ _ _ Hb0). }
            { intros b Hb0; exact (nth_blocks_motives _ _ _ Hb0). }
            rewrite !List.app_nil_r in Ea1, Ea2, G1, G2.
            repeat rewrite List.app_nil_r in Hsh; repeat rewrite List.app_nil_r in Hih.
            destruct (IH (gs1 ++ ca_rec t :: nil) wsu wsa wsb (S s) (S s2))
              as (vsa & vsb & ihsa & ihsb & wfu & F1 & F2 & I1 & I2 & P1 & P2 & Hia & Hir).
            { rewrite <- List.app_assoc; reflexivity. }
            { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact C1'. }
            { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact C2'. }
            { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact Hw1. }
            { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact Hw2. }
            exists (⇑! a1 s :: vsa), (⇑! a2 s :: vsb), (⇑! h1 s2 :: ihsa), (⇑! h2 s2 :: ihsb), wfu.
            refine (conj _ (conj _ (conj _ (conj _ (conj P1 (conj P2 (conj _ _))))))).
            * econstructor; eassumption.
            * econstructor; eassumption.
            * econstructor; eassumption.
            * econstructor; eassumption.
            * eapply con_args_rec; [ exact Hsh | exact Hia ].
            * econstructor; [ exact (Hih _ _ var_per_bot) | exact Hir ].
      Qed.

      (** Each block of a stuck eliminator at a declared member. *)
      Lemma member_pair_decl : forall s Xa Xb i0 Mi, adm_fresh p D ups nr ar dr Xa -> adm_fresh p D ups nr ar dr Xb ->
          List.length Xa = ind_nu D -> List.length Xb = ind_nu D -> ind_member D i0 = Some Mi ->
          member_pair s p D Xa Xb None Xa Xb i0 Mi.
      Proof.
        intros s Xa Xb i0 Mi Ha Hb La Lb HM.
        pose proof (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tsym.
        pose proof (nparams_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as ttrans.
        pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl.
        pose proof (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl_r.
        destruct (mref_fresh_exists _ _ _ Ha HM) as [[[hd1 k1] pre1] R1].
        destruct (mref_fresh_exists _ _ _ Hb HM) as [[[hd2 k2] pre2] R2].
        destruct (mref_at_end_adm _ Ha La _ _ _ _ R1) as [Mj HMj Href1 Hadm1 Hlen1].
        rewrite HM in HMj; injection HMj as <-.
        destruct (mref_at_end_adm _ Hb Lb _ _ _ _ R2) as [Mj HMj Href2 Hadm2 Hlen2].
        rewrite HM in HMj; injection HMj as <-.
        rewrite Href1 in Href2; injection Href2 as <- <-.
        destruct (fresh_tele_rel_ftele _ _ _ _ _ _ _ _ (afr_nparams _ _ _ _ _ _ _ Ha i0 Mi s HM)) as (nsu & nsa & Fu & Fa & Lu & Hua).
        destruct (fresh_tele_rel_ftele _ _ _ _ _ _ _ _ (afr_nparams _ _ _ _ _ _ _ Hb i0 Mi s HM)) as (nsu' & nsb & Fu' & Fb & _ & Hub).
        rewrite List.app_nil_r in Fu, Fa, Fu', Fb.
        pose proof (functional_fresh_tele' _ _ _ _ _ Fu Fu') as <-.
        assert (Hn1 : tele_rel (nr i0) (List.rev (im_nparams Mi)) nsu nsa) by (split; assumption).
        assert (Hn2 : tele_rel (nr i0) (List.rev (im_nparams Mi)) nsu nsb) by (split; assumption).
        pose proof (ttrans _ _ HM _ _ _ (tsym _ _ HM _ _ Hn1) Hn2) as Hab.
        pose proof Hab as Lab; rewrite tele_rel_iff in Lab; destruct Lab as (Lna & Lnb & _).
        rewrite List.length_rev in Lna, Lnb.
        refine (mk_member_pair s p D Xa Xb None Xa Xb i0 Mi Mi HM eq_refl hd1 k1 pre1 pre2 R1 R2 Hlen1 Hlen2 nsa nsb Fa Fb
                  _ eq_refl _).
        - eapply ind_rel_neut; [ exact HM | exact Href1 | exact Hab | | | | | | | exact var_per_bot ].
          + rewrite List.length_app, Hlen1; unfold im_nn; lia.
          + rewrite List.length_app, Hlen2; unfold im_nn; lia.
          + rewrite firstn_app_exact by exact Hlen1; exact Hadm1.
          + rewrite firstn_app_exact by exact Hlen2; exact Hadm2.
          + rewrite skipn_app_exact by exact Hlen1; exact (trefl _ _ HM _ _ Hab).
          + rewrite skipn_app_exact by exact Hlen2; exact (trefl_r _ _ HM _ _ Hab).
        - intros c gs Hin; split; [ exact (gta_plen _ Hass _ _ _ _ HM Hin) |].
          pose proof (cons_lookup_nodup_in _ _ _ (Hnd _ _ HM) Hin) as Hc.
          exists gs; split; [ exact Hc | split; [ reflexivity |] ].
          pose proof (afr_args _ _ _ _ _ _ _ Ha i0 Mi c gs s nsu nsa HM Hc Fu Fa) as C1.
          pose proof (afr_args _ _ _ _ _ _ _ Hb i0 Mi c gs s nsu nsb HM Hc Fu Fb) as C2.
          destruct (fresh_args_decl Xa Xb i0 Mi c gs nsu nsa nsb Ha Hb La Lb HM Hc (gta_plen _ Hass _ _ _ _ HM Hin) Hn1 Hn2
                      gs nil nil nil nil (s + im_nn Mi) (s + im_nn Mi + List.length gs) eq_refl C1 C2
                      (tele_prefix_rel_nil _) (tele_prefix_rel_nil _))
            as (vsa & vsb & ihsa & ihsb & wfu & F1 & F2 & I1 & I2 & P1 & P2 & Hia & Hir).
          rewrite !List.app_nil_r in F1, F2, I1, I2.
          repeat rewrite List.app_nil_r in Hia; repeat rewrite List.app_nil_r in Hir.
          cbn [List.app] in P1, P2.
          refine (mk_brs_pair s p Xa Xb None _ Mi Mi hd1 k1 pre1 pre2 nsa nsb Xa Xb c gs gs vsa vsb ihsa ihsb ihsa ihsb F1 F2 I1 I2
                    (wihs_same _ _ _ _ _ _ _ I1 ρa Bksa) (wihs_same _ _ _ _ _ _ _ I2 ρb Bksb) _ _);
            [| exact Hir ].
          rewrite !List.app_assoc; eapply ind_rel_con; [ exact HM | exact Href1 | exact Hab | exact Hc | | | | | |].
          + rewrite List.length_app, Hlen1; unfold im_nn; lia.
          + rewrite List.length_app, Hlen2; unfold im_nn; lia.
          + rewrite skipn_app_exact by exact Hlen1; exact (trefl _ _ HM _ _ Hab).
          + rewrite skipn_app_exact by exact Hlen2; exact (trefl_r _ _ HM _ _ Hab).
          + rewrite skipn_app_exact by exact Hlen1.
            pose proof (trefl _ _ HM _ _ Hn1) as Huu.
            destruct P1 as [Lw1 Rw1]; destruct P2 as [Lw2 Rw2].
            assert (Q1 : tele_rel (ar i0 nsu c) (cargs_nonrec gs) wfu (nonrec_arg_vals gs vsa)) by (split; assumption).
            assert (Q2 : tele_rel (ar i0 nsu c) (cargs_nonrec gs) wfu (nonrec_arg_vals gs vsb)) by (split; assumption).
            apply (args_rel_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI i0 Mi HM nsu nsa c gs _ _ Hn1 Hc).
            exact (args_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI i0 Mi HM nsu c gs Huu Hc _ _ _
                     (args_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI i0 Mi HM nsu c gs Huu Hc _ _ Q1) Q2).
          + rewrite !skipn_app_exact by assumption; exact Hia.
      Qed.

      (** The stuck eliminator at a declared member, at related neutrals:
          its readbacks agree. *)
      Lemma per_bot_elim_decl : forall j Mj pm u u' ns ns' hd k' as1 as2 e e', ind_member D j = Some Mj ->
          im_head Mj = mh_decl pm ->
          grp_rel p D ups nr ar dr j u u' ns ns' (⇑ (d_ind hd k' as1) e) (⇑ (d_ind hd k' as2) e') ->
          Dom d_elim ρa Bksa p j as1 e ≈ d_elim ρb Bksb p j as2 e' ∈ per_bot.
      Proof.
        intros * HM Hh Hm.
        inversion Hm as [| j0 Mj0 hd0 k0 ns0 ns0' as1' as2' e0 e0' u0 u0' HM0 Hr Hn L1 L2 O1 O2 Hs1 Hs2 He]; subst.
        rewrite HM in HM0; injection HM0 as <-.
        unfold im_ref in Hr; rewrite Hh in Hr; injection Hr as <- <-.
        unfold grp_adm in O1, O2; rewrite HM, Hh in O1, O2.
        unfold im_unu in *; rewrite Hh in *.
        assert (La : List.length (List.firstn (ind_nu D) as1) = ind_nu D) by (rewrite List.length_firstn; lia).
        assert (Lb : List.length (List.firstn (ind_nu D) as2) = ind_nu D) by (rewrite List.length_firstn; lia).
        intros s; destruct (He s) as (M & RM1 & RM2).
        destruct (read_blocks_rel s p D (List.firstn (ind_nu D) as1) (List.firstn (ind_nu D) as2) None
                    (List.firstn (ind_nu D) as1) (List.firstn (ind_nu D) as2) (ind_members D) 0 Hl)
          as (NBks & RB1 & RB2).
        { intros n Mi Hn0; exact (member_pair_decl s _ _ n Mi O1 O2 La Lb Hn0). }
        assert (Hsel : im_sel Mj = None) by (unfold im_sel; rewrite Hh; reflexivity).
        exists (ne_elim p j NBks M); split.
        - eapply read_ne_elim; [ exact Hl | exact HM | unfold im_ref; rewrite Hh; reflexivity | exact Hl | exact HM
                               | unfold im_np; lia | intros i0 Mi b HMi Hb0; rewrite Hsel in Hb0; exact (HnmA _ _ _ HMi Hb0) | rewrite Hsel; exact RB1 | exact RM1 ].
        - eapply read_ne_elim; [ exact Hl | exact HM | unfold im_ref; rewrite Hh; reflexivity | exact Hl | exact HM
                               | unfold im_np; lia | intros i0 Mi b HMi Hb0; rewrite Hsel in Hb0; exact (HnmB _ _ _ HMi Hb0) | rewrite Hsel; exact RB2 | exact RM2 ].
      Qed.

      (** *** The Blocks at a View

          A stuck eliminator at a view is read as the container's, at the
          container's uniform parameters [Ya] and [Yb] of the scrutinee's
          types, each with its container at the fresh variables
          ([view_fresh]): the fresh variables of the telescopes of each
          member of the container's group at them are related to those at
          [⟦Is⟧ups], in the components of the member of this group [vm]
          takes it to.  A position recursive in both has the fresh
          recursive result; one the view nests through, the eliminator at
          its fresh variable, which is stuck at a member of lower rank. *)
      Definition elim_bot (j : nat) : Prop :=
        forall Mj hd k' as1 as2 e1 e1' w w' ns ns', ind_member D j = Some Mj ->
          grp_rel p D ups nr ar dr j w w' ns ns' (⇑ (d_ind hd k' as1) e1) (⇑ (d_ind hd k' as2) e1') ->
          Dom d_elim ρa Bksa p j as1 e1 ≈ d_elim ρb Bksb p j as2 e1' ∈ per_bot.

      Lemma fresh_args_view : forall qc Is Ya Yb Dq v Mv vm c gsf' gsf cups nsu nsa nsb (rk : nat -> nat) r,
          view_fresh p D ups nr ar dr qc Is Ya -> view_fresh p D ups nr ar dr qc Is Yb ->
          List.length Ya = List.length Is -> List.length Yb = List.length Is ->
          ind_member D v = Some Mv -> ind_con Mv c = Some gsf -> cargs_plen Dq gsf' ->
          (forall j' Mj', ind_member Dq j' = Some Mj' ->
             exists j0 Mj0, List.nth_error vm j' = Some j0 /\ ind_member D j0 = Some Mj0 /\ im_nn Mj0 = im_nn Mj') ->
          tele_rel (nr v) (List.rev (im_nparams Mv)) nsu nsa -> tele_rel (nr v) (List.rev (im_nparams Mv)) nsu nsb ->
          (forall j, rk j < r -> elim_bot j) ->
          forall gs' gs gs1' gs1 wcu wca wcb wvu wva wvb s s2, gsf' = gs1' ++ gs' -> gsf = gs1 ++ gs ->
          cargs_corr vm gs' gs -> cargs_nest_ok rk r gs' gs ->
          vfresh_cargs p D ups nr qc cups Ya (ar v nsu c) (dr v) (end_ok p D ups nr ar dr) (view_rec_end p D ups nr ar dr qc Is Ya)
            nsu nsa (List.length (cargs_nonrec gs1)) wcu wca wvu wva s gs' gs ->
          vfresh_cargs p D ups nr qc cups Yb (ar v nsu c) (dr v) (end_ok p D ups nr ar dr) (view_rec_end p D ups nr ar dr qc Is Yb)
            nsu nsb (List.length (cargs_nonrec gs1)) wcu wcb wvu wvb s gs' gs ->
          tele_prefix_rel (ar v nsu c) (List.length (cargs_nonrec gs1)) wvu wva ->
          tele_prefix_rel (ar v nsu c) (List.length (cargs_nonrec gs1)) wvu wvb ->
          exists vsa vsb ihsa ihsb wa wb wfu,
            Fcargs gs' of qc Ya in gc_deps ⍮ gc_stack ⍮ env_args nil (Ya ++ nsa ++ wca) ⍮ s ↘ vsa /\
            Fcargs gs' of qc Yb in gc_deps ⍮ gc_stack ⍮ env_args nil (Yb ++ nsb ++ wcb) ⍮ s ↘ vsb /\
            Fihs vsa at gs' under ρa (motives_sel (Some vm) (blocks_motives Bksa))
              in gc_deps ⍮ gc_stack ⍮ env_args nil (Ya ++ nsa ++ wca) ⍮ s2 ↘ ihsa /\
            Fihs vsb at gs' under ρb (motives_sel (Some vm) (blocks_motives Bksb))
              in gc_deps ⍮ gc_stack ⍮ env_args nil (Yb ++ nsb ++ wcb) ⍮ s2 ↘ ihsb /\
            ⟦wihs vsa of gs' gs with ihsa under p Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ wa /\
            ⟦wihs vsb of gs' gs with ihsb under p Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ wb /\
            tele_prefix_rel (ar v nsu c) (List.length (cargs_nonrec gsf)) wfu (wva ++ nonrec_arg_vals gs vsa) /\
            tele_prefix_rel (ar v nsu c) (List.length (cargs_nonrec gsf)) wfu (wvb ++ nonrec_arg_vals gs vsb) /\
            con_args_rel p D (grp_adm p D ups nr ar dr) (okr_at D ups nr) nr ar dr v ups ups (nsa ++ wva) (nsb ++ wvb) gs vsa vsb /\
            rec_results_rel v ups ups (nsa ++ wva) (nsb ++ wvb) gs vsa vsb wa wb.
      Proof.
        intros qc Is Ya Yb Dq v Mv vm c gsf' gsf cups nsu nsa nsb rk r HYa HYb LYa LYb HM Hc Hpl Hvm
          Hn1 Hn2 HIH.
        induction gs' as [| g' gs' IH]; intros [| g gs] gs1' gs1 wcu wca wcb wvu wva wvb s s2 Heq' Heq Hco Hno C1 C2 Hw1 Hw2;
          cbn in Hco; try contradiction; try (destruct g' as [? | ?]; cbn in Hco; contradiction).
        - exists nil, nil, nil, nil, nil, nil, wvu; rewrite !List.app_nil_r.
          rewrite Heq, List.app_nil_r.
          refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hw1 (conj Hw2 (conj _ _))))))))); constructor.
        - destruct g' as [A' | t']; destruct g as [A | t]; cbn in Hco; try contradiction.
          + (** Non-recursive in both. *)
            inversion C1 as [| k0 wcu0 wcy0 wvu0 wvy0 s0 A0' A0 gs0' gs0 a0 a1 E0 E1 R1 C1' | |]; subst.
            inversion C2 as [| k0 wcu0 wcy0 wvu0 wvy0 s0 A0' A0 gs0' gs0 a0' a2 E0' E2 R2 C2' | |]; subst.
            pose proof (functional_eval_exp _ _ _ _ E0 E0') as <-.
            assert (Hk : List.length (cargs_nonrec (gs1 ++ ca_arg A :: nil)) = S (List.length (cargs_nonrec gs1)))
              by (rewrite cargs_nonrec_app, List.length_app; cbn; lia).
            destruct (IH gs (gs1' ++ ca_arg A' :: nil) (gs1 ++ ca_arg A :: nil) (wcu ++ ⇑! a0 s :: nil) (wca ++ ⇑! a1 s :: nil)
                        (wcb ++ ⇑! a2 s :: nil) (wvu ++ ⇑! a0 s :: nil) (wva ++ ⇑! a1 s :: nil) (wvb ++ ⇑! a2 s :: nil) (S s) s2)
              as (vsa & vsb & ihsa & ihsb & wa & wb & wfu & F1 & F2 & I1 & I2 & W1 & W2 & P1 & P2 & Hia & Hir).
            { rewrite <- List.app_assoc; reflexivity. }
            { rewrite <- List.app_assoc; reflexivity. }
            { exact Hco. }
            { exact Hno. }
            { rewrite Hk; exact C1'. }
            { rewrite Hk; exact C2'. }
            { rewrite Hk; apply tele_prefix_rel_snoc; assumption. }
            { rewrite Hk; apply tele_prefix_rel_snoc; assumption. }
            exists (⇑! a1 s :: vsa), (⇑! a2 s :: vsb), ihsa, ihsb, wa, wb, wfu.
            rewrite <- !List.app_assoc in P1, P2; cbn in P1, P2.
            refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj P1 (conj P2 (conj _ _))))))))).
            * econstructor; [ exact E1 |]; rewrite <- env_args_snoc, <- !List.app_assoc; exact F1.
            * econstructor; [ exact E2 |]; rewrite <- env_args_snoc, <- !List.app_assoc; exact F2.
            * constructor; rewrite <- env_args_snoc, <- !List.app_assoc; exact I1.
            * constructor; rewrite <- env_args_snoc, <- !List.app_assoc; exact I2.
            * eapply wrap_ihs_eval_arg; exact W1.
            * eapply wrap_ihs_eval_arg; exact W2.
            * constructor; rewrite <- !List.app_assoc; exact Hia.
            * constructor; rewrite <- !List.app_assoc; exact Hir.
          + (** Nested through: the eliminator at the fresh variable. *)
            destruct Hno as [Hlt Hno].
            inversion C1 as [| | k0 wcu0 wcy0 wvu0 wvy0 s0 A0' t0 gs0' gs0 a0 a1 E0 E1 V1 C1' |]; subst.
            inversion C2 as [| | k0 wcu0 wcy0 wvu0 wvy0 s0 A0' t0 gs0' gs0 a0' a2 E0' E2 V2 C2' |]; subst.
            pose proof (functional_eval_exp _ _ _ _ E0 E0') as <-.
            assert (Hc' : ind_con Mv c = Some (gs1 ++ ca_rec t :: gs)) by exact Hc.
            pose proof (vshape_neut v Mv c gs1 t gs nsu nsa nsb wvu wva wvb (end_ok p D ups nr ar dr) (end_ok p D ups nr ar dr) HM Hc' Hn1 Hn2 Hw1 Hw2
                          end_ok_adm end_ok_adm (List.length (ptyp_doms t)) 0 nil nil nil
                          a0 a1 a2 (d_var s) (d_var s) eq_refl (tele_prefix_rel_nil _) (tele_prefix_rel_nil _)
                          ltac:(cbn [ptyp_skip]; rewrite List.app_nil_r; exact V1)
                          ltac:(cbn [ptyp_skip]; rewrite List.app_nil_r; exact V2) var_per_bot) as Hsh.
            cbn [ptyp_skip] in Hsh; repeat rewrite List.app_nil_r in Hsh.
            destruct (ih_neut_rel t v ups ups (nsa ++ wva) (nsb ++ wvb) a1 a2 (d_var s) (d_var s) Hsh (HIH _ Hlt))
              as (ih & ih' & J1 & J2 & Hres).
            destruct (IH gs (gs1' ++ ca_arg A' :: nil) (gs1 ++ ca_rec t :: nil) (wcu ++ ⇑! a0 s :: nil) (wca ++ ⇑! a1 s :: nil)
                        (wcb ++ ⇑! a2 s :: nil) wvu wva wvb (S s) s2)
              as (vsa & vsb & ihsa & ihsb & wa & wb & wfu & F1 & F2 & I1 & I2 & W1 & W2 & P1 & P2 & Hia & Hir).
            { rewrite <- List.app_assoc; reflexivity. }
            { rewrite <- List.app_assoc; reflexivity. }
            { exact Hco. }
            { exact Hno. }
            { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact C1'. }
            { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact C2'. }
            { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact Hw1. }
            { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact Hw2. }
            exists (⇑! a1 s :: vsa), (⇑! a2 s :: vsb), ihsa, ihsb, (ih :: wa), (ih' :: wb), wfu.
            refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj P1 (conj P2 (conj _ _))))))))).
            * econstructor; [ exact E1 |]; rewrite <- env_args_snoc, <- !List.app_assoc; exact F1.
            * econstructor; [ exact E2 |]; rewrite <- env_args_snoc, <- !List.app_assoc; exact F2.
            * constructor; rewrite <- env_args_snoc, <- !List.app_assoc; exact I1.
            * constructor; rewrite <- env_args_snoc, <- !List.app_assoc; exact I2.
            * eapply wrap_ihs_eval_nest; [ exact J1 | exact W1 ].
            * eapply wrap_ihs_eval_nest; [ exact J2 | exact W2 ].
            * eapply con_args_rec; [ exact Hsh | exact Hia ].
            * eapply rec_results_rec; [ exact Hres | exact Hir ].
          + (** Recursive in both: the fresh recursive result. *)
            destruct Hco as (Hvt & Hdep & Hco).
            inversion C1 as [| | | k0 wcu0 wcy0 wvu0 wvy0 s0 t0' t0 gs0' gs0 a0 a1 E0 E1 V1 C1']; subst.
            inversion C2 as [| | | k0 wcu0 wcy0 wvu0 wvy0 s0 t0' t0 gs0' gs0 a0' a2 E0' E2 V2 C2']; subst.
            pose proof (functional_eval_shty _ _ _ _ _ _ E0 E0') as <-.
            assert (Hc' : ind_con Mv c = Some (gs1 ++ ca_rec t :: gs)) by exact Hc.
            pose proof (vshape_neut v Mv c gs1 t gs nsu nsa nsb wvu wva wvb
                          (view_rec_end p D ups nr ar dr qc Is Ya) (view_rec_end p D ups nr ar dr qc Is Yb)
                          HM Hc' Hn1 Hn2 Hw1 Hw2
                          (view_rec_end_adm _ _ _ HYa LYa) (view_rec_end_adm _ _ _ HYb LYb)
                          (List.length (ptyp_doms t)) 0 nil nil nil
                          a0 a1 a2 (d_var s) (d_var s) eq_refl (tele_prefix_rel_nil _) (tele_prefix_rel_nil _)
                          ltac:(cbn [ptyp_skip]; rewrite List.app_nil_r; exact V1)
                          ltac:(cbn [ptyp_skip]; rewrite List.app_nil_r; exact V2) var_per_bot) as Hsh.
            pose proof (vshape_tops v Mv c gs1 t gs nsu nsa nsb wvu wva wvb
                          (view_rec_end p D ups nr ar dr qc Is Ya) (view_rec_end p D ups nr ar dr qc Is Yb)
                          HM Hc' Hn1 Hn2 Hw1 Hw2 (List.length (ptyp_doms t)) 0 nil nil nil
                          a0 a1 a2 eq_refl (tele_prefix_rel_nil _) (tele_prefix_rel_nil _)
                          ltac:(cbn [ptyp_skip]; rewrite List.app_nil_r; exact V1)
                          ltac:(cbn [ptyp_skip]; rewrite List.app_nil_r; exact V2)) as Hts.
            cbn [ptyp_skip] in Hsh, Hts; repeat rewrite List.app_nil_r in Hsh; repeat rewrite List.app_nil_r in Hts.
            destruct (ih_fresh t t' v ups ups (nsa ++ wva) (nsb ++ wvb) qc Ya qc Yb _ _ a1 a2 (d_var s) (d_var s)
                        (motives_sel (Some vm) (blocks_motives Bksa)) (motives_sel (Some vm) (blocks_motives Bksb))
                        Hsh Hts Hdep E1 E2) as (h1 & h2 & G1 & G2 & Hih).
            { intros Mj HMj.
              destruct (Hpl gs1' t' gs' eq_refl) as (Mj' & HMj' & HPj).
              destruct (Hvm _ _ HMj') as (j0 & Mj0 & Hj0 & HMj0 & Hnn0).
              rewrite Hvt in Hj0; injection Hj0 as <-; rewrite HMj in HMj0; injection HMj0 as <-.
              rewrite HPj; symmetry; exact Hnn0. }
            { intros b Hb0; exact (nth_motives_sel_view _ _ _ _ _ Hvt Hb0). }
            { intros b Hb0; exact (nth_motives_sel_view _ _ _ _ _ Hvt Hb0). }
            destruct (IH gs (gs1' ++ ca_rec t' :: nil) (gs1 ++ ca_rec t :: nil) wcu wca wcb wvu wva wvb (S s) (S s2))
              as (vsa & vsb & ihsa & ihsb & wa & wb & wfu & F1 & F2 & I1 & I2 & W1 & W2 & P1 & P2 & Hia & Hir).
            { rewrite <- List.app_assoc; reflexivity. }
            { rewrite <- List.app_assoc; reflexivity. }
            { exact Hco. }
            { exact Hno. }
            { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact C1'. }
            { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact C2'. }
            { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact Hw1. }
            { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact Hw2. }
            exists (⇑! a1 s :: vsa), (⇑! a2 s :: vsb), (⇑! h1 s2 :: ihsa), (⇑! h2 s2 :: ihsb),
              (⇑! h1 s2 :: wa), (⇑! h2 s2 :: wb), wfu.
            refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj P1 (conj P2 (conj _ _))))))))).
            * econstructor; eassumption.
            * econstructor; eassumption.
            * econstructor; eassumption.
            * econstructor; eassumption.
            * eapply wrap_ihs_eval_rec; exact W1.
            * eapply wrap_ihs_eval_rec; exact W2.
            * eapply con_args_rec; [ exact Hsh | exact Hia ].
            * eapply rec_results_rec; [ exact (Hih _ _ var_per_bot) | exact Hir ].
      Qed.

      (** Each block of a stuck eliminator at a view. *)
      Lemma member_pair_view : forall s j Mj qc kc Is vm Dq Ya Yb i' Mi' rk,
          ind_member D j = Some Mj -> im_head Mj = mh_view qc kc Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq ->
          view_fresh p D ups nr ar dr qc Is Ya -> view_fresh p D ups nr ar dr qc Is Yb ->
          List.length Ya = List.length Is -> List.length Yb = List.length Is ->
          view_rank_ok gc_deps gc_stack D rk -> (forall j', rk j' < rk j -> elim_bot j') ->
          ind_member Dq i' = Some Mi' ->
          member_pair s qc Dq Ya Yb (Some vm) ups ups i' Mi'.
      Proof.
        intros s j Mj qc kc Is vm Dq Ya Yb i' Mi' rk HM Hh Hq HYa HYb LYa LYb Hrk HIH HMi'.
        pose proof (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tsym.
        pose proof (nparams_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as ttrans.
        pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl.
        pose proof (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl_r.
        pose proof HYa as HVa; pose proof HYb as HVb.
        destruct (gta_vm _ Hass j Mj qc kc Is vm Dq i' Mi' HM Hh Hq HMi') as [v Mv Hvm HMv Hnn Hhead].
        pose proof (mk_view_cmember _ _ _ _ _ _ _ _ j Mj kc vm HM Hh Hq HMi' Hvm HMv) as Hcm.
        assert (Hsrc : elim_src (Some vm) i' = v) by (cbn; apply List.nth_error_nth; exact Hvm).
        destruct (view_fresh_instance _ _ _ _ _ _ _ _ _ HVa) as [_ _ _ _ cups _ _ Ecups].
        destruct (fresh_tele_rel_ftele _ _ _ _ _ _ _ _ (view_fresh_nparams _ _ _ _ _ _ _ _ _ HVa Dq i' Mi' v Mv cups s Hcm Ecups))
          as (nsu & nsa & Fu & Fa & Lu & Hua).
        destruct (fresh_tele_rel_ftele _ _ _ _ _ _ _ _ (view_fresh_nparams _ _ _ _ _ _ _ _ _ HVb Dq i' Mi' v Mv cups s Hcm Ecups))
          as (nsu' & nsb & Fu' & Fb & _ & Hub).
        rewrite List.app_nil_r in Fu, Fa, Fu', Fb.
        pose proof (functional_fresh_tele' _ _ _ _ _ Fu Fu') as <-.
        assert (LT : List.length (List.rev (im_nparams Mi')) = List.length (List.rev (im_nparams Mv)))
          by (rewrite !List.length_rev; unfold im_nn in Hnn; lia).
        assert (Hn1 : tele_rel (nr v) (List.rev (im_nparams Mv)) nsu nsa)
          by (apply (tele_rel_len _ (List.rev (im_nparams Mi'))); [ exact LT | split; assumption ]).
        assert (Hn2 : tele_rel (nr v) (List.rev (im_nparams Mv)) nsu nsb)
          by (apply (tele_rel_len _ (List.rev (im_nparams Mi'))); [ exact LT | split; assumption ]).
        pose proof (ttrans _ _ HMv _ _ _ (tsym _ _ HMv _ _ Hn1) Hn2) as Hab.
        pose proof Hab as Lab; rewrite tele_rel_iff in Lab; destruct Lab as (Lna & Lnb & _).
        rewrite List.length_rev in Lna, Lnb.
        (** The member at both sides, the container's at a view of the
            container's own group. *)
        assert (Hrefs : exists hd k prea preb, ⟦mref i' of qc Ya ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, prea) /\
                   ⟦mref i' of qc Yb ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, preb) /\ im_ref p v Mv = (hd, k) /\
                   List.length prea = im_unu D Mv /\ List.length preb = im_unu D Mv /\
                   grp_adm p D ups nr ar dr v prea /\ grp_adm p D ups nr ar dr v preb).
        { revert Hhead; destruct (im_head Mi') as [pm | qv kv Is'' vm''] eqn:Hh'; intros Hhead.
          - destruct Hhead as [vm' Hhv].
            exists qc, i', Ya, Yb.
            refine (conj (eval_mref_decl _ _ _ _ _ _ _ _ Hq HMi' Hh') (conj (eval_mref_decl _ _ _ _ _ _ _ _ Hq HMi' Hh') _)).
            unfold im_ref, im_unu, grp_adm; rewrite HMv, Hhv.
            exact (conj eq_refl (conj LYa (conj LYb (conj HYa HYb)))).
          - destruct Hhead as (Is' & vm' & Hhv & LIs).
            destruct (view_fresh_inner_ex _ _ _ _ _ _ _ _ _ HVa Dq i' Mi' v Mv qv kv Is'' vm'' Is' vm' Hcm Hh' Hhv) as [pya R1].
            destruct (view_fresh_inner_ex _ _ _ _ _ _ _ _ _ HVb Dq i' Mi' v Mv qv kv Is'' vm'' Is' vm' Hcm Hh' Hhv) as [pyb R2].
            pose proof (view_fresh_inner _ _ _ _ _ _ _ _ _ HVa Dq i' Mi' v Mv qv kv Is'' vm'' Is' vm' pya Hcm Hh' Hhv R1) as Wa.
            pose proof (view_fresh_inner _ _ _ _ _ _ _ _ _ HVb Dq i' Mi' v Mv qv kv Is'' vm'' Is' vm' pyb Hcm Hh' Hhv R2) as Wb.
            destruct (mref_view_inv _ _ _ _ _ _ _ _ _ _ Hq HMi' Hh' R1) as (py1 & E1 & Ey1); injection E1 as <-.
            destruct (mref_view_inv _ _ _ _ _ _ _ _ _ _ Hq HMi' Hh' R2) as (py2 & E2 & Ey2); injection E2 as <-.
            exists qv, kv, pya, pyb; refine (conj R1 (conj R2 _)).
            unfold im_ref, im_unu, grp_adm; rewrite HMv, Hhv.
            refine (conj eq_refl (conj _ (conj _ (conj Wa Wb)))).
            + rewrite (eval_exps_length _ _ _ Ey1); symmetry; exact LIs.
            + rewrite (eval_exps_length _ _ _ Ey2); symmetry; exact LIs. }
        destruct Hrefs as (hd & k & prea & preb & R1 & R2 & Href & La & Lb & Ada & Adb).
        destruct (gta_vwrap _ Hass j Mj qc kc Is vm HM Hh) as (D' & Hq' & Hvw).
        rewrite Hq in Hq'; injection Hq' as <-.
        destruct (vwo_members _ _ _ Hvw i' Mi' v HMi' Hvm) as (Mv' & HMv' & _ & Hnames & Hcorr).
        rewrite HMv in HMv'; injection HMv' as <-.
        refine (mk_member_pair s qc Dq Ya Yb (Some vm) ups ups i' Mi' Mv ltac:(rewrite Hsrc; exact HMv) Hnn hd k prea preb
                  R1 R2 La Lb nsa nsb Fa Fb _ (eq_sym Hnames) _).
        - rewrite Hsrc; eapply ind_rel_neut; [ exact HMv | exact Href | exact Hab | | | | | | | exact var_per_bot ].
          + rewrite List.length_app, La; unfold im_nn; lia.
          + rewrite List.length_app, Lb; unfold im_nn; lia.
          + rewrite firstn_app_exact by exact La; exact Ada.
          + rewrite firstn_app_exact by exact Lb; exact Adb.
          + rewrite skipn_app_exact by exact La; exact (trefl _ _ HMv _ _ Hab).
          + rewrite skipn_app_exact by exact Lb; exact (trefl_r _ _ HMv _ _ Hab).
        - intros c gs' Hin; rewrite Hsrc.
          split; [ exact (gta_cplen _ Hass j Mj qc kc Is vm Dq i' Mi' c gs' HM Hh Hq HMi' Hin) |].
          assert (HinN : List.In c (List.map fst (im_cons Mv)))
            by (rewrite Hnames; apply List.in_map_iff; exists (c, gs'); split; [ reflexivity | exact Hin ]).
          destruct (cons_lookup_names _ _ HinN) as [gs Hc].
          pose proof (Hcorr c gs' gs Hin Hc) as Hco.
          assert (Hc' : ind_con Mi' c = Some gs')
            by (apply cons_lookup_nodup_in; [ rewrite <- Hnames; exact (Hnd _ _ HMv) | exact Hin ]).
          exists gs; split; [ exact Hc | split; [ exact (eq_sym (cargs_corr_length _ _ _ Hco)) |] ].
          pose proof (view_fresh_args _ _ _ _ _ _ _ _ _ HVa Dq i' Mi' v Mv cups s c gs' gs nsu nsa Hcm Ecups Hc' Hc Fu Fa) as C1.
          pose proof (view_fresh_args _ _ _ _ _ _ _ _ _ HVb Dq i' Mi' v Mv cups s c gs' gs nsu nsb Hcm Ecups Hc' Hc Fu Fb) as C2.
          pose proof (vro_nest _ _ _ _ Hrk j Mj qc kc Is vm Dq i' Mi' v Mv c gs' gs HM Hh Hq HMi' Hvm HMv Hc' Hc) as Hno.
          assert (Hvm' : forall j' Mj', ind_member Dq j' = Some Mj' ->
                     exists j0 Mj0, List.nth_error vm j' = Some j0 /\ ind_member D j0 = Some Mj0 /\ im_nn Mj0 = im_nn Mj').
          { intros j' Mj' H'; destruct (gta_vm _ Hass j Mj qc kc Is vm Dq j' Mj' HM Hh Hq H') as [j0 Mj0 Hj0 HMj0 Hnn0 _].
            exists j0, Mj0; auto. }
          destruct (fresh_args_view qc Is Ya Yb Dq v Mv vm c gs' gs cups nsu nsa nsb rk (rk j)
                      HYa HYb LYa LYb HMv Hc (gta_cplen _ Hass j Mj qc kc Is vm Dq i' Mi' c gs' HM Hh Hq HMi' Hin) Hvm'
                      Hn1 Hn2 HIH gs' gs nil nil nil nil nil nil nil nil (s + im_nn Mi') (s + im_nn Mi' + List.length gs')
                      eq_refl eq_refl Hco Hno C1 C2 (tele_prefix_rel_nil _) (tele_prefix_rel_nil _))
            as (vsa & vsb & ihsa & ihsb & wa & wb & wfu & F1 & F2 & I1 & I2 & W1 & W2 & P1 & P2 & Hia & Hir).
          rewrite !List.app_nil_r in F1, F2, I1, I2.
          repeat rewrite List.app_nil_r in Hia; repeat rewrite List.app_nil_r in Hir.
          cbn [List.app] in P1, P2.
          refine (mk_brs_pair s qc Ya Yb (Some vm) v Mv Mi' hd k prea preb nsa nsb ups ups c gs' gs vsa vsb ihsa ihsb wa wb
                    F1 F2 I1 I2 W1 W2 _ _); [| exact Hir ].
          rewrite !List.app_assoc; eapply ind_rel_con; [ exact HMv | exact Href | exact Hab | exact Hc | | | | | |].
          + rewrite List.length_app, La; unfold im_nn; lia.
          + rewrite List.length_app, Lb; unfold im_nn; lia.
          + rewrite skipn_app_exact by exact La; exact (trefl _ _ HMv _ _ Hab).
          + rewrite skipn_app_exact by exact Lb; exact (trefl_r _ _ HMv _ _ Hab).
          + rewrite skipn_app_exact by exact La.
            pose proof (trefl _ _ HMv _ _ Hn1) as Huu.
            destruct P1 as [Lw1 Rw1]; destruct P2 as [Lw2 Rw2].
            assert (Q1 : tele_rel (ar v nsu c) (cargs_nonrec gs) wfu (nonrec_arg_vals gs vsa)) by (split; assumption).
            assert (Q2 : tele_rel (ar v nsu c) (cargs_nonrec gs) wfu (nonrec_arg_vals gs vsb)) by (split; assumption).
            apply (args_rel_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI v Mv HMv nsu nsa c gs _ _ Hn1 Hc).
            exact (args_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI v Mv HMv nsu c gs Huu Hc _ _ _
                     (args_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI v Mv HMv nsu c gs Huu Hc _ _ Q1) Q2).
          + rewrite !skipn_app_exact by assumption; exact Hia.
      Qed.

      (** The stuck eliminator at a view, at related neutrals, when the
          stuck eliminators at the members of lower rank read back alike. *)
      Lemma per_bot_elim_view : forall j Mj qc kc Is vm rk u u' ns ns' hd k' as1 as2 e e', ind_member D j = Some Mj ->
          im_head Mj = mh_view qc kc Is vm -> view_rank_ok gc_deps gc_stack D rk ->
          (forall j', rk j' < rk j -> elim_bot j') ->
          grp_rel p D ups nr ar dr j u u' ns ns' (⇑ (d_ind hd k' as1) e) (⇑ (d_ind hd k' as2) e') ->
          Dom d_elim ρa Bksa p j as1 e ≈ d_elim ρb Bksb p j as2 e' ∈ per_bot.
      Proof.
        intros * HM Hh Hrk HIH Hm.
        inversion Hm as [| j0 Mj0 hd0 k0 ns0 ns0' as1' as2' e0 e0' u0 u0' HM0 Hr Hn L1 L2 O1 O2 Hs1 Hs2 He]; subst.
        rewrite HM in HM0; injection HM0 as <-.
        unfold im_ref in Hr; rewrite Hh in Hr; injection Hr as <- <-.
        unfold grp_adm in O1, O2; rewrite HM, Hh in O1, O2.
        unfold im_unu in *; rewrite Hh in *.
        destruct (gta_views _ Hass j Mj qc kc Is vm HM Hh) as (Dq & Mc & Hq & HMc & Hnnc & LIs).
        assert (La : List.length (List.firstn (List.length Is) as1) = List.length Is) by (rewrite List.length_firstn; lia).
        assert (Lb : List.length (List.firstn (List.length Is) as2) = List.length Is) by (rewrite List.length_firstn; lia).
        intros s; destruct (He s) as (M & RM1 & RM2).
        destruct (read_blocks_rel s qc Dq (List.firstn (List.length Is) as1) (List.firstn (List.length Is) as2) (Some vm) ups ups
                    (ind_members Dq) 0 Hq) as (NBks & RB1 & RB2).
        { intros n Mi Hn0; exact (member_pair_view s j Mj qc kc Is vm Dq _ _ n Mi rk HM Hh Hq O1 O2 La Lb Hrk HIH Hn0). }
        assert (Hsel : im_sel Mj = Some vm) by (unfold im_sel; rewrite Hh; reflexivity).
        assert (Hnm : forall Bks, (forall j1 Mj1 b, ind_member D j1 = Some Mj1 -> List.nth_error Bks j1 = Some b -> eb_nm b = S (im_nn Mj1)) ->
                   blocks_nm_at Dq (Some vm) Bks).
        { intros Bks HB i0 Mi b HMi Hb0.
          destruct (gta_vm _ Hass j Mj qc kc Is vm Dq i0 Mi HM Hh Hq HMi) as [v Mv Hvm HMv Hnn _].
          cbn in Hb0; rewrite (List.nth_error_nth _ _ _ Hvm) in Hb0.
          rewrite (HB _ _ _ HMv Hb0), Hnn; reflexivity. }
        exists (ne_elim qc kc NBks M); split.
        - eapply read_ne_elim; [ exact Hl | exact HM | unfold im_ref; rewrite Hh; reflexivity | exact Hq | exact HMc
                               | unfold im_np; rewrite Hnnc, <- LIs; lia | rewrite Hsel; exact (Hnm _ HnmA)
                               | rewrite Hsel, <- LIs; exact RB1 | exact RM1 ].
        - eapply read_ne_elim; [ exact Hl | exact HM | unfold im_ref; rewrite Hh; reflexivity | exact Hq | exact HMc
                               | unfold im_np; rewrite Hnnc, <- LIs; lia | rewrite Hsel; exact (Hnm _ HnmB)
                               | rewrite Hsel, <- LIs; exact RB2 | exact RM2 ].
      Qed.

      (** ** The Stuck Eliminator

          By strong induction on the rank: a view's readback reads the
          eliminator at members of lower rank at the positions it nests
          through. *)
      Theorem per_bot_elim : forall j, elim_bot j.
      Proof.
        destruct (gta_rank _ Hass) as [rk Hrk].
        assert (H : forall r j, rk j < r -> elim_bot j).
        { induction r as [| r IH]; intros j Hj; [ lia |].
          intros Mj hd k' as1 as2 e1 e1' w w' ns ns' HM Hm.
          destruct (im_head Mj) as [pm | qc kc Is vm] eqn:Hh.
          - exact (per_bot_elim_decl j Mj pm w w' ns ns' hd k' as1 as2 e1 e1' HM Hh Hm).
          - apply (per_bot_elim_view j Mj qc kc Is vm rk w w' ns ns' hd k' as1 as2 e1 e1' HM Hh Hrk); [| exact Hm ].
            intros j' Hj'; apply IH; lia. }
        intros j; exact (H (S (rk j)) j ltac:(lia)).
      Qed.

      Lemma con_args_rel_length : forall adm okr k u u' pre pre' gs vs vs',
          con_args_rel p D adm okr nr ar dr k u u' pre pre' gs vs vs' ->
          List.length vs = List.length gs /\ List.length vs' = List.length gs.
      Proof.
        intros * H; induction H; cbn; try (destruct IHcon_args_rel; split; f_equal; assumption); split; reflexivity.
      Qed.

      (** ** Related Elements Eliminate to Related Values *)
      Theorem per_ind_elim_all :
        (forall j u u' ns ns' m m', grp_rel p D ups nr ar dr j u u' ns ns' m m' ->
           exists r r', ⟦elim m at j of p Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ r /\
             ⟦elim m' at j of p Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ r' /\ Rel j ns m ns' m' r r') /\
        (forall k u u' pre pre' gs vs vs',
           con_args_rel p D (grp_adm p D ups nr ar dr) (okr_at D ups nr) nr ar dr k u u' pre pre' gs vs vs' ->
           exists ihs ihs', ⟦ihs vs of gs under p Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ ihs /\
             ⟦ihs vs' of gs under p Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ ihs' /\ rec_results_rel k u u' pre pre' gs vs vs' ihs ihs') /\
        (forall k u u' pre pre' t v v',
           rec_arg_rel p D (grp_adm p D ups nr ar dr) (okr_at D ups nr) nr ar dr k u u' pre pre' t v v' ->
           exists ih ih', ⟦ih v of t under p Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ ih /\
             ⟦ih v' of t under p Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ ih' /\ rec_result_rel k u u' pre pre' t v v' ih ih') /\
        (forall k u u' pre pre' t f c f' c',
           rec_arg_app_rel p D (grp_adm p D ups nr ar dr) (okr_at D ups nr) nr ar dr k u u' pre pre' t f c f' c' ->
           exists fc fc' r r', $| f & c | gc_deps ⍮ gc_stack ↘ fc /\ $| f' & c' | gc_deps ⍮ gc_stack ↘ fc' /\
             ⟦ih fc of t under p Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ r /\ ⟦ih fc' of t under p Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ r' /\
             rec_result_rel k u u' pre pre' t fc fc' r r').
      Proof.
        pose proof (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tsym.
        apply ind_rel_mut_ind_all.
        - (** A constructor: its branch, at its own parameters, moved to
              the indices. *)
          intros * HM Href Hn Hc Lb Lb' Hs Hs' Ha Hia IH.
          destruct IH as (ihs & ihs' & Ei & Ei' & Hir).
          destruct (HbA _ _ HM) as [ba HBka]; destruct (HbB _ _ HM) as [bb HBkb].
          destruct (brs_names_lookup _ _ _ _ (HnaA _ _ _ HM HBka) Hc) as (n & Ba & HBa & HinA).
          destruct (brs_names_lookup _ _ _ _ (HnaB _ _ _ HM HBkb) Hc) as (n' & Bb & HBb & HinB).
          pose proof (HarA _ _ _ _ _ _ _ HM HBka Hc HinA) as Hn0; pose proof (HarB _ _ _ _ _ _ _ HM HBkb Hc HinB) as Hn0'.
          assert (n' = n) as -> by lia.
          destruct (im_ref_target _ _ _ _ HM Href) as (Dq & Mq & Hq & HMq & Hnnq & Hnuq).
          destruct (con_args_rel_length _ _ _ _ _ _ _ _ _ _ Hia) as [Lv Lv'].
          match goal with |- exists r r', ⟦elim d_con _ _ _ (?bs ++ ?vs) at _ of _ _ ⟧ _ ⍮ _ ⍮ _ ↘ r /\
                                           ⟦elim d_con _ _ _ (?bs' ++ ?vs') at _ of _ _ ⟧ _ ⍮ _ ⍮ _ ↘ r' /\ _ =>
            assert (Hcur : grp_rel p D ups nr ar dr _ _ _ _ _ (d_con _ _ _ (bs ++ vs)) (d_con _ _ _ (bs' ++ vs')))
              by (eapply ind_rel_con; [ exact HM | exact Href | exact Hn | exact Hc | exact Lb | exact Lb' | exact Hs | exact Hs'
                                     | exact Ha | exact Hia ]) end.
          pose proof (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ HM Hcur Hs Hs') as Hm.
          destruct (Hbr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM HBka HBkb Hc HBa HBb Hm Hir) as (r & r' & Er & Er' & Hrr).
          exists r, r'; split; [| split ].
          + eapply eval_elim_con; [ exact Hl | exact HM | exact Href | exact Hq | exact HMq | exact Hc
                                  | rewrite List.length_app; unfold im_np; lia | exact HBka | exact HBa | rewrite Hnnq; exact Hn0 | |].
            * rewrite skipn_app_exact by (unfold im_np; lia); exact Ei.
            * rewrite firstn_app_exact, skipn_app_exact, Hnuq by (unfold im_np; lia); exact Er.
          + eapply eval_elim_con; [ exact Hl | exact HM | exact Href | exact Hq | exact HMq | exact Hc
                                  | rewrite List.length_app; unfold im_np; lia | exact HBkb | exact HBb | rewrite Hnnq; exact Hn0 | |].
            * rewrite skipn_app_exact by (unfold im_np; lia); exact Ei'.
            * rewrite firstn_app_exact, skipn_app_exact, Hnuq by (unfold im_np; lia); exact Er'.
          + apply (motive_rel_move _ _ _ _ _ _ _ _ _ _ HM Hm (tsym _ _ HM _ _ Hs) (tsym _ _ HM _ _ Hs')); exact Hrr.
        - (** A neutral: stuck, its readbacks agree. *)
          intros * u0 u0' HM Href Hn L1 L2 O1 O2 Hs1 Hs2 He.
          eapply (neut_elim_rel _ _ u0 u0'); [ exact HM | | eapply (per_bot_elim _ _ _ _ _ _ _ _ u0 u0'); [ exact HM |] ];
            (eapply ind_rel_neut; [ exact HM | exact Href | exact Hn | exact L1 | exact L2 | exact O1 | exact O2 | exact Hs1
                                  | exact Hs2 | exact He ]).
        - intros; exists nil, nil; split; [ constructor | split; [ constructor | constructor ] ].
        - intros * Hia (ihs & ihs' & Ei & Ei' & Hir).
          exists ihs, ihs'; split; [ constructor; exact Ei | split; [ constructor; exact Ei' | constructor; exact Hir ] ].
        - intros * Hsh (ih & ih' & Eh & Eh' & Hhh) Hia (ihs & ihs' & Ei & Ei' & Hir).
          exists (ih :: ihs), (ih' :: ihs'); split; [ econstructor; eassumption | split; [ econstructor; eassumption |] ].
          econstructor; eassumption.
        - intros * Hb Hb' Ok Ok' Hr (r & r' & Er & Er' & Hrr).
          exists r, r'; split; [ constructor; exact Er | split; [ constructor; exact Er' |] ].
          econstructor; [ exact Hb | exact Hb' | exact Hrr ].
        - intros * Hf IH.
          match goal with |- exists ih ih', ⟦ih ?f of pt_pi _ ?t under _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ih /\
                                            ⟦ih ?f' of _ under _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ih' /\ _ =>
            exists (d_ihfn ρa Bksa p t f), (d_ihfn ρb Bksb p t f') end.
          split; [ constructor | split; [ constructor |] ].
          constructor; intros c c' Hcc.
          destruct (IH c c' Hcc) as (fc & fc' & r & r' & Ef & Ef' & Er & Er' & Hrr).
          econstructor; [ exact Ef | exact Ef' | econstructor; eassumption | econstructor; eassumption | exact Hrr ].
        - intros * Ef Ef' Hsh (ih & ih' & Eh & Eh' & Hhh).
          do 4 eexists; split; [ exact Ef | split; [ exact Ef' | split; [ exact Eh | split; [ exact Eh' | exact Hhh ] ] ] ].
      Qed.
    End ElimRel.
  End ElimGroup.
End Fixed_GCtx.
