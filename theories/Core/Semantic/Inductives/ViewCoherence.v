(** * The Elements of a View, as the Container's

    A view of a group [D] at [p] is the declared member [k'] of the
    container's group [Dq] at [qc] at the uniform arguments [Is]: its
    type is the container's at [⟦Is⟧ups], so its elements are related by
    the container's relation there.  The group relates them by its own
    relation at the view, whose telescopes are the group's own, filed
    free of the group (model P).  Coherence: an element of the container's
    member [i'] is one of the group's member [vm i'] the view takes it to,
    when the two telescopes agree position by position ([view_container_to_group]).
    The agreement is stated over the two relations' families, at prefixes
    the container relates: what the view equations give, read in the PER
    model once the group is a type of it. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic.Inductives Require Export IndCanon.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

  Lemma cargs_corr_app : forall vm gs1' gs1 gs2' gs2, cargs_corr vm gs1' gs1 -> cargs_corr vm gs2' gs2 ->
      cargs_corr vm (gs1' ++ gs2') (gs1 ++ gs2).
  Proof.
    induction gs1' as [| [A' | t'] gs1' IH]; intros [| [A | t] gs1] * H1 H2; cbn in *; try contradiction; auto.
    destruct H1 as (? & ? & ?); auto.
  Qed.

  Lemma cargs_corr_len : forall vm gs' gs, cargs_corr vm gs' gs -> List.length gs' = List.length gs.
  Proof.
    induction gs' as [| [A' | t'] gs' IH]; intros [| [A | t] gs] H; cbn in H |- *; try contradiction; try reflexivity.
    - f_equal; exact (IH _ H).
    - f_equal; exact (IH _ H).
    - f_equal; exact (IH _ (proj2 (proj2 H))).
  Qed.

  Lemma con_args_rel_len : forall p D okr nr ar dr k u u' pre pre' gs vs vs',
      con_args_rel p D okr nr ar dr k u u' pre pre' gs vs vs' -> List.length vs = List.length gs /\ List.length vs' = List.length gs.
  Proof. induction 1; cbn; lia. Qed.

  Section ViewCoh.
    (** The group, with views, and its relations. *)
    Variables (p : qname) (D : ind_decl) (ups ups' : list domain).
    Variable (nr : nat -> nat -> list domain -> relation domain).
    Variable (ar : nat -> list domain -> String.string -> nat -> list domain -> relation domain).
    Variable (dr : nat -> list domain -> exp -> relation domain).
    Hypothesis (Hass : grp_tele_ass D).
    Hypothesis (HnP : nparams_per D nr) (HnI : nparams_inv D nr).
    Hypothesis (HaP : args_per D nr ar) (HaI : args_inv D nr ar).
    Hypothesis (HdP : doms_per D nr ar dr) (HdI : doms_inv D nr ar dr).

    (** The container, and its relations. *)
    Variables (qc : qname) (Dq : ind_decl) (cups cups' : list domain).
    Variable (nr' : nat -> nat -> list domain -> relation domain).
    Variable (ar' : nat -> list domain -> String.string -> nat -> list domain -> relation domain).
    Variable (dr' : nat -> list domain -> exp -> relation domain).
    Hypothesis (Hass' : grp_tele_ass Dq).
    Hypothesis (HnP' : nparams_per Dq nr') (HnI' : nparams_inv Dq nr').
    Hypothesis (HaP' : args_per Dq nr' ar') (HaI' : args_inv Dq nr' ar').
    Hypothesis (HdP' : doms_per Dq nr' ar' dr') (HdI' : doms_inv Dq nr' ar' dr').

    (** The members of the container's group the view takes to members of
        the group. *)
    Variable (vm : list nat).

    #[local] Abbreviation G := (ind_rel p D (okr_at D ups nr) nr ar dr).
    #[local] Abbreviation C := (ind_rel qc Dq (okr_at Dq cups nr') nr' ar' dr').
    #[local] Abbreviation CA := (con_args_rel qc Dq (okr_at Dq cups nr') nr' ar' dr').
    #[local] Abbreviation GA := (con_args_rel p D (okr_at D ups nr) nr ar dr).
    #[local] Abbreviation CR := (rec_arg_rel qc Dq (okr_at Dq cups nr') nr' ar' dr').
    #[local] Abbreviation GR := (rec_arg_rel p D (okr_at D ups nr) nr ar dr).
    #[local] Abbreviation CP := (rec_arg_app_rel qc Dq (okr_at Dq cups nr') nr' ar' dr').
    #[local] Abbreviation GP := (rec_arg_app_rel p D (okr_at D ups nr) nr ar dr).

    (** The member [v] of the group the container's member [i'] is taken
        to: of the same head, as many parameters, its constructors the
        container's, each argument corresponding. *)
    Record view_member (i' : nat) (Mi' : imember) (v : nat) (Mv : imember) : Prop := mk_view_member
      { (** [vm] takes [i'] to [v] *)
        vmb_v : List.nth_error vm i' = Some v
        (** [v] is a member of the group *)
      ; vmb_mem : ind_member D v = Some Mv
        (** It has the same head: both are the same declared member *)
      ; vmb_ref : im_ref p v Mv = im_ref qc i' Mi'
        (** As many own uniform parameters *)
      ; vmb_unu : im_unu D Mv = im_unu Dq Mi'
        (** As many non-uniform parameters *)
      ; vmb_nn : im_nn Mv = im_nn Mi'
        (** Each container constructor is one of [Mv]'s, its arguments
            corresponding *)
      ; vmb_cons : forall c gs', ind_con Mi' c = Some gs' -> exists gs, ind_con Mv c = Some gs /\ cargs_corr vm gs' gs
        (** And conversely *)
      ; vmb_cons' : forall c gs, ind_con Mv c = Some gs -> exists gs', ind_con Mi' c = Some gs' /\ cargs_corr vm gs' gs }.

    (** The parameters a shape ends in, at a base and a prefix on each
        side, related at the member of the group the group's shape ends
        in. *)
    #[warnings="-cannot-define-projection"]
    Record ps_link (Ps' Ps : list exp) (j : nat) (ρc ρg : env) : Prop := mk_ps_link
      { (** The container side's parameters *)
        psl_c : list domain
        (** The group side's parameters *)
      ; psl_g : list domain
        (** The container's shape's [Ps'] evaluate to them *)
      ; psl_eval_c : ⟦ Ps' ⟧* gc_deps ⍮ gc_stack ⍮ ρc ↘ psl_c
        (** The group's shape's [Ps] evaluate to them *)
      ; psl_eval_g : ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ ρg ↘ psl_g
        (** They are related at the member [j] *)
      ; psl_rel : ntele_rel D nr j psl_c psl_g }.

    (** The view maps each member of the container's group, and the two
        telescopes agree position by position. *)
    Record view_agreement : Prop := mk_view_agreement
    { (** Each member of the container's group is taken to a member of the
          group ([view_member]). *)
      agree_members : forall i' Mi', ind_member Dq i' = Some Mi' -> exists v Mv, view_member i' Mi' v Mv
    (** A recursive argument of the container's ends in a member of its group. *)
    ; agree_recursive_targets : forall i' Mi' c gs1' t' gs2', ind_member Dq i' = Some Mi' -> ind_con Mi' c = Some (gs1' ++ ca_rec t' :: gs2') ->
      exists Mj', ind_member Dq (ptyp_mem t') = Some Mj'
    (** The non-uniform parameters. *)
    ; agree_nparams_rel : forall i' Mi' v Mv k vs vs', ind_member Dq i' = Some Mi' -> view_member i' Mi' v Mv ->
      k < im_nn Mi' -> tele_prefix_rel (nr' i') k vs vs' -> (nr' i' k vs <~> nr v k vs)
    (** An argument non-recursive in both, after the arguments [vp] before
        it, [gs1'] and [gs1] as the container and the group have them. *)
    ; agree_args_rel : forall i' Mi' v Mv c gs1' A' gs2' gs1 A gs2 ms ms' vp vp' x y,
      ind_member Dq i' = Some Mi' -> view_member i' Mi' v Mv ->
      ind_con Mi' c = Some (gs1' ++ ca_arg A' :: gs2') -> ind_con Mv c = Some (gs1 ++ ca_arg A :: gs2) ->
      cargs_corr vm gs1' gs1 -> List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
      tele_rel (nr' i') (List.rev (im_nparams Mi')) ms ms' ->
      tele_prefix_rel (ar' i' ms c) (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp') ->
      (ar' i' ms c (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) x y <->
       ar v ms c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vp) x y)
    (** An argument the view nests through: non-recursive in the
        container, recursive of a shape in the group. *)
    ; agree_nested_arg_rel : forall i' Mi' v Mv c gs1' A' gs2' gs1 t gs2 ms ms' vp vp' x y,
      ind_member Dq i' = Some Mi' -> view_member i' Mi' v Mv ->
      ind_con Mi' c = Some (gs1' ++ ca_arg A' :: gs2') -> ind_con Mv c = Some (gs1 ++ ca_rec t :: gs2) ->
      cargs_corr vm gs1' gs1 -> List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
      tele_rel (nr' i') (List.rev (im_nparams Mi')) ms ms' ->
      tele_prefix_rel (ar' i' ms c) (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp') ->
      (ar' i' ms c (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) x y <->
       GR v ups ups' (ms ++ nonrec_arg_vals gs1 vp) (ms' ++ nonrec_arg_vals gs1 vp') t x y)
    (** An argument recursive in both: the domains of the shapes, after
        [ys] of them. *)
    ; agree_shape_doms_rel : forall i' Mi' v Mv c gs1' t' gs2' gs1 t gs2 ms ms' vp vp' d B' B ys ys',
      ind_member Dq i' = Some Mi' -> view_member i' Mi' v Mv ->
      ind_con Mi' c = Some (gs1' ++ ca_rec t' :: gs2') -> ind_con Mv c = Some (gs1 ++ ca_rec t :: gs2) ->
      cargs_corr vm gs1' gs1 -> List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
      List.nth_error (ptyp_doms t') d = Some B' -> List.nth_error (ptyp_doms t) d = Some B ->
      tele_rel (nr' i') (List.rev (im_nparams Mi')) ms ms' ->
      tele_prefix_rel (ar' i' ms c) (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp') ->
      tele_prefix_rel (shape_doms_rel (dr' i') ms (nonrec_arg_vals gs1' vp) (ptyp_doms t')) d ys ys' ->
      (dr' i' (ms ++ nonrec_arg_vals gs1' vp ++ ys) B' <~> dr v (ms ++ nonrec_arg_vals gs1 vp ++ ys) B)
    (** An argument recursive in both: the parameters the shapes end in. *)
    ; agree_shape_params : forall i' Mi' v Mv c gs1' t' gs2' gs1 t gs2 ms ms' vp vp' ys ys',
      ind_member Dq i' = Some Mi' -> view_member i' Mi' v Mv ->
      ind_con Mi' c = Some (gs1' ++ ca_rec t' :: gs2') -> ind_con Mv c = Some (gs1 ++ ca_rec t :: gs2) ->
      cargs_corr vm gs1' gs1 -> List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
      tele_rel (nr' i') (List.rev (im_nparams Mi')) ms ms' ->
      tele_prefix_rel (ar' i' ms c) (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp') ->
      tele_rel (shape_doms_rel (dr' i') ms (nonrec_arg_vals gs1' vp) (ptyp_doms t')) (ptyp_doms t') ys ys' ->
      ps_link (ptyp_ps t') (ptyp_ps t) (ptyp_mem t)
        (env_args nil (cups ++ ms ++ nonrec_arg_vals gs1' vp ++ ys)) (env_args nil (ups ++ ms ++ nonrec_arg_vals gs1 vp ++ ys)) /\
      ps_link (ptyp_ps t') (ptyp_ps t) (ptyp_mem t)
        (env_args nil (cups' ++ ms' ++ nonrec_arg_vals gs1' vp' ++ ys')) (env_args nil (ups' ++ ms' ++ nonrec_arg_vals gs1 vp' ++ ys')) /\
      ps_link (ptyp_ps t') (ptyp_ps t) (ptyp_mem t)
        (env_args nil (cups ++ ms' ++ nonrec_arg_vals gs1' vp' ++ ys')) (env_args nil (ups ++ ms' ++ nonrec_arg_vals gs1 vp' ++ ys')) }.

    Hypothesis (Hvc : view_agreement).
    #[local] Abbreviation Hmem := (agree_members Hvc).
    #[local] Abbreviation HN := (agree_nparams_rel Hvc).
    #[local] Abbreviation HA := (agree_args_rel Hvc).
    #[local] Abbreviation HR := (agree_nested_arg_rel Hvc).
    #[local] Abbreviation HD := (agree_shape_doms_rel Hvc).
    #[local] Abbreviation HP := (agree_shape_params Hvc).
    #[local] Abbreviation Hrm := (agree_recursive_targets Hvc).

    (** ** The Non-Uniform Parameters *)

    Lemma nr_to : forall i' Mi' v Mv a b, ind_member Dq i' = Some Mi' -> view_member i' Mi' v Mv ->
        tele_rel (nr' i') (List.rev (im_nparams Mi')) a b -> tele_rel (nr v) (List.rev (im_nparams Mv)) a b.
    Proof.
      intros * HM Hv H.
      pose proof H as H0; rewrite tele_rel_iff in H0; destruct H0 as (Hl & Hl' & Hr).
      rewrite List.length_rev, length_im_nparams in Hl, Hl'.
      rewrite tele_rel_iff, List.length_rev, length_im_nparams, (vmb_nn _ _ _ _ Hv).
      split; [ exact Hl | split; [ exact Hl' |] ].
      intros j x x' Hx Hx'.
      assert (Hj : j < im_nn Mi') by (rewrite <- Hl; apply List.nth_error_Some; congruence).
      pose proof (tele_prefix_rel_of_full _ _ _ _ j H ltac:(rewrite List.length_rev, length_im_nparams; lia)) as Hp.
      apply (HN _ _ _ _ _ _ _ HM Hv Hj Hp); exact (Hr _ _ _ Hx Hx').
    Qed.

    Lemma nr_from : forall i' Mi' v Mv a b, ind_member Dq i' = Some Mi' -> view_member i' Mi' v Mv ->
        tele_rel (nr v) (List.rev (im_nparams Mv)) a b -> tele_rel (nr' i') (List.rev (im_nparams Mi')) a b.
    Proof.
      intros * HM Hv H.
      pose proof H as H0; rewrite tele_rel_iff in H0; destruct H0 as (Hl & Hl' & Hr).
      rewrite List.length_rev, length_im_nparams, (vmb_nn _ _ _ _ Hv) in Hl, Hl'.
      assert (Hpre : forall j, j <= im_nn Mi' -> tele_prefix_rel (nr' i') j (List.firstn j a) (List.firstn j b)).
      { induction j as [| j IH]; intros Hj; [ cbn; apply tele_prefix_rel_nil |].
        destruct (nth_error_lt_some' a j ltac:(lia)) as [x Hx]; destruct (nth_error_lt_some' b j ltac:(lia)) as [x' Hx'].
        rewrite (firstn_S_snoc _ _ _ Hx), (firstn_S_snoc _ _ _ Hx').
        apply tele_prefix_rel_snoc; [ exact (IH ltac:(lia)) |].
        apply (HN _ _ _ _ j _ _ HM Hv ltac:(lia) (IH ltac:(lia))); exact (Hr _ _ _ Hx Hx'). }
      rewrite tele_rel_iff, List.length_rev, length_im_nparams; split; [ exact Hl | split; [ exact Hl' |] ].
      intros j x x' Hx Hx'.
      assert (Hj : j < im_nn Mi') by (rewrite <- Hl; apply List.nth_error_Some; congruence).
      apply (HN _ _ _ _ _ _ _ HM Hv Hj (Hpre j ltac:(lia))); exact (Hr _ _ _ Hx Hx').
    Qed.

    (** ** The Non-Recursive Arguments the Group Has *)

    Lemma nonrec_to : forall i' Mi' v Mv c ms ms' gs' gs gs1' gs1 vp vp' vs vs', ind_member Dq i' = Some Mi' ->
        view_member i' Mi' v Mv -> ind_con Mi' c = Some (gs1' ++ gs') -> ind_con Mv c = Some (gs1 ++ gs) ->
        cargs_corr vm gs1' gs1 -> cargs_corr vm gs' gs ->
        List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
        List.length vs = List.length gs -> List.length vs' = List.length gs ->
        tele_rel (nr' i') (List.rev (im_nparams Mi')) ms ms' ->
        tele_prefix_rel (ar' i' ms c) (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp') ->
        tele_rel_from (ar' i' ms c) (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs' vs) (nonrec_arg_vals gs' vs') ->
        tele_rel_from (ar v ms c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vp) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs').
    Proof.
      intros i' Mi' v Mv c ms ms' gs'; induction gs' as [| g' gs' IH];
        intros gs0 gs1' gs1 vp vp' vs vs' HM Hv Hc' Hc Hcorr1 Hcorr Hlp Hlp' Hl Hl' Hms Hpre Hfr.
      - destruct gs0; cbn in Hcorr; try contradiction.
        destruct vs, vs'; cbn in *; try discriminate; exact I.
      - destruct gs0 as [| g gs]; [ destruct g'; contradiction |].
        destruct vs as [| x vs], vs' as [| x' vs']; cbn in Hl, Hl'; try discriminate.
        assert (Hlp1 : List.length (vp ++ x :: nil) = List.length (gs1 ++ g :: nil)) by (rewrite !List.length_app; cbn; lia).
        assert (Hlp1' : List.length (vp' ++ x' :: nil) = List.length (gs1 ++ g :: nil)) by (rewrite !List.length_app; cbn; lia).
        assert (Hc1' : ind_con Mi' c = Some ((gs1' ++ g' :: nil) ++ gs')) by (rewrite <- List.app_assoc; exact Hc').
        assert (Hc1 : ind_con Mv c = Some ((gs1 ++ g :: nil) ++ gs)) by (rewrite <- List.app_assoc; exact Hc).
        assert (Hlc : List.length vp = List.length gs1') by (rewrite Hlp; symmetry; exact (cargs_corr_len _ _ _ Hcorr1)).
        assert (Hlc' : List.length vp' = List.length gs1') by (rewrite Hlp'; symmetry; exact (cargs_corr_len _ _ _ Hcorr1)).
        assert (Hk' : List.length (nonrec_arg_vals gs1' vp) = List.length (cargs_nonrec gs1'))
          by exact (length_nonrec_arg_vals _ _ Hlc).
        destruct g' as [A' | t'], g as [A | t]; cbn [cargs_corr] in Hcorr; try contradiction;
          cbn [nonrec_arg_vals tele_rel_from] in Hfr |- *.
        + (* non-recursive in both *)
          destruct Hfr as [Hx Hfr].
          split.
          * exact (proj1 (HA _ _ _ _ _ _ _ _ _ _ _ _ ms' _ vp' _ _ HM Hv Hc' Hc Hcorr1 Hlp Hlp' Hms Hpre) Hx).
          * pose proof (IH gs (gs1' ++ ca_arg A' :: nil) (gs1 ++ ca_arg A :: nil) (vp ++ x :: nil) (vp' ++ x' :: nil) vs vs'
                          HM Hv Hc1' Hc1 (cargs_corr_app _ _ _ (ca_arg A' :: nil) (ca_arg A :: nil) Hcorr1 I) Hcorr Hlp1 Hlp1' ltac:(lia) ltac:(lia) Hms) as IH'.
            rewrite !cargs_nonrec_app, !nonrec_arg_vals_app, !List.length_app in IH' by lia;
            cbn [cargs_nonrec nonrec_arg_vals List.length List.app] in IH'; rewrite ?List.app_nil_r, ?Nat.add_0_r, ?Nat.add_1_r in IH'.
            apply IH'; [| exact Hfr ].
            apply tele_prefix_rel_snoc; [ exact Hpre |].
            rewrite <- Hk' in Hx |- *; exact Hx.
        + (* the view nests through it *)
          destruct Hfr as [Hx Hfr].
          pose proof (IH gs (gs1' ++ ca_arg A' :: nil) (gs1 ++ ca_rec t :: nil) (vp ++ x :: nil) (vp' ++ x' :: nil) vs vs'
                        HM Hv Hc1' Hc1 (cargs_corr_app _ _ _ (ca_arg A' :: nil) (ca_rec t :: nil) Hcorr1 I) Hcorr Hlp1 Hlp1' ltac:(lia) ltac:(lia) Hms) as IH'.
          rewrite !cargs_nonrec_app, !nonrec_arg_vals_app, !List.length_app in IH' by lia;
            cbn [cargs_nonrec nonrec_arg_vals List.length List.app] in IH'; rewrite ?List.app_nil_r, ?Nat.add_0_r, ?Nat.add_1_r in IH'.
          apply IH'; [| exact Hfr ].
          apply tele_prefix_rel_snoc; [ exact Hpre |].
          rewrite <- Hk' in Hx |- *; exact Hx.
        + (* recursive in both *)
          destruct Hcorr as (Hm & Hd & Hcorr).
          pose proof (IH gs (gs1' ++ ca_rec t' :: nil) (gs1 ++ ca_rec t :: nil) (vp ++ x :: nil) (vp' ++ x' :: nil) vs vs'
                        HM Hv Hc1' Hc1 (cargs_corr_app _ _ _ (ca_rec t' :: nil) (ca_rec t :: nil) Hcorr1 (conj Hm (conj Hd I))) Hcorr Hlp1 Hlp1' ltac:(lia) ltac:(lia) Hms)
            as IH'.
          rewrite !cargs_nonrec_app, !nonrec_arg_vals_app, !List.length_app in IH' by lia;
            cbn [cargs_nonrec nonrec_arg_vals List.length List.app] in IH'; rewrite ?List.app_nil_r, ?Nat.add_0_r, ?Nat.add_1_r in IH'.
          exact (IH' Hpre Hfr).
    Qed.

    (** ** From the Container's to the Group's *)

    Lemma app_assoc_3 : forall (a b c : list domain) x, (a ++ b ++ c) ++ x :: nil = a ++ b ++ (c ++ x :: nil).
    Proof. intros; rewrite <- !List.app_assoc; reflexivity. Qed.

    Theorem view_container_to_group_all :
      (forall i' u u' ns ns' x y, C i' u u' ns ns' x y -> u = cups -> u' = cups' ->
         forall v, List.nth_error vm i' = Some v -> G v ups ups' ns ns' x y) /\
      (forall i' u u' pre pre' gs' vs vs', CA i' u u' pre pre' gs' vs vs' -> u = cups -> u' = cups' ->
         forall Mi' v Mv c gs1' gs1 gs ms ms' vp vp',
           ind_member Dq i' = Some Mi' -> view_member i' Mi' v Mv ->
           ind_con Mi' c = Some (gs1' ++ gs') -> ind_con Mv c = Some (gs1 ++ gs) ->
           cargs_corr vm gs1' gs1 -> cargs_corr vm gs' gs ->
           List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
           pre = ms ++ nonrec_arg_vals gs1' vp -> pre' = ms' ++ nonrec_arg_vals gs1' vp' ->
           tele_rel (nr' i') (List.rev (im_nparams Mi')) ms ms' ->
           tele_prefix_rel (ar' i' ms c) (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp') ->
           tele_rel_from (ar' i' ms c) (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp)
             (nonrec_arg_vals gs' vs) (nonrec_arg_vals gs' vs') ->
           GA v ups ups' (ms ++ nonrec_arg_vals gs1 vp) (ms' ++ nonrec_arg_vals gs1 vp') gs vs vs') /\
      (forall i' u u' pre pre' t'' x y, CR i' u u' pre pre' t'' x y -> u = cups -> u' = cups' ->
         forall Mi' v Mv c gs1' t' gs2' gs1 t gs2 ms ms' vp vp' d ys ys',
           ind_member Dq i' = Some Mi' -> view_member i' Mi' v Mv ->
           ind_con Mi' c = Some (gs1' ++ ca_rec t' :: gs2') -> ind_con Mv c = Some (gs1 ++ ca_rec t :: gs2) ->
           cargs_corr vm gs1' gs1 -> List.nth_error vm (ptyp_mem t') = Some (ptyp_mem t) -> ptyp_depth t' = ptyp_depth t ->
           List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
           t'' = ptyp_skip d t' -> List.length ys = d -> List.length ys' = d -> d <= ptyp_depth t' ->
           pre = ms ++ nonrec_arg_vals gs1' vp ++ ys -> pre' = ms' ++ nonrec_arg_vals gs1' vp' ++ ys' ->
           tele_rel (nr' i') (List.rev (im_nparams Mi')) ms ms' ->
           tele_prefix_rel (ar' i' ms c) (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp') ->
           tele_prefix_rel (shape_doms_rel (dr' i') ms (nonrec_arg_vals gs1' vp) (ptyp_doms t')) d ys ys' ->
           GR v ups ups' (ms ++ nonrec_arg_vals gs1 vp ++ ys) (ms' ++ nonrec_arg_vals gs1 vp' ++ ys') (ptyp_skip d t) x y) /\
      (forall i' u u' pre pre' t'' f a f' a', CP i' u u' pre pre' t'' f a f' a' -> u = cups -> u' = cups' ->
         forall Mi' v Mv c gs1' t' gs2' gs1 t gs2 ms ms' vp vp' d ys ys',
           ind_member Dq i' = Some Mi' -> view_member i' Mi' v Mv ->
           ind_con Mi' c = Some (gs1' ++ ca_rec t' :: gs2') -> ind_con Mv c = Some (gs1 ++ ca_rec t :: gs2) ->
           cargs_corr vm gs1' gs1 -> List.nth_error vm (ptyp_mem t') = Some (ptyp_mem t) -> ptyp_depth t' = ptyp_depth t ->
           List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
           t'' = ptyp_skip d t' -> List.length ys = d -> List.length ys' = d -> d <= ptyp_depth t' ->
           pre = ms ++ nonrec_arg_vals gs1' vp ++ ys -> pre' = ms' ++ nonrec_arg_vals gs1' vp' ++ ys' ->
           tele_rel (nr' i') (List.rev (im_nparams Mi')) ms ms' ->
           tele_prefix_rel (ar' i' ms c) (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp') ->
           tele_prefix_rel (shape_doms_rel (dr' i') ms (nonrec_arg_vals gs1' vp) (ptyp_doms t')) d ys ys' ->
           GP v ups ups' (ms ++ nonrec_arg_vals gs1 vp ++ ys) (ms' ++ nonrec_arg_vals gs1 vp' ++ ys') (ptyp_skip d t) f a f' a').
    Proof.
      apply ind_rel_mut_ind_all.
      - (* a constructor *)
        intros k Mk hd k' ns ns' c gs' bs bs' vs vs' u u' HMk Href Hns Hcon Hlb Hlb' Hs Hs' Hnr Hca IH Hu Hu' v Hvm.
        destruct (Hmem _ _ HMk) as (v0 & Mv & Hv).
        assert (v0 = v) as -> by (rewrite (vmb_v _ _ _ _ Hv) in Hvm; congruence).
        destruct (vmb_cons _ _ _ _ Hv c gs' Hcon) as (gs & Hc & Hcorr).
        pose proof (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hca) as [Hlv Hlv'].
        pose proof (cargs_corr_len _ _ _ Hcorr) as Hlg.
        assert (Hms : tele_rel (nr' k) (List.rev (im_nparams Mk)) (List.skipn (im_unu Dq Mk) bs) (List.skipn (im_unu Dq Mk) bs')).
        { eapply (nparams_rel_trans qc Dq cups nr' ar' dr' Hass' HnP' HnI' HaP' HaI' HdP' HdI' k Mk HMk);
            [ exact (nparams_rel_sym qc Dq cups nr' ar' dr' Hass' HnP' HnI' HaP' HaI' HdP' HdI' k Mk HMk _ _ Hs) |].
          exact (nparams_rel_trans qc Dq cups nr' ar' dr' Hass' HnP' HnI' HaP' HaI' HdP' HdI' k Mk HMk _ _ _ Hns Hs'). }
        rewrite <- (vmb_unu _ _ _ _ Hv) in Hlb, Hlb', Hs, Hs', Hnr, Hca, Hms.
        rewrite <- (vmb_nn _ _ _ _ Hv) in Hlb, Hlb'.
        eapply ind_rel_con with (Mk := Mv) (gs := gs);
          [ exact (vmb_mem _ _ _ _ Hv) | rewrite (vmb_ref _ _ _ _ Hv); exact Href | exact (nr_to _ _ _ _ _ _ HMk Hv Hns)
          | exact Hc | exact Hlb | exact Hlb' | exact (nr_to _ _ _ _ _ _ HMk Hv Hs) | exact (nr_to _ _ _ _ _ _ HMk Hv Hs') | |].
        + destruct Hnr as [Hl0 Hnr].
          split; [ rewrite length_nonrec_arg_vals by lia; reflexivity |].
          exact (nonrec_to _ _ _ _ c _ _ gs' gs nil nil nil nil vs vs' HMk Hv Hcon Hc I Hcorr eq_refl eq_refl ltac:(lia) ltac:(lia)
                   Hms (tele_prefix_rel_nil _) Hnr).
        + rewrite (vmb_unu _ _ _ _ Hv) in Hca, Hms, Hnr |- *.
          pose proof (IH Hu Hu' Mk v Mv c nil nil gs (List.skipn (im_unu Dq Mk) bs) (List.skipn (im_unu Dq Mk) bs') nil nil
                        HMk Hv Hcon Hc I Hcorr eq_refl eq_refl ltac:(cbn; rewrite List.app_nil_r; reflexivity)
                        ltac:(cbn; rewrite List.app_nil_r; reflexivity) Hms (tele_prefix_rel_nil _) (proj2 Hnr)) as H.
          cbn [nonrec_arg_vals] in H; rewrite !List.app_nil_r in H; exact H.
      - (* a neutral *)
        intros k Mk hd k' ns ns' as1 as2 m m' u u' HMk Href Hns Hl1 Hl2 Hs Hs' Hm Hu Hu' v Hvm.
        destruct (Hmem _ _ HMk) as (v0 & Mv & Hv).
        assert (v0 = v) as -> by (rewrite (vmb_v _ _ _ _ Hv) in Hvm; congruence).
        rewrite <- (vmb_unu _ _ _ _ Hv) in Hl1, Hl2, Hs, Hs'; rewrite <- (vmb_nn _ _ _ _ Hv) in Hl1, Hl2.
        eapply ind_rel_neut with (Mk := Mv);
          [ exact (vmb_mem _ _ _ _ Hv) | rewrite (vmb_ref _ _ _ _ Hv); exact Href | exact (nr_to _ _ _ _ _ _ HMk Hv Hns)
          | exact Hl1 | exact Hl2 | exact (nr_to _ _ _ _ _ _ HMk Hv Hs) | exact (nr_to _ _ _ _ _ _ HMk Hv Hs')
          | exact Hm ].
      - (* no argument *)
        intros k u u' pre pre' Hu Hu' * _ _ _ _ _ Hcorr _ _ _ _ _ _ _.
        destruct gs; cbn in Hcorr; [ constructor | contradiction ].
      - (* a non-recursive argument of the container's *)
        intros k u u' pre x pre' x' gs' vs vs' A' Hrest IH Hu Hu' Mi' v Mv c gs1' gs1 gs ms ms' vp vp'
          HM Hv Hc' Hc Hcorr1 Hcorr Hlp Hlp' Hpre Hpre' Hms Hpw Hfr.
        assert (Hlc : List.length vp = List.length gs1') by (rewrite Hlp; symmetry; exact (cargs_corr_len _ _ _ Hcorr1)).
        assert (Hlc' : List.length vp' = List.length gs1') by (rewrite Hlp'; symmetry; exact (cargs_corr_len _ _ _ Hcorr1)).
        assert (Hk' : List.length (nonrec_arg_vals gs1' vp) = List.length (cargs_nonrec gs1'))
          by exact (length_nonrec_arg_vals _ _ Hlc).
        assert (Hc1' : ind_con Mi' c = Some ((gs1' ++ ca_arg A' :: nil) ++ gs')) by (rewrite <- List.app_assoc; exact Hc').
        cbn [nonrec_arg_vals tele_rel_from] in Hfr; destruct Hfr as [Hx Hfr].
        assert (Hnv : forall w w', List.length w = List.length gs1' ->
                   nonrec_arg_vals (gs1' ++ ca_arg A' :: nil) (w ++ w' :: nil) = nonrec_arg_vals gs1' w ++ w' :: nil)
          by (intros; rewrite nonrec_arg_vals_app by lia; reflexivity).
        assert (Hln : List.length (cargs_nonrec (gs1' ++ ca_arg A' :: nil)) = S (List.length (cargs_nonrec gs1')))
          by (rewrite cargs_nonrec_app, List.length_app; cbn; lia).
        assert (Hpw1 : tele_prefix_rel (ar' k ms c) (List.length (cargs_nonrec (gs1' ++ ca_arg A' :: nil)))
                         (nonrec_arg_vals (gs1' ++ ca_arg A' :: nil) (vp ++ x :: nil))
                         (nonrec_arg_vals (gs1' ++ ca_arg A' :: nil) (vp' ++ x' :: nil))).
        { rewrite Hln, !Hnv by lia; apply tele_prefix_rel_snoc; [ exact Hpw | rewrite <- Hk' in Hx |- *; exact Hx ]. }
        assert (Hfr1 : tele_rel_from (ar' k ms c) (List.length (cargs_nonrec (gs1' ++ ca_arg A' :: nil)))
                         (nonrec_arg_vals (gs1' ++ ca_arg A' :: nil) (vp ++ x :: nil)) (nonrec_arg_vals gs' vs) (nonrec_arg_vals gs' vs'))
          by (rewrite Hln, Hnv by lia; exact Hfr).
        assert (Hpre1 : pre ++ x :: nil = ms ++ nonrec_arg_vals (gs1' ++ ca_arg A' :: nil) (vp ++ x :: nil))
          by (rewrite Hnv, Hpre, <- List.app_assoc by lia; reflexivity).
        assert (Hpre1' : pre' ++ x' :: nil = ms' ++ nonrec_arg_vals (gs1' ++ ca_arg A' :: nil) (vp' ++ x' :: nil))
          by (rewrite Hnv, Hpre', <- List.app_assoc by lia; reflexivity).
        destruct gs as [| [A | t] gs0]; cbn in Hcorr; try contradiction.
        + (* non-recursive in the group too *)
          assert (Hc1 : ind_con Mv c = Some ((gs1 ++ ca_arg A :: nil) ++ gs0)) by (rewrite <- List.app_assoc; exact Hc).
          pose proof (IH Hu Hu' Mi' v Mv c (gs1' ++ ca_arg A' :: nil) (gs1 ++ ca_arg A :: nil) gs0 ms ms' (vp ++ x :: nil) (vp' ++ x' :: nil)
                        HM Hv Hc1' Hc1 (cargs_corr_app _ _ _ (ca_arg A' :: nil) (ca_arg A :: nil) Hcorr1 I) Hcorr
                        ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                        Hpre1 Hpre1' Hms Hpw1 Hfr1) as H.
          rewrite !nonrec_arg_vals_app in H by lia; cbn [nonrec_arg_vals] in H.
          apply con_args_arg; rewrite <- !List.app_assoc; exact H.
        + (* recursive in the group: the view nests through it *)
          assert (Hc1 : ind_con Mv c = Some ((gs1 ++ ca_rec t :: nil) ++ gs0)) by (rewrite <- List.app_assoc; exact Hc).
          pose proof (IH Hu Hu' Mi' v Mv c (gs1' ++ ca_arg A' :: nil) (gs1 ++ ca_rec t :: nil) gs0 ms ms' (vp ++ x :: nil) (vp' ++ x' :: nil)
                        HM Hv Hc1' Hc1 (cargs_corr_app _ _ _ (ca_arg A' :: nil) (ca_rec t :: nil) Hcorr1 I) Hcorr
                        ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                        Hpre1 Hpre1' Hms Hpw1 Hfr1) as H.
          rewrite !nonrec_arg_vals_app in H by lia; cbn [nonrec_arg_vals] in H; rewrite !List.app_nil_r in H.
          apply con_args_rec; [| exact H ].
          exact (proj1 (HR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hv Hc' Hc Hcorr1 Hlp Hlp' Hms Hpw) Hx).
      - (* a recursive argument of the container's *)
        intros k u u' pre pre' t' x x' gs' vs vs' Hr IHr Hrest IH Hu Hu' Mi' v Mv c gs1' gs1 gs ms ms' vp vp'
          HM Hv Hc' Hc Hcorr1 Hcorr Hlp Hlp' Hpre Hpre' Hms Hpw Hfr.
        destruct gs as [| [A | t] gs0]; cbn in Hcorr; try contradiction.
        destruct Hcorr as (Hm & Hd & Hcorr).
        assert (Hc1' : ind_con Mi' c = Some ((gs1' ++ ca_rec t' :: nil) ++ gs')) by (rewrite <- List.app_assoc; exact Hc').
        assert (Hc1 : ind_con Mv c = Some ((gs1 ++ ca_rec t :: nil) ++ gs0)) by (rewrite <- List.app_assoc; exact Hc).
        assert (Hnv : forall w w' (g : carg) gs1x, List.length w = List.length gs1x ->
                   nonrec_arg_vals (gs1x ++ ca_rec t :: nil) (w ++ w' :: nil) = nonrec_arg_vals gs1x w)
          by (intros; rewrite nonrec_arg_vals_app by lia; cbn; apply List.app_nil_r).
        assert (Hnv' : forall w w' gs1x, List.length w = List.length gs1x ->
                   nonrec_arg_vals (gs1x ++ ca_rec t' :: nil) (w ++ w' :: nil) = nonrec_arg_vals gs1x w)
          by (intros; rewrite nonrec_arg_vals_app by lia; cbn; apply List.app_nil_r).
        assert (Hlc : List.length vp = List.length gs1') by (rewrite Hlp; symmetry; exact (cargs_corr_len _ _ _ Hcorr1)).
        assert (Hlc' : List.length vp' = List.length gs1') by (rewrite Hlp'; symmetry; exact (cargs_corr_len _ _ _ Hcorr1)).
        assert (Hln : forall gs1x tx, List.length (cargs_nonrec (gs1x ++ ca_rec tx :: nil)) = List.length (cargs_nonrec gs1x))
          by (intros; rewrite cargs_nonrec_app, List.length_app; cbn; lia).
        apply con_args_rec.
        + pose proof (IHr Hu Hu' Mi' v Mv c gs1' t' gs' gs1 t gs0 ms ms' vp vp' 0 nil nil HM Hv Hc' Hc Hcorr1 Hm Hd Hlp Hlp'
                        eq_refl eq_refl eq_refl ltac:(lia) ltac:(rewrite Hpre, List.app_nil_r; reflexivity)
                        ltac:(rewrite Hpre', List.app_nil_r; reflexivity) Hms Hpw (tele_prefix_rel_nil _)) as H.
          rewrite !List.app_nil_r in H; exact H.
        + pose proof (IH Hu Hu' Mi' v Mv c (gs1' ++ ca_rec t' :: nil) (gs1 ++ ca_rec t :: nil) gs0 ms ms' (vp ++ x :: nil) (vp' ++ x' :: nil)
                        HM Hv Hc1' Hc1 (cargs_corr_app _ _ _ (ca_rec t' :: nil) (ca_rec t :: nil) Hcorr1 (conj Hm (conj Hd I))) Hcorr
                        ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                        ltac:(rewrite Hnv' by lia; exact Hpre) ltac:(rewrite Hnv' by lia; exact Hpre') Hms
                        ltac:(rewrite Hln, !Hnv' by lia; exact Hpw) ltac:(rewrite Hln, Hnv' by lia; exact Hfr)) as H.
          rewrite !(Hnv _ _ (ca_rec t)) in H by lia; exact H.
      - (* the end of a shape *)
        intros Ps u pre bs u' pre' bs' j x x' k Ebs Ebs' Ho Ho' Hi IH Hu Hu' Mi' v Mv c gs1' t' gs2' gs1 t gs2 ms ms' vp vp' d ys ys'
          HM Hv Hc' Hc Hcorr1 Hm Hdep Hlp Hlp' Hsk Hly Hly' Hd Hpre Hpre' Hms Hpw Hpy.
        subst u u'.
        destruct (ptyp_skip_self _ _ _ _ (eq_sym Hsk)) as (Hle & Hj & HPs); subst j Ps.
        unfold ptyp_depth in Hd, Hdep.
        assert (Hdd : d = List.length (ptyp_doms t')) by lia.
        assert (Hskt : ptyp_skip d t = pt_self (ptyp_mem t) (ptyp_ps t))
          by (rewrite Hdd, Hdep; apply ptyp_skip_end).
        rewrite Hskt; rewrite Hdd in Hpy.
        pose proof (tele_rel_of_pre _ (ptyp_doms t') _ _ Hpy) as Hpy'.
        destruct (HP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hv Hc' Hc Hcorr1 Hlp Hlp' Hms Hpw Hpy') as (HL & HRt & HX).
        subst pre pre'.
        destruct HL as [e bsg Ee Ebsg Hbg]; pose proof (functional_eval_exps' _ _ _ _ Ee Ebs) as ->.
        destruct HRt as [e' bsg' Ee' Ebsg' Hbg']; pose proof (functional_eval_exps' _ _ _ _ Ee' Ebs') as ->.
        pose proof (IH eq_refl eq_refl _ Hm) as Hg.
        destruct (ntele_rel_member p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ Hbg) as (Mj & HMj & Hbgt).
        destruct (ntele_rel_member p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ Hbg') as (Mj0 & HMj0 & Hbgt').
        rewrite HMj in HMj0; injection HMj0 as <-.
        eapply rec_arg_self; [ exact Ebsg | exact Ebsg' | | | ].
        + exact (mk_okr_at _ _ _ _ _ _ _ _ Ebsg (ntele_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ Hbg)).
        + destruct Ho' as [idx' Eidx' Hidx'].
          destruct HX as [e1 e2 Ee1 Ee2 He2]; pose proof (functional_eval_exps' _ _ _ _ Ee1 Eidx') as ->.
          unfold ntele_rel in Hidx'; destruct (ind_member Dq (ptyp_mem t')) as [Mj' |] eqn:HMj'; [| contradiction ].
          destruct (Hmem _ _ HMj') as (v' & Mv' & Hv').
          assert (v' = ptyp_mem t) as -> by (rewrite (vmb_v _ _ _ _ Hv') in Hm; congruence).
          pose proof (nr_to _ _ _ _ _ _ HMj' Hv' Hidx') as Hidx.
          rewrite (vmb_mem _ _ _ _ Hv') in HMj; injection HMj as <-.
          apply (mk_okr_at _ _ _ _ _ _ _ _ Ee2).
          eapply (ntele_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI);
            [ exact (ntele_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ He2) |].
          eapply (ntele_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI); [| exact Hbg' ].
          exact (ntele_rel_of p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ (vmb_mem _ _ _ _ Hv') Hidx).
        + exact (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ HMj Hg Hbgt Hbgt').
      - (* a domain of a shape *)
        intros k pre B' u u' pre' t3 f f' Hr IH Hu Hu' Mi' v Mv c gs1' t' gs2' gs1 t gs2 ms ms' vp vp' d ys ys'
          HM Hv Hc' Hc Hcorr1 Hm Hdep Hlp Hlp' Hsk Hly Hly' Hd Hpre Hpre' Hms Hpw Hpy.
        destruct (ptyp_skip_pi _ _ _ _ (eq_sym Hsk)) as (HB' & Hsk3).
        assert (Hdl : d < List.length (ptyp_doms t)) by (unfold ptyp_depth in Hdep; rewrite <- Hdep; apply List.nth_error_Some; congruence).
        destruct (ptyp_skip_lt d t Hdl) as (B & HB & Hskt).
        rewrite Hskt; apply rec_arg_pi; intros c0 c0' Hcc.
        pose proof (HD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hv Hc' Hc Hcorr1 Hlp Hlp' HB' HB Hms Hpw Hpy) as E.
        apply (proj2 (E _ _)) in Hcc.
        subst pre pre'.
        pose proof (IH _ _ Hcc Hu Hu' Mi' v Mv c gs1' t' gs2' gs1 t gs2 ms ms' vp vp' (S d) (ys ++ c0 :: nil) (ys' ++ c0' :: nil)
                      HM Hv Hc' Hc Hcorr1 Hm Hdep Hlp Hlp' (eq_sym Hsk3)
                      ltac:(rewrite List.length_app; cbn; lia) ltac:(rewrite List.length_app; cbn; lia)
                      ltac:(unfold ptyp_depth; assert (d < List.length (ptyp_doms t')) by (apply List.nth_error_Some; congruence); lia)
                      ltac:(rewrite <- !List.app_assoc; reflexivity) ltac:(rewrite <- !List.app_assoc; reflexivity) Hms Hpw) as H.
        rewrite !app_assoc_3; apply H.
        apply tele_prefix_rel_snoc; [ exact Hpy |].
        unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB'); exact Hcc.
      - (* an application of a shape *)
        intros f a r f' a' r' k u u' pre pre' t'' Ef Ef' Hr IH Hu Hu' * HM Hv Hc' Hc Hcorr1 Hm Hdep Hlp Hlp' Hsk Hly Hly' Hd Hpre Hpre' Hms Hpw Hpy.
        econstructor; [ exact Ef | exact Ef' |].
        eapply IH; eassumption.
    Qed.

    Corollary view_container_to_group : forall i' Mi' v Mv ns ns' x y, ind_member Dq i' = Some Mi' -> view_member i' Mi' v Mv ->
        C i' cups cups' ns ns' x y -> G v ups ups' ns ns' x y.
    Proof. intros * _ Hv H; exact (proj1 view_container_to_group_all _ _ _ _ _ _ _ H eq_refl eq_refl _ (vmb_v _ _ _ _ Hv)). Qed.

    (** ** From the Group's to the Container's

        Conversely, an element of the group at a view is one of the
        container: neither relation puts a condition on a neutral's
        annotation (model P). *)
    Section From.

      Theorem view_group_to_container_all :
        (forall w u u' ns ns' x y, G w u u' ns ns' x y -> u = ups -> u' = ups' ->
           forall i' Mi' Mw, ind_member Dq i' = Some Mi' -> view_member i' Mi' w Mw -> C i' cups cups' ns ns' x y) /\
        (forall w u u' pre pre' gs vs vs', GA w u u' pre pre' gs vs vs' -> u = ups -> u' = ups' ->
           forall i' Mi' Mw c gs1' gs1 gs' ms ms' vp vp',
             ind_member Dq i' = Some Mi' -> view_member i' Mi' w Mw ->
             ind_con Mi' c = Some (gs1' ++ gs') -> ind_con Mw c = Some (gs1 ++ gs) ->
             cargs_corr vm gs1' gs1 -> cargs_corr vm gs' gs ->
             List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
             pre = ms ++ nonrec_arg_vals gs1 vp -> pre' = ms' ++ nonrec_arg_vals gs1 vp' ->
             tele_rel (nr' i') (List.rev (im_nparams Mi')) ms ms' ->
             tele_prefix_rel (ar' i' ms c) (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp') ->
             tele_rel_from (ar w ms c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vp)
               (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') ->
             CA i' cups cups' (ms ++ nonrec_arg_vals gs1' vp) (ms' ++ nonrec_arg_vals gs1' vp') gs' vs vs' /\
             tele_rel_from (ar' i' ms c) (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp)
               (nonrec_arg_vals gs' vs) (nonrec_arg_vals gs' vs')) /\
        (forall w u u' pre pre' t'' x y, GR w u u' pre pre' t'' x y -> u = ups -> u' = ups' ->
           forall i' Mi' Mw c gs1' t' gs2' gs1 t gs2 ms ms' vp vp' d ys ys',
             ind_member Dq i' = Some Mi' -> view_member i' Mi' w Mw ->
             ind_con Mi' c = Some (gs1' ++ ca_rec t' :: gs2') -> ind_con Mw c = Some (gs1 ++ ca_rec t :: gs2) ->
             cargs_corr vm gs1' gs1 -> List.nth_error vm (ptyp_mem t') = Some (ptyp_mem t) -> ptyp_depth t' = ptyp_depth t ->
             List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
             t'' = ptyp_skip d t -> List.length ys = d -> List.length ys' = d -> d <= ptyp_depth t' ->
             pre = ms ++ nonrec_arg_vals gs1 vp ++ ys -> pre' = ms' ++ nonrec_arg_vals gs1 vp' ++ ys' ->
             tele_rel (nr' i') (List.rev (im_nparams Mi')) ms ms' ->
             tele_prefix_rel (ar' i' ms c) (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp') ->
             tele_prefix_rel (shape_doms_rel (dr' i') ms (nonrec_arg_vals gs1' vp) (ptyp_doms t')) d ys ys' ->
             CR i' cups cups' (ms ++ nonrec_arg_vals gs1' vp ++ ys) (ms' ++ nonrec_arg_vals gs1' vp' ++ ys') (ptyp_skip d t') x y) /\
        (forall w u u' pre pre' t'' f a f' a', GP w u u' pre pre' t'' f a f' a' -> u = ups -> u' = ups' ->
           forall i' Mi' Mw c gs1' t' gs2' gs1 t gs2 ms ms' vp vp' d ys ys',
             ind_member Dq i' = Some Mi' -> view_member i' Mi' w Mw ->
             ind_con Mi' c = Some (gs1' ++ ca_rec t' :: gs2') -> ind_con Mw c = Some (gs1 ++ ca_rec t :: gs2) ->
             cargs_corr vm gs1' gs1 -> List.nth_error vm (ptyp_mem t') = Some (ptyp_mem t) -> ptyp_depth t' = ptyp_depth t ->
             List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
             t'' = ptyp_skip d t -> List.length ys = d -> List.length ys' = d -> d <= ptyp_depth t' ->
             pre = ms ++ nonrec_arg_vals gs1 vp ++ ys -> pre' = ms' ++ nonrec_arg_vals gs1 vp' ++ ys' ->
             tele_rel (nr' i') (List.rev (im_nparams Mi')) ms ms' ->
             tele_prefix_rel (ar' i' ms c) (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp') ->
             tele_prefix_rel (shape_doms_rel (dr' i') ms (nonrec_arg_vals gs1' vp) (ptyp_doms t')) d ys ys' ->
             CP i' cups cups' (ms ++ nonrec_arg_vals gs1' vp ++ ys) (ms' ++ nonrec_arg_vals gs1' vp' ++ ys') (ptyp_skip d t') f a f' a').
      Proof.
        apply ind_rel_mut_ind_all.
        - (* a constructor *)
          intros k Mk hd k' ns ns' c gs bs bs' vs vs' u u' HMk Href Hns Hcon Hlb Hlb' Hs Hs' Hnr Hca IH Hu Hu' i' Mi' Mw HMi Hv.
          rewrite (vmb_mem _ _ _ _ Hv) in HMk; injection HMk as <-.
          destruct (vmb_cons' _ _ _ _ Hv c gs Hcon) as (gs' & Hc' & Hcorr).
          pose proof (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hca) as [Hlv Hlv'].
          pose proof (cargs_corr_len _ _ _ Hcorr) as Hlg.
          assert (Hms : tele_rel (nr k) (List.rev (im_nparams Mw)) (List.skipn (im_unu D Mw) bs) (List.skipn (im_unu D Mw) bs')).
          { eapply (nparams_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mw (vmb_mem _ _ _ _ Hv));
              [ exact (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mw (vmb_mem _ _ _ _ Hv) _ _ Hs) |].
            exact (nparams_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mw (vmb_mem _ _ _ _ Hv) _ _ _ Hns Hs'). }
          rewrite (vmb_unu _ _ _ _ Hv) in Hlb, Hlb', Hs, Hs', Hnr, Hca, Hms, IH.
          rewrite (vmb_nn _ _ _ _ Hv) in Hlb, Hlb'.
          pose proof (nr_from _ _ _ _ _ _ HMi Hv Hms) as Hms'.
          destruct Hnr as [_ Hnr].
          pose proof (IH Hu Hu' i' Mi' Mw c nil nil gs' (List.skipn (im_unu Dq Mi') bs) (List.skipn (im_unu Dq Mi') bs') nil nil
                        HMi Hv Hc' Hcon I Hcorr eq_refl eq_refl ltac:(cbn; rewrite List.app_nil_r; reflexivity)
                        ltac:(cbn; rewrite List.app_nil_r; reflexivity) Hms' (tele_prefix_rel_nil _) Hnr) as [Hca' Hnr'].
          cbn [nonrec_arg_vals] in Hca'; rewrite !List.app_nil_r in Hca'.
          rewrite (vmb_ref _ _ _ _ Hv) in Href.
          eapply ind_rel_con with (Mk := Mi') (gs := gs');
            [ exact HMi | exact Href | exact (nr_from _ _ _ _ _ _ HMi Hv Hns) | exact Hc' | exact Hlb | exact Hlb'
            | exact (nr_from _ _ _ _ _ _ HMi Hv Hs) | exact (nr_from _ _ _ _ _ _ HMi Hv Hs') | | exact Hca' ].
          split; [ rewrite length_nonrec_arg_vals by lia; reflexivity | exact Hnr' ].
        - (* a neutral *)
          intros k Mk hd k' ns ns' as1 as2 m m' u u' HMk Href Hns Hl1 Hl2 Hs Hs' Hm Hu Hu' i' Mi' Mw HMi Hv.
          rewrite (vmb_mem _ _ _ _ Hv) in HMk; injection HMk as <-.
          rewrite (vmb_unu _ _ _ _ Hv) in Hl1, Hl2, Hs, Hs'; rewrite (vmb_nn _ _ _ _ Hv) in Hl1, Hl2.
          rewrite (vmb_ref _ _ _ _ Hv) in Href.
          eapply ind_rel_neut with (Mk := Mi');
            [ exact HMi | exact Href | exact (nr_from _ _ _ _ _ _ HMi Hv Hns)
            | exact Hl1 | exact Hl2 | exact (nr_from _ _ _ _ _ _ HMi Hv Hs) | exact (nr_from _ _ _ _ _ _ HMi Hv Hs')
            | exact Hm ].
        - (* no argument *)
          intros k u u' pre pre' Hu Hu' * _ _ _ _ _ Hcorr _ _ _ _ _ _ _.
          destruct gs'; [ split; [ constructor | exact I ] | destruct c0; contradiction ].
        - (* a non-recursive argument of the group's *)
          intros k u u' pre x pre' x' gs vs vs' A Hrest IH Hu Hu' i' Mi' Mw c gs1' gs1 gs' ms ms' vp vp'
            HM Hv Hc' Hc Hcorr1 Hcorr Hlp Hlp' Hpre Hpre' Hms Hpw Hfr.
          destruct gs' as [| [A' | t'] gs0']; cbn in Hcorr; try contradiction.
          assert (Hlc : List.length vp = List.length gs1') by (rewrite Hlp; symmetry; exact (cargs_corr_len _ _ _ Hcorr1)).
          assert (Hlc' : List.length vp' = List.length gs1') by (rewrite Hlp'; symmetry; exact (cargs_corr_len _ _ _ Hcorr1)).
          cbn [nonrec_arg_vals tele_rel_from] in Hfr; destruct Hfr as [Hx Hfr].
          pose proof (proj2 (HA _ _ _ _ _ _ _ _ _ _ _ _ ms' _ vp' _ _ HM Hv Hc' Hc Hcorr1 Hlp Hlp' Hms Hpw) Hx) as Hx'.
          assert (Hnv : forall gs1x Ax w w', List.length w = List.length gs1x ->
                     nonrec_arg_vals (gs1x ++ ca_arg Ax :: nil) (w ++ w' :: nil) = nonrec_arg_vals gs1x w ++ w' :: nil)
            by (intros; rewrite nonrec_arg_vals_app by lia; reflexivity).
          assert (Hln : forall gs1x Ax, List.length (cargs_nonrec (gs1x ++ ca_arg Ax :: nil)) = S (List.length (cargs_nonrec gs1x)))
            by (intros; rewrite cargs_nonrec_app, List.length_app; cbn; lia).
          assert (Hk' : List.length (nonrec_arg_vals gs1' vp) = List.length (cargs_nonrec gs1'))
            by exact (length_nonrec_arg_vals _ _ Hlc).
          pose proof (IH Hu Hu' i' Mi' Mw c (gs1' ++ ca_arg A' :: nil) (gs1 ++ ca_arg A :: nil) gs0' ms ms' (vp ++ x :: nil) (vp' ++ x' :: nil)
                        HM Hv ltac:(rewrite <- List.app_assoc; exact Hc') ltac:(rewrite <- List.app_assoc; exact Hc)
                        (cargs_corr_app _ _ _ (ca_arg A' :: nil) (ca_arg A :: nil) Hcorr1 I) Hcorr
                        ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                        ltac:(rewrite Hnv, Hpre, <- List.app_assoc by lia; reflexivity)
                        ltac:(rewrite Hnv, Hpre', <- List.app_assoc by lia; reflexivity) Hms
                        ltac:(rewrite Hln, !Hnv by lia; apply tele_prefix_rel_snoc; [ exact Hpw | exact Hx' ])
                        ltac:(rewrite Hln, Hnv by lia; exact Hfr)) as [Hca Hfr'].
          rewrite !Hnv in Hca by lia; rewrite Hln, !Hnv in Hfr' by lia.
          split; [ apply con_args_arg; rewrite <- !List.app_assoc; exact Hca | split; [ exact Hx' | exact Hfr' ] ].
        - (* a recursive argument of the group's *)
          intros k u u' pre pre' t x x' gs vs vs' Hr IHr Hrest IH Hu Hu' i' Mi' Mw c gs1' gs1 gs' ms ms' vp vp'
            HM Hv Hc' Hc Hcorr1 Hcorr Hlp Hlp' Hpre Hpre' Hms Hpw Hfr.
          assert (Hlc : List.length vp = List.length gs1') by (rewrite Hlp; symmetry; exact (cargs_corr_len _ _ _ Hcorr1)).
          assert (Hlc' : List.length vp' = List.length gs1') by (rewrite Hlp'; symmetry; exact (cargs_corr_len _ _ _ Hcorr1)).
          assert (Hk' : List.length (nonrec_arg_vals gs1' vp) = List.length (cargs_nonrec gs1'))
            by exact (length_nonrec_arg_vals _ _ Hlc).
          assert (HnvR : forall gs1x tx w w', List.length w = List.length gs1x ->
                     nonrec_arg_vals (gs1x ++ ca_rec tx :: nil) (w ++ w' :: nil) = nonrec_arg_vals gs1x w)
            by (intros; rewrite nonrec_arg_vals_app by lia; cbn; apply List.app_nil_r).
          assert (HlnR : forall gs1x tx, List.length (cargs_nonrec (gs1x ++ ca_rec tx :: nil)) = List.length (cargs_nonrec gs1x))
            by (intros; rewrite cargs_nonrec_app, List.length_app; cbn; lia).
          assert (Hnv : forall gs1x Ax w w', List.length w = List.length gs1x ->
                     nonrec_arg_vals (gs1x ++ ca_arg Ax :: nil) (w ++ w' :: nil) = nonrec_arg_vals gs1x w ++ w' :: nil)
            by (intros; rewrite nonrec_arg_vals_app by lia; reflexivity).
          assert (Hln : forall gs1x Ax, List.length (cargs_nonrec (gs1x ++ ca_arg Ax :: nil)) = S (List.length (cargs_nonrec gs1x)))
            by (intros; rewrite cargs_nonrec_app, List.length_app; cbn; lia).
          cbn [nonrec_arg_vals] in Hfr.
          destruct gs' as [| [A' | t'] gs0']; cbn in Hcorr; try contradiction.
          + (* the view nests through it *)
            subst pre pre' u u'.
            pose proof (proj2 (HR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hv Hc' Hc Hcorr1 Hlp Hlp' Hms Hpw) Hr) as Hx'.
            pose proof (IH eq_refl eq_refl i' Mi' Mw c (gs1' ++ ca_arg A' :: nil) (gs1 ++ ca_rec t :: nil) gs0' ms ms' (vp ++ x :: nil) (vp' ++ x' :: nil)
                          HM Hv ltac:(rewrite <- List.app_assoc; exact Hc') ltac:(rewrite <- List.app_assoc; exact Hc)
                          (cargs_corr_app _ _ _ (ca_arg A' :: nil) (ca_rec t :: nil) Hcorr1 I) Hcorr
                          ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                          ltac:(rewrite HnvR by lia; reflexivity) ltac:(rewrite HnvR by lia; reflexivity) Hms
                          ltac:(rewrite Hln, !Hnv by lia; apply tele_prefix_rel_snoc; [ exact Hpw | exact Hx' ])
                          ltac:(rewrite HlnR, HnvR by lia; exact Hfr)) as [Hca Hfr'].
            rewrite !Hnv in Hca by lia; rewrite Hln, !Hnv in Hfr' by lia.
            split; [ apply con_args_arg; rewrite <- !List.app_assoc; exact Hca | split; [ exact Hx' | exact Hfr' ] ].
          + (* recursive in the container too *)
            destruct Hcorr as (Hm & Hd & Hcorr).
            pose proof (IHr Hu Hu' i' Mi' Mw c gs1' t' gs0' gs1 t gs ms ms' vp vp' 0 nil nil HM Hv Hc' Hc Hcorr1 Hm Hd Hlp Hlp'
                          eq_refl eq_refl eq_refl ltac:(lia) ltac:(rewrite Hpre, List.app_nil_r; reflexivity)
                          ltac:(rewrite Hpre', List.app_nil_r; reflexivity) Hms Hpw (tele_prefix_rel_nil _)) as Hr'.
            rewrite !List.app_nil_r in Hr'.
            pose proof (IH Hu Hu' i' Mi' Mw c (gs1' ++ ca_rec t' :: nil) (gs1 ++ ca_rec t :: nil) gs0' ms ms' (vp ++ x :: nil) (vp' ++ x' :: nil)
                          HM Hv ltac:(rewrite <- List.app_assoc; exact Hc') ltac:(rewrite <- List.app_assoc; exact Hc)
                          (cargs_corr_app _ _ _ (ca_rec t' :: nil) (ca_rec t :: nil) Hcorr1 (conj Hm (conj Hd I))) Hcorr
                          ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                          ltac:(rewrite HnvR by lia; exact Hpre) ltac:(rewrite HnvR by lia; exact Hpre') Hms
                          ltac:(rewrite HlnR, !HnvR by lia; exact Hpw) ltac:(rewrite HlnR, HnvR by lia; exact Hfr)) as [Hca Hfr'].
            rewrite !HnvR in Hca by lia; rewrite HlnR, !HnvR in Hfr' by lia.
            split; [ apply con_args_rec; [ exact Hr' | exact Hca ] | exact Hfr' ].
        - (* the end of a shape *)
          intros Ps u pre bs u' pre' bs' j x x' k Ebs Ebs' Ho Ho' Hi IH Hu Hu' i' Mi' Mw c gs1' t' gs2' gs1 t gs2 ms ms' vp vp' d ys ys'
            HM Hv Hc' Hc Hcorr1 Hm Hdep Hlp Hlp' Hsk Hly Hly' Hd Hpre Hpre' Hms Hpw Hpy.
          subst u u'.
          destruct (ptyp_skip_self _ _ _ _ (eq_sym Hsk)) as (Hle & Hj & HPs); subst j Ps.
          unfold ptyp_depth in Hd, Hdep.
          assert (Hdd : d = List.length (ptyp_doms t')) by lia.
          assert (Hskt : ptyp_skip d t' = pt_self (ptyp_mem t') (ptyp_ps t')) by (rewrite Hdd; apply ptyp_skip_end).
          rewrite Hskt; rewrite Hdd in Hpy.
          pose proof (tele_rel_of_pre _ (ptyp_doms t') _ _ Hpy) as Hpy'.
          destruct (HP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hv Hc' Hc Hcorr1 Hlp Hlp' Hms Hpw Hpy') as (HL & HRt & HX).
          subst pre pre'.
          destruct HL as [bsc e Ebsc Ee Hbg]; pose proof (functional_eval_exps' _ _ _ _ Ee Ebs) as ->.
          destruct HRt as [bsc' e' Ebsc' Ee' Hbg']; pose proof (functional_eval_exps' _ _ _ _ Ee' Ebs') as ->.
          destruct (Hrm _ _ _ _ _ _ HM Hc') as (Mj' & HMj').
          destruct (Hmem _ _ HMj') as (v' & Mv' & Hv').
          assert (v' = ptyp_mem t) as -> by (rewrite (vmb_v _ _ _ _ Hv') in Hm; congruence).
          pose proof (IH eq_refl eq_refl _ _ _ HMj' Hv') as Hg.
          assert (Hsym : forall a b, ntele_rel D nr (ptyp_mem t) a b -> tele_rel (nr' (ptyp_mem t')) (List.rev (im_nparams Mj')) b a).
          { intros a b H; apply (nr_from _ _ _ _ _ _ HMj' Hv').
            pose proof (ntele_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ H) as H'.
            unfold ntele_rel in H'; rewrite (vmb_mem _ _ _ _ Hv') in H'; exact H'. }
          eapply rec_arg_self; [ exact Ebsc | exact Ebsc' | | | ].
          + apply (mk_okr_at _ _ _ _ _ _ _ _ Ebsc); unfold ntele_rel; rewrite HMj'.
            exact (nparams_rel_refl_r qc Dq cups nr' ar' dr' Hass' HnP' HnI' HaP' HaI' HdP' HdI' _ _ HMj' _ _ (Hsym _ _ Hbg)).
          + destruct HX as [e1 e2 Ee1 Ee2 He2].
            destruct Ho' as [idx Eidx Hidx]; pose proof (functional_eval_exps' _ _ _ _ Eidx Ee2) as <-.
            apply (mk_okr_at _ _ _ _ _ _ _ _ Ee1); unfold ntele_rel; rewrite HMj'.
            apply Hsym.
            eapply (ntele_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI); [ exact Hbg' |].
            eapply (ntele_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI); [ exact (ntele_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ Hidx) |].
            exact (ntele_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ He2).
          + exact (ind_rel_idx qc Dq cups nr' ar' dr' Hass' HnP' HnI' HaP' HaI' HdP' HdI' _ _ _ _ _ _ _ _ _ _ _ HMj' Hg
                     (Hsym _ _ Hbg) (Hsym _ _ Hbg')).
        - (* a domain of a shape *)
          intros k pre B u u' pre' t3 f f' Hr IH Hu Hu' i' Mi' Mw c gs1' t' gs2' gs1 t gs2 ms ms' vp vp' d ys ys'
            HM Hv Hc' Hc Hcorr1 Hm Hdep Hlp Hlp' Hsk Hly Hly' Hd Hpre Hpre' Hms Hpw Hpy.
          destruct (ptyp_skip_pi _ _ _ _ (eq_sym Hsk)) as (HB & Hsk3).
          assert (Hdl : d < List.length (ptyp_doms t')) by (unfold ptyp_depth in Hdep; rewrite Hdep; apply List.nth_error_Some; congruence).
          destruct (ptyp_skip_lt d t' Hdl) as (B' & HB' & Hskt).
          rewrite Hskt; apply rec_arg_pi; intros c0 c0' Hcc.
          pose proof (HD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hv Hc' Hc Hcorr1 Hlp Hlp' HB' HB Hms Hpw Hpy) as E.
          pose proof (proj1 (E _ _) Hcc) as Hcc'.
          subst pre pre'.
          pose proof (IH _ _ Hcc' Hu Hu' i' Mi' Mw c gs1' t' gs2' gs1 t gs2 ms ms' vp vp' (S d) (ys ++ c0 :: nil) (ys' ++ c0' :: nil)
                        HM Hv Hc' Hc Hcorr1 Hm Hdep Hlp Hlp' (eq_sym Hsk3)
                        ltac:(rewrite List.length_app; cbn; lia) ltac:(rewrite List.length_app; cbn; lia)
                        ltac:(unfold ptyp_depth; lia)
                        ltac:(rewrite <- !List.app_assoc; reflexivity) ltac:(rewrite <- !List.app_assoc; reflexivity) Hms Hpw) as H.
          rewrite !app_assoc_3; apply H.
          apply tele_prefix_rel_snoc; [ exact Hpy |].
          unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB'); exact Hcc.
        - (* an application of a shape *)
          intros f a r f' a' r' k u u' pre pre' t'' Ef Ef' Hr IH Hu Hu' * HM Hv Hc' Hc Hcorr1 Hm Hdep Hlp Hlp' Hsk Hly Hly' Hd Hpre Hpre' Hms Hpw Hpy.
          econstructor; [ exact Ef | exact Ef' |].
          eapply IH; eassumption.
      Qed.

      Corollary view_group_to_container : forall i' Mi' v Mv ns ns' x y, ind_member Dq i' = Some Mi' -> view_member i' Mi' v Mv ->
          G v ups ups' ns ns' x y -> C i' cups cups' ns ns' x y.
      Proof. intros * HM Hv H; exact (proj1 view_group_to_container_all _ _ _ _ _ _ _ H eq_refl eq_refl _ _ _ HM Hv). Qed.
    End From.
  End ViewCoh.
End Fixed_GCtx.
