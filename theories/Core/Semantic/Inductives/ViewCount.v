(** * The Leaf Paths of a View the Container Has

    A view of a container's member, under its map [vm], has the
    container's leaf paths among its own: of a shape [t] of the group [D]
    against the container's corresponding shape [t'] ([shape_corr]), the
    group's leaf paths that are the container's ([leaf_in]) are as many as
    the container's own ([leaves_in_count_view]), and over a constructor's
    arguments as many as the container's branch binds ([cargs_nin_view]).
    Readback reads a stuck eliminator at a view as the container's and asks
    this count of each branch ([read_brs_cons]); the eliminator's model
    ([IndElim]) and completeness give it. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Semantic.Inductives Require Import ViewCoherence.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** The Shapes of a View against its Container's

    A shape [t'] of the container's against the view's [t]: as many
    domains, ending in a member the view's map takes to [t]'s ([cargs_corr]
    at a recursive argument). *)
Fixpoint shape_corr (vm : list nat) (t' t : ptyp) : Prop :=
  match t', t with
  | pt_self j' _, pt_self j _ => List.nth_error vm j' = Some j
  | pt_pi _ t1', pt_pi _ t1 => shape_corr vm t1' t1
  | _, _ => False
  end.

Lemma shape_corr_of : forall vm t' t, List.nth_error vm (ptyp_mem t') = Some (ptyp_mem t) -> ptyp_depth t' = ptyp_depth t ->
    shape_corr vm t' t.
Proof.
  intros vm t'; induction t' as [j' Ps' | B' t' IH]; intros [j Ps | B t] Hm Hd; unfold ptyp_depth in Hd; cbn in *;
    try discriminate; [ exact Hm | apply IH; [ exact Hm | unfold ptyp_depth; lia ] ].
Qed.

(** ** The Members a View Takes the Container's To

    The field [agree_members] of [view_agreement]: syntactic, from the group's
    conditions ([grp_tele_ass_vwrap], [grp_tele_ass_vm], [grp_tele_ass_views]). *)
Lemma view_agree_members : forall p D k Mk qc k' Is vm Dq, grp_tele_ass D ->
    ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq ->
    forall i' Mi', ind_member Dq i' = Some Mi' -> exists v Mv, view_member p D qc Dq vm i' Mi' v Mv.
Proof.
  intros * Hass HMk Hh HDq i' Mi' HMi'.
  destruct (grp_tele_ass_vwrap _ Hass _ _ _ _ _ _ HMk Hh) as (D' & HD' & Hvw).
  rewrite HDq in HD'; injection HD' as <-.
  destruct (grp_tele_ass_vm _ Hass _ _ _ _ _ _ _ _ _ HMk Hh HDq HMi') as [v Mv Hv HMv Hnn Hhead].
  destruct (grp_tele_ass_views _ Hass _ _ _ _ _ _ HMk Hh) as (Dq' & Mc & HDq' & _ & _ & HlIs).
  rewrite HDq in HDq'; injection HDq' as <-.
  destruct (vwrap_ok_members _ _ _ Hvw _ _ _ HMi' Hv) as (Mv' & HMv' & _ & Hnames & Hcorr).
  rewrite HMv in HMv'; injection HMv' as <-.
  exists v, Mv.
  assert (Hc1 : forall c gs', ind_con Mi' c = Some gs' -> exists gs, ind_con Mv c = Some gs /\ cargs_corr vm gs' gs).
  { intros c gs' Hc.
    pose proof (cons_lookup_in _ _ _ Hc) as Hin.
    assert (Hn : List.In c (List.map fst (im_cons Mv))) by (rewrite Hnames; exact (List.in_map fst _ (c, gs') Hin)).
    apply List.in_map_iff in Hn; destruct Hn as ([c0 gs0] & Ec & Hin0); cbn in Ec; subst c0.
    destruct (cons_lookup_of_in _ _ _ Hin0) as [gs HCv].
    exists gs; split; [ exact HCv | exact (Hcorr c gs' gs Hin HCv) ]. }
  assert (Hc2 : forall c gs, ind_con Mv c = Some gs -> exists gs', ind_con Mi' c = Some gs' /\ cargs_corr vm gs' gs).
  { intros c gs Hc.
    pose proof (cons_lookup_in _ _ _ Hc) as Hin.
    assert (Hn : List.In c (List.map fst (im_cons Mi'))) by (rewrite <- Hnames; exact (List.in_map fst _ (c, gs) Hin)).
    apply List.in_map_iff in Hn; destruct Hn as ([c0 gs0] & Ec & Hin0); cbn in Ec; subst c0.
    destruct (cons_lookup_of_in _ _ _ Hin0) as [gs' HCi].
    exists gs'; split; [ exact HCi | exact (Hcorr c gs' gs (cons_lookup_in _ _ _ HCi) Hc) ]. }
  destruct (im_head Mi') as [pm' | qv kv Is'' vm'' | qr Is'' fl''] eqn:Hh'.
  - destruct Hhead as [vm' Hhv].
    refine (mk_view_member _ _ _ _ _ _ _ _ _ Hv HMv _ _ _ _ Hnames Hnn Hc1 Hc2).
    + unfold im_is_rview; rewrite Hhv, Hh'; reflexivity.
    + intros _; unfold im_ref; rewrite Hhv, Hh'; reflexivity.
    + intros _; unfold im_unu; rewrite Hhv, Hh'; exact HlIs.
    + intros * E; rewrite Hh' in E; discriminate E.
  - destruct Hhead as (Is' & vm' & Hhv & HlI).
    refine (mk_view_member _ _ _ _ _ _ _ _ _ Hv HMv _ _ _ _ Hnames Hnn Hc1 Hc2).
    + unfold im_is_rview; rewrite Hhv, Hh'; reflexivity.
    + intros _; unfold im_ref; rewrite Hhv, Hh'; reflexivity.
    + intros _; unfold im_unu; rewrite Hhv, Hh'; exact HlI.
    + intros * E; rewrite Hh' in E; discriminate E.
  - destruct Hhead as (Is' & Hhv & _).
    refine (mk_view_member _ _ _ _ _ _ _ _ _ Hv HMv _ _ _ _ Hnames Hnn Hc1 Hc2).
    + unfold im_is_rview; rewrite Hhv, Hh'; reflexivity.
    + intros Hr; unfold im_is_rview in Hr; rewrite Hh' in Hr; discriminate Hr.
    + intros Hr; unfold im_is_rview in Hr; rewrite Hh' in Hr; discriminate Hr.
    + intros qr0 Is0 fl0 E; rewrite Hh' in E; injection E as <- <- <-; exists Is'; exact Hhv.
Qed.

(** Each instance [vm] maps, of a member of the container's group, to the
    member of the group it takes it to. *)
Lemma view_members_of_ass : forall p D k Mk qc k' Is vm Dq, grp_tele_ass D ->
    ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq ->
    forall j' j, List.nth_error vm j' = Some j ->
      exists Mj' Mj, ind_member Dq j' = Some Mj' /\ view_member p D qc Dq vm j' Mj' j Mj.
Proof.
  intros * Hass HMk Hh Hq j' j Hv.
  destruct (grp_tele_ass_vwrap _ Hass _ _ _ _ _ _ HMk Hh) as (D2 & Hq2 & Hvw).
  rewrite Hq in Hq2; injection Hq2 as <-.
  assert (Hi : j' < List.length (ind_members Dq)) by (rewrite <- (vwrap_ok_length _ _ _ Hvw); apply List.nth_error_Some; congruence).
  destruct (List.nth_error (ind_members Dq) j') as [Mj' |] eqn:HMj'; [| apply List.nth_error_None in HMj'; lia ].
  destruct (view_agree_members p D k Mk qc k' Is vm Dq Hass HMk Hh Hq j' Mj' HMj') as (v & Mv & Hvm).
  pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvm) as Hv'; rewrite Hv in Hv'; injection Hv' as <-.
  exists Mj', Mv; split; [ exact HMj' | exact Hvm ].
Qed.

(** ** A Group's Own Leaf Paths

    Every leaf path of a shape of the group is the group's own
    ([leaf_in]), and so a branch read as its own group's binds as many
    recursive results as the group's ([cargs_nin_own_of_ass]). *)
Lemma own_leaves_of_ass : forall D, grp_tele_ass D -> forall t m l, (exists M, ind_member D (ptyp_mem t) = Some M) ->
    In l (shape_leaves (rv_leaves D) m t) -> leaf_in D t l = true.
Proof.
  intros D Hass.
  pose proof (grp_tele_ass_rstruct _ Hass) as Hrs.
  apply (leaf_in_own D (leaves_coherent_of_order D (rview_struct_order _ _ _ Hrs))).
  - intros * HM Hh.
    destruct (rview_struct_record _ _ _ Hrs _ _ _ _ _ HM Hh) as [R HR].
    destruct (rview_struct_con _ _ _ Hrs _ _ _ _ _ HM Hh) as (gs & Hcs & Hlen).
    split; [ exact (rview_record_nodup _ _ _ _ _ _ HR) | exists rview_con, gs; split; [ exact Hcs | lia ] ].
  - intros * HM Hh Hcs.
    destruct (grp_tele_ass_plen _ Hass _ _ _ _ HM ltac:(rewrite Hcs; left; reflexivity) gs1 t gs2 eq_refl) as (M & HM' & _).
    exists M; exact HM'.
Qed.

Lemma cargs_nin_own_of_ass : forall D, grp_tele_ass D -> forall gs, cargs_plen D gs -> cargs_nin D D gs gs = cargs_nrec D gs.
Proof.
  intros D Hass; induction gs as [| [A | t] gs IH]; intros Hpl; cbn [cargs_nin cargs_nrec]; [ reflexivity | |].
  - apply IH; intros gs1 t gs2 E; apply (Hpl (ca_arg A :: gs1) t gs2); rewrite E; reflexivity.
  - f_equal.
    + destruct (Hpl nil t gs eq_refl) as (M & HM & _).
      unfold leaves_in_count.
      assert (Hall : forall ls, (forall l, List.In l ls -> leaf_in D t l = true) ->
                       List.length (List.filter (leaf_in D t) ls) = List.length ls).
      { induction ls as [| l ls IHl]; intros Hin; [ reflexivity |]; cbn.
        rewrite (Hin l (or_introl eq_refl)); cbn; rewrite IHl; [ reflexivity |].
        intros; apply Hin; right; assumption. }
      apply Hall; intros l Hin; exact (own_leaves_of_ass D Hass t 0 l (ex_intro _ M HM) Hin).
    + apply IH; intros gs1 t' gs2 E; apply (Hpl (ca_rec t :: gs1) t' gs2); rewrite E; reflexivity.
Qed.

(** ** The Count

    The group [D] at [p], a view of whose members has the container [D']
    at [qc] and the map [vm], each member of the container's group taken to
    one of the group's of the same kind, a record view to one of the same
    record and fields ([view_member]); both groups' tables coherent. *)
Section ViewCount.
  Variables (p qc : qname) (D D' : ind_decl) (vm : list nat).
  Hypotheses (HlcD : leaves_coherent D) (HlcQ : leaves_coherent D')
    (HrsD : rview_struct_ok gc_deps gc_stack D) (HrsQ : rview_struct_ok gc_deps gc_stack D').
  Hypothesis (Hvm : forall j' j, List.nth_error vm j' = Some j ->
                exists Mj' Mj, ind_member D' j' = Some Mj' /\ view_member p D qc D' vm j' Mj' j Mj).

  Lemma leaves_in_count_map_pi : forall B B' t' ls,
      leaves_in_count D' (pt_pi B' t') (List.map (leaf_pi B) ls) = leaves_in_count D' t' ls.
  Proof.
    intros B B' t'; induction ls as [| l ls IH]; [ reflexivity |].
    unfold leaves_in_count in *; cbn [List.map List.filter leaf_in]; destruct (leaf_in D' t' l); cbn; rewrite IH; reflexivity.
  Qed.

  Lemma leaves_in_count_map_wk : forall t' φ ls, leaves_in_count D' t' (List.map (leaf_wk φ) ls) = leaves_in_count D' t' ls.
  Proof.
    intros t' φ; induction ls as [| l ls IH]; [ reflexivity |].
    unfold leaves_in_count in *; cbn [List.map List.filter]; rewrite leaf_in_wk; destruct (leaf_in D' t' l); cbn; rewrite IH; reflexivity.
  Qed.

  Lemma leaves_in_count_app : forall t' ls1 ls2,
      leaves_in_count D' t' (ls1 ++ ls2) = leaves_in_count D' t' ls1 + leaves_in_count D' t' ls2.
  Proof. intros; unfold leaves_in_count; rewrite List.filter_app, List.length_app; reflexivity. Qed.

  (** Of a shape: as many of the group's leaf paths are the container's
      as the container has, by induction on the record views' order. *)
  Lemma leaves_in_count_view : forall n t' t m,
      (forall Mj, ind_member D (ptyp_mem t) = Some Mj -> im_is_rview Mj = true -> ptyp_mem t < n) ->
      shape_corr vm t' t ->
      leaves_in_count D' t' (shape_leaves (rv_leaves D) m t) = List.length (shape_leaves (rv_leaves D') 0 t').
  Proof.
    induction n as [n IHn] using Wf_nat.lt_wf_ind.
    intros t'; induction t' as [j' Ps' | B' t1' IHt]; intros [j Ps | B t1] m Hrk Hsc; cbn in Hsc; try contradiction.
    - (** At the ends: members of one kind. *)
      destruct (Hvm _ _ Hsc) as (Mj' & Mj & HMj' & Hvmb).
      pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMj.
      pose proof (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvmb) as Ervs.
      destruct (im_is_rview Mj) eqn:Hrv.
      + (** Record views: their fields, one by one. *)
        specialize (Hrk Mj HMj Hrv); cbn [ptyp_mem] in Hrk.
        unfold im_is_rview in Ervs; destruct (im_head Mj') as [| | qr Is' fl] eqn:Hh'; try discriminate Ervs.
        destruct (view_member_rview _ _ _ _ _ _ _ _ _ Hvmb _ _ _ Hh') as (Is0 & Hh).
        destruct (rview_struct_con _ _ _ HrsD _ _ _ _ _ HMj Hh) as (gsr & Hcs & Hlen).
        destruct (rview_struct_con _ _ _ HrsQ _ _ _ _ _ HMj' Hh') as (gsr' & Hcs' & Hlen').
        destruct (rview_struct_record _ _ _ HrsQ _ _ _ _ _ HMj' Hh') as [R HR].
        pose proof (rview_record_nodup _ _ _ _ _ _ HR) as Hnd.
        destruct (view_member_cons' _ _ _ _ _ _ _ _ _ Hvmb rview_con gsr
                    ltac:(unfold ind_con; rewrite Hcs; cbn; rewrite ?String.eqb_refl; reflexivity)) as (g0 & Hc0 & Hcorr).
        unfold ind_con in Hc0; rewrite Hcs' in Hc0; cbn in Hc0; rewrite ?String.eqb_refl in Hc0; injection Hc0 as <-.
        cbn [shape_leaves]; rewrite (HlcD _ _ _ _ _ _ _ HMj Hh Hcs), (HlcQ _ _ _ _ _ _ _ HMj' Hh' Hcs').
        rewrite leaves_in_count_map_wk, List.length_map.
        (** The fields after [fs1] and [fs1']. *)
        assert (Hfs : forall fs2 fs2' fs1 fs1' ns ns', List.combine fl gsr = fs1 ++ fs2 -> List.combine fl gsr' = fs1' ++ fs2' ->
                   List.length fs1 = List.length fs1' -> cargs_corr vm (List.map snd fs2') (List.map snd fs2) ->
                   leaves_in_count D' (pt_self j' Ps') (fields_leaves (rv_leaves D) ns fs2)
                   = List.length (fields_leaves (rv_leaves D') ns' fs2')).
        { induction fs2 as [| [f g] fs2 IHf]; intros [| [f' g'] fs2'] fs1 fs1' ns ns' E E' Lf Hco; cbn [List.map cargs_corr] in Hco;
            try (destruct g'; contradiction); try (destruct g; contradiction); [ reflexivity |].
          destruct (combine_app_split _ _ _ _ (eq_sym Hlen) E) as [Efl Egs].
          destruct (combine_app_split _ _ _ _ (eq_sym Hlen') E') as [Efl' Egs'].
          cbn [List.map] in Efl, Efl'.
          assert (Ef : f' = f).
          { assert (Hn1 : List.nth_error fl (List.length fs1) = Some f)
              by (rewrite Efl, List.nth_error_app2 by (rewrite List.length_map; lia); rewrite List.length_map, Nat.sub_diag; reflexivity).
            assert (Hn2 : List.nth_error fl (List.length fs1) = Some f')
              by (rewrite Efl', List.nth_error_app2 by (rewrite List.length_map; lia); rewrite List.length_map, Lf, Nat.sub_diag;
                  reflexivity).
            congruence. }
          subst f'.
          assert (E1 : List.combine fl gsr = (fs1 ++ (f, g) :: nil) ++ fs2) by (rewrite E, <- List.app_assoc; reflexivity).
          assert (E1' : List.combine fl gsr' = (fs1' ++ (f, g') :: nil) ++ fs2') by (rewrite E', <- List.app_assoc; reflexivity).
          assert (L1 : List.length (fs1 ++ (f, g) :: nil) = List.length (fs1' ++ (f, g') :: nil)) by (rewrite !List.length_app; cbn; lia).
          assert (Hfind : List.find (fun fg => String.eqb (fst fg) f) (List.combine fl gsr') = Some (f, g')).
          { rewrite E'; apply find_name_split; rewrite <- E', combine_fst_eq by exact (eq_sym Hlen'); exact Hnd. }
          destruct g as [A | t], g' as [A' | t']; cbn [cargs_corr] in Hco; try contradiction.
          - cbn [fields_leaves]; exact (IHf _ _ _ _ _ E1 E1' L1 Hco).
          - (** Nested through by the group: none of its paths is the
                container's. *)
            cbn [fields_leaves]; rewrite leaves_in_count_app.
            assert (H0 : leaves_in_count D' (pt_self j' Ps') (List.map (leaf_proj f ns) (shape_leaves (rv_leaves D) (List.length ns) t)) = 0).
            { generalize (shape_leaves (rv_leaves D) (List.length ns) t) as ls; intros ls.
              induction ls as [| l ls IHl]; [ reflexivity |].
              unfold leaves_in_count in *; cbn [List.map List.filter leaf_in]; rewrite HMj', Hh', Hcs', Hfind; exact IHl. }
            rewrite H0; exact (IHf _ _ _ _ _ E1 E1' L1 Hco).
          - (** Recursive in both: the field's shapes correspond. *)
            destruct Hco as (Hmt & Hdp & Hco).
            cbn [fields_leaves]; rewrite leaves_in_count_app, List.length_app, List.length_map.
            assert (H0 : leaves_in_count D' (pt_self j' Ps') (List.map (leaf_proj f ns) (shape_leaves (rv_leaves D) (List.length ns) t))
                         = leaves_in_count D' t' (shape_leaves (rv_leaves D) (List.length ns) t)).
            { generalize (shape_leaves (rv_leaves D) (List.length ns) t) as ls; intros ls.
              induction ls as [| l ls IHl]; [ reflexivity |].
              unfold leaves_in_count in *; cbn [List.map List.filter leaf_in]; rewrite HMj', Hh', Hcs', Hfind.
              destruct (leaf_in D' t' l); cbn; rewrite IHl; reflexivity. }
            rewrite H0.
            destruct (combine_split_at _ _ _ _ _ _ (eq_sym Hlen) E) as [_ Egs1].
            assert (Hrk' : forall Mt, ind_member D (ptyp_mem t) = Some Mt -> im_is_rview Mt = true -> ptyp_mem t < j).
            { intros Mt HMt HrT; exact (rview_struct_order _ _ _ HrsD _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs Egs1 HMt HrT). }
            rewrite (IHn j Hrk t' t (List.length ns) Hrk' (shape_corr_of _ _ _ Hmt Hdp)).
            rewrite (length_shape_leaves _ t' 0 (List.length ns')).
            f_equal; exact (IHf _ _ _ _ _ E1 E1' L1 Hco). }
        apply (Hfs (List.combine fl gsr) (List.combine fl gsr') nil nil nil nil eq_refl eq_refl eq_refl).
        rewrite !combine_snd_eq by lia; exact Hcorr.
      + (** Members with a block: one path each. *)
        assert (Hrv' : im_is_rview Mj' = false) by congruence.
        cbn [shape_leaves]; rewrite (rv_leaves_not_rview _ _ _ HMj Hrv), (rv_leaves_not_rview _ _ _ HMj' Hrv').
        unfold leaves_in_count; cbn [List.filter leaf_in]; rewrite HMj', Hrv'; reflexivity.
    - (** Through a domain. *)
      cbn [shape_leaves]; rewrite leaves_in_count_map_pi, List.length_map.
      rewrite (IHt t1 (S m) Hrk Hsc); apply length_shape_leaves.
  Qed.

  (** Of a constructor's arguments: as many as the container's recursive
      results. *)
  Lemma cargs_nin_view : forall gs' gs, cargs_corr vm gs' gs -> cargs_nin D D' gs' gs = cargs_nrec D' gs'.
  Proof.
    induction gs' as [| [A' | t'] gs' IH]; intros [| [A | t] gs] Hco; cbn [cargs_corr] in Hco; try contradiction;
      cbn [cargs_nin cargs_nrec]; try reflexivity; try exact (IH _ Hco).
    destruct Hco as (Hmt & Hdp & Hco).
    rewrite IH by exact Hco; f_equal.
    apply (leaves_in_count_view (S (ptyp_mem t))); [ intros; lia | exact (shape_corr_of _ _ _ Hmt Hdp) ].
  Qed.
End ViewCount.
End Fixed_GCtx.
