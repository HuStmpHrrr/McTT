(** * The Leaf Paths of a View the Container Has

    A view of a container's member, under its map [vm], has the
    container's leaf paths among its own: of a shape [t] of the group [D]
    against the container's corresponding shape [t'] ([shape_correspond]), the
    group's leaf paths that are the container's ([leaf_in]) are as many as
    the container's own ([leaves_in_count_view]), and over a constructor's
    arguments as many as the container's branch binds ([cargs_container_count_view]).
    Readback reads a stuck eliminator at a view as the container's and asks
    this count of each branch ([read_brs_cons]); the eliminator's model
    ([Elim]) and completeness give it. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Semantic.Inductives Require Import ViewCoherence.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The shapes of a view against its container's ([shape_correspond],
    [shape_correspond_of]) are in [Core.Syntactic.Inductives.Inductives]. *)

(** ** The Members a View Takes the Container's To

    The field [agree_members] of [view_agreement]: syntactic, from the group's
    conditions ([group_structure_view_wrap], [group_structure_vm], [group_structure_views]). *)
Lemma view_agree_members : forall p D k Mk qc k' Is vm Dq, group_structure D ->
    ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq ->
    forall i' Mi', ind_member Dq i' = Some Mi' -> exists v Mv, view_member p D qc Dq vm i' Mi' v Mv.
Proof.
  intros * Hass HMk Hh HDq i' Mi' HMi'.
  destruct (group_structure_view_wrap _ Hass _ _ _ _ _ _ HMk Hh) as (D' & HD' & Hvw).
  rewrite HDq in HD'; injection HD' as <-.
  destruct (group_structure_vm _ Hass _ _ _ _ _ _ _ _ _ HMk Hh HDq HMi') as [v Mv Hv HMv Hnn Hhead].
  destruct (group_structure_views _ Hass _ _ _ _ _ _ HMk Hh) as (Dq' & Mc & HDq' & _ & _ & HlIs).
  rewrite HDq in HDq'; injection HDq' as <-.
  exists v, Mv. exact (view_member_of_head p D qc Dq Is vm i' Mi' v Mv Hvw HlIs HMi' Hv HMv Hnn Hhead).
Qed.

(** Each instance [vm] maps, of a member of the container's group, to the
    member of the group it takes it to. *)
Lemma view_members_of_ass : forall p D k Mk qc k' Is vm Dq, group_structure D ->
    ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq ->
    forall j' j, List.nth_error vm j' = Some j ->
      exists Mj' Mj, ind_member Dq j' = Some Mj' /\ view_member p D qc Dq vm j' Mj' j Mj.
Proof.
  intros * Hass HMk Hh Hq j' j Hv.
  destruct (group_structure_view_wrap _ Hass _ _ _ _ _ _ HMk Hh) as (D2 & Hq2 & Hvw).
  rewrite Hq in Hq2; injection Hq2 as <-.
  assert (Hi : j' < List.length (ind_members Dq)) by (rewrite <- (view_wrap_ok_length _ _ _ Hvw); apply List.nth_error_Some; congruence).
  destruct (List.nth_error (ind_members Dq) j') as [Mj' |] eqn:HMj'; [| apply List.nth_error_None in HMj'; lia ].
  destruct (view_agree_members p D k Mk qc k' Is vm Dq Hass HMk Hh Hq j' Mj' HMj') as (v & Mv & Hvm).
  pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvm) as Hv'; rewrite Hv in Hv'; injection Hv' as <-.
  exists Mj', Mv; split; [ exact HMj' | exact Hvm ].
Qed.

(** ** A Group's Own Leaf Paths

    Every leaf path of a shape of the group is the group's own
    ([leaf_in]), and so a branch read as its own group's binds as many
    recursive results as the group's ([cargs_container_count_own_of_ass]). *)
Lemma own_leaves_of_ass : forall D, group_structure D -> forall t m l, (exists M, ind_member D (ptyp_mem t) = Some M) ->
    In l (shape_leaves (rview_leaves D) m t) -> leaf_in D t l = true.
Proof.
  intros D Hass.
  pose proof (group_structure_record_struct _ Hass) as Hrs.
  apply (leaf_in_own D (leaves_coherent_of_order D (rview_struct_order _ _ _ Hrs))).
  - intros * HM Hh.
    destruct (rview_struct_record _ _ _ Hrs _ _ _ _ _ HM Hh) as [R HR].
    destruct (rview_struct_con _ _ _ Hrs _ _ _ _ _ HM Hh) as (gs & Hcs & Hlen).
    split; [ exact (rview_record_nodup _ _ _ _ _ _ HR) | exists rview_con, gs; split; [ exact Hcs | lia ] ].
  - intros * HM Hh Hcs.
    destruct (group_structure_params_length _ Hass _ _ _ _ HM ltac:(rewrite Hcs; left; reflexivity) gs1 t gs2 eq_refl) as (M & HM' & _).
    exists M; exact HM'.
Qed.

Lemma cargs_container_count_own_of_ass : forall D, group_structure D -> forall gs, cargs_params_length D gs -> cargs_container_count D D gs gs = cargs_nrec D gs.
Proof.
  intros D Hass; induction gs as [| [rA A | t] gs IH]; intros Hpl; cbn [cargs_container_count cargs_nrec]; [ reflexivity | |].
  - apply IH; intros gs1 t gs2 E; apply (Hpl (ca_arg rA A :: gs1) t gs2); rewrite E; reflexivity.
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

(** The count of the group's leaf paths the container has
    ([leaves_in_count_view], [cargs_container_count_view]) is in
    [Core.Syntactic.System.Inductives.ViewLeaves]. *)
End Fixed_GCtx.
