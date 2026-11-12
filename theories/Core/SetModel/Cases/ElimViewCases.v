(** * The Set Rule of the Eliminator at a View

    The eliminator of a group [D] at its view [m] of the container's
    declared member [k'] at the instance [Is] is, in the model, the
    container's eliminator at [k'] at the view's blocks wrapped
    ([view_wrap]).  By induction on the group's carriers, the container's
    eliminator at a container's member has, at every element, the group's
    result at the member the view takes it to: at a constructor, the
    wrapped branch is the group's branch at an instance of its context
    whose recursive results are the container's at the container's leaf
    paths and the group's along the others, and the container's are the
    group's ones at the container's paths by the induction. *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Weakening Substitution JudgmentSubstitution.
From Mctt.Core.SetModel.Interpretation.Global Require Import Model.
From Mctt.Core.SetModel.Cases Require Import UniverseCases PropCases FunctionCases ValidUnit MemberTypes Sel IndCases RecordCases
  ElimCases.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members Presup CoreInversions.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths DescTyping MemberLemmas.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing UniformParams Views ViewLeaves.
Import ListNotations.

Section ElimView.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.
  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).
  (** The global context is well formed *)
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  (** The valuation models the global context *)
  Hypothesis Hok : set_gctx_ok T γ.

(** ** The Container's Results Are the Group's *)

Section ContainerResults.
  (** The group's eliminator: its context, environment, sort, group,
      uniform parameters, blocks, the set of its results, the group and
      the level of its motives *)
  Variables (Γ : ctx) (ρ : set_env) (r : abs_kind) (p : qname) (Us : list exp) (Bks : list eblock) (V : aczel_set).
  Variables (D : ind_decl) (i : nat).
  (** The members of the group the view takes the container's to, the
      container's group, its uniform parameters and its blocks *)
  Variables (vm : list nat) (qc : qname) (Is' : list exp) (Bks' : list eblock) (D' : ind_decl).
  (** The container's group is [D'] *)
  Hypothesis HD' : ind_lookup gc_deps gc_stack qc = Some D'.
  (** Both groups' record views are as their declarations say, their
      tables coherent *)
  Hypotheses (HrsD : rview_struct_ok gc_deps gc_stack D) (HrsQ : rview_struct_ok gc_deps gc_stack D').
  (** The view takes each member of the container's group to a member of
      the group ([view_member]) *)
  Hypothesis Hvm : forall j' j, List.nth_error vm j' = Some j ->
    exists Mj' Mj, ind_member D' j' = Some Mj' /\ view_member p D qc D' vm j' Mj' j Mj.

  Let lvalue := leaf_value T γ Γ ρ r p Us Bks V.
  Let HlcD : leaves_coherent D := leaves_coherent_of_order D (rview_struct_order _ _ _ HrsD).
  Let HlcQ : leaves_coherent D' := leaves_coherent_of_order D' (rview_struct_order _ _ _ HrsQ).

(** [view_agree k ns w Mk]: at the group's member [k], [Mk], the
    container's eliminator at every member [i'] the view takes to [k] has
    the group's results of [w] at the container's paths: at a member with a
    block its result, at a record view its fields' results at the paths
    the container has ([sel_ihs]). *)
Record view_agree (k : nat) (ns : list aczel_set) (w : aczel_set) (Mk : imember) : Prop :=
  { (** At a member with a block, at every element equal to [w], the
        container's result is the group's *)
    view_agree_block : r <> ak_propositional -> im_is_rview Mk = false -> forall i' Mi', ind_member D' i' = Some Mi' ->
      List.nth_error vm i' = Some k -> forall w', set_eq w w' ->
      set_elim T γ Γ ρ r qc Is' Bks' i' w' (elim_result T γ Γ ρ r p Us Bks V k w')
    (** At a record view, of the container's record view of the same
        record and fields, the container's results of the fields are the
        group's at the container's paths *)
  ; view_agree_rview : r <> ak_propositional -> forall qr Is fl c gs i' Mi' Is0 c' gs',
      im_head Mk = mh_record qr Is fl -> im_cons Mk = [(c, gs)] ->
      ind_member D' i' = Some Mi' -> im_head Mi' = mh_record qr Is0 fl -> im_cons Mi' = [(c', gs')] ->
      List.nth_error vm i' = Some k -> forall w', set_eq w w' ->
      set_ihs T γ Γ ρ r qc Is' Bks' gs' (List.map (tuple_field w') fl)
        (sel_ihs D' D gs' gs (List.map (fun l => lvalue l w') (fields_leaves (rview_leaves D) nil (List.combine fl gs)))) }.

(** The agreement respects equality. *)
Lemma view_agree_resp : forall k ns ns' w w' Mk, list_set_eq ns ns' -> set_eq w w' ->
    view_agree k ns w Mk -> view_agree k ns' w' Mk.
Proof.
  intros k ns ns' w w' Mk _ E [Hb Hrv]. constructor.
  - intros Hr Hr' i' Mi' Hi' Hv w'' E'. exact (Hb Hr Hr' i' Mi' Hi' Hv w'' (set_eq_trans _ _ _ E E')).
  - intros Hr qr Is fl c gs i' Mi' Is0 c' gs' Hh Hc Hi' Hh' Hc' Hv w'' E'.
    exact (Hrv Hr qr Is fl c gs i' Mi' Is0 c' gs' Hh Hc Hi' Hh' Hc' Hv w'' (set_eq_trans _ _ _ E E')).
Qed.

(** Outside [Prop], a leaf's value is its result. *)
Lemma lvalue_result : r <> ak_propositional -> forall l v, lvalue l v = leaf_result T γ Γ ρ r p Us Bks V l v.
Proof. intros Hr l v. unfold lvalue, leaf_value. destruct r; try reflexivity; contradiction. Qed.

(** Selections of pointwise equal results are pointwise equal. *)
Lemma sel_leaves_vals_set_eq : forall t' ls rs rs', list_set_eq rs rs' ->
    list_set_eq (sel_leaves_vals D' t' ls rs) (sel_leaves_vals D' t' ls rs').
Proof.
  intros t'; induction ls as [| l ls IH]; intros rs rs' E; [ cbn; constructor |].
  destruct E as [| a a' rs rs' Ea E]; cbn; [ constructor |].
  destruct (leaf_in D' t' l); [ constructor; [ exact Ea | apply IH; exact E ] | apply IH; exact E ].
Qed.

(** Along a container's shape whose group's shape has agreeing ends, the
    container's recursive results are the group's at the container's
    paths. *)
Lemma container_ih_of_closed_ok : r <> ak_propositional ->
    forall t' RV t Mk Ta φ Bs1 θ xv, shape_correspond vm t' t ->
    shape_closed_ok T γ Γ ρ r p Us Bks V D i RV view_agree Mk Ta φ Bs1 t θ xv ->
    forall m, set_ih T γ Γ ρ r qc Is' Bks' t' xv
      (List.map (fun l => lvalue l xv) (List.filter (leaf_in D' t') (shape_leaves (rview_leaves D) m t))).
Proof.
  intros Hr t'. induction t' as [j' Ps' | B' t' IH]; intros RV t Mk Ta φ Bs1 θ xv Hco H m;
    destruct t as [j Ps | B t]; cbn [shape_correspond] in Hco; try contradiction; cbn [shape_closed_ok shape_leaves] in *.
  - destruct H as (Mj & ns & [HMj _ _ _ _ [Hblk Hrv]]).
    destruct (Hvm _ _ Hco) as (Mj' & Mj0 & HMj' & Hvmb).
    rewrite (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) in HMj; injection HMj as ->.
    pose proof (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvmb) as Erv.
    pose proof (lvalue_result Hr) as Hlv.
    destruct (im_is_rview Mj') eqn:Hr'.
    + destruct (im_head Mj') as [pm | qc0 k0 Is0 vm0 | qr Is0 fl] eqn:Hh'; unfold im_is_rview in Hr'; rewrite Hh' in Hr'; try discriminate.
      destruct (view_member_rview _ _ _ _ _ _ _ _ _ Hvmb _ _ _ Hh') as (Is1 & Hh).
      destruct (rview_struct_con _ _ _ HrsD _ _ _ _ _ (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) Hh) as (gs & Hcs & Hlen).
      destruct (rview_struct_con _ _ _ HrsQ _ _ _ _ _ HMj' Hh') as (gs' & Hcs' & Hlen').
      destruct (rview_struct_record _ _ _ HrsQ _ _ _ _ _ HMj' Hh') as [R HR].
      pose proof (rview_record_nodup _ _ _ _ _ _ HR) as Hnd.
      rewrite (HlcD _ _ _ _ _ _ _ (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) Hh Hcs).
      rewrite <- (sel_leaves_vals_map D' (pt_self j' Ps') (fun l => lvalue l xv)).
      rewrite (sel_leaves_vals_map_in _ _ _ _ _ _ (fun l => leaf_in_wk D' l (pt_self j' Ps') _)), List.map_map.
      eapply (set_ih_resp T γ); [eapply set_ih_rview; [exact HD' | exact HMj' | exact Hh' | exact Hcs' |
                                  exact (Hrv Hr _ _ _ _ _ j' Mj' Is0 _ _ Hh Hcs HMj' Hh' Hcs' Hco xv (set_eq_refl _))] |].
      rewrite <-(sel_leaves_fields D D' j' Mj' qr Is0 fl rview_con gs' Ps' gs HMj' Hh' Hcs' Hnd (eq_sym Hlen') (eq_sym Hlen))
        by (rewrite List.length_map, length_fields_leaves, combine_snd_eq by lia; reflexivity).
      apply sel_leaves_vals_set_eq. apply map_set_eq. intros l _. rewrite !Hlv. apply set_eq_sym. apply (leaf_result_wk T γ).
    + rewrite (rview_leaves_not_rview _ _ _ (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) ltac:(congruence)). cbn [List.filter leaf_in].
      rewrite HMj', Hr'. cbn [negb List.map].
      eapply set_ih_self; [exact HD' | exact HMj' | exact Hr' |].
      rewrite Hlv. cbn [leaf_result].
      exact (Hblk Hr ltac:(congruence) j' Mj' HMj' Hco xv (set_eq_refl _)).
  - destruct H as (a & [_ Edom Hrest]).
    set (Ls := shape_leaves (rview_leaves D) (S m) t).
    assert (EF : List.filter (leaf_in D' (pt_pi B' t')) (List.map (leaf_pi B) Ls) = List.map (leaf_pi B) (List.filter (leaf_in D' t') Ls)).
    { clear. induction Ls as [| l Ls IH]; cbn [List.map List.filter leaf_in]; [ reflexivity |].
      destruct (leaf_in D' t' l); cbn; rewrite IH; reflexivity. }
    rewrite EF, List.map_map.
    set (Fs := List.filter (leaf_in D' t') Ls).
    eapply (set_ih_resp T γ);
      [eapply (set_ih_pi T γ _ _ _ _ _ _ D' B' t' xv (fun b => List.map (fun l => lvalue l (set_apply xv b)) Fs));
         [exact HD' |]; intros b Hb; exact (IH _ _ _ _ _ _ _ _ Hco (Hrest b (set_mem_eq_r _ _ _ Edom Hb)) (S m)) |].
    replace (List.length (shape_leaves (rview_leaves D') 0 t')) with (List.length Fs).
    2:{ unfold Fs, Ls. rewrite <- (leaves_in_count_view p qc D D' vm HlcD HlcQ HrsD HrsQ Hvm (S (ptyp_mem t)) t' t (S m))
          by (try exact Hco; intros; lia). reflexivity. }
    pose proof (lvalue_result Hr) as Hlv.
    apply map_seq_set_eq. intros n l Hn. cbn [Nat.add]. rewrite Hlv. cbn [leaf_result].
    apply graph_set_resp; [| | apply set_eq_refl |].
    + intros b b' Eb. apply list_set_eq_nth. apply map_set_eq. intros l0 _. rewrite !Hlv. apply (leaf_result_resp T γ).
      apply set_apply_resp; [apply set_eq_refl | exact Eb].
    + intros b b' Eb. apply (leaf_result_resp T γ). apply set_apply_resp; [apply set_eq_refl | exact Eb].
    + intros b _.
      assert (Hnth : List.nth n (List.map (fun l0 => lvalue l0 (set_apply xv b)) Fs) empty_set = lvalue l (set_apply xv b))
        by (apply List.nth_error_nth; rewrite List.nth_error_map, Hn; reflexivity).
      rewrite Hnth, Hlv. apply set_eq_refl.
Qed.

(** Arguments whose recursive ones, at the group's corresponding shapes,
    have agreeing ends have the container's recursive results: the group's
    at the container's paths ([sel_ihs]). *)
Lemma set_ihs_container : r <> ak_propositional -> forall gs' gs nn pat vs, cargs_correspond vm gs' gs ->
    List.length vs = List.length gs' ->
    (forall n t' t v, List.nth_error gs' n = Some (ca_rec t') -> List.nth_error gs n = Some (ca_rec t) -> List.nth_error vs n = Some v ->
       exists RV Mk Ta φ Bs1 θ, shape_closed_ok T γ Γ ρ r p Us Bks V D i RV view_agree Mk Ta φ Bs1 t θ v) ->
    set_ihs T γ Γ ρ r qc Is' Bks' gs' vs (sel_ihs D' D gs' gs (ihs_values T γ Γ ρ r p Us Bks V D nn pat gs vs)).
Proof.
  intros Hr gs'. induction gs' as [| g' gs' IH]; intros gs nn pat vs Hco Hl Hrec.
  - destruct gs; [| contradiction]. destruct vs; [| discriminate]. constructor.
  - destruct gs as [| g gs]; [destruct g'; contradiction |]. destruct vs as [| v vs]; [discriminate |]. cbn in Hl.
    assert (Hrec' : forall n t' t v0, List.nth_error gs' n = Some (ca_rec t') -> List.nth_error gs n = Some (ca_rec t) ->
              List.nth_error vs n = Some v0 -> exists RV Mk Ta φ Bs1 θ, shape_closed_ok T γ Γ ρ r p Us Bks V D i RV view_agree Mk Ta φ Bs1 t θ v0)
      by (intros n t1' t1 v1 H1 H2 H3; exact (Hrec (S n) t1' t1 v1 H1 H2 H3)).
    destruct g' as [κ' A' | t'], g as [κ A | t]; cbn [cargs_correspond] in Hco; try contradiction;
      cbn [ihs_values sel_ihs].
    + destruct Hco as [_ Hco]. constructor. apply IH; [exact Hco | lia | exact Hrec'].
    + destruct Hco as [_ Hco]. rewrite skipn_app_len by (rewrite List.length_map, !(length_shape_leaves _ t _ 0); reflexivity).
      constructor. apply IH; [exact Hco | lia | exact Hrec'].
    + destruct Hco as (Hm & Hd & Hco).
      destruct (Hrec 0 t' t v eq_refl eq_refl eq_refl) as (RV & Mk & Ta & φ & Bs1 & θ & Hcl).
      set (ls := shape_leaves (rview_leaves D) (pat_nargs pat + nn) t).
      assert (Lls : List.length (shape_leaves (rview_leaves D) 0 t) = List.length (List.map (fun l => leaf_value T γ Γ ρ r p Us Bks V l v) ls))
        by (rewrite List.length_map; apply length_shape_leaves).
      rewrite Lls, firstn_app_len, skipn_app_len by reflexivity.
      rewrite (sel_leaves_vals_ext _ _ _ ls _ (leaf_in_shape_leaves _ _ _ _ _ _)), sel_leaves_vals_map.
      constructor.
      * exact (container_ih_of_closed_ok Hr t' RV t Mk Ta φ Bs1 θ v (shape_correspond_of _ _ _ Hm Hd) Hcl _).
      * apply IH; [exact Hco | lia | exact Hrec'].
Qed.

End ContainerResults.

(** ** The Wrapped Branch's Recursive Results, Read *)

(** An environment extended by values holds, at a variable below them,
    the value as far from the end. *)
Lemma set_env_extend_kinded_value : forall vs κs ρ0 x, x < List.length vs ->
    set_entry_value (set_env_extend_kinded ρ0 κs vs x) = List.nth (List.length vs - 1 - x) vs empty_set.
Proof.
  induction vs as [| v vs IH] using List.rev_ind; intros κs ρ0 x Hx; cbn [List.length] in Hx; [lia |].
  rewrite set_env_extend_kinded_snoc_any, List.length_app. cbn [List.length].
  destruct x as [| x].
  - cbn. rewrite List.app_nth2 by lia. replace (List.length vs + 1 - 1 - 0 - List.length vs) with 0 by lia. reflexivity.
  - rewrite List.length_app in Hx. cbn [List.length] in Hx. cbn [set_env_extend]. rewrite IH by lia.
    rewrite List.app_nth1 by lia. f_equal. lia.
Qed.

(** The wrapped recursive results along the group's paths [ls], read at
    an environment whose last entries [ws] are the container's: the
    container's at its paths, the group's [ihsE] elsewhere. *)
Lemma interp_wrap_leaves : forall Ψ ρ0 κs D' t' ls ihs ihsE Y ws r',
    List.length ihs = List.length ls -> set_interp_list T γ Ψ (set_env_extend_kinded ρ0 κs (Y ++ ws)) ihs ihsE ->
    r' + leaves_in_count D' t' ls <= List.length ws ->
    set_interp_list T γ Ψ (set_env_extend_kinded ρ0 κs (Y ++ ws)) (wrap_leaves D' t' ls ihs r' (List.length ws))
      (merge_leaves empty_set D' t' ls ihsE (List.skipn r' ws)).
Proof.
  intros Ψ ρ0 κs D' t'; induction ls as [| l ls IH]; intros [| ih ihs] ihsE Y ws r' Lh Ev Lw; cbn in Lh; try discriminate.
  - inversion Ev; subst; cbn; constructor.
  - inversion Ev as [| ? ? ? ? e es Ee Ees]; subst.
    assert (Hc : leaves_in_count D' t' (l :: ls) = (if leaf_in D' t' l then 1 else 0) + leaves_in_count D' t' ls)
      by (unfold leaves_in_count; cbn; destruct (leaf_in D' t' l); reflexivity).
    rewrite Hc in Lw; cbn [wrap_leaves merge_leaves].
    destruct (leaf_in D' t' l).
    + destruct (nth_error_lt_some ws r' ltac:(lia)) as [a Ha].
      rewrite (skipn_nth_cons _ _ _ Ha); cbn [List.hd List.tl].
      constructor; [| apply IH; [ lia | exact Ees | lia ] ].
      replace a with (set_entry_value (set_env_extend_kinded ρ0 κs (Y ++ ws) (List.length ws - 1 - r'))); [apply set_interp_var |].
      rewrite set_env_extend_kinded_value by (rewrite List.length_app; lia).
      rewrite List.length_app, List.app_nth2 by lia.
      replace (List.length Y + List.length ws - 1 - (List.length ws - 1 - r') - List.length Y) with r' by lia.
      apply List.nth_error_nth; exact Ha.
    + constructor; [ exact Ee | apply IH; [ lia | exact Ees | lia ] ].
Qed.

(** And over a constructor's arguments, [gs'] as the container has them,
    [gs] as the group does. *)
Lemma interp_wrap_ihs : forall Ψ ρ0 κs D' D gs' gs ihs ihsE Y ws r', cargs_same_kinds gs' gs ->
    List.length ihs = cargs_nrec D gs -> set_interp_list T γ Ψ (set_env_extend_kinded ρ0 κs (Y ++ ws)) ihs ihsE ->
    r' + cargs_container_count D D' gs' gs <= List.length ws ->
    set_interp_list T γ Ψ (set_env_extend_kinded ρ0 κs (Y ++ ws)) (wrap_ihs D' D gs' gs ihs r' (List.length ws))
      (merge_ihs empty_set D' D gs' gs ihsE (List.skipn r' ws)).
Proof.
  intros Ψ ρ0 κs D' D; induction gs' as [| [A' | t'] gs' IH]; intros [| [A | t] gs] ihs ihsE Y ws r' Hk Lh Ev Lw;
    cbn in Hk; try contradiction; cbn [wrap_ihs merge_ihs cargs_nrec cargs_container_count] in Lh, Lw |- *.
  - inversion Ev; subst; constructor.
  - exact (IH _ _ _ _ _ _ Hk Lh Ev Lw).
  - set (n0 := List.length (shape_leaves (rview_leaves D) 0 t)) in *.
    rewrite <- (List.firstn_skipn n0 ihs) in Ev.
    destruct (set_interp_list_app_inv T γ _ _ _ _ _ Ev) as [Ea Eb].
    rewrite List.length_firstn, Nat.min_l in Ea, Eb by lia.
    apply set_interp_list_app; [ exact Ea |].
    apply IH; [ exact Hk | rewrite List.length_skipn; lia | exact Eb | exact Lw ].
  - set (ls := shape_leaves (rview_leaves D) 0 t) in *.
    rewrite <- (List.firstn_skipn (List.length ls) ihs) in Ev.
    destruct (set_interp_list_app_inv T γ _ _ _ _ _ Ev) as [Ea Eb].
    rewrite List.length_firstn, Nat.min_l in Ea, Eb by lia.
    apply set_interp_list_app.
    + apply interp_wrap_leaves; [ rewrite List.length_firstn; lia | exact Ea | lia ].
    + rewrite List.skipn_skipn; apply IH; [ exact Hk | rewrite List.length_skipn; lia | exact Eb | lia ].
Qed.

End ElimView.
