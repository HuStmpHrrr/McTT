(** * The Set Rule of the Eliminator at a View

    The eliminator of a group [D] at its view [m] of the container's
    declared member [k'] at the instance [Is] is, in the model, the
    container's eliminator at [k'] at the view's blocks wrapped
    ([view_wrap]).  By induction on the group's carriers, the container's
    eliminator at a container's member has, at every element, the group's
    result at the member the view takes it to: at a constructor, the
    wrapped branch is the group's branch at an instance of its context
    whose recursive results are the container's along the container's leaf
    paths and the group's along the others, and the container's are the
    group's by the induction. *)

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

(** ** The Group's Results along the Container's Leaf Paths *)

Section ViewResults.
  (** The group's eliminator: its context, environment, sort, group,
      uniform parameters, blocks and the set of its results *)
  Variables (Γ : ctx) (ρ : set_env) (r : abs_kind) (p : qname) (Us : list exp) (Bks : list eblock) (V : aczel_set).
  (** The members of the group the view takes the container's to *)
  Variable vm : list nat.

(** The group's result of [v] along the container's leaf path [l]: at the
    end at the container's member [j'], the group's eliminator's at the
    member [vm] takes [j'] to; under a domain the graph of the results at
    [v]'s values; at a projection the result at the field. *)
Fixpoint view_leaf_result (l : leaf_path) (v : aczel_set) : aczel_set :=
  match l with
  | leaf_self j' _ => elim_result T γ Γ ρ r p Us Bks V (List.nth j' vm 0) v
  | leaf_pi _ l' => graph_set (relation_domain v) (fun b => view_leaf_result l' (set_apply v b))
  | leaf_proj f _ l' => view_leaf_result l' (tuple_field v f)
  end.

(** The results respect equality. *)
Lemma view_leaf_result_resp : forall l v v', set_eq v v' -> set_eq (view_leaf_result l v) (view_leaf_result l v').
Proof.
  induction l as [j Ps | B l IH | f ns l IH]; intros v v' E; cbn [view_leaf_result].
  - apply elim_result_resp; exact E.
  - apply graph_set_resp; [intros b b' Eb; apply IH; apply set_apply_resp; [apply set_eq_refl | exact Eb]
                          | intros b b' Eb; apply IH; apply set_apply_resp; [apply set_eq_refl | exact Eb]
                          | apply relation_domain_resp; exact E |].
    intros b _. apply IH. apply set_apply_resp; [exact E | apply set_eq_refl].
  - apply IH. apply tuple_field_resp. exact E.
Qed.

(** A moved path has the same results. *)
Lemma view_leaf_result_wk : forall l φ v, set_eq (view_leaf_result (leaf_wk φ l) v) (view_leaf_result l v).
Proof.
  induction l as [j Ps | B l IH | f ns l IH]; intros φ v; cbn [leaf_wk view_leaf_result].
  - apply set_eq_refl.
  - apply graph_set_resp; [intros b b' Eb; apply view_leaf_result_resp; apply set_apply_resp; [apply set_eq_refl | exact Eb]
                          | intros b b' Eb; apply view_leaf_result_resp; apply set_apply_resp; [apply set_eq_refl | exact Eb]
                          | apply set_eq_refl |].
    intros b _. apply IH.
  - apply IH.
Qed.

End ViewResults.

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
  (** The container's group is [D'], typed *)
  Hypotheses (HD' : ind_lookup gc_deps gc_stack qc = Some D') (HDt' : decl_typed gc_deps gc_stack D').
  (** The view takes record views to record views and the others to the
      others *)
  Hypothesis Hvrv : forall j' Mj' j Mj, ind_member D' j' = Some Mj' -> List.nth_error vm j' = Some j -> ind_member D j = Some Mj ->
    im_is_rview Mj' = im_is_rview Mj.

  Let vresult := view_leaf_result Γ ρ r p Us Bks V vm.

(** [view_agree k ns w Mk]: at the group's member [k], [Mk], the
    container's eliminator at every member [i'] the view takes to [k] has
    the group's results of [w]: at a member with a block its result, at a
    record view its fields' results along the container's paths. *)
Record view_agree (k : nat) (ns : list aczel_set) (w : aczel_set) (Mk : imember) : Prop :=
  { (** At a member with a block, at every element equal to [w], the
        container's result is the group's *)
    view_agree_block : r <> ak_propositional -> im_is_rview Mk = false -> forall i' Mi', ind_member D' i' = Some Mi' ->
      List.nth_error vm i' = Some k -> forall w', set_eq w w' ->
      set_elim T γ Γ ρ r qc Is' Bks' i' w' (elim_result T γ Γ ρ r p Us Bks V k w')
    (** At a record view, the container's results of the fields are the
        group's along the container's paths *)
  ; view_agree_rview : r <> ak_propositional -> forall i' Mi' qr Is0 fl c gs, ind_member D' i' = Some Mi' ->
      im_head Mi' = mh_record qr Is0 fl -> im_cons Mi' = [(c, gs)] -> List.nth_error vm i' = Some k -> forall w', set_eq w w' ->
      set_ihs T γ Γ ρ r qc Is' Bks' gs (List.map (tuple_field w') fl)
        (List.map (fun l => vresult l w') (fields_leaves (rview_leaves D') nil (List.combine fl gs))) }.

(** The agreement respects equality. *)
Lemma view_agree_resp : forall k ns ns' w w' Mk, list_set_eq ns ns' -> set_eq w w' ->
    view_agree k ns w Mk -> view_agree k ns' w' Mk.
Proof.
  intros k ns ns' w w' Mk _ E [Hb Hrv]. constructor.
  - intros Hr Hr' i' Mi' Hi' Hv w'' E'. exact (Hb Hr Hr' i' Mi' Hi' Hv w'' (set_eq_trans _ _ _ E E')).
  - intros Hr i' Mi' qr Is0 fl c gs Hi' Hh Hc Hv w'' E'. exact (Hrv Hr i' Mi' qr Is0 fl c gs Hi' Hh Hc Hv w'' (set_eq_trans _ _ _ E E')).
Qed.

(** Along a container's shape whose group's shape has agreeing ends, the
    container's recursive results are the group's along the container's
    paths. *)
Lemma container_ih_of_closed_ok : r <> ak_propositional ->
    forall t' RV t Mk Ta φ Bs1 θ xv, shape_correspond vm t' t -> (exists Mj', ind_member D' (ptyp_mem t') = Some Mj') ->
    shape_closed_ok T γ Γ ρ r p Us Bks V D i RV view_agree Mk Ta φ Bs1 t θ xv ->
    forall m, set_ih T γ Γ ρ r qc Is' Bks' t' xv (List.map (fun l => vresult l xv) (shape_leaves (rview_leaves D') m t')).
Proof.
  intros Hr t'. induction t' as [j' Ps' | B' t' IH]; intros RV t Mk Ta φ Bs1 θ xv Hco (Mj' & HMj') H m;
    destruct t as [j Ps | B t]; cbn [shape_correspond] in Hco; try contradiction; cbn [shape_closed_ok shape_leaves ptyp_mem] in *.
  - destruct H as (Mj & ns & [HMj _ _ _ _ [Hblk Hrv]]).
    pose proof (Hvrv _ _ _ _ HMj' Hco HMj) as Erv.
    destruct (im_is_rview Mj') eqn:Hr'.
    + destruct (im_head Mj') as [pm | qc0 k0 Is0 vm0 | qr Is0 fl] eqn:Hh; unfold im_is_rview in Hr'; rewrite Hh in Hr'; try discriminate.
      destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ HDt') _ _ _ _ _ HMj' Hh) as (gs & Hcs & _).
      pose proof (leaves_coherent_of_order _ (rview_struct_order _ _ _ (decl_typed_record_struct _ _ _ HDt'))) as Hcoh.
      rewrite (Hcoh _ _ _ _ _ _ _ HMj' Hh Hcs).
      eapply (set_ih_resp T γ); [eapply set_ih_rview; [exact HD' | exact HMj' | exact Hh | exact Hcs
                                                      | exact (Hrv Hr _ _ _ _ _ _ _ HMj' Hh Hcs Hco xv (set_eq_refl _))] |].
      rewrite List.map_map. apply map_set_eq. intros l _. apply set_eq_sym. apply view_leaf_result_wk.
    + rewrite (rview_leaves_not_rview _ _ _ HMj' Hr'). cbn [List.map].
      eapply set_ih_self; [exact HD' | exact HMj' | exact Hr' |].
      unfold vresult. cbn [view_leaf_result]. rewrite (List.nth_error_nth _ _ _ Hco).
      exact (Hblk Hr (eq_sym Erv) j' Mj' HMj' Hco xv (set_eq_refl _)).
  - destruct H as (a & [_ Edom Hrest]). rewrite List.map_map.
    set (Ls := shape_leaves (rview_leaves D') (S m) t').
    eapply (set_ih_resp T γ);
      [eapply (set_ih_pi T γ _ _ _ _ _ _ D' B' t' xv (fun b => List.map (fun l => vresult l (set_apply xv b)) Ls));
         [exact HD' |]; intros b Hb;
         exact (IH _ _ _ _ _ _ _ _ Hco (ex_intro _ Mj' HMj') (Hrest b (set_mem_eq_r _ _ _ Edom Hb)) (S m)) |].
    rewrite (length_shape_leaves (rview_leaves D') t' 0 (S m)). fold Ls.
    apply map_seq_set_eq. intros n l Hn. cbn [view_leaf_result Nat.add].
    apply graph_set_resp; [| | apply set_eq_refl |].
    + intros b b' Eb. apply list_set_eq_nth. apply map_set_eq. intros l0 _. apply view_leaf_result_resp.
      apply set_apply_resp; [apply set_eq_refl | exact Eb].
    + intros b b' Eb. apply view_leaf_result_resp. apply set_apply_resp; [apply set_eq_refl | exact Eb].
    + intros b _.
      assert (Hnth : List.nth n (List.map (fun l0 => vresult l0 (set_apply xv b)) Ls) empty_set = vresult l (set_apply xv b))
        by (apply List.nth_error_nth; rewrite List.nth_error_map, Hn; reflexivity).
      rewrite Hnth. apply set_eq_refl.
Qed.

(** The container's recursive results of the arguments [vs] of the kinds
    [gs']: at each recursive argument, the group's along the container's
    paths of its shape. *)
Fixpoint container_ihs (gs' : list carg) (vs : list aczel_set) : list aczel_set :=
  match gs', vs with
  | ca_rec t' :: gs1', v :: vs' => List.map (fun l => vresult l v) (shape_leaves (rview_leaves D') 0 t') ++ container_ihs gs1' vs'
  | ca_arg _ _ :: gs1', _ :: vs' => container_ihs gs1' vs'
  | _, _ => nil
  end.

(** Arguments whose recursive ones, at the group's corresponding shapes,
    have agreeing ends have the container's recursive results. *)
Lemma set_ihs_container : r <> ak_propositional -> forall gs' gs vs, cargs_correspond vm gs' gs -> List.length vs = List.length gs' ->
    (forall n t' t v, List.nth_error gs' n = Some (ca_rec t') -> List.nth_error gs n = Some (ca_rec t) -> List.nth_error vs n = Some v ->
       (exists Mj', ind_member D' (ptyp_mem t') = Some Mj') /\
       exists RV Mk Ta φ Bs1 θ, shape_closed_ok T γ Γ ρ r p Us Bks V D i RV view_agree Mk Ta φ Bs1 t θ v) ->
    set_ihs T γ Γ ρ r qc Is' Bks' gs' vs (container_ihs gs' vs).
Proof.
  intros Hr gs'. induction gs' as [| g' gs' IH]; intros gs vs Hco Hl Hrec.
  - destruct gs; [| contradiction]. destruct vs; [| discriminate]. constructor.
  - destruct gs as [| g gs]; [destruct g'; contradiction |]. destruct vs as [| v vs]; [discriminate |]. cbn in Hl.
    destruct g' as [κ' A' | t'], g as [κ A | t]; cbn [cargs_correspond] in Hco; try contradiction; cbn [container_ihs].
    + destruct Hco as [_ Hco]. constructor. apply IH with (gs := gs); [exact Hco | lia |].
      intros n t1' t1 v1 H1 H2 H3. exact (Hrec (S n) t1' t1 v1 H1 H2 H3).
    + destruct Hco as [_ Hco]. constructor. apply IH with (gs := gs); [exact Hco | lia |].
      intros n t1' t1 v1 H1 H2 H3. exact (Hrec (S n) t1' t1 v1 H1 H2 H3).
    + destruct Hco as (Hm & Hd & Hco).
      destruct (Hrec 0 t' t v eq_refl eq_refl eq_refl) as [HMj' (RV & Mk & Ta & φ & Bs1 & θ & Hcl)].
      constructor.
      * exact (container_ih_of_closed_ok Hr t' RV t Mk Ta φ Bs1 θ v (shape_correspond_of _ _ _ Hm Hd) HMj' Hcl 0).
      * apply IH with (gs := gs); [exact Hco | lia |].
        intros n t1' t1 v1 H1 H2 H3. exact (Hrec (S n) t1' t1 v1 H1 H2 H3).
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
