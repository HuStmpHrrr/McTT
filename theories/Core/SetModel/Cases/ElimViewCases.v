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
From Mctt.Core.SetModel Require Import Judgments.
From Mctt.Core.SetModel.Cases Require Import UniverseCases PropCases FunctionCases ValidUnit MemberTypes Sel IndCases RecordCases
  ElimCases.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members Presup CoreInversions.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths DescTyping MemberLemmas.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing UniformParams Views ViewLeaves.
Import ListNotations.

Section ElimView.
  (** The context the rule's premises are read at *)
  Variable Θr : gdeps.
  Variable Ξr : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

Section ElimViewSteps.
  Context {GC : GCtx}.
  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).
  (** The global context is well formed *)
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  (** The context the derivations were checked at *)
  Variable Θs : gdeps.
  Variable Ξs : gstack.
  (** The valuation models, here, everything that context resolves *)
  Hypothesis Hemb : set_gctx_embedding Θs Ξs gc_deps gc_stack T γ.

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

(** Variables past some read the entries as far from the end. *)
Lemma set_interp_list_vars_mid : forall Ψ Y vs rest ρ0 κs,
    set_interp_list T γ Ψ (set_env_extend_kinded ρ0 κs (Y ++ vs ++ rest)) (vars_from (List.length rest) (List.length vs)) vs.
Proof.
  intros Ψ Y; induction Y as [| y Y IH]; intros vs rest ρ0 κs; cbn [List.app set_env_extend_kinded];
    [apply set_interp_list_vars_from | apply IH].
Qed.

(** Below the values, an extended environment does not depend on the
    environment extended. *)
Lemma set_env_extend_kinded_lt : forall vs κs ρ1 ρ2 x, x < List.length vs ->
    set_env_extend_kinded ρ1 κs vs x = set_env_extend_kinded ρ2 κs vs x.
Proof.
  induction vs as [| v vs IH]; intros κs ρ1 ρ2 x Hx; cbn [List.length] in Hx; [lia |]. cbn [set_env_extend_kinded].
  destruct (Nat.lt_ge_cases x (List.length vs)) as [H | H]; [apply IH; exact H |].
  replace x with (List.length vs + 0) by lia. rewrite !set_env_extend_kinded_ge. reflexivity.
Qed.

(* [wf_sub_uparams_prefix] and [elim_ihs_moved], the syntax the wrapped
   branch's reading needs, are in [Core.Syntactic.System.Inductives.Views]. *)

(** The recursive results of a record view's fields, its element's
    fields, are those of the element along the fields' paths. *)
Lemma ihs_values_fields : forall Γ ρ r p Us Bks V D w fl gs pat ns, List.length fl = List.length gs ->
    pat_nargs pat = List.length ns ->
    ihs_values T γ Γ ρ r p Us Bks V D 0 pat gs (List.map (tuple_field w) fl)
    = List.map (fun l => leaf_value T γ Γ ρ r p Us Bks V l w) (fields_leaves (rview_leaves D) ns (List.combine fl gs)).
Proof.
  intros Γ ρ r p Us Bks V D w. induction fl as [| f fl IH]; intros [| g gs] pat ns Hl Hp; cbn in Hl; try discriminate; [reflexivity |].
  destruct g as [κ A | t]; cbn [List.map List.combine ihs_values fields_leaves].
  - apply IH; [lia | cbn [pat_nargs]; rewrite Hp, List.length_app; cbn; lia].
  - rewrite List.map_app, List.map_map, Nat.add_0_r, Hp. f_equal. apply IH; [lia | exact Hp].
Qed.

(** ** The Step of the Induction on the Group's Carriers *)

Section ViewStep.
  (** The group's eliminator: its context, environment, sort, group,
      uniform parameters, blocks, the set of its results, the group, the
      level of its motives, the uniform parameters' instance and the
      universe of the carriers *)
  Variables (Γ : ctx) (ρ : set_env) (r : abs_kind) (p : qname) (Us : list exp) (Bks : list eblock) (V : aczel_set).
  Variables (D : ind_decl) (i : nat) (Fσ : set_env -> set_env) (U : aczel_set).
  (** The induction's setting *)
  Hypothesis HS1 : elim_setting_with T γ Θs Ξs Γ r p Us Bks V D i Fσ.
  (** The environment is one of the context *)
  Hypothesis Hρ : set_env_in T γ Γ ρ.
  (** The carriers are the least fixed point in [U] *)
  Hypothesis Hcar : forall k Mk ρk, ind_member D k = Some Mk -> set_env_in T γ (im_params D Mk) ρk ->
    list_set_eq (uniform_values D Mk ρk) (elim_uniform_values ρ D Fσ) ->
    set_eq (set_group_carrier (global_group γ p) k (set_env_values (im_params D Mk) ρk))
           (member_carrier (global_group γ p) (elim_uniform_values ρ D Fσ) U U k (set_env_values (im_nparams Mk) ρk)).

  Let us := elim_uniform_values ρ D Fσ.
  Let G := global_group γ p.

(** At a constructor of a member, at arguments drawn from points of the
    carriers, the recursive eliminations of the arguments, in the context
    of the constructor's parameters and arguments ([con_inst_ctx]) at
    their values, read the recursive results of the arguments. *)
Lemma args_ihs_reading : forall S k Mk SMk cs gs vals θk,
    set_sub S (carrier_fixed_point G us U U) ->
    ind_member D k = Some Mk -> List.nth_error (set_group_members G) k = Some SMk -> In cs (set_member_constructors SMk) ->
    ind_con Mk (set_constructor_name cs) = Some gs ->
    set_env_in T γ (im_params D Mk) θk -> list_set_eq (uniform_values D Mk θk) us ->
    arguments_fit G U S (us ++ set_env_values (im_nparams Mk) θk) (set_constructor_arguments cs) vals ->
    set_interp_list T γ (con_inst_ctx Γ p D Mk Us gs)
      (set_env_extend_kinded ρ (ctx_kinds (cargs_ctx p D Mk gs ++ im_nparams Mk)) (set_env_values (im_nparams Mk) θk ++ vals))
      (elim_ihs r p D (List.map (fun U => exp_sub U (sb_of_wk (wk_shiftn (im_nn Mk + List.length gs)))) Us)
         (blocks_sub Bks (sb_of_wk (wk_shiftn (im_nn Mk + List.length gs))))
         (sb_of_list (sb_of_wk (wk_shiftn (im_nn Mk + List.length gs)))
            (List.map (fun U => exp_sub U (sb_of_wk (wk_shiftn (im_nn Mk + List.length gs)))) Us ++
             vars_from (List.length gs) (im_nn Mk)))
         (im_nn Mk) gs (vars_from 0 (List.length gs)))
      (ihs_values T γ Γ ρ r p Us Bks V D (im_nn Mk) nil gs vals).
Proof.
  intros S k Mk SMk cs gs vals θk HSf Hk HSk Hcs Hgs Hθk Huni Hfit.
  pose proof HS1 as [HΓ HcΓ HDsrc Hσ HDt Hcl HUl HMwf HMot HMctx HMh HBk Hbτ Hbctx Hbrs HBr HV HBt HUs _].
  pose proof (ind_lookup_gc_sub _ _ _ _ _ _ (set_source_sub T γ Θs Ξs Hemb) HDsrc) as HD.
  pose proof (set_source_groups T γ Θs Ξs Hemb _ _ HDsrc) as HG. fold G in HG.
  pose proof (set_group_ok_members _ _ _ _ _ HG _ _ _ Hk HSk) as Hmok.
  pose proof (set_member_ok_constructors _ _ _ _ _ _ _ Hmok cs gs Hcs Hgs) as Hcok.
  pose proof (decls_of_ctx _ _ _ HcΓ) as HDs.
  pose proof (cons_lookup_in _ _ _ Hgs) as Hin.
  set (c := set_constructor_name cs) in *.
  set (sgs := set_constructor_arguments cs) in *.
  pose proof (arguments_fit_length _ _ _ _ _ _ Hfit) as Hlv.
  pose proof (set_arguments_shape_length _ _ (set_constructor_ok_shape _ _ _ _ _ _ _ _ Hcok)) as Hlsh.
  assert (Hlvg : List.length vals = List.length gs) by lia.
  set (ns0 := set_env_values (im_nparams Mk) θk) in *.
  assert (Hln : List.length ns0 = im_nn Mk) by (unfold ns0, im_nn; rewrite length_set_env_values; reflexivity).
  set (nn := im_nn Mk) in *. set (na := List.length gs) in *.
  set (β := sb_of_wk (wk_shiftn (nn + na))).
  (* the environment of the parameters and the arguments *)
  set (ρn := set_env_extend_kinded ρ (ctx_kinds (im_nparams Mk)) ns0).
  pose proof (nparams_env T γ Hfn Hmods Hgw Θs Ξs Hemb Γ ρ p D Us Fσ HΓ HcΓ Hρ HDsrc Hσ k Mk SMk _ _ θk Hk HSk Hin Hθk Huni) as Hρn. fold ns0 ρn in Hρn.
  assert (Hdrop : forall x, set_env_drop nn ρn x = ρ x)
    by (intros x; unfold set_env_drop, ρn; rewrite <- Hln, set_env_extend_kinded_ge; reflexivity).
  assert (Hvn : set_env_values (im_nparams Mk) ρn = ns0)
    by (unfold ρn; apply set_env_values_extend_kinded; exact Hln).
  pose proof (args_env T γ Hfn Hmods Hgw Θs Ξs Hemb Γ ρ p D Us Fσ HΓ HcΓ Hρ HDsrc Hσ U Hcar S HSf k Mk SMk cs gs ρn vals Hk HSk Hcs Hgs Hcok Hρn Hdrop
                ltac:(rewrite Hvn; exact Hfit) gs nil (eq_sym (List.app_nil_r gs))) as Hρa.
  rewrite List.firstn_all2 in Hρa by lia.
  assert (Econ : con_inst_ctx Γ p D Mk Us gs = tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) (sb_of_list sb_id Us) ++ Γ)
    by (unfold con_inst_ctx; rewrite tele_sub_app, length_im_nparams, List.app_assoc; reflexivity).
  rewrite <- Econ in Hρa.
  assert (Eρa : set_env_extend_kinded ρn (ctx_kinds (cargs_ctx p D Mk gs)) vals
                = set_env_extend_kinded ρ (ctx_kinds (cargs_ctx p D Mk gs ++ im_nparams Mk)) (ns0 ++ vals))
    by (unfold ρn; rewrite ctx_kinds_app, set_env_extend_kinded_app by (rewrite length_ctx_kinds; unfold nn in Hln; unfold im_nn in Hln; lia); reflexivity).
  rewrite Eρa in Hρa.
  set (ρa := set_env_extend_kinded ρ (ctx_kinds (cargs_ctx p D Mk gs ++ im_nparams Mk)) (ns0 ++ vals)) in *.
  clear Eρa Hvn Hdrop Hρn.
  pose proof (ihs_reading_at T γ Hfn Hmods Hgw Θs Ξs Hemb Γ ρ r p Us Bks V D i Fσ U no_extra no_extra_resp HΓ HcΓ Hρ HDsrc Hσ HDt Hcl HUl
                HMwf HMot HMctx HMh HBk Hcar Hbτ Hbctx Hbrs HBr HV HBt HUs (fun k' ns' v' _ _ _ => no_extra_point T γ D _ k' ns' v')) as HR.
  pose proof (proj2 (Hbctx k Mk c gs Hk Hgs)) as Hbw.
  clear HMwf HMot HMctx HMh HBk Hbτ Hbctx Hbrs HBr HV HBt HS1.
  pose proof (uniform_interp_list T γ Γ ρ Us D Fσ Hρ Hσ HUl) as HUv. fold us in HUv.
  assert (HlΔ : List.length (ns0 ++ vals) = nn + na) by (rewrite List.length_app; lia).
  assert (Hβa : forall y, sub_entry_agrees T γ (con_inst_ctx Γ p D Mk Us gs) ρa (β y) (ρ y)).
  { intros y. apply sub_agrees_var. unfold ρa. cbn [wk_shiftn]. rewrite Nat.add_comm, <- HlΔ. apply set_env_extend_kinded_ge. }
  pose proof (wf_sub_uparams _ _ _ HDt Hcl _ _ HcΓ HUl HUs) as Hσc.
  destruct (wf_sub_cinst _ _ _ _ _ _ _ _ Hgw HDs HD Hk HcΓ Hσc c gs gs nil Hin (eq_sym (List.app_nil_r gs))) as [HΨa _].
  assert (Hβt : gc_deps ⍮ gc_stack ⍮ con_inst_ctx Γ p D Mk Us gs ⊢ˢ β : Γ).
  { apply wf_sub_of_wk. rewrite Econ. replace (nn + na) with (List.length (tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) (sb_of_list sb_id Us)))
      by (rewrite length_tele_sub, List.length_app, length_cargs_ctx; unfold nn, im_nn; lia).
    apply wf_wk_shiftn_app'. rewrite <- Econ. exact HΨa. }
  assert (HUβ : set_interp_list T γ (con_inst_ctx Γ p D Mk Us gs) ρa (List.map (fun U => exp_sub U β) Us) us).
  { assert (Hset : sub_setting T γ Γ ρ nil Γ (con_inst_ctx Γ p D Mk Us gs) β ρa ρa)
      by (constructor; [reflexivity | exact Hβt | intros x Hx; cbn in Hx; lia | intros y; reflexivity | intros x; exact (Hβa x)]).
    pose proof (proj1 (proj2 (set_interp_sub_all T γ)) _ _ _ _ HUv nil Γ _ β ρa ρa HcΓ Hset) as H.
    cbn [tele_sub List.app List.length sb_qn] in H. exact H. }
  set (κa := ctx_kinds (cargs_ctx p D Mk gs ++ im_nparams Mk)) in ρa.
  assert (HL : set_interp_list T γ (con_inst_ctx Γ p D Mk Us gs) ρa
                 (List.map (fun U => exp_sub U β) Us ++ vars_from na nn ++ vars_from 0 na) (us ++ ns0 ++ vals)).
  { apply set_interp_list_app; [exact HUβ | apply set_interp_list_app].
    - pose proof (set_interp_list_vars_mid (con_inst_ctx Γ p D Mk Us gs) nil ns0 vals ρ κa) as H.
      cbn [List.app] in H. rewrite Hlvg, Hln in H. exact H.
    - pose proof (set_interp_list_vars_mid (con_inst_ctx Γ p D Mk Us gs) ns0 vals nil ρ κa) as H.
      rewrite List.app_nil_r in H. cbn [List.length] in H. rewrite Hlvg in H. exact H. }
  set (θc := set_env_extend_kinded ρ (ctx_kinds (cargs_ctx p D Mk gs ++ im_params D Mk)) (us ++ ns0 ++ vals)).
  assert (Hag : forall y, sub_entry_agrees T γ (con_inst_ctx Γ p D Mk Us gs) ρa
                  (sb_of_list β ((List.map (fun U => exp_sub U β) Us ++ vars_from na nn) ++ vars_from 0 na) y) (θc y))
    by (intros y; rewrite <- List.app_assoc; exact (sub_agrees_of_list T γ _ _ _ _ HL β ρ _ Hβa y)).
  clear HL HUβ.
  (* the closed environment of the arguments and the parameters at those values *)
  pose proof (set_group_ok_respects _ _ _ _ _ HG _ _ _ HSk Hcs) as Hrs.
  assert (Hvθ : list_set_eq (us ++ ns0) (set_env_values (im_params D Mk) θk))
    by (unfold im_params; rewrite set_env_values_app; apply list_set_eq_app; [exact (list_set_eq_sym _ _ Huni) | apply list_set_eq_refl]).
  assert (Hfitθ : arguments_fit G U S (set_env_values (im_params D Mk) θk) sgs vals)
    by (eapply arguments_fit_resp; [exact Hrs | exact Hvθ | apply list_set_eq_refl | exact Hfit]).
  pose proof (args_env_closed T γ Hfn Hmods Θs Ξs Hemb ρ p D Fσ HDsrc U Hcar S HSf k Mk SMk cs gs θk vals Hk HSk Hcs Hgs Hcok Hθk Huni Hfitθ
                gs nil (eq_sym (List.app_nil_r gs))) as Hθc0.
  rewrite List.firstn_all2 in Hθc0 by lia.
  set (Δ := cargs_ctx p D Mk gs ++ im_params D Mk) in *.
  set (θc0 := set_env_extend_kinded θk (ctx_kinds (cargs_ctx p D Mk gs)) vals) in *.
  pose proof (cargs_ctx_closed p D k Mk _ gs gs nil Hcl Hk Hin (eq_sym (List.app_nil_r gs))) as Hs1. fold Δ in Hs1.
  pose proof (decl_closed_params_ass _ _ _ Hcl Hk) as Hass0.
  assert (Hass1 : all_assumptions Δ) by (apply List.Forall_app; split; [apply cargs_ctx_aux_ass | exact Hass0]).
  pose proof (set_ctx_of_tele_types T γ Hfn Hmods _ _ _ (set_constructor_ok_types _ _ _ _ _ _ _ _ Hcok)
                (member_params_ctx T γ Hfn Hmods Θs Ξs Hemb p D HDsrc k Mk SMk Hk HSk)) as HTc. fold Δ in HTc.
  assert (Hvals : list_set_eq (set_env_values Δ θc0) (us ++ ns0 ++ vals)).
  { unfold Δ. rewrite set_env_values_app, List.app_assoc. apply list_set_eq_app.
    - rewrite (set_env_values_agree _ _ θk); [exact (list_set_eq_sym _ _ Hvθ) |].
      intros y _. unfold set_env_drop, θc0.
      replace (List.length (cargs_ctx p D Mk gs)) with (List.length vals) by (rewrite length_cargs_ctx; lia).
      apply set_env_extend_kinded_ge.
    - unfold θc0. rewrite set_env_values_extend_kinded by (rewrite length_cargs_ctx; lia). apply list_set_eq_refl. }
  pose proof (set_env_rel_retarget T γ Δ nil θc0 (us ++ ns0 ++ vals) Hass1 ltac:(rewrite List.app_nil_r; exact Hθc0) Hvals) as Hrt.
  rewrite List.app_nil_r in Hrt.
  destruct (set_env_rel_per T γ Δ HTc) as [Hsym Htrans].
  pose proof (Htrans _ _ _ (Hsym _ _ Hrt) Hrt) as Hθc1.
  pose proof (List.Forall2_length Hvals) as HlΔv. rewrite length_set_env_values in HlΔv.
  assert (Hθc : set_env_in T γ Δ θc).
  { apply (env_in_closed_agree T γ Hfn Hmods Hgw Δ _ θc Hs1 Hass1 HTc Hθc1).
    - intros x Hx. apply set_env_extend_kinded_lt. lia.
    - intros x. unfold set_env_drop, θc. rewrite HlΔv, set_env_extend_kinded_ge. exact (set_env_rel_eq T γ _ _ _ Hρ x). }
  clear Hθc1 Hrt Hsym Htrans Hθc0 Hvals θc0 Hfitθ Hvθ.
  (* the parameters and the arguments, as variables, substitute their context *)
  assert (Hδ' : gc_deps ⍮ gc_stack ⍮ con_inst_ctx Γ p D Mk Us gs ⊢ˢ sb_of_list β (vars_from na nn ++ vars_from 0 na)
                 : [] ++ con_inst_ctx Γ p D Mk Us gs).
  { clear HR Hag Hθc HTc HUv Hρa Hcar Hfit Hmok Hcok HG.
    assert (Hlc : List.length (cargs_ctx p D Mk gs ++ im_nparams Mk) = na + nn)
      by (rewrite List.length_app, length_cargs_ctx; reflexivity).
    cbn [List.app]. rewrite Econ at 2.
    apply wf_sub_of_list; [ apply all_assumptions_sub, List.Forall_app; split;
                              [ apply cargs_ctx_aux_ass | exact (decl_typed_nparams_ass _ _ _ HDt _ _ Hk) ]
                          | rewrite <- Econ; exact HΨa | exact Hβt
                          | rewrite ?length_tele_sub, !List.length_app, !length_vars_from, ?length_cargs_ctx; unfold nn, na, im_nn in *; lia |].
    change (vars_from na nn) with (vars_from (0 + na) nn). rewrite vars_from_app.
    intros j N A HN HA. rewrite tele_insts_tele_sub in HA.
    replace 0 with (List.length (@nil centry)) in HN, HA by reflexivity.
    rewrite Econ. change (tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) (sb_of_list sb_id Us) ++ Γ)
      with (nil ++ tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) (sb_of_list sb_id Us) ++ Γ).
    replace (nn + na) with (List.length (cargs_ctx p D Mk gs ++ im_nparams Mk)) in HN, HA by lia.
    eapply (wf_vars_tele_gen _ _ nil _ (sb_of_list sb_id Us) _ Γ (ind_nu D));
      [ apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_typed_nparams_ass _ _ _ HDt _ _ Hk) ]
      | apply List.Forall_app; split; [ eapply cargs_ctx_mvc; eassumption | exact (decl_nparams_mvc _ _ _ HDt _ _ Hk) ]
      | apply ctx_scoped_app; split;
        [ rewrite length_im_nparams; eapply decl_closed_cargs_scoped; eassumption | eapply decl_closed_nparams_scoped; eassumption ]
      | cbn [List.app]; rewrite <- Econ; exact HΨa | | exact HN | exact HA ].
    intros y Hy; unfold β; cbn [sb_compose]; rewrite <- sentry_exp_sub, exp_sub_of_wk; f_equal.
    cbn [List.length]. f_equal. rewrite Hlc. lia. }
  (* the parameters and the arguments substitute the closed context *)
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hgw HDs HD Hk Hin gs nil (eq_sym (List.app_nil_r gs))) as (Hw1 & _ & _). fold Δ in Hw1.
  pose proof (wf_ctx_closed_app _ _ _ _ Hass1 Hs1 Hw1 HcΓ) as HwΓ1.
  assert (Hσf : gc_deps ⍮ gc_stack ⍮ con_inst_ctx Γ p D Mk Us gs
                 ⊢ˢ sb_of_list (sb_of_list β (List.map (fun U => exp_sub U β) Us ++ vars_from na nn)) (vars_from 0 na)
                 : cargs_ctx p D Mk gs ++ im_params D Mk ++ Γ).
  { rewrite <- sb_of_list_app, <- List.app_assoc.
    unfold im_params. rewrite List.app_assoc, List.app_assoc, <- (List.app_assoc _ (ind_uparams D) Γ).
    apply (wf_sub_uparams_prefix _ _ _ Γ β (cargs_ctx p D Mk gs ++ im_nparams Mk) (ind_uparams D) Us).
    - exact Hβt.
    - exact Hσc.
    - rewrite <- Econ. exact HΨa.
    - unfold Δ, im_params in HwΓ1. rewrite <- !List.app_assoc in HwΓ1 |- *. rewrite <- List.app_assoc in HwΓ1. exact HwΓ1.
    - rewrite List.length_app, !length_vars_from, List.length_app, length_cargs_ctx. unfold nn, im_nn. lia.
    - rewrite HUl. reflexivity.
    - rewrite <- Econ. exact Hδ'. }
  (* the values of the closed environment *)
  assert (Hlu : List.length us = ind_nu D) by (rewrite <- HUl; clear -HUv; induction HUv; cbn; congruence).
  assert (EvΔ : set_env_values Δ θc = us ++ ns0 ++ vals) by (unfold θc; apply set_env_values_extend_kinded; symmetry; exact HlΔv).
  assert (Evc : set_env_values (cargs_ctx p D Mk gs) θc = vals).
  { assert (Eθ : θc = set_env_extend_kinded (set_env_extend_kinded ρ (ctx_kinds (im_params D Mk)) (us ++ ns0))
                       (ctx_kinds (cargs_ctx p D Mk gs)) vals).
    { unfold θc, Δ. rewrite ctx_kinds_app, List.app_assoc, set_env_extend_kinded_app; [reflexivity |].
      rewrite length_ctx_kinds, List.length_app, length_im_params, Hlu, Hln. unfold nn, im_np, im_nn. lia. }
    rewrite Eθ. apply set_env_values_extend_kinded. rewrite length_cargs_ctx. exact Hlvg. }
  pose proof (HR _ ρa β k Mk SMk cs gs θc (List.map (fun U => exp_sub U β) Us ++ vars_from na nn) (vars_from 0 na)
                HΨa Hρa Hβa Hβt Hk HSk Hcs Hgs Hθc) as H.
  rewrite Evc in H. cbn [cargs_pat] in H. apply H; clear H.
  - change (cargs_ctx p D Mk gs ++ im_params D Mk) with Δ. rewrite EvΔ, List.firstn_app, List.firstn_all2 by lia.
    rewrite Hlu, Nat.sub_diag. cbn [List.firstn]. rewrite List.app_nil_r. apply list_set_eq_refl.
  - rewrite List.firstn_app, List.firstn_all2 by (rewrite List.length_map; lia). rewrite List.length_map, HUl, Nat.sub_diag.
    cbn [List.firstn]. rewrite List.app_nil_r. reflexivity.
  - rewrite List.length_app, List.length_map, length_vars_from. unfold im_np. unfold nn in *. lia.
  - rewrite length_vars_from. reflexivity.
  - rewrite skipn_app_len by (rewrite List.length_map; exact HUl). exact Hδ'.
  - exact Hσf.
  - exact Hag.
Qed.

(** At a constructor of a member with a block, at arguments drawn from
    points of the carriers, the container's wrapped branch at the
    container's branch environment, whose recursive results are the
    group's at the container's paths ([sel_ihs]), reads as the group's
    branch at the group's branch environment. *)
Lemma wrapped_branch_interp : forall S k Mk SMk cs gs vals θk b n B FS FB FB' m Mm qc k' Is vm D' i' Mi' gs',
    set_sub S (carrier_fixed_point G us U U) ->
    ind_member D k = Some Mk -> im_is_rview Mk = false ->
    List.nth_error (set_group_members G) k = Some SMk -> In cs (set_member_constructors SMk) ->
    ind_con Mk (set_constructor_name cs) = Some gs ->
    set_env_in T γ (im_params D Mk) θk -> list_set_eq (uniform_values D Mk θk) us ->
    arguments_fit G U S (us ++ set_env_values (im_nparams Mk) θk) (set_constructor_arguments cs) vals ->
    List.nth_error Bks k = Some b -> brs_lookup (eb_brs b) (set_constructor_name cs) = Some (n, B) ->
    set_exp_eq_with T γ (elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ)
      (elim_branch_type p D k Mk (set_constructor_name cs) gs (eb_motive b) Us) B B FS FB FB' ->
    ind_member D m = Some Mm -> im_head Mm = mh_view qc k' Is vm -> ind_lookup gc_deps gc_stack qc = Some D' ->
    ind_member D' i' = Some Mi' -> im_is_rview Mi' = false -> List.nth_error vm i' = Some k ->
    ind_con Mi' (set_constructor_name cs) = Some gs' -> cargs_correspond vm gs' gs ->
    List.length (sel_ihs D' D gs' gs (ihs_values T γ Γ ρ r p Us Bks V D (im_nn Mk) nil gs vals)) = cargs_nrec D' gs' ->
    set_interp T γ
      (elim_bctx r qc D' Mi' gs' (blocks_motives (view_wrap r p qc D D' vm Us (List.map (fun I => exp_sub I (sb_of_list sb_id Us)) Is) Bks))
         (List.map (fun I => exp_sub I (sb_of_list sb_id Us)) Is) ++ Γ)
      (set_env_extend_kinded ρ
         (ctx_kinds (elim_bctx r qc D' Mi' gs' (blocks_motives (view_wrap r p qc D D' vm Us (List.map (fun I => exp_sub I (sb_of_list sb_id Us)) Is) Bks))
            (List.map (fun I => exp_sub I (sb_of_list sb_id Us)) Is)))
         (set_env_values (im_nparams Mk) θk ++ vals ++
          sel_ihs D' D gs' gs (ihs_values T γ Γ ρ r p Us Bks V D (im_nn Mk) nil gs vals)))
      (snd (wrap_branch r p D D' Us Bks Mk (eb_brs b) (set_constructor_name cs) gs'))
      (FB (set_env_extend_kinded ρ (ctx_kinds (elim_bctx r p D Mk gs (blocks_motives Bks) Us))
             (set_env_values (im_nparams Mk) θk ++ vals ++ ihs_values T γ Γ ρ r p Us Bks V D (im_nn Mk) nil gs vals))).
Proof.
  intros S k Mk SMk cs gs vals θk b n B FS FB FB' m Mm qc k' Is vm D' i' Mi' gs' HSf Hk Hrv HSk Hcs Hgs Hθk Huni Hfit Hb Hlook HBr0
    Hm Hh HD' Hi' Hri' Hv Hcon' Hcorr Hlws.
  pose proof (arguments_fit_length _ _ _ _ _ _ Hfit) as Hlv.
  pose proof (args_ihs_reading S k Mk SMk cs gs vals θk HSf Hk HSk Hcs Hgs Hθk Huni Hfit) as HEI.
  pose proof HS1 as [HΓ HcΓ HDsrc Hσ HDt Hcl HUl HMwf HMot HMctx HMh HBk Hbτ Hbctx Hbrs HBr HV HBt HUs _].
  pose proof (ind_lookup_gc_sub _ _ _ _ _ _ (set_source_sub T γ Θs Ξs Hemb) HDsrc) as HD.
  pose proof (set_source_groups T γ Θs Ξs Hemb _ _ HDsrc) as HG. fold G in HG.
  pose proof (set_group_ok_respects _ _ _ _ _ HG) as HGr.
  (* the group's branch, at the group's branch environment *)
  assert (HQ1 : set_sub (carrier_fixed_point G us U U) (carrier_points_with G us U U (elim_point_with T γ Γ ρ r p Us Bks V D i no_extra us))).
  { apply (fixed_point_in_points_with G us U U HGr). intros k0 ns0' v0 Hn0 Hv0 Hc0. split; [| apply no_extra_point].
    eapply elim_point_step; first [eassumption | exact no_extra_resp | intros; apply no_extra_point]. }
  pose proof (set_group_ok_respects _ _ _ _ _ HG _ _ _ HSk Hcs) as Hrs.
  pose proof (set_arguments_shape_length _ _ (set_constructor_ok_shape _ _ _ _ _ _ _ _
                (set_member_ok_constructors _ _ _ _ _ _ _ (set_group_ok_members _ _ _ _ _ HG _ _ _ Hk HSk) cs gs Hcs Hgs))) as Hlsh.
  assert (Hlvg : List.length vals = List.length gs) by lia. clear Hlv Hlsh.
  assert (Hfit1 : arguments_fit G U (carrier_points_with G us U U (elim_point_with T γ Γ ρ r p Us Bks V D i no_extra us))
                    (us ++ set_env_values (im_nparams Mk) θk) (set_constructor_arguments cs) vals)
    by (eapply arguments_fit_mono; [intros z Hz; exact (HQ1 _ (HSf _ Hz)) | exact Hrs | exact Hfit]).
  destruct (block_branch_elim T γ Hfn Hmods Hgw Θs Ξs Hemb Γ ρ r p Us Bks V D i Fσ U no_extra no_extra_resp HΓ HcΓ Hρ HDsrc Hσ HDt Hcl HUl
              HMwf HMot HMctx HMh HBk Hcar Hbτ Hbctx HBr HV HBt k Mk SMk cs gs vals θk b n B FS FB FB' Hk Hrv HSk Hcs Hgs Hθk Huni
              Hfit1 Hb Hlook HBr0) as [Hρb _].
  pose proof HBr0 as [_ HFB _ _ _].
  pose proof (set_denotes_exists _ _ _ _ _ HFB _ Hρb) as Hres.
  pose proof (proj2 (Hbctx k Mk _ gs Hk Hgs)) as Hbw.
  clear HMwf HMot HMctx HMh HBk Hbτ Hbctx Hbrs HBr HV HQ1 Hfit1 HBr0 HFB HG HGr Hrs Hcar.
  (* the wrapped branch and its substitution *)
  pose proof (decls_of_ctx _ _ _ HcΓ) as HDs.
  destruct (decl_typed_view_wrap _ _ _ HDt _ _ _ _ _ _ Hm Hh) as (D2 & Hl2 & Hvw). rewrite HD' in Hl2. injection Hl2 as <-.
  pose proof (view_blocks_branch_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hgw HDs HD Hm Hh HD' Hvw HcΓ HUl HUs HBt
                i' Mi' k Mk _ gs' gs Hi' Hri' Hv Hk Hcon' Hgs Hcorr) as Hδt.
  pose proof (view_blocks_branch_base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hgw HDs HD Hm Hh HD' Hvw HcΓ HUl HUs HBt
                i' Mi' k Mk _ gs' gs Hi' Hri' Hv Hk Hcon' Hgs) as Hσat.
  unfold wrap_branch; cbv zeta; rewrite Hgs, Hlook; cbn [snd].
  set (Is' := List.map (fun I => exp_sub I (sb_of_list sb_id Us)) Is) in *.
  set (Δc := elim_bctx r qc D' Mi' gs' (blocks_motives (view_wrap r p qc D D' vm Us Is' Bks)) Is') in *.
  set (ihv := ihs_values T γ Γ ρ r p Us Bks V D (im_nn Mk) [] gs vals) in *.
  set (ns0 := set_env_values (im_nparams Mk) θk) in *.
  clear HS1 HΓ Hσ HSf Hfit HSk Hcs Huni Hθk Hb.
  pose proof (cargs_correspond_length _ _ _ Hcorr) as Hlg.
  cbn [cargs_pat] in Hres, Hρb.
  set (nn := im_nn Mk) in *. set (na := List.length gs') in *. set (nr' := cargs_nrec D' gs') in *.
  set (w := wk_shiftn (nn + na + nr')) in *.
  set (nv := vars_from (nr' + na) nn) in *. set (av := vars_from nr' na) in *.
  set (ws := sel_ihs D' D gs' gs ihv) in *.
  assert (Hln : List.length ns0 = nn) by (unfold ns0, nn, im_nn; rewrite length_set_env_values; reflexivity).
  assert (Hlall : List.length (ns0 ++ vals ++ ws) = nn + na + nr') by (rewrite !List.length_app; lia).
  set (ρb' := set_env_extend_kinded ρ (ctx_kinds Δc) (ns0 ++ vals ++ ws)).
  assert (Hbase : forall y, sub_entry_agrees T γ (Δc ++ Γ) ρb' (sb_of_wk w y) (ρ y)).
  { intros y. apply sub_agrees_var. unfold ρb', w. cbn [wk_shiftn]. rewrite Nat.add_comm, <- Hlall. apply set_env_extend_kinded_ge. }
  (* the parameters and the arguments, as variables, read their values *)
  assert (HL : set_interp_list T γ (Δc ++ Γ) ρb' (nv ++ av) (ns0 ++ vals)).
  { apply set_interp_list_app.
    - pose proof (set_interp_list_vars_mid (Δc ++ Γ) nil ns0 (vals ++ ws) ρ (ctx_kinds Δc)) as H.
      cbn [List.app] in H. rewrite List.length_app, Hln, Hlws, Hlvg, <- Hlg, Nat.add_comm in H. exact H.
    - pose proof (set_interp_list_vars_mid (Δc ++ Γ) ns0 vals ws ρ (ctx_kinds Δc)) as H.
      rewrite Hlws, Hlvg, <- Hlg in H. exact H. }
  (* the recursive eliminations, read in the constructor's context, moved to the container's branch's *)
  assert (HEI' : set_interp_list T γ (Δc ++ Γ) ρb'
                  (elim_ihs r p D (List.map (fun U0 => exp_wk U0 w) Us) (blocks_wk Bks w)
                     (sb_of_list (sb_of_wk w) (List.map (fun U0 => exp_wk U0 w) Us ++ nv)) nn gs av) ihv).
  { assert (Hset : sub_setting T γ (con_inst_ctx Γ p D Mk Us gs)
                     (set_env_extend_kinded ρ (ctx_kinds (cargs_ctx p D Mk gs ++ im_nparams Mk)) (ns0 ++ vals))
                     nil (con_inst_ctx Γ p D Mk Us gs) (Δc ++ Γ) (sb_of_list (sb_of_wk w) (nv ++ av)) ρb' ρb').
    { constructor; [reflexivity | rewrite con_inst_ctx_con_inst_tele; exact Hσat | intros x Hx; cbn in Hx; lia
                   | intros y; reflexivity | intros x; exact (sub_agrees_of_list T γ _ _ _ _ HL _ ρ _ Hbase x)]. }
    pose proof (wf_sub_cinst _ _ _ _ _ _ _ _ Hgw HDs HD Hk HcΓ (wf_sub_uparams _ _ _ HDt Hcl _ _ HcΓ HUl HUs)
                  _ gs gs nil (cons_lookup_in _ _ _ Hgs) (eq_sym (List.app_nil_r gs))) as [HΨa _].
    pose proof (proj1 (proj2 (set_interp_sub_all T γ)) _ _ _ _ HEI nil _ _ _ ρb' ρb' HΨa Hset) as H.
    cbn [tele_sub List.app List.length sb_qn] in H.
    rewrite (elim_ihs_moved r p D Us Bks nn gs w nv av) in H by (unfold nv, av; rewrite !length_vars_from; lia).
    exact H. }
  (* the wrapped recursive results read the group's: the container's at its paths *)
  assert (HW : set_interp_list T γ (Δc ++ Γ) ρb'
                (wrap_ihs D' D gs' gs (elim_ihs r p D (List.map (fun U0 => exp_wk U0 w) Us) (blocks_wk Bks w)
                     (sb_of_list (sb_of_wk w) (List.map (fun U0 => exp_wk U0 w) Us ++ nv)) nn gs av) 0 nr') ihv).
  { pose proof (cargs_same_kinds_of_correspond _ _ _ Hcorr) as Hsk.
    assert (Hli : List.length ihv = cargs_nrec D gs) by (unfold ihv; eapply length_ihs_values; eassumption).
    assert (HlE : List.length (elim_ihs r p D (List.map (fun U0 => exp_wk U0 w) Us) (blocks_wk Bks w)
                     (sb_of_list (sb_of_wk w) (List.map (fun U0 => exp_wk U0 w) Us ++ nv)) nn gs av) = List.length ihv)
      by (clear -HEI'; induction HEI'; cbn; congruence).
    unfold ρb' in HEI' |- *. rewrite List.app_assoc in HEI' |- *.
    pose proof (interp_wrap_ihs _ ρ (ctx_kinds Δc) D' D gs' gs _ ihv (ns0 ++ vals) ws 0 Hsk (eq_trans HlE Hli) HEI') as H.
    pose proof (length_sel_ihs D' D gs' gs ihv Hsk Hli) as Hls. fold ws in Hls.
    specialize (H ltac:(lia)). rewrite Hlws in H. cbn [List.skipn] in H.
    unfold ws in H. rewrite merge_sel_ihs in H by assumption. exact H. }
  (* the group's branch, moved by the wrapped branch's substitution *)
  change (cargs_pat []) with (@nil bool) in Hres. fold ihv in Hres.
  set (W := wrap_ihs D' D gs' gs (elim_ihs r p D (List.map (fun U0 => exp_wk U0 w) Us) (blocks_wk Bks w)
              (sb_of_list (sb_of_wk w) (List.map (fun U0 => exp_wk U0 w) Us ++ nv)) nn gs av) 0 nr') in *.
  assert (HLW : set_interp_list T γ (Δc ++ Γ) ρb' (nv ++ av ++ W) (ns0 ++ vals ++ ihv))
    by (rewrite (List.app_assoc nv), (List.app_assoc ns0); apply set_interp_list_app; [exact HL | exact HW]).
  assert (Hset : sub_setting T γ (elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ)
                   (set_env_extend_kinded ρ (ctx_kinds (elim_bctx r p D Mk gs (blocks_motives Bks) Us)) (ns0 ++ vals ++ ihv))
                   nil (elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ) (Δc ++ Γ) (sb_of_list (sb_of_wk w) (nv ++ av ++ W)) ρb' ρb')
    by (constructor; [reflexivity | exact Hδt | intros x Hx; cbn in Hx; lia
                     | intros y; reflexivity | intros x; exact (sub_agrees_of_list T γ _ _ _ _ HLW _ ρ _ Hbase x)]).
  pose proof (proj1 (set_interp_sub_all T γ) _ _ _ _ Hres nil _ _ _ ρb' ρb' Hbw Hset) as H.
  cbn [tele_sub List.app List.length sb_qn] in H. exact H.
Qed.

(** At a constructor of a member with a block, at arguments drawn from
    points of the carriers, an element equal to the constructor's has, at
    a container's member the view takes to the member, the container's
    eliminator's result the group's, given the container's recursive
    results of the arguments: the group's at the container's paths. *)
Lemma container_block_elim : forall S k Mk SMk cs gs vals θk m Mm qc k' Is vm D' i' Mi' gs' w',
    r <> ak_propositional -> set_sub S (carrier_fixed_point G us U U) ->
    ind_member D k = Some Mk -> im_is_rview Mk = false ->
    List.nth_error (set_group_members G) k = Some SMk -> In cs (set_member_constructors SMk) ->
    ind_con Mk (set_constructor_name cs) = Some gs ->
    set_env_in T γ (im_params D Mk) θk -> list_set_eq (uniform_values D Mk θk) us ->
    arguments_fit G U S (us ++ set_env_values (im_nparams Mk) θk) (set_constructor_arguments cs) vals ->
    ind_member D m = Some Mm -> im_head Mm = mh_view qc k' Is vm -> ind_lookup gc_deps gc_stack qc = Some D' ->
    ind_member D' i' = Some Mi' -> im_is_rview Mi' = false -> List.nth_error vm i' = Some k ->
    ind_con Mi' (set_constructor_name cs) = Some gs' -> cargs_correspond vm gs' gs ->
    im_ref p k Mk = im_ref qc i' Mi' ->
    set_eq w' (con_val (set_constructor_name cs) (set_env_values (im_nparams Mk) θk ++ vals)) ->
    set_elim T γ Γ ρ r p Us Bks k w' (elim_result T γ Γ ρ r p Us Bks V k w') ->
    set_ihs T γ Γ ρ r qc (List.map (fun I => exp_sub I (sb_of_list sb_id Us)) Is)
      (view_wrap r p qc D D' vm Us (List.map (fun I => exp_sub I (sb_of_list sb_id Us)) Is) Bks) gs' vals
      (sel_ihs D' D gs' gs (ihs_values T γ Γ ρ r p Us Bks V D (im_nn Mk) nil gs vals)) ->
    List.length (sel_ihs D' D gs' gs (ihs_values T γ Γ ρ r p Us Bks V D (im_nn Mk) nil gs vals)) = cargs_nrec D' gs' ->
    set_elim T γ Γ ρ r qc (List.map (fun I => exp_sub I (sb_of_list sb_id Us)) Is)
      (view_wrap r p qc D D' vm Us (List.map (fun I => exp_sub I (sb_of_list sb_id Us)) Is) Bks) i' w'
      (elim_result T γ Γ ρ r p Us Bks V k w').
Proof.
  intros S k Mk SMk cs gs vals θk m Mm qc k' Is vm D' i' Mi' gs' w' Hr HSf Hk Hrv HSk Hcs Hgs Hθk Huni Hfit Hm Hh HD' Hi' Hri' Hv
    Hcon' Hcorr Href Ew Hel Hihs Hlws.
  pose proof HS1 as [HΓ HcΓ HDsrc Hσ HDt Hcl HUl HMwf HMot HMctx HMh HBk Hbτ Hbctx Hbrs HBr HV HBt HUs _].
  pose proof (ind_lookup_gc_sub _ _ _ _ _ _ (set_source_sub T γ Θs Ξs Hemb) HDsrc) as HD.
  destruct (HBk k Mk Hk Hrv) as [b Hb].
  destruct (brs_names_lookup _ _ _ _ (Hbrs k Mk b Hk Hb) Hgs) as (n & B & Hlook & HinB).
  destruct (HBr k Mk b _ gs n B Hk Hb Hgs HinB) as (FS & FB & FB' & HBr0).
  pose proof (wrapped_branch_interp S k Mk SMk cs gs vals θk b n B FS FB FB' m Mm qc k' Is vm D' i' Mi' gs' HSf Hk Hrv HSk Hcs Hgs
                Hθk Huni Hfit Hb Hlook HBr0 Hm Hh HD' Hi' Hri' Hv Hcon' Hcorr Hlws) as HI.
  (* the group's result is the branch's *)
  pose proof (set_source_groups T γ Θs Ξs Hemb _ _ HDsrc) as HG. fold G in HG.
  assert (HQ1 : set_sub (carrier_fixed_point G us U U) (carrier_points_with G us U U (elim_point_with T γ Γ ρ r p Us Bks V D i no_extra us))).
  { apply (fixed_point_in_points_with G us U U (set_group_ok_respects _ _ _ _ _ HG)). intros k0 ns0' v0 Hn0 Hv0 Hc0. split; [| apply no_extra_point].
    eapply elim_point_step; first [eassumption | exact no_extra_resp | intros; apply no_extra_point]. }
  assert (Hfit1 : arguments_fit G U (carrier_points_with G us U U (elim_point_with T γ Γ ρ r p Us Bks V D i no_extra us))
                    (us ++ set_env_values (im_nparams Mk) θk) (set_constructor_arguments cs) vals)
    by (eapply arguments_fit_mono; [intros z Hz; exact (HQ1 _ (HSf _ Hz)) | exact (set_group_ok_respects _ _ _ _ _ HG _ _ _ HSk Hcs) | exact Hfit]).
  destruct (block_branch_elim T γ Hfn Hmods Hgw Θs Ξs Hemb Γ ρ r p Us Bks V D i Fσ U no_extra no_extra_resp HΓ HcΓ Hρ HDsrc Hσ HDt Hcl HUl
              HMwf HMot HMctx HMh HBk Hcar Hbτ Hbctx HBr HV HBt k Mk SMk cs gs vals θk b n B FS FB FB' Hk Hrv HSk Hcs Hgs Hθk Huni
              Hfit1 Hb Hlook HBr0) as [_ Helim1].
  pose proof (set_elim_functional T γ Hfn Hmods Γ ρ r p Us Bks Hρ _ _ _ _ Hel (Helim1 Hr w' Ew)) as E1.
  destruct (member_reference T γ Θs Ξs Hemb p D HDsrc HDt k Mk Hk Hrv) as (Dq & Mq & [HDq HMq Hnnq]).
  rewrite Href in HDq, HMq.
  clear HMwf HMot HMctx HMh Hbτ Hbrs HBr HV HQ1 Hfit1 Helim1 Hcar.
  (* the container's block at [i'] and its branch at the constructor *)
  pose proof (decls_of_ctx _ _ _ HcΓ) as HDs.
  destruct (decl_typed_view_wrap _ _ _ HDt _ _ _ _ _ _ Hm Hh) as (D2 & Hl2 & Hvw). rewrite HD' in Hl2. injection Hl2 as <-.
  destruct (view_wrap_ok_members _ _ _ Hvw _ _ _ Hi' Hv) as (Mv & HMv & Hnnv & _). rewrite Hk in HMv. injection HMv as <-.
  pose proof (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ (HDs qc D' HD'))) as Hsuf'.
  set (Is' := List.map (fun I => exp_sub I (sb_of_list sb_id Us)) Is) in *.
  pose proof (nth_error_view_wrap r p qc D D' vm Us Is' Bks i' Mi' Hsuf' Hi' Hri') as HBk'.
  rewrite (view_wrap_block_eq r p qc D D' vm Us Is' Bks i' Mi' k Mk b Hv Hb Hk) in HBk'.
  pose proof (brs_lookup_wrap r p D D' Us Bks Mk (eb_brs b) (im_cons Mi') (set_constructor_name cs)) as Hlk'.
  change (cons_lookup (im_cons Mi') (set_constructor_name cs)) with (ind_con Mi' (set_constructor_name cs)) in Hlk'.
  rewrite Hcon' in Hlk'. cbn [option_map] in Hlk'.
  pose proof (cargs_correspond_length _ _ _ Hcorr) as Hlg.
  pose proof (set_arguments_shape_length _ _ (set_constructor_ok_shape _ _ _ _ _ _ _ _
                (set_member_ok_constructors _ _ _ _ _ _ _ (set_group_ok_members _ _ _ _ _ HG _ _ _ Hk HSk) cs gs Hcs Hgs))) as Hlsh.
  pose proof (arguments_fit_length _ _ _ _ _ _ Hfit) as Hlv.
  assert (Hlen3 : List.length (set_env_values (im_nparams Mk) θk ++ vals ++
                  sel_ihs D' D gs' gs (ihs_values T γ Γ ρ r p Us Bks V D (im_nn Mk) [] gs vals))
                = List.length (elim_bctx r qc D' Mi' gs' (blocks_motives (view_wrap r p qc D D' vm Us Is' Bks)) Is'))
    by (rewrite length_elim_bctx, !List.length_app, Hlws, length_set_env_values; unfold im_nn in *; lia).
  (* the container's eliminator at the element: the wrapped branch's value, the group's result *)
  apply (set_elim_resp T γ _ _ _ _ _ _ _ _ _ _ (set_elim_con T γ Γ ρ r qc Is' _ i' w' _ D' Mi' _ _ Dq Mq _ gs'
           (set_env_values (im_nparams Mk) θk) vals _ _ _ _ _ _ _ HD' Hi' (surjective_pairing _) HDq HMq Hcon' Ew
           ltac:(rewrite Hnnq; unfold im_nn; apply length_set_env_values) ltac:(lia) HBk' Hlk' Hihs Hlen3
           (view_blocks_branch_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hgw HDs HD Hm Hh HD' Hvw HcΓ HUl HUs HBt i' Mi' _ gs' Hi' Hcon') HI)).
  apply set_eq_sym. exact E1.
Qed.

Section ViewAt.
  (** The view: the group's member [m], [Mm], a view of the container's
      member [k'] at the instance [Is], of the members [vm] of the
      container's group [D'] at [qc] *)
  Variables (m : nat) (Mm : imember) (qc : qname) (k' : nat) (Is : list exp) (vm : list nat) (D' : ind_decl).
  Hypotheses (Hm : ind_member D m = Some Mm) (Hh : im_head Mm = mh_view qc k' Is vm)
    (HD' : ind_lookup gc_deps gc_stack qc = Some D').

  Let Is' := List.map (fun I => exp_sub I (sb_of_list sb_id Us)) Is.
  Let Bks' := view_wrap r p qc D D' vm Us Is' Bks.
  Let XV := view_agree Γ ρ r p Us Bks V D vm qc Is' Bks' D'.
  Let S := carrier_points_with G us U U (elim_point_with T γ Γ ρ r p Us Bks V D i XV us).

(** The view takes each member of the container's group to a member of
    the group ([view_member]). *)
Lemma view_at_members : forall j' j, List.nth_error vm j' = Some j ->
    exists Mj' Mj, ind_member D' j' = Some Mj' /\ view_member p D qc D' vm j' Mj' j Mj.
Proof.
  intros j' j Hj.
  pose proof HS1 as [_ HcΓ _ _ HDt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  destruct (decl_typed_view_wrap _ _ _ HDt _ _ _ _ _ _ Hm Hh) as (D2 & Hl2 & Hvw). rewrite HD' in Hl2. injection Hl2 as <-.
  destruct (nth_error_lt_some (ind_members D') j') as [Mj' HMj'].
  { rewrite <- (view_wrap_ok_length _ _ _ Hvw). apply List.nth_error_Some. congruence. }
  destruct (view_member_of_typed _ _ p D m Mm qc k' Is vm D' j' Mj' HDt Hm Hh HD' HMj') as (v & Mv & Hvmb).
  pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvmb) as Hv. rewrite Hj in Hv. injection Hv as <-.
  exists Mj', Mv. split; [exact HMj' | exact Hvmb].
Qed.

(** The induction's step for the view: an element built from arguments
    drawn from the points whose results agree with the container's has its
    results agree.  At a member with a block, the container's eliminator
    at every member the view takes to it is the wrapped branch's value
    ([container_block_elim]); at a record view, the container's results of
    its fields are the group's at the container's paths. *)
Lemma view_step : forall k ns v, set_mem (list_code ns) U -> set_mem v U ->
    constructed_from G us U S k ns v -> extra_point T γ D XV us k ns v.
Proof.
  intros k ns v HnsU HvU Hc Mk θk Hk Hθk Huni Hns.
  pose proof HS1 as [HΓ HcΓ HDsrc Hσ HDt Hcl HUl HMwf HMot HMctx HMh HBk Hbτ Hbctx Hbrs HBr HV HBt HUs _].
  pose proof (ind_lookup_gc_sub _ _ _ _ _ _ (set_source_sub T γ Θs Ξs Hemb) HDsrc) as HD.
  pose proof (set_source_groups T γ Θs Ξs Hemb _ _ HDsrc) as HG. fold G in HG.
  pose proof (set_group_ok_respects _ _ _ _ _ HG) as HGr.
  assert (HSfix : set_sub S (carrier_fixed_point G us U U))
    by (intros z Hz; apply (set_mem_separation _ _ _ (carrier_points_with_pred_resp _)) in Hz as [Hz _]; exact Hz).
  destruct Hc as (SMk & cs & vals & [HSk Hcs Hfit Ev]).
  pose proof (set_group_ok_respects _ _ _ _ _ HG _ _ _ HSk Hcs) as Hrs.
  pose proof (set_group_ok_members _ _ _ _ _ HG _ _ _ Hk HSk) as Hmok.
  set (ns0 := set_env_values (im_nparams Mk) θk) in *.
  assert (Hfit0 : arguments_fit G U S (us ++ ns0) (set_constructor_arguments cs) vals)
    by (eapply arguments_fit_resp; [exact Hrs | apply list_set_eq_app; [apply list_set_eq_refl | apply list_set_eq_sym; exact Hns]
                                   | apply list_set_eq_refl | exact Hfit]).
  assert (Hcn : In (set_constructor_name cs) (List.map fst (im_cons Mk)))
    by (rewrite <- (set_member_ok_names _ _ _ _ _ _ _ Hmok); apply List.in_map; exact Hcs).
  destruct (cons_lookup_of_names _ _ Hcn) as [gs Hgs]. change (ind_con Mk (set_constructor_name cs) = Some gs) in Hgs.
  assert (Hvmem : set_mem v (member_carrier G us U U k ns)).
  { apply member_carrier_intro; [exact HGr | exact HnsU | exact HvU |].
    exists SMk, cs, vals. constructor; [exact HSk | exact Hcs | eapply arguments_fit_mono; [exact HSfix | exact Hrs | exact Hfit] | exact Ev]. }
  assert (Hvm0 : set_mem v (member_carrier G us U U k ns0))
    by (eapply set_mem_eq_r; [apply candidate_carrier_resp; exact (list_set_eq_sym _ _ Hns) | exact Hvmem]).
  pose proof (decls_of_ctx _ _ _ HcΓ) as HDs.
  pose proof (decl_typed_record_struct _ _ _ HDt) as HrsD.
  pose proof (decl_typed_record_struct _ _ _ (HDs qc D' HD')) as HrsQ.
  pose proof (leaves_coherent_of_order D (rview_struct_order _ _ _ HrsD)) as HlcD.
  pose proof (leaves_coherent_of_order D' (rview_struct_order _ _ _ HrsQ)) as HlcQ.
  (* the recursive arguments have their shapes' ends agree *)
  assert (Hrec : forall gs' n t' t v0, cargs_correspond vm gs' gs -> List.nth_error gs' n = Some (ca_rec t') ->
            List.nth_error gs n = Some (ca_rec t) -> List.nth_error vals n = Some v0 ->
            exists RV Mk0 Ta φ Bs1 θ, shape_closed_ok T γ Γ ρ r p Us Bks V D i RV XV Mk0 Ta φ Bs1 t θ v0).
  { intros gs' n0 t' t v0 _ _ H2 H3.
    destruct (List.nth_error_split gs n0 H2) as (gs1 & gs2 & Egs & Hl1). subst n0.
    destruct (block_arg_closed T γ Hfn Hmods Hgw Θs Ξs Hemb Γ ρ r p Us Bks V D i Fσ U XV (view_agree_resp Γ ρ r p Us Bks V D vm qc Is' Bks' D')
                HΓ HcΓ Hρ HDsrc Hσ HDt Hcl HUl HMwf HMot HMctx Hcar k Mk SMk cs gs vals θk gs1 t gs2 v0 Hk HSk Hcs Hgs Hθk Huni Hfit0
                Egs H3) as [_ Hcl'].
    do 6 eexists. exact Hcl'. }
  constructor.
  - (* a member with a block *)
    intros Hr Hrv i' Mi' Hi' Hvi w' Ew'.
    destruct (view_at_members i' k Hvi) as (Mj' & Mj & HMj' & Hvmb). rewrite Hi' in HMj'. injection HMj' as <-.
    pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMj. rewrite Hk in HMj. injection HMj as <-.
    pose proof (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvmb) as Erv.
    assert (Hri' : im_is_rview Mi' = false) by congruence.
    destruct (view_member_cons' _ _ _ _ _ _ _ _ _ Hvmb _ _ Hgs) as (gs' & Hcon' & Hcorr).
    pose proof (view_member_ref _ _ _ _ _ _ _ _ _ Hvmb Hri') as Href.
    assert (Ew0 : set_eq w' (con_val (set_constructor_name cs) (ns0 ++ vals))).
    { eapply set_eq_trans; [apply set_eq_sym; exact Ew' |]. eapply set_eq_trans; [exact Ev |].
      unfold constructed_element. destruct (set_member_record_fields SMk) as [fl |] eqn:Hfl.
      - exfalso. destruct (proj1 (set_member_ok_record_fields _ _ _ _ _ _ _ Hmok fl) Hfl) as (qr & Is0 & Hh').
        unfold im_is_rview in Hrv. rewrite Hh' in Hrv. discriminate.
      - unfold con_val. apply ordered_pair_resp; [apply set_eq_refl |]. apply list_code_resp.
        apply list_set_eq_app; [exact (list_set_eq_sym _ _ Hns) | apply list_set_eq_refl]. }
    (* the group's result *)
    pose proof (elim_point_of_carrier T γ Hfn Hmods Hgw Θs Ξs Hemb Γ ρ r p Us Bks V D i Fσ U no_extra no_extra_resp HΓ HcΓ Hρ HDsrc Hσ HDt Hcl
                  HUl HMwf HMot HMctx HMh HBk Hcar Hbτ Hbctx Hbrs HBr HV HBt HUs (fun k0 ns1 v1 _ _ _ => no_extra_point T γ D _ k0 ns1 v1)
                  k ns0 v Hvm0) as [HP1 _].
    destruct (HP1 Mk θk Hk Hθk Huni (list_set_eq_refl _)) as [Hres1 _ _ _].
    destruct (Hres1 Hr w' Ew') as [_ Hblk1 _]. destruct (Hblk1 Hrv) as (res1 & Hel1 & HV1).
    pose proof (elim_result_spec T γ Hfn Hmods Γ ρ r p Us Bks V Hρ _ _ _ Hel1 HV1) as Hel.
    (* the container's recursive results *)
    assert (Hsk : cargs_same_kinds gs' gs) by exact (cargs_same_kinds_of_correspond _ _ _ Hcorr).
    pose proof (arguments_fit_length _ _ _ _ _ _ Hfit0) as Hlv.
    pose proof (set_arguments_shape_length _ _ (set_constructor_ok_shape _ _ _ _ _ _ _ _
                  (set_member_ok_constructors _ _ _ _ _ _ _ Hmok cs gs Hcs Hgs))) as Hlsh.
    pose proof (cargs_correspond_length _ _ _ Hcorr) as Hlg.
    pose proof (set_ihs_container Γ ρ r p Us Bks V D i vm qc Is' Bks' D' HD' HrsD HrsQ view_at_members Hr gs' gs (im_nn Mk) nil vals
                  Hcorr ltac:(lia) (fun n0 t' t v0 H1 H2 H3 => Hrec gs' n0 t' t v0 Hcorr H1 H2 H3)) as Hihs.
    assert (Hlws : List.length (sel_ihs D' D gs' gs (ihs_values T γ Γ ρ r p Us Bks V D (im_nn Mk) nil gs vals)) = cargs_nrec D' gs').
    { rewrite length_sel_ihs by (first [exact Hsk | eapply length_ihs_values; lia]).
      exact (cargs_container_count_view p qc D D' vm HlcD HlcQ HrsD HrsQ view_at_members gs' gs Hcorr). }
    exact (container_block_elim S k Mk SMk cs gs vals θk m Mm qc k' Is vm D' i' Mi' gs' w' Hr HSfix Hk Hrv HSk Hcs Hgs Hθk Huni Hfit0
             Hm Hh HD' Hi' Hri' Hvi Hcon' Hcorr Href Ew0 Hel Hihs Hlws).
  - (* a record view: its fields, at the container's paths *)
    intros Hr qr Is0 fl c gsr i' Mi' Is1 c' gs' Hh0 Hcs1 Hi' Hh1 Hcs1' Hvi w' Ew'.
    pose proof (member_closed_rview_nn _ _ (decl_closed_members _ Hcl _ _ Hk) _ _ _ Hh0) as Hnp.
    assert (Ens0 : ns0 = nil) by (unfold ns0; rewrite Hnp; reflexivity).
    rewrite Ens0, List.app_nil_r in Hfit0.
    pose proof (proj2 (set_member_ok_record_fields _ _ _ _ _ _ _ Hmok fl) (ex_intro _ qr (ex_intro _ Is0 Hh0))) as Hfl.
    destruct (set_group_ok_record_views _ _ _ _ _ HG _ _ _ HSk Hfl) as (Hnd & _ & Hargs).
    pose proof (arguments_fit_length _ _ _ _ _ _ Hfit0) as Hlv.
    assert (Hlfv : List.length fl = List.length vals) by (rewrite Hlv; symmetry; exact (Hargs cs Hcs)).
    assert (Exv : set_eq v (tuple_code (List.combine fl vals))) by (unfold constructed_element in Ev; rewrite Hfl in Ev; exact Ev).
    pose proof (cons_lookup_in _ _ _ Hgs) as Hin. rewrite Hcs1 in Hin. destruct Hin as [E | []]. injection E as Ec Eg. subst gsr.
    destruct (view_at_members i' k Hvi) as (Mj' & Mj & HMj' & Hvmb). rewrite Hi' in HMj'. injection HMj' as <-.
    pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMj. rewrite Hk in HMj. injection HMj as <-.
    destruct (view_member_cons' _ _ _ _ _ _ _ _ _ Hvmb _ _ Hgs) as (gs'' & Hcon'' & Hcorr).
    pose proof (cons_lookup_in _ _ _ Hcon'') as Hin'. rewrite Hcs1' in Hin'. destruct Hin' as [E' | []]. injection E' as _ <-.
    destruct (rview_struct_con _ _ _ HrsQ _ _ _ _ _ Hi' Hh1) as (gs3 & Hcs3 & Hlen3). rewrite Hcs1' in Hcs3. injection Hcs3 as _ <-.
    set (θ0 := set_env_drop (im_nn Mk) θk).
    assert (Hθ0 : set_env_in T γ (ind_uparams D) θ0) by exact (set_env_rel_drop T γ _ _ _ _ Hθk).
    pose proof (set_ihs_container Γ ρ r p Us Bks V D i vm qc Is' Bks' D' HD' HrsD HrsQ view_at_members Hr gs' gs 0 nil
                  (List.map (tuple_field w') fl) Hcorr ltac:(rewrite List.length_map; lia)) as H.
    rewrite (ihs_values_fields Γ ρ r p Us Bks V D w' fl gs nil nil) in H
      by (first [reflexivity | pose proof (cargs_correspond_length _ _ _ Hcorr); lia]).
    apply H. clear H.
    intros n t' t v0 _ H2 H3. rewrite List.nth_error_map in H3.
    destruct (List.nth_error fl n) as [f |] eqn:Hf; [| discriminate]. cbn in H3. injection H3 as <-.
    destruct (List.nth_error_split (List.combine fl gs) n (Typing.nth_error_combine_both _ _ _ _ _ Hf H2)) as (fs1 & fs2 & Ec2 & _).
    destruct (rview_field_closed_ok T γ Hfn Hmods Θs Ξs Hemb Γ ρ r p Us Bks V D i Fσ U XV (view_agree_resp Γ ρ r p Us Bks V D vm qc Is' Bks' D')
                HDsrc HDt Hcl HUl HMwf HMot HMctx Hcar k Mk qr Is0 fl SMk cs gs vals w' θ0 fs1 f t fs2 Hk Hh0 HSk Hcs Hgs Hfit0 Hnd Hlfv
                (set_eq_trans _ _ _ (set_eq_sym _ _ Ew') Exv) Hθ0 Huni Ec2) as [_ Hshape].
    do 6 eexists. exact Hshape.
Qed.

(** The container's results at every element of a carrier are the
    group's, at every instance of its member's parameters. *)
Lemma view_agree_of_carrier : forall k ns v, set_mem v (member_carrier G us U U k ns) -> extra_point T γ D XV us k ns v.
Proof.
  intros k ns v Hv.
  pose proof HS1 as [HΓ HcΓ HDsrc Hσ HDt Hcl HUl HMwf HMot HMctx HMh HBk Hbτ Hbctx Hbrs HBr HV HBt HUs _].
  pose proof (ind_lookup_gc_sub _ _ _ _ _ _ (set_source_sub T γ Θs Ξs Hemb) HDsrc) as HD.
  exact (proj2 (elim_point_of_carrier T γ Hfn Hmods Hgw Θs Ξs Hemb Γ ρ r p Us Bks V D i Fσ U XV
                  (view_agree_resp Γ ρ r p Us Bks V D vm qc Is' Bks' D') HΓ HcΓ Hρ HDsrc Hσ HDt Hcl HUl HMwf HMot HMctx HMh HBk Hcar
                  Hbτ Hbctx Hbrs HBr HV HBt HUs view_step k ns v Hv)).
Qed.

End ViewAt.

End ViewStep.

(** ** The Rule of the Eliminator at a View *)

(** [set_elim_view_setting Γ r p m Bks M D Mm bm Ps i qc k' vm D' FM Fns FMot]:
    the facts at one context the eliminator at a view rests on: the
    group's elimination's setting, and the container's eliminator at the
    view's blocks wrapped denoting the group's results. *)
Record set_elim_view_setting (Γ : ctx) (r : abs_kind) (p : qname) (m : nat) (Bks : list eblock) (M : exp)
    (D : ind_decl) (Mm : imember) (bm : eblock) (Ps : list exp) (i : nat) (qc : qname) (k' : nat) (vm : list nat)
    (D' : ind_decl) (FM : set_env -> aczel_set) (Fns : set_env -> list aczel_set) (FMot : set_env -> aczel_set) : Prop :=
  { (** The group's elimination's setting *)
    set_elim_view_setting_left : set_elim_setting T γ Γ r p m Bks M D Mm bm Ps i FM Fns FMot
    (** The container's elimination denotes the group's results *)
  ; set_elim_view_setting_right : set_denotes T γ Γ
      (a_elim r qc (im_pre Mm (List.firstn (ind_nu D) Ps)) k'
         (view_wrap r p qc D D' vm (List.firstn (ind_nu D) Ps) (im_pre Mm (List.firstn (ind_nu D) Ps)) Bks) M)
      (fun ρ => end_value T γ Γ ρ r p (List.firstn (ind_nu D) Ps) Bks (large_results T i) m (FM ρ)) }.

(** The setting of the eliminator at a view, from its premises: at every
    environment, the group's result at the scrutinee's value is the
    container's ([view_agree_of_carrier]). *)
Lemma set_elim_view_setting_of_premises : forall Γ r p Us m Bks M D Mm bm Ps i qc k' Is vm D' C,
    set_ctx T γ Γ ->
    ind_lookup Θs Ξs p = Some D ->
    ind_member D m = Some Mm ->
    im_head Mm = mh_view qc k' Is vm ->
    ind_lookup Θs Ξs qc = Some D' ->
    List.nth_error Bks m = Some bm ->
    List.length Bks = ind_nblk D ->
    List.length Ps = im_np D Mm ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) sb_id Ps) k = Some A ->
       gc_deps ⍮ gc_stack ⍮ Γ ⊢ P : A) ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) sb_id Ps) k = Some A ->
       set_rel_exp_eq T γ Γ A P P) ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    set_rel_exp_eq T γ Γ (ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps)) M M ->
    Us = List.firstn (ind_nu D) Ps ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ ce_ass ak_relevant (eb_scrutinee_type b) :: tele_sub (im_nparams Mk) (sb_of_list sb_id (List.firstn (ind_nu D) Ps))
                    ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       gc_deps ⍮ gc_stack ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : abs_kind_sort r (a_typ i)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       set_rel_exp_eq T γ (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ) (abs_kind_sort r (a_typ i)) (eb_motive b) (eb_motive b)) ->
    (forall k Mk, ind_member D k = Some Mk ->
       gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk, ind_member D k = Some Mk -> set_ctx T γ (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                    ≈ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       set_ctx T γ (elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ)) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       gc_deps ⍮ gc_stack ⍮ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
         : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       set_rel_exp_eq T γ (elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ)
         (elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) B B) ->
    motive_kind r ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_elim r qc (im_pre Mm (List.firstn (ind_nu D) Ps)) k'
        (view_wrap r p qc D D' vm (List.firstn (ind_nu D) Ps) (im_pre Mm (List.firstn (ind_nu D) Ps)) Bks) M : C ->
    exists FM Fns FMot, set_elim_view_setting Γ r p m Bks M D Mm bm Ps i qc k' vm D' FM Fns FMot.
Proof.
  intros Γ r p Us m Bks M D Mm bm Ps i qc k' Is vm D' C HΓ HDsrc Hm Hh HD'src Hbm HlB HPl HPs HPsem HMt HMsem HUs Hcnt Hsc HMty
    HMotsem HMx HMxsem Hbrs HBx HBxsem Hn HBty HBsem Hmk HR.
  pose proof (ind_lookup_gc_sub _ _ _ _ _ _ (set_source_sub T γ Θs Ξs Hemb) HDsrc) as HD.
  pose proof (ind_lookup_gc_sub _ _ _ _ _ _ (set_source_sub T γ Θs Ξs Hemb) HD'src) as HD'.
  (* the left side, by the eliminator's rule *)
  destruct (set_elim_setting_of_premises T γ Hfn Hmods Hgw Θs Ξs Hemb Γ r p Us m Bks M D Mm bm Ps i HΓ HDsrc Hm Hbm HlB HPl HPs HPsem
              HMt HMsem HUs Hcnt Hsc HMty HMotsem HMx HMxsem Hbrs HBx HBxsem Hn HBty HBsem Hmk) as (FMs & Fns & FMot & Hset).
  pose proof Hset as [_ _ HFMs _ _ _ _ _ _ _ _].
  subst Us. set (Us := List.firstn (ind_nu D) Ps) in *.
  pose proof (presup_exp_ctx HMt) as HcΓ.
  destruct (decl_of_lookup _ _ _ _ _ HcΓ HD) as [HDt Hcl].
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.firstn_length_le; [reflexivity |]; rewrite HPl; unfold im_np; lia).
  destruct (params_typed_split _ _ D Hcl _ _ Γ Ps Hm HPl HPs) as [HUt _].
  assert (Hrv : im_is_rview Mm = false) by (unfold im_is_rview; rewrite Hh; reflexivity).
  (* the scrutinee and the induction's setting *)
  destruct HMsem as (FA0 & FM & FM' & HMw).
  destruct (elim_scrutinee_setting T γ Hfn Hmods Hgw Θs Ξs Hemb Γ p D m Mm Ps M FA0 FM FM' HΓ HcΓ HDsrc Hm Hrv HPl HPs HPsem HMw) as (Fι & [HFι Hσ HNr Hpts]).
  set (Fσ := fun ρ => set_env_drop (im_nn Mm) (Fι ρ)) in *.
  set (V := large_results T i).
  pose proof (elim_setting_of_rule T γ Hfn Hmods Hgw Θs Ξs Hemb Γ r p Us Bks D i Fσ HΓ HcΓ HDsrc Hσ HUl HUt HlB Hcnt Hsc HMty HMotsem HMx HMxsem Hbrs HBx HBxsem
              Hn HBty HBsem Hmk) as HS1. fold V in HS1.
  assert (EIs : im_pre Mm Us = List.map (fun I => exp_sub I (sb_of_list sb_id Us)) Is) by (unfold im_pre; rewrite Hh; reflexivity).
  rewrite EIs in HR.
  destruct (decl_typed_view _ _ _ HDt _ _ _ _ _ _ Hm Hh) as (D0 & Mk' & Hl0 & Hk' & _ & _ & _ & Hvk & _).
  rewrite HD' in Hl0. injection Hl0 as <-.
  pose proof HS1 as [_ _ _ _ _ _ _ HMwf HMot HMctx HMh HBk Hbτ Hbctx _ HBr HV HBt HUs0 Hcars].
  pose proof HMw as [_ HFM _ _ _].
  (* at every environment, the container's elimination reads the group's result at the scrutinee *)
  exists FMs, Fns, FMot. constructor; [exact Hset |]. fold Us. rewrite EIs.
  apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ. unfold end_value. fold V.
  destruct Hmk as [| ]; [| apply set_interp_elim_prop].
  destruct (Hcars ρ Hρ) as [U Hcar].
  destruct (Hpts ρ Hρ) as (θc & [Hθc Huni Ens Hmem0]).
  pose proof (set_mem_eq_l _ _ _ (set_denotes_agree T γ _ _ _ _ _ HFM HFMs Hρ) Hmem0) as Hmem.
  assert (Hw : set_mem (FMs ρ) (member_carrier (global_group γ p) (elim_uniform_values ρ D Fσ) U U m (set_env_values (im_nparams Mm) θc)))
    by (eapply set_mem_eq_r; [exact (Hcar m Mm θc Hm Hθc Huni) | exact Hmem]).
  pose proof (set_denotes_exists _ _ _ _ _ HFMs _ Hρ) as HMv.
  pose proof (view_agree_of_carrier Γ ρ _ p Us Bks V D i Fσ U HS1 Hρ Hcar m Mm qc k' Is vm D' Hm Hh HD' m _ (FMs ρ) Hw
                Mm θc Hm Hθc Huni (list_set_eq_refl _)) as HXV.
  eapply set_interp_elim; [discriminate | exact HR | exact HMv |].
  exact (view_agree_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HXV ltac:(discriminate) Hrv k' Mk' Hk' Hvk (FMs ρ) (set_eq_refl _)).
Qed.

End ElimViewSteps.

(** The eliminator at a view, of which the parameters, the scrutinee, the
    motives and the branches hold in the model, is in the model the
    container's eliminator at the view's blocks wrapped. *)
Lemma set_rule_elim_view : forall Γ r p Us m Bks M D Mm bm Ps i qc k' Is vm D' C,
    set_ctx_slots Θr Ξr T γ Γ ->
    ind_lookup Θr Ξr p = Some D ->
    ind_member D m = Some Mm ->
    im_head Mm = mh_view qc k' Is vm ->
    ind_lookup Θr Ξr qc = Some D' ->
    List.nth_error Bks m = Some bm ->
    List.length Bks = ind_nblk D ->
    List.length Ps = im_np D Mm ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) sb_id Ps) k = Some A ->
       Θr ⍮ Ξr ⍮ Γ ⊢ P : A) ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) sb_id Ps) k = Some A ->
       set_exp_eq Θr Ξr T γ Γ A P P) ->
    Θr ⍮ Ξr ⍮ Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    set_exp_eq Θr Ξr T γ Γ (ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps)) M M ->
    Us = List.firstn (ind_nu D) Ps ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       Θr ⍮ Ξr ⍮ Γ ⊢ˣ ce_ass ak_relevant (eb_scrutinee_type b) :: tele_sub (im_nparams Mk) (sb_of_list sb_id (List.firstn (ind_nu D) Ps))
                    ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       Θr ⍮ Ξr ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : abs_kind_sort r (a_typ i)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       set_exp_eq Θr Ξr T γ (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ) (abs_kind_sort r (a_typ i)) (eb_motive b) (eb_motive b)) ->
    (forall k Mk, ind_member D k = Some Mk ->
       Θr ⍮ Ξr ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk, ind_member D k = Some Mk ->
       set_ext_eq_suffixes Θr Ξr T γ Γ (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps))) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       Θr ⍮ Ξr ⍮ Γ ⊢ˣ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                    ≈ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       set_ext_eq_suffixes Θr Ξr T γ Γ (elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps))
         (elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps))) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       Θr ⍮ Ξr ⍮ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
         : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       set_exp_eq Θr Ξr T γ (elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ)
         (elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) B B) ->
    motive_kind r ->
    Θr ⍮ Ξr ⍮ Γ ⊢ a_elim r qc (im_pre Mm (List.firstn (ind_nu D) Ps)) k'
        (view_wrap r p qc D D' vm (List.firstn (ind_nu D) Ps) (im_pre Mm (List.firstn (ind_nu D) Ps)) Bks) M : C ->
    set_exp_eq Θr Ξr T γ Γ (exp_sub (eb_motive bm) (sb_of_list sb_id (List.skipn (ind_nu D) Ps ++ M :: nil)))
      (a_elim r p Us m Bks M)
      (a_elim r qc (im_pre Mm (List.firstn (ind_nu D) Ps)) k'
         (view_wrap r p qc D D' vm (List.firstn (ind_nu D) Ps) (im_pre Mm (List.firstn (ind_nu D) Ps)) Bks) M).
Proof.
  intros Γ r p Us m Bks M D Mm bm Ps i qc k' Is vm D' C HΓ HDsrc Hm Hh HD'src Hbm HlB HPl HPs0 HPsem0 HMt HMsem HUs Hcnt Hsc0
    HMty0 HMotsem0 HMx0 HMxsem0 Hbrs HBx0 HBxsem0 Hn HBty0 HBsem0 Hmk HR.
  set_open. destruct HΓ as [HΓ _]. subst Us.
  destruct (gctx_embedding_preserves_wf _ _ _ _ Hμe) as (_ & Mx & _ & _ & Me & _).
  pose proof (fun k P A H1 H2 => Mx _ _ _ (HPs0 k P A H1 H2)) as HPs.
  pose proof (fun k P A H1 H2 => HPsem0 k P A H1 H2 _ _ Hμ) as HPsem.
  pose proof (fun k Mk b H1 H2 => Me _ _ _ (Hsc0 k Mk b H1 H2)) as Hsc.
  pose proof (fun k Mk b H1 H2 => Mx _ _ _ (HMty0 k Mk b H1 H2)) as HMty.
  pose proof (fun k Mk b H1 H2 => HMotsem0 k Mk b H1 H2 _ _ Hμ) as HMotsem.
  pose proof (fun k Mk H1 => Me _ _ _ (HMx0 k Mk H1)) as HMx.
  pose proof (fun k Mk H1 => set_ext_eq_left T γ _ _ _
                (set_ext_eq_suffixes_eq T γ _ _ _ (HMxsem0 k Mk H1 _ _ Hμ) nil _ nil _ eq_refl eq_refl eq_refl)) as HMxsem.
  pose proof (fun k Mk c gs H1 H2 => Me _ _ _ (HBx0 k Mk c gs H1 H2)) as HBx.
  pose proof (fun k Mk c gs H1 H2 => set_ext_eq_left T γ _ _ _
                (set_ext_eq_suffixes_eq T γ _ _ _ (HBxsem0 k Mk c gs H1 H2 _ _ Hμ) nil _ nil _ eq_refl eq_refl eq_refl)) as HBxsem.
  pose proof (fun k Mk b c gs n B H1 H2 H3 H4 => Mx _ _ _ (HBty0 k Mk b c gs n B H1 H2 H3 H4)) as HBty.
  pose proof (fun k Mk b c gs n B H1 H2 H3 H4 => HBsem0 k Mk b c gs n B H1 H2 H3 H4 _ _ Hμ) as HBsem.
  cbv beta in HPs, HPsem, Hsc, HMty, HMotsem, HMx, HMxsem, HBx, HBxsem, HBty, HBsem.
  assert (Hex : exists FM Fns FMot, set_elim_view_setting Γ r p m Bks M D Mm bm Ps i qc k' vm D' FM Fns FMot)
    by (eapply set_elim_view_setting_of_premises; first [eassumption | reflexivity]).
  destruct Hex as (FM & Fns & FMot & [Hset HFR]).
  exists (fun ρ => FMot (elim_motive_env p D m Mm (List.firstn (ind_nu D) Ps) Fns FM ρ)),
    (fun ρ => end_value T γ Γ ρ r p (List.firstn (ind_nu D) Ps) Bks (large_results T i) m (FM ρ)),
    (fun ρ => end_value T γ Γ ρ r p (List.firstn (ind_nu D) Ps) Bks (large_results T i) m (FM ρ)).
  constructor; [eapply set_elim_motive_denotes; eassumption | eapply set_elim_denotes; eassumption | exact HFR
               | intros; apply set_eq_refl | exact (set_elim_setting_value T γ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hset)].
Qed.

End ElimView.
