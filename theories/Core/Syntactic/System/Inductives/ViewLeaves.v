(** * The Recursive Results of a Wrapped Branch's Instance

    The eliminator at a view is the container's at the view's blocks
    wrapped ([view_wrap]): a wrapped branch reads, at each argument of a
    view's constructor, the container's recursive results at the leaf
    paths the container has ([leaf_in]) and the group's at the others.
    Here are those lists of results, over any type of values
    ([merge_leaves], [merge_ihs]), the group's results at the paths the
    container has ([sel_leaves_vals], [sel_ihs]), and the counts they rest
    on, for the models of the eliminator at a view. *)

From Stdlib Require Import Lia List PeanoNat.
From Stdlib Require String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System.Inductives Require Import Views.
#[local] Open Scope list_scope.

(** ** The Kinds of Two Constructors' Arguments *)

(** The kinds of a constructor's arguments in the group read ([gs']) and
    in the group of the eliminator ([gs]): non-recursive in both,
    recursive in both, or nested through (non-recursive in the group read
    only). *)
Fixpoint cargs_same_kinds (gs' gs : list carg) : Prop :=
  match gs', gs with
  | nil, nil => True
  | ca_arg _ _ :: gs1', ca_arg _ _ :: gs1 => cargs_same_kinds gs1' gs1
  | ca_rec _ :: gs1', ca_rec _ :: gs1 => cargs_same_kinds gs1' gs1
  | ca_arg _ _ :: gs1', ca_rec _ :: gs1 => cargs_same_kinds gs1' gs1
  | _, _ => False
  end.

(** Arguments have the kinds of themselves. *)
Lemma cargs_same_kinds_refl : forall gs, cargs_same_kinds gs gs.
Proof. induction gs as [| [rA A | t] gs IH]; cbn; auto. Qed.

(** The container's arguments have the kinds of the view's they
    correspond to. *)
Lemma cargs_same_kinds_of_correspond : forall vm gs' gs, cargs_correspond vm gs' gs -> cargs_same_kinds gs' gs.
Proof.
  induction gs' as [| [rA' A' | t'] gs' IH]; intros [| [rA A | t] gs] H; cbn in H |- *; try contradiction;
    [ exact I | exact (IH _ (proj2 H)) | exact (IH _ (proj2 H)) | exact (IH _ (proj2 (proj2 H))) ].
Qed.

(** Which leaf paths of an argument's shape are the container's does not
    depend on the binders the shape's components are over. *)
Lemma leaves_in_count_shift : forall D D' t' t m,
    leaves_in_count D' t' (shape_leaves (rview_leaves D) m t) = leaves_in_count D' t' (shape_leaves (rview_leaves D) 0 t).
Proof. intros; apply leaves_in_count_ext, leaf_in_shape_leaves. Qed.

(** The leaf paths of record views' fields: one per path of each
    recursive field's shape. *)
Lemma length_fields_leaves : forall D fs ns, List.length (fields_leaves (rview_leaves D) ns fs) = cargs_nrec D (List.map snd fs).
Proof.
  intros D; induction fs as [| [f [A | t]] fs IH]; intros ns; cbn [fields_leaves List.map snd cargs_nrec]; [ reflexivity | apply IH |].
  rewrite List.length_app, List.length_map, IH, (length_shape_leaves _ _ _ 0); reflexivity.
Qed.

(** Dropping one more is dropping the rest of the tail. *)
Lemma skipn_S_tl : forall {A : Type} n (l : list A), List.skipn (S n) l = List.skipn n (List.tl l).
Proof. intros A n [| x l]; cbn; [ destruct n; reflexivity | reflexivity ]. Qed.

Section ViewLeaves.
  (** The type of the results, and the result read where the
      container's results run out *)
  Context {A : Type} (d : A).

(** ** Merged Results

    Along the group's leaf paths [ls] of an argument whose shape the
    container has as [t']: the container's next result of [rsC] at a path
    the container has, the group's of [rsG] at the others
    ([wrap_leaves]); and so over a constructor's arguments, [gs'] as the
    container has them, [gs] as the group does ([wrap_ihs]). *)
Fixpoint merge_leaves (D' : ind_decl) (t' : ptyp) (ls : list leaf_path) (rsG rsC : list A) : list A :=
  match ls, rsG with
  | l :: ls', g :: rsG' =>
      if leaf_in D' t' l then List.hd d rsC :: merge_leaves D' t' ls' rsG' (List.tl rsC)
      else g :: merge_leaves D' t' ls' rsG' rsC
  | _, _ => nil
  end.

(** The recursive results of a constructor's arguments, [gs'] as the
    container has them and [gs] as the group does: at an argument
    recursive on both sides, [merge_leaves] of the group's results [ihsG]
    and the container's [w]; at one recursive in the group only, the
    group's results. *)
Fixpoint merge_ihs (D' D : ind_decl) (gs' gs : list carg) (ihsG w : list A) : list A :=
  match gs', gs with
  | ca_rec t' :: gs1', ca_rec t :: gs1 =>
      let ls := shape_leaves (rview_leaves D) 0 t in
      merge_leaves D' t' ls (List.firstn (List.length ls) ihsG) w ++
        merge_ihs D' D gs1' gs1 (List.skipn (List.length ls) ihsG) (List.skipn (leaves_in_count D' t' ls) w)
  | ca_arg _ _ :: gs1', ca_rec t :: gs1 =>
      let n := List.length (shape_leaves (rview_leaves D) 0 t) in
      List.firstn n ihsG ++ merge_ihs D' D gs1' gs1 (List.skipn n ihsG) w
  | _ :: gs1', ca_arg _ _ :: gs1 => merge_ihs D' D gs1' gs1 ihsG w
  | _, _ => nil
  end.

(** The merge depends on the paths only through which are the
    container's. *)
Lemma merge_leaves_ext : forall D' t' ls1 ls2 rsG rsC, List.map (leaf_in D' t') ls1 = List.map (leaf_in D' t') ls2 ->
    merge_leaves D' t' ls1 rsG rsC = merge_leaves D' t' ls2 rsG rsC.
Proof.
  intros D' t'; induction ls1 as [| l1 ls1 IH]; intros [| l2 ls2] rsG rsC H; cbn in H; try discriminate; [ reflexivity |].
  injection H as Hl Hls; destruct rsG as [| g rsG]; cbn [merge_leaves]; [ reflexivity |].
  rewrite Hl; destruct (leaf_in D' t' l2); rewrite (IH _ _ _ Hls); reflexivity.
Qed.

(** Paths under a domain merge as the rest. *)
Lemma merge_leaves_map_pi : forall D' B B' t' ls rsG rsC,
    merge_leaves D' (pt_pi B' t') (List.map (leaf_pi B) ls) rsG rsC = merge_leaves D' t' ls rsG rsC.
Proof.
  intros D' B B' t'; induction ls as [| l ls IH]; intros [| g rsG] rsC; cbn [List.map merge_leaves leaf_in]; try reflexivity.
  destruct (leaf_in D' t' l); rewrite IH; reflexivity.
Qed.

(** Moved paths merge alike. *)
Lemma merge_leaves_map_wk : forall D' t' φ ls rsG rsC,
    merge_leaves D' t' (List.map (leaf_wk φ) ls) rsG rsC = merge_leaves D' t' ls rsG rsC.
Proof.
  intros D' t' φ; induction ls as [| l ls IH]; intros [| g rsG] rsC; cbn [List.map merge_leaves]; try reflexivity.
  rewrite leaf_in_wk; destruct (leaf_in D' t' l); rewrite IH; reflexivity.
Qed.

(** One merged result per path. *)
Lemma length_merge_leaves : forall D' t' ls rsG rsC, List.length rsG = List.length ls ->
    List.length (merge_leaves D' t' ls rsG rsC) = List.length ls.
Proof.
  intros D' t'; induction ls as [| l ls IH]; intros [| g rsG] rsC H; cbn in H |- *; try lia.
  destruct (leaf_in D' t' l); cbn; rewrite IH by lia; reflexivity.
Qed.

(** The merge along two runs of paths. *)
Lemma merge_leaves_app : forall D' t' ls1 ls2 rsG rsC, List.length rsG = List.length ls1 + List.length ls2 ->
    merge_leaves D' t' (ls1 ++ ls2) rsG rsC
    = merge_leaves D' t' ls1 (List.firstn (List.length ls1) rsG) rsC ++
      merge_leaves D' t' ls2 (List.skipn (List.length ls1) rsG) (List.skipn (leaves_in_count D' t' ls1) rsC).
Proof.
  intros D' t'; induction ls1 as [| l ls1 IH]; intros ls2 rsG rsC Hl.
  - unfold leaves_in_count; cbn; reflexivity.
  - destruct rsG as [| g rsG]; cbn [List.length] in Hl; [ lia |].
    cbn [List.app List.length List.firstn List.skipn merge_leaves].
    unfold leaves_in_count; cbn [List.filter]; destruct (leaf_in D' t' l); cbn [List.length List.app].
    + rewrite IH by lia; rewrite skipn_S_tl; reflexivity.
    + rewrite IH by lia; reflexivity.
Qed.

(** No path the container's: the group's results. *)
Lemma merge_leaves_none : forall D' t' ls rsG rsC, (forall l, In l ls -> leaf_in D' t' l = false) ->
    List.length rsG = List.length ls -> merge_leaves D' t' ls rsG rsC = rsG.
Proof.
  intros D' t'; induction ls as [| l ls IH]; intros [| g rsG] rsC Hn Hl; cbn in Hl |- *; try lia; [ reflexivity |].
  rewrite (Hn l (or_introl eq_refl)), IH; [ reflexivity | intros; apply Hn; right; assumption | lia ].
Qed.

(** Results related pointwise on both sides merge to results related
    pointwise. *)
Lemma merge_leaves_Forall2 : forall (P : A -> A -> Prop) D' t' ls rsG rsC rsG' rsC',
    List.Forall2 P rsG rsG' -> List.Forall2 P rsC rsC' ->
    List.length rsG = List.length ls -> List.length rsC = leaves_in_count D' t' ls ->
    List.Forall2 P (merge_leaves D' t' ls rsG rsC) (merge_leaves D' t' ls rsG' rsC').
Proof.
  intros P D' t'; induction ls as [| l ls IH]; intros rsG rsC rsG' rsC' HG HC Lg Lc; [ cbn; constructor |].
  destruct HG as [| g g' rsG rsG' Hg HG]; cbn in Lg; [ lia |].
  unfold leaves_in_count in Lc; cbn [List.filter] in Lc; cbn [merge_leaves].
  destruct (leaf_in D' t' l).
  - destruct HC as [| c c' rsC rsC' Hc HC]; cbn in Lc; [ lia |].
    cbn [List.hd List.tl]; constructor; [ exact Hc | apply IH; [ exact HG | exact HC | lia | unfold leaves_in_count; lia ] ].
  - constructor; [ exact Hg | apply IH; [ exact HG | exact HC | lia | exact Lc ] ].
Qed.

(** A property of every result on both sides holds of every merged
    result. *)
Lemma merge_leaves_Forall : forall (P : A -> Prop) D' t' ls rsG rsC,
    List.Forall P rsG -> List.Forall P rsC -> List.length rsC = leaves_in_count D' t' ls ->
    List.Forall P (merge_leaves D' t' ls rsG rsC).
Proof.
  intros P D' t'; induction ls as [| l ls IH]; intros rsG rsC HG HC Lc; [ cbn; constructor |].
  destruct HG as [| g rsG Hg HG]; [ cbn; constructor |].
  unfold leaves_in_count in Lc; cbn [List.filter] in Lc; cbn [merge_leaves].
  destruct (leaf_in D' t' l).
  - destruct HC as [| c rsC Hc HC]; cbn in Lc; [ lia |].
    cbn [List.hd List.tl]; constructor; [ exact Hc | apply IH; [ exact HG | exact HC | unfold leaves_in_count; lia ] ].
  - constructor; [ exact Hg | apply IH; [ exact HG | exact HC | exact Lc ] ].
Qed.

(** Paths mapped into the container's alike merge alike. *)
Lemma merge_leaves_map_in : forall D' t1 t2 (F : leaf_path -> leaf_path) ls rsG rsC,
    (forall l, leaf_in D' t1 (F l) = leaf_in D' t2 l) ->
    merge_leaves D' t1 (List.map F ls) rsG rsC = merge_leaves D' t2 ls rsG rsC.
Proof.
  intros D' t1 t2 F; induction ls as [| l ls IH]; intros [| g rsG] rsC H; cbn [List.map merge_leaves]; try reflexivity.
  rewrite H; destruct (leaf_in D' t2 l); rewrite IH by exact H; reflexivity.
Qed.

(** So are they counted. *)
Lemma leaves_in_count_map_in : forall D' t1 t2 (F : leaf_path -> leaf_path) ls,
    (forall l, leaf_in D' t1 (F l) = leaf_in D' t2 l) -> leaves_in_count D' t1 (List.map F ls) = leaves_in_count D' t2 ls.
Proof.
  intros D' t1 t2 F; induction ls as [| l ls IH]; intros H; [ reflexivity |].
  unfold leaves_in_count in *; cbn [List.map List.filter]; rewrite H; destruct (leaf_in D' t2 l); cbn; rewrite IH by exact H; reflexivity.
Qed.

(** Paths mapped out of the container's merge to the group's results. *)
Lemma merge_leaves_map_out : forall D' t1 (F : leaf_path -> leaf_path) ls rsG rsC,
    (forall l, leaf_in D' t1 (F l) = false) -> List.length rsG = List.length ls -> merge_leaves D' t1 (List.map F ls) rsG rsC = rsG.
Proof.
  intros * H L; apply merge_leaves_none; [| rewrite List.length_map; exact L ].
  intros l Hl; apply List.in_map_iff in Hl as (l0 & <- & _); apply H.
Qed.

(** And none is counted. *)
Lemma leaves_in_count_map_out : forall D' t1 (F : leaf_path -> leaf_path) ls,
    (forall l, leaf_in D' t1 (F l) = false) -> leaves_in_count D' t1 (List.map F ls) = 0.
Proof.
  intros D' t1 F; induction ls as [| l ls IH]; intros H; [ reflexivity |].
  unfold leaves_in_count in *; cbn [List.map List.filter]; rewrite H; exact (IH H).
Qed.

(** The container's results consumed: what follows does not matter. *)
Lemma merge_leaves_app_tail : forall D' t' ls rsG rsC rsE, List.length rsC = leaves_in_count D' t' ls ->
    merge_leaves D' t' ls rsG (rsC ++ rsE) = merge_leaves D' t' ls rsG rsC.
Proof.
  intros D' t'; induction ls as [| l ls IH]; intros [| g rsG] rsC rsE Lc; cbn [merge_leaves]; try reflexivity.
  unfold leaves_in_count in Lc; cbn [List.filter] in Lc.
  destruct (leaf_in D' t' l).
  - destruct rsC as [| c rsC]; cbn in Lc |- *; [ lia |]; rewrite IH by (unfold leaves_in_count; lia); reflexivity.
  - rewrite IH by exact Lc; reflexivity.
Qed.

(** At a record view of the container, of the fields [fl]: the merge
    along the group's paths through the fields is the merge over the
    fields' kinds on both sides. *)
Lemma merge_leaves_fields : forall D D' j' Mj' qr Is' fl c' gsr' Ps' gsr,
    ind_member D' j' = Some Mj' -> im_head Mj' = mh_record qr Is' fl -> im_cons Mj' = (c', gsr') :: nil ->
    List.NoDup fl -> List.length fl = List.length gsr' -> List.length fl = List.length gsr ->
    forall ihsG rsC, List.length ihsG = cargs_nrec D gsr ->
    merge_leaves D' (pt_self j' Ps') (fields_leaves (rview_leaves D) nil (List.combine fl gsr)) ihsG rsC = merge_ihs D' D gsr' gsr ihsG rsC.
Proof.
  intros * HMj' Hh' Hcs' Hnd Hlen' Hlen.
  assert (Hfs : forall fs2 fs2' fs1 fs1' ns, List.combine fl gsr = fs1 ++ fs2 -> List.combine fl gsr' = fs1' ++ fs2' ->
             List.length fs1 = List.length fs1' -> forall ihsG rsC, List.length ihsG = cargs_nrec D (List.map snd fs2) ->
             merge_leaves D' (pt_self j' Ps') (fields_leaves (rview_leaves D) ns fs2) ihsG rsC
             = merge_ihs D' D (List.map snd fs2') (List.map snd fs2) ihsG rsC).
  { induction fs2 as [| [f g] fs2 IHf]; intros fs2' fs1 fs1' ns E E' Lf ihsG rsC Lg.
    - cbn [fields_leaves merge_leaves]; destruct (List.map snd fs2') as [| [] ?]; destruct ihsG; reflexivity.
    - destruct fs2' as [| [f' g'] fs2'].
      { exfalso.
        assert (L1 : List.length (List.combine fl gsr) = List.length fl) by (rewrite List.length_combine; lia).
        assert (L2 : List.length (List.combine fl gsr') = List.length fl) by (rewrite List.length_combine; lia).
        rewrite E in L1; rewrite E' in L2; rewrite !List.length_app in L1, L2; cbn in L1, L2; lia. }
      destruct (combine_app_split _ _ _ _ Hlen E) as [Efl Egs].
      destruct (combine_app_split _ _ _ _ Hlen' E') as [Efl' Egs'].
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
      { rewrite E'; apply find_name_split; rewrite <- E', combine_fst_eq by exact Hlen'; exact Hnd. }
      destruct g as [A0 | t].
      + cbn [fields_leaves List.map snd]; cbn [List.map snd cargs_nrec] in Lg.
        rewrite (IHf _ _ _ _ E1 E1' L1 _ _ Lg); destruct g'; reflexivity.
      + cbn [fields_leaves List.map snd]; cbn [List.map snd cargs_nrec] in Lg.
        assert (Lls : List.length (shape_leaves (rview_leaves D) (List.length ns) t) = List.length (shape_leaves (rview_leaves D) 0 t))
          by apply length_shape_leaves.
        rewrite merge_leaves_app by (rewrite List.length_map, length_fields_leaves; lia).
        rewrite List.length_map, Lls.
        assert (Lsk : List.length (List.skipn (List.length (shape_leaves (rview_leaves D) 0 t)) ihsG) = cargs_nrec D (List.map snd fs2))
          by (rewrite List.length_skipn; lia).
        destruct g' as [A' | t'].
        * (** The container takes the field as non-recursive. *)
          assert (Hout : forall l, leaf_in D' (pt_self j' Ps') (leaf_proj f ns l) = false)
            by (intros l; cbn [leaf_in]; rewrite HMj', Hh', Hcs', Hfind; reflexivity).
          rewrite (merge_leaves_map_out _ _ _ _ _ _ Hout) by (rewrite List.length_firstn, Lls; lia).
          rewrite (leaves_in_count_map_out _ _ _ _ Hout); cbn [List.skipn].
          cbn [List.map snd merge_ihs].
          rewrite (IHf _ _ _ _ E1 E1' L1 _ _ Lsk); reflexivity.
        * (** Recursive in both: the container's paths are those through
              its field's shape. *)
          assert (Hin : forall l, leaf_in D' (pt_self j' Ps') (leaf_proj f ns l) = leaf_in D' t' l)
            by (intros l; cbn [leaf_in]; rewrite HMj', Hh', Hcs', Hfind; reflexivity).
          rewrite (merge_leaves_map_in _ _ _ _ _ _ _ Hin), (leaves_in_count_map_in _ _ _ _ _ Hin).
          rewrite (merge_leaves_ext _ _ _ (shape_leaves (rview_leaves D) 0 t) _ _ (leaf_in_shape_leaves _ _ _ _ _ _)).
          rewrite (leaves_in_count_shift D D' t' t).
          cbn [List.map snd merge_ihs].
          rewrite (IHf _ _ _ _ E1 E1' L1 _ _ Lsk); reflexivity. }
  intros ihsG rsC Lg.
  pose proof (Hfs (List.combine fl gsr) (List.combine fl gsr') nil nil nil eq_refl eq_refl eq_refl ihsG rsC
                ltac:(rewrite combine_snd_eq by exact Hlen; exact Lg)) as H.
  rewrite !combine_snd_eq in H by assumption; exact H.
Qed.

(** At a path the container has: the container's next result. *)
Lemma merge_leaves_nth_in : forall D' t' ls rsG rsC n l, List.nth_error ls n = Some l -> leaf_in D' t' l = true ->
    List.length rsG = List.length ls ->
    List.nth n (merge_leaves D' t' ls rsG rsC) d = List.nth (leaves_in_count D' t' (List.firstn n ls)) rsC d.
Proof.
  intros D' t'; induction ls as [| l0 ls IH]; intros [| g rsG] rsC [| n] l Hn Hin Lg; cbn in Hn, Lg; try discriminate; try lia.
  - injection Hn as <-; cbn [merge_leaves]; rewrite Hin; unfold leaves_in_count; cbn.
    destruct rsC; reflexivity.
  - cbn [merge_leaves List.firstn]; unfold leaves_in_count; cbn [List.filter].
    destruct (leaf_in D' t' l0); cbn [List.nth List.length].
    + rewrite (IH rsG (List.tl rsC) n l Hn Hin ltac:(lia)); unfold leaves_in_count.
      generalize (List.length (List.filter (leaf_in D' t') (List.firstn n ls))) as k0; intros k0; destruct rsC; [ destruct k0 |];
        reflexivity.
    + exact (IH rsG rsC n l Hn Hin ltac:(lia)).
Qed.

(** ** The Group's Results at the Container's Paths *)

(** The group's results at the paths the container has. *)
Fixpoint sel_leaves_vals (D' : ind_decl) (t' : ptyp) (ls : list leaf_path) (rs : list A) : list A :=
  match ls, rs with
  | l :: ls', r :: rs' => if leaf_in D' t' l then r :: sel_leaves_vals D' t' ls' rs' else sel_leaves_vals D' t' ls' rs'
  | _, _ => nil
  end.

(** The group's recursive results [ihs] of a constructor's arguments at the
    paths the container has: [sel_leaves_vals] at an argument recursive on
    both sides, none at one recursive in the group only. *)
Fixpoint sel_ihs (D' D : ind_decl) (gs' gs : list carg) (ihs : list A) : list A :=
  match gs', gs with
  | ca_rec t' :: gs1', ca_rec t :: gs1 =>
      let ls := shape_leaves (rview_leaves D) 0 t in
      sel_leaves_vals D' t' ls (List.firstn (List.length ls) ihs) ++ sel_ihs D' D gs1' gs1 (List.skipn (List.length ls) ihs)
  | ca_arg _ _ :: gs1', ca_rec t :: gs1 => sel_ihs D' D gs1' gs1 (List.skipn (List.length (shape_leaves (rview_leaves D) 0 t)) ihs)
  | _ :: gs1', ca_arg _ _ :: gs1 => sel_ihs D' D gs1' gs1 ihs
  | _, _ => nil
  end.

(** The selection depends on the paths only through which are the
    container's. *)
Lemma sel_leaves_vals_ext : forall D' t' ls1 ls2 rs, List.map (leaf_in D' t') ls1 = List.map (leaf_in D' t') ls2 ->
    sel_leaves_vals D' t' ls1 rs = sel_leaves_vals D' t' ls2 rs.
Proof.
  intros D' t'; induction ls1 as [| l1 ls1 IH]; intros [| l2 ls2] rs H; cbn in H; try discriminate; [ reflexivity |].
  injection H as Hl Hls; destruct rs as [| r rs]; cbn [sel_leaves_vals]; [ reflexivity |].
  rewrite Hl, (IH _ _ Hls); reflexivity.
Qed.

(** One more path, one more result if it is the container's. *)
Lemma sel_leaves_vals_snoc : forall D' t' ls l rs r, List.length rs = List.length ls ->
    sel_leaves_vals D' t' (ls ++ l :: nil) (rs ++ r :: nil)
    = sel_leaves_vals D' t' ls rs ++ (if leaf_in D' t' l then r :: nil else nil).
Proof.
  intros D' t'; induction ls as [| l0 ls IH]; intros l [| r0 rs] r Hl; cbn in Hl |- *; try lia.
  - destruct (leaf_in D' t' l); reflexivity.
  - rewrite IH by lia; destruct (leaf_in D' t' l0); reflexivity.
Qed.

(** One selected result per path the container has. *)
Lemma length_sel_leaves_vals : forall D' t' ls rs, List.length rs = List.length ls ->
    List.length (sel_leaves_vals D' t' ls rs) = leaves_in_count D' t' ls.
Proof.
  intros D' t'; induction ls as [| l ls IH]; intros [| r rs] Hl; cbn in Hl |- *; try lia; try reflexivity.
  unfold leaves_in_count in *; cbn [List.filter]; destruct (leaf_in D' t' l); cbn; rewrite IH by lia; reflexivity.
Qed.

(** One merged result per recursive result of the group. *)
Lemma length_merge_ihs : forall D' D gs' gs ihs w, cargs_same_kinds gs' gs -> List.length ihs = cargs_nrec D gs ->
    List.length (merge_ihs D' D gs' gs ihs w) = cargs_nrec D gs.
Proof.
  intros D' D; induction gs' as [| [A' | t'] gs' IH]; intros [| [A0 | t] gs] ihs w Hk Hl; cbn in Hk |- *; try contradiction;
    cbn [cargs_nrec] in Hl; try reflexivity; rewrite ?List.length_app.
  - exact (IH _ _ _ Hk Hl).
  - rewrite List.length_firstn, (IH gs) by (try exact Hk; rewrite List.length_skipn; lia); lia.
  - rewrite length_merge_leaves by (rewrite List.length_firstn; lia);
      rewrite (IH gs) by (try exact Hk; rewrite List.length_skipn; lia); lia.
Qed.

(** The merge over two runs of arguments. *)
Lemma merge_ihs_app : forall D' D G1' G1 G2' G2 ihs w, cargs_same_kinds G1' G1 ->
    merge_ihs D' D (G1' ++ G2') (G1 ++ G2) ihs w
    = merge_ihs D' D G1' G1 (List.firstn (cargs_nrec D G1) ihs) w ++
      merge_ihs D' D G2' G2 (List.skipn (cargs_nrec D G1) ihs) (List.skipn (cargs_container_count D D' G1' G1) w).
Proof.
  intros D' D; induction G1' as [| [A' | t'] G1' IH]; intros [| [A0 | t] G1] G2' G2 ihs w Hk; cbn in Hk; try contradiction;
    cbn [List.app merge_ihs cargs_nrec cargs_container_count].
  - reflexivity.
  - exact (IH _ _ _ _ _ Hk).
  - rewrite IH by exact Hk; rewrite <- List.app_assoc, List.firstn_firstn, Nat.min_l by lia; f_equal; f_equal.
    + rewrite List.skipn_firstn_comm.
      replace (List.length (shape_leaves (rview_leaves D) 0 t) + cargs_nrec D G1 - List.length (shape_leaves (rview_leaves D) 0 t))
        with (cargs_nrec D G1) by lia; reflexivity.
    + rewrite List.skipn_skipn, Nat.add_comm; reflexivity.
  - rewrite IH by exact Hk; rewrite <- List.app_assoc, List.firstn_firstn, Nat.min_l by lia; f_equal; f_equal.
    + rewrite List.skipn_firstn_comm.
      replace (List.length (shape_leaves (rview_leaves D) 0 t) + cargs_nrec D G1 - List.length (shape_leaves (rview_leaves D) 0 t))
        with (cargs_nrec D G1) by lia; reflexivity.
    + rewrite !List.skipn_skipn, (Nat.add_comm (cargs_nrec D G1)), (Nat.add_comm (cargs_container_count D D' G1' G1)); reflexivity.
Qed.

(** The selection over two runs of arguments. *)
Lemma sel_ihs_app : forall D' D G1' G1 G2' G2 ihs, cargs_same_kinds G1' G1 ->
    sel_ihs D' D (G1' ++ G2') (G1 ++ G2) ihs
    = sel_ihs D' D G1' G1 (List.firstn (cargs_nrec D G1) ihs) ++ sel_ihs D' D G2' G2 (List.skipn (cargs_nrec D G1) ihs).
Proof.
  intros D' D; induction G1' as [| [A' | t'] G1' IH]; intros [| [A0 | t] G1] G2' G2 ihs Hk; cbn in Hk; try contradiction;
    cbn [List.app sel_ihs cargs_nrec].
  - reflexivity.
  - exact (IH _ _ _ _ Hk).
  - rewrite IH by exact Hk; f_equal; f_equal.
    + rewrite List.skipn_firstn_comm.
      replace (List.length (shape_leaves (rview_leaves D) 0 t) + cargs_nrec D G1 - List.length (shape_leaves (rview_leaves D) 0 t))
        with (cargs_nrec D G1) by lia; reflexivity.
    + rewrite List.skipn_skipn, Nat.add_comm; reflexivity.
  - rewrite IH by exact Hk; rewrite <- List.app_assoc, List.firstn_firstn, Nat.min_l by lia; f_equal; f_equal.
    + rewrite List.skipn_firstn_comm.
      replace (List.length (shape_leaves (rview_leaves D) 0 t) + cargs_nrec D G1 - List.length (shape_leaves (rview_leaves D) 0 t))
        with (cargs_nrec D G1) by lia; reflexivity.
    + rewrite List.skipn_skipn, Nat.add_comm; reflexivity.
Qed.

(** One selected result per path the container's branch binds. *)
Lemma length_sel_ihs : forall D' D gs' gs ihs, cargs_same_kinds gs' gs -> List.length ihs = cargs_nrec D gs ->
    List.length (sel_ihs D' D gs' gs ihs) = cargs_container_count D D' gs' gs.
Proof.
  intros D' D; induction gs' as [| [A' | t'] gs' IH]; intros [| [A0 | t] gs] ihs Hk Hl; cbn in Hk |- *; try contradiction;
    cbn [cargs_nrec] in Hl; try reflexivity.
  - exact (IH _ _ Hk Hl).
  - apply IH; [ exact Hk | rewrite List.length_skipn; lia ].
  - rewrite List.length_app, length_sel_leaves_vals by (rewrite List.length_firstn; lia).
    rewrite IH by (try exact Hk; rewrite List.length_skipn; lia); reflexivity.
Qed.

(** The results of the paths selected at the container's: the results of
    the container's paths among them. *)
Lemma sel_leaves_vals_map : forall D' t' (F : leaf_path -> A) ls,
    sel_leaves_vals D' t' ls (List.map F ls) = List.map F (List.filter (leaf_in D' t') ls).
Proof.
  intros D' t' F; induction ls as [| l ls IH]; cbn; [ reflexivity |].
  destruct (leaf_in D' t' l); cbn; rewrite IH; reflexivity.
Qed.

(** The selection along two runs of paths. *)
Lemma sel_leaves_vals_app : forall D' t' ls1 ls2 rs, List.length rs = List.length ls1 + List.length ls2 ->
    sel_leaves_vals D' t' (ls1 ++ ls2) rs
    = sel_leaves_vals D' t' ls1 (List.firstn (List.length ls1) rs) ++ sel_leaves_vals D' t' ls2 (List.skipn (List.length ls1) rs).
Proof.
  intros D' t'; induction ls1 as [| l ls1 IH]; intros ls2 rs Hl; [ reflexivity |].
  destruct rs as [| r rs]; cbn in Hl; [ lia |]. cbn [List.app List.length List.firstn List.skipn sel_leaves_vals].
  destruct (leaf_in D' t' l); rewrite IH by lia; reflexivity.
Qed.

(** No path the container's: no result selected. *)
Lemma sel_leaves_vals_none : forall D' t' ls rs, (forall l, In l ls -> leaf_in D' t' l = false) ->
    sel_leaves_vals D' t' ls rs = nil.
Proof.
  intros D' t'; induction ls as [| l ls IH]; intros [| r rs] Hn; cbn; try reflexivity.
  rewrite (Hn l (or_introl eq_refl)); apply IH; intros; apply Hn; right; assumption.
Qed.

(** Paths mapped into the container's alike select alike. *)
Lemma sel_leaves_vals_map_in : forall D' t1 t2 (F : leaf_path -> leaf_path) ls rs,
    (forall l, leaf_in D' t1 (F l) = leaf_in D' t2 l) ->
    sel_leaves_vals D' t1 (List.map F ls) rs = sel_leaves_vals D' t2 ls rs.
Proof.
  intros D' t1 t2 F; induction ls as [| l ls IH]; intros [| r rs] H; cbn [List.map sel_leaves_vals]; try reflexivity.
  rewrite H; destruct (leaf_in D' t2 l); rewrite IH by exact H; reflexivity.
Qed.

(** At a record view of the container, of the fields [fl]: the selection
    along the group's paths through the fields is the selection over the
    fields' kinds on both sides. *)
Lemma sel_leaves_fields : forall D D' j' Mj' qr Is' fl c' gsr' Ps' gsr,
    ind_member D' j' = Some Mj' -> im_head Mj' = mh_record qr Is' fl -> im_cons Mj' = (c', gsr') :: nil ->
    List.NoDup fl -> List.length fl = List.length gsr' -> List.length fl = List.length gsr ->
    forall rs, List.length rs = cargs_nrec D gsr ->
    sel_leaves_vals D' (pt_self j' Ps') (fields_leaves (rview_leaves D) nil (List.combine fl gsr)) rs = sel_ihs D' D gsr' gsr rs.
Proof.
  intros * HMj' Hh' Hcs' Hnd Hlen' Hlen.
  assert (Hfs : forall fs2 fs2' fs1 fs1' ns, List.combine fl gsr = fs1 ++ fs2 -> List.combine fl gsr' = fs1' ++ fs2' ->
             List.length fs1 = List.length fs1' -> forall rs, List.length rs = cargs_nrec D (List.map snd fs2) ->
             sel_leaves_vals D' (pt_self j' Ps') (fields_leaves (rview_leaves D) ns fs2) rs
             = sel_ihs D' D (List.map snd fs2') (List.map snd fs2) rs).
  { induction fs2 as [| [f g] fs2 IHf]; intros fs2' fs1 fs1' ns E E' Lf rs Lg.
    - cbn [fields_leaves sel_leaves_vals]; destruct (List.map snd fs2') as [| [] ?]; destruct rs; reflexivity.
    - destruct fs2' as [| [f' g'] fs2'].
      { exfalso.
        assert (L1 : List.length (List.combine fl gsr) = List.length fl) by (rewrite List.length_combine; lia).
        assert (L2 : List.length (List.combine fl gsr') = List.length fl) by (rewrite List.length_combine; lia).
        rewrite E in L1; rewrite E' in L2; rewrite !List.length_app in L1, L2; cbn in L1, L2; lia. }
      destruct (combine_app_split _ _ _ _ Hlen E) as [Efl Egs].
      destruct (combine_app_split _ _ _ _ Hlen' E') as [Efl' Egs'].
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
      { rewrite E'; apply find_name_split; rewrite <- E', combine_fst_eq by exact Hlen'; exact Hnd. }
      destruct g as [A0 | t].
      + cbn [fields_leaves List.map snd]; cbn [List.map snd cargs_nrec] in Lg.
        rewrite (IHf _ _ _ _ E1 E1' L1 _ Lg); destruct g'; reflexivity.
      + cbn [fields_leaves List.map snd]; cbn [List.map snd cargs_nrec] in Lg.
        assert (Lls : List.length (shape_leaves (rview_leaves D) (List.length ns) t) = List.length (shape_leaves (rview_leaves D) 0 t))
          by apply length_shape_leaves.
        rewrite sel_leaves_vals_app by (rewrite List.length_map, length_fields_leaves; lia).
        rewrite List.length_map, Lls.
        assert (Lsk : List.length (List.skipn (List.length (shape_leaves (rview_leaves D) 0 t)) rs) = cargs_nrec D (List.map snd fs2))
          by (rewrite List.length_skipn; lia).
        destruct g' as [A' | t'].
        * (** The container takes the field as non-recursive. *)
          rewrite sel_leaves_vals_none
            by (intros l Hl; apply List.in_map_iff in Hl as (l0 & <- & _); cbn [leaf_in]; rewrite HMj', Hh', Hcs', Hfind; reflexivity).
          cbn [List.app List.map snd sel_ihs].
          rewrite (IHf _ _ _ _ E1 E1' L1 _ Lsk); reflexivity.
        * (** Recursive in both: the container's paths are those through
              its field's shape. *)
          assert (Hin : forall l, leaf_in D' (pt_self j' Ps') (leaf_proj f ns l) = leaf_in D' t' l)
            by (intros l; cbn [leaf_in]; rewrite HMj', Hh', Hcs', Hfind; reflexivity).
          rewrite (sel_leaves_vals_map_in _ _ _ _ _ _ Hin).
          rewrite (sel_leaves_vals_ext _ _ _ (shape_leaves (rview_leaves D) 0 t) _ (leaf_in_shape_leaves _ _ _ _ _ _)).
          cbn [List.map snd sel_ihs].
          rewrite (IHf _ _ _ _ E1 E1' L1 _ Lsk); reflexivity. }
  intros rs Lg.
  pose proof (Hfs (List.combine fl gsr) (List.combine fl gsr') nil nil nil eq_refl eq_refl eq_refl rs
                ltac:(rewrite combine_snd_eq by exact Hlen; exact Lg)) as H.
  rewrite !combine_snd_eq in H by assumption; exact H.
Qed.

(** The group's results merged with their selection at the container's
    paths are the group's results. *)
Lemma merge_sel_leaves : forall D' t' ls rs, List.length rs = List.length ls ->
    merge_leaves D' t' ls rs (sel_leaves_vals D' t' ls rs) = rs.
Proof.
  intros D' t'; induction ls as [| l ls IH]; intros [| r rs] Hl; cbn in Hl |- *; try lia; [ reflexivity |].
  destruct (leaf_in D' t' l); cbn [List.hd List.tl]; rewrite IH by lia; reflexivity.
Qed.

(** And so over a constructor's arguments. *)
Lemma merge_sel_ihs : forall D' D gs' gs ihs, cargs_same_kinds gs' gs -> List.length ihs = cargs_nrec D gs ->
    merge_ihs D' D gs' gs ihs (sel_ihs D' D gs' gs ihs) = ihs.
Proof.
  intros D' D; induction gs' as [| [A' | t'] gs' IH]; intros [| [A0 | t] gs] ihs Hk Hl; cbn in Hk; try contradiction;
    cbn [merge_ihs sel_ihs cargs_nrec] in Hl |- *.
  - destruct ihs; [ reflexivity | cbn in Hl; lia ].
  - exact (IH _ _ Hk Hl).
  - rewrite IH by (try exact Hk; rewrite List.length_skipn; lia). apply List.firstn_skipn.
  - set (ls := shape_leaves (rview_leaves D) 0 t) in *.
    rewrite merge_leaves_app_tail by (apply length_sel_leaves_vals; rewrite List.length_firstn; lia).
    rewrite merge_sel_leaves by (rewrite List.length_firstn; lia).
    rewrite List.skipn_app, (length_sel_leaves_vals D' t' ls (List.firstn (List.length ls) ihs)) by (rewrite List.length_firstn; lia).
    rewrite (List.skipn_all2 (sel_leaves_vals D' t' ls (List.firstn (List.length ls) ihs)))
      by (rewrite length_sel_leaves_vals by (rewrite List.length_firstn; lia); lia).
    rewrite Nat.sub_diag, List.skipn_O; cbn [List.app].
    rewrite IH by (try exact Hk; rewrite List.length_skipn; lia). apply List.firstn_skipn.
Qed.

End ViewLeaves.

(** ** The Members a View Takes the Container's To *)

(** A member's own uniform parameters: the group's for a declared one, the
    container's for a view.  A record view's pseudo-constructor is the
    group's own, at the group's uniform parameters (its saturated value is
    a tuple, never a [d_con], so this is never read). *)
Definition im_unu (D : ind_decl) (M : imember) : nat :=
  match im_head M with
  | mh_decl _ => ind_nu D
  | mh_view _ _ Is _ => List.length Is
  | mh_record _ _ _ => ind_nu D
  end.

(** The member [v] of the group [D] at [p] the container's member [i'] of
    [Dq] at [qc] is taken to by the view's map [vm]: of the same head, as
    many parameters, its constructors the container's, each argument
    corresponding. *)
Record view_member (p : qname) (D : ind_decl) (qc : qname) (Dq : ind_decl) (vm : list nat)
    (i' : nat) (Mi' : imember) (v : nat) (Mv : imember) : Prop := mk_view_member
  { (** [vm] takes [i'] to [v] *)
    view_member_v : List.nth_error vm i' = Some v
    (** [v] is a member of the group *)
  ; view_member_mem : ind_member D v = Some Mv
    (** Both are record views, or neither *)
  ; view_member_is_rview : im_is_rview Mv = im_is_rview Mi'
    (** Not a record view, it has the same head: both are the same
        declared member *)
  ; view_member_ref : im_is_rview Mi' = false -> im_ref p v Mv = im_ref qc i' Mi'
    (** Not a record view, as many own uniform parameters *)
  ; view_member_unu : im_is_rview Mi' = false -> im_unu D Mv = im_unu Dq Mi'
    (** A record view, a record view of the same record and fields *)
  ; view_member_rview : forall qr Is fl, im_head Mi' = mh_record qr Is fl -> exists Is', im_head Mv = mh_record qr Is' fl
    (** The same constructor names, in order *)
  ; view_member_names : List.map fst (im_cons Mv) = List.map fst (im_cons Mi')
    (** As many non-uniform parameters *)
  ; view_member_nn : im_nn Mv = im_nn Mi'
    (** Each container constructor is one of [Mv]'s, its arguments
        corresponding *)
  ; view_member_cons : forall c gs', ind_con Mi' c = Some gs' -> exists gs, ind_con Mv c = Some gs /\ cargs_correspond vm gs' gs
    (** And conversely *)
  ; view_member_cons' : forall c gs, ind_con Mv c = Some gs -> exists gs', ind_con Mi' c = Some gs' /\ cargs_correspond vm gs' gs }.

(** The member the view's map takes the container's member [i'] to, of as
    many non-uniform parameters and of the head the declaration gives it
    (the view of [i'] at a declared [i'], a view of the same container
    member at a view, a record view of the same record and fields at a
    record view), is a [view_member]. *)
Lemma view_member_of_head : forall p D qc Dq Is vm i' Mi' v Mv,
    view_wrap_ok D Dq vm -> List.length Is = ind_nu Dq -> ind_member Dq i' = Some Mi' -> List.nth_error vm i' = Some v ->
    ind_member D v = Some Mv -> im_nn Mv = im_nn Mi' ->
    match im_head Mi' with
    | mh_decl _ => exists vm', im_head Mv = mh_view qc i' Is vm'
    | mh_view qv kv Is'' _ => exists Is' vm', im_head Mv = mh_view qv kv Is' vm' /\ List.length Is' = List.length Is''
    | mh_record qr Is'' fl => exists Is', im_head Mv = mh_record qr Is' fl /\ List.length Is' = List.length Is''
    end ->
    view_member p D qc Dq vm i' Mi' v Mv.
Proof.
  intros * Hvw HlIs HMi' Hv HMv Hnn Hhead.
  destruct (view_wrap_ok_members _ _ _ Hvw _ _ _ HMi' Hv) as (Mv' & HMv' & _ & Hnames & Hcorr).
  rewrite HMv in HMv'; injection HMv' as <-.
  assert (Hc1 : forall c gs', ind_con Mi' c = Some gs' -> exists gs, ind_con Mv c = Some gs /\ cargs_correspond vm gs' gs).
  { intros c gs' Hc.
    pose proof (cons_lookup_in _ _ _ Hc) as Hin.
    assert (Hn : List.In c (List.map fst (im_cons Mv))) by (rewrite Hnames; exact (List.in_map fst _ (c, gs') Hin)).
    apply List.in_map_iff in Hn; destruct Hn as ([c0 gs0] & Ec & Hin0); cbn in Ec; subst c0.
    destruct (cons_lookup_of_in _ _ _ Hin0) as [gs HCv].
    exists gs; split; [ exact HCv | exact (Hcorr c gs' gs Hin HCv) ]. }
  assert (Hc2 : forall c gs, ind_con Mv c = Some gs -> exists gs', ind_con Mi' c = Some gs' /\ cargs_correspond vm gs' gs).
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

(** In a typed group, each member of a view's container's group is taken
    to a [view_member]. *)
Lemma view_member_of_typed : forall Θ Ξ p D k Mk qc k' Is vm Dq i' Mi', decl_typed Θ Ξ D ->
    ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm -> ind_lookup Θ Ξ qc = Some Dq -> ind_member Dq i' = Some Mi' ->
    exists v Mv, view_member p D qc Dq vm i' Mi' v Mv.
Proof.
  intros * HD HMk Hh HDq HMi'.
  destruct (decl_typed_view _ _ _ HD _ _ _ _ _ _ HMk Hh) as (Dq' & Mc & HDq' & _ & _ & HlIs & _).
  rewrite HDq in HDq'; injection HDq' as <-.
  destruct (decl_typed_view_wrap _ _ _ HD _ _ _ _ _ _ HMk Hh) as (D' & HD' & Hvw).
  rewrite HDq in HD'; injection HD' as <-.
  assert (Hi' : i' < List.length vm)
    by (rewrite (view_wrap_ok_length _ _ _ Hvw); apply List.nth_error_Some; unfold ind_member in HMi'; congruence).
  destruct (List.nth_error vm i') as [w |] eqn:Hw; [| apply List.nth_error_None in Hw; lia].
  destruct (view_wrap_ok_members _ _ _ Hvw _ _ _ HMi' Hw) as (Mw & HMw & Hnn & _).
  exists w, Mw. apply (view_member_of_head p D qc Dq Is vm i' Mi' w Mw Hvw HlIs HMi' Hw HMw Hnn).
  destruct (im_head Mi') as [pm' | q'' k'' Is'' vm'' | q'' Is'' fl''] eqn:Hh'.
  - destruct (decl_typed_view_decl _ _ _ HD _ _ _ _ _ _ _ _ _ _ _ HMk Hh HDq HMi' Hh' Hw) as (Mw' & vm' & HMw' & Hhw).
    rewrite HMw in HMw'; injection HMw' as <-; exists vm'; exact Hhw.
  - destruct (decl_typed_view_view _ _ _ HD _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh HDq HMi' Hh' Hw) as (Mw' & X & vm' & HMw' & Hhw & HlX).
    rewrite HMw in HMw'; injection HMw' as <-; exists X, vm'; split; [ exact Hhw | exact HlX ].
  - destruct (decl_typed_view_rview _ _ _ HD _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh HDq HMi' Hh' Hw) as (Mw' & X & HMw' & Hhw & HlX).
    rewrite HMw in HMw'; injection HMw' as <-; exists X; split; [ exact Hhw | exact HlX ].
Qed.

Section ViewCountFixed.
  Context {GC : GCtx}.

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
      shape_correspond vm t' t ->
      leaves_in_count D' t' (shape_leaves (rview_leaves D) m t) = List.length (shape_leaves (rview_leaves D') 0 t').
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
                   List.length fs1 = List.length fs1' -> cargs_correspond vm (List.map snd fs2') (List.map snd fs2) ->
                   leaves_in_count D' (pt_self j' Ps') (fields_leaves (rview_leaves D) ns fs2)
                   = List.length (fields_leaves (rview_leaves D') ns' fs2')).
        { induction fs2 as [| [f g] fs2 IHf]; intros [| [f' g'] fs2'] fs1 fs1' ns ns' E E' Lf Hco; cbn [List.map cargs_correspond] in Hco;
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
          destruct g as [rA A | t], g' as [rA' A' | t']; cbn [cargs_correspond snd] in Hco; try contradiction;
            try (match type of Hco with _ = _ /\ cargs_correspond _ _ _ => destruct Hco as [_ Hco] end).
          - cbn [fields_leaves]; exact (IHf _ _ _ _ _ E1 E1' L1 Hco).
          - (** Nested through by the group: none of its paths is the
                container's. *)
            cbn [fields_leaves]; rewrite leaves_in_count_app.
            assert (H0 : leaves_in_count D' (pt_self j' Ps') (List.map (leaf_proj f ns) (shape_leaves (rview_leaves D) (List.length ns) t)) = 0).
            { generalize (shape_leaves (rview_leaves D) (List.length ns) t) as ls; intros ls.
              induction ls as [| l ls IHl]; [ reflexivity |].
              unfold leaves_in_count in *; cbn [List.map List.filter leaf_in]; rewrite HMj', Hh', Hcs', Hfind; exact IHl. }
            rewrite H0; exact (IHf _ _ _ _ _ E1 E1' L1 Hco).
          - (** Recursive in both: the field's shapes correspond. *)
            destruct Hco as (Hmt & Hdp & Hco).
            cbn [fields_leaves]; rewrite leaves_in_count_app, List.length_app, List.length_map.
            assert (H0 : leaves_in_count D' (pt_self j' Ps') (List.map (leaf_proj f ns) (shape_leaves (rview_leaves D) (List.length ns) t))
                         = leaves_in_count D' t' (shape_leaves (rview_leaves D) (List.length ns) t)).
            { generalize (shape_leaves (rview_leaves D) (List.length ns) t) as ls; intros ls.
              induction ls as [| l ls IHl]; [ reflexivity |].
              unfold leaves_in_count in *; cbn [List.map List.filter leaf_in]; rewrite HMj', Hh', Hcs', Hfind.
              destruct (leaf_in D' t' l); cbn; rewrite IHl; reflexivity. }
            rewrite H0.
            destruct (combine_split_at _ _ _ _ _ _ (eq_sym Hlen) E) as [_ Egs1].
            assert (Hrk' : forall Mt, ind_member D (ptyp_mem t) = Some Mt -> im_is_rview Mt = true -> ptyp_mem t < j).
            { intros Mt HMt HrT; exact (rview_struct_order _ _ _ HrsD _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs Egs1 HMt HrT). }
            rewrite (IHn j Hrk t' t (List.length ns) Hrk' (shape_correspond_of _ _ _ Hmt Hdp)).
            rewrite (length_shape_leaves _ t' 0 (List.length ns')).
            f_equal; exact (IHf _ _ _ _ _ E1 E1' L1 Hco). }
        apply (Hfs (List.combine fl gsr) (List.combine fl gsr') nil nil nil nil eq_refl eq_refl eq_refl).
        rewrite !combine_snd_eq by lia; exact Hcorr.
      + (** Members with a block: one path each. *)
        assert (Hrv' : im_is_rview Mj' = false) by congruence.
        cbn [shape_leaves]; rewrite (rview_leaves_not_rview _ _ _ HMj Hrv), (rview_leaves_not_rview _ _ _ HMj' Hrv').
        unfold leaves_in_count; cbn [List.filter leaf_in]; rewrite HMj', Hrv'; reflexivity.
    - (** Through a domain. *)
      cbn [shape_leaves]; rewrite leaves_in_count_map_pi, List.length_map.
      rewrite (IHt t1 (S m) Hrk Hsc); apply length_shape_leaves.
  Qed.

  (** Of a constructor's arguments: as many as the container's recursive
      results. *)
  Lemma cargs_container_count_view : forall gs' gs, cargs_correspond vm gs' gs -> cargs_container_count D D' gs' gs = cargs_nrec D' gs'.
  Proof.
    induction gs' as [| [rA' A' | t'] gs' IH]; intros [| [rA A | t] gs] Hco; cbn [cargs_correspond] in Hco; try contradiction;
      cbn [cargs_container_count cargs_nrec]; try reflexivity; try exact (IH _ (proj2 Hco)).
    destruct Hco as (Hmt & Hdp & Hco).
    rewrite IH by exact Hco; f_equal.
    apply (leaves_in_count_view (S (ptyp_mem t))); [ intros; lia | exact (shape_correspond_of _ _ _ Hmt Hdp) ].
  Qed.
End ViewCount.
End ViewCountFixed.

(** ** The Branches of a Wrapped Block *)

(** The wrapped branch of a constructor: the container's arity at its
    arguments, and the group's branch at an instance. *)
Lemma brs_lookup_wrap : forall r pq D D' Us Bks Mv Bs cs c,
    brs_lookup (List.map (fun cg => wrap_branch r pq D D' Us Bks Mv Bs (fst cg) (snd cg)) cs) c
    = option_map (fun gs' => ((im_nn Mv + List.length gs' + cargs_nrec D' gs')%nat, snd (wrap_branch r pq D D' Us Bks Mv Bs c gs')))
        (cons_lookup cs c).
Proof.
  intros r pq D D' Us Bks Mv Bs; induction cs as [| [c' gs'] cs IH]; intros c; [ reflexivity |].
  cbn [List.map fst snd cons_lookup]; unfold wrap_branch at 1; cbv zeta; cbn [brs_lookup].
  destruct (String.eqb c c') eqn:E; [ apply String.eqb_eq in E; subst c'; reflexivity | apply IH ].
Qed.

(** One wrapped branch per constructor, in order. *)
Lemma brs_names_wrap : forall r pq D D' Us Bks Mv Bs cs,
    brs_names cs (List.map (fun cg => wrap_branch r pq D D' Us Bks Mv Bs (fst cg) (snd cg)) cs).
Proof.
  intros; unfold brs_names; rewrite List.map_map; apply List.map_ext; intros [c gs']; reflexivity.
Qed.

(** A wrapped branch is a constructor's, of the container's arity. *)
Lemma brs_in_wrap : forall r pq D D' Us Bks Mv Bs cs c n B,
    In (c, n, B) (List.map (fun cg => wrap_branch r pq D D' Us Bks Mv Bs (fst cg) (snd cg)) cs) ->
    exists gs', In (c, gs') cs /\ n = (im_nn Mv + List.length gs' + cargs_nrec D' gs')%nat.
Proof.
  intros * H; apply List.in_map_iff in H as ([c0 gs0] & He & Hin).
  unfold wrap_branch in He; cbv zeta in He; cbn [fst snd] in He; injection He as Hc0 Hn0 _.
  exists gs0; split; [ rewrite <- Hc0; exact Hin | symmetry; exact Hn0 ].
Qed.
