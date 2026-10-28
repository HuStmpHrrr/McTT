(** * The Eliminator at a View, as the Container's (E1′)

    The eliminator of a group [D] at its view [m] of the container's
    declared member [k'] at the instance [Is] is the container's
    eliminator at [k'], at the view's blocks wrapped ([view_wrap]).  At related
    environments the two eliminate related elements to related values
    (the cross relation): by induction on the group's elements, a
    constructor's branch against its wrapped branch, which is the group's
    branch at an instance of its context ([ViewBranch.v]); a stuck
    eliminator against the container's stuck eliminator, read back alike
    by the views' rank, the blocks the two read being the group's own by
    the agreement of the views' maps ([view_maps_coherent]).

    The recursive results go by leaf path.  The container's results of an
    argument recursive in both are those along its own leaf paths ([D']'s
    table), the group's along the group's ([D]'s): at a record view, the
    group's paths through a field the container takes as non-recursive are
    not the container's ([leaf_in]); there the group's result is its own
    eliminator's. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing Views.
From Mctt.Core.Syntactic.System.Global Require Import Presup MemberLemmas MemberWf.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Instance Telescope.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness Require Import VariableCases FunctionCases LevelCases SubtypingCases.
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews ArgTypes ViewEquations ViewArgs Con CargsRel Elim Iota ViewBranch.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence ViewCount IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The shapes of a view against its container's ([shape_corr]) and the
    count of the leaf paths the container has ([cargs_nin_view]) are in
    [Core.Semantic.Inductives.ViewCount]. *)

(** ** The Recursive Results of a View against its Container's

    The container's group [D'] (the left side) against the group [D] (the
    right side), [dr] and [Rel] the group's relations of the shapes'
    domains and of the members' results; [ρa], [pq], [ua] and [Bksa] the
    group's eliminator, whose results are the group's where the container
    has none. *)
Section CrossRel.
  Variables (D D' : ind_decl).
  Variable (dr : nat -> list domain -> exp -> relation domain).
  Variable (Rel : nat -> list domain -> domain -> list domain -> domain -> relation domain).
  Variables (ρa : env) (pq : qname) (ua : list domain) (Bksa : list eblock).

  (** The recursive results [rs] of the container's argument [v] of shape
      [t'], along the container's leaf paths, against [rs'] of the
      group's argument [v'] of shape [t], along the group's, after the
      values [pre] and [pre'] of the shapes' components: at the end at
      members with a block, related at [Rel] of the group's member; at
      record views, those of their fields at the projections; at a domain,
      pointwise. *)
  Inductive cross_result_rel (k : nat) (u u' : list domain) :
      list domain -> list domain -> ptyp -> ptyp -> domain -> domain -> list domain -> list domain -> Prop :=
  (** At the end, at members with a block: related at [Rel] of the
      group's member [j] *)
  | cross_result_self : forall pre pre' j' Mj' Ps' j Mj Ps bs bs' v v' ih ih',
      ind_member D' j' = Some Mj' -> im_is_rview Mj' = false ->
      ind_member D j = Some Mj -> im_is_rview Mj = false ->
      ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (u ++ pre) ↘ bs ->
      ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (u' ++ pre') ↘ bs' ->
      Rel j bs v bs' v' ih ih' ->
      cross_result_rel k u u' pre pre' (pt_self j' Ps') (pt_self j Ps) v v' (ih :: nil) (ih' :: nil)
  (** At the end, at record views of one record and fields: the results of
      their fields at the projections *)
  | cross_result_rview : forall pre pre' j' Mj' qr Is' fl c' gs' Ps' j Mj Is c gs Ps v v' ws ws' rs rs',
      ind_member D' j' = Some Mj' -> im_head Mj' = mh_record qr Is' fl -> im_cons Mj' = (c', gs') :: nil ->
      ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil ->
      ⟦projs fl of v ⟧ gc_deps ⍮ gc_stack ↘ ws -> ⟦projs fl of v' ⟧ gc_deps ⍮ gc_stack ↘ ws' ->
      cross_fields_rel j u u' nil nil gs' gs ws ws' rs rs' ->
      cross_result_rel k u u' pre pre' (pt_self j' Ps') (pt_self j Ps) v v' rs rs'
  (** At a domain: pointwise at related arguments *)
  | cross_result_pi : forall pre pre' B' t' B t v v' rs rs',
      (forall c c', dr k pre B c c' -> cross_result_app_rel k u u' (pre ++ c :: nil) (pre' ++ c' :: nil) t' t v c v' c' rs rs') ->
      cross_result_rel k u u' pre pre' (pt_pi B' t') (pt_pi B t) v v' rs rs'
  with cross_result_app_rel (k : nat) (u u' : list domain) :
      list domain -> list domain -> ptyp -> ptyp -> domain -> domain -> domain -> domain -> list domain -> list domain -> Prop :=
  (** The arguments and each result applied, related at the rest *)
  | cross_result_app_mk : forall pre pre' t' t v c v' c' rs rs' fc fc' rcs rcs',
      $| v & c | gc_deps ⍮ gc_stack ↘ fc -> $| v' & c' | gc_deps ⍮ gc_stack ↘ fc' ->
      List.Forall2 (fun f r => $| f & c | gc_deps ⍮ gc_stack ↘ r) rs rcs ->
      List.Forall2 (fun f r => $| f & c' | gc_deps ⍮ gc_stack ↘ r) rs' rcs' ->
      cross_result_rel k u u' pre pre' t' t fc fc' rcs rcs' ->
      cross_result_app_rel k u u' pre pre' t' t v c v' c' rs rs'
  (** The recursive results [w] of the container's arguments [vs] of kinds
      [gs'] against [ihs] of the group's arguments [vs'] of kinds [gs],
      after the values [pre] and [pre'] of the non-uniform parameters and
      the non-recursive arguments before them. *)
  with cross_fields_rel (k : nat) (u u' : list domain) :
      list domain -> list domain -> list carg -> list carg -> list domain -> list domain -> list domain -> list domain -> Prop :=
  (** No argument *)
  | cross_fields_nil : forall pre pre', cross_fields_rel k u u' pre pre' nil nil nil nil nil nil
  (** Non-recursive in both: no result, the argument joins the prefixes *)
  | cross_fields_arg : forall pre pre' A' A gs' gs v v' vs vs' w ihs,
      cross_fields_rel k u u' (pre ++ v :: nil) (pre' ++ v' :: nil) gs' gs vs vs' w ihs ->
      cross_fields_rel k u u' pre pre' (ca_arg A' :: gs') (ca_arg A :: gs) (v :: vs) (v' :: vs') w ihs
  (** Nested through: no result of the container's; the group's are its
      eliminator's *)
  | cross_fields_nest : forall pre pre' A' t gs' gs v v' vs vs' w rs' ihs,
      ⟦ih v' of t under pq ua Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ rs' ->
      cross_fields_rel k u u' pre pre' gs' gs vs vs' w ihs ->
      cross_fields_rel k u u' pre pre' (ca_arg A' :: gs') (ca_rec t :: gs) (v :: vs) (v' :: vs') w (rs' ++ ihs)
  (** Recursive in both: the results along each side's leaf paths, the
      container's one per path of the group's it has *)
  | cross_fields_rec : forall pre pre' t' t gs' gs v v' vs vs' rs rs' w ihs,
      List.length rs = leaves_in_count D' t' (shape_leaves (rv_leaves D) 0 t) ->
      List.length rs' = List.length (shape_leaves (rv_leaves D) 0 t) ->
      cross_result_rel k u u' pre pre' t' t v v' rs rs' ->
      cross_fields_rel k u u' pre pre' gs' gs vs vs' w ihs ->
      cross_fields_rel k u u' pre pre' (ca_rec t' :: gs') (ca_rec t :: gs) (v :: vs) (v' :: vs') (rs ++ w) (rs' ++ ihs).

  Lemma cross_fields_rel_vs_len : forall k u u' pre pre' gs' gs vs vs' w ihs,
      cross_fields_rel k u u' pre pre' gs' gs vs vs' w ihs -> List.length vs = List.length gs /\ List.length vs' = List.length gs.
  Proof. induction 1; cbn; lia. Qed.

  Lemma cross_fields_rel_w_len : forall k u u' pre pre' gs' gs vs vs' w ihs,
      cross_fields_rel k u u' pre pre' gs' gs vs vs' w ihs -> List.length w = cargs_nin D D' gs' gs.
  Proof. induction 1; cbn [cargs_nin List.length]; rewrite ?List.length_app; lia. Qed.
End CrossRel.

Scheme cross_result_rel_mut_ind := Induction for cross_result_rel Sort Prop
with cross_result_app_rel_mut_ind := Induction for cross_result_app_rel Sort Prop
with cross_fields_rel_mut_ind := Induction for cross_fields_rel Sort Prop.
Combined Scheme cross_result_rel_mut_ind_all from cross_result_rel_mut_ind, cross_result_app_rel_mut_ind, cross_fields_rel_mut_ind.

(** ** The Skeleton of a Leaf Path

    What [leaf_in] reads of a path: its steps and the fields it projects,
    not the members, components and names before. *)
Fixpoint leaf_skel (l : leaf_path) : leaf_path :=
  match l with
  | leaf_self _ _ => leaf_self 0 nil
  | leaf_pi _ l1 => leaf_pi a_True (leaf_skel l1)
  | leaf_proj f _ l1 => leaf_proj f nil (leaf_skel l1)
  end.

Lemma leaf_in_skel : forall D' l t', leaf_in D' t' (leaf_skel l) = leaf_in D' t' l.
Proof.
  intros D' l; induction l as [j Ps | B l IH | f ns l IH]; intros [j' Ps' | B' t']; cbn [leaf_skel leaf_in]; auto.
  destruct (ind_member D' j') as [M' |]; [| reflexivity ].
  destruct (im_head M'), (im_cons M') as [| [? ?] [|]]; try reflexivity.
  destruct (List.find _ _) as [[? [] ] |]; try reflexivity; apply IH.
Qed.

Lemma leaf_skel_wk : forall l φ, leaf_skel (leaf_wk φ l) = leaf_skel l.
Proof. induction l as [j Ps | B l IH | f ns l IH]; intros φ; cbn [leaf_wk leaf_skel]; rewrite ?IH; reflexivity. Qed.

(** The flags of the paths a test [g] keeps, among those of all paths. *)
Fixpoint sel_flags (cs fs : list bool) : list bool :=
  match cs, fs with
  | true :: cs', f :: fs' => f :: sel_flags cs' fs'
  | false :: cs', _ :: fs' => sel_flags cs' fs'
  | _, _ => nil
  end.

Lemma sel_flags_map : forall (g f : leaf_path -> bool) ls,
    sel_flags (List.map g ls) (List.map f ls) = List.map f (List.filter g ls).
Proof. intros g f; induction ls as [| l ls IH]; cbn; [ reflexivity |]; destruct (g l); cbn; rewrite IH; reflexivity. Qed.

(** ** The Leaf Paths the Container Has

    The leaf paths of a shape of the group's [D] that are the container's
    [D'] ([leaf_in]) are as many as the container's own leaf paths of the
    corresponding shape ([shape_corr]): the view's map takes each member of
    the container's group to one of the group's of the same kind, a record
    view to one of the same record and fields, its fields' kinds
    corresponding ([view_member]). *)
(** A field found by its name among fields of corresponding kinds, of
    the same names: found at the same place, of a corresponding kind. *)
Lemma find_corr : forall vm fs' fs f f1 t', List.map fst fs' = List.map fst fs ->
    cargs_corr vm (List.map snd fs') (List.map snd fs) ->
    List.find (fun fg => String.eqb (fst fg) f) fs' = Some (f1, ca_rec t') ->
    exists t, List.find (fun fg => String.eqb (fst fg) f) fs = Some (f1, ca_rec t) /\ shape_corr vm t' t.
Proof.
  intros vm; induction fs' as [| [f0 g0'] fs' IH]; intros [| [f2 g0] fs] f f1 t' Hn Hc Hf; cbn in Hn, Hf; try discriminate.
  injection Hn as <- Hn; cbn [List.map cargs_corr] in Hc |- *.
  destruct (String.eqb f0 f) eqn:E.
  - injection Hf as -> ->.
    destruct g0 as [A | t]; cbn in Hc; [ contradiction |].
    destruct Hc as (Hmt & Hdp & _); exists t; split; [ cbn; rewrite E; reflexivity | exact (shape_corr_of _ _ _ Hmt Hdp) ].
  - cbn; rewrite E; apply (IH fs f f1 t' Hn); [| exact Hf ].
    destruct g0', g0; cbn in Hc; try contradiction; tauto.
Qed.

Section ViewCount.
  Variables (p qc : qname) (D D' : ind_decl) (vm : list nat).
  Hypotheses (HlcD : leaves_coherent D) (HlcQ : leaves_coherent D')
    (HrsD : rview_struct_ok gc_deps gc_stack D) (HrsQ : rview_struct_ok gc_deps gc_stack D').
  Hypothesis (Hvm : forall j' j, List.nth_error vm j' = Some j ->
                exists Mj' Mj, ind_member D' j' = Some Mj' /\ view_member p D qc D' vm j' Mj' j Mj).

  (** The count of those leaf paths ([leaves_in_count_view],
      [cargs_nin_view]) is in [Core.Semantic.Inductives.ViewCount].
      More: those leaf paths are the container's own, in order, up to
      their skeletons. *)
  Lemma filter_map_pi : forall B B' t' ls,
      List.filter (leaf_in D' (pt_pi B' t')) (List.map (leaf_pi B) ls) = List.map (leaf_pi B) (List.filter (leaf_in D' t') ls).
  Proof. intros B B' t'; induction ls as [| l ls IH]; cbn; [ reflexivity |]; destruct (leaf_in D' t' l); cbn; rewrite IH; reflexivity. Qed.

  Lemma filter_map_wk : forall t' φ ls,
      List.filter (leaf_in D' t') (List.map (leaf_wk φ) ls) = List.map (leaf_wk φ) (List.filter (leaf_in D' t') ls).
  Proof. intros t' φ; induction ls as [| l ls IH]; cbn; [ reflexivity |]; rewrite leaf_in_wk; destruct (leaf_in D' t' l); cbn; rewrite IH; reflexivity. Qed.

  Lemma skel_map_wk : forall φ ls, List.map leaf_skel (List.map (leaf_wk φ) ls) = List.map leaf_skel ls.
  Proof. intros; rewrite List.map_map; apply List.map_ext; intros; apply leaf_skel_wk. Qed.

  Lemma leaves_view_skel : forall n t' t m m',
      (forall Mj, ind_member D (ptyp_mem t) = Some Mj -> im_is_rview Mj = true -> ptyp_mem t < n) ->
      shape_corr vm t' t ->
      List.map leaf_skel (List.filter (leaf_in D' t') (shape_leaves (rv_leaves D) m t))
      = List.map leaf_skel (shape_leaves (rv_leaves D') m' t').
  Proof.
    induction n as [n IHn] using Wf_nat.lt_wf_ind.
    intros t'; induction t' as [j' Ps' | B' t1' IHt]; intros [j Ps | B t1] m m' Hrk Hsc; cbn in Hsc; try contradiction.
    - destruct (Hvm _ _ Hsc) as (Mj' & Mj & HMj' & Hvmb).
      pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMj.
      pose proof (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvmb) as Ervs.
      destruct (im_is_rview Mj) eqn:Hrv.
      + specialize (Hrk Mj HMj Hrv); cbn [ptyp_mem] in Hrk.
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
        rewrite filter_map_wk, !skel_map_wk.
        assert (Hfs : forall fs2 fs2' fs1 fs1' ns ns', List.combine fl gsr = fs1 ++ fs2 -> List.combine fl gsr' = fs1' ++ fs2' ->
                   List.length fs1 = List.length fs1' -> cargs_corr vm (List.map snd fs2') (List.map snd fs2) ->
                   List.map leaf_skel (List.filter (leaf_in D' (pt_self j' Ps')) (fields_leaves (rv_leaves D) ns fs2))
                   = List.map leaf_skel (fields_leaves (rv_leaves D') ns' fs2')).
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
            cbn [fields_leaves]; rewrite List.filter_app.
            assert (H0 : List.filter (leaf_in D' (pt_self j' Ps'))
                           (List.map (leaf_proj f ns) (shape_leaves (rv_leaves D) (List.length ns) t)) = nil).
            { generalize (shape_leaves (rv_leaves D) (List.length ns) t) as ls; intros ls.
              induction ls as [| l ls IHl]; [ reflexivity |].
              cbn [List.map List.filter leaf_in]; rewrite HMj', Hh', Hcs', Hfind; exact IHl. }
            rewrite H0; exact (IHf _ _ _ _ _ E1 E1' L1 Hco).
          - destruct Hco as (Hmt & Hdp & Hco).
            cbn [fields_leaves]; rewrite List.filter_app, !List.map_app.
            assert (H0 : List.filter (leaf_in D' (pt_self j' Ps'))
                           (List.map (leaf_proj f ns) (shape_leaves (rv_leaves D) (List.length ns) t))
                         = List.map (leaf_proj f ns) (List.filter (leaf_in D' t') (shape_leaves (rv_leaves D) (List.length ns) t))).
            { generalize (shape_leaves (rv_leaves D) (List.length ns) t) as ls; intros ls.
              induction ls as [| l ls IHl]; [ reflexivity |].
              cbn [List.map List.filter leaf_in]; rewrite HMj', Hh', Hcs', Hfind.
              destruct (leaf_in D' t' l); cbn; rewrite IHl; reflexivity. }
            rewrite H0, !List.map_map.
            destruct (combine_split_at _ _ _ _ _ _ (eq_sym Hlen) E) as [_ Egs1].
            assert (Hrk' : forall Mt, ind_member D (ptyp_mem t) = Some Mt -> im_is_rview Mt = true -> ptyp_mem t < j).
            { intros Mt HMt HrT; exact (rview_struct_order _ _ _ HrsD _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs Egs1 HMt HrT). }
            pose proof (IHn j Hrk t' t (List.length ns) (List.length ns') Hrk' (shape_corr_of _ _ _ Hmt Hdp)) as IHt'.
            f_equal; [| exact (IHf _ _ _ _ _ E1 E1' L1 Hco) ].
            transitivity (List.map (fun l => leaf_proj f nil (leaf_skel l))
                            (List.filter (leaf_in D' t') (shape_leaves (rv_leaves D) (List.length ns) t)));
              [ apply List.map_ext; intros; reflexivity |].
            transitivity (List.map (fun l => leaf_proj f nil (leaf_skel l)) (shape_leaves (rv_leaves D') (List.length ns') t'));
              [| apply List.map_ext; intros; reflexivity ].
            rewrite <- (List.map_map leaf_skel (leaf_proj f nil)), IHt', List.map_map; reflexivity. }
        apply (Hfs (List.combine fl gsr) (List.combine fl gsr') nil nil nil nil eq_refl eq_refl eq_refl).
        rewrite !combine_snd_eq by lia; exact Hcorr.
      + assert (Hrv' : im_is_rview Mj' = false) by congruence.
        cbn [shape_leaves]; rewrite (rv_leaves_not_rview _ _ _ HMj Hrv), (rv_leaves_not_rview _ _ _ HMj' Hrv').
        cbn [List.filter leaf_in]; rewrite HMj', Hrv'; reflexivity.
    - cbn [shape_leaves]; rewrite filter_map_pi, !List.map_map.
      transitivity (List.map (fun l => leaf_pi a_True (leaf_skel l)) (List.filter (leaf_in D' t1') (shape_leaves (rv_leaves D) (S m) t1)));
        [ reflexivity |].
      transitivity (List.map (fun l => leaf_pi a_True (leaf_skel l)) (shape_leaves (rv_leaves D') (S m') t1')); [| reflexivity ].
      rewrite <- !(List.map_map leaf_skel (leaf_pi a_True)), (IHt t1 (S m) (S m') Hrk Hsc); reflexivity.
  Qed.

  (** A path of the container's ([leaf_in]) is one of the group's: the
      group's record views have recursive every field the container's
      have. *)
  Lemma leaf_in_view_mono : forall l t' t, shape_corr vm t' t -> leaf_in D' t' l = true -> leaf_in D t l = true.
  Proof.
    induction l as [j0 Ps0 | B0 l IH | f ns l IH]; intros [j' Ps' | B' t1'] [j Ps | B t1] Hsc Hin; cbn in Hsc; try contradiction;
      cbn [leaf_in] in Hin |- *; try discriminate; try exact (IH _ _ Hsc Hin).
    - destruct (Hvm _ _ Hsc) as (Mj' & Mj & HMj' & Hvmb).
      rewrite HMj' in Hin; rewrite (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb), (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvmb).
      exact Hin.
    - destruct (Hvm _ _ Hsc) as (Mj' & Mj & HMj' & Hvmb).
      pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMj.
      rewrite HMj' in Hin; rewrite HMj.
      destruct (im_head Mj') as [| | qr Is' fl] eqn:Hh'; try discriminate Hin.
      destruct (view_member_rview _ _ _ _ _ _ _ _ _ Hvmb _ _ _ Hh') as (Is0 & Hh).
      destruct (rview_struct_con _ _ _ HrsD _ _ _ _ _ HMj Hh) as (gsr & Hcs & Hlen).
      destruct (rview_struct_con _ _ _ HrsQ _ _ _ _ _ HMj' Hh') as (gsr' & Hcs' & Hlen').
      rewrite Hcs' in Hin; rewrite Hh, Hcs.
      destruct (view_member_cons' _ _ _ _ _ _ _ _ _ Hvmb rview_con gsr
                  ltac:(unfold ind_con; rewrite Hcs; cbn; rewrite ?String.eqb_refl; reflexivity)) as (g0 & Hc0 & Hcorr).
      unfold ind_con in Hc0; rewrite Hcs' in Hc0; cbn in Hc0; rewrite ?String.eqb_refl in Hc0; injection Hc0 as <-.
      (** The field [f], on each side. *)
      destruct (List.find (fun fg => String.eqb (fst fg) f) (List.combine fl gsr')) as [[f1 g'] |] eqn:Hf'; [| discriminate Hin ].
      destruct g' as [A' | t']; [ discriminate Hin |].
      destruct (find_corr vm (List.combine fl gsr') (List.combine fl gsr) f f1 t'
                  ltac:(rewrite !combine_fst_eq by lia; reflexivity) ltac:(rewrite !combine_snd_eq by lia; exact Hcorr) Hf')
        as (t & Hf & Hsc').
      rewrite Hf.
      exact (IH t' t Hsc' Hin).
  Qed.

End ViewCount.

(** ** The Recursive Results of a Wrapped Branch's Instance

    Along the group's leaf paths [ls] of an argument whose shape the
    container has as [t']: the container's next result of [rsC] at a path
    the container has, the group's of [rsG] at the others
    ([wrap_leaves]); and so over a constructor's arguments, [gs'] as the
    container has them, [gs] as the group does ([wrap_ihs]). *)
Fixpoint merge_leaves (D' : ind_decl) (t' : ptyp) (ls : list leaf_path) (rsG rsC : list domain) : list domain :=
  match ls, rsG with
  | l :: ls', g :: rsG' =>
      if leaf_in D' t' l then List.hd d_True rsC :: merge_leaves D' t' ls' rsG' (List.tl rsC)
      else g :: merge_leaves D' t' ls' rsG' rsC
  | _, _ => nil
  end.

(** The recursive results of a constructor's arguments, [gs'] as the
    container has them and [gs] as the group does: at an argument
    recursive on both sides, [merge_leaves] of the group's results [ihsG]
    and the container's [w]; at one recursive in the group only, the
    group's results. *)
Fixpoint merge_ihs (D' D : ind_decl) (gs' gs : list carg) (ihsG w : list domain) : list domain :=
  match gs', gs with
  | ca_rec t' :: gs1', ca_rec t :: gs1 =>
      let ls := shape_leaves (rv_leaves D) 0 t in
      merge_leaves D' t' ls (List.firstn (List.length ls) ihsG) w ++
        merge_ihs D' D gs1' gs1 (List.skipn (List.length ls) ihsG) (List.skipn (leaves_in_count D' t' ls) w)
  | ca_arg _ :: gs1', ca_rec t :: gs1 =>
      let n := List.length (shape_leaves (rv_leaves D) 0 t) in
      List.firstn n ihsG ++ merge_ihs D' D gs1' gs1 (List.skipn n ihsG) w
  | _ :: gs1', ca_arg _ :: gs1 => merge_ihs D' D gs1' gs1 ihsG w
  | _, _ => nil
  end.

Lemma skipn_S_tl : forall {A : Type} n (l : list A), List.skipn (S n) l = List.skipn n (List.tl l).
Proof. intros A n [| x l]; cbn; [ destruct n; reflexivity | reflexivity ]. Qed.

Lemma merge_leaves_ext : forall D' t' ls1 ls2 rsG rsC, List.map (leaf_in D' t') ls1 = List.map (leaf_in D' t') ls2 ->
    merge_leaves D' t' ls1 rsG rsC = merge_leaves D' t' ls2 rsG rsC.
Proof.
  intros D' t'; induction ls1 as [| l1 ls1 IH]; intros [| l2 ls2] rsG rsC H; cbn in H; try discriminate; [ reflexivity |].
  injection H as Hl Hls; destruct rsG as [| g rsG]; cbn [merge_leaves]; [ reflexivity |].
  rewrite Hl; destruct (leaf_in D' t' l2); rewrite (IH _ _ _ Hls); reflexivity.
Qed.

Lemma merge_leaves_map_pi : forall D' B B' t' ls rsG rsC,
    merge_leaves D' (pt_pi B' t') (List.map (leaf_pi B) ls) rsG rsC = merge_leaves D' t' ls rsG rsC.
Proof.
  intros D' B B' t'; induction ls as [| l ls IH]; intros [| g rsG] rsC; cbn [List.map merge_leaves leaf_in]; try reflexivity.
  destruct (leaf_in D' t' l); rewrite IH; reflexivity.
Qed.

Lemma merge_leaves_map_wk : forall D' t' φ ls rsG rsC,
    merge_leaves D' t' (List.map (leaf_wk φ) ls) rsG rsC = merge_leaves D' t' ls rsG rsC.
Proof.
  intros D' t' φ; induction ls as [| l ls IH]; intros [| g rsG] rsC; cbn [List.map merge_leaves]; try reflexivity.
  rewrite leaf_in_wk; destruct (leaf_in D' t' l); rewrite IH; reflexivity.
Qed.

Lemma length_merge_leaves : forall D' t' ls rsG rsC, List.length rsG = List.length ls ->
    List.length (merge_leaves D' t' ls rsG rsC) = List.length ls.
Proof.
  intros D' t'; induction ls as [| l ls IH]; intros [| g rsG] rsC H; cbn in H |- *; try lia.
  destruct (leaf_in D' t' l); cbn; rewrite IH by lia; reflexivity.
Qed.

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

Lemma merge_leaves_none : forall D' t' ls rsG rsC, (forall l, In l ls -> leaf_in D' t' l = false) ->
    List.length rsG = List.length ls -> merge_leaves D' t' ls rsG rsC = rsG.
Proof.
  intros D' t'; induction ls as [| l ls IH]; intros [| g rsG] rsC Hn Hl; cbn in Hl |- *; try lia; [ reflexivity |].
  rewrite (Hn l (or_introl eq_refl)), IH; [ reflexivity | intros; apply Hn; right; assumption | lia ].
Qed.

Lemma merge_leaves_Forall2 : forall (P : domain -> domain -> Prop) D' t' ls rsG rsC rsG' rsC',
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

Lemma merge_leaves_map_in : forall D' t1 t2 (F : leaf_path -> leaf_path) ls rsG rsC,
    (forall l, leaf_in D' t1 (F l) = leaf_in D' t2 l) ->
    merge_leaves D' t1 (List.map F ls) rsG rsC = merge_leaves D' t2 ls rsG rsC.
Proof.
  intros D' t1 t2 F; induction ls as [| l ls IH]; intros [| g rsG] rsC H; cbn [List.map merge_leaves]; try reflexivity.
  rewrite H; destruct (leaf_in D' t2 l); rewrite IH by exact H; reflexivity.
Qed.

Lemma leaves_in_count_map_in : forall D' t1 t2 (F : leaf_path -> leaf_path) ls,
    (forall l, leaf_in D' t1 (F l) = leaf_in D' t2 l) -> leaves_in_count D' t1 (List.map F ls) = leaves_in_count D' t2 ls.
Proof.
  intros D' t1 t2 F; induction ls as [| l ls IH]; intros H; [ reflexivity |].
  unfold leaves_in_count in *; cbn [List.map List.filter]; rewrite H; destruct (leaf_in D' t2 l); cbn; rewrite IH by exact H; reflexivity.
Qed.

Lemma merge_leaves_map_out : forall D' t1 (F : leaf_path -> leaf_path) ls rsG rsC,
    (forall l, leaf_in D' t1 (F l) = false) -> List.length rsG = List.length ls -> merge_leaves D' t1 (List.map F ls) rsG rsC = rsG.
Proof.
  intros * H L; apply merge_leaves_none; [| rewrite List.length_map; exact L ].
  intros l Hl; apply List.in_map_iff in Hl as (l0 & <- & _); apply H.
Qed.

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

(** The functions of the recursive results of a function shape, applied:
    the recursive results of the rest at the function's value. *)
Lemma ihfn_apps_inv : forall ρ Bks q0 ups t v c fc X rcs n,
    $| v & c | gc_deps ⍮ gc_stack ↘ fc -> ⟦ih fc of t under q0 ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ X -> List.length X = n ->
    List.Forall2 (fun f r => $| f & c | gc_deps ⍮ gc_stack ↘ r) (List.map (fun i => d_ihfn ρ Bks q0 ups t i v) (List.seq 0 n)) rcs ->
    rcs = X.
Proof.
  intros * Ef EX LX HF.
  apply List.nth_error_ext; intros i.
  destruct (Nat.lt_ge_cases i n) as [Hi | Hi].
  - destruct (nth_error_lt_some' X i ltac:(lia)) as [x Hx].
    assert (Hm : List.nth_error (List.map (fun i => d_ihfn ρ Bks q0 ups t i v) (List.seq 0 n)) i = Some (d_ihfn ρ Bks q0 ups t i v))
      by (rewrite List.nth_error_map, List.nth_error_seq; destruct (Nat.ltb_spec i n); [ reflexivity | lia ]).
    destruct (Forall2_nth_error _ _ _ _ _ HF Hm) as (r & Hr & Ea).
    inversion Ea; subst.
    match goal with H1 : $| v & c | _ ⍮ _ ↘ ?f1, H2 : ⟦ih ?f1 of t under q0 ups Bks ⟧ _ ⍮ _ ⍮ ρ ↘ ?X1 |- _ =>
      pose proof (functional_eval_app _ _ _ _ H1 Ef) as ->; pose proof (functional_eval_ih _ _ _ _ _ _ _ _ H2 EX) as -> end.
    congruence.
  - pose proof (List.Forall2_length HF) as L; rewrite List.length_map, List.length_seq in L.
    rewrite !(proj2 (List.nth_error_None _ _)) by lia; reflexivity.
Qed.

(** The leaf paths of record views' fields: the container has a path of
    the group's through a field the container takes as recursive when its
    own field's shape has the rest. *)
Lemma length_fields_leaves : forall D fs ns, List.length (fields_leaves (rv_leaves D) ns fs) = cargs_nrec D (List.map snd fs).
Proof.
  intros D; induction fs as [| [f [A | t]] fs IH]; intros ns; cbn [fields_leaves List.map snd cargs_nrec]; [ reflexivity | apply IH |].
  rewrite List.length_app, List.length_map, IH, (length_shape_leaves _ _ _ 0); reflexivity.
Qed.

Lemma merge_leaves_fields : forall D D' j' Mj' qr Is' fl c' gsr' Ps' gsr,
    ind_member D' j' = Some Mj' -> im_head Mj' = mh_record qr Is' fl -> im_cons Mj' = (c', gsr') :: nil ->
    List.NoDup fl -> List.length fl = List.length gsr' -> List.length fl = List.length gsr ->
    forall ihsG rsC, List.length ihsG = cargs_nrec D gsr ->
    merge_leaves D' (pt_self j' Ps') (fields_leaves (rv_leaves D) nil (List.combine fl gsr)) ihsG rsC = merge_ihs D' D gsr' gsr ihsG rsC.
Proof.
  intros * HMj' Hh' Hcs' Hnd Hlen' Hlen.
  assert (Hfs : forall fs2 fs2' fs1 fs1' ns, List.combine fl gsr = fs1 ++ fs2 -> List.combine fl gsr' = fs1' ++ fs2' ->
             List.length fs1 = List.length fs1' -> forall ihsG rsC, List.length ihsG = cargs_nrec D (List.map snd fs2) ->
             merge_leaves D' (pt_self j' Ps') (fields_leaves (rv_leaves D) ns fs2) ihsG rsC
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
      destruct g as [A | t].
      + cbn [fields_leaves List.map snd]; cbn [List.map snd cargs_nrec] in Lg.
        rewrite (IHf _ _ _ _ E1 E1' L1 _ _ Lg); destruct g'; reflexivity.
      + cbn [fields_leaves List.map snd]; cbn [List.map snd cargs_nrec] in Lg.
        assert (Lls : List.length (shape_leaves (rv_leaves D) (List.length ns) t) = List.length (shape_leaves (rv_leaves D) 0 t))
          by apply length_shape_leaves.
        rewrite merge_leaves_app by (rewrite List.length_map, length_fields_leaves; lia).
        rewrite List.length_map, Lls.
        assert (Lsk : List.length (List.skipn (List.length (shape_leaves (rv_leaves D) 0 t)) ihsG) = cargs_nrec D (List.map snd fs2))
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
          rewrite (merge_leaves_ext _ _ _ (shape_leaves (rv_leaves D) 0 t) _ _ (leaf_in_shape_leaves _ _ _ _ _ _)).
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
    List.nth n (merge_leaves D' t' ls rsG rsC) d_True = List.nth (leaves_in_count D' t' (List.firstn n ls)) rsC d_True.
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

(** The group's results at the paths the container has. *)
Fixpoint sel_leaves_vals (D' : ind_decl) (t' : ptyp) (ls : list leaf_path) (rs : list domain) : list domain :=
  match ls, rs with
  | l :: ls', r :: rs' => if leaf_in D' t' l then r :: sel_leaves_vals D' t' ls' rs' else sel_leaves_vals D' t' ls' rs'
  | _, _ => nil
  end.

(** The group's recursive results [ihs] of a constructor's arguments at the
    paths the container has: [sel_leaves_vals] at an argument recursive on
    both sides, none at one recursive in the group only. *)
Fixpoint sel_ihs (D' D : ind_decl) (gs' gs : list carg) (ihs : list domain) : list domain :=
  match gs', gs with
  | ca_rec t' :: gs1', ca_rec t :: gs1 =>
      let ls := shape_leaves (rv_leaves D) 0 t in
      sel_leaves_vals D' t' ls (List.firstn (List.length ls) ihs) ++ sel_ihs D' D gs1' gs1 (List.skipn (List.length ls) ihs)
  | ca_arg _ :: gs1', ca_rec t :: gs1 => sel_ihs D' D gs1' gs1 (List.skipn (List.length (shape_leaves (rv_leaves D) 0 t)) ihs)
  | _ :: gs1', ca_arg _ :: gs1 => sel_ihs D' D gs1' gs1 ihs
  | _, _ => nil
  end.

Lemma sel_leaves_vals_ext : forall D' t' ls1 ls2 rs, List.map (leaf_in D' t') ls1 = List.map (leaf_in D' t') ls2 ->
    sel_leaves_vals D' t' ls1 rs = sel_leaves_vals D' t' ls2 rs.
Proof.
  intros D' t'; induction ls1 as [| l1 ls1 IH]; intros [| l2 ls2] rs H; cbn in H; try discriminate; [ reflexivity |].
  injection H as Hl Hls; destruct rs as [| r rs]; cbn [sel_leaves_vals]; [ reflexivity |].
  rewrite Hl, (IH _ _ Hls); reflexivity.
Qed.

Lemma sel_leaves_vals_snoc : forall D' t' ls l rs r, List.length rs = List.length ls ->
    sel_leaves_vals D' t' (ls ++ l :: nil) (rs ++ r :: nil)
    = sel_leaves_vals D' t' ls rs ++ (if leaf_in D' t' l then r :: nil else nil).
Proof.
  intros D' t'; induction ls as [| l0 ls IH]; intros l [| r0 rs] r Hl; cbn in Hl |- *; try lia.
  - destruct (leaf_in D' t' l); reflexivity.
  - rewrite IH by lia; destruct (leaf_in D' t' l0); reflexivity.
Qed.

Lemma length_sel_leaves_vals : forall D' t' ls rs, List.length rs = List.length ls ->
    List.length (sel_leaves_vals D' t' ls rs) = leaves_in_count D' t' ls.
Proof.
  intros D' t'; induction ls as [| l ls IH]; intros [| r rs] Hl; cbn in Hl |- *; try lia; try reflexivity.
  unfold leaves_in_count in *; cbn [List.filter]; destruct (leaf_in D' t' l); cbn; rewrite IH by lia; reflexivity.
Qed.

(** The instance of a stage with its own variables leaves the variables'
    terms as they are. *)
Lemma wrap_inst_var : forall nn na r x, sentry_exp (wrap_inst nn na r (vars_from 0 r) x) = a_var x.
Proof.
  intros nn na r x; unfold wrap_inst.
  rewrite List.app_assoc, sb_of_list_app.
  destruct (Nat.lt_ge_cases x r) as [Hx | Hx]; [ rewrite sb_of_list_vars by exact Hx; reflexivity |].
  replace x with (List.length (vars_from 0 r) + (x - r)) at 1 by (rewrite length_vars_from; lia).
  rewrite sb_of_list_ge, sb_of_list_app.
  destruct (Nat.lt_ge_cases (x - r) na) as [Hx' | Hx']; [ rewrite sb_of_list_vars by exact Hx'; cbn; f_equal; lia |].
  replace (x - r) with (List.length (vars_from r na) + (x - r - na)) by (rewrite length_vars_from; lia).
  rewrite sb_of_list_ge.
  destruct (Nat.lt_ge_cases (x - r - na) nn) as [Hx'' | Hx'']; [ rewrite sb_of_list_vars by exact Hx''; cbn; f_equal; lia |].
  replace (x - r - na) with (List.length (vars_from (r + na) nn) + (x - r - na - nn)) by (rewrite length_vars_from; lia).
  rewrite sb_of_list_ge; cbn; f_equal; lia.
Qed.

(** The components of a branch's recursive results at a stage of [r]
    results: variables, and the uniform parameters past the stage. *)
Lemma ihs_sub_shape : forall nn Us na pat r y, List.length pat <= na ->
    (exists z, sentry_exp (ihs_sub nn Us na pat r y) = a_var z) \/
    (exists M, sentry_exp (ihs_sub nn Us na pat r y) = M[sb_of_wk (wk_shiftn (r + na + nn))]).
Proof.
  intros * Hp; unfold ihs_sub; cbn [sb_compose sb_of_wk sentry_sub].
  set (z := wk_pat pat y).
  destruct (Nat.lt_ge_cases z (List.length pat + nn)) as [Hz | Hz].
  - left; rewrite sb_qn_lt by exact Hz; cbn; eexists; reflexivity.
  - rewrite sb_qn_ge by exact Hz.
    assert (HU : forall x, (exists M, sb_of_list Id Us x = se_exp M) \/ sb_of_list Id Us x = se_var (x - List.length Us)).
    { intros x; destruct (Nat.lt_ge_cases x (List.length Us)) as [Hx | Hx].
      - left; rewrite (sb_of_list_nth _ _ _ a_True) by exact Hx; eexists; reflexivity.
      - right; replace x with (List.length Us + (x - List.length Us)) at 1 by lia; rewrite sb_of_list_ge; reflexivity. }
    destruct (HU (z - (List.length pat + nn))) as [[M EM] | EM]; rewrite EM; cbn [sentry_wk sentry_sub sentry_exp].
    + right; exists M; rewrite exp_sub_of_wk, exp_wk_wk, <- exp_sub_of_wk; apply exp_sub_sb_eq.
      intros w; cbn; f_equal; lia.
    + left; eexists; reflexivity.
Qed.

(** A branch's components at a stage of [r] results: the parameters'
    instance moved by the arguments before, as terms. *)
Lemma ihs_sub_wrap : forall nn Us na r (gs1 : list carg), List.length gs1 <= na ->
    forall y, sentry_exp (ihs_sub nn Us na (cargs_pat gs1) r y) = sentry_exp (cargs_sub (wrap_base Us nn na r) gs1 (vars_from r na) y).
Proof.
  intros * Hg y.
  pose proof (wrap_inst_ihs_sub nn Us na r gs1 (vars_from 0 r) Hg) as H; rewrite length_vars_from in H.
  rewrite <- (H y); cbn [sb_compose]; rewrite <- sentry_exp_sub.
  destruct (ihs_sub_shape nn Us na (cargs_pat gs1) r y ltac:(rewrite length_cargs_pat; exact Hg)) as [[z Ez] | [M EM]];
    rewrite ?Ez, ?EM.
  - cbn [exp_sub]; rewrite wrap_inst_var; reflexivity.
  - rewrite exp_sub_sub; apply exp_sub_sb_eq.
    pose proof (wrap_inst_shift nn na r (vars_from 0 r)) as Hs; rewrite length_vars_from in Hs; symmetry; exact Hs.
Qed.

Lemma length_merge_ihs : forall D' D gs' gs ihs w, cargs_kinds gs' gs -> List.length ihs = cargs_nrec D gs ->
    List.length (merge_ihs D' D gs' gs ihs w) = cargs_nrec D gs.
Proof.
  intros D' D; induction gs' as [| [A' | t'] gs' IH]; intros [| [A | t] gs] ihs w Hk Hl; cbn in Hk |- *; try contradiction;
    cbn [cargs_nrec] in Hl; try reflexivity; rewrite ?List.length_app.
  - exact (IH _ _ _ Hk Hl).
  - rewrite List.length_firstn, (IH gs) by (try exact Hk; rewrite List.length_skipn; lia); lia.
  - rewrite length_merge_leaves by (rewrite List.length_firstn; lia);
      rewrite (IH gs) by (try exact Hk; rewrite List.length_skipn; lia); lia.
Qed.

Lemma merge_ihs_app : forall D' D G1' G1 G2' G2 ihs w, cargs_kinds G1' G1 ->
    merge_ihs D' D (G1' ++ G2') (G1 ++ G2) ihs w
    = merge_ihs D' D G1' G1 (List.firstn (cargs_nrec D G1) ihs) w ++
      merge_ihs D' D G2' G2 (List.skipn (cargs_nrec D G1) ihs) (List.skipn (cargs_nin D D' G1' G1) w).
Proof.
  intros D' D; induction G1' as [| [A' | t'] G1' IH]; intros [| [A | t] G1] G2' G2 ihs w Hk; cbn in Hk; try contradiction;
    cbn [List.app merge_ihs cargs_nrec cargs_nin].
  - reflexivity.
  - exact (IH _ _ _ _ _ Hk).
  - rewrite IH by exact Hk; rewrite <- List.app_assoc, List.firstn_firstn, Nat.min_l by lia; f_equal; f_equal.
    + rewrite List.skipn_firstn_comm.
      replace (List.length (shape_leaves (rv_leaves D) 0 t) + cargs_nrec D G1 - List.length (shape_leaves (rv_leaves D) 0 t))
        with (cargs_nrec D G1) by lia; reflexivity.
    + rewrite List.skipn_skipn, Nat.add_comm; reflexivity.
  - rewrite IH by exact Hk; rewrite <- List.app_assoc, List.firstn_firstn, Nat.min_l by lia; f_equal; f_equal.
    + rewrite List.skipn_firstn_comm.
      replace (List.length (shape_leaves (rv_leaves D) 0 t) + cargs_nrec D G1 - List.length (shape_leaves (rv_leaves D) 0 t))
        with (cargs_nrec D G1) by lia; reflexivity.
    + rewrite !List.skipn_skipn, (Nat.add_comm (cargs_nrec D G1)), (Nat.add_comm (cargs_nin D D' G1' G1)); reflexivity.
Qed.

Lemma sel_ihs_app : forall D' D G1' G1 G2' G2 ihs, cargs_kinds G1' G1 ->
    sel_ihs D' D (G1' ++ G2') (G1 ++ G2) ihs
    = sel_ihs D' D G1' G1 (List.firstn (cargs_nrec D G1) ihs) ++ sel_ihs D' D G2' G2 (List.skipn (cargs_nrec D G1) ihs).
Proof.
  intros D' D; induction G1' as [| [A' | t'] G1' IH]; intros [| [A | t] G1] G2' G2 ihs Hk; cbn in Hk; try contradiction;
    cbn [List.app sel_ihs cargs_nrec].
  - reflexivity.
  - exact (IH _ _ _ _ Hk).
  - rewrite IH by exact Hk; f_equal; f_equal.
    + rewrite List.skipn_firstn_comm.
      replace (List.length (shape_leaves (rv_leaves D) 0 t) + cargs_nrec D G1 - List.length (shape_leaves (rv_leaves D) 0 t))
        with (cargs_nrec D G1) by lia; reflexivity.
    + rewrite List.skipn_skipn, Nat.add_comm; reflexivity.
  - rewrite IH by exact Hk; rewrite <- List.app_assoc, List.firstn_firstn, Nat.min_l by lia; f_equal; f_equal.
    + rewrite List.skipn_firstn_comm.
      replace (List.length (shape_leaves (rv_leaves D) 0 t) + cargs_nrec D G1 - List.length (shape_leaves (rv_leaves D) 0 t))
        with (cargs_nrec D G1) by lia; reflexivity.
    + rewrite List.skipn_skipn, Nat.add_comm; reflexivity.
Qed.

Lemma length_sel_ihs : forall D' D gs' gs ihs, cargs_kinds gs' gs -> List.length ihs = cargs_nrec D gs ->
    List.length (sel_ihs D' D gs' gs ihs) = cargs_nin D D' gs' gs.
Proof.
  intros D' D; induction gs' as [| [A' | t'] gs' IH]; intros [| [A | t] gs] ihs Hk Hl; cbn in Hk |- *; try contradiction;
    cbn [cargs_nrec] in Hl; try reflexivity.
  - exact (IH _ _ Hk Hl).
  - apply IH; [ exact Hk | rewrite List.length_skipn; lia ].
  - rewrite List.length_app, length_sel_leaves_vals by (rewrite List.length_firstn; lia).
    rewrite IH by (try exact Hk; rewrite List.length_skipn; lia); reflexivity.
Qed.

(** The type of the group's recursive result along a leaf path, at a stage
    of [r] results, as the branch's context has it ([leaves_ctx]) and as
    the wrapped branch's does ([wrap_leaves_ctx]). *)
Lemma wrap_leaf_ihty_eq : forall D v Mv c gs gs1 t gs2 l As Us r, decl_closed D -> decl_mvc D ->
    ind_member D v = Some Mv -> In (c, gs) (im_cons Mv) -> gs = gs1 ++ ca_rec t :: gs2 ->
    In l (shape_leaves (rv_leaves D) (pat_nargs (cargs_pat gs1) + im_nn Mv) t) ->
    leaf_ihty As (sb_of_wk (wk_shiftn (r + List.length gs + im_nn Mv))) (ihs_sub (im_nn Mv) Us (List.length gs) (cargs_pat gs1) r)
      (a_var (r + List.length gs - 1 - List.length (cargs_pat gs1))) l
    = leaf_ihty As (sb_of_wk (wk_shiftn (r + List.length gs + im_nn Mv)))
        (cargs_sub (wrap_base Us (im_nn Mv) (List.length gs) r) gs1 (vars_from r (List.length gs)))
        (a_var (r + (List.length gs - 1 - List.length gs1))) l.
Proof.
  intros * Hc Hmvc HMv Hin Heq Hinl.
  assert (Hlt : List.length gs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
  rewrite length_cargs_pat.
  replace (r + List.length gs - 1 - List.length gs1) with (r + (List.length gs - 1 - List.length gs1)) by lia.
  pose proof (member_closed_recs _ _ (decl_closed_members _ Hc _ _ HMv) _ _ _ _ _ Hin Heq) as Hst.
  rewrite cargs_strat_nonrec, List.length_rev, List.length_map in Hst.
  assert (Hsl : leaf_scoped (pat_nargs (cargs_pat gs1) + im_nn Mv + ind_nu D) l).
  { assert (Hst' : ptyp_scoped (pat_nargs (cargs_pat gs1) + im_nn Mv + ind_nu D) t)
      by (rewrite pat_nargs_cargs_pat, cargs_strat_nonrec, List.length_rev, List.length_map;
          replace (List.length (cargs_nonrec gs1) + im_nn Mv + ind_nu D) with (List.length (cargs_nonrec gs1) + im_np D Mv)
            by (unfold im_np, im_nn; lia); exact Hst).
    pose proof (shape_leaves_scoped (rv_leaves D) (ind_nu D) t (pat_nargs (cargs_pat gs1) + im_nn Mv) (rv_leaves_scoped D Hc) Hst') as HF.
    rewrite List.Forall_forall in HF; exact (HF l Hinl). }
  assert (Hml : leaf_mvc l).
  { destruct (decl_mvc_members _ Hmvc _ _ HMv) as (_ & _ & Hmg).
    pose proof (Hmg _ _ Hin) as Hm; rewrite Heq in Hm; apply List.Forall_app in Hm as [_ Hm].
    apply List.Forall_cons_iff in Hm as [[HmB HmP] _].
    pose proof (shape_leaves_mvc (rv_leaves D) t (pat_nargs (cargs_pat gs1) + im_nn Mv) (rv_leaves_mvc _ Hmvc) HmB HmP) as HM.
    rewrite List.Forall_forall in HM; exact (HM _ Hinl). }
  eapply leaf_ihty_mvc_agree; [ exact Hsl | exact Hml |].
  intros y _; apply ihs_sub_wrap; lia.
Qed.

(** ** The Branches of a Wrapped Block *)
Lemma brs_lookup_wrap : forall pq D D' Us Bks Mv Bs cs c,
    brs_lookup (List.map (fun cg => wrap_br pq D D' Us Bks Mv Bs (fst cg) (snd cg)) cs) c
    = option_map (fun gs' => ((im_nn Mv + List.length gs' + cargs_nrec D' gs')%nat, snd (wrap_br pq D D' Us Bks Mv Bs c gs')))
        (cons_lookup cs c).
Proof.
  induction cs as [| [c' gs'] cs IH]; intros c; [ reflexivity |].
  cbn [List.map fst snd cons_lookup]; unfold wrap_br at 1; cbv zeta; cbn [brs_lookup].
  destruct (String.eqb c c') eqn:E; [ apply String.eqb_eq in E; subst c'; reflexivity | apply IH ].
Qed.

Lemma brs_names_wrap : forall pq D D' Us Bks Mv Bs cs,
    brs_names cs (List.map (fun cg => wrap_br pq D D' Us Bks Mv Bs (fst cg) (snd cg)) cs).
Proof.
  intros; unfold brs_names; rewrite List.map_map; apply List.map_ext; intros [c gs']; reflexivity.
Qed.

Lemma brs_in_wrap : forall pq D D' Us Bks Mv Bs cs c n B,
    In (c, n, B) (List.map (fun cg => wrap_br pq D D' Us Bks Mv Bs (fst cg) (snd cg)) cs) ->
    exists gs', In (c, gs') cs /\ n = (im_nn Mv + List.length gs' + cargs_nrec D' gs')%nat.
Proof.
  intros * H; apply List.in_map_iff in H as ([c0 gs0] & He & Hin).
  unfold wrap_br in He; cbv zeta in He; cbn [fst snd] in He; injection He as Hc0 Hn0 _.
  exists gs0; split; [ rewrite <- Hc0; exact Hin | symmetry; exact Hn0 ].
Qed.

(** The context of a wrapped branch is a telescope of assumptions, of
    as many entries as the branch's arity. *)
Lemma wrap_leaves_ctx_ass : forall D' t' nn As Us na gs0 ls r, tele_ass (wrap_leaves_ctx D' t' nn As Us na gs0 r ls).
Proof.
  intros D' t' nn As Us na gs0; induction ls as [| l ls IH]; intros r; cbn [wrap_leaves_ctx]; [ constructor |].
  destruct (leaf_in D' t' l); [ apply List.Forall_app; split; [ apply IH | constructor; eauto ] | apply IH ].
Qed.

Lemma wrap_ihs_ctx_ass : forall D D' nn As Us na gs' gs gs0 r, tele_ass (wrap_ihs_ctx D D' nn As Us na gs0 r gs' gs).
Proof.
  intros D D' nn As Us na; induction gs' as [| [] gs' IH]; intros [| [] gs] *; cbn [wrap_ihs_ctx]; try constructor; try apply IH.
  apply List.Forall_app; split; [ apply IH | apply wrap_leaves_ctx_ass ].
Qed.

Lemma wrap_bctx_ass : forall pq D D' k M gs' gs As Us, decl_closed D -> ind_member D k = Some M ->
    tele_ass (wrap_bctx pq D D' M gs' gs As Us).
Proof.
  intros * HD HM; unfold wrap_bctx; apply List.Forall_app; split; [ apply wrap_ihs_ctx_ass |].
  apply List.Forall_app; split; apply tele_ass_sub; [ apply cargs_ctx_aux_ass | eapply decl_closed_nparams_ass; eassumption ].
Qed.

Lemma length_wrap_bctx : forall pq D D' M gs' gs As Us, cargs_kinds gs' gs ->
    List.length (wrap_bctx pq D D' M gs' gs As Us) = (cargs_nin D D' gs' gs + List.length gs + im_nn M)%nat.
Proof.
  intros * Hk; unfold wrap_bctx; rewrite !List.length_app, length_wrap_ihs_ctx by exact Hk.
  rewrite !length_tele_sub, length_cargs_ctx; unfold im_nn; lia.
Qed.

(** A list substitution evaluated: the values of its terms after its
    base's. *)
Lemma eval_sb_of_list_inv : forall Ms σ ρ E E0, ⟦ sb_of_list σ Ms ⟧s gc_deps ⍮ gc_stack ⍮ ρ ↘ E ->
    ⟦ σ ⟧s gc_deps ⍮ gc_stack ⍮ ρ ↘ E0 ->
    exists ms, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\ env_eq E (env_args E0 ms).
Proof.
  induction Ms as [| M Ms IH]; intros σ ρ E E0 H H0; cbn [sb_of_list] in H.
  - exists nil; split; [ constructor |]; cbn; intros x; specialize (H x); specialize (H0 x).
    destruct (σ x); cbn in H, H0.
    + rewrite H, H0; reflexivity.
    + destruct H as (m & -> & Hm); destruct H0 as (m' & -> & Hm'); f_equal; eapply functional_eval_exp; eassumption.
    + destruct H as (h & -> & Hh); destruct H0 as (h' & -> & Hh'); f_equal; eapply functional_eval_modexp; eassumption.
    + destruct H as (n & h & -> & Hn & Hh); destruct H0 as (n' & h' & -> & Hn' & Hh');
        f_equal; [ eapply functional_eval_exp | eapply functional_eval_modexp ]; eassumption.
  - pose proof (H (List.length Ms + 0)) as Hx; rewrite sb_of_list_ge in Hx; cbn in Hx.
    destruct Hx as (m & Hme & Hm).
    destruct (IH _ _ _ (E0 ↦ m) H (eval_sub_extend _ _ _ _ _ H0 Hm)) as (ms & Hms & HE).
    exists (m :: ms); split; [ econstructor; eassumption | exact HE ].
Qed.

(** The value of the wrapped branch's recursive results: the container's,
    variables of the last [|w|] entries of the environment, where the
    paths are its, the values of the group's [ihsE] elsewhere
    ([merge_leaves], [merge_ihs]). *)
Lemma eval_wrap_leaves : forall D' t' ls ihs ihsE C Y w r',
    List.length ihs = List.length ls -> ⟦ ihs ⟧* gc_deps ⍮ gc_stack ⍮ env_args C (Y ++ w) ↘ ihsE ->
    r' + leaves_in_count D' t' ls <= List.length w ->
    ⟦ wrap_leaves D' t' ls ihs r' (List.length w) ⟧* gc_deps ⍮ gc_stack ⍮ env_args C (Y ++ w)
      ↘ merge_leaves D' t' ls ihsE (List.skipn r' w).
Proof.
  intros D' t'; induction ls as [| l ls IH]; intros [| ih ihs] ihsE C Y w r' Lh Ev Lw; cbn in Lh; try discriminate.
  - inversion Ev; subst; cbn; constructor.
  - inversion Ev as [| ? ? ? e es Ee Ees]; subst.
    assert (Hc : leaves_in_count D' t' (l :: ls) = (if leaf_in D' t' l then 1 else 0) + leaves_in_count D' t' ls)
      by (unfold leaves_in_count; cbn; destruct (leaf_in D' t' l); reflexivity).
    rewrite Hc in Lw; cbn [wrap_leaves merge_leaves].
    destruct (leaf_in D' t' l).
    + destruct (nth_error_lt_some' w r' ltac:(lia)) as [a Ha].
      rewrite (skipn_nth_cons _ _ _ Ha); cbn [List.hd List.tl].
      constructor; [| apply IH; [ lia | exact Ees | lia ] ].
      pose proof (eval_var_args C (Y ++ w) (List.length w - 1 - r') ltac:(rewrite List.length_app; lia)) as HV.
      replace (List.nth (List.length (Y ++ w) - 1 - (List.length w - 1 - r')) (Y ++ w) d_true) with a in HV; [ exact HV |].
      rewrite List.length_app, List.app_nth2 by lia.
      replace (List.length Y + List.length w - 1 - (List.length w - 1 - r') - List.length Y) with r' by lia.
      symmetry; apply List.nth_error_nth; exact Ha.
    + constructor; [ exact Ee | apply IH; [ lia | exact Ees | lia ] ].
Qed.

Lemma eval_wrap_ihs : forall D' D gs' gs ihs ihsE C Y w r', cargs_kinds gs' gs -> List.length ihs = cargs_nrec D gs ->
    ⟦ ihs ⟧* gc_deps ⍮ gc_stack ⍮ env_args C (Y ++ w) ↘ ihsE -> r' + cargs_nin D D' gs' gs <= List.length w ->
    ⟦ wrap_ihs D' D gs' gs ihs r' (List.length w) ⟧* gc_deps ⍮ gc_stack ⍮ env_args C (Y ++ w)
      ↘ merge_ihs D' D gs' gs ihsE (List.skipn r' w).
Proof.
  intros D' D; induction gs' as [| [A' | t'] gs' IH]; intros [| [A | t] gs] ihs ihsE C Y w r' Hk Lh Ev Lw;
    cbn in Hk; try contradiction; cbn [wrap_ihs merge_ihs cargs_nrec cargs_nin] in Lh, Lw |- *.
  - inversion Ev; subst; constructor.
  - exact (IH _ _ _ _ _ _ _ Hk Lh Ev Lw).
  - set (n0 := List.length (shape_leaves (rv_leaves D) 0 t)) in *.
    rewrite <- (List.firstn_skipn n0 ihs) in Ev.
    apply eval_exps_app_inv in Ev as (a & b & -> & Ea & Eb).
    pose proof (eval_exps_length _ _ _ Ea) as La; rewrite List.length_firstn, Nat.min_l in La by lia.
    rewrite firstn_app_exact, skipn_app_exact by exact La.
    apply eval_exps_app; [ exact Ea |].
    apply IH; [ exact Hk | rewrite List.length_skipn; lia | exact Eb | exact Lw ].
  - set (ls := shape_leaves (rv_leaves D) 0 t) in *.
    rewrite <- (List.firstn_skipn (List.length ls) ihs) in Ev.
    apply eval_exps_app_inv in Ev as (a & b & -> & Ea & Eb).
    pose proof (eval_exps_length _ _ _ Ea) as La; rewrite List.length_firstn, Nat.min_l in La by lia.
    rewrite firstn_app_exact, skipn_app_exact by exact La.
    apply eval_exps_app.
    + apply eval_wrap_leaves; [ rewrite List.length_firstn; lia | exact Ea | lia ].
    + rewrite List.skipn_skipn; apply IH; [ exact Hk | rewrite List.length_skipn; lia | exact Eb | lia ].
Qed.

(** ** The Container's Eliminator against the Group's

    The eliminator of the container's group [D'] at [qc], at the blocks
    [VBb] at [ρb] and the uniform parameters [ub], against the group's at
    [Bks] at [C1]: at related elements of the group's member [j] the view's
    map [vm] takes the container's [i'] to, related results, when the
    blocks are related member by member ([Hmot_x], [Hbr_x]) and so are the
    stuck eliminators ([Hbot_x]).  The container's side is on the left.

    First, the group's eliminator against itself at [C1], and the group's
    recursive results of a wrapped branch's instance ([merge_ihs]). *)
Section SelfElim.
  #[local] Set Default Proof Using "All".
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups VP) (HPD : VP p D).
  Let Hvg := valid_groups_valid VP HP p D HPD.
  Let Hcv := containers_valid_of_groups VP HP p D HPD.
  Let HD := valid_group_valid _ _ Hvg.
  Let Hc := valid_group_closed _ _ Hvg.
  Let Hl := valid_group_lookup _ _ Hvg.
  Let Hdt := valid_group_typed _ _ Hvg.
  Let Hass := valid_group_ass _ _ Hvg.
  Let Hlc : leaves_coherent D := leaves_coherent_of_order D (rview_struct_order _ _ _ (grp_tele_ass_rstruct _ Hass)).
  Variable (Γ : ctx) (RΓ : relation env).
  Hypotheses (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HΓ : ⊨ Γ).
  Variable (RU : relation env).
  Hypothesis (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).
  Variable (Us : list exp).
  Hypotheses (HUl : List.length Us = ind_nu D)
    (HUs : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊨ N : T).
  Variable (C1 : env) (u0 : list domain).
  Hypotheses (HC11 : RΓ C1 C1) (HUC : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ C1 ↘ u0).
  Variable (Bks : list eblock) (iA : nat).
  Hypothesis (HBk : valid_blocks p D Γ Us Bks iA).
  Let HBks := valid_blocks_has p D Γ Us Bks iA Hdt HBk.
  Let HMall := valid_blocks_mctx _ _ _ _ _ _ HBk.
  Let HAv := valid_blocks_motive _ _ _ _ _ _ HBk.
  Let nr := canon_nparams_rel D u0.
  Let ar := canon_args_rel D u0.
  Let dr := canon_doms_rel u0.
  Let G := grp_rel p D u0 nr ar dr.
  Let Rel := fun j ns m ns' m' =>
    per_head (List.nth j (blocks_motives Bks) a_True) (List.nth j (blocks_motives Bks) a_True)
      (env_args C1 (ns ++ m :: nil)) (env_args C1 (ns' ++ m' :: nil)).
  #[local] Abbreviation EB f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HC11 HUC).
  #[local] Abbreviation EM f := (EB f C1 HC11 Bks iA HBks HMall HAv).
  #[local] Abbreviation u0_len' := (u0_len D Us HUl C1 u0 HUC).
  #[local] Abbreviation u0_env' := (EB u0_env).
  #[local] Abbreviation u0_gargs' := (EB u0_gargs).
  #[local] Abbreviation Hcp := (vg_canon p D Hvg u0 u0_gargs' u0_len').
  #[local] Abbreviation HnP := (ind_canon_props_np_per _ _ Hcp).
  #[local] Abbreviation HnI := (ind_canon_props_np_iff _ _ Hcp).
  #[local] Abbreviation HaP := (ind_canon_props_arg_per _ _ Hcp).
  #[local] Abbreviation HaI := (ind_canon_props_arg_iff _ _ Hcp).
  #[local] Abbreviation HdP := (ind_canon_props_dom_per _ _ Hcp).
  #[local] Abbreviation HdI := (ind_canon_props_dom_iff _ _ Hcp).
  #[local] Abbreviation Had := (vg_adm p D Hvg u0 u0 u0_gargs' u0_len' u0_gargs').

  (** *** The Group's Eliminator against Itself at [C1] *)
  Lemma self_ups_ok : elim_ups_ok p D u0 nr ar dr u0 u0.
  Proof. exact (EB ups_ok u0 u0 u0_env' u0_env' u0_len' u0_len'). Qed.

  Lemma self_motive : forall j Mj ba bb u u' ns ns' x x', ind_member D j = Some Mj -> im_is_rview Mj = false ->
      List.nth_error Bks j = Some ba -> List.nth_error Bks j = Some bb -> G j u u' ns ns' x x' ->
      exists a a', ⟦ eb_motive ba ⟧ env_args C1 (ns ++ x :: nil) ↘ a /\ ⟦ eb_motive bb ⟧ env_args C1 (ns' ++ x' :: nil) ↘ a' /\
        DF a ≈ a' ∈ per_univ_elem iA ↘ Rel j ns x ns' x'.
  Proof.
    intros * HMj _ Hba Hbb Hm; rewrite Hba in Hbb; injection Hbb as <-.
    exact (EB mot_mid C1 HC11 Bks iA HMall j Mj ba (eb_motive ba) HMj Hba (HAv _ _ _ HMj Hba) u u' ns ns' x x' Hm).
  Qed.

  Lemma self_branch : forall j Mj ba bb c gs n Ba Bb u u' bs bs' vs vs' ihs ihs' hd k0, ind_member D j = Some Mj ->
      im_is_rview Mj = false -> List.nth_error Bks j = Some ba -> List.nth_error Bks j = Some bb -> ind_con Mj c = Some gs ->
      brs_lookup (eb_brs ba) c = Some (n, Ba) -> brs_lookup (eb_brs bb) c = Some (n, Bb) ->
      G j u u' (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs') (d_con hd k0 c (bs ++ vs)) (d_con hd k0 c (bs' ++ vs')) ->
      rec_results_rel D dr Rel j u u' (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs') gs vs vs' ihs ihs' ->
      exists r r', ⟦ Ba ⟧ env_args C1 (List.skipn (im_unu D Mj) bs ++ vs ++ ihs) ↘ r /\
        ⟦ Bb ⟧ env_args C1 (List.skipn (im_unu D Mj) bs' ++ vs' ++ ihs') ↘ r' /\
        Rel j (List.skipn (im_unu D Mj) bs) (d_con hd k0 c (bs ++ vs)) (List.skipn (im_unu D Mj) bs') (d_con hd k0 c (bs' ++ vs')) r r'.
  Proof.
    assert (HBB : forall j Mj b b' c gs n B B', ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
               List.nth_error Bks j = Some b' -> ind_con Mj c = Some gs ->
               brs_lookup (eb_brs b) c = Some (n, B) -> brs_lookup (eb_brs b') c = Some (n, B') ->
               elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ ⊨ B ≈ B' : elim_bty p D j Mj c gs (eb_motive b) Us).
    { intros * HMj Hb Hb' Hcon Hlb Hlb'; rewrite Hb in Hb'; injection Hb' as <-.
      rewrite Hlb in Hlb'; injection Hlb' as <-.
      exact (valid_blocks_branch _ _ _ _ _ _ HBk _ _ _ _ _ _ _ HMj Hb Hcon (brs_lookup_in _ _ _ _ Hlb)). }
    exact (EM br_mid (valid_blocks_bctx _ _ _ _ _ _ HBk) Bks HBB).
  Qed.

  #[local] Abbreviation XS f := (f p D u0 nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI Had iA C1 C1 Bks Bks u0 u0 self_ups_ok Rel
     HBks HBks (valid_blocks_nm _ _ _ _ _ _ HBk) (valid_blocks_nm _ _ _ _ _ _ HBk)
     (valid_blocks_names _ _ _ _ _ _ HBk) (valid_blocks_names _ _ _ _ _ _ HBk) (valid_blocks_arity _ _ _ _ _ _ HBk)
     (valid_blocks_arity _ _ _ _ _ _ HBk) (decl_typed_nodup _ _ _ Hdt) self_motive
     (EB rneut_rel u0 u0 u0_env' u0_env' u0_len' u0_len') self_branch).

  Lemma self_elim_all :
      (forall j u u' ns ns' x x', G j u u' ns ns' x x' -> member_results p D dr C1 C1 Bks Bks u0 u0 Rel j u u' ns ns' x x') /\
      (forall k u u' pre pre' gs vs vs',
        con_args_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' gs vs vs' ->
        exists ihs ihs', ⟦ihs vs of gs under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ ihs /\
          ⟦ihs vs' of gs under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ ihs' /\
          rec_results_rel D dr Rel k u u' pre pre' gs vs vs' ihs ihs') /\
      (forall k u u' pre pre' t x x',
        rec_arg_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t x x' ->
        exists rs rs', ⟦ih x of t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ rs /\
          ⟦ih x' of t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ rs' /\
          rec_result_rel D dr Rel k u u' pre pre' t x x' rs rs') /\
      (forall k u u' pre pre' t f c f' c',
        rec_arg_app_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t f c f' c' ->
        exists fc fc' rcs rcs', $| f & c | gc_deps ⍮ gc_stack ↘ fc /\ $| f' & c' | gc_deps ⍮ gc_stack ↘ fc' /\
          ⟦ih fc of t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ rcs /\
          ⟦ih fc' of t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ rcs' /\
          rec_result_rel D dr Rel k u u' pre pre' t fc fc' rcs rcs').
  Proof. exact (XS per_ind_elim_all). Qed.

  (** The recursive results of related neutrals of a record view, and their
      types, at the projections: defined on each side. *)
  #[warnings="-cannot-define-projection"]
  Record self_rview_results (gs : list carg) (ws ws' : list domain) : Prop := mk_self_rview_results
    { (** The left types *)
      self_rview_tys : list domain
      (** The right types *)
    ; self_rview_tys' : list domain
      (** The left results *)
    ; self_rview_rs : list domain
      (** The right results *)
    ; self_rview_rs' : list domain
      (** The left types, over the uniform parameters *)
    ; self_rview_Ta : ⟦ihtys ws of gs at p u0 under C1 (blocks_motives Bks) ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil u0 ↘ self_rview_tys
      (** The right types *)
    ; self_rview_Tb : ⟦ihtys ws' of gs at p u0 under C1 (blocks_motives Bks) ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil u0 ↘ self_rview_tys'
      (** The left results *)
    ; self_rview_Ra : ⟦ihs ws of gs under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ self_rview_rs
      (** The right results *)
    ; self_rview_Rb : ⟦ihs ws' of gs under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ self_rview_rs' }.

  Lemma self_rview_ihs : forall k ns ns' v v' Mk qr Is fl c gs ws ws', G k u0 u0 ns ns' v v' -> is_neut v -> is_neut v' ->
      ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl -> im_cons Mk = (c, gs) :: nil ->
      ⟦projs fl of v ⟧ gc_deps ⍮ gc_stack ↘ ws -> ⟦projs fl of v' ⟧ gc_deps ⍮ gc_stack ↘ ws' ->
      self_rview_results gs ws ws'.
  Proof.
    intros * HG Hv Hv' HM Hh Hcs Ew Ew'.
    assert (Hfl : forall ms : list nat, leaf_flags_ok (elim_bot p D u0 nr ar dr C1 C1 Bks Bks u0 u0) (List.map (fun _ => true) ms) ms)
      by (induction ms; cbn; constructor; assumption).
    destruct (proj1 (XS ih_leaves_all) _ _ _ _ _ _ _ HG eq_refl eq_refl Hv Hv' _ _ _ _ _ _ _ _ HM Hh Hcs Ew Ew' _ (Hfl _))
      as [tya tyb resa resb Ta Tb Ra Rb _ _ _ _ _].
    exact (mk_self_rview_results _ _ _ tya tyb resa resb Ta Tb Ra Rb).
  Qed.

  Lemma self_motive_move : forall j Mj u u' ns ns' x x' ns1 ns1', ind_member D j = Some Mj -> im_is_rview Mj = false ->
      G j u u' ns ns' x x' ->
      tele_rel (nr j) (List.rev (im_nparams Mj)) ns ns1 -> tele_rel (nr j) (List.rev (im_nparams Mj)) ns' ns1' ->
      (Rel j ns x ns' x' <~> Rel j ns1 x ns1' x').
  Proof. exact (XS motive_rel_move). Qed.

  Lemma self_ref_target : forall j Mj hd k, ind_member D j = Some Mj -> im_ref p j Mj = (hd, k) ->
      exists Dq Mk, ind_lookup gc_deps gc_stack hd = Some Dq /\ ind_member Dq k = Some Mk /\
        im_nn Mk = im_nn Mj /\ ind_nu Dq = im_unu D Mj.
  Proof. exact (XS im_ref_target). Qed.

  (** *** The Container's Results Merged into the Group's

      Results of the container's group [D'] against the group's, as the
      cross relation has them, and the group's own results [ihsG] at the
      container's arguments, related to the group's eliminator's at the
      group's: the group's results with the container's at the paths it has
      ([merge_leaves], [merge_ihs]) are related as the group's. *)
  Section Merge.
    Variable (D' : ind_decl).
    Hypothesis (HrsQ : rview_struct_ok gc_deps gc_stack D').
    Let HrsD := grp_tele_ass_rstruct _ Hass.

    Lemma cross_merge_all : forall k u u',
      (forall pre pre' t' t v v' rs rs', cross_result_rel D D' dr Rel C1 p u0 Bks k u u' pre pre' t' t v v' rs rs' ->
         forall ihsG ownR, rec_arg_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t v v' ->
         ⟦ih v' of t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ ownR ->
         List.length ihsG = List.length (shape_leaves (rv_leaves D) 0 t) ->
         List.length rs = leaves_in_count D' t' (shape_leaves (rv_leaves D) 0 t) ->
         rec_result_rel D dr Rel k u u' pre pre' t v v' ihsG ownR ->
         rec_result_rel D dr Rel k u u' pre pre' t v v' (merge_leaves D' t' (shape_leaves (rv_leaves D) 0 t) ihsG rs) rs') /\
      (forall pre pre' t' t v c v' c' rs rs',
         cross_result_app_rel D D' dr Rel C1 p u0 Bks k u u' pre pre' t' t v c v' c' rs rs' ->
         forall ihsG, rec_arg_app_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t v c v' c' ->
         List.length ihsG = List.length (shape_leaves (rv_leaves D) 0 t) ->
         List.length rs = leaves_in_count D' t' (shape_leaves (rv_leaves D) 0 t) ->
         rec_result_app_rel D dr Rel k u u' pre pre' t v c v' c' ihsG
           (List.map (fun i => d_ihfn C1 Bks p u0 t i v') (List.seq 0 (List.length (shape_leaves (rv_leaves D) 0 t)))) ->
         rec_result_app_rel D dr Rel k u u' pre pre' t v c v' c' (merge_leaves D' t' (shape_leaves (rv_leaves D) 0 t) ihsG rs) rs') /\
      (forall pre pre' gs' gs vs vs' w ihs, cross_fields_rel D D' dr Rel C1 p u0 Bks k u u' pre pre' gs' gs vs vs' w ihs ->
         forall ihsG ownR, con_args_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' gs vs vs' ->
         ⟦ihs vs' of gs under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ ownR ->
         List.length ihsG = cargs_nrec D gs ->
         rec_results_rel D dr Rel k u u' pre pre' gs vs vs' ihsG ownR ->
         rec_results_rel D dr Rel k u u' pre pre' gs vs vs' (merge_ihs D' D gs' gs ihsG w) ihs).
    Proof.
      apply (cross_result_rel_mut_ind_all D D' dr Rel C1 p u0 Bks
               (fun k u u' pre pre' t' t v v' rs rs' _ =>
                  forall ihsG ownR, rec_arg_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t v v' ->
                  ⟦ih v' of t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ ownR ->
                  List.length ihsG = List.length (shape_leaves (rv_leaves D) 0 t) ->
                  List.length rs = leaves_in_count D' t' (shape_leaves (rv_leaves D) 0 t) ->
                  rec_result_rel D dr Rel k u u' pre pre' t v v' ihsG ownR ->
                  rec_result_rel D dr Rel k u u' pre pre' t v v' (merge_leaves D' t' (shape_leaves (rv_leaves D) 0 t) ihsG rs) rs')
               (fun k u u' pre pre' t' t v c v' c' rs rs' _ =>
                  forall ihsG, rec_arg_app_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t v c v' c' ->
                  List.length ihsG = List.length (shape_leaves (rv_leaves D) 0 t) ->
                  List.length rs = leaves_in_count D' t' (shape_leaves (rv_leaves D) 0 t) ->
                  rec_result_app_rel D dr Rel k u u' pre pre' t v c v' c' ihsG
                    (List.map (fun i => d_ihfn C1 Bks p u0 t i v') (List.seq 0 (List.length (shape_leaves (rv_leaves D) 0 t)))) ->
                  rec_result_app_rel D dr Rel k u u' pre pre' t v c v' c'
                    (merge_leaves D' t' (shape_leaves (rv_leaves D) 0 t) ihsG rs) rs')
               (fun k u u' pre pre' gs' gs vs vs' w ihs _ =>
                  forall ihsG ownR, con_args_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' gs vs vs' ->
                  ⟦ihs vs' of gs under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ ownR ->
                  List.length ihsG = cargs_nrec D gs ->
                  rec_results_rel D dr Rel k u u' pre pre' gs vs vs' ihsG ownR ->
                  rec_results_rel D dr Rel k u u' pre pre' gs vs vs' (merge_ihs D' D gs' gs ihsG w) ihs)).
      - (** At members with a block: the container's result. *)
        intros k u u' pre pre' j' Mj' Ps' j Mj Ps bs bs' v v' ih ih' HMj' Hrv' HMj Hrv Ebs Ebs' Hrr ihsG ownR _ _ Lg _ _.
        cbn [shape_leaves] in Lg |- *; rewrite (rv_leaves_not_rview _ _ _ HMj Hrv) in Lg |- *.
        destruct ihsG as [| g [| ? ?]]; cbn in Lg; try lia.
        cbn [merge_leaves leaf_in]; rewrite HMj', Hrv'; cbn [negb List.hd List.tl merge_leaves].
        eapply rec_result_self; [ exact HMj | exact Hrv | exact Ebs | exact Ebs' | exact Hrr ].
      - (** At record views: their fields'. *)
        intros k u u' pre pre' j' Mj' qr Is' fl c' gs' Ps' j Mj Is0 c gs Ps v v' ws ws' rs rs' HMj' Hh' Hcs' HMj Hh Hcs Ew Ew' Hcf IH
          ihsG ownR Ha Eown Lg _ Hrel.
        destruct (rec_result_rview_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs Hrel) as (ws0 & ws0' & Ew0 & Ew0' & Hrr).
        pose proof (functional_eval_projs _ _ _ _ Ew0 Ew) as ->; pose proof (functional_eval_projs _ _ _ _ Ew0' Ew') as ->.
        destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ha) as (bq & bq' & _ & _ & _ & _ & Hff).
        destruct (ind_rel_rview_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs Hff) as (ws1 & ws1' & Ew1 & Ew1' & _ & Hca).
        pose proof (functional_eval_projs _ _ _ _ Ew1 Ew) as ->; pose proof (functional_eval_projs _ _ _ _ Ew1' Ew') as ->.
        inversion Eown; subst;
          match goal with H1 : ind_lookup _ _ p = Some ?D1 |- _ => rewrite Hl in H1; injection H1 as <- end;
          match goal with H1 : ind_member D j = Some ?M1 |- _ => rewrite HMj in H1; injection H1 as <- end;
          [ exfalso; eapply not_rview_record; eassumption |].
        match goal with H2 : im_head Mj = _, H3 : im_cons Mj = _ |- _ =>
          rewrite Hh in H2; injection H2 as <- <- <-; rewrite Hcs in H3; injection H3 as <- <- end.
        match goal with E1 : ⟦projs fl of v' ⟧ _ ⍮ _ ↘ ?w1 |- _ => pose proof (functional_eval_projs _ _ _ _ E1 Ew') as -> end.
        destruct (rview_struct_con _ _ _ HrsD _ _ _ _ _ HMj Hh) as (gs0 & Hcs0 & Hlen).
        rewrite Hcs in Hcs0; injection Hcs0 as _ <-.
        destruct (rview_struct_con _ _ _ HrsQ _ _ _ _ _ HMj' Hh') as (gs1 & Hcs1 & Hlen').
        rewrite Hcs' in Hcs1; injection Hcs1 as _ <-.
        destruct (rview_struct_record _ _ _ HrsQ _ _ _ _ _ HMj' Hh') as [R HR].
        pose proof (rview_record_nodup _ _ _ _ _ _ HR) as Hnd.
        assert (Lg' : List.length ihsG = cargs_nrec D gs)
          by (rewrite Lg; exact (length_shape_leaves_rview _ _ _ _ _ _ _ _ _ 0 Hlc HMj Hh Hcs (eq_sym Hlen))).
        match goal with E1 : ⟦ihs ws' of gs under p u0 Bks ⟧ _ ⍮ _ ⍮ C1 ↘ ownR |- _ =>
          pose proof (IH ihsG ownR Hca E1 Lg' Hrr) as Hm end.
        cbn [shape_leaves]; rewrite (Hlc _ _ _ _ _ _ _ HMj Hh Hcs), merge_leaves_map_wk.
        rewrite (merge_leaves_fields D D' j' Mj' qr Is' fl c' gs' Ps' gs HMj' Hh' Hcs' Hnd (eq_sym Hlen') (eq_sym Hlen) ihsG rs Lg').
        eapply rec_result_rview; [ exact HMj | exact Hh | exact Hcs | exact Ew | exact Ew' | exact Hm ].
      - (** At a domain: pointwise. *)
        intros k u u' pre pre' B' t' B t v v' rs rs' Hf IH ihsG ownR Ha Eown Lg Lrs Hrel.
        inversion Eown; subst.
        match goal with H1 : ind_lookup _ _ p = Some ?D1 |- _ => rewrite Hl in H1; injection H1 as <- end.
        cbn [shape_leaves] in Lg, Lrs |- *.
        rewrite merge_leaves_map_pi, (merge_leaves_ext _ _ _ (shape_leaves (rv_leaves D) 0 t) _ _ (leaf_in_shape_leaves _ _ _ _ _ _)).
        rewrite List.length_map, (length_shape_leaves _ _ _ 0) in Lg.
        rewrite leaves_in_count_map_pi, (leaves_in_count_shift D D' t' t) in Lrs.
        apply rec_result_pi; intros c c' Hcc.
        inversion Ha as [| ? ? ? ? ? ? ? ? ? Hfa]; subst.
        inversion Hrel as [| | ? ? ? ? ? ? ? ? Hfr]; subst.
        exact (IH c c' Hcc ihsG (Hfa c c' Hcc) Lg Lrs (Hfr c c' Hcc)).
      - (** The arguments applied. *)
        intros k u u' pre pre' t' t v c v' c' rs rs' fc fc' rcs rcs' Ef Ef' F1 F2 Hcr IH ihsG Ha Lg Lrs Happ.
        inversion Happ as [? ? ? ? ? ? ? ? ? fcG fcG' rcsG rcsG' EfG EfG' F1G F2G HrG]; subst.
        pose proof (functional_eval_app _ _ _ _ EfG Ef) as ->; pose proof (functional_eval_app _ _ _ _ EfG' Ef') as ->.
        inversion Ha as [? ? ? ? ? ? ? ? ? ? ? ? Er Er' Ha0]; subst.
        pose proof (functional_eval_app _ _ _ _ Er Ef) as ->; pose proof (functional_eval_app _ _ _ _ Er' Ef') as ->.
        destruct (proj1 (proj2 (proj2 self_elim_all)) _ _ _ _ _ _ _ _ Ha0) as (rsL & rsR & _ & ER & _).
        assert (LR : List.length rsR = List.length (shape_leaves (rv_leaves D) 0 t))
          by exact (proj1 (proj2 eval_ih_length_all) _ _ _ _ _ _ _ ER D Hl Hlc).
        pose proof (ihfn_apps_inv _ _ _ _ _ _ _ _ _ _ _ Ef' ER LR F2G) as ->.
        pose proof (List.Forall2_length F1G) as LG; pose proof (List.Forall2_length F1) as LC.
        econstructor; [ exact Ef | exact Ef' | | exact F2 |].
        + apply merge_leaves_Forall2; [ exact F1G | exact F1 | exact Lg | exact Lrs ].
        + apply (IH rcsG rsR); [ exact Ha0 | exact ER | lia | lia | exact HrG ].
      - (** No argument. *)
        intros k u u' pre pre' ihsG ownR _ _ _ Hrel; inversion Hrel; subst; cbn; constructor.
      - (** Non-recursive in both. *)
        intros k u u' pre pre' A' A gs' gs v v' vs vs' w ihs Hcf IH ihsG ownR Ha Eown Lg Hrel.
        inversion Ha; subst; inversion Eown; subst; inversion Hrel; subst.
        cbn [merge_ihs]; apply rec_results_arg; eapply IH; eassumption.
      - (** Nested through: the group's own. *)
        intros k u u' pre pre' A' t gs' gs v v' vs vs' w rs' ihs Ers Hcf IH ihsG ownR Ha Eown Lg Hrel.
        inversion Ha; subst.
        match goal with Hr : rec_arg_rel _ _ _ _ _ _ _ _ _ _ _ t v v', Hc : con_args_rel _ _ _ _ _ _ _ _ _ _ _ gs vs vs' |- _ =>
          rename Hr into Hra, Hc into Ha' end.
        inversion Eown; subst.
        match goal with E1 : ⟦ih v' of t under p u0 Bks ⟧ _ ⍮ _ ⍮ C1 ↘ _, E2 : ⟦ihs vs' of gs under p u0 Bks ⟧ _ ⍮ _ ⍮ C1 ↘ _ |- _ =>
          rename E1 into Er1, E2 into Eo2 end.
        pose proof (functional_eval_ih _ _ _ _ _ _ _ _ Er1 Ers) as Efe; subst.
        assert (L0 : List.length rs' = List.length (shape_leaves (rv_leaves D) 0 t))
          by exact (proj1 (proj2 eval_ih_length_all) _ _ _ _ _ _ _ Ers D Hl Hlc).
        inversion Hrel; subst.
        match goal with Hr : rec_result_rel _ _ _ _ _ _ _ _ t v v' ?a ?b, Hr2 : rec_results_rel _ _ _ _ _ _ _ _ gs vs vs' ?c ?d,
                        L1 : List.length ?a = _, L2 : List.length ?b = _, E : ?b ++ ?d = rs' ++ _ |- _ =>
          destruct (app_split_eq _ _ _ _ E ltac:(lia)) as [-> ->];
          cbn [merge_ihs]; rewrite firstn_app_exact, skipn_app_exact by exact L1;
          rewrite List.length_app, L1 in Lg; cbn [cargs_nrec] in Lg;
          apply rec_results_rec; [ exact L1 | exact L0 | exact Hr | eapply IH; [ exact Ha' | exact Eo2 | lia | exact Hr2 ] ]
        end.
      - (** Recursive in both. *)
        intros k u u' pre pre' t' t gs' gs v v' vs vs' rs rs' w ihs Lrs Lrs' Hcr IHr Hcf IHf ihsG ownR Ha Eown Lg Hrel.
        inversion Ha; subst.
        match goal with Hr : rec_arg_rel _ _ _ _ _ _ _ _ _ _ _ t v v', Hc : con_args_rel _ _ _ _ _ _ _ _ _ _ _ gs vs vs' |- _ =>
          rename Hr into Hra, Hc into Ha' end.
        inversion Eown; subst.
        match goal with E1 : ⟦ih v' of t under p u0 Bks ⟧ _ ⍮ _ ⍮ C1 ↘ ?r1, E2 : ⟦ihs vs' of gs under p u0 Bks ⟧ _ ⍮ _ ⍮ C1 ↘ _ |- _ =>
          rename E1 into Er1, E2 into Eo2;
          assert (L0 : List.length r1 = List.length (shape_leaves (rv_leaves D) 0 t))
            by exact (proj1 (proj2 eval_ih_length_all) _ _ _ _ _ _ _ Er1 D Hl Hlc) end.
        inversion Hrel; subst.
        match goal with Hr : rec_result_rel _ _ _ _ _ _ _ _ t v v' ?a ?b, Hr2 : rec_results_rel _ _ _ _ _ _ _ _ gs vs vs' ?c ?d,
                        L1 : List.length ?a = _, L2 : List.length ?b = _, E : ?b ++ ?d = _ ++ _ |- _ =>
          destruct (app_split_eq _ _ _ _ E ltac:(lia)) as [-> ->];
          cbn [merge_ihs]; rewrite firstn_app_exact, skipn_app_exact by exact L1;
          rewrite skipn_app_exact by exact Lrs; rewrite merge_leaves_app_tail by exact Lrs;
          rewrite List.length_app, L1 in Lg; cbn [cargs_nrec] in Lg;
          apply rec_results_rec; [ rewrite length_merge_leaves by exact L1; reflexivity | exact Lrs'
                                 | exact (IHr _ _ Hra Er1 L1 Lrs Hr) | eapply IHf; [ exact Ha' | exact Eo2 | lia | exact Hr2 ] ]
        end.
    Qed.

    (** The cross relation at the arguments' bases is that at [u0]: the
        group's motives at the parameters' values at [u0] ([Elim.rel_move]). *)
    Lemma cross_rebase_all : forall k u u',
      (forall pre pre' t' t v v' rs rs', cross_result_rel D D' dr Rel C1 p u0 Bks k u u' pre pre' t' t v v' rs rs' ->
         rec_arg_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t v v' ->
         cross_result_rel D D' dr Rel C1 p u0 Bks k u0 u0 pre pre' t' t v v' rs rs') /\
      (forall pre pre' t' t v c v' c' rs rs', cross_result_app_rel D D' dr Rel C1 p u0 Bks k u u' pre pre' t' t v c v' c' rs rs' ->
         rec_arg_app_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t v c v' c' ->
         cross_result_app_rel D D' dr Rel C1 p u0 Bks k u0 u0 pre pre' t' t v c v' c' rs rs') /\
      (forall pre pre' gs' gs vs vs' w ihs, cross_fields_rel D D' dr Rel C1 p u0 Bks k u u' pre pre' gs' gs vs vs' w ihs ->
         con_args_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' gs vs vs' ->
         cross_fields_rel D D' dr Rel C1 p u0 Bks k u0 u0 pre pre' gs' gs vs vs' w ihs).
    Proof.
      apply (cross_result_rel_mut_ind_all D D' dr Rel C1 p u0 Bks
               (fun k u u' pre pre' t' t v v' rs rs' _ => rec_arg_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t v v' ->
                  cross_result_rel D D' dr Rel C1 p u0 Bks k u0 u0 pre pre' t' t v v' rs rs')
               (fun k u u' pre pre' t' t v c v' c' rs rs' _ => rec_arg_app_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t v c v' c' ->
                  cross_result_app_rel D D' dr Rel C1 p u0 Bks k u0 u0 pre pre' t' t v c v' c' rs rs')
               (fun k u u' pre pre' gs' gs vs vs' w ihs _ => con_args_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' gs vs vs' ->
                  cross_fields_rel D D' dr Rel C1 p u0 Bks k u0 u0 pre pre' gs' gs vs vs' w ihs)).
      - (** At members with a block: the motive at [u0]'s parameters. *)
        intros k u u' pre pre' j' Mj' Ps' j Mj Ps bs bs' v v' ih ih' HMj' Hrv' HMj Hrv Ebs Ebs' Hrr Ha.
        destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ha) as (bs0 & bs0' & Eb0 & Eb0' & [o Eo Ho] & [o' Eo' Ho'] & Hir).
        pose proof (functional_eval_exps' _ _ _ _ Eb0 Ebs) as ->; pose proof (functional_eval_exps' _ _ _ _ Eb0' Ebs') as ->.
        unfold ntele_rel in Ho, Ho'; rewrite HMj in Ho, Ho'.
        eapply cross_result_self; [ exact HMj' | exact Hrv' | exact HMj | exact Hrv | exact Eo | exact Eo' |].
        exact (proj1 (self_motive_move j Mj _ _ _ _ _ _ _ _ HMj Hrv Hir
                        (nparams_rel_sym p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HMj _ _ Ho)
                        (nparams_rel_sym p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HMj _ _ Ho') ih ih') Hrr).
      - (** At record views: their fields'. *)
        intros k u u' pre pre' j' Mj' qr Is' fl c' gs' Ps' j Mj Is0 c gs Ps v v' ws ws' rs rs' HMj' Hh' Hcs' HMj Hh Hcs Ew Ew' Hcf IH Ha.
        destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ha) as (bq & bq' & _ & _ & _ & _ & Hff).
        destruct (ind_rel_rview_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs Hff) as (ws1 & ws1' & Ew1 & Ew1' & _ & Hca).
        pose proof (functional_eval_projs _ _ _ _ Ew1 Ew) as ->; pose proof (functional_eval_projs _ _ _ _ Ew1' Ew') as ->.
        eapply cross_result_rview; [ exact HMj' | exact Hh' | exact Hcs' | exact HMj | exact Hh | exact Hcs | exact Ew | exact Ew'
                                   | exact (IH Hca) ].
      - (** At a domain: at related arguments. *)
        intros k u u' pre pre' B' t' B t v v' rs rs' Hf IH Ha.
        inversion Ha as [| ? ? ? ? ? ? ? ? ? Hfa]; subst.
        constructor; intros c0 c0' Hc0; exact (IH c0 c0' Hc0 (Hfa c0 c0' Hc0)).
      - intros k u u' pre pre' t' t v c v' c' rs rs' fc fc' rcs rcs' Ef Ef' F1 F2 Hcr IH Ha.
        inversion Ha; subst.
        match goal with Er : $| v & c | gc_deps ⍮ gc_stack ↘ ?r, Er' : $| v' & c' | gc_deps ⍮ gc_stack ↘ ?r',
                        Ha' : rec_arg_rel _ _ _ _ _ _ _ _ _ _ _ _ ?r ?r' |- _ =>
          pose proof (functional_eval_app _ _ _ _ Er Ef) as ->; pose proof (functional_eval_app _ _ _ _ Er' Ef') as ->;
          econstructor; [ exact Ef | exact Ef' | exact F1 | exact F2 | exact (IH Ha') ]
        end.
      - intros; constructor.
      - intros * Hcf IH Ha; inversion Ha; subst; constructor; apply IH; assumption.
      - intros * Ers Hcf IH Ha; inversion Ha; subst; econstructor; [ exact Ers | apply IH; assumption ].
      - intros * L1 L2 Hcr IHr Hcf IHf Ha; inversion Ha; subst.
        constructor; [ exact L1 | exact L2 | apply IHr; assumption | apply IHf; assumption ].
    Qed.
  End Merge.

  (** *** The Wrapped Branch's Context at Related Arguments

      Arguments of two constructors of the view's member [v], related
      canonically, the container's results [w] on the left, merged into
      the group's ([merge_ihs]), related to the group's results [ihs'] on
      the right: related at the recursive results of the wrapped branch's
      context, the group's at the paths the container has ([sel_ihs]).
      Each entry is the type of the group's result along its path, whose
      relation is the result's ([leaf_walk_sem]). *)
  Section WrapCv.
    Variable (D' : ind_decl).
    Variable (v : nat) (Mv : imember) (c : String.string) (gs' gs : list carg).
    Hypotheses (HMv : ind_member D v = Some Mv) (Hcon : ind_con Mv c = Some gs) (Hk : cargs_kinds gs' gs)
      (HrvMv : im_is_rview Mv = false).
    Let nn := im_nn Mv.
    Let na := List.length gs.
    Let T := List.rev (im_nparams Mv).
    Let As := blocks_motives Bks.
    Let τU := sb_of_list Id Us.
    Let Cs := tele_sub (cargs_ctx p D Mv gs) (sb_qn nn τU).
    Let Ns := tele_sub (im_nparams Mv) τU.
    Let HB := valid_blocks_bctx _ _ _ _ _ _ HBk _ _ _ _ HMv Hcon.
    #[local] Abbreviation WB f := (f VP p D HP HPD Γ Us Bks iA HΓ HUl HUs HBk D' v Mv c gs' gs HMv HrvMv Hcon Hk).
    #[local] Abbreviation EBr f := (EM f v Mv c gs HMv Hcon HB HrvMv).

    Lemma cv_wrap_ihs : forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
        forall X X' vs vs' ihsM w ihs',
        tele_rel (nr v) T X X' ->
        tele_rel (ar v X c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') ->
        con_args_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 X X' gs vs vs' ->
        rec_results_rel D dr Rel v u0 u0 X X' gs vs vs' (merge_ihs D' D gs' gs ihsM w) ihs' ->
        List.length ihsM = cargs_nrec D gs -> List.length w = cargs_nin D D' gs' gs ->
        per_gargs (List.rev (Cs ++ Ns)) B1 B2 (X ++ vs) (X' ++ vs') ->
        forall kk, kk <= na ->
        per_gargs (List.rev (wrap_ihs_ctx D D' nn As Us na nil 0 (List.firstn kk gs') (List.firstn kk gs)))
          (env_args B1 (X ++ vs)) (env_args B2 (X' ++ vs'))
          (List.firstn (cargs_nin D D' (List.firstn kk gs') (List.firstn kk gs)) w)
          (sel_ihs D' D (List.firstn kk gs') (List.firstn kk gs) (List.firstn (cargs_nrec D (List.firstn kk gs)) ihs')).
    Proof.
      intros B1 B2 HB1 HB2 * HX Har Hia Hir LM Lw Hci.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      assert (HB12 : RΓ B1 B2) by (etransitivity; [ exact HB1 | symmetry; exact HB2 ]).
      destruct (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia) as [Lv Lv'].
      destruct (rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Li Li'].
      pose proof HX as HX0; rewrite tele_rel_iff in HX0; destruct HX0 as (LX & LX' & _).
      unfold T in LX, LX'; rewrite List.length_rev, length_im_nparams in LX, LX'.
      pose proof (nparams_rel_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HMv _ _ HX) as HXX.
      pose proof (cargs_kinds_length _ _ Hk) as Lgs.
      induction kk as [| kk IH]; intros Hkk; [ cbn; constructor |].
      destruct (nth_error_lt_some' gs kk ltac:(unfold na in Hkk; lia)) as [g Hg].
      destruct (nth_error_lt_some' gs' kk ltac:(unfold na in Hkk; lia)) as [g' Hg'].
      assert (Heq0 : gs = List.firstn kk gs ++ g :: List.skipn (S kk) gs)
        by (rewrite <- (skipn_nth_cons' _ _ _ Hg), List.firstn_skipn; reflexivity).
      assert (Heq0' : gs' = List.firstn kk gs' ++ g' :: List.skipn (S kk) gs')
        by (rewrite <- (skipn_nth_cons' _ _ _ Hg'), List.firstn_skipn; reflexivity).
      assert (Lk : List.length (List.firstn kk gs) = kk) by (rewrite List.length_firstn; unfold na in Hkk; lia).
      assert (Lk' : List.length (List.firstn kk gs') = kk) by (rewrite List.length_firstn; unfold na in Hkk; lia).
      pose proof (IH ltac:(lia)) as IHk.
      rewrite (firstn_S_snoc _ _ _ Hg), (firstn_S_snoc _ _ _ Hg').
      set (G1 := List.firstn kk gs) in *; set (G1' := List.firstn kk gs') in *.
      set (G2 := List.skipn (S kk) gs) in *; set (G2' := List.skipn (S kk) gs') in *.
      assert (Hkk' : cargs_kinds (G1' ++ g' :: G2') (G1 ++ g :: G2)) by (rewrite <- Heq0, <- Heq0'; exact Hk).
      destruct (cargs_kinds_app_inv G1' G1 (g' :: G2') (g :: G2) ltac:(lia) Hkk') as [Hk1 Hkg].
      rewrite wrap_ihs_ctx_app, cargs_nin_app, sel_ihs_app by exact Hk1.
      rewrite List.firstn_firstn, Nat.min_l by (rewrite cargs_nrec_app'; lia).
      destruct g' as [A' | t'], g as [A | t]; cbn in Hkg; try contradiction; cbn [wrap_ihs_ctx List.app cargs_nin cargs_nrec sel_ihs].
      all: rewrite ?Nat.add_0_r, ?List.app_nil_r; try exact IHk.
      (** An argument recursive in both: its entries, one per leaf path the
          container has. *)
      clear Hkg IH.
      set (ls0 := shape_leaves (rv_leaves D) 0 t) in *.
      set (ls := shape_leaves (rv_leaves D) (pat_nargs (cargs_pat G1) + nn) t) in *.
      set (nin1 := cargs_nin D D' G1' G1) in *.
      destruct (rec_results_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ Hir G1 t G2 Heq0)
        as (x & x' & rs & rs' & ih1 & ih1' & ih2 & ih2' & Hx & Hx' & Eih & Eih' & Lih1 & Lih1' & Lrs & Lrs' & Hrih).
      pose proof (merge_ihs_app D' D G1' G1 (ca_rec t' :: G2') (ca_rec t :: G2) ihsM w Hk1) as Hm.
      rewrite <- Heq0, <- Heq0', Eih in Hm; cbn [merge_ihs] in Hm; fold ls0 nin1 in Hm.
      assert (LM1 : List.length (merge_ihs D' D G1' G1 (List.firstn (cargs_nrec D G1) ihsM) w) = cargs_nrec D G1)
        by (apply length_merge_ihs; [ exact Hk1 | rewrite List.length_firstn, LM, Heq0, cargs_nrec_app'; cbn [cargs_nrec]; lia ]).
      destruct (app_split_eq _ _ _ _ Hm ltac:(lia)) as [_ Hm2].
      assert (LML : List.length (merge_leaves D' t' ls0 (List.firstn (List.length ls0) (List.skipn (cargs_nrec D G1) ihsM))
                                  (List.skipn nin1 w)) = List.length ls0)
        by (apply length_merge_leaves; rewrite List.length_firstn, List.length_skipn, LM, Heq0, cargs_nrec_app'; cbn [cargs_nrec];
            fold ls0; lia).
      destruct (app_split_eq _ _ _ _ Hm2 ltac:(fold ls0 in Lrs; lia)) as [Ers _].
      clear Hm Hm2 LM1 LML.
      assert (Eih1' : List.firstn (cargs_nrec D G1) ihs' = ih1') by (rewrite Eih', <- Lih1'; apply firstn_app_exact; reflexivity).
      fold ls0 in Lrs, Lrs'.
      assert (Ers' : List.firstn (List.length ls0) (List.skipn (cargs_nrec D G1) (List.firstn (cargs_nrec D (G1 ++ ca_rec t :: nil)) ihs'))
                     = rs').
      { rewrite Eih', cargs_nrec_app'; cbn [cargs_nrec]; fold ls0; rewrite Nat.add_0_r, <- Lih1', List.app_assoc,
          firstn_app_exact by (rewrite List.length_app; lia).
        rewrite skipn_app_exact by reflexivity; apply List.firstn_all2; lia. }
      assert (Hfa : forall (l : list domain) n m, List.firstn (n + m) l = List.firstn n l ++ List.firstn m (List.skipn n l)).
      { induction l as [| a l IHl]; intros [| n] m; cbn; try reflexivity; [ destruct m; reflexivity | rewrite IHl; reflexivity ]. }
      rewrite Eih1', Ers', Hfa, List.rev_app_distr.
      assert (Lw1 : nin1 + leaves_in_count D' t' ls0 <= List.length w)
        by (rewrite Lw, Heq0', Heq0, cargs_nin_app by exact Hk1; cbn [cargs_nin]; fold nin1 ls0; lia).
      rewrite Eih1' in IHk.
      apply per_gargs_app_intro; [ rewrite List.length_rev, length_wrap_ihs_ctx, List.length_firstn by exact Hk1; fold nin1; lia
                                 | exact IHk |].
      clear Hfa.
      assert (Emap : List.map (leaf_in D' t') ls = List.map (leaf_in D' t') ls0) by apply leaf_in_shape_leaves.
      assert (Lls : List.length ls = List.length ls0) by apply length_shape_leaves.
      rewrite (leaves_in_count_ext _ _ ls0 ls (eq_sym Emap)), (sel_leaves_vals_ext _ _ ls0 ls _ (eq_sym Emap)).
      set (wt := List.skipn nin1 w) in *.
      assert (Lwt : leaves_in_count D' t' ls <= List.length wt)
        by (unfold wt; rewrite List.length_skipn, (leaves_in_count_ext _ _ ls ls0 Emap); lia).
      assert (LG : List.length G1' = List.length G1) by lia.
      pose proof (WB w_valid G1' (ca_rec t' :: G2') G1 (ca_rec t :: G2) Heq0' Heq0 LG) as HW.
      set (W1 := wrap_ihs_ctx D D' nn As Us na nil 0 G1' G1) in *.
      assert (LW1 : List.length W1 = nin1) by (unfold W1, nin1; apply length_wrap_ihs_ctx; exact Hk1).
      fold nn na As in HW; fold W1 in HW.
      set (ihp1 := List.firstn nin1 w) in *; set (ihq1 := sel_ihs D' D G1' G1 ih1') in *.
      assert (Lihp1 : List.length ihp1 = nin1) by (unfold ihp1; rewrite List.length_firstn; lia).
      assert (Lihq1 : List.length ihq1 = nin1) by (unfold ihq1, nin1; apply length_sel_ihs; [ exact Hk1 | exact Lih1' ]).
      assert (Hlsn : forall n, n <= List.length ls ->
                per_gargs (List.rev (wrap_leaves_ctx D' t' nn As Us na G1 nin1 (List.firstn n ls)))
                  (env_args (env_args B1 (X ++ vs)) ihp1) (env_args (env_args B2 (X' ++ vs')) ihq1)
                  (List.firstn (leaves_in_count D' t' (List.firstn n ls)) wt)
                  (sel_leaves_vals D' t' (List.firstn n ls) (List.firstn n rs'))).
      2: { pose proof (Hlsn (List.length ls) (le_n _)) as H; rewrite List.firstn_all in H.
           rewrite (List.firstn_all2 rs') in H by lia; exact H. }
      induction n as [| n IHn]; intros Hn; [ cbn; constructor |].
      destruct (nth_error_lt_some' ls n ltac:(lia)) as [l Hl0].
      destruct (nth_error_lt_some' rs' n ltac:(lia)) as [r2 Hr2].
      pose proof (IHn ltac:(lia)) as IHn'; clear IHn.
      rewrite (firstn_S_snoc _ _ _ Hl0), (firstn_S_snoc _ _ _ Hr2).
      rewrite wrap_leaves_ctx_app, leaves_in_count_app, sel_leaves_vals_snoc by (rewrite !List.length_firstn; lia).
      cbn [wrap_leaves_ctx].
      assert (Hc1 : leaves_in_count D' t' (l :: nil) = if leaf_in D' t' l then 1 else 0)
        by (unfold leaves_in_count; cbn; destruct (leaf_in D' t' l); reflexivity).
      rewrite Hc1; fold (leaves_in_count D' t' (List.firstn n ls)).
      destruct (leaf_in D' t' l) eqn:Hin; cbn [List.app]; [| rewrite Nat.add_0_r, List.app_nil_r; exact IHn' ].
      set (cn := leaves_in_count D' t' (List.firstn n ls)) in *.
      assert (Lcn : cn < List.length wt).
      { assert (Hle : leaves_in_count D' t' (List.firstn (S n) ls) <= leaves_in_count D' t' ls).
        { rewrite <- (List.firstn_skipn (S n) ls) at 2; rewrite leaves_in_count_app; lia. }
        rewrite (firstn_S_snoc _ _ _ Hl0), leaves_in_count_app, Hc1 in Hle; fold cn in Hle; lia. }
      destruct (nth_error_lt_some' wt cn Lcn) as [w1 Hw1].
      rewrite Nat.add_1_r, (firstn_S_snoc _ _ _ Hw1).
      cbn [List.rev].
      set (Te := leaf_ihty As (ι wk_shiftn (cn + nin1 + na + nn)) (cargs_sub (wrap_base Us nn na (cn + nin1)) G1 (vars_from (cn + nin1) na))
                   (a_var (cn + nin1 + (na - 1 - List.length G1))) l).
      set (Er := wrap_leaves_ctx D' t' nn As Us na G1 nin1 (List.firstn n ls) ++ W1).
      assert (LEr : List.length Er = cn + nin1)
        by (unfold Er; rewrite List.length_app, length_wrap_leaves_ctx, LW1; reflexivity).
      assert (ECs : Cs ++ Ns = tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU)
        by (unfold Cs, Ns; rewrite tele_sub_app, length_im_nparams; reflexivity).
      assert (HΔeq : Er ++ cinst Γ p D Mv Us gs = (Er ++ Cs ++ Ns) ++ Γ)
        by (rewrite cinst_eq, ECs, List.app_assoc; reflexivity).
      pose proof (WB w_valid_leaves G1' t' G2' G1 t G2 Heq0' Heq0 LG HW (List.firstn (S n) ls) (List.skipn (S n) ls)
                    (eq_sym (List.firstn_skipn _ _))) as HCtx2.
      rewrite (firstn_S_snoc _ _ _ Hl0), wrap_leaves_ctx_app in HCtx2; cbn [wrap_leaves_ctx] in HCtx2; rewrite Hin in HCtx2.
      rewrite Nat.add_0_r in HCtx2; fold nn na As cn nin1 τU Cs Ns W1 in HCtx2; cbn [List.app] in HCtx2.
      rewrite List.app_assoc in HCtx2; fold Er Te in HCtx2.
      destruct (rel_ctx_wf_ass_inv HCtx2) as [jT HT].
      assert (HCtx : ⊨ Er ++ cinst Γ p D Mv Us gs) by (rewrite HΔeq, <- !List.app_assoc; exact (rel_ctx_wf_tail HCtx2)).
      destruct (rel_ctx_wf_per_ctx_env HCtx) as [RS HRS].
      assert (HRS' : EF (Er ++ Cs ++ Ns) ++ Γ ≈ (Er ++ Cs ++ Ns) ++ Γ ∈ per_ctx_env ↘ RS) by (rewrite <- HΔeq; exact HRS).
      assert (HCtx' : ⊨ (Er ++ Cs ++ Ns) ++ Γ) by (rewrite <- HΔeq; exact HCtx).
      set (ihp := ihp1 ++ List.firstn cn wt); set (ihq := ihq1 ++ sel_leaves_vals D' t' (List.firstn n ls) (List.firstn n rs')).
      assert (Lihp : List.length ihp = cn + nin1) by (unfold ihp; rewrite List.length_app, List.length_firstn; lia).
      assert (Lihq : List.length ihq = cn + nin1)
        by (unfold ihq; rewrite List.length_app, length_sel_leaves_vals by (rewrite !List.length_firstn; lia); fold cn; lia).
      assert (HEp : RS (env_args B1 ((X ++ vs) ++ ihp)) (env_args B2 ((X' ++ vs') ++ ihq))).
      { eapply (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRS' HCtx' HB12);
          [ unfold Cs, Ns; rewrite !List.length_app, !length_tele_sub, length_cargs_ctx, length_im_nparams, LEr, Lihp;
            unfold na, nn, im_nn in *; lia |].
        unfold Er; rewrite (List.rev_app_distr (_ ++ W1) (Cs ++ Ns)), (List.rev_app_distr _ W1).
        apply per_gargs_app_intro;
          [ unfold Cs, Ns; rewrite List.length_rev, !List.length_app, !length_tele_sub, length_cargs_ctx, length_im_nparams;
            unfold na, nn, im_nn in *; lia | exact Hci |].
        unfold ihp, ihq; apply per_gargs_app_intro; [ rewrite List.length_rev, LW1; lia | exact IHk | exact IHn' ]. }
      replace (Er ++ Cs ++ Ns ++ Γ) with ((Er ++ Cs ++ Ns) ++ Γ) in HT by (rewrite <- !List.app_assoc; reflexivity).
      destruct (rel_exp_of_typ_inversion_simple_at HRS' HT _ _ HEp) as (ty & ty' & Et & Et' & [R HR]).
      destruct (per_univ_elem_to_nat _ _ _ _ HR) as [i0 Hi0].
      pose proof Et as EtF; pose proof Et' as EtF'.
      rewrite env_args_app in Et, Et'; unfold ihp, ihq in Et, Et'; rewrite env_args_app in Et, Et'.
      apply (per_gargs_snoc _ _ _ _ _ _ _ _ i0 R);
        [ rewrite List.length_rev, length_wrap_leaves_ctx, List.length_firstn; fold cn; lia | exact IHn'
        | exact (mk_rel_mod_eval _ _ Et Et' Hi0) |].
      clear Et Et'.
      (** The two sides, in the frame of the argument ([leaf_walk_sem]). *)
      assert (Hsplit : forall (Y ws : list domain) w0 (ihq0 : list domain), List.nth_error ws kk = Some w0 -> List.length ws = List.length gs ->
                 (Y ++ ws) ++ ihq0 = Y ++ List.firstn kk ws ++ w0 :: List.skipn (S kk) ws ++ ihq0).
      { intros * Hw0 Lw0.
        pose proof (List.firstn_skipn kk ws) as Hfs; rewrite (skipn_nth_cons' _ _ _ Hw0) in Hfs.
        rewrite <- Hfs at 1; rewrite <- !List.app_assoc; reflexivity. }
      rewrite Lk in Hx, Hx'.
      rewrite (Hsplit X vs x ihp Hx Lv) in EtF, HEp.
      rewrite (Hsplit X' vs' x' ihq Hx' Lv') in EtF', HEp.
      assert (HPS : PER RS) by (eapply per_env_PER; exact HRS).
      assert (HE1 : RS (env_args B1 (X ++ List.firstn kk vs ++ x :: List.skipn (S kk) vs ++ ihp))
                       (env_args B1 (X ++ List.firstn kk vs ++ x :: List.skipn (S kk) vs ++ ihp)))
        by (etransitivity; [ exact HEp | symmetry; exact HEp ]).
      assert (HE2 : RS (env_args B2 (X' ++ List.firstn kk vs' ++ x' :: List.skipn (S kk) vs' ++ ihq))
                       (env_args B2 (X' ++ List.firstn kk vs' ++ x' :: List.skipn (S kk) vs' ++ ihq)))
        by (etransitivity; [ symmetry; exact HEp | exact HEp ]).
      assert (Lf : forall ws : list domain, List.length ws = List.length gs -> List.length (List.firstn kk ws) = List.length G1)
        by (intros; rewrite List.length_firstn; lia).
      assert (Ls : forall ws : list domain, List.length ws = List.length gs -> List.length (List.skipn (S kk) ws) = List.length G2)
        by (intros; unfold G2; rewrite !List.length_skipn; lia).
      assert (Lihp' : List.length ihp = List.length Er) by lia.
      assert (Lihq' : List.length ihq = List.length Er) by lia.
      destruct (EBr side_w G1 t G2 Heq0 Er HCtx RS HRS B1 X (List.firstn kk vs) x (List.skipn (S kk) vs) ihp HB1 LX (Lf _ Lv) (Ls _ Lv)
                  Lihp' HE1) as (wu1 & Hwu1 & HwU1 & Lwu1).
      destruct (EBr side_w G1 t G2 Heq0 Er HCtx RS HRS B2 X' (List.firstn kk vs') x' (List.skipn (S kk) vs') ihq HB2 LX' (Lf _ Lv')
                  (Ls _ Lv') Lihq' HE2) as (wu2 & Hwu2 & HwU2 & Lwu2).
      pose proof (EBr e_vals G1 t G2 Heq0 Er HCtx RS HRS B1 X (List.firstn kk vs) x (List.skipn (S kk) vs) ihp wu1 HB1 LX (Lf _ Lv)
                    (Ls _ Lv) Lihp' HE1 Hwu1 HwU1 Lwu1) as Hv1.
      pose proof (EBr e_vals G1 t G2 Heq0 Er HCtx RS HRS B2 X' (List.firstn kk vs') x' (List.skipn (S kk) vs') ihq wu2 HB2 LX'
                    (Lf _ Lv') (Ls _ Lv') Lihq' HE2 Hwu2 HwU2 Lwu2) as Hv2.
      pose proof (EBr e_frame G1 t G2 Heq0 Er HCtx) as Hf.
      destruct (length_rec_ps D HD v Mv HMv c gs G1 t G2 Hcon Heq0) as (Mj & HMj & _).
      assert (HRS0 : EF (Er ++ tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU) ++ Γ
                       ≈ (Er ++ tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU) ++ Γ ∈ per_ctx_env ↘ RS)
        by (rewrite <- ECs; exact HRS').
      destruct (con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia G1 t G2 Heq0) as (y & y' & Hy & Hy' & Hrr).
      rewrite Lk in Hy, Hy', Hrr, Hrih; rewrite Hx in Hy; injection Hy as <-; rewrite Hx' in Hy'; injection Hy' as <-.
      set (K := List.length (cargs_nonrec G1)).
      assert (Hnv : forall ws, List.length ws = List.length gs -> List.firstn K (nonrec_arg_vals gs ws) = nonrec_arg_vals G1 (List.firstn kk ws)).
      { intros ws Lw0; rewrite Heq0 in Lw0 |- *; rewrite <- Lk; exact (nonrec_arg_vals_firstn _ _ _ Lw0). }
      assert (HKl : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq0, cargs_nonrec_app, List.length_app; lia).
      assert (Hpk : tele_prefix_rel (ar v X c) K (nonrec_arg_vals G1 (List.firstn kk vs)) (nonrec_arg_vals G1 (List.firstn kk vs'))).
      { rewrite <- (Hnv vs Lv), <- (Hnv vs' Lv'); apply tele_prefix_rel_of_full with (T := cargs_nonrec gs); [ exact Har | exact HKl ]. }
      assert (Hl1 : List.nth_error (shape_leaves (rv_leaves D) (im_nn Mv + K + 0) (ptyp_skip 0 t)) n = Some l).
      { replace (im_nn Mv + K + 0) with (pat_nargs (cargs_pat G1) + im_nn Mv); [ exact Hl0 |].
        rewrite pat_nargs_cargs_pat, cargs_strat_nonrec, List.length_rev, List.length_map; fold K; lia. }
      assert (EtT : forall E a, ⟦ Te ⟧ E ↘ a ->
                ⟦ leaf_ihty (blocks_motives Bks) (sb_shift_iter 0 (sb_of_wk (wk_shiftn (List.length Er + List.length gs + im_nn Mv))))
                    (sb_qn 0 (ihs_sub (im_nn Mv) Us (List.length gs) (cargs_pat G1) (List.length Er)))
                    (apps_vars_iter 0 (a_var (List.length Er + List.length gs - 1 - List.length (cargs_pat G1)))) l ⟧ E ↘ a).
      { intros E a Ea; cbn [sb_shift_iter sb_qn apps_vars_iter].
        rewrite (wrap_leaf_ihty_eq D v Mv c gs G1 t G2 l (blocks_motives Bks) Us (List.length Er) Hc (decl_typed_mvc _ _ _ Hdt) HMv
                   (cons_lookup_in _ _ _ Hcon) Heq0 (List.nth_error_In _ _ Hl0)).
        rewrite LEr; exact Ea. }
      pose proof (EM leaf_walk_sem (S (ptyp_mem t)) v Mv c gs G1 t G2 HMv Hcon Heq0 Mj HMj (fun _ => Nat.lt_succ_diag_r _) _ _ _ _ Hf
                    (leaf_term_var _) RS HRS0 X _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hv1 Hv2 HXX HX Hpk 0 nil nil x x' rs rs' (Nat.le_0_l _)
                    eq_refl eq_refl (tele_prefix_rel_nil _) (eval_apps_nil _ _ _) (eval_apps_nil _ _ _)
                    ltac:(rewrite !List.app_nil_r; exact Hrr) ltac:(rewrite !List.app_nil_r; exact Hrih)
                    ltac:(rewrite Lrs; reflexivity) ltac:(rewrite Lrs'; reflexivity) n l Hl1 ty ty' i0 R (EtT _ _ EtF) (EtT _ _ EtF') Hi0)
        as HRR.
      rewrite (List.nth_error_nth _ _ _ Hr2) in HRR.
      destruct (nth_error_lt_some' ls0 n ltac:(lia)) as [l0 Hl00].
      assert (Hin0 : leaf_in D' t' l0 = true).
      { pose proof (f_equal (fun m => List.nth_error m n) Emap) as E; cbn beta in E.
        rewrite !List.nth_error_map, Hl0, Hl00 in E; cbn in E; injection E as E; rewrite <- E; exact Hin. }
      rewrite Ers, (merge_leaves_nth_in D' t' ls0 _ wt n l0 Hl00 Hin0) in HRR
        by (rewrite List.length_firstn, List.length_skipn, LM, Heq0, cargs_nrec_app'; cbn [cargs_nrec]; fold ls0; lia).
      assert (Ecn : leaves_in_count D' t' (List.firstn n ls0) = cn).
      { unfold cn; apply leaves_in_count_ext; rewrite <- !List.firstn_map, Emap; reflexivity. }
      rewrite Ecn, (List.nth_error_nth _ _ _ Hw1) in HRR; exact HRR.
    Qed.

    (** The environments of the wrapped branch's context at such arguments
        and results. *)
    Lemma cv_wrap : forall B1 B2, RΓ B1 C1 -> RΓ B2 C1 ->
        forall X X' vs vs' ihsM w ihs',
        tele_rel (nr v) T X X' ->
        tele_rel (ar v X c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') ->
        con_args_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 X X' gs vs vs' ->
        rec_results_rel D dr Rel v u0 u0 X X' gs vs vs' (merge_ihs D' D gs' gs ihsM w) ihs' ->
        List.length ihsM = cargs_nrec D gs -> List.length w = cargs_nin D D' gs' gs ->
        forall RB, EF wrap_bctx p D D' Mv gs' gs As Us ++ Γ ≈ wrap_bctx p D D' Mv gs' gs As Us ++ Γ ∈ per_ctx_env ↘ RB ->
        RB (env_args B1 (X ++ vs ++ w)) (env_args B2 (X' ++ vs' ++ sel_ihs D' D gs' gs ihs')).
    Proof.
      intros B1 B2 HB1 HB2 * HX Har Hia Hir LM Lw RB HRB.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      assert (HB12 : RΓ B1 B2) by (etransitivity; [ exact HB1 | symmetry; exact HB2 ]).
      destruct (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia) as [Lv Lv'].
      destruct (rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ Hir) as [Li Li'].
      pose proof HX as HX0; rewrite tele_rel_iff in HX0; destruct HX0 as (LX & LX' & _).
      unfold T in LX, LX'; rewrite List.length_rev, length_im_nparams in LX, LX'.
      pose proof (cargs_kinds_length _ _ Hk) as Lgs.
      destruct (us_class VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HUC B1 HB1) as (u1 & Hu1 & H10).
      destruct (us_class VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HUC B2 HB2) as (u2 & Hu2 & H20).
      pose proof (EB closed_args_gargs v Mv c gs HMv Hcon X X' vs vs' HX Har Hia (List.length gs) (le_n _)) as Hcg.
      rewrite List.firstn_all, !List.firstn_all2 in Hcg by lia.
      assert (HKa : tele_ass ((cargs_ctx p D Mv gs ++ im_nparams Mv) ++ ind_uparams D))
        by (rewrite <- List.app_assoc; fold (im_params D Mv); apply List.Forall_app; split;
            [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc v Mv HMv) ]).
      assert (HK : ⊨ (cargs_ctx p D Mv gs ++ im_nparams Mv) ++ ind_uparams D)
        by (rewrite <- List.app_assoc; fold (im_params D Mv); exact (vg_cargs_sem p D Hvg Hcv v Mv c gs HMv Hcon)).
      pose proof (ihs_pre_sem p D Γ Us Bks Mv gs HB nil gs eq_refl) as HC0; cbn [ihs_ctx_aux List.app] in HC0; rewrite cinst_eq in HC0.
      pose proof (EB cv_gen _ HKa HK HC0 B1 B2 u1 u2 HB12 Hu1 Hu2 H10 H20 _ _ Hcg
                    ltac:(rewrite !List.length_app, length_cargs_ctx, length_im_nparams; lia)) as Hci.
      rewrite tele_sub_app, length_im_nparams in Hci; fold τU nn Cs Ns in Hci.
      pose proof (cv_wrap_ihs B1 B2 HB1 HB2 _ _ _ _ _ _ _ HX Har Hia Hir LM Lw Hci na (le_n _)) as Hih.
      unfold na in Hih; rewrite (List.firstn_all gs), (List.firstn_all2 gs'), !List.firstn_all2 in Hih by lia.
      pose proof (WB valid_wrap_bctx) as HW.
      unfold As in HRB; rewrite (WB w_ctx_eq) in HW, HRB.
      fold nn na As τU Cs Ns in HW, HRB.
      set (Wc := wrap_ihs_ctx D D' nn As Us na nil 0 gs' gs) in HW, HRB, Hih.
      replace (Wc ++ Cs ++ Ns ++ Γ) with ((Wc ++ Cs ++ Ns) ++ Γ) in HW, HRB by (rewrite <- !List.app_assoc; reflexivity).
      rewrite (List.app_assoc X), (List.app_assoc X').
      eapply (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRB HW HB12).
      - unfold Wc; rewrite !List.length_app, length_wrap_ihs_ctx by exact Hk.
        unfold Cs, Ns; rewrite !length_tele_sub, length_cargs_ctx, length_im_nparams; unfold nn, na, im_nn in *; lia.
      - rewrite List.rev_app_distr; apply per_gargs_app_intro;
          [ unfold Cs, Ns; rewrite List.length_rev, !List.length_app, !length_tele_sub, length_cargs_ctx, length_im_nparams;
            unfold nn, im_nn in *; lia | exact Hci | exact Hih ].
    Qed.

    (** *** The Group's Recursive Results in the Wrapped Branch's Context

        The group's eliminator along the leaf paths of the arguments, as the
        wrapped branch's instance has it ([wrap_br_sub]), at an environment
        of the wrapped branch's context over [C1] whose arguments are
        related to [vs']: related to the group's own recursive results at
        [vs'].  The frame of each argument is that of the branch's context
        extended by the wrapped branch's results ([Elim.e_frame]); the walk
        is [Iota.leaf_ihs_vals]. *)
    Let Ew := wrap_ihs_ctx D D' nn As Us na nil 0 gs' gs.
    Let Rw := List.length Ew.
    Let nw := Rw + na + nn.
    Let Uw := List.map (fun U => U[wk_shiftn nw]ʷ) Us.
    Let Bw := blocks_wk Bks (wk_shiftn nw).
    Let Aw := vars_from Rw na.
    Let σw := wrap_base Us nn na Rw.
    #[local] Abbreviation LV f := (f VP p D HP HPD Γ (Some p) Us Bks iA HΓ (or_introl eq_refl) HUl HUs
       (valid_blocks_len _ _ _ _ _ _ HBk) (valid_blocks_nm _ _ _ _ _ _ HBk) HMall HAv (valid_blocks_names _ _ _ _ _ _ HBk)
       (valid_blocks_bctx _ _ _ _ _ _ HBk) (valid_blocks_arity _ _ _ _ _ _ HBk) (valid_blocks_branch _ _ _ _ _ _ HBk)
       RΓ RU HRΓ HRU C1 u0 HC11 HUC).

    (** The group's eliminator along the leaf paths of a recursive argument,
        as the wrapped branch's instance has it, is that of the argument's
        frame in the branch's context extended by the wrapped results. *)
    Lemma wrap_leaf_ihs_eq : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
        List.map (leaf_ih p D (Some p) (List.map (fun U => U[sb_of_wk (wk_shiftn nw)]) Us) (blocks_sub Bks (sb_of_wk (wk_shiftn nw)))
                    (ihs_sub nn Us na (cargs_pat gs1) Rw) (a_var (Rw + na - 1 - List.length (cargs_pat gs1))))
          (shape_leaves (rv_leaves D) (nn + List.length (cargs_nonrec gs1)) t)
        = List.map (leaf_ih p D (Some p) Uw Bw (cargs_sub σw gs1 Aw) (a_var (Rw + (na - 1 - List.length gs1))))
            (shape_leaves (rv_leaves D) (pat_nargs (cargs_pat gs1) + nn) t).
    Proof.
      intros * Heq.
      assert (Hlt : List.length gs1 < na) by (unfold na; rewrite Heq, List.length_app; cbn; lia).
      rewrite map_sub_of_wk, blocks_sub_of_wk, length_cargs_pat; fold Uw Bw.
      replace (Rw + na - 1 - List.length gs1) with (Rw + (na - 1 - List.length gs1)) by lia.
      rewrite pat_nargs_cargs_pat, cargs_strat_nonrec, List.length_rev, List.length_map,
        (Nat.add_comm (List.length (cargs_nonrec gs1)) nn).
      apply List.map_ext_in; intros l Hinl; rewrite (Nat.add_comm nn) in Hinl.
      pose proof (member_closed_recs _ _ (decl_closed_members _ Hc _ _ HMv) _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq) as Hst.
      rewrite cargs_strat_nonrec, List.length_rev, List.length_map in Hst.
      assert (Hsl : leaf_scoped (List.length (cargs_nonrec gs1) + nn + ind_nu D) l).
      { assert (Hst' : ptyp_scoped (List.length (cargs_nonrec gs1) + nn + ind_nu D) t)
          by (replace (List.length (cargs_nonrec gs1) + nn + ind_nu D) with (List.length (cargs_nonrec gs1) + im_np D Mv)
                by (unfold im_np, nn, im_nn; lia); exact Hst).
        pose proof (shape_leaves_scoped (rv_leaves D) (ind_nu D) t (List.length (cargs_nonrec gs1) + nn) (rv_leaves_scoped D Hc) Hst')
          as HF.
        rewrite List.Forall_forall in HF; exact (HF l Hinl). }
      assert (Hml : leaf_mvc l).
      { destruct (decl_mvc_members _ (decl_typed_mvc _ _ _ Hdt) _ _ HMv) as (_ & _ & Hmg).
        pose proof (Hmg _ _ (cons_lookup_in _ _ _ Hcon)) as Hm; rewrite Heq in Hm; apply List.Forall_app in Hm as [_ Hm].
        apply List.Forall_cons_iff in Hm as [[HmB HmP] _].
        pose proof (shape_leaves_mvc (rv_leaves D) t (List.length (cargs_nonrec gs1) + nn) (rv_leaves_mvc _ (decl_typed_mvc _ _ _ Hdt))
                      HmB HmP) as HM.
        rewrite List.Forall_forall in HM; exact (HM _ Hinl). }
      eapply leaf_ih_mvc_agree; [ exact Hsl | exact Hml |].
      intros y _; apply ihs_sub_wrap; lia.
    Qed.

    (** What the group's eliminator in the wrapped context gives at the
        arguments [rest] after [gs1]: the values of the instance's recursive
        results at the wrapped context's environment, against the group's
        own at [vs']. *)
    #[warnings="-cannot-define-projection"]
    Record wrap_ihs_vals_out (X X' vs vs' w : list domain) (gs1 rest : list carg) : Prop := mk_wrap_ihs_vals_out
      { (** The values of the instance's recursive results *)
        wrap_ihs_vals_terms : list domain
        (** The group's own recursive results at [vs'] *)
      ; wrap_ihs_vals_own : list domain
        (** The instance's, at the wrapped context's environment *)
      ; wrap_ihs_vals_eval_terms :
          ⟦ elim_ihs p D (Some p) Uw Bw (cargs_sub σw gs1 Aw) (pat_nargs (cargs_pat gs1) + nn) rest (List.skipn (List.length gs1) Aw) ⟧*
            gc_deps ⍮ gc_stack ⍮ env_args C1 (X ++ vs ++ w) ↘ wrap_ihs_vals_terms
        (** The group's own, at [C1] *)
      ; wrap_ihs_vals_eval_own : ⟦ihs List.skipn (List.length gs1) vs' of rest under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ wrap_ihs_vals_own
        (** Related as recursive results *)
      ; wrap_ihs_vals_related :
          rec_results_rel D dr Rel v u0 u0 (X ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
            (X' ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs')) rest
            (List.skipn (List.length gs1) vs) (List.skipn (List.length gs1) vs') wrap_ihs_vals_terms wrap_ihs_vals_own }.

    Lemma wrap_ihs_vals : forall RS, EF Ew ++ cinst Γ p D Mv Us gs ≈ Ew ++ cinst Γ p D Mv Us gs ∈ per_ctx_env ↘ RS ->
        forall X X' vs vs' w, RS (env_args C1 (X ++ vs ++ w)) (env_args C1 (X ++ vs ++ w)) ->
        List.length X = nn -> List.length w = Rw ->
        tele_rel (nr v) T X X' ->
        tele_rel (ar v X c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') ->
        con_args_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 X X' gs vs vs' ->
        con_args_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 X X gs vs vs ->
        forall rest gs1, gs = gs1 ++ rest -> wrap_ihs_vals_out X X' vs vs' w gs1 rest.
    Proof.
      intros RS HRS X X' vs vs' w HE LX Lw HX Har Hia Hia0.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      destruct (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia) as [Lv Lv'].
      pose proof (nparams_rel_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HMv _ _ HX) as HXX.
      assert (HCtx : ⊨ Ew ++ cinst Γ p D Mv Us gs) by (rewrite cinst_eq, tele_sub_app, length_im_nparams, <- List.app_assoc; exact (WB f_HE)).
      assert (HRS0 : EF (Ew ++ tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU) ++ Γ
                       ≈ (Ew ++ tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU) ++ Γ ∈ per_ctx_env ↘ RS)
        by (rewrite cinst_eq in HRS; rewrite <- List.app_assoc; exact HRS).
      induction rest as [| g rest IH]; intros gs1 Heq.
      - assert (E1 : List.skipn (List.length gs1) vs = nil) by (apply List.skipn_all2; rewrite Lv, Heq, List.app_nil_r; lia).
        assert (E2 : List.skipn (List.length gs1) vs' = nil) by (apply List.skipn_all2; rewrite Lv', Heq, List.app_nil_r; lia).
        apply (mk_wrap_ihs_vals_out _ _ _ _ _ _ _ nil nil); rewrite ?E1, ?E2; [ cbn; constructor | constructor | constructor ].
      - enough (H : exists ihsE own,
                   ⟦ elim_ihs p D (Some p) Uw Bw (cargs_sub σw gs1 Aw) (pat_nargs (cargs_pat gs1) + nn) (g :: rest)
                       (List.skipn (List.length gs1) Aw) ⟧* gc_deps ⍮ gc_stack ⍮ env_args C1 (X ++ vs ++ w) ↘ ihsE /\
                   ⟦ihs List.skipn (List.length gs1) vs' of g :: rest under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ own /\
                   rec_results_rel D dr Rel v u0 u0 (X ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
                     (X' ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs')) (g :: rest)
                     (List.skipn (List.length gs1) vs) (List.skipn (List.length gs1) vs') ihsE own)
          by (destruct H as (ihsE & own & H1 & H2 & H3); exact (mk_wrap_ihs_vals_out _ _ _ _ _ _ _ ihsE own H1 H2 H3)).
        assert (Hlt : List.length gs1 < List.length vs) by (rewrite Lv, Heq, List.length_app; cbn; lia).
        destruct (nth_error_lt_some vs _ Hlt) as [x Hx].
        destruct (nth_error_lt_some vs' (List.length gs1) ltac:(lia)) as [x' Hx'].
        assert (Lf : List.length (List.firstn (List.length gs1) vs) = List.length gs1) by (rewrite List.length_firstn; lia).
        assert (Lf' : List.length (List.firstn (List.length gs1) vs') = List.length gs1) by (rewrite List.length_firstn; lia).
        assert (Heq' : gs = (gs1 ++ g :: nil) ++ rest) by (rewrite <- List.app_assoc; exact Heq).
        destruct (IH _ Heq') as [ihc ihe Ec Ee Hr].
        rewrite List.length_app in Ec, Ee, Hr; cbn [List.length] in Ec, Ee, Hr; rewrite Nat.add_1_r in Ec, Ee, Hr.
        rewrite (firstn_S_nth _ _ _ Hx), (firstn_S_nth _ _ _ Hx'), !nonrec_arg_vals_app in Hr by assumption.
        assert (HAw : List.skipn (List.length gs1) Aw = a_var (Rw + (na - 1 - List.length gs1)) :: List.skipn (S (List.length gs1)) Aw)
          by exact (WB f_avar gs1 g rest Heq).
        rewrite (skipn_nth_cons _ _ _ Hx), (skipn_nth_cons _ _ _ Hx'), HAw.
        rewrite cargs_pat_snoc in Ec.
        destruct g as [B0 | t].
        + assert (Hsa : cargs_sub σw (gs1 ++ ca_arg B0 :: nil) Aw = (cargs_sub σw gs1 Aw ,, a_var (Rw + (na - 1 - List.length gs1))))
            by exact (WB f_sub_arg gs1 B0 rest Heq).
          rewrite Hsa in Ec; cbn [nonrec_arg_vals pat_nargs] in Hr, Ec; rewrite !List.app_assoc in Hr.
          exists ihc, ihe; split; [ cbn [elim_ihs]; exact Ec | split; [ constructor; exact Ee | constructor; exact Hr ] ].
        + assert (Hsr : cargs_sub σw (gs1 ++ ca_rec t :: nil) Aw = cargs_sub σw gs1 Aw) by exact (WB f_sub_rec gs1 t rest Heq).
          rewrite Hsr in Ec; cbn [nonrec_arg_vals pat_nargs] in Hr, Ec; rewrite !List.app_nil_r in Hr.
          destruct (length_rec_ps D HD v Mv HMv c gs gs1 t rest Hcon Heq) as (Mj & HMj & _).
          set (nv := nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) in *.
          set (nv' := nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs')) in *.
          destruct (con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia gs1 t rest Heq) as (y & y' & Hy & Hy' & Hsh).
          rewrite Hx in Hy; injection Hy as <-; rewrite Hx' in Hy'; injection Hy' as <-.
          destruct (con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia0 gs1 t rest Heq) as (z & z' & Hz & Hz' & Hsh0).
          rewrite Hx in Hz, Hz'; injection Hz as <-; injection Hz' as <-.
          assert (HKl : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
            by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
          assert (Hpk : tele_prefix_rel (ar v X c) (List.length (cargs_nonrec gs1)) nv nv).
          { assert (Hpk0 : tele_prefix_rel (ar v X c) (List.length (cargs_nonrec gs1)) nv nv').
            { rewrite <- (List.firstn_skipn (List.length gs1) vs), <- (List.firstn_skipn (List.length gs1) vs') in Har.
              exact (nonrec_prefix_gen _ gs gs1 (ca_rec t :: rest) _ _ _ _ Heq Lf Lf' Har). }
            exact (args_rel_pre_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI v Mv HMv X c gs HXX Hcon _ _ _ HKl Hpk0). }
          (** The argument's frame in the wrapped context, at [C1]. *)
          set (L := X ++ List.firstn (List.length gs1) vs ++ x :: List.skipn (S (List.length gs1)) vs ++ w).
          assert (EL : X ++ vs ++ w = L).
          { unfold L; rewrite <- (List.firstn_skipn (List.length gs1) vs) at 1; rewrite (skipn_nth_cons _ _ _ Hx).
            rewrite <- !List.app_assoc; reflexivity. }
          assert (Ls : List.length (List.skipn (S (List.length gs1)) vs) = List.length rest)
            by (rewrite List.length_skipn, Lv, Heq, List.length_app; cbn; lia).
          rewrite EL in HE |- *.
          destruct (EBr side_w gs1 t rest Heq Ew HCtx RS HRS C1 X (List.firstn (List.length gs1) vs) x
                      (List.skipn (S (List.length gs1)) vs) w HC11 LX Lf Ls Lw HE) as (wu & Hwu & HwU & Lwu).
          pose proof (EBr e_vals gs1 t rest Heq Ew HCtx RS HRS C1 X (List.firstn (List.length gs1) vs) x
                        (List.skipn (S (List.length gs1)) vs) w wu HC11 LX Lf Ls Lw HE Hwu HwU Lwu) as Hvals.
          pose proof (EBr e_frame gs1 t rest Heq Ew HCtx) as Hf.
          assert (Hlink : iota_arg_link p D Γ C1 u0 v (X ++ nv ++ nil) (ptyp_skip 0 t) x (apps_vars_iter 0 (a_var (Rw + na - 1 - List.length (cargs_pat gs1))))
                            (L ++ nil)).
          { intros Δ RΔ zs _ _ _; cbn [apps_vars_iter ptyp_skip]; exists (X ++ nv ++ nil), x; split; [| rewrite !List.app_nil_r; exact Hsh0 ].
            rewrite List.app_nil_r; cbn [exp_wk wk_shiftn].
            assert (LL : List.length L = (Rw + na + nn))
              by (unfold L; rewrite !List.length_app; cbn [List.length]; rewrite List.length_app, Lf, LX, Lw, List.length_skipn, Lv;
                  unfold na; lia).
            pose proof (eval_var_args C1 (L ++ zs) (Rw + na - 1 - List.length (cargs_pat gs1) + List.length zs)
                          ltac:(rewrite List.length_app, LL, length_cargs_pat; unfold na in *; lia)) as HV.
            replace (List.nth _ (L ++ zs) d_true) with x in HV; [ exact HV |].
            rewrite List.length_app, LL, length_cargs_pat, List.app_nth1 by (rewrite LL; unfold na in *; lia).
            unfold L; rewrite List.app_nth2 by lia; rewrite List.app_nth2 by lia.
            rewrite LX, Lf.
            replace (Rw + na + nn + List.length zs - 1 - (Rw + na - 1 - List.length gs1 + List.length zs) - nn - List.length gs1)
              with 0 by (unfold na in *; lia).
            reflexivity. }
          destruct (LV leaf_ihs_vals (S (ptyp_mem t)) v Mv c gs gs1 t rest HMv Hcon Heq Mj HMj (fun _ => Nat.lt_succ_diag_r _)
                      _ _ _ _ Hf RS HRS0 _ wu X nv x X nv Hvals HXX Hpk 0 nil nil x x' (X' ++ nv' ++ nil)
                      (Nat.le_0_l _) eq_refl (tele_prefix_rel_nil _) ltac:(cbn [ptyp_skip]; rewrite !List.app_nil_r; exact Hsh) Hlink)
            as [rs' rs Ers' Ers Hrs].
          cbn [ptyp_skip sb_shift_iter sb_qn apps_vars_iter] in Ers, Ers', Hrs.
          rewrite Nat.add_0_r in Ers'.
          change (List.length Ew) with Rw in Ers'; change (List.length gs) with na in Ers'; change (im_nn Mv) with nn in Ers'.
          change (Rw + na + nn) with nw in Ers'; rewrite (wrap_leaf_ihs_eq gs1 t rest Heq) in Ers'; fold L in Ers'.
          rewrite List.app_nil_r in Ers'; clear Hlink Hvals Hf Hwu.
          exists (rs' ++ ihc), (rs ++ ihe); split; [| split ].
          * cbn [elim_ihs]; apply eval_exps_app; [ exact Ers' | rewrite <- EL; exact Ec ].
          * constructor; [ exact Ers | exact Ee ].
          * apply rec_results_rec; [| | rewrite !List.app_nil_r in Hrs; exact Hrs | exact Hr ].
            -- rewrite (eval_exps_length _ _ _ Ers'), List.length_map; apply length_shape_leaves.
            -- exact (proj1 (proj2 eval_ih_length_all) _ _ _ _ _ _ _ Ers D Hl Hlc).
    Qed.

    (** *** A Wrapped Branch against the Group's Branch

        The wrapped branch of the constructor [c] at an environment over
        [C1] of the container's arguments and results, against the group's
        branch at [C1] at related arguments: related values, at the motive.
        The wrapped branch is the group's at the instance [wrap_br_sub]
        ([gsub_wrap_br]), whose value is the group's branch's environment
        at the group's results merged with the container's
        ([wrap_ihs_vals], [eval_wrap_ihs], [cross_merge_all]). *)
    Variable (bv : eblock).
    Hypotheses (Hbv : List.nth_error Bks v = Some bv) (HrsQ : rview_struct_ok gc_deps gc_stack D')
      (Hcnt : cargs_nin D D' gs' gs = cargs_nrec D' gs').

    Lemma wrap_br_sub_eq : ViewBranch.wrap_br_sub p D D' Us Bks Mv gs' gs
        = sb_of_list (sb_of_wk (wk_shiftn nw)) (vars_from (Rw + na) nn ++ Aw ++ wrap_ihs D' D gs' gs (elim_ihs p D (Some p) Uw Bw σw nn gs Aw) 0 Rw).
    Proof.
      assert (HR : cargs_nrec D' gs' = Rw) by (rewrite <- Hcnt; symmetry; exact (WB f_R)).
      assert (Hna : List.length gs' = na) by exact (cargs_kinds_length _ _ Hk).
      unfold ViewBranch.wrap_br_sub; cbv zeta; rewrite HR, Hna; change (im_nn Mv) with nn.
      replace (nn + na + Rw) with nw by (unfold nw; lia).
      reflexivity.
    Qed.

    (** What a wrapped branch [Ba] moved by [wrap_br_sub] gives against the
        group's branch [Ba], at the container's arguments [vs] and results
        [w] and the group's [vs'] and [ihs] of the constructor
        [d_con hd k c]. *)
    #[warnings="-cannot-define-projection"]
    Record wrap_branch_out (Ba : exp) (bs bs' vs vs' w ihs : list domain) (hd : qname) (k : nat) : Prop := mk_wrap_branch_out
      { (** The wrapped branch's value *)
        wrap_branch_val : domain
        (** The group's branch's value *)
      ; wrap_branch_val' : domain
        (** The wrapped branch, at the container's arguments and results *)
      ; wrap_branch_eval :
          ⟦ Ba[ViewBranch.wrap_br_sub p D D' Us Bks Mv gs' gs] ⟧ env_args C1 (List.skipn (im_unu D Mv) bs ++ vs ++ w) ↘ wrap_branch_val
        (** The group's branch, at the group's *)
      ; wrap_branch_eval' : ⟦ Ba ⟧ env_args C1 (List.skipn (im_unu D Mv) bs' ++ vs' ++ ihs) ↘ wrap_branch_val'
        (** Related at the motive *)
      ; wrap_branch_related : Rel v (List.skipn (im_unu D Mv) bs) (d_con hd k c (bs ++ vs)) (List.skipn (im_unu D Mv) bs')
          (d_con hd k c (bs' ++ vs')) wrap_branch_val wrap_branch_val'
        (** The wrapped branch moved by a substitution into [C1]'s class:
            related to the group's branch's value *)
      ; wrap_branch_moved : forall Γ' RΓ' σ0 ρ0, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ0 ≈ σ0 : Γ -> RΓ' ρ0 ρ0 ->
          ⟦ σ0 ⟧s ρ0 ↘ C1 ->
          exists r0, ⟦ Ba[ViewBranch.wrap_br_sub p D D' Us Bks Mv gs' gs][sb_qn (im_nn Mv + List.length gs' + cargs_nrec D' gs') σ0] ⟧
                       env_args ρ0 (List.skipn (im_unu D Mv) bs ++ vs ++ w) ↘ r0 /\
            Rel v (List.skipn (im_unu D Mv) bs) (d_con hd k c (bs ++ vs)) (List.skipn (im_unu D Mv) bs') (d_con hd k c (bs' ++ vs'))
              r0 wrap_branch_val' }.

    Lemma wrap_branch_rel : forall na0 Ba, brs_lookup (eb_brs bv) c = Some (na0, Ba) ->
        forall u u' bs bs' vs vs' w ihs hd k,
        G v u u' (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs') (d_con hd k c (bs ++ vs)) (d_con hd k c (bs' ++ vs')) ->
        cross_fields_rel D D' dr Rel C1 p u0 Bks v u u' (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs') gs' gs vs vs' w ihs ->
        wrap_branch_out Ba bs bs' vs vs' w ihs hd k.
    Proof.
      intros na0 Ba HBa * Hm Hcr.
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
      destruct (cross_fields_rel_vs_len D D' dr Rel C1 p u0 Bks _ _ _ _ _ _ _ _ _ _ _ Hcr) as [Lv Lv'].
      pose proof (cross_fields_rel_w_len D D' dr Rel C1 p u0 Bks _ _ _ _ _ _ _ _ _ _ _ Hcr) as Lw.
      assert (LwR : List.length w = Rw) by (rewrite Lw; exact (eq_sym (WB f_R))).
      destruct (ind_rel_con_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm HMv HrvMv Hcon Lv Lv') as [Lbs Lbs'].
      destruct (ind_rel_con_inv p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hm HMv HrvMv Lbs)
        as (gs0 & bs1 & vs1 & Ez & _ & HX & Hcon0 & Lbs1 & _ & _ & _ & Hia).
      rewrite Hcon in Hcon0; injection Hcon0 as <-; injection Ez as Ez.
      destruct (app_split_eq _ _ _ _ Ez ltac:(congruence)) as [<- <-].
      pose proof (ind_rel_rebase p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ u0 u0 _ _ _ _ Had Had Had Hm) as Hm0.
      destruct (ind_rel_con_inv p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 HMv HrvMv Lbs)
        as (gs0 & bs2 & vs2 & Ez0 & _ & _ & Hcon0 & Lbs2 & _ & _ & Har0 & Hia0).
      rewrite Hcon in Hcon0; injection Hcon0 as <-; injection Ez0 as Ez0.
      destruct (app_split_eq _ _ _ _ Ez0 ltac:(congruence)) as [<- <-].
      pose proof (proj1 (ind_rel_trans_all p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (okr_at D u0 nr)) _ _ _ _ _ _ _ Hm0 _ _ _ _
                    (proj1 (ind_rel_sym_all p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (okr_at D u0 nr)) _ _ _ _ _ _ _ Hm0)) as Hm00.
      destruct (ind_rel_con_inv p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hm00 HMv HrvMv Lbs)
        as (gs0 & bs3 & vs3 & Ez1 & _ & _ & Hcon0 & Lbs3 & _ & _ & _ & Hia00).
      rewrite Hcon in Hcon0; injection Hcon0 as <-; injection Ez1 as Ez1.
      destruct (app_split_eq _ _ _ _ Ez1 ltac:(congruence)) as [<- <-].
      pose proof (proj2 (proj2 (cross_rebase_all D' HrsQ v u u')) _ _ _ _ _ _ _ _ Hcr Hia) as Hcr0.
      set (X := List.skipn (im_unu D Mv) bs) in *; set (X' := List.skipn (im_unu D Mv) bs') in *.
      assert (LX : List.length X = nn) by (unfold X; rewrite List.length_skipn; unfold nn; lia).
      clear Ez Ez0 Ez1 Lbs1 Lbs2 Lbs3.
      (** The group's own results at both sides, merged with the
          container's: the wrapped branch's context's environment. *)
      destruct (proj1 (proj2 self_elim_all) _ _ _ _ _ _ _ _ Hia0) as (ihsL & ihsR & EL & ER & HLR).
      destruct (rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ HLR) as [LL LR].
      pose proof (proj2 (proj2 (cross_merge_all D' HrsQ v u0 u0)) _ _ _ _ _ _ _ _ Hcr0 ihsL ihsR Hia0 ER LL HLR) as Hm1.
      pose proof (WB valid_wrap_bctx) as HWE.
      destruct (rel_ctx_wf_per_ctx_env HWE) as [RW HRW].
      assert (HPW : PER RW) by (eapply per_env_PER; exact HRW).
      pose proof (cv_wrap C1 C1 HC11 HC11 X X' vs vs' ihsL w ihs HX Har0 Hia0 Hm1 LL Lw RW HRW) as Hcw.
      set (Eb := env_args C1 (X ++ vs ++ w)) in *.
      assert (HEb : RW Eb Eb) by (etransitivity; [ exact Hcw | symmetry; exact Hcw ]).
      assert (HRS : EF Ew ++ cinst Γ p D Mv Us gs ≈ Ew ++ cinst Γ p D Mv Us gs ∈ per_ctx_env ↘ RW).
      { pose proof HRW as H; rewrite (WB w_ctx_eq) in H.
        rewrite cinst_eq, tele_sub_app, length_im_nparams, <- List.app_assoc; exact H. }
      (** The values of the group's recursive results in the wrapped
          context, merged with the container's. *)
      destruct (wrap_ihs_vals RW HRS X X' vs vs' w HEb LX LwR HX Har0 Hia0 Hia00 gs nil eq_refl) as [ihsE own EE Eown HE].
      cbn [List.length List.firstn List.skipn nonrec_arg_vals cargs_sub cargs_pat pat_nargs] in EE, Eown, HE.
      rewrite !List.app_nil_r in HE.
      assert (own = ihsR) as -> by (eapply functional_eval_ihs; eassumption).
      destruct (rec_results_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ HE) as [LE _].
      pose proof (proj2 (proj2 (cross_merge_all D' HrsQ v u0 u0)) _ _ _ _ _ _ _ _ Hcr0 ihsE ihsR Hia0 ER LE HE) as Hrr.
      set (ihsT := merge_ihs D' D gs' gs ihsE w) in *.
      assert (LXvw : List.length (X ++ vs ++ w) = nw) by (rewrite !List.length_app, LX, Lv, LwR; unfold nw, na; lia).
      assert (Hτe : ⟦ ViewBranch.wrap_br_sub p D D' Us Bks Mv gs' gs ⟧s Eb ↘ env_args C1 (X ++ vs ++ ihsT)).
      { rewrite wrap_br_sub_eq; apply eval_sb_of_list.
        - pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn (List.length (X ++ vs ++ w))) Eb (wk_mono_shiftn _)) as H.
          unfold Eb in H; rewrite eval_wk_shiftn_args, LXvw in H; exact H.
        - apply eval_exps_app; [| apply eval_exps_app ].
          + pose proof (eval_vars_from_args X C1 (vs ++ w)) as H; rewrite List.length_app, Lv, LwR, LX in H.
            replace (Rw + na) with (List.length gs + Rw) by (unfold na; lia); exact H.
          + pose proof (eval_vars_from_args vs (env_args C1 X) w) as H; unfold Aw, Eb; rewrite env_args_app; rewrite Lv, LwR in H;
              exact H.
          + unfold ihsT, Eb; rewrite List.app_assoc, <- LwR.
            replace (merge_ihs D' D gs' gs ihsE w) with (merge_ihs D' D gs' gs ihsE (List.skipn 0 w)) by reflexivity.
            apply eval_wrap_ihs; [ exact Hk | exact (eq_trans (eq_sym (eval_exps_length _ _ _ EE)) LE) | rewrite <- List.app_assoc; exact EE | lia ]. }
      clear EE Eown Hcw.
      (** The wrapped branch, the group's at the instance, against the
          group's branch at the group's arguments. *)
      pose proof (valid_blocks_branch _ _ _ _ _ _ HBk _ _ _ _ _ _ _ HMv Hbv Hcon (brs_lookup_in _ _ _ _ HBa)) as HBv.
      destruct (exp_inst_link _ _ _ _ _ _ _ _ _ HBv HRW (gsub_valid (WB gsub_wrap_br Hcnt)) HEb Hτe) as (m & n0 & Em & En0 & Hmn).
      destruct (rel_ctx_wf_per_ctx_env HB) as [RB HRB].
      assert (HPB : PER RB) by (eapply per_env_PER; exact HRB).
      pose proof (EBr cv_bctx_elem C1 C1 HC11 HC11 u0 u0 hd k bs bs' vs vs' ihsT ihs Hm0 Hrr RB HRB) as HEB.
      destruct (rel_exp_under_ctx_simple_at HRB HBv _ _ HEB) as (n1 & r' & En1 & Er' & Hnr).
      assert (n1 = n0) as -> by (eapply functional_eval_exp; eassumption).
      destruct (presup_rel_exp_under_ctx HBv) as [iT HT].
      assert (HEτ : RB (env_args C1 (X ++ vs ++ ihsT)) (env_args C1 (X ++ vs ++ ihsT)))
        by (etransitivity; [ exact HEB | symmetry; exact HEB ]).
      assert (Eq1 : per_head (elim_bty p D v Mv c gs (eb_motive bv) Us) (elim_bty p D v Mv c gs (eb_motive bv) Us)
                      (env_args C1 (X ++ vs ++ ihsT)) (env_args C1 (X ++ vs ++ ihsT))
                    <~> per_head (elim_bty p D v Mv c gs (eb_motive bv) Us) (elim_bty p D v Mv c gs (eb_motive bv) Us)
                      (env_args C1 (X ++ vs ++ ihsT)) (env_args C1 (X' ++ vs' ++ ihs))).
      { apply (per_head_of_typ_resp HRB HT).
        apply rel_chain_cons; [ exact HEτ |]. apply rel_chain_cons; [ exact HEτ |]. apply rel_chain_of_pair; exact HEB. }
      assert (Hfin : forall m0, per_head (elim_bty p D v Mv c gs (eb_motive bv) Us) (elim_bty p D v Mv c gs (eb_motive bv) Us)
                                  (env_args C1 (X ++ vs ++ ihsT)) (env_args C1 (X ++ vs ++ ihsT)) m0 m ->
                       Rel v X (d_con hd k c (bs ++ vs)) X' (d_con hd k c (bs' ++ vs')) m0 r').
      { intros m0 Hm0'.
        apply (proj1 (EBr bty_rel bv Hbv C1 C1 HC11 HC11 u0 u0 hd k bs bs' vs vs' ihsT ihs Hm0 Hrr m0 r')).
        exact (per_head_trans _ _ _ _ _ _ HRB HT HEB _ _ _
                 (proj1 (Eq1 _ _) (per_head_trans _ _ _ _ _ _ HRB HT HEτ _ _ _ Hm0' Hmn)) Hnr). }
      apply (mk_wrap_branch_out _ _ _ _ _ _ _ _ _ m r' Em Er').
      - apply Hfin; exact (per_head_trans _ _ _ _ _ _ HRB HT HEτ _ _ _ Hmn (per_head_sym _ _ _ _ _ _ HRB HT HEτ _ _ Hmn)).
      - (** The wrapped branch moved by a semantic substitution, by an outer
            link in its context. *)
        intros Γ' RΓ' σ0 ρ0 HRΓ' Hσ0 Hρ0 Hev0.
        set (Δ := wrap_bctx p D D' Mv gs' gs (blocks_motives Bks) Us) in *.
        assert (HΔa : tele_ass Δ) by exact (wrap_bctx_ass p D D' v Mv gs' gs _ Us Hc HMv).
        assert (LΔ : List.length (X ++ vs ++ w) = List.length Δ)
          by (unfold Δ; rewrite length_wrap_bctx by exact Hk; rewrite LXvw; unfold nw; rewrite <- LwR, Lw; unfold na, nn; lia).
        assert (Ll : List.length (X ++ vs ++ w) = List.length (List.rev Δ)) by (rewrite List.length_rev; exact LΔ).
        assert (HΔr : ⊨ List.rev (List.rev Δ) ++ Γ) by (rewrite List.rev_involutive; exact HWE).
        assert (HRWr : EF List.rev (List.rev Δ) ++ Γ ≈ List.rev (List.rev Δ) ++ Γ ∈ per_ctx_env ↘ RW)
          by (rewrite List.rev_involutive; exact HRW).
        pose proof (proj2 (rel_gargs _ _ _ _ HRΓ HΔr (List.Forall_rev HΔa) HRWr _ _ _ _ Ll Ll HEb)) as Hg.
        pose proof (WB valid_wrap_br Hcnt bv na0 Ba Hbv HBa) as HBw.
        rewrite (wrap_br_snd _ _ _ _ _ _ _ _ _ _ _ _ Hcon HBa) in HBw.
        destruct (outer_exp_link Δ Γ Γ' RΓ' σ0 ρ0 C1 _ _ _ HΔa HWE HBw HRΓ' Hσ0 Hρ0 Hev0 _ Hg LΔ)
          as (RΔ & F & m1 & n1 & HRΔ & HF & Em1 & Eo1 & Hmn1).
        assert (n1 = m) as -> by (eapply functional_eval_exp; eassumption).
        assert (ERW : RΔ <~> RW) by (eapply per_ctx_env_right_irrel; eassumption).
        apply ERW in HF.
        destruct (presup_rel_exp_under_ctx HBw) as [iW HTw].
        assert (EW : per_head (elim_bty p D v Mv c gs (eb_motive bv) Us)[ViewBranch.wrap_br_sub p D D' Us Bks Mv gs' gs]
                       (elim_bty p D v Mv c gs (eb_motive bv) Us)[ViewBranch.wrap_br_sub p D D' Us Bks Mv gs' gs] F Eb
                     <~> per_head (elim_bty p D v Mv c gs (eb_motive bv) Us)[ViewBranch.wrap_br_sub p D D' Us Bks Mv gs' gs]
                       (elim_bty p D v Mv c gs (eb_motive bv) Us)[ViewBranch.wrap_br_sub p D D' Us Bks Mv gs' gs] Eb Eb).
        { apply (per_head_of_typ_resp HRW HTw).
          apply rel_chain_cons; [ exact HF |]. apply rel_chain_cons; [ exact HEb |]. apply rel_chain_of_pair; exact HEb. }
        exists m1; split.
        + unfold Δ in Em1; rewrite length_wrap_bctx in Em1 by exact Hk.
          replace (im_nn Mv + List.length gs' + cargs_nrec D' gs') with (cargs_nin D D' gs' gs + List.length gs + im_nn Mv)
            by (rewrite (cargs_kinds_length _ _ Hk), Hcnt; lia).
          exact Em1.
        + apply Hfin.
          exact (proj1 (per_head_inst _ _ _ _ _ _ _ _ _ _ HT HRW (gsub_valid (WB gsub_wrap_br Hcnt)) HEb Hτe Hτe m1 m)
                   (proj1 (EW _ _) Hmn1)).
    Qed.
  End WrapCv.
End SelfElim.

Section CrossElim.
  #[local] Set Default Proof Using "All".
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups VP) (HPD : VP p D).
  Let Hvg := valid_groups_valid VP HP p D HPD.
  Let Hcv := containers_valid_of_groups VP HP p D HPD.
  Let HD := valid_group_valid _ _ Hvg.
  Let Hc := valid_group_closed _ _ Hvg.
  Let Hl := valid_group_lookup _ _ Hvg.
  Let Hdt := valid_group_typed _ _ Hvg.
  Let Hass := valid_group_ass _ _ Hvg.
  Let Hlc : leaves_coherent D := leaves_coherent_of_order D (rview_struct_order _ _ _ (grp_tele_ass_rstruct _ Hass)).
  Variable (Γ : ctx) (RΓ : relation env).
  Hypotheses (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HΓ : ⊨ Γ).
  Variable (RU : relation env).
  Hypothesis (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).
  Variable (Us : list exp).
  Hypotheses (HUl : List.length Us = ind_nu D)
    (HUs : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊨ N : T).
  Variable (C1 : env) (u0 : list domain).
  Hypotheses (HC11 : RΓ C1 C1) (HUC : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ C1 ↘ u0).
  Variable (Bks : list eblock) (iA : nat).
  Hypothesis (HBk : valid_blocks p D Γ Us Bks iA).
  Let HBks := valid_blocks_has p D Γ Us Bks iA Hdt HBk.
  Let HMall := valid_blocks_mctx _ _ _ _ _ _ HBk.
  Let HAv := valid_blocks_motive _ _ _ _ _ _ HBk.
  Let nr := canon_nparams_rel D u0.
  Let ar := canon_args_rel D u0.
  Let dr := canon_doms_rel u0.
  Let G := grp_rel p D u0 nr ar dr.
  Let Rel := fun j ns m ns' m' =>
    per_head (List.nth j (blocks_motives Bks) a_True) (List.nth j (blocks_motives Bks) a_True)
      (env_args C1 (ns ++ m :: nil)) (env_args C1 (ns' ++ m' :: nil)).
  #[local] Abbreviation EB f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HC11 HUC).
  #[local] Abbreviation EM f := (EB f C1 HC11 Bks iA HBks HMall HAv).
  #[local] Abbreviation u0_len' := (u0_len D Us HUl C1 u0 HUC).
  #[local] Abbreviation u0_env' := (EB u0_env).
  #[local] Abbreviation u0_gargs' := (EB u0_gargs).
  #[local] Abbreviation Hcp := (vg_canon p D Hvg u0 u0_gargs' u0_len').
  #[local] Abbreviation HnP := (ind_canon_props_np_per _ _ Hcp).
  #[local] Abbreviation HnI := (ind_canon_props_np_iff _ _ Hcp).
  #[local] Abbreviation HaP := (ind_canon_props_arg_per _ _ Hcp).
  #[local] Abbreviation HaI := (ind_canon_props_arg_iff _ _ Hcp).
  #[local] Abbreviation HdP := (ind_canon_props_dom_per _ _ Hcp).
  #[local] Abbreviation HdI := (ind_canon_props_dom_iff _ _ Hcp).
  #[local] Abbreviation Had := (vg_adm p D Hvg u0 u0 u0_gargs' u0_len' u0_gargs').
  (** The group's eliminator against itself at [C1] ([SelfElim]). *)
  #[local] Abbreviation SE f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HC11 HUC Bks iA HBk).
  #[local] Abbreviation self_elim_all := (SE self_elim_all).
  #[local] Abbreviation self_motive_move := (SE self_motive_move).
  #[local] Abbreviation self_ref_target := (SE self_ref_target).

  (** The view [m] of the container's member [k'], its map [vm]. *)
  Variable (qc : qname) (D' : ind_decl) (m : nat) (Mm : imember) (k' : nat) (Is : list exp) (vm : list nat).
  Hypotheses (Hq : ind_lookup gc_deps gc_stack qc = Some D') (HMm : ind_member D m = Some Mm)
    (Hh : im_head Mm = mh_view qc k' Is vm).
  Let HgQ := valid_groups_valid VP HP qc D' (valid_groups_containers VP HP p D m Mm qc k' Is vm D' HPD HMm Hh Hq).
  Let HassQ := valid_group_ass _ _ HgQ.
  Let HlcQ : leaves_coherent D' := leaves_coherent_of_order D' (rview_struct_order _ _ _ (grp_tele_ass_rstruct _ HassQ)).

  (** The container's eliminator: a block for each member with one. *)
  Variable (ρb : env) (VBb : list eblock) (ub : list domain).
  Hypotheses (HbB : forall i' Mi', ind_member D' i' = Some Mi' -> im_is_rview Mi' = false -> exists b, List.nth_error VBb i' = Some b)
    (HnmB : forall i' Mi' b, ind_member D' i' = Some Mi' -> List.nth_error VBb i' = Some b -> eb_nm b = S (im_nn Mi'))
    (HnaB : forall i' Mi' b, ind_member D' i' = Some Mi' -> List.nth_error VBb i' = Some b -> brs_names (im_cons Mi') (eb_brs b))
    (HarB : forall i' Mi' b c gs' n B, ind_member D' i' = Some Mi' -> List.nth_error VBb i' = Some b ->
              ind_con Mi' c = Some gs' -> In (c, n, B) (eb_brs b) -> n = (im_nn Mi' + List.length gs' + cargs_nrec D' gs')%nat).
  Hypothesis (Hmot_x : forall i' Mi' v bb ba u u' ns ns' x x', ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
                List.nth_error vm i' = Some v -> List.nth_error VBb i' = Some bb -> List.nth_error Bks v = Some ba ->
                G v u u' ns ns' x x' ->
                exists a a', ⟦ eb_motive bb ⟧ env_args ρb (ns ++ x :: nil) ↘ a /\
                  ⟦ eb_motive ba ⟧ env_args C1 (ns' ++ x' :: nil) ↘ a' /\
                  DF a ≈ a' ∈ per_univ_elem iA ↘ Rel v ns x ns' x').
  Hypothesis (Hbr_x : forall i' Mi' v Mv bb ba c gs' gs nb na Bb Ba u u' bs bs' vs vs' w ihs hd k,
                ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
                List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
                List.nth_error VBb i' = Some bb -> List.nth_error Bks v = Some ba ->
                ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
                brs_lookup (eb_brs bb) c = Some (nb, Bb) -> brs_lookup (eb_brs ba) c = Some (na, Ba) ->
                G v u u' (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs')
                  (d_con hd k c (bs ++ vs)) (d_con hd k c (bs' ++ vs')) ->
                cross_fields_rel D D' dr Rel C1 p u0 Bks v u u'
                  (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs') gs' gs vs vs' w ihs ->
                exists r r', ⟦ Bb ⟧ env_args ρb (List.skipn (im_unu D Mv) bs ++ vs ++ w) ↘ r /\
                  ⟦ Ba ⟧ env_args C1 (List.skipn (im_unu D Mv) bs' ++ vs' ++ ihs) ↘ r' /\
                  Rel v (List.skipn (im_unu D Mv) bs) (d_con hd k c (bs ++ vs))
                    (List.skipn (im_unu D Mv) bs') (d_con hd k c (bs' ++ vs')) r r').

  (** The members of the container's group and those of the group the
      view's map takes them to. *)
  Lemma cross_member : forall i' j, List.nth_error vm i' = Some j ->
      exists Mi' Mj, ind_member D' i' = Some Mi' /\ view_member p D qc D' vm i' Mi' j Mj.
  Proof.
    intros i' j Hv.
    destruct (grp_tele_ass_view_wrap _ Hass _ _ _ _ _ _ HMm Hh) as (D2 & Hq2 & Hvw).
    rewrite Hq in Hq2; injection Hq2 as <-.
    assert (Hi : i' < List.length (ind_members D')) by (rewrite <- (view_wrap_ok_length _ _ _ Hvw); apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some' _ _ Hi) as [Mi' HMi'].
    destruct (view_agree_members p D m Mm qc k' Is vm D' Hass HMm Hh Hq i' Mi' HMi') as (v & Mv & Hvm).
    pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvm) as Hv'; rewrite Hv in Hv'; injection Hv' as <-.
    exists Mi', Mv; split; [ exact HMi' | exact Hvm ].
  Qed.

  (** What the two eliminators give two related elements of the group's
      member [j] the view's map takes the container's member [i'] to: at
      members with a block, the eliminators' values, related at [Rel]; at
      record views, the recursive results of their fields at the
      projections. *)
  Inductive cross_member_results (i' j : nat) (u u' ns ns' : list domain) (x x' : domain) : Prop :=
  (** Members with a block: the eliminators *)
  | cross_member_elim : forall Mi' Mj r r', ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
      ind_member D j = Some Mj -> im_is_rview Mj = false ->
      ⟦elim x at i' of qc ub VBb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ r -> ⟦elim x' at j of p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ r' ->
      Rel j ns x ns' x' r r' -> cross_member_results i' j u u' ns ns' x x'
  (** Record views of one record and fields: their fields' recursive
      results *)
  | cross_member_rview : forall Mi' Mj qr Is' Is0 fl c' gs' c gs ws ws' rs rs',
      ind_member D' i' = Some Mi' -> im_head Mi' = mh_record qr Is' fl -> im_cons Mi' = (c', gs') :: nil ->
      ind_member D j = Some Mj -> im_head Mj = mh_record qr Is0 fl -> im_cons Mj = (c, gs) :: nil ->
      ⟦projs fl of x ⟧ gc_deps ⍮ gc_stack ↘ ws -> ⟦projs fl of x' ⟧ gc_deps ⍮ gc_stack ↘ ws' ->
      ⟦ihs ws of gs' under qc ub VBb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ rs ->
      ⟦ihs ws' of gs under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ rs' ->
      cross_fields_rel D D' dr Rel C1 p u0 Bks j u u' nil nil gs' gs ws ws' rs rs' ->
      cross_member_results i' j u u' ns ns' x x'.

  (** The two eliminators' recursive results of related constructor
      arguments: the container's, the group's, and their relation. *)
  #[warnings="-cannot-define-projection"]
  Record cross_args_vals (k : nat) (u u' pre pre' : list domain) (gs' gs : list carg) (vs vs' : list domain) : Prop :=
    mk_cross_args_vals
    { (** The container's recursive results *)
      cross_args_vals_container : list domain
      (** The group's recursive results *)
    ; cross_args_vals_group : list domain
      (** The container's, by its eliminator *)
    ; cross_args_vals_eval_container :
        ⟦ihs vs of gs' under qc ub VBb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ cross_args_vals_container
      (** The group's, by its eliminator *)
    ; cross_args_vals_eval_group : ⟦ihs vs' of gs under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ cross_args_vals_group
      (** Related *)
    ; cross_args_vals_related : cross_fields_rel D D' dr Rel C1 p u0 Bks k u u' pre pre' gs' gs vs vs'
        cross_args_vals_container cross_args_vals_group }.

  (** Those of related recursive arguments of shapes [t'] and [t]. *)
  #[warnings="-cannot-define-projection"]
  Record cross_arg_vals (k : nat) (u u' pre pre' : list domain) (t' t : ptyp) (x x' : domain) : Prop :=
    mk_cross_arg_vals
    { (** The container's recursive results *)
      cross_arg_vals_container : list domain
      (** The group's recursive results *)
    ; cross_arg_vals_group : list domain
      (** The container's, by its eliminator *)
    ; cross_arg_vals_eval_container : ⟦ih x of t' under qc ub VBb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ cross_arg_vals_container
      (** The group's, by its eliminator *)
    ; cross_arg_vals_eval_group : ⟦ih x' of t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ cross_arg_vals_group
      (** Related *)
    ; cross_arg_vals_related : cross_result_rel D D' dr Rel C1 p u0 Bks k u u' pre pre' t' t x x'
        cross_arg_vals_container cross_arg_vals_group }.

  (** Those of related recursive arguments applied to related values. *)
  #[warnings="-cannot-define-projection"]
  Record cross_app_vals (k : nat) (u u' pre pre' : list domain) (t' t : ptyp) (f c f' c' : domain) : Prop :=
    mk_cross_app_vals
    { (** The container's argument applied *)
      cross_app_vals_fc : domain
      (** The group's argument applied *)
    ; cross_app_vals_fc' : domain
      (** The container's recursive results there *)
    ; cross_app_vals_container : list domain
      (** The group's recursive results there *)
    ; cross_app_vals_group : list domain
      (** The container's application *)
    ; cross_app_vals_app_container : $| f & c | gc_deps ⍮ gc_stack ↘ cross_app_vals_fc
      (** The group's application *)
    ; cross_app_vals_app_group : $| f' & c' | gc_deps ⍮ gc_stack ↘ cross_app_vals_fc'
      (** The container's, by its eliminator *)
    ; cross_app_vals_eval_container :
        ⟦ih cross_app_vals_fc of t' under qc ub VBb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ cross_app_vals_container
      (** The group's, by its eliminator *)
    ; cross_app_vals_eval_group : ⟦ih cross_app_vals_fc' of t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ cross_app_vals_group
      (** Related *)
    ; cross_app_vals_related : cross_result_rel D D' dr Rel C1 p u0 Bks k u u' pre pre' t' t cross_app_vals_fc cross_app_vals_fc'
        cross_app_vals_container cross_app_vals_group }.

  (** A stuck eliminator of each side at related neutrals, when the two
      read back alike: related at the family. *)
  Lemma cross_neut_elim : forall i' j Mj hd k as1 as2 e e' w w' ns ns', List.nth_error vm i' = Some j ->
      ind_member D j = Some Mj -> im_is_rview Mj = false ->
      G j w w' ns ns' (⇑ (d_ind hd k as1) e) (⇑ (d_ind hd k as2) e') ->
      Dom d_elim ρb VBb qc ub i' as1 e ≈ d_elim C1 Bks p u0 j as2 e' ∈ per_bot ->
      cross_member_results i' j w w' ns ns' (⇑ (d_ind hd k as1) e) (⇑ (d_ind hd k as2) e').
  Proof.
    pose proof (nparams_rel_sym p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tsym.
    intros * Hvi HM Hrv Hcur Hb.
    pose proof Hcur as Hcur0.
    inversion Hcur0 as [| j0 Mj0 hd0 k0 ns0 ns0' as1' as2' e0 e0' w0 w0' HM0 Hrv0 Href Hn L1 L2 Hs1 Hs2 He |]; subst;
      [| rewrite HM in *; match goal with H : Some _ = Some _ |- _ => injection H as <- end;
         exfalso; eapply not_rview_record; eassumption ].
    rewrite HM in HM0; injection HM0 as <-.
    destruct (cross_member i' j Hvi) as (Mi' & Mk0 & HMi' & Hvmb).
    pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMk0; rewrite HM in HMk0; injection HMk0 as <-.
    pose proof (view_member_nn _ _ _ _ _ _ _ _ _ Hvmb) as Hnn'.
    assert (HrvI : im_is_rview Mi' = false) by (rewrite <- (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvmb); exact Hrv).
    pose proof (ind_rel_idx p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ HM Hcur Hs1 Hs2) as Hm.
    destruct (self_ref_target _ _ _ _ HM Href) as (Dq & Mq & Hq' & HMq & Hnnq & Hnuq).
    destruct (HbB _ _ HMi' HrvI) as [bb Hbb]; destruct (HBks _ _ HM Hrv) as [ba Hba].
    destruct (Hmot_x i' Mi' j bb ba w w' _ _ _ _ HMi' HrvI Hvi Hbb Hba Hm) as (a & a' & Ea & Ea' & HR).
    apply (cross_member_elim _ _ _ _ _ _ _ _ Mi' Mj (⇑ a (d_elim ρb VBb qc ub i' as1 e)) (⇑ a' (d_elim C1 Bks p u0 j as2 e'))
             HMi' HrvI HM Hrv).
    - eapply eval_elim_neut; [ exact Hq | exact HMi' | rewrite <- (view_member_ref _ _ _ _ _ _ _ _ _ Hvmb HrvI); exact Href | exact Hq'
                             | exact HMq | unfold im_np; lia | exact Hbb | rewrite (HnmB _ _ _ HMi' Hbb), Hnnq, Hnn'; reflexivity
                             | rewrite Hnuq; exact Ea ].
    - eapply eval_elim_neut; [ exact Hl | exact HM | exact Href | exact Hq' | exact HMq | unfold im_np; lia | exact Hba
                             | rewrite (valid_blocks_nm _ _ _ _ _ _ HBk _ _ _ HM Hba), Hnnq; reflexivity | rewrite Hnuq; exact Ea' ].
    - apply (self_motive_move _ _ _ _ _ _ _ _ _ _ HM Hrv Hm (tsym _ _ HM _ _ Hs1) (tsym _ _ HM _ _ Hs2)).
      exact (per_bot_then_per_elem HR Hb).
  Qed.

  Hypothesis (Hbot_x : forall i' j Mj hd k as1 as2 e e' w w' ns ns', List.nth_error vm i' = Some j ->
                ind_member D j = Some Mj -> im_is_rview Mj = false ->
                G j w w' ns ns' (⇑ (d_ind hd k as1) e) (⇑ (d_ind hd k as2) e') ->
                Dom d_elim ρb VBb qc ub i' as1 e ≈ d_elim C1 Bks p u0 j as2 e' ∈ per_bot).

  (** *** Related Elements Eliminate to Related Values *)
  Theorem cross_elim_all :
    (forall j u u' ns ns' x x', G j u u' ns ns' x x' ->
       forall i', List.nth_error vm i' = Some j -> cross_member_results i' j u u' ns ns' x x') /\
    (forall k u u' pre pre' gs vs vs',
       con_args_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' gs vs vs' ->
       forall gs', cargs_corr vm gs' gs -> cross_args_vals k u u' pre pre' gs' gs vs vs') /\
    (forall k u u' pre pre' t x x',
       rec_arg_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t x x' ->
       forall t', shape_corr vm t' t -> cross_arg_vals k u u' pre pre' t' t x x') /\
    (forall k u u' pre pre' t f c f' c',
       rec_arg_app_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t f c f' c' ->
       forall t', shape_corr vm t' t -> cross_app_vals k u u' pre pre' t' t f c f' c').
  Proof.
    pose proof (nparams_rel_sym p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tsym.
    apply ind_rel_mut_ind_all.
    - (** A constructor: the container's wrapped branch against the
          group's, moved to the indices. *)
      intros * HM Hrv Href Hn Hcn Lb Lb' Hs Hs' Ha Hia IH i' Hvi.
      destruct (cross_member i' k Hvi) as (Mi' & Mk0 & HMi' & Hvmb).
      pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMk0; rewrite HM in HMk0; injection HMk0 as <-.
      assert (HrvI : im_is_rview Mi' = false) by (rewrite <- (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvmb); exact Hrv).
      destruct (view_member_cons' _ _ _ _ _ _ _ _ _ Hvmb c gs Hcn) as (gs' & Hc' & Hcorr).
      destruct (IH gs' Hcorr) as [w ihs Ew Ei Hcr].
      destruct (HbB _ _ HMi' HrvI) as [bb Hbb]; destruct (HBks _ _ HM Hrv) as [ba Hba].
      destruct (brs_names_lookup _ _ _ _ (HnaB _ _ _ HMi' Hbb) Hc') as (nb & Bb & HBb & HinB).
      destruct (brs_names_lookup _ _ _ _ (valid_blocks_names _ _ _ _ _ _ HBk _ _ _ HM Hba) Hcn) as (na & Ba & HBa & HinA).
      pose proof (HarB _ _ _ _ _ _ _ HMi' Hbb Hc' HinB) as Hnb.
      pose proof (valid_blocks_arity _ _ _ _ _ _ HBk _ _ _ _ _ _ _ HM Hba Hcn HinA) as Hna.
      destruct (self_ref_target _ _ _ _ HM Href) as (Dq & Mq & Hq' & HMq & Hnnq & Hnuq).
      destruct (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia) as [Lv Lv'].
      pose proof (cargs_corr_len _ _ _ Hcorr) as Lgs.
      pose proof (view_member_nn _ _ _ _ _ _ _ _ _ Hvmb) as Hnn'.
      match goal with |- cross_member_results _ _ _ _ _ _ (d_con _ _ _ (?bs ++ ?vs)) (d_con _ _ _ (?bs' ++ ?vs')) =>
        assert (Hcur : G _ _ _ _ _ (d_con _ _ _ (bs ++ vs)) (d_con _ _ _ (bs' ++ vs')))
          by (eapply ind_rel_con; [ exact HM | exact Hrv | exact Href | exact Hn | exact Hcn | exact Lb | exact Lb' | exact Hs
                                 | exact Hs' | exact Ha | exact Hia ]) end.
      pose proof (ind_rel_idx p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ HM Hcur Hs Hs') as Hm.
      destruct (Hbr_x i' Mi' k Mk bb ba c gs' gs nb na Bb Ba u u' bs bs' vs vs' w ihs hd k'0 HMi' HrvI Hvi HM Hbb Hba Hc' Hcn HBb HBa
                  Hm Hcr) as (r & r' & Er & Er' & Hrr).
      apply (cross_member_elim _ _ _ _ _ _ _ _ Mi' Mk r r' HMi' HrvI HM Hrv).
      + eapply eval_elim_con; [ exact Hq | exact HMi' | rewrite <- (view_member_ref _ _ _ _ _ _ _ _ _ Hvmb HrvI); exact Href | exact Hq'
                              | exact HMq | exact Hc' | rewrite List.length_app; unfold im_np; lia | exact Hbb | exact HBb
                              | rewrite Hnnq, Hnn'; exact Hnb | exact HlcQ | |].
        * rewrite skipn_app_exact by (unfold im_np; lia); exact Ew.
        * rewrite firstn_app_exact, skipn_app_exact, Hnuq by (unfold im_np; lia); exact Er.
      + eapply eval_elim_con; [ exact Hl | exact HM | exact Href | exact Hq' | exact HMq | exact Hcn
                              | rewrite List.length_app; unfold im_np; lia | exact Hba | exact HBa | rewrite Hnnq; exact Hna
                              | exact Hlc | |].
        * rewrite skipn_app_exact by (unfold im_np; lia); exact Ei.
        * rewrite firstn_app_exact, skipn_app_exact, Hnuq by (unfold im_np; lia); exact Er'.
      + apply (self_motive_move _ _ _ _ _ _ _ _ _ _ HM Hrv Hm (tsym _ _ HM _ _ Hs) (tsym _ _ HM _ _ Hs')); exact Hrr.
    - (** A neutral: both stuck, their readbacks agree. *)
      intros * HM Hrv Href Hn L1 L2 Hs1 Hs2 He i' Hvi.
      assert (Hcur : G k u u' ns ns' (⇑ (d_ind hd k'0 as1) m0) (⇑ (d_ind hd k'0 as2) m'))
        by (eapply ind_rel_neut; [ exact HM | exact Hrv | exact Href | exact Hn | exact L1 | exact L2 | exact Hs1 | exact Hs2
                                 | exact He ]).
      exact (cross_neut_elim i' k Mk hd k'0 as1 as2 m0 m' u u' ns ns' Hvi HM Hrv Hcur
               (Hbot_x i' k Mk hd k'0 as1 as2 m0 m' u u' ns ns' Hvi HM Hrv Hcur)).
    - (** A record view: the container's is one of the same record and
          fields, its fields' results against the group's fields'. *)
      intros * HM Hhr Hnp Hcs Hp Hp' Ha Hia IH i' Hvi.
      destruct (cross_member i' k Hvi) as (Mi' & Mk0 & HMi' & Hvmb).
      pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMk0; rewrite HM in HMk0; injection HMk0 as <-.
      assert (HrvI : im_is_rview Mi' = true)
        by (rewrite <- (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvmb); unfold im_is_rview; rewrite Hhr; reflexivity).
      unfold im_is_rview in HrvI; destruct (im_head Mi') as [| | qr' Is' fl'] eqn:Hh'; try discriminate HrvI.
      destruct (view_member_rview _ _ _ _ _ _ _ _ _ Hvmb _ _ _ Hh') as (Is2 & Hh2).
      rewrite Hhr in Hh2; injection Hh2 as <- <- <-.
      destruct (rview_struct_con _ _ _ (grp_tele_ass_rstruct _ HassQ) _ _ _ _ _ HMi' Hh') as (gs0 & Hcs' & _).
      destruct (view_member_cons' _ _ _ _ _ _ _ _ _ Hvmb c gs ltac:(unfold ind_con; rewrite Hcs; cbn; rewrite String.eqb_refl; reflexivity))
        as (gs' & Hc' & Hcorr).
      unfold ind_con in Hc'; rewrite Hcs' in Hc'; cbn in Hc'.
      destruct (String.eqb c rview_con) eqn:Ec; [| discriminate Hc' ]; apply String.eqb_eq in Ec; subst c.
      injection Hc' as ->.
      destruct (IH gs' Hcorr) as [w ihs Ew Ei Hcr].
      exact (cross_member_rview _ _ _ _ _ _ _ _ Mi' Mk qr Is' Is0 fl rview_con gs' rview_con gs vs vs' w ihs
               HMi' Hh' Hcs' HM Hhr Hcs Hp Hp' Ew Ei Hcr).
    - intros k0 u u' pre pre' [| [A' | t'] gs'] Hco; cbn in Hco; try contradiction.
      exact (mk_cross_args_vals _ _ _ _ _ _ _ _ _ nil nil ltac:(constructor) ltac:(constructor) ltac:(constructor)).
    - intros * Hia IH [| [A' | t'] gs'] Hco; cbn in Hco; try contradiction.
      destruct (IH gs' Hco) as [w ihs Ew Ei Hcr].
      exact (mk_cross_args_vals _ _ _ _ _ _ _ _ _ w ihs ltac:(constructor; exact Ew) ltac:(constructor; exact Ei)
               ltac:(constructor; exact Hcr)).
    - intros * Hsh IHsh Hia IHia [| [A' | t'] gs'] Hco; cbn in Hco; try contradiction.
      + (** Nested through: the group's own results. *)
        destruct (IHia gs' Hco) as [w ihs Ew Ei Hcr].
        destruct (proj1 (proj2 (proj2 self_elim_all)) _ _ _ _ _ _ _ _ Hsh) as (rs0 & rs & _ & Eh & _).
        exact (mk_cross_args_vals _ _ _ _ _ _ _ _ _ w (rs ++ ihs) ltac:(constructor; exact Ew)
                 ltac:(econstructor; [ exact Eh | exact Ei ]) ltac:(econstructor; [ exact Eh | exact Hcr ])).
      + destruct Hco as (Hm & Hd & Hco).
        destruct (IHia gs' Hco) as [w ihs Ew Ei Hcr].
        destruct (IHsh t' (shape_corr_of _ _ _ Hm Hd)) as [rs rs' Eh Eh' Hhh].
        refine (mk_cross_args_vals _ _ _ _ _ _ _ _ _ (rs ++ w) (rs' ++ ihs) ltac:(econstructor; [ exact Eh | exact Ew ])
                  ltac:(econstructor; [ exact Eh' | exact Ei ]) _).
        apply cross_fields_rec; [| | exact Hhh | exact Hcr ].
        * rewrite (proj1 (proj2 eval_ih_length_all) _ _ _ _ _ _ _ Eh D' Hq HlcQ).
          symmetry; exact (leaves_in_count_view p qc D D' vm Hlc HlcQ (grp_tele_ass_rstruct _ Hass) (grp_tele_ass_rstruct _ HassQ)
                             cross_member (S (ptyp_mem t)) t' t 0 (fun _ _ _ => Nat.lt_succ_diag_r _) (shape_corr_of _ _ _ Hm Hd)).
        * exact (proj1 (proj2 eval_ih_length_all) _ _ _ _ _ _ _ Eh' D Hl Hlc).
    - (** The end of a shape. *)
      intros * Hb Hb' Ok Ok' Hr IHr [j' Ps' | B' t'] Hsc; cbn in Hsc; try contradiction.
      destruct (IHr j' Hsc) as [Mi' Mj r r' HMi' HrvI HMj Hrv Er Er' Hrr
                              | Mi' Mj qr Is' Is0 fl c' gs' c gs ws ws' rs rs' HMi' Hh' Hcs' HMj Hh0 Hcs Ep Ep' Ei Ei' Hcr].
      + exact (mk_cross_arg_vals _ _ _ _ _ _ _ _ _ (r :: nil) (r' :: nil) ltac:(eapply eval_ih_self; eassumption)
                 ltac:(eapply eval_ih_self; eassumption)
                 ltac:(eapply cross_result_self; [ exact HMi' | exact HrvI | exact HMj | exact Hrv | exact Hb | exact Hb' | exact Hrr ])).
      + refine (mk_cross_arg_vals _ _ _ _ _ _ _ _ _ rs rs' _ _ _).
        * eapply eval_ih_rview; [ exact Hq | exact HMi' | exact Hh' | exact Hcs' | exact Ep | exact Ei ].
        * eapply eval_ih_rview; [ exact Hl | exact HMj | exact Hh0 | exact Hcs | exact Ep' | exact Ei' ].
        * eapply cross_result_rview; [ exact HMi' | exact Hh' | exact Hcs' | exact HMj | exact Hh0 | exact Hcs | exact Ep | exact Ep'
                                     | exact Hcr ].
    - (** A function shape: the families, at each leaf path. *)
      intros * Hf IH [j' Ps' | B' t'] Hsc; cbn in Hsc; try contradiction.
      match goal with |- cross_arg_vals _ _ _ _ _ _ (pt_pi _ ?t) ?f ?f' =>
        refine (mk_cross_arg_vals _ _ _ _ _ _ _ _ _
                  (List.map (fun i => d_ihfn ρb VBb qc ub t' i f) (List.seq 0 (List.length (shape_leaves (rv_leaves D') 0 t'))))
                  (List.map (fun i => d_ihfn C1 Bks p u0 t i f') (List.seq 0 (List.length (shape_leaves (rv_leaves D) 0 t))))
                  ltac:(eapply eval_ih_pi; exact Hq) ltac:(eapply eval_ih_pi; exact Hl) _) end.
      constructor; intros c c' Hcc.
      destruct (IH c c' Hcc t' Hsc) as [fc fc' rcs rcs' Ef Ef' Er Er' Hrr].
      econstructor; [ exact Ef | exact Ef' | | | exact Hrr ].
      + exact (ihfn_app _ _ _ _ _ _ _ _ _ _ Ef Er (proj1 (proj2 eval_ih_length_all) _ _ _ _ _ _ _ Er D' Hq HlcQ)).
      + exact (ihfn_app _ _ _ _ _ _ _ _ _ _ Ef' Er' (proj1 (proj2 eval_ih_length_all) _ _ _ _ _ _ _ Er' D Hl Hlc)).
    - intros * Ef Ef' Hsh IHsh t' Hsc.
      destruct (IHsh t' Hsc) as [rs rs' Eh Eh' Hhh].
      exact (mk_cross_app_vals _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ef Ef' Eh Eh' Hhh).
  Qed.
End CrossElim.

(** ** The Container's Wrapped Blocks

    The blocks [view_wrap] of the view [m] of the container's group [D'] at
    [qc] meet the conditions of [CrossElim], at [C1] and moved by a
    substitution into [C1]'s class.  The container's members with a block
    are taken to the group's members with one ([view_member]); its record
    views have none. *)
Section WrappedBlocks.
  #[local] Set Default Proof Using "All".
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups VP) (HPD : VP p D).
  Let Hvg := valid_groups_valid VP HP p D HPD.
  Let Hc := valid_group_closed _ _ Hvg.
  Let Hdt := valid_group_typed _ _ Hvg.
  Let Hass := valid_group_ass _ _ Hvg.
  Let Hlc : leaves_coherent D := leaves_coherent_of_order D (rview_struct_order _ _ _ (grp_tele_ass_rstruct _ Hass)).
  Variable (Γ : ctx) (RΓ : relation env).
  Hypotheses (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HΓ : ⊨ Γ).
  Variable (RU : relation env).
  Hypothesis (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).
  Variable (Us : list exp).
  Hypotheses (HUl : List.length Us = ind_nu D)
    (HUs : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊨ N : T).
  Variable (C1 : env) (u0 : list domain).
  Hypotheses (HC11 : RΓ C1 C1) (HUC : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ C1 ↘ u0).
  Variable (Bks : list eblock) (iA : nat).
  Hypothesis (HBk : valid_blocks p D Γ Us Bks iA).
  Let HBks := valid_blocks_has p D Γ Us Bks iA Hdt HBk.
  Let HMall := valid_blocks_mctx _ _ _ _ _ _ HBk.
  Let HAv := valid_blocks_motive _ _ _ _ _ _ HBk.
  Let nr := canon_nparams_rel D u0.
  Let ar := canon_args_rel D u0.
  Let dr := canon_doms_rel u0.
  Let G := grp_rel p D u0 nr ar dr.
  Let Rel := fun j ns m ns' m' =>
    per_head (List.nth j (blocks_motives Bks) a_True) (List.nth j (blocks_motives Bks) a_True)
      (env_args C1 (ns ++ m :: nil)) (env_args C1 (ns' ++ m' :: nil)).
  #[local] Abbreviation EB f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HC11 HUC).
  #[local] Abbreviation WR f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HC11 HUC Bks iA HBk).

  Variable (qc : qname) (D' : ind_decl) (m : nat) (Mm : imember) (k' : nat) (Is : list exp) (vm : list nat).
  Hypotheses (Hq : ind_lookup gc_deps gc_stack qc = Some D') (HMm : ind_member D m = Some Mm)
    (Hh : im_head Mm = mh_view qc k' Is vm).
  Let HgQ := valid_groups_valid VP HP qc D' (valid_groups_containers VP HP p D m Mm qc k' Is vm D' HPD HMm Hh Hq).
  Let HdtQ := valid_group_typed _ _ HgQ.
  Let HrsQ : rview_struct_ok gc_deps gc_stack D' := decl_typed_rstruct _ _ _ HdtQ.
  Let HassQ := valid_group_ass _ _ HgQ.
  Let HlcQ : leaves_coherent D' := leaves_coherent_of_order D' (rview_struct_order _ _ _ (grp_tele_ass_rstruct _ HassQ)).
  Let VB := view_wrap p D D' vm Us Bks.

  (** Each member of the container's group, the member of the group the
      view's map takes it to. *)
  Lemma wrapped_view_member : forall i' Mi', ind_member D' i' = Some Mi' -> exists v Mv, view_member p D qc D' vm i' Mi' v Mv.
  Proof. exact (view_agree_members p D m Mm qc k' Is vm D' Hass HMm Hh Hq). Qed.

  Lemma wrapped_view_members : forall j' j, List.nth_error vm j' = Some j ->
      exists Mj' Mj, ind_member D' j' = Some Mj' /\ view_member p D qc D' vm j' Mj' j Mj.
  Proof.
    intros j' j Hv.
    destruct (grp_tele_ass_view_wrap _ Hass _ _ _ _ _ _ HMm Hh) as (D2 & Hq2 & Hvw).
    rewrite Hq in Hq2; injection Hq2 as <-.
    assert (Hi : j' < List.length (ind_members D')) by (rewrite <- (view_wrap_ok_length _ _ _ Hvw); apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some' _ _ Hi) as [Mj' HMj'].
    destruct (wrapped_view_member j' Mj' HMj') as (v & Mv & Hvm).
    pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvm) as Hv'; rewrite Hv in Hv'; injection Hv' as <-.
    exists Mj', Mv; split; [ exact HMj' | exact Hvm ].
  Qed.

  (** The block of the container's member [i'] with a block: the group's
      block of the member [vm] takes it to, its branches wrapped. *)
  #[warnings="-cannot-define-projection"]
  Record wrapped_block_at (i' : nat) (Mi' : imember) : Prop := mk_wrapped_block_at
    { (** The member of the group [vm] takes [i'] to *)
      wrapped_block_at_index : nat
      (** That member *)
    ; wrapped_block_at_member : imember
      (** Its block *)
    ; wrapped_block_at_block : eblock
      (** [vm] takes [i'] to it *)
    ; wrapped_block_at_in_view_map : List.nth_error vm i' = Some wrapped_block_at_index
      (** It is a member of the group *)
    ; wrapped_block_at_is_member : ind_member D wrapped_block_at_index = Some wrapped_block_at_member
      (** It is not a record view *)
    ; wrapped_block_at_not_rview : im_is_rview wrapped_block_at_member = false
      (** It has its block *)
    ; wrapped_block_at_has_block : List.nth_error Bks wrapped_block_at_index = Some wrapped_block_at_block
      (** It has as many non-uniform parameters as [Mi'] *)
    ; wrapped_block_at_same_nparams_count : im_nn wrapped_block_at_member = im_nn Mi'
      (** The constructors' arguments correspond *)
    ; wrapped_block_at_args_corr : forall c gs' gs, ind_con Mi' c = Some gs' -> ind_con wrapped_block_at_member c = Some gs ->
        cargs_corr vm gs' gs
      (** The wrapped block of [i'] is its block, its branches wrapped *)
    ; wrapped_block_at_wrapped : List.nth_error VB i'
        = Some (eb_mk (eb_nm wrapped_block_at_block) None (eb_motive wrapped_block_at_block)
                  (List.map (fun cg => wrap_br p D D' Us Bks wrapped_block_at_member (eb_brs wrapped_block_at_block) (fst cg) (snd cg))
                     (im_cons Mi'))) }.

  Lemma wrapped_block : forall i' Mi', ind_member D' i' = Some Mi' -> im_is_rview Mi' = false -> wrapped_block_at i' Mi'.
  Proof.
    intros i' Mi' HMi' Hrv'.
    destruct (wrapped_view_member i' Mi' HMi') as (v & Mv & Hvm).
    pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvm) as Hv.
    pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvm) as HMv.
    assert (Hrv : im_is_rview Mv = false) by (rewrite (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvm); exact Hrv').
    destruct (HBks _ _ HMv Hrv) as [bv Hbv].
    refine (mk_wrapped_block_at i' Mi' v Mv bv Hv HMv Hrv Hbv (view_member_nn _ _ _ _ _ _ _ _ _ Hvm) _ _).
    - intros c gs' gs Hc' Hcn.
      destruct (view_member_cons _ _ _ _ _ _ _ _ _ Hvm c gs' Hc') as (gs0 & Hc0 & Hco).
      rewrite Hcn in Hc0; injection Hc0 as <-; exact Hco.
    - unfold VB; rewrite (nth_error_view_wrap _ _ _ _ _ _ _ _ (rview_struct_suffix _ _ _ HrsQ) HMi' Hrv').
      rewrite (view_wrap_block_eq _ _ _ _ _ _ _ _ _ _ _ Hv Hbv HMv); reflexivity.
  Qed.

  (** A block of the wrapped blocks is of a member that is not a record
      view. *)
  Lemma wrapped_at_not_rview : forall i' Mi' b, ind_member D' i' = Some Mi' -> List.nth_error VB i' = Some b ->
      im_is_rview Mi' = false.
  Proof.
    intros * HMi' Hb; unfold VB, view_wrap in Hb.
    destruct (nth_error_view_wrap_from _ _ _ _ _ _ _ _ _ _ Hb) as (Mi'' & Hi & _).
    destruct (ind_bmembers_member _ _ _ Hi) as [HM Hlt].
    rewrite HMi' in HM; injection HM as <-.
    destruct (im_is_rview Mi') eqn:E; [| reflexivity ].
    apply (proj1 (rview_struct_suffix _ _ _ HrsQ _ _ HMi')) in E; lia.
  Qed.

  Lemma wrapped_nodup : forall i' Mi', ind_member D' i' = Some Mi' -> List.NoDup (List.map fst (im_cons Mi')).
  Proof. exact (decl_typed_nodup _ _ _ HdtQ). Qed.

  (** *** At [C1] *)
  Lemma wrapped_at_has : forall i' Mi', ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
      exists b, List.nth_error VB i' = Some b.
  Proof. intros * HMi' Hrv'; destruct (wrapped_block _ _ HMi' Hrv'); eexists; eassumption. Qed.

  Lemma wrapped_at_nm : forall i' Mi' b, ind_member D' i' = Some Mi' -> List.nth_error VB i' = Some b -> eb_nm b = S (im_nn Mi').
  Proof.
    intros * HMi' Hb; destruct (wrapped_block _ _ HMi' (wrapped_at_not_rview _ _ _ HMi' Hb)) as [v Mv bv Hv HMv _ Hbv Hnn _ Hvb].
    rewrite Hvb in Hb; injection Hb as <-; cbn [eb_nm].
    rewrite (valid_blocks_nm _ _ _ _ _ _ HBk _ _ _ HMv Hbv), Hnn; reflexivity.
  Qed.

  Lemma wrapped_at_names : forall i' Mi' b, ind_member D' i' = Some Mi' -> List.nth_error VB i' = Some b ->
      brs_names (im_cons Mi') (eb_brs b).
  Proof.
    intros * HMi' Hb; destruct (wrapped_block _ _ HMi' (wrapped_at_not_rview _ _ _ HMi' Hb)) as [v Mv bv Hv HMv _ Hbv Hnn _ Hvb].
    rewrite Hvb in Hb; injection Hb as <-; cbn [eb_brs]; apply brs_names_wrap.
  Qed.

  Lemma wrapped_at_arity : forall i' Mi' b c gs' n B, ind_member D' i' = Some Mi' -> List.nth_error VB i' = Some b ->
      ind_con Mi' c = Some gs' -> In (c, n, B) (eb_brs b) -> n = (im_nn Mi' + List.length gs' + cargs_nrec D' gs')%nat.
  Proof.
    intros * HMi' Hb Hc' Hin.
    destruct (wrapped_block _ _ HMi' (wrapped_at_not_rview _ _ _ HMi' Hb)) as [v Mv bv Hv HMv _ Hbv Hnn _ Hvb].
    rewrite Hvb in Hb; injection Hb as <-; cbn [eb_brs] in Hin.
    destruct (brs_in_wrap _ _ _ _ _ _ _ _ _ _ _ Hin) as (gs0 & Hin0 & ->).
    pose proof (cons_lookup_nodup_in _ _ _ (wrapped_nodup _ _ HMi') Hin0) as Hc0.
    unfold ind_con in Hc'; rewrite Hc0 in Hc'; injection Hc' as ->; rewrite Hnn; reflexivity.
  Qed.

  Lemma wrapped_at_motive : forall i' Mi' v bb ba u u' ns ns' x x', ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
      List.nth_error vm i' = Some v -> List.nth_error VB i' = Some bb -> List.nth_error Bks v = Some ba -> G v u u' ns ns' x x' ->
      exists a a', ⟦ eb_motive bb ⟧ env_args C1 (ns ++ x :: nil) ↘ a /\
        ⟦ eb_motive ba ⟧ env_args C1 (ns' ++ x' :: nil) ↘ a' /\
        DF a ≈ a' ∈ per_univ_elem iA ↘ Rel v ns x ns' x'.
  Proof.
    intros * HMi' Hrv' Hv Hb Hba Hm; destruct (wrapped_block _ _ HMi' Hrv') as [v0 Mv bv Hv0 HMv _ Hbv Hnn _ Hvb].
    rewrite Hv in Hv0; injection Hv0 as <-; rewrite Hbv in Hba; injection Hba as <-.
    rewrite Hvb in Hb; injection Hb as <-; cbn [eb_motive].
    exact (EB mot_mid C1 HC11 Bks iA HMall v Mv bv (eb_motive bv) HMv Hbv (HAv _ _ _ HMv Hbv) u u' ns ns' x x' Hm).
  Qed.

  (** The wrapped branch of [c] in the wrapped block of [i'], at the view's
      member [Mv]: [wrap_branch_rel]'s. *)
  Lemma wrapped_branch_of : forall i' Mi' v Mv bb ba c gs' gs nb na Bb Ba,
      ind_member D' i' = Some Mi' -> List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
      List.nth_error VB i' = Some bb -> List.nth_error Bks v = Some ba ->
      ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
      brs_lookup (eb_brs bb) c = Some (nb, Bb) -> brs_lookup (eb_brs ba) c = Some (na, Ba) ->
      Bb = Ba[ViewBranch.wrap_br_sub p D D' Us Bks Mv gs' gs] /\ nb = (im_nn Mv + List.length gs' + cargs_nrec D' gs')%nat /\
      im_is_rview Mv = false /\ cargs_corr vm gs' gs.
  Proof.
    intros * HMi' Hv HMv Hb Hba Hc' Hcn HBb HBa.
    destruct (wrapped_block _ _ HMi' (wrapped_at_not_rview _ _ _ HMi' Hb)) as [v0 Mv0 bv Hv0 HMv0 Hrv Hbv Hnn Hcorr Hvb].
    rewrite Hv in Hv0; injection Hv0 as <-; rewrite HMv in HMv0; injection HMv0 as <-; rewrite Hbv in Hba; injection Hba as <-.
    rewrite Hvb in Hb; injection Hb as <-; cbn [eb_brs] in HBb.
    rewrite brs_lookup_wrap in HBb; unfold ind_con in Hc'; rewrite Hc' in HBb; cbn [option_map] in HBb.
    rewrite (wrap_br_snd _ _ _ _ _ _ _ _ _ _ _ _ Hcn HBa) in HBb.
    injection HBb as <- <-.
    repeat split; [ exact Hrv | exact (Hcorr _ _ _ Hc' Hcn) ].
  Qed.

  Lemma wrapped_at_branch : forall i' Mi' v Mv bb ba c gs' gs nb na Bb Ba u u' bs bs' vs vs' w ihs hd k,
      ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
      List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
      List.nth_error VB i' = Some bb -> List.nth_error Bks v = Some ba ->
      ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
      brs_lookup (eb_brs bb) c = Some (nb, Bb) -> brs_lookup (eb_brs ba) c = Some (na, Ba) ->
      G v u u' (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs') (d_con hd k c (bs ++ vs)) (d_con hd k c (bs' ++ vs')) ->
      cross_fields_rel D D' dr Rel C1 p u0 Bks v u u'
        (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs') gs' gs vs vs' w ihs ->
      exists r r', ⟦ Bb ⟧ env_args C1 (List.skipn (im_unu D Mv) bs ++ vs ++ w) ↘ r /\
        ⟦ Ba ⟧ env_args C1 (List.skipn (im_unu D Mv) bs' ++ vs' ++ ihs) ↘ r' /\
        Rel v (List.skipn (im_unu D Mv) bs) (d_con hd k c (bs ++ vs)) (List.skipn (im_unu D Mv) bs') (d_con hd k c (bs' ++ vs')) r r'.
  Proof.
    intros * HMi' _ Hv HMv Hb Hba Hc' Hcn HBb HBa Hm Hcr.
    destruct (wrapped_branch_of _ _ _ _ _ _ _ _ _ _ _ _ _ HMi' Hv HMv Hb Hba Hc' Hcn HBb HBa) as (-> & _ & Hrv & Hco).
    pose proof (cargs_kinds_of_corr _ _ _ Hco) as Hk.
    pose proof (cargs_nin_view p qc D D' vm Hlc HlcQ (grp_tele_ass_rstruct _ Hass) HrsQ wrapped_view_members gs' gs Hco) as Hcnt.
    destruct (WR wrap_branch_rel D' v Mv c gs' gs HMv Hcn Hk Hrv ba Hba HrsQ Hcnt na Ba HBa u u' bs bs' vs vs' w ihs hd k Hm Hcr)
      as [r r' Er Er' Hrr _].
    exists r, r'; split; [ exact Er | split; [ exact Er' | exact Hrr ] ].
  Qed.

  (** *** Moved by a Semantic Substitution

      The wrapped blocks moved by a semantic substitution [σ0] from [Γ'] at
      [ρ0], of value [C1] there. *)
  Section Moved.
    Variable (Γ' : ctx) (RΓ' : relation env) (σ0 : sub) (ρ0 : env).
    Hypotheses (HRΓ' : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ') (Hσ0 : Γ' ⊨ˢ σ0 ≈ σ0 : Γ) (Hρ0 : RΓ' ρ0 ρ0)
      (Hev0 : ⟦ σ0 ⟧s ρ0 ↘ C1).
    Let VBs := blocks_sub VB σ0.

    Lemma moved_at_has : forall i' Mi', ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
        exists b, List.nth_error VBs i' = Some b.
    Proof.
      intros * HMi' Hrv'; destruct (wrapped_at_has _ _ HMi' Hrv') as [b Hb].
      exists (eblock_sub b σ0); unfold VBs; rewrite nth_error_blocks_sub, Hb; reflexivity.
    Qed.

    Lemma moved_at_nm : forall i' Mi' b, ind_member D' i' = Some Mi' -> List.nth_error VBs i' = Some b -> eb_nm b = S (im_nn Mi').
    Proof.
      intros * HMi' Hb; destruct (nth_error_blocks_sub_inv _ _ _ _ Hb) as (b0 & Hb0 & ->).
      rewrite eb_nm_sub; exact (wrapped_at_nm _ _ _ HMi' Hb0).
    Qed.

    Lemma moved_at_names : forall i' Mi' b, ind_member D' i' = Some Mi' -> List.nth_error VBs i' = Some b ->
        brs_names (im_cons Mi') (eb_brs b).
    Proof.
      intros * HMi' Hb; destruct (nth_error_blocks_sub_inv _ _ _ _ Hb) as (b0 & Hb0 & ->).
      rewrite eb_brs_sub; apply brs_names_sub; exact (wrapped_at_names _ _ _ HMi' Hb0).
    Qed.

    Lemma moved_at_arity : forall i' Mi' b c gs' n B, ind_member D' i' = Some Mi' -> List.nth_error VBs i' = Some b ->
        ind_con Mi' c = Some gs' -> In (c, n, B) (eb_brs b) -> n = (im_nn Mi' + List.length gs' + cargs_nrec D' gs')%nat.
    Proof.
      intros * HMi' Hb Hc' Hin; destruct (nth_error_blocks_sub_inv _ _ _ _ Hb) as (b0 & Hb0 & ->).
      rewrite eb_brs_sub in Hin; destruct (brs_in_sub _ _ _ _ _ Hin) as [B0 Hin0].
      exact (wrapped_at_arity _ _ _ _ _ _ _ HMi' Hb0 Hc' Hin0).
    Qed.

    Lemma moved_at_motive : forall i' Mi' v bb ba u u' ns ns' x x', ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
        List.nth_error vm i' = Some v -> List.nth_error VBs i' = Some bb -> List.nth_error Bks v = Some ba -> G v u u' ns ns' x x' ->
        exists a a', ⟦ eb_motive bb ⟧ env_args ρ0 (ns ++ x :: nil) ↘ a /\
          ⟦ eb_motive ba ⟧ env_args C1 (ns' ++ x' :: nil) ↘ a' /\
          DF a ≈ a' ∈ per_univ_elem iA ↘ Rel v ns x ns' x'.
    Proof.
      intros * HMi' Hrv' Hv Hb Hba Hm.
      destruct (nth_error_blocks_sub_inv _ _ _ _ Hb) as (b0 & Hb0 & ->).
      destruct (wrapped_block _ _ HMi' Hrv') as [v0 Mv bv Hv0 HMv _ Hbv Hnn _ Hvb].
      rewrite Hv in Hv0; injection Hv0 as <-; rewrite Hbv in Hba; injection Hba as <-.
      rewrite Hvb in Hb0; injection Hb0 as <-.
      rewrite eb_motive_sub; cbn [eb_motive eb_nm].
      rewrite (valid_blocks_nm _ _ _ _ _ _ HBk _ _ _ HMv Hbv).
      exact (EB mot_out C1 HC11 Bks iA HMall HAv v Mv bv HMv Hbv Γ' RΓ' σ0 ρ0 C1 (eb_motive bv) HRΓ' Hσ0 Hρ0 Hev0 HC11
               (HAv _ _ _ HMv Hbv) u u' ns ns' x x' Hm).
    Qed.

    Lemma moved_at_branch : forall i' Mi' v Mv bb ba c gs' gs nb na Bb Ba u u' bs bs' vs vs' w ihs hd k,
        ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
        List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
        List.nth_error VBs i' = Some bb -> List.nth_error Bks v = Some ba ->
        ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
        brs_lookup (eb_brs bb) c = Some (nb, Bb) -> brs_lookup (eb_brs ba) c = Some (na, Ba) ->
        G v u u' (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs') (d_con hd k c (bs ++ vs)) (d_con hd k c (bs' ++ vs')) ->
        cross_fields_rel D D' dr Rel C1 p u0 Bks v u u'
          (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs') gs' gs vs vs' w ihs ->
        exists r r', ⟦ Bb ⟧ env_args ρ0 (List.skipn (im_unu D Mv) bs ++ vs ++ w) ↘ r /\
          ⟦ Ba ⟧ env_args C1 (List.skipn (im_unu D Mv) bs' ++ vs' ++ ihs) ↘ r' /\
          Rel v (List.skipn (im_unu D Mv) bs) (d_con hd k c (bs ++ vs)) (List.skipn (im_unu D Mv) bs') (d_con hd k c (bs' ++ vs')) r r'.
    Proof.
      intros * HMi' _ Hv HMv Hb Hba Hc' Hcn HBb HBa Hm Hcr.
      destruct (nth_error_blocks_sub_inv _ _ _ _ Hb) as (b0 & Hb0 & ->).
      rewrite eb_brs_sub in HBb; destruct (brs_lookup_sub_inv _ _ _ _ _ HBb) as (B0 & HlB0 & ->).
      destruct (wrapped_branch_of _ _ _ _ _ _ _ _ _ _ _ _ _ HMi' Hv HMv Hb0 Hba Hc' Hcn HlB0 HBa) as (-> & -> & Hrv & Hco).
      pose proof (cargs_kinds_of_corr _ _ _ Hco) as Hk.
      pose proof (cargs_nin_view p qc D D' vm Hlc HlcQ (grp_tele_ass_rstruct _ Hass) HrsQ wrapped_view_members gs' gs Hco) as Hcnt.
      destruct (WR wrap_branch_rel D' v Mv c gs' gs HMv Hcn Hk Hrv ba Hba HrsQ Hcnt na Ba HBa u u' bs bs' vs vs' w ihs hd k Hm Hcr)
        as [r r' _ Er' _ Hout].
      destruct (Hout Γ' RΓ' σ0 ρ0 HRΓ' Hσ0 Hρ0 Hev0) as (r0 & Er0 & Hrr).
      exists r0, r'; split; [| split; [ exact Er' | exact Hrr ] ].
      rewrite (cargs_kinds_length _ _ Hk) in Er0 |- *.
      exact Er0.
    Qed.
  End Moved.
End WrappedBlocks.

End Fixed_GCtx.
