(** * The View Search, as a Total Function

    The views of a group declaration are found breadth-first ([views_bfs],
    in [Core.Syntactic.Inductives.Group]) from the instances its
    constructors meet.  This file computes them with no fuel, generically
    over the data the checker files for each view: a functional relation
    [E x a] ("the view [x] has the data [a]", from which its siblings
    [sibs_of a] and the instances its constructors meet [meets_of a] are
    read), decided by [E_dec].

    - The search ([search]) is by structural recursion on an accessibility
      proof in [Prop] (erased by extraction), for the order "more views
      found, or as many and a shorter queue" ([search_lt]); it needs only
      that the views reachable from the queue form a finite set
      ([reach_finite]).  It is sound and complete for [views_bfs].
    - The finiteness itself follows from a cluster argument
      ([reach_finite_of_clusters]): every view of an invariant [Inv] has a
      finite cluster closed under siblings, whose meets stay in it or
      descend a well-founded order [lt]; the meets of any view are of
      [Inv]; and the siblings of any view are of [Inv], or have the same
      siblings.  The instances of these hypotheses, read off the PER model,
      are in [Extraction.ViewsReach]. *)

From Stdlib Require Import List Lia PeanoNat Wf_nat.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Inductives Require Import Group.
Import ListNotations.

Section Search.
  (** The data of a view. *)
  Variable A : Type.
  (** The view [x] has the data [a]. *)
  Variable E : rview -> A -> Prop.
  (** The siblings, and the instances met, read off the data. *)
  Variables (sibs_of meets_of : A -> list rview).
  Hypothesis E_functional : forall x a a', E x a -> E x a' -> a = a'.
  (** Why a view has no data. *)
  Variable Err : Type.
  Variable E_dec : forall x, ({a | E x a} + {e : Err | forall a, ~ E x a})%type.
  (** The instances the declared members' constructors meet. *)
  Variable init : list rview.

  (** The views reachable from the queue: an over-approximation of what the
      search visits (it follows the siblings of every reachable view, the
      search only those of the views it meets). *)
  Inductive reach : rview -> Prop :=
  (** An instance of the queue *)
  | reach_init : forall x, In x init -> reach x
  (** A sibling of a reachable view, or the view itself *)
  | reach_sib : forall x a y, reach x -> E x a -> In y (sibs_of a ++ x :: nil) -> reach y
  (** An instance a reachable view's constructors meet *)
  | reach_meet : forall x a y, reach x -> E x a -> In y (meets_of a) -> reach y.

  (** The table of the instances met, aligned with the views. *)
  Definition mtbl (Vs : list rview) (Ms : list (list rview)) (x : rview) : list rview :=
    match rview_index x Vs with Some v => List.nth v Ms nil | None => nil end.

  Lemma meets_tbl_mtbl : forall Vs csV x, meets_tbl Vs csV x = mtbl Vs (List.map rcons_views csV) x.
  Proof.
    intros; unfold meets_tbl, mtbl; destruct (rview_index x Vs); [| reflexivity ].
    change nil with (rcons_views nil) at 2; rewrite List.map_nth; reflexivity.
  Qed.

  Lemma Forall2_nth : forall {X Y} (R : X -> Y -> Prop) l1 l2 v x, Forall2 R l1 l2 -> nth_error l1 v = Some x ->
      exists y, nth_error l2 v = Some y /\ R x y.
  Proof.
    intros X Y R l1 l2 v x H; revert v; induction H as [| a b l1 l2 Hab _ IH]; intros [| v] Hv; cbn in *; try discriminate.
    - injection Hv as <-; eauto.
    - eauto.
  Qed.

  (** A table of data satisfying [E] reads off the data of a key. *)
  Lemma tbl_at : forall Vs As y a, Forall2 E Vs As -> In y Vs -> E y a ->
      sibs_tbl Vs (List.map sibs_of As) y = sibs_of a /\ mtbl Vs (List.map meets_of As) y = meets_of a.
  Proof.
    intros * HF Hy Ha; unfold sibs_tbl, mtbl.
    destruct (rview_index y Vs) as [v |] eqn:Hv.
    2:{ exfalso; destruct (rview_mem y Vs) eqn:Hm; [| apply (proj2 (rview_mem_spec y Vs)) in Hy; congruence ].
        unfold rview_mem in Hm; rewrite Hv in Hm; discriminate. }
    apply rview_index_in in Hv.
    destruct (Forall2_nth _ _ _ _ _ HF Hv) as (a' & Ha' & He); rewrite (E_functional _ _ _ He Ha) in Ha'.
    split; apply List.nth_error_nth; rewrite List.nth_error_map, Ha'; reflexivity.
  Qed.

  Lemma views_new_incl : forall acc ss y, In y (views_new acc ss) -> In y ss.
  Proof.
    intros acc ss; revert acc; induction ss as [| s ss IH]; cbn; intros acc y H; [ exact H |].
    destruct (rview_mem s acc); [ right; eapply IH; eauto |].
    destruct H as [<- | H]; [ left; reflexivity | right; eapply IH; eauto ].
  Qed.

  Lemma views_new_nodup : forall acc ss, NoDup acc -> NoDup (acc ++ views_new acc ss).
  Proof.
    intros acc ss; revert acc; induction ss as [| s ss IH]; cbn; intros acc Hd; [ rewrite app_nil_r; exact Hd |].
    destruct (rview_mem s acc) eqn:Hm; [ apply IH, Hd |].
    replace (acc ++ s :: views_new (acc ++ [s]) ss) with ((acc ++ [s]) ++ views_new (acc ++ [s]) ss)
      by (rewrite <- List.app_assoc; reflexivity).
    apply IH; apply NoDup_app; [ exact Hd | constructor; [ intros [] | constructor ] |].
    intros y Hy [Heq | []]; subst y; apply (proj2 (rview_mem_spec s acc)) in Hy; congruence.
  Qed.

  (** ** The Search's Order

      More views found, or as many and a shorter queue; the views found
      are distinct and reachable, so there are boundedly many. *)

  (** The views found are distinct and reachable. *)
  Definition found_ok (Vs : list rview) : Prop := NoDup Vs /\ forall y, In y Vs -> reach y.

  (** The order of the search's states (the views found, the queue). *)
  Definition search_lt (s' s : prod (list rview) (list rview)) : Prop :=
    found_ok (fst s') /\
    ((incl (fst s) (fst s') /\ List.length (fst s) < List.length (fst s')) \/
     (fst s' = fst s /\ List.length (snd s') < List.length (snd s))).

  Section Order.
    Hypothesis reach_finite : exists L, forall y, reach y -> In y L.

    Lemma search_acc : forall Vs tr, Acc search_lt (Vs, tr).
    Proof.
      destruct reach_finite as [L HL].
      assert (Hb : forall Vs, found_ok Vs -> List.length Vs <= List.length L).
      { intros Vs [Hd Hr]; apply NoDup_incl_length; [ exact Hd | intros y Hy; apply HL, Hr, Hy ]. }
      assert (H : forall n m Vs tr, List.length L - List.length Vs <= n -> List.length tr <= m -> Acc search_lt (Vs, tr)).
      { induction n as [n IHn] using (well_founded_induction lt_wf); induction m as [m IHm] using (well_founded_induction lt_wf).
        intros Vs tr Hn Hm; constructor; intros [Vs' tr'] Hl; unfold search_lt in Hl; cbn in Hl;
          destruct Hl as [Hok [[Hi Hlt] | [-> Hlt]]].
        - pose proof (Hb _ Hok); apply (IHn (List.length L - List.length Vs') ltac:(lia) (List.length tr') Vs' tr'); lia.
        - apply (IHm (List.length tr') ltac:(lia) _ _ Hn); lia. }
      intros; eapply H; reflexivity.
    Qed.
  End Order.

  (** The data of a list of views, or the first one that has none, with
      why; the data [ak] of the view [k] is known already. *)
  Fixpoint data_of (k : rview) (ak : A) (Hk : E k ak) (ys : list rview) :
      ({As | Forall2 E ys As} + {ye : rview * Err | In (fst ye) ys /\ forall a, ~ E (fst ye) a})%type.
  Proof.
    destruct ys as [| y ys].
    - left; exists nil; constructor.
    - assert (Hy : ({a | E y a} + {e : Err | forall a, ~ E y a})%type).
      { destruct (rview_eq_dec y k) as [-> | _]; [ left; exists ak; exact Hk | exact (E_dec y) ]. }
      destruct Hy as [[a Ha] | [e Hn]]; [| right; exists (y, e); split; [ left; reflexivity | exact Hn ] ].
      destruct (data_of k ak Hk ys) as [[As HAs] | [ye [Hy Hn]]]; [ left; exists (a :: As); constructor; assumption |].
      right; exists ye; split; [ right; exact Hy | exact Hn ].
  Defined.

  (** What the search returns from the views [Vs] found and the queue
      [tr]: the views [Vf] (with their data [Af]) of a run of [views_bfs]
      at the tables of the data, or a view with no data (with why) and a
      refutation of every run whose tables agree with [E] and whose views
      all have data. *)
  Definition result (Vs tr : list rview) : Type :=
    ({p : prod (list rview) (list A) |
      NoDup (fst p) /\ Forall2 E (fst p) (snd p) /\
      views_bfs (sibs_tbl (fst p) (List.map sibs_of (snd p))) (mtbl (fst p) (List.map meets_of (snd p))) Vs tr (fst p)}
    + {ye : rview * Err | forall sibs meets Vf, views_bfs sibs meets Vs tr Vf ->
        (forall y a, In y Vf -> E y a -> sibs y = sibs_of a /\ meets y = meets_of a) ->
        (forall y, In y Vf -> exists a, E y a) -> False})%type.

  Lemma views_met_new : forall sibs Vs x, ~ In x Vs -> views_met sibs Vs x = views_new Vs (sibs x ++ [x]).
  Proof.
    intros * Hx; unfold views_met; destruct (rview_mem x Vs) eqn:Hm; [| reflexivity ].
    exfalso; apply Hx, rview_mem_spec, Hm.
  Qed.

  Lemma views_met_old : forall sibs Vs x, In x Vs -> views_met sibs Vs x = nil.
  Proof. intros * Hx; unfold views_met; apply rview_mem_spec in Hx; rewrite Hx; reflexivity. Qed.

  Lemma in_views_met : forall sibs Vs x, ~ In x Vs -> In x (views_met sibs Vs x).
  Proof.
    intros * Hx; rewrite views_met_new by exact Hx.
    destruct (views_new_in Vs (sibs x ++ [x]) x ltac:(apply in_or_app; right; left; reflexivity)); tauto.
  Qed.

  Lemma map_tbl : forall Vf Af ys bs, NoDup Vf -> Forall2 E Vf Af -> incl ys Vf -> Forall2 E ys bs ->
      List.map (mtbl Vf (List.map meets_of Af)) ys = List.map meets_of bs.
  Proof.
    intros * Hd HF Hi Hy; induction Hy as [| y b ys bs Hb Hys IH]; cbn; [ reflexivity |].
    f_equal; [ apply (tbl_at _ _ _ _ HF (Hi y (or_introl eq_refl)) Hb) | apply IH; intros z Hz; apply Hi; right; exact Hz ].
  Qed.

  (** The search, by recursion on the accessibility proof. *)
  Fixpoint search (Vs : list rview) (As : list A) (tr : list rview)
      (Hd : NoDup Vs) (HF : Forall2 E Vs As) (Hr : forall y, In y Vs -> reach y)
      (Ht : forall y, In y tr -> reach y) (Hacc : Acc search_lt (Vs, tr)) {struct Hacc} : result Vs tr.
  Proof.
    destruct Hacc as [Hacc].
    destruct tr as [| x tr'].
    { left; exists (Vs, As); cbn; split; [ exact Hd | split; [ exact HF | constructor ] ]. }
    destruct (in_dec rview_eq_dec x Vs) as [Hx | Hx].
    - (* met already: nothing found, the queue shrinks *)
      refine (match search Vs As tr' Hd HF Hr (fun y Hy => Ht y (or_intror Hy)) (Hacc (Vs, tr') _) with
              | inl p => inl _ | inr Hf => inr _ end).
      + split; [ split; assumption | right; cbn; split; [ reflexivity | lia ] ].
      + destruct p as [[Vf Af] (Hd' & HF' & Hb)]; exists (Vf, Af); cbn in *; split; [ exact Hd' | split; [ exact HF' |] ].
        apply views_bfs_step; rewrite views_met_old by exact Hx; cbn; rewrite !app_nil_r; exact Hb.
      + destruct Hf as [ye Hf]; exists ye.
        intros sibs meets Vf Hb Hag Hex; inversion Hb; subst.
        rewrite views_met_old in * by exact Hx; cbn in *; rewrite !app_nil_r in *.
        eapply Hf; eassumption.
    - destruct (E_dec x) as [[ax Hax] | [e Hn]].
      2:{ right; exists (x, e); intros sibs meets Vf Hb Hag Hex; inversion Hb; subst.
          destruct (Hex x) as [a Ha]; [| exact (Hn a Ha) ].
          eapply views_bfs_incl; [ eassumption | apply in_or_app; right; apply in_views_met, Hx ]. }
      remember (views_new Vs (sibs_of ax ++ [x])) as nw eqn:Hnw.
      assert (Hxnew : In x nw).
      { rewrite Hnw; destruct (views_new_in Vs (sibs_of ax ++ [x]) x ltac:(apply in_or_app; right; left; reflexivity)); tauto. }
      destruct (data_of x ax Hax nw) as [[bs Hbs] | [ye [Hy Hny]]].
      2:{ right; exists ye; intros sibs meets Vf Hb Hag Hex; inversion Hb; subst.
          assert (HxVf : In x Vf) by (eapply views_bfs_incl; [ eassumption | apply in_or_app; right; apply in_views_met, Hx ]).
          rewrite views_met_new, (proj1 (Hag x ax HxVf Hax)) in * by exact Hx.
          destruct (Hex (fst ye)) as [b Hb']; [| exact (Hny b Hb') ].
          eapply views_bfs_incl; [ eassumption | apply in_or_app; right; exact Hy ]. }
      assert (Hrnew : forall y, In y nw -> reach y)
        by (intros y Hy; rewrite Hnw in Hy; apply views_new_incl in Hy;
            eapply reach_sib; [ apply Ht; left; reflexivity | exact Hax | exact Hy ]).
      assert (Hok : found_ok (Vs ++ nw)).
      { split; [ rewrite Hnw; apply views_new_nodup, Hd |].
        intros y Hy; apply in_app_or in Hy as [Hy | Hy]; auto. }
      assert (Htr : forall y, In y (tr' ++ List.concat (List.map meets_of bs)) -> reach y).
      { intros y Hy; apply in_app_or in Hy as [Hy | Hy]; [ apply Ht; right; exact Hy |].
        apply in_concat in Hy as (ms & Hms & Hy); apply in_map_iff in Hms as (b & <- & Hb).
        destruct (In_nth_error _ _ Hb) as [v Hv].
        destruct (Forall2_nth _ _ _ _ _ (Forall2_flip Hbs) Hv) as (z & Hz & Hzb).
        eapply reach_meet; [ apply Hrnew, (nth_error_In _ _ Hz) | exact Hzb | exact Hy ]. }
      assert (Hlt : search_lt (Vs ++ nw, tr' ++ List.concat (List.map meets_of bs)) (Vs, x :: tr')).
      { split; [ exact Hok | left; cbn; split; [ intros y Hy; apply in_or_app; left; exact Hy |] ].
        rewrite length_app; destruct nw; [ destruct Hxnew | cbn; lia ]. }
      refine (match search (Vs ++ nw) (As ++ bs) (tr' ++ List.concat (List.map meets_of bs))
                (proj1 Hok) (Forall2_app HF Hbs) (proj2 Hok) Htr (Hacc _ Hlt) with
              | inl p => inl _ | inr Hf => inr _ end).
      + destruct p as [[Vf Af] (Hd' & HF' & Hb)]; exists (Vf, Af); cbn in *; split; [ exact Hd' | split; [ exact HF' |] ].
        assert (Hinc : incl (Vs ++ nw) Vf) by (intros y Hy; eapply views_bfs_incl; eassumption).
        apply views_bfs_step; rewrite views_met_new by exact Hx.
        rewrite (proj1 (tbl_at _ _ _ _ HF' (Hinc x ltac:(apply in_or_app; right; exact Hxnew)) Hax)).
        rewrite <- Hnw, (map_tbl _ _ _ _ Hd' HF' (fun y Hy => Hinc y (in_or_app _ _ _ (or_intror Hy))) Hbs); exact Hb.
      + destruct Hf as [ye Hf]; exists ye.
        intros sibs meets Vf Hb Hag Hex; inversion Hb; subst.
        assert (HxVf : In x Vf) by (eapply views_bfs_incl; [ eassumption | apply in_or_app; right; apply in_views_met, Hx ]).
        rewrite views_met_new, (proj1 (Hag x ax HxVf Hax)) in * by exact Hx.
        assert (Hm : List.map meets (views_new Vs (sibs_of ax ++ [x])) = List.map meets_of bs).
        { assert (Hi : incl (views_new Vs (sibs_of ax ++ [x])) Vf)
            by (intros y Hy; eapply views_bfs_incl; [ eassumption | apply in_or_app; right; exact Hy ]).
          clear - Hbs Hag Hi; revert Hi; induction Hbs as [| y b ys bs' Hyb _ IH]; intros Hi; cbn; [ reflexivity |].
          f_equal; [ exact (proj2 (Hag y b (Hi y (or_introl eq_refl)) Hyb)) | apply IH; intros z Hz; apply Hi; right; exact Hz ]. }
        rewrite Hm in *; eapply Hf; eassumption.
  Defined.

  (** The search from no view found and the declared members' instances,
      given that the reachable views are finitely many. *)
  Definition views_search_from (Hfin : exists L, forall y, reach y -> In y L) : result nil init :=
    search nil nil init (NoDup_nil _) (Forall2_nil _) (fun y H => match H with end)
      (fun y H => reach_init y H) (search_acc Hfin nil init).

  (** ** Finiteness from Clusters *)

  (** The views reachable from one view. *)
  Inductive reach_from (x : rview) : rview -> Prop :=
  (** The view itself *)
  | reach_from_self : reach_from x x
  (** A sibling of a view reachable from [x], or that view *)
  | reach_from_sib : forall y a w, reach_from x y -> E y a -> In w (sibs_of a ++ y :: nil) -> reach_from x w
  (** An instance a view reachable from [x] meets *)
  | reach_from_meet : forall y a w, reach_from x y -> E y a -> In w (meets_of a) -> reach_from x w.

  Lemma reach_from_trans : forall x y w, reach_from x y -> reach_from y w -> reach_from x w.
  Proof.
    intros x y w Hxy Hyw; induction Hyw as [| y' a w Hy IH He Hw | y' a w Hy IH He Hw ];
      [ exact Hxy | eapply reach_from_sib | eapply reach_from_meet ]; eassumption.
  Qed.

  (** Finitely many views are reachable from [x]. *)
  Definition fin_from (x : rview) : Prop := exists L, forall y, reach_from x y -> In y L.

  (** The views of a list that the queue reaches, each either known by
      [Q] or with finitely many reachable views: one list holds all of
      those. *)
  Lemma cover : forall (Q : rview -> Prop) (ys : list rview),
      (forall y, In y ys -> Q y \/ fin_from y) ->
      exists L, forall y, In y ys -> Q y \/ forall w, reach_from y w -> In w L.
  Proof.
    intros Q ys; induction ys as [| y ys IH]; intros H; [ exists nil; intros ? [] |].
    destruct IH as [L HL]; [ intros; apply H; right; assumption |].
    destruct (H y (or_introl eq_refl)) as [HQ | [Ly HLy]].
    - exists L; intros y' [<- | Hin]; [ left; exact HQ | exact (HL _ Hin) ].
    - exists (Ly ++ L); intros y' [<- | Hin].
      + right; intros w Hw; apply in_or_app; left; exact (HLy _ Hw).
      + destruct (HL _ Hin) as [HQ | Hf]; [ left; exact HQ | right; intros w Hw; apply in_or_app; right; exact (Hf _ Hw) ].
  Qed.

  (** The instances the views of [L] that have data meet. *)
  Definition all_meets (L : list rview) : list rview :=
    List.concat (List.map (fun y => match E_dec y with inl (exist _ a _) => meets_of a | inr _ => nil end) L).

  Lemma in_all_meets : forall L y a z, In y L -> E y a -> In z (meets_of a) -> In z (all_meets L).
  Proof.
    intros * Hy Ha Hz; unfold all_meets; apply in_concat.
    exists (match E_dec y with inl (exist _ a _) => meets_of a | inr _ => nil end); split; [ apply in_map_iff; exists y; split; [ reflexivity | exact Hy ] |].
    destruct (E_dec y) as [[a' Ha'] | [e Hn]]; [ rewrite (E_functional _ _ _ Ha' Ha); exact Hz | exfalso; exact (Hn a Ha) ].
  Qed.

  Lemma all_meets_in : forall L z, In z (all_meets L) -> exists y a, In y L /\ E y a /\ In z (meets_of a).
  Proof.
    intros * Hz; unfold all_meets in Hz; apply in_concat in Hz as (ms & Hms & Hz).
    apply in_map_iff in Hms as (y & <- & Hy).
    destruct (E_dec y) as [[a Ha] | [e Hn]]; [ exists y, a; auto | destruct Hz ].
  Qed.

  (** Every view a view of [L] reaches is in [L], or reached from a view
      each of whose reachable views is in [L']: so in [L ++ L']. *)
  Lemma fin_of_anchor : forall x L L', (forall w, reach_from x w -> In w L \/
        exists u, (forall w', reach_from u w' -> In w' L') /\ reach_from u w) ->
      fin_from x.
  Proof.
    intros * H; exists (L ++ L'); intros w Hw; apply in_or_app.
    destruct (H w Hw) as [Hin | (u & Hu & Huw)]; [ left; exact Hin | right; exact (Hu _ Huw) ].
  Qed.

  Section Clusters.
    (** The views of the invariant: those whose data is read off the PER
        model. *)
    Variable Inv : rview -> Prop.
    (** The order the meets leaving a cluster descend. *)
    Variable lt : rview -> rview -> Prop.

    (** [L] is a cluster of the view [x]. *)
    Record cluster_of (x : rview) (L : list rview) : Prop := mk_cluster_of
      { (** It holds [x] *)
        cluster_self : In x L
        (** Its views are of the invariant *)
      ; cluster_inv : forall y, In y L -> Inv y
        (** It holds the siblings of its views *)
      ; cluster_closed : forall y ay, In y L -> E y ay -> incl (sibs_of ay ++ y :: nil) L
        (** The instances its views meet are in it, or below [x] *)
      ; cluster_meets : forall y ay z, In y L -> E y ay -> In z (meets_of ay) -> In z L \/ lt z x }.

    Hypothesis lt_acc : forall x, Inv x -> Acc lt x.
    (** A view of the invariant has a cluster. *)
    Hypothesis cluster : forall x, Inv x -> exists L, cluster_of x L.
    (** The instances any view meets are of the invariant. *)
    Hypothesis meets_inv : forall x ax z, E x ax -> In z (meets_of ax) -> Inv z.
    (** The siblings of any view are of the invariant, or have its
        siblings. *)
    Hypothesis sibs_inv : forall x ax y, E x ax -> In y (sibs_of ax ++ x :: nil) ->
      Inv y \/ forall ay, E y ay -> incl (sibs_of ay ++ y :: nil) (sibs_of ax ++ x :: nil).

    (** From a view of the invariant, finitely many views are reachable:
        its cluster, and those reachable from the meets below it. *)
    Lemma fin_of_inv : forall x, Inv x -> fin_from x.
    Proof.
      intros x Hx; pose proof (lt_acc x Hx) as Hacc; revert Hx; induction Hacc as [x _ IH]; intros Hx.
      destruct (cluster x Hx) as [L HL].
      destruct (cover (fun z => In z L) (all_meets L)) as [LL HLL].
      { intros z Hz; destruct (all_meets_in _ _ Hz) as (y & a & Hy & Ha & Hza).
        destruct (cluster_meets _ _ HL _ _ _ Hy Ha Hza) as [Hin | Hlt]; [ left; exact Hin |].
        right; apply IH; [ exact Hlt | exact (meets_inv _ _ _ Ha Hza) ]. }
      apply (fin_of_anchor x L LL); intros w Hw.
      induction Hw as [| y a w Hy IHy Ha Hw | y a w Hy IHy Ha Hw].
      - left; exact (cluster_self _ _ HL).
      - destruct IHy as [HyL | (u & Hu & Huy)].
        + left; exact (cluster_closed _ _ HL _ _ HyL Ha _ Hw).
        + right; exists u; split; [ exact Hu | eapply reach_from_sib; eassumption ].
      - destruct IHy as [HyL | (u & Hu & Huy)].
        + destruct (HLL w (in_all_meets _ _ _ _ HyL Ha Hw)) as [HwL | Hf]; [ left; exact HwL |].
          right; exists w; split; [ exact Hf | apply reach_from_self ].
        + right; exists u; split; [ exact Hu | eapply reach_from_meet; eassumption ].
    Qed.

    (** From any view, finitely many views are reachable: its siblings, and
        those reachable from the siblings of the invariant and from the
        instances the siblings meet. *)
    Lemma fin_of_any : forall x, fin_from x.
    Proof.
      intros x; destruct (E_dec x) as [[ax Hax] | [e Hn]].
      - set (C := sibs_of ax ++ x :: nil).
        destruct (cover (fun y => forall ay, E y ay -> incl (sibs_of ay ++ y :: nil) C) C) as [LC HLC].
        { intros y Hy; destruct (sibs_inv _ _ _ Hax Hy) as [Hi | Hs]; [ right; exact (fin_of_inv _ Hi) | left; exact Hs ]. }
        destruct (cover (fun _ => False) (all_meets C)) as [LM HLM].
        { intros z Hz; destruct (all_meets_in _ _ Hz) as (y & a & Hy & Ha & Hza).
          right; exact (fin_of_inv _ (meets_inv _ _ _ Ha Hza)). }
        apply (fin_of_anchor x C (LC ++ LM)); intros w Hw.
        induction Hw as [| y a w Hy IHy Ha Hw | y a w Hy IHy Ha Hw].
        + left; apply in_or_app; right; left; reflexivity.
        + destruct IHy as [HyC | (u & Hu & Huy)].
          * destruct (HLC y HyC) as [Hs | Hf]; [ left; exact (Hs _ Ha _ Hw) |].
            right; exists y; split; [ intros w' Hw'; apply in_or_app; left; exact (Hf _ Hw') |].
            eapply reach_from_sib; [ apply reach_from_self | exact Ha | exact Hw ].
          * right; exists u; split; [ exact Hu | eapply reach_from_sib; eassumption ].
        + destruct IHy as [HyC | (u & Hu & Huy)].
          * destruct (HLM w (in_all_meets _ _ _ _ HyC Ha Hw)) as [[] | Hf].
            right; exists w; split; [ intros w' Hw'; apply in_or_app; right; exact (Hf _ Hw') | apply reach_from_self ].
          * right; exists u; split; [ exact Hu | eapply reach_from_meet; eassumption ].
      - exists (x :: nil); intros w Hw.
        assert (Hx : w = x).
        { induction Hw as [| y a w Hy IHy Ha Hw | y a w Hy IHy Ha Hw]; [ reflexivity | |];
            subst y; exfalso; exact (Hn a Ha). }
        subst w; left; reflexivity.
    Qed.

    Lemma reach_from_init : forall y, reach y -> exists x, In x init /\ reach_from x y.
    Proof.
      induction 1 as [x Hx | x a y Hx IH Ha Hy | x a y Hx IH Ha Hy].
      - exists x; split; [ exact Hx | apply reach_from_self ].
      - destruct IH as (x0 & Hx0 & Hr); exists x0; split; [ exact Hx0 | eapply reach_from_sib; eassumption ].
      - destruct IH as (x0 & Hx0 & Hr); exists x0; split; [ exact Hx0 | eapply reach_from_meet; eassumption ].
    Qed.

    (** So the views reachable from the queue are finitely many. *)
    Theorem reach_finite_of_clusters : exists L, forall y, reach y -> In y L.
    Proof.
      destruct (cover (fun _ => False) init) as [L HL]; [ intros y _; right; apply fin_of_any |].
      exists L; intros y Hy; destruct (reach_from_init _ Hy) as (x & Hx & Hr).
      destruct (HL _ Hx) as [[] | Hf]; exact (Hf _ Hr).
    Qed.
  End Clusters.
End Search.
