(** * Finding the Views of a Group Declaration

    The search of [ViewsSearch] instantiated with the data the declaration
    asks of each view ([view_sibs], [view_cls], [view_nps], decided by
    [IndDecl]), and its termination: the views reachable from the
    declaration's own instances are finitely many
    ([views_reach_finite]), by [ViewsSearch.reach_finite_of_clusters] on
    the clusters of [ViewsCluster] and the order [view_lt]. *)

From Stdlib Require Import Lia List PeanoNat String.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Inductives Require Import Group.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Core.Completeness.Inductives Require Import Elim.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Extraction Require Import Lookup GlobalCheck IndDecl ViewsSearch ViewsReach ViewsCluster.
From Mctt.Extraction Require Command.
#[local] Open Scope list_scope.

(** The data a view has: its siblings, its classified constructors and
    its filed non-uniform parameters. *)
Record view_data : Type := mk_view_data
  { (** The siblings *)
    data_sibs : list view_key
    (** The constructors, classified *)
  ; data_cons : list (string * list rcarg)
    (** The non-uniform parameters, filed *)
  ; data_nparams : ctx }.

(** [a] is the data of the view [x] of the declaration [R]. *)
Record view_data_ok (Θ : gdeps) (Ξ : gstack) (R : raw_decl) (x : view_key) (a : view_data) : Prop := mk_view_data_ok
  { (** Its siblings *)
    data_ok_sibs : view_sibs Θ Ξ R x (data_sibs a)
    (** Its constructors *)
  ; data_ok_cons : view_cls Θ Ξ R x (data_cons a)
    (** Its non-uniform parameters *)
  ; data_ok_nparams : view_nps Θ Ξ R x (data_nparams a) }.

(** The instances a view's constructors meet. *)
Definition data_meets (a : view_data) : list view_key := rcons_views (data_cons a).

Lemma view_data_functional : forall Θ Ξ R x a a', view_data_ok Θ Ξ R x a -> view_data_ok Θ Ξ R x a' -> a = a'.
Proof.
  intros * [Hs Hc Hn] [Hs' Hc' Hn']; destruct a, a'; cbn in *.
  rewrite (view_sibs_functional _ _ _ _ _ _ Hs Hs'), (view_cls_functional _ _ _ _ _ _ Hc Hc'),
    (view_nps_functional _ _ _ _ _ _ Hn Hn'); reflexivity.
Qed.

(** The data of a view, or why it has none: its siblings first, then its
    constructors, then its parameters, looked up at the fast context
    [F]. *)
Definition view_data_dec (F : FCtx) (HΞ : ⊢ᵍ fc_deps F ⍮ fc_stack F) (R : raw_decl) (x : view_key) :
    ({a | view_data_ok (fc_deps F) (fc_stack F) R x a} + {e : view_why | forall a, ~ view_data_ok (fc_deps F) (fc_stack F) R x a})%type.
Proof.
  destruct (view_sibs_dec F HΞ R x) as [[ss Hs] | [e He]];
    [| right; exists e; intros a Ha; exact (He _ (data_ok_sibs _ _ _ _ _ Ha)) ].
  destruct (view_cls_dec F HΞ R x) as [[cs Hc] | [e He]];
    [| right; exists e; intros a Ha; exact (He _ (data_ok_cons _ _ _ _ _ Ha)) ].
  destruct (view_nps_dec F HΞ R x) as [[Nv Hn] | [e He]];
    [| right; exists e; intros a Ha; exact (He _ (data_ok_nparams _ _ _ _ _ Ha)) ].
  left; exists (mk_view_data ss cs Nv); constructor; assumption.
Defined.

(** ** The Clusters *)

Section Clusters.
  (** The fast context the views' data are looked up in; the judgments
      are at the Core context it stands for. *)
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).
  Hypothesis HΞ : ⊢ᵍ Θ ⍮ Ξ.
  Variable R : raw_decl.

  (** The views whose data the PER model reads: typed views whose
      arguments are their own normal forms, over the declaration's
      context. *)
  Definition view_good (x : view_key) : Prop := key_inv Θ Ξ (rd_uctx Ξ R) x.

  (** A sibling of a good view, in its context if well formed, is good. *)
  Lemma sib_good : forall qx kx Cs D i M y, view_good (vk_ind qx kx Cs) -> ind_lookup Θ Ξ qx = Some D -> ind_member D i = Some M ->
      sib_entry Θ Ξ (rd_uctx Ξ R) qx Cs i M y -> view_good y.
  Proof.
    intros * [[D' Hl' Hk HCl HCt HΓu] Ws HWs HCs] Hl HM Hse.
    rewrite Hl in Hl'; injection Hl' as <-.
    destruct (decl_of_glookup _ _ _ _ HΞ Hl) as [Hdt _].
    inversion Hse as [? ? pm Hh | ? ? qv kv Iv vmv Dv Wv Hh Hlv Hnv | ? ? qr Ir fl Rr Wr Hh Hlr Hnr]; subst; cbn [view_good key_inv].
    - assert (Hd : im_is_decl M = true) by (unfold im_is_decl; rewrite Hh; reflexivity).
      apply (decl_typed_order _ _ _ Hdt _ _ HM) in Hd.
      exact (mk_view_inv _ _ _ _ _ _ (mk_view_typed _ _ _ _ _ _ D Hl Hd HCl HCt HΓu) Ws HWs eq_refl).
    - exact (@sib_view_inv (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ _ _ _ _ HΞ HΓu Hl HM Hh Hlv Hnv).
    - exact (@sib_record_inv (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ _ _ _ HΞ HΓu Hl HM Hh Hlr Hnr).
  Qed.

  (** The data of a record view: itself its only sibling, its constructor
      its record's fields at its instance. *)
  Lemma record_view_data : forall qx Isx a, view_data_ok Θ Ξ R (vk_record qx Isx) a ->
      data_sibs a = vk_record qx Isx :: nil /\
      exists Rx, record_lookup Θ Ξ qx = Some Rx /\
        cls_cons_in Θ Ξ (rd_uctx Ξ R) (rd_nu R) (rd_nu R) (rd_n R)
          ((rview_con, ctx_args (tele_sub (record_fctx Rx (List.length (record_fields Rx))) (sb_of_list sb_id Isx))) :: nil)
          (data_cons a).
  Proof.
    intros * [Hs Hc _].
    inversion Hs; subst; split; [ reflexivity |].
    inversion Hc as [| ? ? Rx cs Hl Hcls]; subst; exists Rx; split; assumption.
  Qed.

  (** A good view has a cluster: its siblings and itself. *)
  Theorem views_cluster : forall x, view_good x ->
      exists L, cluster_of view_data (view_data_ok Θ Ξ R) data_sibs data_meets view_good (view_lt Θ Ξ (rd_uctx Ξ R)) x L.
  Proof.
    intros x Hx.
    destruct (view_data_dec F HΞ R x) as [[a Ha] | [e Hn]].
    2:{ (** no data: the view alone *)
        exists (x :: nil); constructor.
        - left; reflexivity.
        - intros y [<- | []]; exact Hx.
        - intros y ay [<- | []] Hay; exfalso; exact (Hn _ Hay).
        - intros y ay z [<- | []] Hay; exfalso; exact (Hn _ Hay). }
    destruct x as [qx kx Cs | qx Isx].
    2:{ (** a record view: itself alone, whose meets are below it *)
        exists (vk_record qx Isx :: nil); constructor.
        - left; reflexivity.
        - intros y [<- | []]; exact Hx.
        - intros y ay [<- | []] Hay; destruct (record_view_data _ _ _ Hay) as [-> _].
          intros w [<- | [<- | []]]; left; reflexivity.
        - intros y ay z [<- | []] Hay Hz; right.
          destruct (record_view_data _ _ _ Hay) as [_ (Rx & Hl & Hcls)].
          exact (@record_view_meets_below (gc_mk Θ Ξ) (rd_uctx Ξ R) qx Isx Rx (data_cons ay) (rd_nu R) (rd_n R) z
                   HΞ (record_inv_typed _ _ _ _ _ Hx) Hl Hcls Hz). }
    pose proof Hx as Hx'; destruct Hx' as [[D Hl Hk HCl HCt HΓu] Ws HWs HCs].
    pose proof Ha as [Hs _ _].
    inversion Hs as [? ? ? D' ss' Hl' Hss |]; subst.
    rewrite Hl in Hl'; injection Hl' as <-.
    exists (data_sibs a ++ vk_ind qx kx (List.map nf_to_exp Ws) :: nil); constructor.
    - apply List.in_or_app; right; left; reflexivity.
    - (** the siblings of a good view are good *)
      intros y Hy; apply List.in_app_or in Hy as [Hy | [<- | []]]; [| exact Hx ].
      destruct (sibs_from_in _ _ _ _ _ _ _ _ Hss _ Hy) as (j & M & HM & _ & Hse).
      exact (sib_good _ _ _ _ _ _ _ Hx Hl HM Hse).
    - (** the siblings of the siblings are siblings *)
      intros y ay Hy Hay z Hz.
      apply List.in_app_or in Hy as [Hy | [<- | []]].
      2:{ rewrite (view_data_functional _ _ _ _ _ _ Hay Ha) in Hz; exact Hz. }
      destruct (sibs_from_in _ _ _ _ _ _ _ _ Hss _ Hy) as (j & M & HM & _ & Hse).
      apply List.in_or_app; left.
      inversion Hse as [? ? pm Hh | ? ? qv kv Iv vmv Dv Wv Hh Hlv Hnv | ? ? qr Ir fl Rr Wr Hh Hlr Hnr]; subst.
      + rewrite (view_sibs_same _ _ _ _ _ _ _ _ _ (data_ok_sibs _ _ _ _ _ Hay) Hs) in Hz.
        apply List.in_app_or in Hz as [Hz | [<- | []]]; assumption.
      + pose proof (data_ok_sibs _ _ _ _ _ Hay) as Hsy.
        inversion Hsy as [? ? ? Dv' ssy Hlv' Hssy |]; subst.
        rewrite Hlv in Hlv'; injection Hlv' as <-.
        pose proof (@view_entry_sibs (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΞ HΓu Hl HCl HCt HM Hh Hlv Hnv Hss Hssy) as Hinc.
        apply List.in_app_or in Hz as [Hz | [<- | []]]; [ exact (Hinc _ Hz) | exact Hy ].
      + (** a record view: itself alone *)
        destruct (record_view_data _ _ _ Hay) as [Esy _]; rewrite Esy in Hz.
        destruct Hz as [<- | [<- | []]]; exact Hy.
    - (** the instances they meet are siblings, or below the view *)
      intros y ay z Hy Hay Hz; unfold data_meets in Hz.
      pose proof (data_ok_cons _ _ _ _ _ Hay) as Hcy.
      assert (Hin : forall z', In z' (data_sibs a) -> In z' (data_sibs a ++ vk_ind qx kx (List.map nf_to_exp Ws) :: nil))
        by (intros; apply List.in_or_app; left; assumption).
      apply List.in_app_or in Hy as [Hy | [<- | []]].
      2:{ inversion Hcy as [? ? ? D'' Mk' cs' Hl'' HMk' Hcls |]; subst.
          rewrite Hl in Hl''; injection Hl'' as <-.
          destruct (@member_meets (gc_mk Θ Ξ) (rd_uctx Ξ R) qx D kx _ Ws (data_sibs a) kx Mk' (data_cons ay) (rd_nu R) (rd_n R) z
                      HΞ HΓu Hl HCl HCt (HWs D Hl) eq_refl Hss HMk' Hcls Hz)
            as [Hz' | Hlt]; [ left; exact (Hin _ Hz') | right; exact Hlt ]. }
      destruct (sibs_from_in _ _ _ _ _ _ _ _ Hss _ Hy) as (j & M & HM & _ & Hse).
      inversion Hse as [? ? pm Hh | ? ? qv kv Iv vmv Dv Wv Hh Hlv Hnv | ? ? qr Ir fl Rr Wr Hh Hlr Hnr]; subst.
      + inversion Hcy as [? ? ? D'' Mk' cs' Hl'' HMk' Hcls |]; subst.
        rewrite Hl in Hl''; injection Hl'' as <-.
        destruct (@member_meets (gc_mk Θ Ξ) (rd_uctx Ξ R) qx D kx _ Ws (data_sibs a) j Mk' (data_cons ay) (rd_nu R) (rd_n R) z
                    HΞ HΓu Hl HCl HCt (HWs D Hl) eq_refl Hss HMk' Hcls Hz)
          as [Hz' | Hlt]; [ left; exact (Hin _ Hz') | right; exact Hlt ].
      + inversion Hcy as [? ? ? D'' My cs' Hl'' HMy Hcls |]; subst.
        rewrite Hlv in Hl''; injection Hl'' as <-.
        destruct (@view_sib_meets (gc_mk Θ Ξ) (rd_uctx Ξ R) qx D kx _ Ws (data_sibs a) j M qv kv Iv vmv Dv Wv My (data_cons ay)
                    (rd_nu R) (rd_n R) z HΞ HΓu Hl HCl HCt (HWs D Hl) eq_refl Hss HM Hh Hlv Hnv HMy Hcls Hz)
          as [Hz' | Hlt]; [ left; exact (Hin _ Hz') | right; exact Hlt ].
      + destruct (record_view_data _ _ _ Hay) as [_ (Rr' & Hlr' & Hcls)].
        rewrite Hlr in Hlr'; injection Hlr' as <-.
        destruct (@record_sib_meets (gc_mk Θ Ξ) (rd_uctx Ξ R) qx D kx _ Ws (data_sibs a) j M qr Ir fl Rr Wr (data_cons ay)
                    (rd_nu R) (rd_n R) z HΞ HΓu Hl HCl HCt (HWs D Hl) eq_refl Hss HM Hh Hlr Hnr Hcls Hz)
          as [Hz' | Hlt]; [ left; exact (Hin _ Hz') | right; exact Hlt ].
  Qed.

  (** The instances any view meets are good. *)
  Lemma views_meets_good : forall x ax z, view_data_ok Θ Ξ R x ax -> In z (data_meets ax) -> view_good z.
  Proof. intros * Hx Hz; exact (view_meets_inv _ _ _ _ _ _ (data_ok_cons _ _ _ _ _ Hx) Hz). Qed.

  (** The siblings of any view are good, or have no siblings but its
      siblings. *)
  Lemma views_sibs_good : forall x ax y, view_data_ok Θ Ξ R x ax -> In y (data_sibs ax ++ x :: nil) ->
      view_good y \/ forall ay, view_data_ok Θ Ξ R y ay -> incl (data_sibs ay ++ y :: nil) (data_sibs ax ++ x :: nil).
  Proof.
    intros x ax y Hx Hy.
    apply List.in_app_or in Hy as [Hy | [<- | []]].
    2:{ right; intros ay Hay; rewrite (view_data_functional _ _ _ _ _ _ Hay Hx); apply incl_refl. }
    destruct x as [qx kx Cs | qx Isx].
    2:{ (** a record view: itself alone *)
        destruct (record_view_data _ _ _ Hx) as [Es _]; rewrite Es in Hy; destruct Hy as [<- | []].
        right; intros ay Hay; rewrite (view_data_functional _ _ _ _ _ _ Hay Hx); apply incl_refl. }
    pose proof (data_ok_sibs _ _ _ _ _ Hx) as Hs.
    inversion Hs as [? ? ? D ss Hl Hss |]; subst.
    destruct (sibs_from_in _ _ _ _ _ _ _ _ Hss _ Hy) as (j & M & HM & _ & Hse).
    inversion Hse as [? ? pm Hh | ? ? qv kv Iv vmv Dv Wv Hh Hlv Hnv | ? ? qr Ir fl Rr Wr Hh Hlr Hnr]; subst.
    - (** a declared member: the same siblings *)
      right; intros ay Hay.
      rewrite (view_sibs_same _ _ _ _ _ _ _ _ _ (data_ok_sibs _ _ _ _ _ Hay) Hs).
      intros w Hw; apply List.in_app_or in Hw as [Hw | [<- | []]]; apply List.in_or_app; left; assumption.
    - destruct (check_ctx F HΞ (rd_uctx Ξ R)) as [HΓu | HΓu].
      + (** a view in a well-formed context: good *)
        left; exact (@sib_view_inv (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ _ _ _ _ HΞ HΓu Hl HM Hh Hlv Hnv).
      + (** a view in an ill-formed one: siblings of the view *)
        right; intros ay Hay.
        pose proof (data_ok_sibs _ _ _ _ _ Hay) as Hsy.
        inversion Hsy as [? ? ? Dv' ssy Hlv' Hssy |]; subst.
        rewrite Hlv in Hlv'; injection Hlv' as <-.
        pose proof (@view_entry_sibs_ill (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΞ HΓu Hl HM Hh Hlv Hnv Hss Hssy) as Hinc.
        intros w Hw; apply List.in_app_or in Hw as [Hw | [<- | []]]; apply List.in_or_app; left; [ exact (Hinc _ Hw) | exact Hy ].
    - (** a record view: itself alone, a sibling *)
      right; intros ay Hay; destruct (record_view_data _ _ _ Hay) as [Esy _]; rewrite Esy.
      intros w [<- | [<- | []]]; apply List.in_or_app; left; exact Hy.
  Qed.

  (** Good views are accessible for the nesting order. *)
  Lemma views_lt_acc : forall x, view_good x -> Acc (view_lt Θ Ξ (rd_uctx Ξ R)) x.
  Proof. intros x Hx; exact (key_inv_acc _ _ _ _ HΞ Hx). Qed.

  (** ** Termination

      From the instances the declared members' constructors meet, the
      search reaches finitely many views.

      Informally, a declaration has a nesting budget.  Each container [C]
      gets a measure [m_C], computed in filing order, so the containers a
      group nests through are measured before it:
      - an occurrence of the group's own members counts nothing;
      - an occurrence of a parameter costs what the parameter does: a
        parameter of a type is the identity;
      - a parameter of a function type gets a function measure, and
        applying it composes;
      - an occurrence of a container [C'] at arguments costs one more than
        [m_C'] at the arguments' measures.
      The views a declaration finds are at most its budget's levels.  For
      instance, with
      - [E (G) | mkE (y : G ℕ)],
      - [D (F) | mkD (x : E (λY. F (F Y)))],
      - [T | t (d : D (λX. Pair X T))],
      the occurrence of [D] in [T] costs [m_D(f) = 1 + m_E(f∘f)], with
      [f] the measure of [λX. Pair X T] (one more than its argument,
      [T] itself counting nothing): [1 + (1 + f(f(0))) = 4] levels, and
      [T] has the 4 views [D] at [λX. Pair X T], [E] at
      [λY. Pair (Pair Y T) T], [Pair] at [Pair ℕ T] and [T], and [Pair]
      at [ℕ] and [T].

      The proof does not compute this budget: it uses the semantic
      measure the budget explains, the derivations of the PER model.  A
      good view's type is one of the model ([view_inv_acc], through
      [per_univ_nest_acc]); the views reachable from it within its group
      at its arguments are its cluster, its siblings ([views_cluster]);
      every instance the cluster meets outside it is a nesting step below
      it ([view_lt], by [nonrec_meet_below]); and nesting steps are well
      founded on the types of the model ([NestAcc.per_univ_nest_acc]).
      Every instance met is good ([views_meets_good]), and a sibling is
      good or has no siblings but its group's ([views_sibs_good]). *)
  Theorem views_reach_finite : forall csD, exists L,
      forall y, reach view_data (view_data_ok Θ Ξ R) data_sibs data_meets (List.concat (List.map rcons_views csD)) y -> In y L.
  Proof.
    intros csD.
    exact (reach_finite_of_clusters view_data (view_data_ok Θ Ξ R) data_sibs data_meets (view_data_functional Θ Ξ R) view_why
             (view_data_dec F HΞ R) _ view_good (view_lt Θ Ξ (rd_uctx Ξ R)) views_lt_acc views_cluster views_meets_good
             views_sibs_good).
  Qed.

  (** The search from the instances the declared members' constructors
      [csD] meet. *)
  Definition views_search_run (csD : list (list (string * list rcarg))) :
      result view_data (view_data_ok Θ Ξ R) data_sibs data_meets view_why nil (List.concat (List.map rcons_views csD)) :=
    views_search_from view_data (view_data_ok Θ Ξ R) data_sibs data_meets (view_data_functional Θ Ξ R) view_why
      (view_data_dec F HΞ R) _ (views_reach_finite csD).
End Clusters.

(** ** The Views Found, as the Checker Asks *)

(** A run of the search is one with any tables equal pointwise. *)
Lemma views_dfs_ext : forall sibs sibs' meets meets' acc tr Vs, (forall x, sibs x = sibs' x) -> (forall x, meets x = meets' x) ->
    views_dfs sibs meets acc tr Vs -> views_dfs sibs' meets' acc tr Vs.
Proof.
  intros * Hs Hm H; induction H as [acc | acc x tr Vs _ IH]; [ constructor |].
  assert (E : views_met sibs acc x = views_met sibs' acc x) by (unfold views_met; rewrite Hs; reflexivity).
  constructor; rewrite <- E, <- (List.map_ext _ _ Hm); exact IH.
Qed.

Lemma Forall2_map_impl : forall {X Y Z} (P : X -> Y -> Prop) (Q : X -> Z -> Prop) (f : Y -> Z) xs ys,
    Forall2 P xs ys -> (forall x y, P x y -> Q x (f y)) -> Forall2 Q xs (List.map f ys).
Proof. intros * H Hf; induction H; constructor; auto. Qed.

(** The name a rejected view is reported under: the declaration's first
    member's. *)
Definition rd_first_name (R : raw_decl) : string :=
  match raw_decl_members R with Mr :: _ => raw_member_name Mr | nil => ""%string end.

(** A run of the search, as the checker asks of the views. *)
Lemma views_found_ok : forall Θ Ξ R csD Vf Af, NoDup Vf -> Forall2 (view_data_ok Θ Ξ R) Vf Af ->
    views_dfs (sibs_tbl Vf (List.map data_sibs Af)) (mtbl Vf (List.map data_meets Af)) nil (List.concat (List.map rcons_views csD)) Vf ->
    Command.views_ok Θ Ξ R csD Vf (List.map data_sibs Af) (List.map data_cons Af) (List.map data_nparams Af).
Proof.
  intros * _ HF Hb; constructor.
  - exact (Forall2_map_impl _ _ _ _ _ HF (fun x a H => data_ok_sibs _ _ _ _ _ H)).
  - exact (Forall2_map_impl _ _ _ _ _ HF (fun x a H => data_ok_cons _ _ _ _ _ H)).
  - exact (Forall2_map_impl _ _ _ _ _ HF (fun x a H => data_ok_nparams _ _ _ _ _ H)).
  - eapply views_dfs_ext; [ intros; reflexivity | | exact Hb ].
    intros x; rewrite meets_tbl_mtbl, List.map_map; reflexivity.
Defined.

(** The views of a group declaration, found: the views of the search, or
    the first view it meets that has no data, with why. *)
Definition views_search (F : FCtx) (HΞ : ⊢ᵍ fc_deps F ⍮ fc_stack F) (R : raw_decl) (csD : list (list (string * list rcarg))) :
    Command.run_result (Command.views_found (fc_deps F) (fc_stack F) R csD) :=
  match views_search_run F HΞ R csD with
  | inl (exist _ (Vf, Af) (conj Hd (conj HF Hb))) =>
      Command.run_success (existT _ Vf (existT _ (List.map data_sibs Af) (existT _ (List.map data_cons Af)
        (exist _ (List.map data_nparams Af) (views_found_ok (fc_deps F) (fc_stack F) R csD Vf Af Hd HF Hb)))))
  | inr (exist _ (x, e) _) => Command.run_failure (Command.run_error_view (rd_first_name R) x e)
  end.

(** The search finds the views whenever there are some. *)
Theorem views_search_complete : forall F HΞ R csD Vs Ss csV Nvs,
    Command.views_ok (fc_deps F) (fc_stack F) R csD Vs Ss csV Nvs -> exists v, views_search F HΞ R csD = Command.run_success v.
Proof.
  intros * [Hs Hc Hn Hb]; unfold views_search.
  destruct (views_search_run F HΞ R csD) as [[[Vf Af] (Hd & HF & Hbf)] | [[x e] Hf]]; [ eexists; reflexivity |].
  exfalso; apply (Hf (sibs_tbl Vs Ss) (meets_tbl Vs csV) Vs Hb).
  - intros y a Hy Ha.
    destruct (view_key_index_in_some _ _ Hy) as [v Hv]; unfold sibs_tbl, meets_tbl, data_meets; rewrite Hv; split.
    + exact (view_sibs_functional _ _ _ _ _ _ (Forall2_index _ _ _ _ _ _ Hs Hv) (data_ok_sibs _ _ _ _ _ Ha)).
    + f_equal; exact (view_cls_functional _ _ _ _ _ _ (Forall2_index _ _ _ _ _ _ Hc Hv) (data_ok_cons _ _ _ _ _ Ha)).
  - intros y Hy; destruct (view_key_index_in_some _ _ Hy) as [v Hv].
    exists (mk_view_data (List.nth v Ss nil) (List.nth v csV nil) (List.nth v Nvs nil)); constructor; cbn.
    + exact (Forall2_index _ _ _ _ _ _ Hs Hv).
    + exact (Forall2_index _ _ _ _ _ _ Hc Hv).
    + exact (Forall2_index _ _ _ _ _ _ Hn Hv).
Qed.
