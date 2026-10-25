(** * The Nesting Order on Semantic Types Is Well Founded

    The view search of a group declaration ([views_bfs], in
    [Core.Syntactic.Inductives.Group]) starts from the nested occurrences
    written in the declaration and follows, from each instance it meets,
    the instances nested in the argument types of its constructors.  Its
    termination is read off the PER model.

    [grp_step b a]: [a] is the type value of a declared member of a filed
    group at the uniform parameters [ups], and [b] is related to the shape
    end (the end of a chain of [Π]s, read at fresh variables) of a type
    related to the value of a non-recursive argument type of a constructor
    of *any* member of that group (declared or view), at [ups] and at
    elements of the member's non-uniform parameters and of the arguments
    before ([tele_elems]).  These are the edges of the view search that
    leave a group's cluster (the members of the group at [ups]).  The
    non-uniform parameters [ns] of [a], and which declared member [a] is,
    play no part.

    Theorem [per_univ_nest_acc]: every type of the PER model, every type
    related to one, and every shape end of those, is accessible for
    [grp_step] ([nest_acc]).  The proof is the induction principle of the
    PER model ([per_univ_elem_ind]): the clause for inductive types
    carries, for every member and every constructor, the derivation of
    each non-recursive argument's type at every related environment, with
    its induction hypothesis.  Accessibility is invariant along the
    relation ([nest_acc_rel]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions.
From Equations Require Import Equations.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic Require Import PER.Tele.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section NestAcc.
  Context {GC : GCtx}.

  (** Elements of a telescope of assumptions over the values [base], built
      from the left: the next one is an element of the next entry's type at
      the ones before it. *)
  Inductive tele_elems (base : list domain) : list centry -> list domain -> Prop :=
  (** No entry, no element *)
  | tele_elems_nil : tele_elems base nil nil
  (** The next entry's type evaluates at [base] and the elements before
      it to a type of the model, and [v] is an element of it *)
  | tele_elems_snoc : forall T vs A t (i : uidx) R v,
      tele_elems base T vs ->
      ⟦ A ⟧ env_args nil (base ++ vs) ↘ t ->
      DF t ≈ t ∈ per_univ_elem i ↘ R ->
      R v v ->
      tele_elems base (T ++ ce_ass A :: nil) (vs ++ v :: nil).

  (** The end of a chain of [Π]s, each codomain read at a fresh
      variable. *)
  Inductive shape_end : domain -> domain -> Prop :=
  (** No [Π]: the type itself *)
  | se_here : forall a, shape_end a a
  (** A [Π]: the end of its codomain at a fresh variable of its domain *)
  | se_pi : forall e a ρ B n b,
      ⟦ B ⟧ ρ ↦ ⇑! a n ↘ b -> shape_end e b -> shape_end e (Πᵈ a ρ B).

  (** One step of nesting, out of a group at [ups]. *)
  Inductive grp_step : domain -> domain -> Prop :=
  (** The only rule *)
  | grp_step_intro : forall b p k D ups ns m Mm c gs j A ms vs b0 i0 R0 z e i2 R2,
      (** [a] is a member of the group [D] at [p] at [ups] *)
      ind_lookup gc_deps gc_stack p = Some D ->
      List.length ups = ind_nu D ->
      (** the [j]-th non-recursive argument [A] of the constructor [c] of
          the member [m] *)
      ind_member D m = Some Mm ->
      ind_con Mm c = Some gs ->
      List.nth_error (cargs_nonrec gs) j = Some A ->
      (** at elements of the member's non-uniform parameters and of the
          arguments before *)
      tele_elems ups (List.rev (im_nparams Mm)) ms ->
      tele_elems (ups ++ ms) (List.map ce_ass (List.firstn j (cargs_nonrec gs))) vs ->
      ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b0 ->
      (** [b] is related to a shape end of a type related to it *)
      DF z ≈ b0 ∈ per_univ_elem i0 ↘ R0 ->
      shape_end e z ->
      DF b ≈ e ∈ per_univ_elem i2 ↘ R2 ->
      grp_step b (d_ind p k (ups ++ ns)).

  (** Accessibility for [grp_step]. *)
  Inductive nest_acc : domain -> Prop :=
  (** The only rule: every step out of [a] is accessible *)
  | nest_acc_intro : forall a, (forall b, grp_step b a -> nest_acc b) -> nest_acc a.

  Lemma nest_acc_non_ind : forall a, (forall p k us, a <> d_ind p k us) -> nest_acc a.
  Proof. intros a Ha; constructor; intros b Hb; inversion Hb; subst; exfalso; eapply Ha; reflexivity. Qed.

  Lemma shape_end_non_pi : forall e z, shape_end e z -> (forall a ρ B, z <> Πᵈ a ρ B) -> e = z.
  Proof. intros * H Hz; inversion H; subst; [ reflexivity | exfalso; eapply Hz; reflexivity ]. Qed.

  Lemma per_univ_elem_some_uidx : forall (i : uidx) R x y, DF x ≈ y ∈ per_univ_elem i ↘ R ->
      exists j : uidx, DF x ≈ y ∈ per_univ_elem j ↘ R.
  Proof. intros * H; exists i; exact H. Qed.

  Lemma tele_elems_length : forall base T vs, tele_elems base T vs -> List.length vs = List.length T.
  Proof. induction 1; [ reflexivity | rewrite !List.length_app; cbn; lia ]. Qed.

  (** Elements over one base are, the same values, elements over a related
      base, related to themselves at the telescope's relations. *)
  Lemma tele_elems_transfer : forall (P : relation domain -> domain -> domain -> Prop)
      (HP : forall R x y, P R x y -> exists i : uidx, DF x ≈ y ∈ per_univ_elem i ↘ R) tr b1 b2 T vs,
      tele_elems b1 T vs ->
      (forall k A vs1 vs2, List.nth_error T k = Some (ce_ass A) -> tele_prefix_rel tr k vs1 vs2 ->
         rel_mod_eval P A (env_args nil (b1 ++ vs1)) A (env_args nil (b2 ++ vs2)) (tr k vs1)) ->
      tele_prefix_rel tr (List.length T) vs vs /\ tele_elems b2 T vs.
  Proof.
    intros * HP tr b1 b2 T vs H; induction H as [| T vs A t i R v H IH Ht Htt Hv]; intros Hev.
    - split; [ apply tele_prefix_rel_nil | constructor ].
    - destruct IH as (Hr & Hf).
      { intros k A' vs1 vs2 Hk Hp; apply Hev; [ rewrite List.nth_error_app1; [ exact Hk | apply List.nth_error_Some; congruence ] | exact Hp ]. }
      pose proof (tele_elems_length _ _ _ H) as Hl.
      destruct (Hev (List.length T) A vs vs ltac:(rewrite List.nth_error_app2, Nat.sub_diag by lia; reflexivity)
                  ltac:(rewrite <- Hl; rewrite <- Hl in Hr; exact Hr)) as [t1 t2 E1 E2 HPt].
      pose proof (functional_eval_exp _ _ _ _ Ht E1) as <-.
      destruct (HP _ _ _ HPt) as [i' Ht12].
      assert (Htr : tr (List.length T) vs v v).
      { apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ Htt Ht12 v v); exact Hv. }
      rewrite List.length_app; cbn; rewrite Nat.add_1_r.
      split; [ rewrite <- Hl; apply tele_prefix_rel_snoc; [ rewrite Hl; exact Hr | rewrite Hl; exact Htr ] |].
      econstructor; [ exact Hf | exact E2 | | exact Htr ].
      eapply per_univ_trans; [ apply per_univ_sym; exact Ht12 | exact Ht12 ].
  Qed.

  (** The heads of related types. *)
  Lemma per_univ_left_ind : forall i R p k us a, DF d_ind p k us ≈ a ∈ per_univ_elem i ↘ R -> exists us', a = d_ind p k us'.
  Proof. intros * H; basic_invert_per_univ_elem H; eauto. Qed.

  Lemma per_univ_left_pi : forall i R x ρ B a, DF Πᵈ x ρ B ≈ a ∈ per_univ_elem i ↘ R -> exists x' ρ' B', a = Πᵈ x' ρ' B'.
  Proof. intros * H; basic_invert_per_univ_elem H; eauto. Qed.

  (** Not an inductive type when related to one that is not. *)
  Lemma non_ind_related : forall j R z a, DF z ≈ a ∈ per_univ_elem j ↘ R ->
      (forall p k us, a <> d_ind p k us) -> forall p k us, z <> d_ind p k us.
  Proof. intros * Hz Ha p k us ->; destruct (per_univ_left_ind _ _ _ _ _ _ Hz) as [? ->]; eapply Ha; reflexivity. Qed.

  (** Neither an inductive type nor a [Π] when related to one that is
      neither. *)
  Lemma non_ind_non_pi_nest : forall j R z a e j2 R2 e',
      DF z ≈ a ∈ per_univ_elem j ↘ R ->
      (forall p k us, a <> d_ind p k us) -> (forall x ρ B, a <> Πᵈ x ρ B) ->
      shape_end e z -> DF e' ≈ e ∈ per_univ_elem j2 ↘ R2 -> nest_acc e'.
  Proof.
    intros * Hz Ha Hb He He'.
    assert (Hzp : forall x ρ B, z <> Πᵈ x ρ B)
      by (intros x ρ B ->; destruct (per_univ_left_pi _ _ _ _ _ _ Hz) as (? & ? & ? & ->); eapply Hb; reflexivity).
    rewrite (shape_end_non_pi _ _ He Hzp) in He'.
    assert (Hea : per_univ j2 e' a) by (eapply per_univ_trans'; eexists; eassumption).
    destruct Hea as [R3 Hea].
    apply nest_acc_non_ind, (non_ind_related _ _ _ _ Hea Ha).
  Qed.

  (** A step out of a type is one out of any type related to it. *)
  Lemma grp_step_rel : forall i R a a' b, DF a ≈ a' ∈ per_univ_elem i ↘ R -> grp_step b a' -> grp_step b a.
  Proof.
    intros * Ha Hb.
    inversion Hb as [b' p k D ups' ns' m Mm c gs j A ms vs b0 i0 R0 z e i2 R2 HD Hlu HMm Hc HA Hms Hvs Hb0 Hz Hse Hbe Heqb Heqa];
      subst.
    pose proof (per_univ_sym _ _ _ _ Ha) as Ha'.
    destruct (per_univ_left_ind _ _ _ _ _ _ Ha') as [us ->].
    basic_invert_per_univ_elem Ha'.
    repeat match goal with
      | H1 : ind_lookup _ _ p = Some ?D1, H2 : ind_lookup _ _ p = Some ?D2 |- _ =>
          tryif unify D1 D2 then fail else (rewrite H1 in H2; injection H2 as <-)
      end.
    match goal with
    | Hx : ?u1 ++ ?n1 = ups' ++ ns', Hl1 : List.length ?u1 = ind_nu D |- _ =>
        destruct (app_split_eq _ _ _ _ Hx ltac:(lia)) as [<- _]
    end.
    match goal with
    | Hn : nparams_evals (per_univ_elem _) _ ?u1 ?u2 _, Ha0 : args_evals (per_univ_elem _) _ _ _ _ _ |- _ =>
        rename Hn into Hn0; rename Ha0 into Hargs; rename u1 into upsL; rename u2 into ups1
    end.
    destruct (tele_elems_transfer (per_univ_elem _) (fun _ _ _ H => per_univ_elem_some_uidx _ _ _ _ H) (nr m) upsL ups1 _ _ Hms
                (fun k0 A0 vs1 vs2 Hk Hp => Hn0 _ _ _ _ _ _ HMm Hk Hp)) as (Hrms & Hmsa).
    assert (Hrms' : tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms) by (apply tele_rel_of_pre; exact Hrms).
    assert (Hk' : forall k0 A0, List.nth_error (List.map ce_ass (List.firstn j (cargs_nonrec gs))) k0 = Some (ce_ass A0) ->
              List.nth_error (cargs_nonrec gs) k0 = Some A0).
    { intros k0 A0 Hk; rewrite List.nth_error_map in Hk.
      destruct (List.nth_error (List.firstn j (cargs_nonrec gs)) k0) as [A1 |] eqn:E; cbn in Hk; [| discriminate ].
      injection Hk as ->; rewrite List.nth_error_firstn in E; destruct (k0 <? j); [ exact E | discriminate ]. }
    destruct (tele_elems_transfer (per_univ_elem _) (fun _ _ _ H => per_univ_elem_some_uidx _ _ _ _ H) (ar m ms c) (upsL ++ ms) (ups1 ++ ms) _ _ Hvs
                (fun k0 A0 vs1 vs2 Hk Hp => ltac:(rewrite <- !List.app_assoc;
                   exact (Hargs _ _ _ _ _ _ _ _ _ _ HMm Hrms' Hc (Hk' _ _ Hk) Hp)))) as (Hrvs & Hvsa).
    assert (Hlj : List.length (List.map ce_ass (List.firstn j (cargs_nonrec gs))) = j).
    { rewrite List.length_map, List.length_firstn; assert (j < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence); lia. }
    rewrite Hlj in Hrvs.
    destruct (Hargs _ _ _ _ _ _ _ _ _ _ HMm Hrms' Hc HA Hrvs) as [b1 ba Eb1 Eba Hb1a].
    pose proof (functional_eval_exp _ _ _ _ Hb0 Eb1) as <-.
    assert (Hzb : per_univ i0 z ba) by (eapply per_univ_trans'; [ eexists; exact Hz | eexists; exact Hb1a ]).
    destruct Hzb as [R9 HR9].
    match goal with Hl1 : List.length ups1 = ind_nu D |- grp_step b (d_ind p k (ups1 ++ ?n1)) =>
      exact (grp_step_intro b p k D ups1 n1 m Mm c gs j A ms vs ba i0 R9 z e i2 R2 HD Hl1 HMm Hc HA Hmsa Hvsa Eba HR9 Hse Hbe) end.
  Qed.

  (** Accessibility is invariant along the relation. *)
  Lemma nest_acc_rel : forall i R a a', DF a ≈ a' ∈ per_univ_elem i ↘ R -> nest_acc a' -> nest_acc a.
  Proof.
    intros * Ha Hacc; inversion Hacc as [? Hs]; subst.
    constructor; intros b Hb; apply Hs; eapply grp_step_rel; [ apply per_univ_sym; exact Ha | exact Hb ].
  Qed.

  (** Which declared member, and its non-uniform parameters, play no
      part in a step. *)
  Lemma grp_step_member_irrel : forall b p k k' D ups ns ns', ind_lookup gc_deps gc_stack p = Some D ->
      List.length ups = ind_nu D -> grp_step b (d_ind p k (ups ++ ns)) -> grp_step b (d_ind p k' (ups ++ ns')).
  Proof.
    intros * HD Hl Hb.
    inversion Hb as [b' p' k0 D' ups' ns0 m Mm c gs j A ms vs b0 i0 R0 z e i2 R2 HD' Hlu HMm Hc HA Hms Hvs Hb0 Hz Hse Hbe Heqb Heqa];
      subst.
    rewrite HD in HD'; injection HD' as <-.
    match goal with Hx : _ ++ _ = ups ++ ns |- _ => destruct (app_split_eq _ _ _ _ Hx ltac:(lia)) as [-> _] end.
    eapply grp_step_intro; eauto.
  Qed.

  (** The induction hypothesis of [per_univ_nest_acc]: every type related
      to [a], every shape end of it, and every type related to that, is
      accessible. *)
  Definition nest_motive (i : uidx) (R : relation domain) (a a' : domain) : Prop :=
    forall j R' z, DF z ≈ a ∈ per_univ_elem j ↘ R' -> forall e, shape_end e z ->
      forall j2 R2 e', DF e' ≈ e ∈ per_univ_elem j2 ↘ R2 -> nest_acc e'.

  Theorem per_univ_nest_acc : forall i R a a', DF a ≈ a' ∈ per_univ_elem i ↘ R -> nest_motive i R a a'.
  Proof.
    intros i R a a' H.
    eapply per_univ_elem_ind with (motive := nest_motive); try eassumption; unfold nest_motive; intros.
    1-5,7,9: match goal with
      | Hz : per_univ_elem _ _ ?z _, He : shape_end ?e ?z, He' : per_univ_elem _ _ ?e' ?e |- nest_acc ?e' =>
          exact (non_ind_non_pi_nest _ _ _ _ _ _ _ _ Hz ltac:(intros; discriminate) ltac:(intros; discriminate) He He')
      end.
    - (* a [Π]: the shape end of a related type is one of a codomain at a
         fresh variable, related to this codomain's at a fresh variable *)
      destruct (per_univ_left_pi _ _ _ _ _ _ (per_univ_sym _ _ _ _ H5)) as (az & ρz & Bz & ->).
      inversion H6 as [| ee a1 ρ1 B1 n b Hb Hse]; subst.
      { apply nest_acc_non_ind; eapply non_ind_related; [ exact H7 | intros; discriminate ]. }
      basic_invert_per_univ_elem H5.
      assert (Hc0 : in_rel0 (⇑! az n) (⇑! a0 n)) by (eapply var_per_elem; eassumption).
      destruct (H6 _ _ Hc0) as [b1 b2 Eb1 Eb2 Hb12].
      pose proof (functional_eval_exp _ _ _ _ Hb Eb1) as <-.
      assert (Hc : in_rel (⇑! a0 n) (⇑! a'0 n)) by (eapply var_per_elem; eassumption).
      destruct (H3 _ _ Hc) as [c1 c2 Ec1 Ec2 [_ HIH]].
      pose proof (functional_eval_exp _ _ _ _ Eb2 Ec1) as <-.
      eapply HIH; eassumption.
    - (* an inductive type: a step out of a related type is one out of
         this type, whose components carry the induction hypothesis *)
      match goal with Hz : per_univ_elem _ _ ?z (d_ind _ _ _), He : shape_end _ ?z,
                      He' : per_univ_elem _ _ ?e' ?e |- _ =>
        rename Hz into Hzr0; rename He into Hez; rename He' into Hee end.
      destruct (per_univ_left_ind _ _ _ _ _ _ (per_univ_sym _ _ _ _ Hzr0)) as [us0 ->].
      rewrite (shape_end_non_pi _ _ Hez ltac:(intros; discriminate)) in Hee.
      assert (Hzr1 : per_univ j2 e' (d_ind p k (ups ++ ns))) by (eapply per_univ_trans'; eexists; eassumption).
      destruct Hzr1 as [R3 Hzr].
      eapply nest_acc_rel; [ exact Hzr |].
      constructor; intros b Hb.
      inversion Hb as [b' p2 k2 D2 uz nz m Mm c gs jx A ms vs b0 i1 R1 z1 e1 i3 R4 HD2 Hlz HMm Hc HA Hms Hvs Hb0 Hz1 Hse Hbe];
        subst.
      match goal with HD : ind_lookup _ _ p = Some D |- _ => rewrite HD in HD2; injection HD2 as <- end.
      match goal with Hx : uz ++ nz = ups ++ ns |- _ => destruct (app_split_eq _ _ _ _ Hx ltac:(lia)) as [-> _] end.
      match goal with
      | HnI : nparams_evals (fun _ _ _ => _ /\ _) _ _ _ _, HaI : args_evals (fun _ _ _ => _ /\ _) _ _ _ _ _ |- _ =>
          rename HnI into HnIH; rename HaI into HaIH
      end.
      destruct (tele_elems_transfer _ (fun _ _ _ H => per_univ_elem_some_uidx _ _ _ _ (proj1 H)) (nr m) ups ups' _ _ Hms
                 (fun k0 A0 vs1 vs2 Hk Hp => HnIH _ _ _ _ _ _ HMm Hk Hp)) as (Hrms & _).
      assert (Hrms' : tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms) by (apply tele_rel_of_pre; exact Hrms).
      assert (Hk' : forall k0 A0, List.nth_error (List.map ce_ass (List.firstn jx (cargs_nonrec gs))) k0 = Some (ce_ass A0) ->
                List.nth_error (cargs_nonrec gs) k0 = Some A0).
      { intros k0 A0 Hk; rewrite List.nth_error_map in Hk.
        destruct (List.nth_error (List.firstn jx (cargs_nonrec gs)) k0) as [A1 |] eqn:E; cbn in Hk; [| discriminate ].
        injection Hk as ->; rewrite List.nth_error_firstn in E; destruct (k0 <? jx); [ exact E | discriminate ]. }
      destruct (tele_elems_transfer _ (fun _ _ _ H => per_univ_elem_some_uidx _ _ _ _ (proj1 H)) (ar m ms c) (ups ++ ms) (ups' ++ ms) _ _ Hvs
                 (fun k0 A0 vs1 vs2 Hk Hp => ltac:(rewrite <- !List.app_assoc;
                    exact (HaIH _ _ _ _ _ _ _ _ _ _ HMm Hrms' Hc (Hk' _ _ Hk) Hp)))) as (Hrvs & _).
      assert (Hljx : List.length (List.map ce_ass (List.firstn jx (cargs_nonrec gs))) = jx).
      { rewrite List.length_map, List.length_firstn; assert (jx < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence); lia. }
      rewrite Hljx in Hrvs.
      destruct (HaIH _ _ _ _ _ _ _ _ _ _ HMm Hrms' Hc HA Hrvs) as [c1 c2 Ec1 Ec2 [_ HIH]].
      pose proof (functional_eval_exp _ _ _ _ Hb0 Ec1) as <-.
      eapply HIH; [ exact Hz1 | exact Hse | exact Hbe ].
  Qed.

  (** Every type of the model, and every type related to one, is
      accessible. *)
  Corollary per_univ_nest_acc_rel : forall i R a a' j R' b, DF a ≈ a' ∈ per_univ_elem i ↘ R ->
      DF b ≈ a ∈ per_univ_elem j ↘ R' -> nest_acc b.
  Proof.
    intros * H Hb; eapply (per_univ_nest_acc _ _ _ _ H); [ | apply se_here | exact Hb ].
    eapply per_univ_trans; [ exact H | apply per_univ_sym, H ].
  Qed.
End NestAcc.
