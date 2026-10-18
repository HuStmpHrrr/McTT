(** * Relations at Telescopes

    [tele_full tr T vs vs'] relates two lists position by position, the
    [k]-th values at [tr k] of the two prefixes before them.  Every lemma
    here is about the lists only: it is used for the parameters and the
    arguments of inductive types, whose relations [tr] come from the PER
    model.  The one workhorse is [tele_full_combine]: a fact at every position
    of up to three lists, given the facts at the prefixes before it, holds of
    the whole lists. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.Definitions.
Import Domain_Notations.
#[local] Open Scope list_scope.

Section Tele.
  Context {GC : GCtx}.

  Lemma nth_error_lt_some' : forall {A} (l : list A) k, k < List.length l -> exists a, List.nth_error l k = Some a.
  Proof.
    intros * H; destruct (List.nth_error l k) as [a |] eqn:E; [ eauto |].
    apply List.nth_error_None in E; lia.
  Qed.

  Lemma firstn_S_snoc : forall {A} (l : list A) k a, List.nth_error l k = Some a ->
      List.firstn (S k) l = List.firstn k l ++ a :: nil.
  Proof.
    induction l as [| b l IH]; intros [| k] a H; cbn in *; try discriminate.
    - injection H as ->; reflexivity.
    - rewrite (IH _ _ H); reflexivity.
  Qed.

  Lemma tele_rel_aux_iff : forall tr vs vs' k pre,
      tele_rel_aux tr k pre vs vs' <->
      List.length vs = List.length vs' /\
      forall j x x', List.nth_error vs j = Some x -> List.nth_error vs' j = Some x' ->
        tr (k + j) (pre ++ List.firstn j vs) x x'.
  Proof.
    induction vs as [| v vs IH]; intros [| v' vs'] k pre; cbn [tele_rel_aux List.length].
    - split; [ intros _; split; [ reflexivity | intros [] ? ? ? ?; discriminate ] | intros _; exact I ].
    - split; [ intros [] | intros [? _]; discriminate ].
    - split; [ intros [] | intros [? _]; discriminate ].
    - rewrite IH; split.
      + intros (Hv & Hl & Hr); split; [ congruence |].
        intros [| j] x x' Hx Hx'; cbn in Hx, Hx' |- *.
        * injection Hx as <-; injection Hx' as <-; rewrite Nat.add_0_r, !List.app_nil_r; exact Hv.
        * replace (k + S j) with (S k + j) by lia; specialize (Hr _ _ _ Hx Hx'); rewrite <- !List.app_assoc in Hr; exact Hr.
      + intros [Hl Hr]; split; [| split; [ congruence |] ].
        * specialize (Hr 0 v v' eq_refl eq_refl); rewrite Nat.add_0_r, !List.app_nil_r in Hr; exact Hr.
        * intros j x x' Hx Hx'; specialize (Hr (S j) x x' Hx Hx'); cbn in Hr.
          replace (S k + j) with (k + S j) by lia; rewrite <- !List.app_assoc; exact Hr.
  Qed.

  Lemma tele_full_iff : forall {X} tr (T : list X) vs vs',
      tele_full tr T vs vs' <->
      List.length vs = List.length T /\ List.length vs' = List.length T /\
      forall j x x', List.nth_error vs j = Some x -> List.nth_error vs' j = Some x' ->
        tr j (List.firstn j vs) x x'.
  Proof.
    intros; unfold tele_full; rewrite tele_rel_aux_iff; split.
    - intros (Hl & Hl' & Hr); split; [ exact Hl | split; [ congruence |] ]; exact Hr.
    - intros (Hl & Hl' & Hr); split; [ exact Hl | split; [ congruence | exact Hr ] ].
  Qed.

  Lemma tele_pre_iff : forall tr k vs vs',
      tele_pre tr k vs vs' <->
      List.length vs = k /\ List.length vs' = k /\
      forall j x x', List.nth_error vs j = Some x -> List.nth_error vs' j = Some x' ->
        tr j (List.firstn j vs) x x'.
  Proof.
    intros; unfold tele_pre; rewrite tele_rel_aux_iff; split.
    - intros (Hl & Hl' & Hr); split; [ exact Hl | split; [ congruence |] ]; exact Hr.
    - intros (Hl & Hl' & Hr); split; [ exact Hl | split; [ congruence | exact Hr ] ].
  Qed.

  Lemma nth_error_firstn_lt : forall {A} (l : list A) k j, j < k -> List.nth_error (List.firstn k l) j = List.nth_error l j.
  Proof.
    induction l as [| a l IH]; intros [| k] [| j] Hj; cbn; try reflexivity; try lia.
    apply IH; lia.
  Qed.

  Lemma firstn_firstn_le : forall {A} (l : list A) k j, j <= k -> List.firstn j (List.firstn k l) = List.firstn j l.
  Proof. intros; rewrite List.firstn_firstn; f_equal; lia. Qed.

  (** A prefix of related lists is related. *)
  Lemma tele_pre_of_full : forall {X} tr (T : list X) vs vs' k,
      tele_full tr T vs vs' -> k <= List.length T ->
      tele_pre tr k (List.firstn k vs) (List.firstn k vs').
  Proof.
    intros * H Hk; rewrite tele_full_iff in H; destruct H as (Hl & Hl' & Hr).
    rewrite tele_pre_iff; split; [ rewrite List.length_firstn; lia | split; [ rewrite List.length_firstn; lia |] ].
    intros j x x' Hx Hx'.
    assert (Hj : j < k) by (assert (Hn : List.nth_error (List.firstn k vs) j <> None) by congruence;
                            apply List.nth_error_Some in Hn; rewrite List.length_firstn in Hn; lia).
    rewrite nth_error_firstn_lt in Hx, Hx' by exact Hj.
    rewrite !firstn_firstn_le by lia; exact (Hr _ _ _ Hx Hx').
  Qed.

  Lemma tele_pre_of_pre : forall tr k vs vs' j,
      tele_pre tr k vs vs' -> j <= k ->
      tele_pre tr j (List.firstn j vs) (List.firstn j vs').
  Proof.
    intros * H Hk; eapply tele_pre_of_full with (T := List.repeat tt k); [| rewrite List.repeat_length; exact Hk ].
    rewrite tele_full_iff, List.repeat_length; rewrite tele_pre_iff in H; exact H.
  Qed.

  Lemma tele_pre_nil : forall tr, tele_pre tr 0 nil nil.
  Proof. intros; split; [ reflexivity | exact I ]. Qed.

  Lemma tele_pre_snoc : forall tr k vs vs' x x',
      tele_pre tr k vs vs' -> tr k vs x x' ->
      tele_pre tr (S k) (vs ++ x :: nil) (vs' ++ x' :: nil).
  Proof.
    intros * H Hx; rewrite tele_pre_iff in *; destruct H as (Hl & Hl' & Hr).
    rewrite !List.length_app; cbn; split; [ lia | split; [ lia |] ].
    intros j y y' Hy Hy'.
    destruct (Nat.lt_ge_cases j k) as [Hj | Hj].
    - rewrite List.nth_error_app1 in Hy, Hy' by lia.
      rewrite !List.firstn_app, (proj2 (Nat.sub_0_le j (List.length vs))) by lia.
      cbn; rewrite !List.app_nil_r; exact (Hr _ _ _ Hy Hy').
    - rewrite List.nth_error_app2 in Hy, Hy' by lia.
      destruct (j - List.length vs) as [| ?] eqn:E1; [| destruct n; discriminate ].
      destruct (j - List.length vs') as [| ?] eqn:E2; [| destruct n; discriminate ].
      cbn in Hy, Hy'; injection Hy as <-; injection Hy' as <-.
      assert (j = k) as -> by lia.
      rewrite <- Hl, List.firstn_app, Nat.sub_diag, List.firstn_all; cbn; rewrite List.app_nil_r, Hl; exact Hx.
  Qed.

  (** The whole list from its prefixes. *)
  Lemma tele_full_of_pre : forall {X} tr (T : list X) vs vs',
      tele_pre tr (List.length T) vs vs' -> tele_full tr T vs vs'.
  Proof.
    intros * H; rewrite tele_pre_iff in H; rewrite tele_full_iff; exact H.
  Qed.

  Lemma tele_full_pre : forall {X} tr (T : list X) vs vs',
      tele_full tr T vs vs' -> tele_pre tr (List.length T) vs vs'.
  Proof.
    intros * H; rewrite tele_full_iff in H; rewrite tele_pre_iff; exact H.
  Qed.

  (** The workhorse: a fact at each position of up to three lists [L s],
      given the facts at the positions before it and the inputs there, holds
      of the whole lists. *)
  Lemma tele_full_combine : forall {X} (T : list X) tr1 tr2 tr3 (L : nat -> list domain) s1 s1' s2 s2' s3 s3',
      (s3 = s1 \/ s3 = s1' \/ s3 = s2 \/ s3 = s2') ->
      (s3' = s1 \/ s3' = s1' \/ s3' = s2 \/ s3' = s2') ->
      (forall k x1 x1' x2 x2' x3 x3', k < List.length T ->
         tele_pre tr1 k (List.firstn k (L s1)) (List.firstn k (L s1')) ->
         tele_pre tr2 k (List.firstn k (L s2)) (List.firstn k (L s2')) ->
         tele_pre tr3 k (List.firstn k (L s3)) (List.firstn k (L s3')) ->
         List.nth_error (L s1) k = Some x1 -> List.nth_error (L s1') k = Some x1' ->
         List.nth_error (L s2) k = Some x2 -> List.nth_error (L s2') k = Some x2' ->
         List.nth_error (L s3) k = Some x3 -> List.nth_error (L s3') k = Some x3' ->
         tr1 k (List.firstn k (L s1)) x1 x1' ->
         tr2 k (List.firstn k (L s2)) x2 x2' ->
         tr3 k (List.firstn k (L s3)) x3 x3') ->
      tele_full tr1 T (L s1) (L s1') -> tele_full tr2 T (L s2) (L s2') -> tele_full tr3 T (L s3) (L s3').
  Proof.
    intros * Hs3 Hs3' Hstep H1 H2.
    pose proof H1 as H1'; pose proof H2 as H2'.
    rewrite tele_full_iff in H1', H2'; destruct H1' as (Hl1 & Hl1' & Hr1); destruct H2' as (Hl2 & Hl2' & Hr2).
    assert (Hl3 : List.length (L s3) = List.length T) by (destruct Hs3 as [-> | [-> | [-> | ->]]]; assumption).
    assert (Hl3' : List.length (L s3') = List.length T) by (destruct Hs3' as [-> | [-> | [-> | ->]]]; assumption).
    apply tele_full_of_pre.
    assert (Hall : forall k, k <= List.length T -> tele_pre tr3 k (List.firstn k (L s3)) (List.firstn k (L s3'))).
    { induction k as [| k IH]; intros Hk; [ apply tele_pre_nil |].
      assert (Hlt : k < List.length T) by lia.
      destruct (nth_error_lt_some' (L s1) k ltac:(lia)) as [x1 E1].
      destruct (nth_error_lt_some' (L s1') k ltac:(lia)) as [x1' E1'].
      destruct (nth_error_lt_some' (L s2) k ltac:(lia)) as [x2 E2].
      destruct (nth_error_lt_some' (L s2') k ltac:(lia)) as [x2' E2'].
      destruct (nth_error_lt_some' (L s3) k ltac:(lia)) as [x3 E3].
      destruct (nth_error_lt_some' (L s3') k ltac:(lia)) as [x3' E3'].
      rewrite (firstn_S_snoc _ _ _ E3), (firstn_S_snoc _ _ _ E3').
      apply tele_pre_snoc; [ apply IH; lia |].
      eapply Hstep; try eassumption;
        [ apply tele_pre_of_full with (T := T); [ exact H1 | lia ]
        | apply tele_pre_of_full with (T := T); [ exact H2 | lia ]
        | apply IH; lia
        | exact (Hr1 _ _ _ E1 E1') | exact (Hr2 _ _ _ E2 E2') ]. }
    specialize (Hall _ (le_n _)); rewrite !List.firstn_all2 in Hall by lia; exact Hall.
  Qed.

  (** ** Lists of Arguments *)

  Lemma env_args_snoc : forall ρ vs v, env_args ρ (vs ++ v :: nil) = env_args ρ vs ↦ v.
  Proof. intros; unfold env_args; rewrite List.fold_left_app; reflexivity. Qed.

  Lemma cargs_nonrec_app : forall gs gs', cargs_nonrec (gs ++ gs') = cargs_nonrec gs ++ cargs_nonrec gs'.
  Proof. induction gs as [| [] gs IH]; intros; cbn; rewrite ?IH; reflexivity. Qed.

  Lemma nonrec_vals_app : forall gs gs' vs vs', List.length vs = List.length gs ->
      nonrec_vals (gs ++ gs') (vs ++ vs') = nonrec_vals gs vs ++ nonrec_vals gs' vs'.
  Proof.
    induction gs as [| [] gs IH]; intros gs' [| v vs] vs' Hl; cbn in *; try discriminate; try reflexivity;
      rewrite IH by lia; reflexivity.
  Qed.

  Lemma length_nonrec_vals : forall gs vs, List.length vs = List.length gs ->
      List.length (nonrec_vals gs vs) = List.length (cargs_nonrec gs).
  Proof.
    induction gs as [| [] gs IH]; intros [| v vs] Hl; cbn in *; try discriminate; try reflexivity;
      rewrite ?IH by lia; reflexivity.
  Qed.

  Lemma firstn_app_exact : forall {A} (l l' : list A) n, List.length l = n -> List.firstn n (l ++ l') = l.
  Proof. intros * <-; rewrite List.firstn_app, Nat.sub_diag, List.firstn_all; cbn; apply List.app_nil_r. Qed.

  Lemma skipn_app_exact : forall {A} (l l' : list A) n, List.length l = n -> List.skipn n (l ++ l') = l'.
  Proof. intros * <-; rewrite List.skipn_app, Nat.sub_diag, List.skipn_all; reflexivity. Qed.

  Lemma app_split_eq : forall {A} (l1 l2 l1' l2' : list A), l1 ++ l2 = l1' ++ l2' -> List.length l1 = List.length l1' ->
      l1 = l1' /\ l2 = l2'.
  Proof.
    intros * H Hl; split.
    - rewrite <- (firstn_app_exact l1 l2 _ eq_refl), H, Hl, firstn_app_exact by reflexivity; reflexivity.
    - rewrite <- (skipn_app_exact l1 l2 _ eq_refl), H, Hl, skipn_app_exact by reflexivity; reflexivity.
  Qed.

  Lemma functional_eval_exps' : forall Ms ρ ms1 ms2,
      eval_exps gc_deps gc_stack Ms ρ ms1 -> eval_exps gc_deps gc_stack Ms ρ ms2 -> ms1 = ms2.
  Proof. intros; eapply (proj1 (proj2 (proj2 (@functional_eval gc_deps gc_stack)))); eassumption. Qed.

  Lemma nparams_nth_ass : forall D k e,
      tele_ass (ind_params D) -> List.nth_error (List.rev (ind_nparams D)) k = Some e -> exists A, e = ce_ass A.
  Proof.
    intros * Hass He.
    assert (Hf : List.Forall (fun e => exists A, e = ce_ass A) (List.rev (ind_nparams D)))
      by (apply List.Forall_rev; unfold ind_nparams; apply Forall_firstn'; exact Hass).
    rewrite List.Forall_forall in Hf; apply Hf; eapply List.nth_error_In; exact He.
  Qed.

  Lemma per_top_ps_sym : forall T vs vs', per_top_ps T vs vs' -> per_top_ps T vs' vs.
  Proof. intros * H s; destruct (H s) as (Ms & H1 & H2); eauto. Qed.

  Lemma per_top_ps_trans : forall T vs vs' vs'', per_top_ps T vs vs' -> per_top_ps T vs' vs'' -> per_top_ps T vs vs''.
  Proof.
    intros * H H' s; destruct (H s) as (Ms & H1 & H2); destruct (H' s) as (Ms' & H1' & H2').
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (@functional_read gc_deps gc_stack))))) _ _ _ _ _ H2 _ H1') as <-.
    eauto.
  Qed.

  (** ** Derived Forms of [tele_full_combine] *)

  Lemma tele_full_map : forall {X} (T : list X) tr1 tr2 a b,
      (forall k pa pb x y, k < List.length T -> tele_pre tr1 k pa pb -> tele_pre tr2 k pa pb ->
         tr1 k pa x y -> tr2 k pa x y) ->
      tele_full tr1 T a b -> tele_full tr2 T a b.
  Proof.
    intros * Hs H.
    apply (tele_full_combine T tr1 tr1 tr2 (fun n => match n with 0 => a | _ => b end) 0 1 0 1 0 1);
      [ left; reflexivity | right; left; reflexivity | | exact H | exact H ].
    intros k * Hk Hp1 _ Hp3 E1 E1' _ _ E3 E3' Hr1 _.
    rewrite E1 in E3; injection E3 as <-; rewrite E1' in E3'; injection E3' as <-.
    exact (Hs _ _ _ _ _ Hk Hp1 Hp3 Hr1).
  Qed.

  Lemma tele_full_flip : forall {X} (T : list X) tr1 tr2 a b,
      (forall k pa pb x y, k < List.length T -> tele_pre tr1 k pa pb -> tele_pre tr2 k pb pa ->
         tr1 k pa x y -> tr2 k pb y x) ->
      tele_full tr1 T a b -> tele_full tr2 T b a.
  Proof.
    intros * Hs H.
    apply (tele_full_combine T tr1 tr1 tr2 (fun n => match n with 0 => a | _ => b end) 0 1 0 1 1 0);
      [ right; left; reflexivity | left; reflexivity | | exact H | exact H ].
    intros k * Hk Hp1 _ Hp3 E1 E1' _ _ E3 E3' Hr1 _.
    rewrite E1' in E3; injection E3 as <-; rewrite E1 in E3'; injection E3' as <-.
    exact (Hs _ _ _ _ _ Hk Hp1 Hp3 Hr1).
  Qed.

  Lemma tele_full_compose : forall {X} (T : list X) tr1 tr2 tr3 a b c,
      (forall k pa pb pc x y z, k < List.length T -> tele_pre tr1 k pa pb -> tele_pre tr2 k pb pc ->
         tele_pre tr3 k pa pc -> tr1 k pa x y -> tr2 k pb y z -> tr3 k pa x z) ->
      tele_full tr1 T a b -> tele_full tr2 T b c -> tele_full tr3 T a c.
  Proof.
    intros * Hs H1 H2.
    apply (tele_full_combine T tr1 tr2 tr3 (fun n => match n with 0 => a | 1 => b | _ => c end) 0 1 1 2 0 2);
      [ left; reflexivity | right; right; right; reflexivity | | exact H1 | exact H2 ].
    intros k * Hk Hp1 Hp2 Hp3 E1 E1' E2 E2' E3 E3' Hr1 Hr2.
    rewrite E1 in E3; injection E3 as <-; rewrite E2' in E3'; injection E3' as <-.
    rewrite E1' in E2; injection E2 as <-.
    exact (Hs _ _ _ _ _ _ _ Hk Hp1 Hp2 Hp3 Hr1 Hr2).
  Qed.

  Lemma tele_pre_full_iff : forall tr k a b, tele_pre tr k a b <-> tele_full tr (List.repeat tt k) a b.
  Proof. intros; rewrite tele_pre_iff, tele_full_iff, List.repeat_length; reflexivity. Qed.

  (** Across two families whose relations agree along related prefixes. *)
  Lemma tele_full_cross_refl : forall {X} (T : list X) tr1 tr2 a b,
      (forall k pa pb, k < List.length T -> tele_pre tr1 k pa pb -> tele_pre tr2 k pb pb -> (tr1 k pa <~> tr2 k pb)) ->
      (forall k vs vs', k < List.length T -> tele_pre tr2 k vs vs' -> PER (tr2 k vs)) ->
      tele_full tr1 T a b -> tele_full tr2 T b b.
  Proof.
    intros * Heq HP H.
    apply (tele_full_combine T tr1 tr1 tr2 (fun n => match n with 0 => a | _ => b end) 0 1 0 1 1 1);
      [ right; left; reflexivity | right; left; reflexivity | | exact H | exact H ].
    intros k * Hk Hp1 _ Hp3 E1 E1' _ _ E3 E3' Hr1 _.
    rewrite E1' in E3; injection E3 as <-; rewrite E1' in E3'; injection E3' as <-.
    pose proof (HP _ _ _ Hk Hp3) as HPer.
    apply (Heq _ _ _ Hk Hp1 Hp3) in Hr1.
    etransitivity; [ symmetry |]; exact Hr1.
  Qed.

  Lemma tele_full_compose_cross : forall {X} (T : list X) tr1 tr2 a b c,
      (forall k pa pb pc, k < List.length T -> tele_pre tr1 k pa pb -> tele_pre tr2 k pb pc -> (tr1 k pa <~> tr2 k pb)) ->
      (forall k vs vs', k < List.length T -> tele_pre tr1 k vs vs' -> PER (tr1 k vs)) ->
      tele_full tr1 T a b -> tele_full tr2 T b c -> tele_full tr1 T a c.
  Proof.
    intros * Heq HP H1 H2.
    apply (tele_full_compose T tr1 tr2 tr1 a b c); [| exact H1 | exact H2 ].
    intros k pa pb pc x y z Hk Hp1 Hp2 _ Hr1 Hr2.
    pose proof (HP _ _ _ Hk Hp1) as HPer.
    apply (Heq _ _ _ _ Hk Hp1 Hp2) in Hr2.
    etransitivity; eassumption.
  Qed.

  Lemma tele_pre_cross_refl : forall tr1 tr2 n k a b, k <= n ->
      (forall j pa pb, j < n -> tele_pre tr1 j pa pb -> tele_pre tr2 j pb pb -> (tr1 j pa <~> tr2 j pb)) ->
      (forall j vs vs', j < n -> tele_pre tr2 j vs vs' -> PER (tr2 j vs)) ->
      tele_pre tr1 k a b -> tele_pre tr2 k b b.
  Proof.
    intros * Hk Heq HP H; rewrite tele_pre_full_iff in *.
    eapply tele_full_cross_refl; [| | exact H ]; rewrite List.repeat_length; intros; [ eapply Heq | eapply HP ]; eauto; lia.
  Qed.

  (** ** A Telescope of PERs

      A family [tr] of PERs, each invariant along related prefixes, makes
      [tele_full tr T] a PER on lists. *)
  Section TelePER.
    Variable (n : nat) (tr : nat -> list domain -> relation domain).
    Hypothesis (HP : forall k vs vs', k < n -> tele_pre tr k vs vs' -> PER (tr k vs)).
    Hypothesis (HI : forall k vs vs', k < n -> tele_pre tr k vs vs' -> (tr k vs <~> tr k vs')).

    Lemma tele_full_sym : forall {X} (T : list X) a b, List.length T <= n -> tele_full tr T a b -> tele_full tr T b a.
    Proof.
      intros * Hn H; apply (tele_full_flip T tr tr); [| exact H ].
      intros k pa pb x y Hk Hp1 _ Hr.
      pose proof (HP k pa pb ltac:(lia) Hp1) as HPer.
      apply (HI k pa pb ltac:(lia) Hp1); symmetry; exact Hr.
    Qed.

    Lemma tele_full_trans : forall {X} (T : list X) a b c, List.length T <= n ->
        tele_full tr T a b -> tele_full tr T b c -> tele_full tr T a c.
    Proof.
      intros * Hn H1 H2; apply (tele_full_compose T tr tr tr _ b); [| exact H1 | exact H2 ].
      intros k pa pb pc x y z Hk Hp1 Hp2 _ Hr1 Hr2.
      pose proof (HP k pa pb ltac:(lia) Hp1) as HPer.
      apply (HI k pa pb ltac:(lia) Hp1) in Hr2; etransitivity; eassumption.
    Qed.

    Lemma tele_full_refl_r : forall {X} (T : list X) a b, List.length T <= n -> tele_full tr T a b -> tele_full tr T b b.
    Proof. intros * Hn H; eapply tele_full_trans; [ exact Hn | apply tele_full_sym; [ exact Hn | exact H ] | exact H ]. Qed.

    Lemma tele_pre_sym : forall k a b, k <= n -> tele_pre tr k a b -> tele_pre tr k b a.
    Proof.
      intros * Hk H; rewrite tele_pre_full_iff in *; apply tele_full_sym; [ rewrite List.repeat_length; exact Hk | exact H ].
    Qed.

    Lemma tele_pre_trans : forall k a b c, k <= n -> tele_pre tr k a b -> tele_pre tr k b c -> tele_pre tr k a c.
    Proof.
      intros * Hk H1 H2; rewrite tele_pre_full_iff in *; eapply tele_full_trans; [ rewrite List.repeat_length; exact Hk | exact H1 | exact H2 ].
    Qed.

    Lemma tele_pre_refl_l : forall k a b, k <= n -> tele_pre tr k a b -> tele_pre tr k a a.
    Proof. intros * Hk H; eapply tele_pre_trans; [ exact Hk | exact H | apply tele_pre_sym; [ exact Hk | exact H ] ]. Qed.

    Lemma tele_pre_refl_r : forall k a b, k <= n -> tele_pre tr k a b -> tele_pre tr k b b.
    Proof. intros * Hk H; eapply tele_pre_trans; [ exact Hk | apply tele_pre_sym; [ exact Hk | exact H ] | exact H ]. Qed.
  End TelePER.

  (** ** The Elements of an Inductive Type, Generically

      The lemmas below need only the conditions the clause of
      [per_univ_elem_core] for inductive types states on the relations
      [nr] and [ar]: each is a PER, invariant along related prefixes and
      instances, and the recursive instances of related arguments are
      related (the closures). *)

  Lemma nparams_lt_ass : forall D k, tele_ass (ind_params D) -> k < List.length (List.rev (ind_nparams D)) ->
      exists A, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A).
  Proof.
    intros * Hass Hk; destruct (nth_error_lt_some' _ _ Hk) as [e He].
    destruct (nparams_nth_ass _ _ _ Hass He) as [A ->]; eauto.
  Qed.

  Lemma nonrec_prefix_gen : forall tr gsf gs1 gs vp vp' vs vs', gsf = gs1 ++ gs ->
      List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
      tele_full tr (cargs_nonrec gsf) (nonrec_vals gsf (vp ++ vs)) (nonrec_vals gsf (vp' ++ vs')) ->
      tele_pre tr (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 vp) (nonrec_vals gs1 vp').
  Proof.
    intros * Heq Hl Hl' Ha.
    pose proof (tele_pre_of_full _ _ _ _ (List.length (cargs_nonrec gs1)) Ha) as H.
    rewrite Heq, cargs_nonrec_app, List.length_app in H; specialize (H ltac:(lia)).
    rewrite !nonrec_vals_app in H by assumption.
    rewrite !(firstn_app_exact (nonrec_vals gs1 _)) in H by (apply length_nonrec_vals; assumption).
    exact H.
  Qed.

  Lemma ptyp_skip_pi : forall k t0 B t, ptyp_skip k t0 = pt_pi B t ->
      List.nth_error (ptyp_doms t0) k = Some B /\ ptyp_skip (S k) t0 = t.
  Proof.
    induction k as [| k IH]; intros [] * H; cbn in *; try discriminate.
    - injection H as -> ->; split; reflexivity.
    - exact (IH _ _ _ H).
  Qed.

  Lemma ptyp_skip_self : forall k t0 j Ps, ptyp_skip k t0 = pt_self j Ps ->
      List.length (ptyp_doms t0) <= k /\ ptyp_ps t0 = Ps.
  Proof.
    induction k as [| k IH]; intros [] * H; cbn in *; try discriminate.
    - injection H as -> ->; split; [ lia | reflexivity ].
    - injection H as -> ->; split; [ lia | reflexivity ].
    - destruct (IH _ _ _ H); split; [ lia | assumption ].
  Qed.

  (** The rest of a simple shape after its domains is its end, and before
      them a domain. *)
  Lemma ptyp_skip_end : forall t, ptyp_simple t = true -> ptyp_skip (List.length (ptyp_doms t)) t = pt_self 0 (ptyp_ps t).
  Proof. induction t as [[| k] Ps | k Ps | B t IH]; cbn; intros H; try discriminate; [ reflexivity | exact (IH H) ]. Qed.

  Lemma ptyp_skip_lt : forall k t, k < List.length (ptyp_doms t) ->
      exists B, List.nth_error (ptyp_doms t) k = Some B /\ ptyp_skip k t = pt_pi B (ptyp_skip (S k) t).
  Proof.
    induction k as [| k IH]; intros [k0 Ps | k0 Ps | B0 t0] H; cbn in *; try lia; [ eauto |].
    exact (IH t0 ltac:(lia)).
  Qed.

  Lemma per_top_sym' : forall a b, per_top a b -> per_top b a.
  Proof. intros * H s; destruct (H s) as (L & H1 & H2); eauto. Qed.

  Lemma per_top_trans' : forall a b d, per_top a b -> per_top b d -> per_top a d.
  Proof.
    intros * H1 H2 s; destruct (H1 s) as (L & HL1 & HL2); destruct (H2 s) as (L' & HL2' & HL3).
    pose proof (functional_read_nf _ _ _ _ HL2 HL2') as <-; eauto.
  Qed.

  Section IndPER.
    #[local] Set Default Proof Using "All".
    Variable (p : qname) (D : ind_decl) (ups : list domain).
    Variable (nr : nat -> list domain -> relation domain).
    Variable (ar : list domain -> String.string -> nat -> list domain -> relation domain).
    Variable (dr : list domain -> exp -> relation domain).
    Let T := List.rev (ind_nparams D).
    Hypothesis (Hass : tele_ass (ind_params D)).
    Hypothesis (HnP : forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_pre nr k vs vs' -> PER (nr k vs)).
    Hypothesis (HnI : forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_pre nr k vs vs' -> (nr k vs <~> nr k vs')).
    Hypothesis (HaP : forall ms ms' c gs k A vs vs', tele_full nr T ms ms' -> ind_con D c = Some gs ->
                      List.nth_error (cargs_nonrec gs) k = Some A -> tele_pre (ar ms c) k vs vs' -> PER (ar ms c k vs)).
    Hypothesis (HaI : forall ms ms' c gs k A vs vs', tele_full nr T ms ms' -> ind_con D c = Some gs ->
                      List.nth_error (cargs_nonrec gs) k = Some A -> tele_pre (ar ms c) k vs vs' ->
                      (ar ms c k vs <~> ar ms' c k vs')).
    Hypothesis (HdP : forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_full nr T ms ms' ->
                      ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                      tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
                      List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr dr ms ws (ptyp_doms t)) k ys ys' ->
                      PER (dr (ms ++ ws ++ ys) B)).
    Hypothesis (HdI : forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_full nr T ms ms' ->
                      ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                      tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
                      List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr dr ms ws (ptyp_doms t)) k ys ys' ->
                      (dr (ms ++ ws ++ ys) B <~> dr (ms' ++ ws' ++ ys') B)).

    Lemma nr_P : forall k vs vs', k < List.length T -> tele_pre nr k vs vs' -> PER (nr k vs).
    Proof. intros * Hk H; destruct (nparams_lt_ass D k Hass Hk) as [A HA]; eapply HnP; eassumption. Qed.

    Lemma nr_I : forall k vs vs', k < List.length T -> tele_pre nr k vs vs' -> (nr k vs <~> nr k vs').
    Proof. intros * Hk H; destruct (nparams_lt_ass D k Hass Hk) as [A HA]; eapply HnI; eassumption. Qed.

    Lemma tnr_sym : forall a b, tele_full nr T a b -> tele_full nr T b a.
    Proof. intros; eapply (tele_full_sym (List.length T) nr nr_P nr_I); [ lia | eassumption ]. Qed.

    Lemma tnr_trans : forall a b c, tele_full nr T a b -> tele_full nr T b c -> tele_full nr T a c.
    Proof. intros; eapply (tele_full_trans (List.length T) nr nr_P nr_I); [ lia | eassumption | eassumption ]. Qed.

    Lemma tnr_refl_l : forall a b, tele_full nr T a b -> tele_full nr T a a.
    Proof. intros * H; exact (tnr_trans _ _ _ H (tnr_sym _ _ H)). Qed.

    Lemma tnr_refl_r : forall a b, tele_full nr T a b -> tele_full nr T b b.
    Proof. intros * H; exact (tnr_trans _ _ _ (tnr_sym _ _ H) H). Qed.

    Section Args.
      Variable (ms : list domain) (c : String.string) (gs : list carg).
      Hypothesis (Hms : tele_full nr T ms ms) (Hc : ind_con D c = Some gs).

      Lemma ar_P : forall k vs vs', k < List.length (cargs_nonrec gs) -> tele_pre (ar ms c) k vs vs' -> PER (ar ms c k vs).
      Proof. intros * Hk H; destruct (nth_error_lt_some' _ _ Hk) as [A HA]; eapply HaP; eassumption. Qed.

      Lemma ar_I : forall k vs vs', k < List.length (cargs_nonrec gs) -> tele_pre (ar ms c) k vs vs' ->
          (ar ms c k vs <~> ar ms c k vs').
      Proof.
        intros * Hk H; destruct (nth_error_lt_some' _ _ Hk) as [A HA].
        exact (HaI _ _ _ _ _ _ _ _ Hms Hc HA H).
      Qed.

      Lemma tar_sym : forall a b, tele_full (ar ms c) (cargs_nonrec gs) a b -> tele_full (ar ms c) (cargs_nonrec gs) b a.
      Proof. intros; eapply (tele_full_sym (List.length (cargs_nonrec gs)) _ ar_P ar_I); [ lia | eassumption ]. Qed.

      Lemma tar_trans : forall a b d, tele_full (ar ms c) (cargs_nonrec gs) a b -> tele_full (ar ms c) (cargs_nonrec gs) b d ->
          tele_full (ar ms c) (cargs_nonrec gs) a d.
      Proof. intros; eapply (tele_full_trans (List.length (cargs_nonrec gs)) _ ar_P ar_I); [ lia | eassumption | eassumption ]. Qed.

      Lemma tar_pre_refl_l : forall k a b, k <= List.length (cargs_nonrec gs) -> tele_pre (ar ms c) k a b -> tele_pre (ar ms c) k a a.
      Proof. intros; eapply (tele_pre_refl_l (List.length (cargs_nonrec gs)) _ ar_P ar_I); eassumption. Qed.

      Lemma tar_pre_sym : forall k a b, k <= List.length (cargs_nonrec gs) -> tele_pre (ar ms c) k a b -> tele_pre (ar ms c) k b a.
      Proof. intros; eapply (tele_pre_sym (List.length (cargs_nonrec gs)) _ ar_P ar_I); eassumption. Qed.
    End Args.

    (** The argument relation at an instance related to another. *)
    Lemma tar_inst : forall ms ms' c gs a b, tele_full nr T ms ms' -> ind_con D c = Some gs ->
        tele_full (ar ms c) (cargs_nonrec gs) a b -> tele_full (ar ms' c) (cargs_nonrec gs) a b.
    Proof.
      intros * Hm Hc H; apply (tele_full_map _ (ar ms c)); [| exact H ].
      intros k pa pb x y Hk Hp1 _ Hr.
      destruct (nth_error_lt_some' _ _ Hk) as [A HA].
      assert (Hrefl : tele_pre (ar ms c) k pa pa)
        by (eapply (tar_pre_refl_l ms c gs (tnr_refl_l _ _ Hm) Hc); [ lia | exact Hp1 ]).
      apply (HaI _ _ _ _ _ _ _ _ Hm Hc HA Hrefl); exact Hr.
    Qed.

    Lemma tnrp_sym : forall k a b, k <= List.length T -> tele_pre nr k a b -> tele_pre nr k b a.
    Proof. intros; eapply (tele_pre_sym (List.length T) nr nr_P nr_I); eassumption. Qed.

    Lemma tarp_inst : forall ms ms' c gs k a b, tele_full nr T ms ms' -> ind_con D c = Some gs ->
        k <= List.length (cargs_nonrec gs) -> tele_pre (ar ms c) k a b -> tele_pre (ar ms' c) k a b.
    Proof.
      intros * Hm Hc Hk H.
      rewrite tele_pre_full_iff in H |- *.
      apply (tele_full_map _ (ar ms c)); [| exact H ].
      intros j pa pb x y Hj Hp1 _ Hr; rewrite List.repeat_length in Hj.
      destruct (nth_error_lt_some' (cargs_nonrec gs) j ltac:(lia)) as [A HA].
      assert (Hrefl : tele_pre (ar ms c) j pa pa)
        by (eapply (tar_pre_refl_l ms c gs (tnr_refl_l _ _ Hm) Hc); [ lia | exact Hp1 ]).
      apply (HaI _ _ _ _ _ _ _ _ Hm Hc HA Hrefl); exact Hr.
    Qed.

    Lemma tarp_sym : forall ms c gs k a b, tele_full nr T ms ms -> ind_con D c = Some gs ->
        k <= List.length (cargs_nonrec gs) -> tele_pre (ar ms c) k a b -> tele_pre (ar ms c) k b a.
    Proof. intros; eapply (tar_pre_sym ms c gs); eassumption. Qed.

    Lemma tnrp_refl_l : forall k a b, k <= List.length T -> tele_pre nr k a b -> tele_pre nr k a a.
    Proof. intros; eapply (tele_pre_refl_l (List.length T) nr nr_P nr_I); eassumption. Qed.

    Lemma tnrp_refl_r : forall k a b, k <= List.length T -> tele_pre nr k a b -> tele_pre nr k b b.
    Proof. intros; eapply (tele_pre_refl_r (List.length T) nr nr_P nr_I); eassumption. Qed.

    (** An instance of the arguments' relation at the right instance and
        prefix, on the diagonal. *)
    Lemma tarp_refl_r : forall ms ms' c gs k a b, tele_full nr T ms ms' -> ind_con D c = Some gs ->
        k <= List.length (cargs_nonrec gs) -> tele_pre (ar ms c) k a b -> tele_pre (ar ms' c) k b b.
    Proof.
      intros * Hm Hc Hk H.
      pose proof (tarp_inst _ _ _ _ _ _ _ Hm Hc Hk H) as H'.
      eapply (tar_pre_refl_l ms' c gs (tnr_refl_r _ _ Hm) Hc); [ exact Hk |].
      eapply (tar_pre_sym ms' c gs (tnr_refl_r _ _ Hm) Hc); [ exact Hk | exact H' ].
    Qed.

    (** ** The Domains of a Shape

        At an instance and a prefix of the arguments on the diagonal, the
        domains of a recursive argument's shape are a telescope of PERs. *)
    Section Shape.
      Variable (ms : list domain) (c : String.string) (gs gs1 : list carg) (t : ptyp) (gs2 : list carg) (ws : list domain).
      Hypothesis (Hms : tele_full nr T ms ms) (Hc : ind_con D c = Some gs) (Heq : gs = gs1 ++ ca_rec t :: gs2)
                 (Hws : tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws).

      Lemma sh_P : forall k ys ys', k < List.length (ptyp_doms t) -> tele_pre (shape_tr dr ms ws (ptyp_doms t)) k ys ys' ->
          PER (shape_tr dr ms ws (ptyp_doms t) k ys).
      Proof.
        intros * Hk H; destruct (nth_error_lt_some' _ _ Hk) as [B HB]; unfold shape_tr at 1.
        rewrite (List.nth_error_nth _ _ _ HB); eapply HdP; eassumption.
      Qed.

      Lemma sh_I : forall k ys ys', k < List.length (ptyp_doms t) -> tele_pre (shape_tr dr ms ws (ptyp_doms t)) k ys ys' ->
          (shape_tr dr ms ws (ptyp_doms t) k ys <~> shape_tr dr ms ws (ptyp_doms t) k ys').
      Proof.
        intros * Hk H; destruct (nth_error_lt_some' _ _ Hk) as [B HB]; unfold shape_tr.
        rewrite (List.nth_error_nth _ _ _ HB); eapply HdI; eassumption.
      Qed.

      Lemma tsh_sym : forall k a b, k <= List.length (ptyp_doms t) ->
          tele_pre (shape_tr dr ms ws (ptyp_doms t)) k a b -> tele_pre (shape_tr dr ms ws (ptyp_doms t)) k b a.
      Proof. intros; eapply (tele_pre_sym (List.length (ptyp_doms t)) _ sh_P sh_I); eassumption. Qed.

      Lemma tsh_refl_l : forall k a b, k <= List.length (ptyp_doms t) ->
          tele_pre (shape_tr dr ms ws (ptyp_doms t)) k a b -> tele_pre (shape_tr dr ms ws (ptyp_doms t)) k a a.
      Proof. intros; eapply (tele_pre_refl_l (List.length (ptyp_doms t)) _ sh_P sh_I); eassumption. Qed.

      Lemma tsh_refl_r : forall k a b, k <= List.length (ptyp_doms t) ->
          tele_pre (shape_tr dr ms ws (ptyp_doms t)) k a b -> tele_pre (shape_tr dr ms ws (ptyp_doms t)) k b b.
      Proof. intros; eapply (tele_pre_refl_r (List.length (ptyp_doms t)) _ sh_P sh_I); eassumption. Qed.
    End Shape.

    (** The domains' telescope at another instance and prefix related to
        the diagonal one. *)
    Lemma tsh_inst : forall ms ms' c gs gs1 t gs2 ws ws' k a b, tele_full nr T ms ms' -> ind_con D c = Some gs ->
        gs = gs1 ++ ca_rec t :: gs2 -> tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
        k <= List.length (ptyp_doms t) ->
        tele_pre (shape_tr dr ms ws (ptyp_doms t)) k a b -> tele_pre (shape_tr dr ms' ws' (ptyp_doms t)) k a b.
    Proof.
      intros * Hm Hc Heq Hw Hk H.
      assert (Hww : tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws).
      { eapply (tar_pre_refl_l ms c gs (tnr_refl_l _ _ Hm) Hc); [| exact Hw ].
        rewrite Heq, cargs_nonrec_app, List.length_app; lia. }
      rewrite tele_pre_full_iff in H |- *.
      apply (tele_full_map _ (shape_tr dr ms ws (ptyp_doms t))); [| exact H ].
      intros j pa pb x y Hj Hp1 _ Hr; rewrite List.repeat_length in Hj.
      destruct (nth_error_lt_some' (ptyp_doms t) j ltac:(lia)) as [B HB].
      assert (Hrefl : tele_pre (shape_tr dr ms ws (ptyp_doms t)) j pa pa)
        by (eapply (tsh_refl_l ms c gs gs1 t gs2 ws (tnr_refl_l _ _ Hm) Hc Heq Hww); [ lia | exact Hp1 ]).
      unfold shape_tr in Hr |- *; rewrite (List.nth_error_nth _ _ _ HB) in Hr |- *.
      apply (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw HB Hrefl); exact Hr.
    Qed.

    Lemma tsh_refl_inst : forall ms ms' c gs gs1 t gs2 ws ws' k a b, tele_full nr T ms ms' -> ind_con D c = Some gs ->
        gs = gs1 ++ ca_rec t :: gs2 -> tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
        k <= List.length (ptyp_doms t) ->
        tele_pre (shape_tr dr ms ws (ptyp_doms t)) k a b -> tele_pre (shape_tr dr ms' ws' (ptyp_doms t)) k b b.
    Proof.
      intros * Hm Hc Heq Hw Hk H.
      assert (Hk1 : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      assert (Hw' : tele_pre (ar ms' c) (List.length (cargs_nonrec gs1)) ws' ws') by exact (tarp_refl_r ms ms' c gs _ ws ws' Hm Hc Hk1 Hw).
      pose proof (tsh_inst _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw Hk H) as H'.
      eapply (tsh_refl_r ms' c gs gs1 t gs2 ws' (tnr_refl_r _ _ Hm) Hc Heq Hw'); [ exact Hk |].
      exact H'.
    Qed.

    (** The parameters of a recursive argument at related instances,
        prefixes and domains, evaluated beside [ups] and [ups2]. *)
    Definition ind_closure (ups2 : list domain) : Prop :=
      forall ms ms' c gs gs1 t gs2 ws ws' ys ys', tele_full nr T ms ms' -> ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
        tele_full (shape_tr dr ms ws (ptyp_doms t)) (ptyp_doms t) ys ys' ->
        exps_rel (ptyp_ps t) (env_args nil (ups ++ ms ++ ws ++ ys)) (env_args nil (ups2 ++ ms' ++ ws' ++ ys')) (tele_full nr T).

    Lemma adm_cl : forall u, ind_adm D ups nr ar dr u -> ind_closure u.
    Proof. intros u [_ _ H _]; exact H. Qed.

    Lemma shape_k_le : forall gs gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
        List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs).
    Proof. intros * ->; rewrite cargs_nonrec_app, List.length_app; lia. Qed.

    Lemma nth_error_lt' : forall {A} (l : list A) k a, List.nth_error l k = Some a -> k < List.length l.
    Proof. intros * H; apply List.nth_error_Some; congruence. Qed.

    (** Admissibility at another base admissible beside [ups]. *)
    Lemma adm_base : forall u1 u2, ind_adm D ups nr ar dr u1 -> ind_adm D ups nr ar dr u2 -> ind_adm D u1 nr ar dr u2.
    Proof.
      intros u1 u2 [H1n H1a H1c H1d] [H2n H2a H2c H2d]; constructor.
      - intros k A vs vs' s Hk Hp.
        assert (Hkl : k < List.length T) by (apply List.nth_error_Some; unfold T; congruence).
        destruct (H1n _ _ _ _ s Hk (tnrp_refl_l k vs vs' ltac:(lia) Hp)) as (a0 & a1 & E0 & E1 & R1).
        destruct (H2n _ _ _ _ s Hk Hp) as (b0 & a2 & F0 & E2 & R2).
        functional_eval_rewrite_clear.
        pose proof (HnP _ _ _ _ Hk Hp) as HP.
        exists a1, a2; split; [ exact E1 | split; [ exact E2 |] ].
        etransitivity; [ symmetry; exact R1 | exact R2 ].
      - intros ms ms' c gs k A vs vs' s Hm Hc Hk Hp.
        assert (Hkl : k < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        pose proof (tnr_refl_l _ _ Hm) as Hmm.
        destruct (H1a _ _ _ _ _ _ _ _ s Hmm Hc Hk (tar_pre_refl_l ms c gs Hmm Hc k vs vs' ltac:(lia) Hp)) as (a0 & a1 & E0 & E1 & R1).
        destruct (H2a _ _ _ _ _ _ _ _ s Hm Hc Hk Hp) as (b0 & a2 & F0 & E2 & R2).
        functional_eval_rewrite_clear.
        pose proof (HaP _ _ _ _ _ _ _ _ Hm Hc Hk Hp) as HP.
        exists a1, a2; split; [ exact E1 | split; [ exact E2 |] ].
        etransitivity; [ symmetry; exact R1 | exact R2 ].
      - intros ms ms' c gs gs1 t gs2 ws ws' ys ys' Hm Hc Heq Hp Hy.
        pose proof (shape_k_le _ _ _ _ Heq) as Hk.
        pose proof (tnr_refl_l _ _ Hm) as Hmm.
        pose proof (tar_pre_refl_l ms c gs Hmm Hc _ ws ws' Hk Hp) as Hww.
        assert (Hyy : tele_full (shape_tr dr ms ws (ptyp_doms t)) (ptyp_doms t) ys ys)
          by (apply tele_full_of_pre; eapply (tsh_refl_l ms c gs gs1 t gs2 ws Hmm Hc Heq Hww); [ lia | apply tele_full_pre; exact Hy ]).
        destruct (H1c _ _ _ _ _ _ _ _ _ _ _ Hmm Hc Heq Hww Hyy) as [b0 b1 E0 E1 H01].
        destruct (H2c _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hp Hy) as [b0' b2 E0' E2 H02].
        pose proof (functional_eval_exps' _ _ _ _ E0 E0') as <-.
        exists b1 b2; [ exact E1 | exact E2 | exact (tnr_trans _ _ _ (tnr_sym _ _ H01) H02) ].
      - intros ms ms' c gs gs1 t gs2 ws ws' k B ys ys' Hm Hc Heq Hp HB Hy.
        pose proof (shape_k_le _ _ _ _ Heq) as Hk.
        pose proof (nth_error_lt' _ _ _ HB) as Hkl.
        pose proof (tnr_refl_l _ _ Hm) as Hmm.
        pose proof (tar_pre_refl_l ms c gs Hmm Hc _ ws ws' Hk Hp) as Hww.
        pose proof (tsh_refl_l ms c gs gs1 t gs2 ws Hmm Hc Heq Hww k ys ys' ltac:(lia) Hy) as Hyy.
        pose proof (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ Hmm Hc Heq Hww HB Hyy) as HPd.
        destruct (H1d _ _ _ _ _ _ _ _ _ _ _ _ _ Hmm Hc Heq Hww HB Hyy) as (a0 & a1 & E0 & E1 & T1).
        destruct (H2d _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hp HB Hy) as (a0' & a2 & E0' & E2 & T2).
        functional_eval_rewrite_clear.
        exists a1, a2; split; [ exact E1 | split; [ exact E2 |] ].
        intros x x' Hx.
        assert (Hxx : dr (ms ++ ws ++ ys) B x x) by (etransitivity; [ exact Hx | symmetry; exact Hx ]).
        exact (per_top_trans' _ _ _ (per_top_sym' _ _ (T1 _ _ Hxx)) (T2 _ _ Hx)).
    Qed.

    (** Admissibility composes. *)
    Lemma adm_compose : forall u1 u2, ind_adm D ups nr ar dr u1 -> ind_adm D u1 nr ar dr u2 -> ind_adm D ups nr ar dr u2.
    Proof.
      intros u1 u2 [H1n H1a H1c H1d] [H2n H2a H2c H2d]; constructor.
      - intros k A vs vs' s Hk Hp.
        assert (Hkl : k < List.length T) by (apply List.nth_error_Some; unfold T; congruence).
        destruct (H1n _ _ _ _ s Hk Hp) as (a0 & a1 & E0 & E1 & R1).
        destruct (H2n _ _ _ _ s Hk (tnrp_refl_r k vs vs' ltac:(lia) Hp)) as (b1 & a2 & F1 & E2 & R2).
        functional_eval_rewrite_clear.
        pose proof (HnP _ _ _ _ Hk Hp) as HP.
        apply (HnI _ _ _ _ Hk Hp) in R2.
        exists a0, a2; split; [ exact E0 | split; [ exact E2 |] ].
        etransitivity; [ exact R1 | exact R2 ].
      - intros ms ms' c gs k A vs vs' s Hm Hc Hk Hp.
        assert (Hkl : k < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        destruct (H1a _ _ _ _ _ _ _ _ s Hm Hc Hk Hp) as (a0 & a1 & E0 & E1 & R1).
        destruct (H2a _ _ _ _ _ _ _ _ s (tnr_refl_r _ _ Hm) Hc Hk (tarp_refl_r ms ms' c gs k vs vs' Hm Hc ltac:(lia) Hp))
          as (b1 & a2 & F1 & E2 & R2).
        functional_eval_rewrite_clear.
        pose proof (HaP _ _ _ _ _ _ _ _ Hm Hc Hk Hp) as HP.
        apply (HaI _ _ _ _ _ _ _ _ Hm Hc Hk Hp) in R2.
        exists a0, a2; split; [ exact E0 | split; [ exact E2 |] ].
        etransitivity; [ exact R1 | exact R2 ].
      - intros ms ms' c gs gs1 t gs2 ws ws' ys ys' Hm Hc Heq Hp Hy.
        pose proof (shape_k_le _ _ _ _ Heq) as Hk.
        pose proof (tarp_refl_r _ _ _ _ _ _ _ Hm Hc Hk Hp) as Hw'.
        assert (Hy' : tele_full (shape_tr dr ms' ws' (ptyp_doms t)) (ptyp_doms t) ys' ys')
          by (apply tele_full_of_pre; eapply tsh_refl_inst; [ exact Hm | exact Hc | exact Heq | exact Hp | lia | apply tele_full_pre; exact Hy ]).
        destruct (H1c _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hp Hy) as [b0 b1 E0 E1 H01].
        destruct (H2c _ _ _ _ _ _ _ _ _ _ _ (tnr_refl_r _ _ Hm) Hc Heq Hw' Hy') as [b1' b2 E1' E2 H12].
        pose proof (functional_eval_exps' _ _ _ _ E1 E1') as <-.
        exists b0 b2; [ exact E0 | exact E2 | exact (tnr_trans _ _ _ H01 H12) ].
      - intros ms ms' c gs gs1 t gs2 ws ws' k B ys ys' Hm Hc Heq Hp HB Hy.
        pose proof (shape_k_le _ _ _ _ Heq) as Hk.
        pose proof (nth_error_lt' _ _ _ HB) as Hkl.
        pose proof (tarp_refl_r _ _ _ _ _ _ _ Hm Hc Hk Hp) as Hw'.
        pose proof (tsh_refl_inst ms ms' c gs gs1 t gs2 ws ws' k ys ys' Hm Hc Heq Hp ltac:(lia) Hy) as Hy'.
        pose proof (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ (tnr_refl_r _ _ Hm) Hc Heq Hw' HB Hy') as HPd.
        destruct (H1d _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hp HB Hy) as (a0 & a1 & E0 & E1 & T1).
        destruct (H2d _ _ _ _ _ _ _ _ _ _ _ _ _ (tnr_refl_r _ _ Hm) Hc Heq Hw' HB Hy') as (a1' & a2 & E1' & E2 & T2).
        pose proof (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hp HB Hy) as HdIe.
        functional_eval_rewrite_clear.
        exists a0, a2; split; [ exact E0 | split; [ exact E2 |] ].
        intros x x' Hx.
        pose proof (proj1 (HdIe _ _) Hx) as Hx'.
        assert (Hxx : dr (ms' ++ ws' ++ ys') B x' x') by (etransitivity; [ symmetry; exact Hx' | exact Hx' ]).
        exact (per_top_trans' _ _ _ (T1 _ _ Hx) (T2 _ _ Hxx)).
    Qed.

    Lemma nonrec_prefix : forall ns c gsf gs1 gs vp vp' vs vs',
        tele_full nr T ns ns -> ind_con D c = Some gsf -> gsf = gs1 ++ gs ->
        List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
        tele_full (ar ns c) (cargs_nonrec gsf) (nonrec_vals gsf (vp ++ vs)) (nonrec_vals gsf (vp' ++ vs')) ->
        tele_pre (ar ns c) (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 vp) (nonrec_vals gs1 vp').
    Proof.
      intros * Hns Hc Heq Hl Hl' Ha.
      pose proof (tele_pre_of_full _ _ _ _ (List.length (cargs_nonrec gs1)) Ha) as H.
      rewrite Heq, cargs_nonrec_app, List.length_app in H; specialize (H ltac:(lia)).
      rewrite !nonrec_vals_app in H by assumption.
      rewrite !(firstn_app_exact (nonrec_vals gs1 _)) in H by (apply length_nonrec_vals; assumption).
      exact H.
    Qed.

    Lemma nonrec_prefix_refl : forall ns c gsf gs1 gs vp vp' vs vs',
        tele_full nr T ns ns -> ind_con D c = Some gsf -> gsf = gs1 ++ gs ->
        List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
        tele_full (ar ns c) (cargs_nonrec gsf) (nonrec_vals gsf (vp ++ vs)) (nonrec_vals gsf (vp' ++ vs')) ->
        tele_pre (ar ns c) (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 vp) (nonrec_vals gs1 vp).
    Proof.
      intros * Hns Hc Heq Hl Hl' Ha.
      eapply (tar_pre_refl_l ns c gsf Hns Hc); [ rewrite Heq, cargs_nonrec_app, List.length_app; lia |].
      eapply nonrec_prefix; eassumption.
    Qed.

    Lemma nonrec_vals_snoc_arg : forall gs1 vp A v, List.length vp = List.length gs1 ->
        nonrec_vals (gs1 ++ ca_arg A :: nil) (vp ++ v :: nil) = nonrec_vals gs1 vp ++ v :: nil.
    Proof. intros; rewrite nonrec_vals_app by assumption; reflexivity. Qed.

    Lemma nonrec_vals_snoc_rec : forall gs1 vp t v, List.length vp = List.length gs1 ->
        nonrec_vals (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil) = nonrec_vals gs1 vp.
    Proof. intros; rewrite nonrec_vals_app by assumption; cbn; rewrite List.app_nil_r; reflexivity. Qed.

    (** A shape's invariants: its domains after the arguments before it
        related on the diagonal, [k] of them consumed. *)
    Lemma shape_pi_step : forall ns c gs1 t0 gs2 ws ws' k ys ys' B t,
        tele_full nr T ns ns -> ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
        tele_pre (ar ns c) (List.length (cargs_nonrec gs1)) ws ws' ->
        ptyp_skip k t0 = pt_pi B t -> tele_pre (shape_tr dr ns ws (ptyp_doms t0)) k ys ys' ->
        List.nth_error (ptyp_doms t0) k = Some B /\ ptyp_skip (S k) t0 = t /\ S k <= List.length (ptyp_doms t0) /\
        PER (dr (ns ++ ws ++ ys) B) /\
        (forall a a', dr (ns ++ ws ++ ys) B a a' ->
           tele_pre (shape_tr dr ns ws (ptyp_doms t0)) (S k) (ys ++ a :: nil) (ys' ++ a' :: nil)).
    Proof.
      intros * Hns Hc Hw Hs Hy.
      destruct (ptyp_skip_pi _ _ _ _ Hs) as [HB Hs'].
      pose proof (nth_error_lt' _ _ _ HB) as Hkl.
      pose proof (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ Hns Hc eq_refl Hw HB Hy) as HP.
      split; [ exact HB | split; [ exact Hs' | split; [ lia | split; [ exact HP |] ] ] ].
      intros a a' Ha; apply tele_pre_snoc; [ exact Hy |].
      unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HB); exact Ha.
    Qed.

    Lemma ind_rel_move : forall ups2, ind_adm D ups nr ar dr ups2 ->
        (forall ns x y, ind_rel p D ups nr ar dr ns x y -> forall ns1, tele_full nr T ns ns1 -> ind_rel p D ups2 nr ar dr ns1 x y) /\
        (forall pre gs vs vs', ind_args_rel p D ups nr ar dr pre gs vs vs' ->
           forall ns ns1 c gsf gs1 vp vp', pre = ns ++ nonrec_vals gs1 vp ->
             List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
             tele_full nr T ns ns1 -> ind_con D c = Some gsf -> gsf = gs1 ++ gs ->
             tele_full (ar ns c) (cargs_nonrec gsf) (nonrec_vals gsf (vp ++ vs)) (nonrec_vals gsf (vp' ++ vs')) ->
             ind_args_rel p D ups2 nr ar dr (ns1 ++ nonrec_vals gs1 vp) gs vs vs') /\
        (forall pre t v v', ind_shape_rel p D ups nr ar dr pre t v v' ->
           forall ns ns1 c gs1 t0 gs2 ws k ys, pre = ns ++ ws ++ ys ->
             tele_full nr T ns ns1 -> ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
             tele_pre (ar ns c) (List.length (cargs_nonrec gs1)) ws ws ->
             ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
             tele_pre (shape_tr dr ns ws (ptyp_doms t0)) k ys ys ->
             ind_shape_rel p D ups2 nr ar dr (ns1 ++ ws ++ ys) t v v') /\
        (forall pre t f a f' a', ind_app_rel p D ups nr ar dr pre t f a f' a' ->
           forall ns ns1 c gs1 t0 gs2 ws k ys, pre = ns ++ ws ++ ys ->
             tele_full nr T ns ns1 -> ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
             tele_pre (ar ns c) (List.length (cargs_nonrec gs1)) ws ws ->
             ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
             tele_pre (shape_tr dr ns ws (ptyp_doms t0)) k ys ys ->
             ind_app_rel p D ups2 nr ar dr (ns1 ++ ws ++ ys) t f a f' a').
    Proof.
      intros ups2 Had; pose proof (adm_cl _ Had) as Hcl; apply ind_rel_mut_ind_all.
      - intros * Hns Hc Hb Hb' Hs Hs' Ha Hia IH ns1 Hns1.
        econstructor; [ exact (tnr_refl_r _ _ Hns1) | exact Hc | exact Hb | exact Hb'
                      | exact (tnr_trans _ _ _ (tnr_sym _ _ Hns1) Hs) | exact (tnr_trans _ _ _ (tnr_sym _ _ Hns1) Hs')
                      | exact (tar_inst _ _ _ _ _ _ Hns1 Hc Ha) |].
        rewrite <- (List.app_nil_r ns1).
        apply (IH ns ns1 c gs nil nil nil);
          [ cbn; rewrite List.app_nil_r; reflexivity | reflexivity | reflexivity | exact Hns1 | exact Hc | reflexivity | exact Ha ].
      - intros * Hl1 Hl2 Ha1 Ha2 Hs1 Hs2 Hm ns1 Hns1.
        constructor; [ exact Hl1 | exact Hl2 | exact (adm_base _ _ Had Ha1) | exact (adm_base _ _ Had Ha2)
                     | exact (tnr_trans _ _ _ (tnr_sym _ _ Hns1) Hs1) | exact (tnr_trans _ _ _ (tnr_sym _ _ Hns1) Hs2) | exact Hm ].
      - intros; constructor.
      - intros * Hia IH ns ns1 c gsf gs1 vp vp' Hρ Hl Hl' Hn Hc Heq Ha.
        constructor; rewrite <- List.app_assoc, <- nonrec_vals_snoc_arg with (A := A) by assumption.
        apply (IH ns ns1 c gsf (gs1 ++ ca_arg A :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil));
          [ rewrite Hρ, nonrec_vals_snoc_arg, List.app_assoc by assumption; reflexivity
          | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
          | rewrite Heq, <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Ha ].
      - intros * Hsh IHs Hia IH ns ns1 c gsf gs1 vp vp' Hρ Hl Hl' Hn Hc Heq Ha.
        assert (Hnn : tele_full nr T ns ns) by exact (tnr_refl_l _ _ Hn).
        pose proof (nonrec_prefix_refl _ _ _ _ _ _ _ _ _ Hnn Hc Heq Hl Hl' Ha) as Hpre.
        constructor.
        + rewrite <- (List.app_nil_r (nonrec_vals gs1 vp)).
          apply (IHs ns ns1 c gs1 t gs (nonrec_vals gs1 vp) 0 nil);
            [ rewrite List.app_nil_r; exact Hρ | exact Hn | rewrite <- Heq; exact Hc | exact Hpre | reflexivity | lia
            | apply tele_pre_nil ].
        + rewrite <- nonrec_vals_snoc_rec with (t := t) (v := v) by assumption.
          apply (IH ns ns1 c gsf (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil));
            [ rewrite Hρ, nonrec_vals_snoc_rec by assumption; reflexivity
            | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
            | rewrite Heq, <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Ha ].
      - intros * Hb Hr IHr ns ns1 c gs1 t0 gs2 ws k0 ys Hρ Hn Hc Hw Hs Hk Hy.
        destruct (ptyp_skip_self _ _ _ _ Hs) as [Hkd HPs].
        assert (Hyf : tele_full (shape_tr dr ns ws (ptyp_doms t0)) (ptyp_doms t0) ys ys)
          by (destruct Hy as [Hyl Hya]; split; [ lia | exact Hya ]).
        destruct (Hcl ns ns1 c _ gs1 t0 gs2 ws ws ys ys Hn Hc eq_refl Hw Hyf) as [bs0 bs1 E0 E1 Hbs].
        rewrite HPs in E0, E1; subst pre.
        pose proof (functional_eval_exps' _ _ _ _ Hb E0) as <-.
        econstructor; [ exact E1 | exact (IHr _ Hbs) ].
      - intros * Hf IH ns ns1 c gs1 t0 gs2 ws k0 ys Hρ Hn Hc Hw Hs Hk Hy.
        pose proof (tnr_refl_l _ _ Hn) as Hnn.
        destruct (shape_pi_step _ _ _ _ _ _ _ _ _ _ _ _ Hnn Hc Hw Hs Hy) as (HB & Hs' & Hk' & HP & Hstep).
        constructor; intros a a' Haa.
        pose proof (proj2 (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hn Hc eq_refl Hw HB Hy _ _) Haa) as Haa0.
        rewrite <- !List.app_assoc.
        subst pre.
        apply (IH a a' Haa0 ns ns1 c gs1 t0 gs2 ws (S k0) (ys ++ a :: nil));
          [ rewrite <- !List.app_assoc; reflexivity | exact Hn | exact Hc | exact Hw | exact Hs' | exact Hk' |].
        apply Hstep; etransitivity; [ exact Haa0 | symmetry; exact Haa0 ].
      - intros * Ef Ef' Hsh IH ns ns1 c gs1 t0 gs2 ws k0 ys Hρ Hn Hc Hw Hs Hk Hy.
        econstructor; [ exact Ef | exact Ef' | eapply IH; eassumption ].
    Qed.

    Lemma ind_rel_sym_all : ind_adm D ups nr ar dr ups ->
        (forall ns x y, ind_rel p D ups nr ar dr ns x y -> ind_rel p D ups nr ar dr ns y x) /\
        (forall pre gs vs vs', ind_args_rel p D ups nr ar dr pre gs vs vs' ->
           forall ns c gsf gs1 vp vp', pre = ns ++ nonrec_vals gs1 vp ->
             List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
             tele_full nr T ns ns -> ind_con D c = Some gsf -> gsf = gs1 ++ gs ->
             tele_full (ar ns c) (cargs_nonrec gsf) (nonrec_vals gsf (vp ++ vs)) (nonrec_vals gsf (vp' ++ vs')) ->
             ind_args_rel p D ups nr ar dr (ns ++ nonrec_vals gs1 vp') gs vs' vs) /\
        (forall pre t v v', ind_shape_rel p D ups nr ar dr pre t v v' ->
           forall ns c gs1 t0 gs2 ws ws' k ys ys', pre = ns ++ ws ++ ys ->
             tele_full nr T ns ns -> ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
             tele_pre (ar ns c) (List.length (cargs_nonrec gs1)) ws ws' ->
             ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
             tele_pre (shape_tr dr ns ws (ptyp_doms t0)) k ys ys' ->
             ind_shape_rel p D ups nr ar dr (ns ++ ws' ++ ys') t v' v) /\
        (forall pre t f a f' a', ind_app_rel p D ups nr ar dr pre t f a f' a' ->
           forall ns c gs1 t0 gs2 ws ws' k ys ys', pre = ns ++ ws ++ ys ->
             tele_full nr T ns ns -> ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
             tele_pre (ar ns c) (List.length (cargs_nonrec gs1)) ws ws' ->
             ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
             tele_pre (shape_tr dr ns ws (ptyp_doms t0)) k ys ys' ->
             ind_app_rel p D ups nr ar dr (ns ++ ws' ++ ys') t f' a' f a).
    Proof.
      intros Had; pose proof (adm_cl _ Had) as Hcd; apply ind_rel_mut_ind_all.
      - intros * Hns Hc Hb Hb' Hs Hs' Ha Hia IH.
        econstructor; [ exact Hns | exact Hc | exact Hb' | exact Hb | exact Hs' | exact Hs
                      | exact (tar_sym _ _ _ Hns Hc _ _ Ha) |].
        rewrite <- (List.app_nil_r ns).
        apply (IH ns c gs nil nil nil);
          [ cbn; rewrite List.app_nil_r; reflexivity | reflexivity | reflexivity | exact Hns | exact Hc | reflexivity | exact Ha ].
      - intros * Hl1 Hl2 Ha1 Ha2 Hs1 Hs2 Hm; constructor; try assumption; intros s0; destruct (Hm s0) as (L & HL & HL'); eauto.
      - intros; constructor.
      - intros * Hia IH ns c gsf gs1 vp vp' Hρ Hl Hl' Hn Hc Heq Ha.
        constructor; rewrite <- List.app_assoc, <- nonrec_vals_snoc_arg with (A := A) by assumption.
        apply (IH ns c gsf (gs1 ++ ca_arg A :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil));
          [ rewrite Hρ, nonrec_vals_snoc_arg, List.app_assoc by assumption; reflexivity
          | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
          | rewrite Heq, <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Ha ].
      - intros * Hsh IHs Hia IH ns c gsf gs1 vp vp' Hρ Hl Hl' Hn Hc Heq Ha.
        pose proof (nonrec_prefix _ _ _ _ _ _ _ _ _ Hn Hc Heq Hl Hl' Ha) as Hpre.
        constructor.
        + rewrite <- (List.app_nil_r (nonrec_vals gs1 vp')).
          apply (IHs ns c gs1 t gs (nonrec_vals gs1 vp) (nonrec_vals gs1 vp') 0 nil nil);
            [ rewrite List.app_nil_r; exact Hρ | exact Hn | rewrite <- Heq; exact Hc | exact Hpre | reflexivity | lia
            | apply tele_pre_nil ].
        + rewrite <- nonrec_vals_snoc_rec with (t := t) (v := v') by assumption.
          apply (IH ns c gsf (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil));
            [ rewrite Hρ, nonrec_vals_snoc_rec by assumption; reflexivity
            | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
            | rewrite Heq, <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Ha ].
      - intros * Hb Hr IHr ns c gs1 t0 gs2 ws ws' k0 ys ys' Hρ Hn Hc Hw Hs Hk Hy.
        destruct (ptyp_skip_self _ _ _ _ Hs) as [Hkd HPs].
        assert (Hyf : tele_full (shape_tr dr ns ws (ptyp_doms t0)) (ptyp_doms t0) ys ys')
          by (destruct Hy as [Hyl Hya]; split; [ lia | exact Hya ]).
        destruct (Hcd ns ns c _ gs1 t0 gs2 ws ws' ys ys' Hn Hc eq_refl Hw Hyf) as [bs0 bs1 E0 E1 Hbs].
        rewrite HPs in E0, E1; subst pre.
        pose proof (functional_eval_exps' _ _ _ _ Hb E0) as <-.
        econstructor; [ exact E1 | exact (proj1 (ind_rel_move ups Had) _ _ _ IHr _ Hbs) ].
      - intros * Hf IH ns c gs1 t0 gs2 ws ws' k0 ys ys' Hρ Hn Hc Hw Hs Hk Hy.
        destruct (shape_pi_step _ _ _ _ _ _ _ _ _ _ _ _ Hn Hc Hw Hs Hy) as (HB & Hs' & Hk' & HP & Hstep).
        constructor; intros a a' Haa.
        pose proof (proj2 (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hn Hc eq_refl Hw HB Hy _ _) Haa) as Haa0.
        assert (Hsym : dr pre B a' a) by (subst pre; symmetry; exact Haa0).
        rewrite <- !List.app_assoc.
        apply (IH a' a Hsym ns c gs1 t0 gs2 ws ws' (S k0) (ys ++ a' :: nil) (ys' ++ a :: nil));
          [ subst pre; rewrite <- !List.app_assoc; reflexivity | exact Hn | exact Hc | exact Hw | exact Hs' | exact Hk' |].
        apply Hstep; subst pre; exact Hsym.
      - intros * Ef Ef' Hsh IH ns c gs1 t0 gs2 ws ws' k0 ys ys' Hρ Hn Hc Hw Hs Hk Hy.
        econstructor; [ exact Ef' | exact Ef | eapply IH; eassumption ].
    Qed.

    (** Inverting an element on its left: its form fixes the constructor,
        the parameters and the arguments. *)
    Lemma ind_rel_con_inv : forall ns c bs vs z,
        ind_rel p D ups nr ar dr ns (d_con p c (bs ++ vs)) z -> List.length bs = ind_np D ->
        exists gs bs' vs', z = d_con p c (bs' ++ vs') /\
          tele_full nr T ns ns /\ ind_con D c = Some gs /\ List.length bs' = ind_np D /\
          tele_full nr T ns (List.skipn (ind_nu D) bs) /\ tele_full nr T ns (List.skipn (ind_nu D) bs') /\
          tele_full (ar ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs') /\
          ind_args_rel p D ups nr ar dr ns gs vs vs'.
    Proof.
      intros * H Hl; inversion H as [ns0 c0 gs bs0 bs' vs0 vs' Hns Hc Hb Hb' Hs Hs' Ha Hia |]; subst.
      match goal with He : _ ++ _ = bs ++ vs |- _ => destruct (app_split_eq _ _ _ _ He ltac:(congruence)) as [-> ->] end.
      exact (ex_intro _ gs (ex_intro _ bs' (ex_intro _ vs' (conj eq_refl (conj Hns (conj Hc (conj Hb' (conj Hs (conj Hs' (conj Ha Hia)))))))))).
    Qed.

    Lemma ind_rel_trans_all : ind_adm D ups nr ar dr ups ->
        (forall ns x y, ind_rel p D ups nr ar dr ns x y -> forall z, ind_rel p D ups nr ar dr ns y z -> ind_rel p D ups nr ar dr ns x z) /\
        (forall pre gs vs vs', ind_args_rel p D ups nr ar dr pre gs vs vs' ->
           forall ns c gsf gs1 vp vp' vs'', pre = ns ++ nonrec_vals gs1 vp ->
             List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
             tele_full nr T ns ns -> ind_con D c = Some gsf -> gsf = gs1 ++ gs ->
             tele_full (ar ns c) (cargs_nonrec gsf) (nonrec_vals gsf (vp ++ vs)) (nonrec_vals gsf (vp' ++ vs')) ->
             ind_args_rel p D ups nr ar dr (ns ++ nonrec_vals gs1 vp') gs vs' vs'' ->
             ind_args_rel p D ups nr ar dr pre gs vs vs'') /\
        (forall pre t v v', ind_shape_rel p D ups nr ar dr pre t v v' ->
           forall ns c gs1 t0 gs2 ws ws' k ys ys' v'', pre = ns ++ ws ++ ys ->
             tele_full nr T ns ns -> ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
             tele_pre (ar ns c) (List.length (cargs_nonrec gs1)) ws ws' ->
             ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
             tele_pre (shape_tr dr ns ws (ptyp_doms t0)) k ys ys' ->
             ind_shape_rel p D ups nr ar dr (ns ++ ws' ++ ys') t v' v'' ->
             ind_shape_rel p D ups nr ar dr pre t v v'') /\
        (forall pre t f a f' a', ind_app_rel p D ups nr ar dr pre t f a f' a' ->
           forall ns c gs1 t0 gs2 ws ws' k ys ys' f'' a'', pre = ns ++ ws ++ ys ->
             tele_full nr T ns ns -> ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
             tele_pre (ar ns c) (List.length (cargs_nonrec gs1)) ws ws' ->
             ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
             tele_pre (shape_tr dr ns ws (ptyp_doms t0)) k ys ys' ->
             ind_app_rel p D ups nr ar dr (ns ++ ws' ++ ys') t f' a' f'' a'' ->
             ind_app_rel p D ups nr ar dr pre t f a f'' a'').
    Proof.
      intros Had; pose proof (adm_cl _ Had) as Hcd; apply ind_rel_mut_ind_all.
      - intros * Hns Hc Hb Hb' Hs Hs' Ha Hia IH z Hz.
        destruct (ind_rel_con_inv _ _ _ _ _ Hz Hb') as (gs0 & bs'' & vs'' & -> & _ & Hc0 & Hb'' & _ & Hs'' & Ha0 & Hia0).
        rewrite Hc in Hc0; injection Hc0 as <-.
        econstructor; [ exact Hns | exact Hc | exact Hb | exact Hb'' | exact Hs | exact Hs''
                      | exact (tar_trans _ _ _ Hns Hc _ _ _ Ha Ha0) |].
        apply (IH ns c gs nil nil nil vs'');
          [ cbn; rewrite List.app_nil_r; reflexivity | reflexivity | reflexivity | exact Hns | exact Hc | reflexivity | exact Ha
          | cbn; rewrite List.app_nil_r; exact Hia0 ].
      - intros * Hl1 Hl2 Ha1 Ha2 Hs1 Hs2 Hm z Hz; inversion Hz; subst.
        constructor; try assumption.
        match goal with H1 : per_bot _ ?y, H2 : per_bot ?y _ |- per_bot _ _ =>
          intros s0; destruct (H1 s0) as (L & HL & HL'); destruct (H2 s0) as (L' & HL0 & HL'') end.
        pose proof (functional_read_ne _ _ _ _ HL' HL0) as <-; eauto.
      - intros * _ _ _ _ _ _ _ Hz; inversion Hz; subst; constructor.
      - intros * Hia IH ns c gsf gs1 vp vp' vs'' Hρ Hl Hl' Hn Hc Heq Ha Hz.
        subst pre gsf.
        inversion Hz; subst.
        match goal with
        | H3 : ind_args_rel _ _ _ _ _ _ ((ns ++ nonrec_vals gs1 vp') ++ v' :: nil) gs vs' _ |- _ => rename H3 into Hz'
        end.
        constructor.
        apply (IH ns c (gs1 ++ ca_arg A :: gs) (gs1 ++ ca_arg A :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil));
          [ rewrite nonrec_vals_snoc_arg, List.app_assoc by assumption; reflexivity
          | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
          | rewrite <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Ha
          | rewrite nonrec_vals_snoc_arg, List.app_assoc by assumption; exact Hz' ].
      - intros * Hsh IHs Hia IH ns c gsf gs1 vp vp' vs'' Hρ Hl Hl' Hn Hc Heq Ha Hz.
        subst pre gsf.
        inversion Hz; subst.
        match goal with
        | H2 : ind_shape_rel _ _ _ _ _ _ (ns ++ nonrec_vals gs1 vp') t v' _,
          H3 : ind_args_rel _ _ _ _ _ _ (ns ++ nonrec_vals gs1 vp') gs vs' _ |- _ =>
            rename H2 into Hsh2; rename H3 into Hz'
        end.
        pose proof (nonrec_prefix _ _ _ _ _ _ _ _ _ Hn Hc eq_refl Hl Hl' Ha) as Hpre.
        constructor.
        + idtac.
          apply (IHs ns c gs1 t gs (nonrec_vals gs1 vp) (nonrec_vals gs1 vp') 0 nil nil);
            [ rewrite List.app_nil_r; reflexivity | exact Hn | exact Hc | exact Hpre | reflexivity | lia
            | apply tele_pre_nil | rewrite List.app_nil_r; exact Hsh2 ].
        + apply (IH ns c (gs1 ++ ca_rec t :: gs) (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil));
            [ rewrite nonrec_vals_snoc_rec by assumption; reflexivity
            | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
            | rewrite <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Ha
            | rewrite nonrec_vals_snoc_rec by assumption; exact Hz' ].
      - intros * Hb Hr IHr ns c gs1 t0 gs2 ws ws' k0 ys ys' v'' Hρ Hn Hc Hw Hs Hk Hy Hz.
        destruct (ptyp_skip_self _ _ _ _ Hs) as [Hkd HPs].
        inversion Hz; subst.
        match goal with
        | H1 : eval_exps _ _ _ (env_args nil (ups ++ ns ++ ws' ++ ys')) ?b2,
          H2 : ind_rel _ _ _ _ _ _ ?b2 v' _ |- _ => rename H1 into Hb2; rename H2 into Hr2
        end.
        assert (Hyf : tele_full (shape_tr dr ns ws (ptyp_doms t0)) (ptyp_doms t0) ys ys')
          by (destruct Hy as [Hyl Hya]; split; [ lia | exact Hya ]).
        destruct (Hcd ns ns c _ gs1 t0 gs2 ws ws' ys ys' Hn Hc eq_refl Hw Hyf) as [bsa bsb E0 E1 Hbs].
        try rewrite HPs in E0, E1.
        pose proof (functional_eval_exps' _ _ _ _ Hb E0) as <-.
        pose proof (functional_eval_exps' _ _ _ _ Hb2 E1) as <-.
        econstructor; [ exact Hb | apply IHr; exact (proj1 (ind_rel_move ups Had) _ _ _ Hr2 _ (tnr_sym _ _ Hbs)) ].
      - intros * Hf IH ns c gs1 t0 gs2 ws ws' k0 ys ys' f'' Hρ Hn Hc Hw Hs Hk Hy Hz.
        subst pre; inversion Hz; subst.
        match goal with Hz0 : forall c c', dr _ _ c c' -> _ |- _ => rename Hz0 into Hz' end.
        destruct (shape_pi_step _ _ _ _ _ _ _ _ _ _ _ _ Hn Hc Hw Hs Hy) as (HB & Hs' & Hk' & HP & Hstep).
        constructor; intros a a'' Haa.
        assert (Ha2 : dr (ns ++ ws ++ ys) B a'' a'') by (etransitivity; [ symmetry; exact Haa | exact Haa ]).
        pose proof (proj1 (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hn Hc eq_refl Hw HB Hy _ _) Ha2) as Ha2'.
        specialize (Hz' _ _ Ha2').
        apply (IH a a'' Haa ns c gs1 t0 gs2 ws ws' (S k0) (ys ++ a :: nil) (ys' ++ a'' :: nil) f'' a'');
          [ rewrite <- !List.app_assoc; reflexivity | exact Hn | exact Hc | exact Hw | exact Hs' | exact Hk'
          | apply Hstep; exact Haa |].
        rewrite <- !List.app_assoc in Hz'; exact Hz'.
      - intros * Ef Ef' Hsh IH ns c gs1 t0 gs2 ws ws' k0 ys ys' f'' a'' Hρ Hn Hc Hw Hs Hk Hy Hz.
        inversion Hz; subst.
        match goal with
        | E1 : eval_app _ _ ?F ?A ?R, E2 : eval_app _ _ ?F ?A ?R2 |- _ =>
            assert_fails (unify R R2); pose proof (functional_eval_app _ _ _ _ E1 E2) as <-
        end.
        econstructor; [ exact Ef | eassumption | apply (IH ns c gs1 t0 gs2 ws ws' k0 ys ys'); first [ reflexivity | eassumption ] ].
    Qed.

    (** The admissibility the swapped type needs: of [ups] and of [ups']
        beside [ups']. *)
    Lemma adm_flip : forall ups', ind_adm D ups nr ar dr ups' -> ind_adm D ups nr ar dr ups -> ind_adm D ups' nr ar dr ups.
    Proof. intros * H' H; exact (adm_base _ _ H' H). Qed.

    Lemma adm_diag_r : forall ups', ind_adm D ups nr ar dr ups' -> ind_adm D ups' nr ar dr ups'.
    Proof. intros * H'; exact (adm_base _ _ H' H'). Qed.
  End IndPER.

  (** ** Changing the Relations

      The elements depend on the relations only where they are used: at
      the left parameters and arguments. *)
  Section FamChange.
    #[local] Set Default Proof Using "All".
    Variable (p : qname) (D : ind_decl) (ups : list domain).
    Variable (nr1 nr2 : nat -> list domain -> relation domain).
    Variable (ar1 ar2 : list domain -> String.string -> nat -> list domain -> relation domain).
    Variable (dr1 dr2 : list domain -> exp -> relation domain).
    Let T := List.rev (ind_nparams D).
    Hypothesis (Hn : forall k vs vs1 vs2, k < List.length T -> tele_pre nr1 k vs vs1 -> tele_pre nr2 k vs vs2 ->
                     (nr1 k vs <~> nr2 k vs)).
    Hypothesis (Ha : forall ms ms1 ms2 c gs k vs vs1 vs2, tele_full nr1 T ms ms1 -> tele_full nr2 T ms ms2 ->
                     ind_con D c = Some gs -> k < List.length (cargs_nonrec gs) ->
                     tele_pre (ar1 ms c) k vs vs1 -> tele_pre (ar2 ms c) k vs vs2 ->
                     (ar1 ms c k vs <~> ar2 ms c k vs)).
    Hypothesis (Hd : forall ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 k ys ys1 ys2,
                     tele_full nr1 T ms ms1 -> tele_full nr2 T ms ms2 ->
                     ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                     tele_pre (ar1 ms c) (List.length (cargs_nonrec gs1)) ws ws1 ->
                     tele_pre (ar2 ms c) (List.length (cargs_nonrec gs1)) ws ws2 ->
                     k < List.length (ptyp_doms t) ->
                     tele_pre (shape_tr dr1 ms ws (ptyp_doms t)) k ys ys1 ->
                     tele_pre (shape_tr dr2 ms ws (ptyp_doms t)) k ys ys2 ->
                     (shape_tr dr1 ms ws (ptyp_doms t) k ys <~> shape_tr dr2 ms ws (ptyp_doms t) k ys)).

    Lemma tele_full_nr_change : forall a b, tele_full nr1 T a b -> tele_full nr2 T a b.
    Proof. intros * H; apply (tele_full_map T nr1); [| exact H ]; intros; eapply Hn; eassumption. Qed.

    Lemma tele_full_nr_change' : forall a b, tele_full nr2 T a b -> tele_full nr1 T a b.
    Proof. intros * H; apply (tele_full_map T nr2); [| exact H ]; intros; eapply Hn; eassumption. Qed.

    Lemma tele_pre_nr_change' : forall k a b, k <= List.length T -> tele_pre nr2 k a b -> tele_pre nr1 k a b.
    Proof.
      intros * Hk H; rewrite tele_pre_full_iff in H |- *.
      apply (tele_full_map _ nr2); [| exact H ].
      intros j pa pb x y Hj Hp1 Hp2 Hr; rewrite List.repeat_length in Hj.
      eapply Hn; [ lia | exact Hp2 | exact Hp1 | exact Hr ].
    Qed.

    Lemma tele_pre_ar_change' : forall ms ms1 ms2 c gs k a b, tele_full nr1 T ms ms1 -> tele_full nr2 T ms ms2 ->
        ind_con D c = Some gs -> k <= List.length (cargs_nonrec gs) ->
        tele_pre (ar2 ms c) k a b -> tele_pre (ar1 ms c) k a b.
    Proof.
      intros * Hm1 Hm2 Hc Hk H; rewrite tele_pre_full_iff in H |- *.
      apply (tele_full_map _ (ar2 ms c)); [| exact H ].
      intros j pa pb x y Hj Hp1 Hp2 Hr; rewrite List.repeat_length in Hj.
      eapply Ha; [ exact Hm1 | exact Hm2 | exact Hc | lia | exact Hp2 | exact Hp1 | exact Hr ].
    Qed.

    Lemma tele_pre_ar_change : forall ms ms1 ms2 c gs k a b, tele_full nr1 T ms ms1 -> tele_full nr2 T ms ms2 ->
        ind_con D c = Some gs -> k <= List.length (cargs_nonrec gs) ->
        tele_pre (ar1 ms c) k a b -> tele_pre (ar2 ms c) k a b.
    Proof.
      intros * Hm1 Hm2 Hc Hk H; rewrite tele_pre_full_iff in H |- *.
      apply (tele_full_map _ (ar1 ms c)); [| exact H ].
      intros j pa pb x y Hj Hp1 Hp2 Hr; rewrite List.repeat_length in Hj.
      eapply Ha; [ exact Hm1 | exact Hm2 | exact Hc | lia | exact Hp1 | exact Hp2 | exact Hr ].
    Qed.

    Lemma tele_pre_sh_change : forall ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 k a b,
        tele_full nr1 T ms ms1 -> tele_full nr2 T ms ms2 -> ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        tele_pre (ar1 ms c) (List.length (cargs_nonrec gs1)) ws ws1 ->
        tele_pre (ar2 ms c) (List.length (cargs_nonrec gs1)) ws ws2 -> k <= List.length (ptyp_doms t) ->
        tele_pre (shape_tr dr1 ms ws (ptyp_doms t)) k a b -> tele_pre (shape_tr dr2 ms ws (ptyp_doms t)) k a b.
    Proof.
      intros * Hm1 Hm2 Hc Heq Hw1 Hw2 Hk H; rewrite tele_pre_full_iff in H |- *.
      apply (tele_full_map _ (shape_tr dr1 ms ws (ptyp_doms t))); [| exact H ].
      intros j pa pb x y Hj Hp1 Hp2 Hr; rewrite List.repeat_length in Hj.
      eapply Hd; [ exact Hm1 | exact Hm2 | exact Hc | exact Heq | exact Hw1 | exact Hw2 | lia | exact Hp1 | exact Hp2 | exact Hr ].
    Qed.

    Lemma tele_pre_sh_change' : forall ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 k a b,
        tele_full nr1 T ms ms1 -> tele_full nr2 T ms ms2 -> ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        tele_pre (ar1 ms c) (List.length (cargs_nonrec gs1)) ws ws1 ->
        tele_pre (ar2 ms c) (List.length (cargs_nonrec gs1)) ws ws2 -> k <= List.length (ptyp_doms t) ->
        tele_pre (shape_tr dr2 ms ws (ptyp_doms t)) k a b -> tele_pre (shape_tr dr1 ms ws (ptyp_doms t)) k a b.
    Proof.
      intros * Hm1 Hm2 Hc Heq Hw1 Hw2 Hk H; rewrite tele_pre_full_iff in H |- *.
      apply (tele_full_map _ (shape_tr dr2 ms ws (ptyp_doms t))); [| exact H ].
      intros j pa pb x y Hj Hp1 Hp2 Hr; rewrite List.repeat_length in Hj.
      eapply Hd; [ exact Hm1 | exact Hm2 | exact Hc | exact Heq | exact Hw1 | exact Hw2 | lia | exact Hp2 | exact Hp1 | exact Hr ].
    Qed.

    Lemma adm_change : forall ua, ind_adm D ups nr1 ar1 dr1 ua -> ind_adm D ups nr2 ar2 dr2 ua.
    Proof.
      intros ua [H1 H2 H3 H4]; constructor.
      - intros k A vs vs' s Hk Hp.
        assert (Hkl : k < List.length T) by (apply List.nth_error_Some; unfold T; congruence).
        pose proof (tele_pre_nr_change' k vs vs' ltac:(lia) Hp) as Hp1.
        destruct (H1 _ _ _ _ s Hk Hp1) as (a & a' & E & E' & R).
        exists a, a'; split; [ exact E | split; [ exact E' |] ].
        eapply Hn; [ exact Hkl | exact Hp1 | exact Hp | exact R ].
      - intros ms ms' c gs k A vs vs' s Hm Hc Hk Hp.
        assert (Hkl : k < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        pose proof (tele_full_nr_change' _ _ Hm) as Hm1.
        pose proof (tele_pre_ar_change' ms ms' ms' c gs k vs vs' Hm1 Hm Hc ltac:(lia) Hp) as Hp1.
        destruct (H2 _ _ _ _ _ _ _ _ s Hm1 Hc Hk Hp1) as (a & a' & E & E' & R).
        exists a, a'; split; [ exact E | split; [ exact E' |] ].
        eapply Ha; [ exact Hm1 | exact Hm | exact Hc | exact Hkl | exact Hp1 | exact Hp | exact R ].
      - intros ms ms' c gs gs1 t gs2 ws ws' ys ys' Hm Hc Heq Hp Hy.
        assert (Hk : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
          by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
        pose proof (tele_full_nr_change' _ _ Hm) as Hm1.
        pose proof (tele_pre_ar_change' _ _ _ _ _ _ _ _ Hm1 Hm Hc Hk Hp) as Hp1.
        assert (Hy1 : tele_full (shape_tr dr1 ms ws (ptyp_doms t)) (ptyp_doms t) ys ys').
        { apply tele_full_of_pre; eapply tele_pre_sh_change'; [ exact Hm1 | exact Hm | exact Hc | exact Heq | exact Hp1 | exact Hp
                                                              | lia | apply tele_full_pre; exact Hy ]. }
        destruct (H3 _ _ _ _ _ _ _ _ _ _ _ Hm1 Hc Heq Hp1 Hy1) as [bs bs' E E' R].
        exists bs bs'; [ exact E | exact E' | exact (tele_full_nr_change _ _ R) ].
      - intros ms ms' c gs gs1 t gs2 ws ws' k B ys ys' Hm Hc Heq Hp HB Hy.
        assert (Hk : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
          by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
        assert (Hkl : k < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
        pose proof (tele_full_nr_change' _ _ Hm) as Hm1.
        pose proof (tele_pre_ar_change' _ _ _ _ _ _ _ _ Hm1 Hm Hc Hk Hp) as Hp1.
        pose proof (tele_pre_sh_change' ms ms' ms' c gs gs1 t gs2 ws ws' ws' k ys ys' Hm1 Hm Hc Heq Hp1 Hp ltac:(lia) Hy) as Hy1.
        pose proof (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm1 Hm Hc Heq Hp1 Hp Hkl Hy1 Hy) as Hdd.
        unfold shape_tr in Hdd; rewrite (List.nth_error_nth _ _ _ HB) in Hdd.
        destruct (H4 _ _ _ _ _ _ _ _ _ _ _ _ _ Hm1 Hc Heq Hp1 HB Hy1) as (a & a' & E & E' & Ht).
        exists a, a'; split; [ exact E | split; [ exact E' |] ].
        intros x x' Hx; exact (Ht _ _ (proj2 (Hdd _ _) Hx)).
    Qed.

    Lemma ind_rel_change :
      (forall ns x y, ind_rel p D ups nr1 ar1 dr1 ns x y -> ind_rel p D ups nr2 ar2 dr2 ns x y) /\
      (forall pre gs vs vs', ind_args_rel p D ups nr1 ar1 dr1 pre gs vs vs' ->
         forall ns c gsf gs1 vp vp', pre = ns ++ nonrec_vals gs1 vp ->
           List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
           tele_full nr1 T ns ns -> ind_con D c = Some gsf -> gsf = gs1 ++ gs ->
           tele_full (ar1 ns c) (cargs_nonrec gsf) (nonrec_vals gsf (vp ++ vs)) (nonrec_vals gsf (vp' ++ vs')) ->
           ind_args_rel p D ups nr2 ar2 dr2 pre gs vs vs') /\
      (forall pre t v v', ind_shape_rel p D ups nr1 ar1 dr1 pre t v v' ->
         forall ns c gs1 t0 gs2 ws ws' k ys ys', pre = ns ++ ws ++ ys ->
           tele_full nr1 T ns ns -> ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
           tele_pre (ar1 ns c) (List.length (cargs_nonrec gs1)) ws ws' ->
           ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
           tele_pre (shape_tr dr1 ns ws (ptyp_doms t0)) k ys ys' ->
           ind_shape_rel p D ups nr2 ar2 dr2 pre t v v') /\
      (forall pre t f a f' a', ind_app_rel p D ups nr1 ar1 dr1 pre t f a f' a' ->
         forall ns c gs1 t0 gs2 ws ws' k ys ys', pre = ns ++ ws ++ ys ->
           tele_full nr1 T ns ns -> ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
           tele_pre (ar1 ns c) (List.length (cargs_nonrec gs1)) ws ws' ->
           ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
           tele_pre (shape_tr dr1 ns ws (ptyp_doms t0)) k ys ys' ->
           ind_app_rel p D ups nr2 ar2 dr2 pre t f a f' a').
    Proof.
      apply ind_rel_mut_ind_all.
      - intros * Hns Hc Hb Hb' Hs Hs' Har Hia IH.
        econstructor; try eassumption; try (apply tele_full_nr_change; eassumption).
        + apply (tele_full_map _ (ar1 ns c)); [| eassumption ].
          intros; eapply Ha; try eassumption; apply tele_full_nr_change; eassumption.
        + apply (IH ns c gs nil nil nil);
            [ cbn; rewrite List.app_nil_r; reflexivity | reflexivity | reflexivity | exact Hns | exact Hc | reflexivity | exact Har ].
      - intros; econstructor; try eassumption; try (apply tele_full_nr_change; eassumption); apply adm_change; eassumption.
      - intros; constructor.
      - intros * Hia IH ns c gsf gs1 vp vp' Hρ Hl Hl' Hn' Hc Heq Har.
        constructor.
        apply (IH ns c gsf (gs1 ++ ca_arg A :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil));
          [ rewrite Hρ, nonrec_vals_app, <- List.app_assoc by assumption; reflexivity
          | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
          | rewrite Heq, <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Har ].
      - intros * Hsh IHs Hia IH ns c gsf gs1 vp vp' Hρ Hl Hl' Hn' Hc Heq Har.
        pose proof (nonrec_prefix_gen _ _ _ _ _ _ _ _ Heq Hl Hl' Har) as Hpre.
        constructor.
        + apply (IHs ns c gs1 t gs (nonrec_vals gs1 vp) (nonrec_vals gs1 vp') 0 nil nil);
            [ rewrite List.app_nil_r; exact Hρ | exact Hn' | rewrite <- Heq; exact Hc | exact Hpre | reflexivity | lia
            | apply tele_pre_nil ].
        + apply (IH ns c gsf (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil));
            [ rewrite Hρ, nonrec_vals_app by assumption; cbn; rewrite List.app_nil_r; reflexivity
            | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
            | rewrite Heq, <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Har ].
      - intros * Hb Hr IHr; intros; econstructor; [ exact Hb | exact (IHr) ].
      - intros * Hf IH ns c gs1 t0 gs2 ws ws' k0 ys ys' Hρ Hn' Hc Hw Hs Hk Hy.
        destruct (ptyp_skip_pi _ _ _ _ Hs) as [HB Hs'].
        assert (Hkl : k0 < List.length (ptyp_doms t0)) by (apply List.nth_error_Some; congruence).
        pose proof (tele_full_nr_change _ _ Hn') as Hn2.
        assert (Hk1 : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
          by (rewrite cargs_nonrec_app, List.length_app; lia).
        pose proof (tele_pre_ar_change _ _ _ _ _ _ _ _ Hn' Hn2 Hc Hk1 Hw) as Hw2.
        pose proof (tele_pre_sh_change _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hn' Hn2 Hc eq_refl Hw Hw2 Hk Hy) as Hy2.
        pose proof (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hn' Hn2 Hc eq_refl Hw Hw2 Hkl Hy Hy2) as Hdd.
        unfold shape_tr in Hdd; rewrite (List.nth_error_nth _ _ _ HB) in Hdd.
        constructor; intros a a' Haa.
        subst pre; pose proof (proj2 (Hdd _ _) Haa) as Haa1.
        apply (IH a a' Haa1 ns c gs1 t0 gs2 ws ws' (S k0) (ys ++ a :: nil) (ys' ++ a' :: nil));
          [ rewrite <- !List.app_assoc; reflexivity | exact Hn' | exact Hc | exact Hw | exact Hs' | lia |].
        apply tele_pre_snoc; [ exact Hy |]; unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HB); exact Haa1.
      - intros * Ef Ef' Hsh IH; intros; econstructor; [ exact Ef | exact Ef' | eapply IH; eassumption ].
    Qed.
  End FamChange.
End Tele.
