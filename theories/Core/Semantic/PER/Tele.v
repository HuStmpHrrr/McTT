(** * Relations at Telescopes

    [tele_rel tr T vs vs'] relates two lists position by position, the
    [k]-th values at [tr k] of the two prefixes before them.  Every lemma
    here is about the lists only: it is used for the parameters and the
    arguments of inductive types, whose relations [tr] come from the PER
    model.  The one workhorse is [tele_rel_combine]: a fact at every position
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

  Lemma tele_rel_from_iff : forall tr vs vs' k pre,
      tele_rel_from tr k pre vs vs' <->
      List.length vs = List.length vs' /\
      forall j x x', List.nth_error vs j = Some x -> List.nth_error vs' j = Some x' ->
        tr (k + j) (pre ++ List.firstn j vs) x x'.
  Proof.
    induction vs as [| v vs IH]; intros [| v' vs'] k pre; cbn [tele_rel_from List.length].
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

  Lemma tele_rel_iff : forall {X} tr (T : list X) vs vs',
      tele_rel tr T vs vs' <->
      List.length vs = List.length T /\ List.length vs' = List.length T /\
      forall j x x', List.nth_error vs j = Some x -> List.nth_error vs' j = Some x' ->
        tr j (List.firstn j vs) x x'.
  Proof.
    intros; unfold tele_rel; rewrite tele_rel_from_iff; split.
    - intros (Hl & Hl' & Hr); split; [ exact Hl | split; [ congruence |] ]; exact Hr.
    - intros (Hl & Hl' & Hr); split; [ exact Hl | split; [ congruence | exact Hr ] ].
  Qed.

  Lemma tele_prefix_rel_iff : forall tr k vs vs',
      tele_prefix_rel tr k vs vs' <->
      List.length vs = k /\ List.length vs' = k /\
      forall j x x', List.nth_error vs j = Some x -> List.nth_error vs' j = Some x' ->
        tr j (List.firstn j vs) x x'.
  Proof.
    intros; unfold tele_prefix_rel; rewrite tele_rel_from_iff; split.
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
  Lemma tele_prefix_rel_of_full : forall {X} tr (T : list X) vs vs' k,
      tele_rel tr T vs vs' -> k <= List.length T ->
      tele_prefix_rel tr k (List.firstn k vs) (List.firstn k vs').
  Proof.
    intros * H Hk; rewrite tele_rel_iff in H; destruct H as (Hl & Hl' & Hr).
    rewrite tele_prefix_rel_iff; split; [ rewrite List.length_firstn; lia | split; [ rewrite List.length_firstn; lia |] ].
    intros j x x' Hx Hx'.
    assert (Hj : j < k) by (assert (Hn : List.nth_error (List.firstn k vs) j <> None) by congruence;
                            apply List.nth_error_Some in Hn; rewrite List.length_firstn in Hn; lia).
    rewrite nth_error_firstn_lt in Hx, Hx' by exact Hj.
    rewrite !firstn_firstn_le by lia; exact (Hr _ _ _ Hx Hx').
  Qed.

  Lemma tele_prefix_rel_of_pre : forall tr k vs vs' j,
      tele_prefix_rel tr k vs vs' -> j <= k ->
      tele_prefix_rel tr j (List.firstn j vs) (List.firstn j vs').
  Proof.
    intros * H Hk; eapply tele_prefix_rel_of_full with (T := List.repeat tt k); [| rewrite List.repeat_length; exact Hk ].
    rewrite tele_rel_iff, List.repeat_length; rewrite tele_prefix_rel_iff in H; exact H.
  Qed.

  Lemma tele_prefix_rel_nil : forall tr, tele_prefix_rel tr 0 nil nil.
  Proof. intros; split; [ reflexivity | exact I ]. Qed.

  Lemma tele_prefix_rel_snoc : forall tr k vs vs' x x',
      tele_prefix_rel tr k vs vs' -> tr k vs x x' ->
      tele_prefix_rel tr (S k) (vs ++ x :: nil) (vs' ++ x' :: nil).
  Proof.
    intros * H Hx; rewrite tele_prefix_rel_iff in *; destruct H as (Hl & Hl' & Hr).
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
  Lemma tele_rel_of_pre : forall {X} tr (T : list X) vs vs',
      tele_prefix_rel tr (List.length T) vs vs' -> tele_rel tr T vs vs'.
  Proof.
    intros * H; rewrite tele_prefix_rel_iff in H; rewrite tele_rel_iff; exact H.
  Qed.

  Lemma tele_rel_pre : forall {X} tr (T : list X) vs vs',
      tele_rel tr T vs vs' -> tele_prefix_rel tr (List.length T) vs vs'.
  Proof.
    intros * H; rewrite tele_rel_iff in H; rewrite tele_prefix_rel_iff; exact H.
  Qed.

  (** The workhorse: a fact at each position of up to three lists [L s],
      given the facts at the positions before it and the inputs there, holds
      of the whole lists. *)
  Lemma tele_rel_combine : forall {X} (T : list X) tr1 tr2 tr3 (L : nat -> list domain) s1 s1' s2 s2' s3 s3',
      (s3 = s1 \/ s3 = s1' \/ s3 = s2 \/ s3 = s2') ->
      (s3' = s1 \/ s3' = s1' \/ s3' = s2 \/ s3' = s2') ->
      (forall k x1 x1' x2 x2' x3 x3', k < List.length T ->
         tele_prefix_rel tr1 k (List.firstn k (L s1)) (List.firstn k (L s1')) ->
         tele_prefix_rel tr2 k (List.firstn k (L s2)) (List.firstn k (L s2')) ->
         tele_prefix_rel tr3 k (List.firstn k (L s3)) (List.firstn k (L s3')) ->
         List.nth_error (L s1) k = Some x1 -> List.nth_error (L s1') k = Some x1' ->
         List.nth_error (L s2) k = Some x2 -> List.nth_error (L s2') k = Some x2' ->
         List.nth_error (L s3) k = Some x3 -> List.nth_error (L s3') k = Some x3' ->
         tr1 k (List.firstn k (L s1)) x1 x1' ->
         tr2 k (List.firstn k (L s2)) x2 x2' ->
         tr3 k (List.firstn k (L s3)) x3 x3') ->
      tele_rel tr1 T (L s1) (L s1') -> tele_rel tr2 T (L s2) (L s2') -> tele_rel tr3 T (L s3) (L s3').
  Proof.
    intros * Hs3 Hs3' Hstep H1 H2.
    pose proof H1 as H1'; pose proof H2 as H2'.
    rewrite tele_rel_iff in H1', H2'; destruct H1' as (Hl1 & Hl1' & Hr1); destruct H2' as (Hl2 & Hl2' & Hr2).
    assert (Hl3 : List.length (L s3) = List.length T) by (destruct Hs3 as [-> | [-> | [-> | ->]]]; assumption).
    assert (Hl3' : List.length (L s3') = List.length T) by (destruct Hs3' as [-> | [-> | [-> | ->]]]; assumption).
    apply tele_rel_of_pre.
    assert (Hall : forall k, k <= List.length T -> tele_prefix_rel tr3 k (List.firstn k (L s3)) (List.firstn k (L s3'))).
    { induction k as [| k IH]; intros Hk; [ apply tele_prefix_rel_nil |].
      assert (Hlt : k < List.length T) by lia.
      destruct (nth_error_lt_some' (L s1) k ltac:(lia)) as [x1 E1].
      destruct (nth_error_lt_some' (L s1') k ltac:(lia)) as [x1' E1'].
      destruct (nth_error_lt_some' (L s2) k ltac:(lia)) as [x2 E2].
      destruct (nth_error_lt_some' (L s2') k ltac:(lia)) as [x2' E2'].
      destruct (nth_error_lt_some' (L s3) k ltac:(lia)) as [x3 E3].
      destruct (nth_error_lt_some' (L s3') k ltac:(lia)) as [x3' E3'].
      rewrite (firstn_S_snoc _ _ _ E3), (firstn_S_snoc _ _ _ E3').
      apply tele_prefix_rel_snoc; [ apply IH; lia |].
      eapply Hstep; try eassumption;
        [ apply tele_prefix_rel_of_full with (T := T); [ exact H1 | lia ]
        | apply tele_prefix_rel_of_full with (T := T); [ exact H2 | lia ]
        | apply IH; lia
        | exact (Hr1 _ _ _ E1 E1') | exact (Hr2 _ _ _ E2 E2') ]. }
    specialize (Hall _ (le_n _)); rewrite !List.firstn_all2 in Hall by lia; exact Hall.
  Qed.

  (** ** Lists of Arguments *)

  Lemma env_args_snoc : forall ρ vs v, env_args ρ (vs ++ v :: nil) = env_args ρ vs ↦ v.
  Proof. intros; unfold env_args; rewrite List.fold_left_app; reflexivity. Qed.

  Lemma cargs_nonrec_app : forall gs gs', cargs_nonrec (gs ++ gs') = cargs_nonrec gs ++ cargs_nonrec gs'.
  Proof. induction gs as [| [] gs IH]; intros; cbn; rewrite ?IH; reflexivity. Qed.

  Lemma nonrec_arg_vals_app : forall gs gs' vs vs', List.length vs = List.length gs ->
      nonrec_arg_vals (gs ++ gs') (vs ++ vs') = nonrec_arg_vals gs vs ++ nonrec_arg_vals gs' vs'.
  Proof.
    induction gs as [| [] gs IH]; intros gs' [| v vs] vs' Hl; cbn in *; try discriminate; try reflexivity;
      rewrite IH by lia; reflexivity.
  Qed.

  Lemma length_nonrec_arg_vals : forall gs vs, List.length vs = List.length gs ->
      List.length (nonrec_arg_vals gs vs) = List.length (cargs_nonrec gs).
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
      ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms1 -> ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms2 -> ms1 = ms2.
  Proof. intros; eapply (proj1 (proj2 (proj2 (@functional_eval gc_deps gc_stack)))); eassumption. Qed.

  Lemma per_top_ps_sym : forall T vs vs', per_top_ps T vs vs' -> per_top_ps T vs' vs.
  Proof. intros * H s; destruct (H s) as (Ms & H1 & H2); eauto. Qed.

  Lemma per_top_ps_trans : forall T vs vs' vs'', per_top_ps T vs vs' -> per_top_ps T vs' vs'' -> per_top_ps T vs vs''.
  Proof.
    intros * H H' s; destruct (H s) as (Ms & H1 & H2); destruct (H' s) as (Ms' & H1' & H2').
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (@functional_read gc_deps gc_stack))))) _ _ _ _ _ H2 _ H1') as <-.
    eauto.
  Qed.

  (** ** Derived Forms of [tele_rel_combine] *)

  Lemma tele_rel_map : forall {X} (T : list X) tr1 tr2 a b,
      (forall k pa pb x y, k < List.length T -> tele_prefix_rel tr1 k pa pb -> tele_prefix_rel tr2 k pa pb ->
         tr1 k pa x y -> tr2 k pa x y) ->
      tele_rel tr1 T a b -> tele_rel tr2 T a b.
  Proof.
    intros * Hs H.
    apply (tele_rel_combine T tr1 tr1 tr2 (fun n => match n with 0 => a | _ => b end) 0 1 0 1 0 1);
      [ left; reflexivity | right; left; reflexivity | | exact H | exact H ].
    intros k * Hk Hp1 _ Hp3 E1 E1' _ _ E3 E3' Hr1 _.
    rewrite E1 in E3; injection E3 as <-; rewrite E1' in E3'; injection E3' as <-.
    exact (Hs _ _ _ _ _ Hk Hp1 Hp3 Hr1).
  Qed.

  Lemma tele_rel_flip : forall {X} (T : list X) tr1 tr2 a b,
      (forall k pa pb x y, k < List.length T -> tele_prefix_rel tr1 k pa pb -> tele_prefix_rel tr2 k pb pa ->
         tr1 k pa x y -> tr2 k pb y x) ->
      tele_rel tr1 T a b -> tele_rel tr2 T b a.
  Proof.
    intros * Hs H.
    apply (tele_rel_combine T tr1 tr1 tr2 (fun n => match n with 0 => a | _ => b end) 0 1 0 1 1 0);
      [ right; left; reflexivity | left; reflexivity | | exact H | exact H ].
    intros k * Hk Hp1 _ Hp3 E1 E1' _ _ E3 E3' Hr1 _.
    rewrite E1' in E3; injection E3 as <-; rewrite E1 in E3'; injection E3' as <-.
    exact (Hs _ _ _ _ _ Hk Hp1 Hp3 Hr1).
  Qed.

  Lemma tele_rel_compose : forall {X} (T : list X) tr1 tr2 tr3 a b c,
      (forall k pa pb pc x y z, k < List.length T -> tele_prefix_rel tr1 k pa pb -> tele_prefix_rel tr2 k pb pc ->
         tele_prefix_rel tr3 k pa pc -> tr1 k pa x y -> tr2 k pb y z -> tr3 k pa x z) ->
      tele_rel tr1 T a b -> tele_rel tr2 T b c -> tele_rel tr3 T a c.
  Proof.
    intros * Hs H1 H2.
    apply (tele_rel_combine T tr1 tr2 tr3 (fun n => match n with 0 => a | 1 => b | _ => c end) 0 1 1 2 0 2);
      [ left; reflexivity | right; right; right; reflexivity | | exact H1 | exact H2 ].
    intros k * Hk Hp1 Hp2 Hp3 E1 E1' E2 E2' E3 E3' Hr1 Hr2.
    rewrite E1 in E3; injection E3 as <-; rewrite E2' in E3'; injection E3' as <-.
    rewrite E1' in E2; injection E2 as <-.
    exact (Hs _ _ _ _ _ _ _ Hk Hp1 Hp2 Hp3 Hr1 Hr2).
  Qed.

  Lemma tele_prefix_rel_full_iff : forall tr k a b, tele_prefix_rel tr k a b <-> tele_rel tr (List.repeat tt k) a b.
  Proof. intros; rewrite tele_prefix_rel_iff, tele_rel_iff, List.repeat_length; reflexivity. Qed.

  (** Across two families whose relations agree along related prefixes. *)
  Lemma tele_rel_cross_refl : forall {X} (T : list X) tr1 tr2 a b,
      (forall k pa pb, k < List.length T -> tele_prefix_rel tr1 k pa pb -> tele_prefix_rel tr2 k pb pb -> (tr1 k pa <~> tr2 k pb)) ->
      (forall k vs vs', k < List.length T -> tele_prefix_rel tr2 k vs vs' -> PER (tr2 k vs)) ->
      tele_rel tr1 T a b -> tele_rel tr2 T b b.
  Proof.
    intros * Heq HP H.
    apply (tele_rel_combine T tr1 tr1 tr2 (fun n => match n with 0 => a | _ => b end) 0 1 0 1 1 1);
      [ right; left; reflexivity | right; left; reflexivity | | exact H | exact H ].
    intros k * Hk Hp1 _ Hp3 E1 E1' _ _ E3 E3' Hr1 _.
    rewrite E1' in E3; injection E3 as <-; rewrite E1' in E3'; injection E3' as <-.
    pose proof (HP _ _ _ Hk Hp3) as HPer.
    apply (Heq _ _ _ Hk Hp1 Hp3) in Hr1.
    etransitivity; [ symmetry |]; exact Hr1.
  Qed.

  Lemma tele_rel_compose_cross : forall {X} (T : list X) tr1 tr2 a b c,
      (forall k pa pb pc, k < List.length T -> tele_prefix_rel tr1 k pa pb -> tele_prefix_rel tr2 k pb pc -> (tr1 k pa <~> tr2 k pb)) ->
      (forall k vs vs', k < List.length T -> tele_prefix_rel tr1 k vs vs' -> PER (tr1 k vs)) ->
      tele_rel tr1 T a b -> tele_rel tr2 T b c -> tele_rel tr1 T a c.
  Proof.
    intros * Heq HP H1 H2.
    apply (tele_rel_compose T tr1 tr2 tr1 a b c); [| exact H1 | exact H2 ].
    intros k pa pb pc x y z Hk Hp1 Hp2 _ Hr1 Hr2.
    pose proof (HP _ _ _ Hk Hp1) as HPer.
    apply (Heq _ _ _ _ Hk Hp1 Hp2) in Hr2.
    etransitivity; eassumption.
  Qed.

  Lemma tele_prefix_rel_cross_refl : forall tr1 tr2 n k a b, k <= n ->
      (forall j pa pb, j < n -> tele_prefix_rel tr1 j pa pb -> tele_prefix_rel tr2 j pb pb -> (tr1 j pa <~> tr2 j pb)) ->
      (forall j vs vs', j < n -> tele_prefix_rel tr2 j vs vs' -> PER (tr2 j vs)) ->
      tele_prefix_rel tr1 k a b -> tele_prefix_rel tr2 k b b.
  Proof.
    intros * Hk Heq HP H; rewrite tele_prefix_rel_full_iff in *.
    eapply tele_rel_cross_refl; [| | exact H ]; rewrite List.repeat_length; intros; [ eapply Heq | eapply HP ]; eauto; lia.
  Qed.

  (** ** A Telescope of PERs

      A family [tr] of PERs, each invariant along related prefixes, makes
      [tele_rel tr T] a PER on lists. *)
  Section TelePER.
    Variable (n : nat) (tr : nat -> list domain -> relation domain).
    Hypothesis (HP : forall k vs vs', k < n -> tele_prefix_rel tr k vs vs' -> PER (tr k vs)).
    Hypothesis (HI : forall k vs vs', k < n -> tele_prefix_rel tr k vs vs' -> (tr k vs <~> tr k vs')).

    Lemma tele_rel_sym : forall {X} (T : list X) a b, List.length T <= n -> tele_rel tr T a b -> tele_rel tr T b a.
    Proof.
      intros * Hn H; apply (tele_rel_flip T tr tr); [| exact H ].
      intros k pa pb x y Hk Hp1 _ Hr.
      pose proof (HP k pa pb ltac:(lia) Hp1) as HPer.
      apply (HI k pa pb ltac:(lia) Hp1); symmetry; exact Hr.
    Qed.

    Lemma tele_rel_trans : forall {X} (T : list X) a b c, List.length T <= n ->
        tele_rel tr T a b -> tele_rel tr T b c -> tele_rel tr T a c.
    Proof.
      intros * Hn H1 H2; apply (tele_rel_compose T tr tr tr _ b); [| exact H1 | exact H2 ].
      intros k pa pb pc x y z Hk Hp1 Hp2 _ Hr1 Hr2.
      pose proof (HP k pa pb ltac:(lia) Hp1) as HPer.
      apply (HI k pa pb ltac:(lia) Hp1) in Hr2; etransitivity; eassumption.
    Qed.

    Lemma tele_rel_refl_r : forall {X} (T : list X) a b, List.length T <= n -> tele_rel tr T a b -> tele_rel tr T b b.
    Proof. intros * Hn H; eapply tele_rel_trans; [ exact Hn | apply tele_rel_sym; [ exact Hn | exact H ] | exact H ]. Qed.

    Lemma tele_prefix_rel_sym : forall k a b, k <= n -> tele_prefix_rel tr k a b -> tele_prefix_rel tr k b a.
    Proof.
      intros * Hk H; rewrite tele_prefix_rel_full_iff in *; apply tele_rel_sym; [ rewrite List.repeat_length; exact Hk | exact H ].
    Qed.

    Lemma tele_prefix_rel_trans : forall k a b c, k <= n -> tele_prefix_rel tr k a b -> tele_prefix_rel tr k b c -> tele_prefix_rel tr k a c.
    Proof.
      intros * Hk H1 H2; rewrite tele_prefix_rel_full_iff in *; eapply tele_rel_trans; [ rewrite List.repeat_length; exact Hk | exact H1 | exact H2 ].
    Qed.

    Lemma tele_prefix_rel_refl_l : forall k a b, k <= n -> tele_prefix_rel tr k a b -> tele_prefix_rel tr k a a.
    Proof. intros * Hk H; eapply tele_prefix_rel_trans; [ exact Hk | exact H | apply tele_prefix_rel_sym; [ exact Hk | exact H ] ]. Qed.

    Lemma tele_prefix_rel_refl_r : forall k a b, k <= n -> tele_prefix_rel tr k a b -> tele_prefix_rel tr k b b.
    Proof. intros * Hk H; eapply tele_prefix_rel_trans; [ exact Hk | apply tele_prefix_rel_sym; [ exact Hk | exact H ] | exact H ]. Qed.
  End TelePER.

  (** ** The Elements of an Inductive Type, Generically

      The lemmas below need only the conditions the clause of
      [per_univ_elem_core] for inductive types states on the relations
      [nparams_rel] and [args_rel]: each is a PER, invariant along related prefixes and
      instances, and the recursive instances of related arguments are
      related (the closures). *)

  Lemma nparams_lt_ass : forall D m Mm k, grp_tele_ass D -> ind_member D m = Some Mm ->
      k < List.length (List.rev (im_nparams Mm)) -> exists A, List.nth_error (List.rev (im_nparams Mm)) k = Some (ce_ass A).
  Proof.
    intros * Hass HM Hk; destruct (nth_error_lt_some' _ _ Hk) as [e He].
    assert (Hf : List.Forall (fun e => exists A, e = ce_ass A) (List.rev (im_nparams Mm)))
      by (apply List.Forall_rev; exact (gta_nparams _ Hass _ _ HM)).
    rewrite List.Forall_forall in Hf; destruct (Hf e (List.nth_error_In _ _ He)) as [A ->]; eauto.
  Qed.

  Lemma nonrec_prefix_gen : forall tr gsf gs1 gs vp vp' vs vs', gsf = gs1 ++ gs ->
      List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
      tele_rel tr (cargs_nonrec gsf) (nonrec_arg_vals gsf (vp ++ vs)) (nonrec_arg_vals gsf (vp' ++ vs')) ->
      tele_prefix_rel tr (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vp) (nonrec_arg_vals gs1 vp').
  Proof.
    intros * Heq Hl Hl' Ha.
    pose proof (tele_prefix_rel_of_full _ _ _ _ (List.length (cargs_nonrec gs1)) Ha) as H.
    rewrite Heq, cargs_nonrec_app, List.length_app in H; specialize (H ltac:(lia)).
    rewrite !nonrec_arg_vals_app in H by assumption.
    rewrite !(firstn_app_exact (nonrec_arg_vals gs1 _)) in H by (apply length_nonrec_arg_vals; assumption).
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
      List.length (ptyp_doms t0) <= k /\ ptyp_mem t0 = j /\ ptyp_ps t0 = Ps.
  Proof.
    induction k as [| k IH]; intros [] * H; cbn in *; try discriminate.
    - injection H as -> ->; split; [ lia | split; reflexivity ].
    - injection H as -> ->; split; [ lia | split; reflexivity ].
    - destruct (IH _ _ _ H) as (? & ? & ?); split; [ lia | split; assumption ].
  Qed.

  (** The rest of a shape after its domains is its end, and before them a
      domain. *)
  Lemma ptyp_skip_end : forall t, ptyp_skip (List.length (ptyp_doms t)) t = pt_self (ptyp_mem t) (ptyp_ps t).
  Proof. induction t as [j Ps | B t IH]; cbn; [ reflexivity | exact IH ]. Qed.

  Lemma ptyp_skip_lt : forall k t, k < List.length (ptyp_doms t) ->
      exists B, List.nth_error (ptyp_doms t) k = Some B /\ ptyp_skip k t = pt_pi B (ptyp_skip (S k) t).
  Proof.
    induction k as [| k IH]; intros [k0 Ps | B0 t0] H; cbn in *; try lia; [ eauto |].
    exact (IH t0 ltac:(lia)).
  Qed.

  Lemma per_top_sym' : forall a b, per_top a b -> per_top b a.
  Proof. intros * H s; destruct (H s) as (L & H1 & H2); eauto. Qed.

  Lemma per_top_trans' : forall a b d, per_top a b -> per_top b d -> per_top a d.
  Proof.
    intros * H1 H2 s; destruct (H1 s) as (L & HL1 & HL2); destruct (H2 s) as (L' & HL2' & HL3).
    pose proof (functional_read_nf _ _ _ _ HL2 HL2') as <-; eauto.
  Qed.

  Lemma functional_fresh_tele' : forall ρ T s vs vs', Ftele T in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ vs ->
      Ftele T in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ vs' -> vs = vs'.
  Proof.
    intros * H; revert vs'; induction H; intros vs' H'; inversion H'; subst; [ reflexivity |].
    functional_eval_rewrite_clear; f_equal; auto.
  Qed.

  (** The fresh variables of a telescope, related. *)
  Lemma fresh_tele_rel_ftele : forall tr u ua k pre pre' s T, fresh_tele_rel tr u ua k pre pre' s T ->
      exists ws ws', Ftele T in gc_deps ⍮ gc_stack ⍮ env_args nil (u ++ pre) ⍮ s ↘ ws /\
        Ftele T in gc_deps ⍮ gc_stack ⍮ env_args nil (ua ++ pre') ⍮ s ↘ ws' /\
        List.length ws = List.length T /\ tele_rel_from tr k pre ws ws'.
  Proof.
    induction 1 as [k pre pre' s | k pre pre' s A T a a' Ea Ea' Hr H IH]; [ exists nil, nil; repeat split; constructor |].
    destruct IH as (ws & ws' & F & F' & Hl & Hw).
    exists (⇑! a s :: ws), (⇑! a' s :: ws'); split; [| split; [| split ] ].
    - econstructor; [ exact Ea |]; rewrite <- env_args_snoc, <- List.app_assoc; exact F.
    - econstructor; [ exact Ea' |]; rewrite <- env_args_snoc, <- List.app_assoc; exact F'.
    - cbn; rewrite Hl; reflexivity.
    - cbn; split; [ exact Hr | exact Hw ].
  Qed.




  Section IndPER.
    #[local] Set Default Proof Using "All".
    Variable (p : qname) (D : ind_decl) (ups : list domain).
    Variable (nparams_rel : nat -> nat -> list domain -> relation domain).
    Variable (args_rel : nat -> list domain -> String.string -> nat -> list domain -> relation domain).
    Variable (doms_rel : nat -> list domain -> exp -> relation domain).
    Hypothesis (Hass : grp_tele_ass D).
    Hypothesis (HnP : nparams_per D nparams_rel) (HnI : nparams_inv D nparams_rel).
    Hypothesis (HaP : args_per D nparams_rel args_rel) (HaI : args_inv D nparams_rel args_rel).
    Hypothesis (HdP : doms_per D nparams_rel args_rel doms_rel) (HdI : doms_inv D nparams_rel args_rel doms_rel).

    (** *** At One Member *)
    Section Member.
      Variable (m : nat) (Mm : imember).
      Hypothesis (HM : ind_member D m = Some Mm).
      Let T := List.rev (im_nparams Mm).

    Lemma nparams_rel_per : forall k vs vs', k < List.length T -> tele_prefix_rel (nparams_rel m) k vs vs' -> PER (nparams_rel m k vs).
    Proof. intros * Hk H; destruct (nparams_lt_ass D m Mm k Hass HM Hk) as [A HA]; eapply HnP; eassumption. Qed.

    Lemma nparams_rel_invariant : forall k vs vs', k < List.length T -> tele_prefix_rel (nparams_rel m) k vs vs' ->
        (nparams_rel m k vs <~> nparams_rel m k vs').
    Proof. intros * Hk H; destruct (nparams_lt_ass D m Mm k Hass HM Hk) as [A HA]; eapply HnI; eassumption. Qed.

    Lemma nparams_rel_sym : forall a b, tele_rel (nparams_rel m) T a b -> tele_rel (nparams_rel m) T b a.
    Proof. intros; eapply (tele_rel_sym (List.length T) (nparams_rel m) nparams_rel_per nparams_rel_invariant); [ lia | eassumption ]. Qed.

    Lemma nparams_rel_trans : forall a b c, tele_rel (nparams_rel m) T a b -> tele_rel (nparams_rel m) T b c -> tele_rel (nparams_rel m) T a c.
    Proof. intros; eapply (tele_rel_trans (List.length T) (nparams_rel m) nparams_rel_per nparams_rel_invariant); [ lia | eassumption | eassumption ]. Qed.

    Lemma nparams_rel_refl_l : forall a b, tele_rel (nparams_rel m) T a b -> tele_rel (nparams_rel m) T a a.
    Proof. intros * H; exact (nparams_rel_trans _ _ _ H (nparams_rel_sym _ _ H)). Qed.

    Lemma nparams_rel_refl_r : forall a b, tele_rel (nparams_rel m) T a b -> tele_rel (nparams_rel m) T b b.
    Proof. intros * H; exact (nparams_rel_trans _ _ _ (nparams_rel_sym _ _ H) H). Qed.

    Section Args.
      Variable (ms : list domain) (c : String.string) (gs : list carg).
      Hypothesis (Hms : tele_rel (nparams_rel m) T ms ms) (Hc : ind_con Mm c = Some gs).

      Lemma args_rel_per : forall k vs vs', k < List.length (cargs_nonrec gs) -> tele_prefix_rel (args_rel m ms c) k vs vs' ->
          PER (args_rel m ms c k vs).
      Proof. intros * Hk H; destruct (nth_error_lt_some' _ _ Hk) as [A HA]; eapply HaP; eassumption. Qed.

      Lemma args_rel_invariant : forall k vs vs', k < List.length (cargs_nonrec gs) -> tele_prefix_rel (args_rel m ms c) k vs vs' ->
          (args_rel m ms c k vs <~> args_rel m ms c k vs').
      Proof.
        intros * Hk H; destruct (nth_error_lt_some' _ _ Hk) as [A HA].
        exact (HaI _ _ _ _ _ _ _ _ _ _ HM Hms Hc HA H).
      Qed.

      Lemma args_rel_sym : forall a b, tele_rel (args_rel m ms c) (cargs_nonrec gs) a b -> tele_rel (args_rel m ms c) (cargs_nonrec gs) b a.
      Proof. intros; eapply (tele_rel_sym (List.length (cargs_nonrec gs)) _ args_rel_per args_rel_invariant); [ lia | eassumption ]. Qed.

      Lemma args_rel_trans : forall a b d, tele_rel (args_rel m ms c) (cargs_nonrec gs) a b -> tele_rel (args_rel m ms c) (cargs_nonrec gs) b d ->
          tele_rel (args_rel m ms c) (cargs_nonrec gs) a d.
      Proof. intros; eapply (tele_rel_trans (List.length (cargs_nonrec gs)) _ args_rel_per args_rel_invariant); [ lia | eassumption | eassumption ]. Qed.

      Lemma args_rel_pre_refl_l : forall k a b, k <= List.length (cargs_nonrec gs) -> tele_prefix_rel (args_rel m ms c) k a b ->
          tele_prefix_rel (args_rel m ms c) k a a.
      Proof. intros; eapply (tele_prefix_rel_refl_l (List.length (cargs_nonrec gs)) _ args_rel_per args_rel_invariant); eassumption. Qed.

      Lemma args_rel_pre_sym : forall k a b, k <= List.length (cargs_nonrec gs) -> tele_prefix_rel (args_rel m ms c) k a b ->
          tele_prefix_rel (args_rel m ms c) k b a.
      Proof. intros; eapply (tele_prefix_rel_sym (List.length (cargs_nonrec gs)) _ args_rel_per args_rel_invariant); eassumption. Qed.
    End Args.

    (** The argument relation at an instance related to another. *)
    Lemma args_rel_inst : forall ms ms' c gs a b, tele_rel (nparams_rel m) T ms ms' -> ind_con Mm c = Some gs ->
        tele_rel (args_rel m ms c) (cargs_nonrec gs) a b -> tele_rel (args_rel m ms' c) (cargs_nonrec gs) a b.
    Proof.
      intros * Hm Hc H; apply (tele_rel_map _ (args_rel m ms c)); [| exact H ].
      intros k pa pb x y Hk Hp1 _ Hr.
      destruct (nth_error_lt_some' _ _ Hk) as [A HA].
      assert (Hrefl : tele_prefix_rel (args_rel m ms c) k pa pa)
        by (eapply (args_rel_pre_refl_l ms c gs (nparams_rel_refl_l _ _ Hm) Hc); [ lia | exact Hp1 ]).
      apply (HaI _ _ _ _ _ _ _ _ _ _ HM Hm Hc HA Hrefl); exact Hr.
    Qed.

    Lemma nparams_prefix_rel_sym : forall k a b, k <= List.length T -> tele_prefix_rel (nparams_rel m) k a b ->
        tele_prefix_rel (nparams_rel m) k b a.
    Proof. intros; eapply (tele_prefix_rel_sym (List.length T) (nparams_rel m) nparams_rel_per nparams_rel_invariant); eassumption. Qed.

    Lemma args_prefix_rel_inst : forall ms ms' c gs k a b, tele_rel (nparams_rel m) T ms ms' -> ind_con Mm c = Some gs ->
        k <= List.length (cargs_nonrec gs) -> tele_prefix_rel (args_rel m ms c) k a b -> tele_prefix_rel (args_rel m ms' c) k a b.
    Proof.
      intros * Hm Hc Hk H.
      rewrite tele_prefix_rel_full_iff in H |- *.
      apply (tele_rel_map _ (args_rel m ms c)); [| exact H ].
      intros j pa pb x y Hj Hp1 _ Hr; rewrite List.repeat_length in Hj.
      destruct (nth_error_lt_some' (cargs_nonrec gs) j ltac:(lia)) as [A HA].
      assert (Hrefl : tele_prefix_rel (args_rel m ms c) j pa pa)
        by (eapply (args_rel_pre_refl_l ms c gs (nparams_rel_refl_l _ _ Hm) Hc); [ lia | exact Hp1 ]).
      apply (HaI _ _ _ _ _ _ _ _ _ _ HM Hm Hc HA Hrefl); exact Hr.
    Qed.

    Lemma args_prefix_rel_sym : forall ms c gs k a b, tele_rel (nparams_rel m) T ms ms -> ind_con Mm c = Some gs ->
        k <= List.length (cargs_nonrec gs) -> tele_prefix_rel (args_rel m ms c) k a b -> tele_prefix_rel (args_rel m ms c) k b a.
    Proof. intros; eapply (args_rel_pre_sym ms c gs); eassumption. Qed.

    Lemma nparams_prefix_rel_refl_l : forall k a b, k <= List.length T -> tele_prefix_rel (nparams_rel m) k a b ->
        tele_prefix_rel (nparams_rel m) k a a.
    Proof. intros; eapply (tele_prefix_rel_refl_l (List.length T) (nparams_rel m) nparams_rel_per nparams_rel_invariant); eassumption. Qed.

    Lemma nparams_prefix_rel_refl_r : forall k a b, k <= List.length T -> tele_prefix_rel (nparams_rel m) k a b ->
        tele_prefix_rel (nparams_rel m) k b b.
    Proof. intros; eapply (tele_prefix_rel_refl_r (List.length T) (nparams_rel m) nparams_rel_per nparams_rel_invariant); eassumption. Qed.

    (** An instance of the arguments' relation at the right instance and
        prefix, on the diagonal. *)
    Lemma args_prefix_rel_refl_r : forall ms ms' c gs k a b, tele_rel (nparams_rel m) T ms ms' -> ind_con Mm c = Some gs ->
        k <= List.length (cargs_nonrec gs) -> tele_prefix_rel (args_rel m ms c) k a b -> tele_prefix_rel (args_rel m ms' c) k b b.
    Proof.
      intros * Hm Hc Hk H.
      pose proof (args_prefix_rel_inst _ _ _ _ _ _ _ Hm Hc Hk H) as H'.
      eapply (args_rel_pre_refl_l ms' c gs (nparams_rel_refl_r _ _ Hm) Hc); [ exact Hk |].
      eapply (args_rel_pre_sym ms' c gs (nparams_rel_refl_r _ _ Hm) Hc); [ exact Hk | exact H' ].
    Qed.

    (** ** The Domains of a Shape

        At an instance and a prefix of the arguments on the diagonal, the
        domains of a recursive argument's shape are a telescope of PERs. *)
    Section Shape.
      Variable (ms : list domain) (c : String.string) (gs gs1 : list carg) (t : ptyp) (gs2 : list carg) (ws : list domain).
      Hypothesis (Hms : tele_rel (nparams_rel m) T ms ms) (Hc : ind_con Mm c = Some gs) (Heq : gs = gs1 ++ ca_rec t :: gs2)
                 (Hws : tele_prefix_rel (args_rel m ms c) (List.length (cargs_nonrec gs1)) ws ws).

      Lemma doms_rel_per : forall k ys ys', k < List.length (ptyp_doms t) ->
          tele_prefix_rel (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t)) k ys ys' ->
          PER (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t) k ys).
      Proof.
        intros * Hk H; destruct (nth_error_lt_some' _ _ Hk) as [B HB]; unfold shape_doms_rel at 1.
        rewrite (List.nth_error_nth _ _ _ HB); eapply HdP; eassumption.
      Qed.

      Lemma doms_rel_invariant : forall k ys ys', k < List.length (ptyp_doms t) ->
          tele_prefix_rel (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t)) k ys ys' ->
          (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t) k ys <~> shape_doms_rel (doms_rel m) ms ws (ptyp_doms t) k ys').
      Proof.
        intros * Hk H; destruct (nth_error_lt_some' _ _ Hk) as [B HB]; unfold shape_doms_rel.
        rewrite (List.nth_error_nth _ _ _ HB); eapply HdI; eassumption.
      Qed.

      Lemma doms_rel_sym : forall k a b, k <= List.length (ptyp_doms t) ->
          tele_prefix_rel (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t)) k a b ->
          tele_prefix_rel (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t)) k b a.
      Proof. intros; eapply (tele_prefix_rel_sym (List.length (ptyp_doms t)) _ doms_rel_per doms_rel_invariant); eassumption. Qed.

      Lemma doms_rel_refl_l : forall k a b, k <= List.length (ptyp_doms t) ->
          tele_prefix_rel (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t)) k a b ->
          tele_prefix_rel (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t)) k a a.
      Proof. intros; eapply (tele_prefix_rel_refl_l (List.length (ptyp_doms t)) _ doms_rel_per doms_rel_invariant); eassumption. Qed.

      Lemma doms_rel_refl_r : forall k a b, k <= List.length (ptyp_doms t) ->
          tele_prefix_rel (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t)) k a b ->
          tele_prefix_rel (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t)) k b b.
      Proof. intros; eapply (tele_prefix_rel_refl_r (List.length (ptyp_doms t)) _ doms_rel_per doms_rel_invariant); eassumption. Qed.
    End Shape.

    (** The domains' telescope at another instance and prefix related to
        the diagonal one. *)
    Lemma doms_rel_inst : forall ms ms' c gs gs1 t gs2 ws ws' k a b, tele_rel (nparams_rel m) T ms ms' -> ind_con Mm c = Some gs ->
        gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (args_rel m ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
        k <= List.length (ptyp_doms t) ->
        tele_prefix_rel (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t)) k a b ->
        tele_prefix_rel (shape_doms_rel (doms_rel m) ms' ws' (ptyp_doms t)) k a b.
    Proof.
      intros * Hm Hc Heq Hw Hk H.
      assert (Hww : tele_prefix_rel (args_rel m ms c) (List.length (cargs_nonrec gs1)) ws ws).
      { eapply (args_rel_pre_refl_l ms c gs (nparams_rel_refl_l _ _ Hm) Hc); [| exact Hw ].
        rewrite Heq, cargs_nonrec_app, List.length_app; lia. }
      rewrite tele_prefix_rel_full_iff in H |- *.
      apply (tele_rel_map _ (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t))); [| exact H ].
      intros j pa pb x y Hj Hp1 _ Hr; rewrite List.repeat_length in Hj.
      destruct (nth_error_lt_some' (ptyp_doms t) j ltac:(lia)) as [B HB].
      assert (Hrefl : tele_prefix_rel (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t)) j pa pa)
        by (eapply (doms_rel_refl_l ms c gs gs1 t gs2 ws (nparams_rel_refl_l _ _ Hm) Hc Heq Hww); [ lia | exact Hp1 ]).
      unfold shape_doms_rel in Hr |- *; rewrite (List.nth_error_nth _ _ _ HB) in Hr |- *.
      apply (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hc Heq Hw HB Hrefl); exact Hr.
    Qed.

    Lemma doms_rel_refl_inst : forall ms ms' c gs gs1 t gs2 ws ws' k a b, tele_rel (nparams_rel m) T ms ms' -> ind_con Mm c = Some gs ->
        gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (args_rel m ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
        k <= List.length (ptyp_doms t) ->
        tele_prefix_rel (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t)) k a b ->
        tele_prefix_rel (shape_doms_rel (doms_rel m) ms' ws' (ptyp_doms t)) k b b.
    Proof.
      intros * Hm Hc Heq Hw Hk H.
      assert (Hk1 : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      assert (Hw' : tele_prefix_rel (args_rel m ms' c) (List.length (cargs_nonrec gs1)) ws' ws')
        by exact (args_prefix_rel_refl_r ms ms' c gs _ ws ws' Hm Hc Hk1 Hw).
      pose proof (doms_rel_inst _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw Hk H) as H'.
      eapply (doms_rel_refl_r ms' c gs gs1 t gs2 ws' (nparams_rel_refl_r _ _ Hm) Hc Heq Hw'); [ exact Hk |].
      exact H'.
    Qed.
    End Member.

    Lemma shape_k_le : forall gs gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
        List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs).
    Proof. intros * ->; rewrite cargs_nonrec_app, List.length_app; lia. Qed.

    Lemma nth_error_lt' : forall {A} (l : list A) k a, List.nth_error l k = Some a -> k < List.length l.
    Proof. intros * H; apply List.nth_error_Some; congruence. Qed.

    (** *** At the Member a Shape Ends In *)
    Lemma ntele_rel_member : forall j a b, ntele_rel D nparams_rel j a b ->
        exists Mj, ind_member D j = Some Mj /\ tele_rel (nparams_rel j) (List.rev (im_nparams Mj)) a b.
    Proof. unfold ntele_rel; intros j a b; destruct (ind_member D j) as [Mj |]; [ eauto | intros [] ]. Qed.

    Lemma ntele_rel_of : forall j Mj a b, ind_member D j = Some Mj -> tele_rel (nparams_rel j) (List.rev (im_nparams Mj)) a b ->
        ntele_rel D nparams_rel j a b.
    Proof. unfold ntele_rel; intros * -> H; exact H. Qed.

    Lemma ntele_rel_sym : forall j a b, ntele_rel D nparams_rel j a b -> ntele_rel D nparams_rel j b a.
    Proof.
      intros * H; destruct (ntele_rel_member _ _ _ H) as (Mj & Hj & H'); eapply ntele_rel_of; [ exact Hj |].
      exact (nparams_rel_sym _ _ Hj _ _ H').
    Qed.

    Lemma ntele_rel_trans : forall j a b c, ntele_rel D nparams_rel j a b -> ntele_rel D nparams_rel j b c -> ntele_rel D nparams_rel j a c.
    Proof.
      intros * H1 H2; destruct (ntele_rel_member _ _ _ H1) as (Mj & Hj & H1'); destruct (ntele_rel_member _ _ _ H2) as (Mj' & Hj' & H2').
      rewrite Hj in Hj'; injection Hj' as <-; eapply ntele_rel_of; [ exact Hj |].
      exact (nparams_rel_trans _ _ Hj _ _ _ H1' H2').
    Qed.

    Lemma ntele_rel_refl_l : forall j a b, ntele_rel D nparams_rel j a b -> ntele_rel D nparams_rel j a a.
    Proof. intros * H; exact (ntele_rel_trans _ _ _ _ H (ntele_rel_sym _ _ _ H)). Qed.

    Lemma ntele_rel_refl_r : forall j a b, ntele_rel D nparams_rel j a b -> ntele_rel D nparams_rel j b b.
    Proof. intros * H; exact (ntele_rel_trans _ _ _ _ (ntele_rel_sym _ _ _ H) H). Qed.

    (** *** Admissibility at Every Prefix *)

    (** Admissibility at another base admissible beside [ups]. *)
    Lemma adm_base : forall u1 u2, adm_uparams D ups nparams_rel args_rel doms_rel u1 ->
        adm_uparams D ups nparams_rel args_rel doms_rel u2 -> adm_uparams D u1 nparams_rel args_rel doms_rel u2.
    Proof.
      intros u1 u2 [H1n H1a H1c H1d] [H2n H2a H2c H2d]; constructor.
      - intros m Mm k A vs vs' s HM Hk Hp.
        assert (Hkl : k < List.length (List.rev (im_nparams Mm))) by (apply List.nth_error_Some; congruence).
        destruct (H1n _ _ _ _ _ _ s HM Hk (nparams_prefix_rel_refl_l _ _ HM k vs vs' ltac:(lia) Hp)) as [a0 a1 E0 E1 R1].
        destruct (H2n _ _ _ _ _ _ s HM Hk Hp) as [b0 a2 F0 E2 R2].
        functional_eval_rewrite_clear.
        pose proof (HnP _ _ _ _ _ _ HM Hk Hp) as HP.
        exists a1 a2; [ exact E1 | exact E2 |].
        etransitivity; [ symmetry; exact R1 | exact R2 ].
      - intros m Mm ms ms' c gs k A vs vs' s HM Hm Hc Hk Hp.
        assert (Hkl : k < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        pose proof (nparams_rel_refl_l _ _ HM _ _ Hm) as Hmm.
        destruct (H1a _ _ _ _ _ _ _ _ _ _ s HM Hmm Hc Hk (args_rel_pre_refl_l _ _ HM ms c gs Hmm Hc k vs vs' ltac:(lia) Hp))
          as [a0 a1 E0 E1 R1].
        destruct (H2a _ _ _ _ _ _ _ _ _ _ s HM Hm Hc Hk Hp) as [b0 a2 F0 E2 R2].
        functional_eval_rewrite_clear.
        pose proof (HaP _ _ _ _ _ _ _ _ _ _ HM Hm Hc Hk Hp) as HP.
        exists a1 a2; [ exact E1 | exact E2 |].
        etransitivity; [ symmetry; exact R1 | exact R2 ].
      - intros m Mm ms ms' c gs gs1 t gs2 ws ws' ys ys' HM Hm Hc Heq Hp Hy.
        pose proof (shape_k_le _ _ _ _ Heq) as Hk.
        pose proof (nparams_rel_refl_l _ _ HM _ _ Hm) as Hmm.
        pose proof (args_rel_pre_refl_l _ _ HM ms c gs Hmm Hc _ ws ws' Hk Hp) as Hww.
        assert (Hyy : tele_rel (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t)) (ptyp_doms t) ys ys)
          by (apply tele_rel_of_pre; eapply (doms_rel_refl_l _ _ HM ms c gs gs1 t gs2 ws Hmm Hc Heq Hww);
              [ lia | apply tele_rel_pre; exact Hy ]).
        destruct (H1c _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hmm Hc Heq Hww Hyy) as [b0 b1 E0 E1 H01].
        destruct (H2c _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hc Heq Hp Hy) as [b0' b2 E0' E2 H02].
        pose proof (functional_eval_exps' _ _ _ _ E0 E0') as <-.
        exists b1 b2; [ exact E1 | exact E2 | exact (ntele_rel_trans _ _ _ _ (ntele_rel_sym _ _ _ H01) H02) ].
      - intros m Mm ms ms' c gs gs1 t gs2 ws ws' k B ys ys' HM Hm Hc Heq Hp HB Hy.
        pose proof (shape_k_le _ _ _ _ Heq) as Hk.
        pose proof (nth_error_lt' _ _ _ HB) as Hkl.
        pose proof (nparams_rel_refl_l _ _ HM _ _ Hm) as Hmm.
        pose proof (args_rel_pre_refl_l _ _ HM ms c gs Hmm Hc _ ws ws' Hk Hp) as Hww.
        pose proof (doms_rel_refl_l _ _ HM ms c gs gs1 t gs2 ws Hmm Hc Heq Hww k ys ys' ltac:(lia) Hy) as Hyy.
        pose proof (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hmm Hc Heq Hww HB Hyy) as HPd.
        destruct (H1d _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hmm Hc Heq Hww HB Hyy) as [a0 a1 E0 E1 T1].
        destruct (H2d _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hc Heq Hp HB Hy) as [a0' a2 E0' E2 T2].
        functional_eval_rewrite_clear.
        exists a1 a2; [ exact E1 | exact E2 |].
        intros x x' Hx.
        assert (Hxx : doms_rel m (ms ++ ws ++ ys) B x x) by (etransitivity; [ exact Hx | symmetry; exact Hx ]).
        exact (per_top_trans' _ _ _ (per_top_sym' _ _ (T1 _ _ Hxx)) (T2 _ _ Hx)).
    Qed.

    (** Admissibility composes. *)
    Lemma adm_compose : forall u1 u2, adm_uparams D ups nparams_rel args_rel doms_rel u1 ->
        adm_uparams D u1 nparams_rel args_rel doms_rel u2 -> adm_uparams D ups nparams_rel args_rel doms_rel u2.
    Proof.
      intros u1 u2 [H1n H1a H1c H1d] [H2n H2a H2c H2d]; constructor.
      - intros m Mm k A vs vs' s HM Hk Hp.
        assert (Hkl : k < List.length (List.rev (im_nparams Mm))) by (apply List.nth_error_Some; congruence).
        destruct (H1n _ _ _ _ _ _ s HM Hk Hp) as [a0 a1 E0 E1 R1].
        destruct (H2n _ _ _ _ _ _ s HM Hk (nparams_prefix_rel_refl_r _ _ HM k vs vs' ltac:(lia) Hp)) as [b1 a2 F1 E2 R2].
        functional_eval_rewrite_clear.
        pose proof (HnP _ _ _ _ _ _ HM Hk Hp) as HP.
        apply (HnI _ _ _ _ _ _ HM Hk Hp) in R2.
        exists a0 a2; [ exact E0 | exact E2 |].
        etransitivity; [ exact R1 | exact R2 ].
      - intros m Mm ms ms' c gs k A vs vs' s HM Hm Hc Hk Hp.
        assert (Hkl : k < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        destruct (H1a _ _ _ _ _ _ _ _ _ _ s HM Hm Hc Hk Hp) as [a0 a1 E0 E1 R1].
        destruct (H2a _ _ _ _ _ _ _ _ _ _ s HM (nparams_rel_refl_r _ _ HM _ _ Hm) Hc Hk
                    (args_prefix_rel_refl_r _ _ HM ms ms' c gs k vs vs' Hm Hc ltac:(lia) Hp))
          as [b1 a2 F1 E2 R2].
        functional_eval_rewrite_clear.
        pose proof (HaP _ _ _ _ _ _ _ _ _ _ HM Hm Hc Hk Hp) as HP.
        apply (HaI _ _ _ _ _ _ _ _ _ _ HM Hm Hc Hk Hp) in R2.
        exists a0 a2; [ exact E0 | exact E2 |].
        etransitivity; [ exact R1 | exact R2 ].
      - intros m Mm ms ms' c gs gs1 t gs2 ws ws' ys ys' HM Hm Hc Heq Hp Hy.
        pose proof (shape_k_le _ _ _ _ Heq) as Hk.
        pose proof (args_prefix_rel_refl_r _ _ HM _ _ _ _ _ _ _ Hm Hc Hk Hp) as Hw'.
        assert (Hy' : tele_rel (shape_doms_rel (doms_rel m) ms' ws' (ptyp_doms t)) (ptyp_doms t) ys' ys')
          by (apply tele_rel_of_pre; eapply doms_rel_refl_inst;
              [ exact HM | exact Hm | exact Hc | exact Heq | exact Hp | lia | apply tele_rel_pre; exact Hy ]).
        destruct (H1c _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hc Heq Hp Hy) as [b0 b1 E0 E1 H01].
        destruct (H2c _ _ _ _ _ _ _ _ _ _ _ _ _ HM (nparams_rel_refl_r _ _ HM _ _ Hm) Hc Heq Hw' Hy') as [b1' b2 E1' E2 H12].
        pose proof (functional_eval_exps' _ _ _ _ E1 E1') as <-.
        exists b0 b2; [ exact E0 | exact E2 | exact (ntele_rel_trans _ _ _ _ H01 H12) ].
      - intros m Mm ms ms' c gs gs1 t gs2 ws ws' k B ys ys' HM Hm Hc Heq Hp HB Hy.
        pose proof (shape_k_le _ _ _ _ Heq) as Hk.
        pose proof (nth_error_lt' _ _ _ HB) as Hkl.
        pose proof (args_prefix_rel_refl_r _ _ HM _ _ _ _ _ _ _ Hm Hc Hk Hp) as Hw'.
        pose proof (doms_rel_refl_inst _ _ HM ms ms' c gs gs1 t gs2 ws ws' k ys ys' Hm Hc Heq Hp ltac:(lia) Hy) as Hy'.
        pose proof (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM (nparams_rel_refl_r _ _ HM _ _ Hm) Hc Heq Hw' HB Hy') as HPd.
        destruct (H1d _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hc Heq Hp HB Hy) as [a0 a1 E0 E1 T1].
        destruct (H2d _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM (nparams_rel_refl_r _ _ HM _ _ Hm) Hc Heq Hw' HB Hy') as [a1' a2 E1' E2 T2].
        pose proof (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hc Heq Hp HB Hy) as HdIe.
        functional_eval_rewrite_clear.
        exists a0 a2; [ exact E0 | exact E2 |].
        intros x x' Hx.
        pose proof (proj1 (HdIe _ _) Hx) as Hx'.
        assert (Hxx : doms_rel m (ms' ++ ws' ++ ys') B x' x') by (etransitivity; [ symmetry; exact Hx' | exact Hx' ]).
        exact (per_top_trans' _ _ _ (T1 _ _ Hx) (T2 _ _ Hxx)).
    Qed.

    Lemma nonrec_prefix : forall m Mm ns c gsf gs1 gs vp vp' vs vs', ind_member D m = Some Mm ->
        tele_rel (nparams_rel m) (List.rev (im_nparams Mm)) ns ns -> ind_con Mm c = Some gsf -> gsf = gs1 ++ gs ->
        List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
        tele_rel (args_rel m ns c) (cargs_nonrec gsf) (nonrec_arg_vals gsf (vp ++ vs)) (nonrec_arg_vals gsf (vp' ++ vs')) ->
        tele_prefix_rel (args_rel m ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vp) (nonrec_arg_vals gs1 vp').
    Proof. intros * _ _ _ Heq Hl Hl' Ha; exact (nonrec_prefix_gen _ _ _ _ _ _ _ _ Heq Hl Hl' Ha). Qed.

    Lemma nonrec_prefix_refl : forall m Mm ns c gsf gs1 gs vp vp' vs vs', ind_member D m = Some Mm ->
        tele_rel (nparams_rel m) (List.rev (im_nparams Mm)) ns ns -> ind_con Mm c = Some gsf -> gsf = gs1 ++ gs ->
        List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
        tele_rel (args_rel m ns c) (cargs_nonrec gsf) (nonrec_arg_vals gsf (vp ++ vs)) (nonrec_arg_vals gsf (vp' ++ vs')) ->
        tele_prefix_rel (args_rel m ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vp) (nonrec_arg_vals gs1 vp).
    Proof.
      intros * HM Hns Hc Heq Hl Hl' Ha.
      eapply (args_rel_pre_refl_l _ _ HM ns c gsf Hns Hc); [ rewrite Heq, cargs_nonrec_app, List.length_app; lia |].
      eapply nonrec_prefix; eassumption.
    Qed.

    Lemma nonrec_arg_vals_snoc_arg : forall gs1 vp A v, List.length vp = List.length gs1 ->
        nonrec_arg_vals (gs1 ++ ca_arg A :: nil) (vp ++ v :: nil) = nonrec_arg_vals gs1 vp ++ v :: nil.
    Proof. intros; rewrite nonrec_arg_vals_app by assumption; reflexivity. Qed.

    Lemma nonrec_arg_vals_snoc_rec : forall gs1 vp t v, List.length vp = List.length gs1 ->
        nonrec_arg_vals (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil) = nonrec_arg_vals gs1 vp.
    Proof. intros; rewrite nonrec_arg_vals_app by assumption; cbn; rewrite List.app_nil_r; reflexivity. Qed.

    (** A shape's invariants: its domains after the arguments before it
        related on the diagonal, [k] of them consumed. *)
    Lemma shape_pi_step : forall m Mm ns c gs1 t0 gs2 ws ws' k ys ys' B t, ind_member D m = Some Mm ->
        tele_rel (nparams_rel m) (List.rev (im_nparams Mm)) ns ns -> ind_con Mm c = Some (gs1 ++ ca_rec t0 :: gs2) ->
        tele_prefix_rel (args_rel m ns c) (List.length (cargs_nonrec gs1)) ws ws' ->
        ptyp_skip k t0 = pt_pi B t -> tele_prefix_rel (shape_doms_rel (doms_rel m) ns ws (ptyp_doms t0)) k ys ys' ->
        List.nth_error (ptyp_doms t0) k = Some B /\ ptyp_skip (S k) t0 = t /\ S k <= List.length (ptyp_doms t0) /\
        PER (doms_rel m (ns ++ ws ++ ys) B) /\
        (forall a a', doms_rel m (ns ++ ws ++ ys) B a a' ->
           tele_prefix_rel (shape_doms_rel (doms_rel m) ns ws (ptyp_doms t0)) (S k) (ys ++ a :: nil) (ys' ++ a' :: nil)).
    Proof.
      intros * HM Hns Hc Hw Hs Hy.
      destruct (ptyp_skip_pi _ _ _ _ Hs) as [HB Hs'].
      pose proof (nth_error_lt' _ _ _ HB) as Hkl.
      pose proof (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hns Hc eq_refl Hw HB Hy) as HP.
      split; [ exact HB | split; [ exact Hs' | split; [ lia | split; [ exact HP |] ] ] ].
      intros a a' Ha; apply tele_prefix_rel_snoc; [ exact Hy |].
      unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Ha.
    Qed.

    (** *** The Elements

        Each element is read at its own parameters, so the relation is
        symmetric by swapping its sides and transitive by sharing the
        middle element's evaluations; no base is moved, and no
        admissibility is used. *)

    (** Weakening the admissible bases and indices. *)
    Lemma ind_rel_ok : forall (adm1 adm2 : nat -> list domain -> Prop) (okr1 okr2 : nat -> list domain -> list exp -> list domain -> Prop),
        (forall k u, adm1 k u -> adm2 k u) -> (forall j pre Ps bs, okr1 j pre Ps bs -> okr2 j pre Ps bs) ->
        (forall k u u' ns ns' x y, ind_rel p D adm1 okr1 nparams_rel args_rel doms_rel k u u' ns ns' x y ->
           ind_rel p D adm2 okr2 nparams_rel args_rel doms_rel k u u' ns ns' x y) /\
        (forall k u u' pre pre' gs vs vs', con_args_rel p D adm1 okr1 nparams_rel args_rel doms_rel k u u' pre pre' gs vs vs' ->
           con_args_rel p D adm2 okr2 nparams_rel args_rel doms_rel k u u' pre pre' gs vs vs') /\
        (forall k u u' pre pre' t v v', rec_arg_rel p D adm1 okr1 nparams_rel args_rel doms_rel k u u' pre pre' t v v' ->
           rec_arg_rel p D adm2 okr2 nparams_rel args_rel doms_rel k u u' pre pre' t v v') /\
        (forall k u u' pre pre' t f a f' a', rec_arg_app_rel p D adm1 okr1 nparams_rel args_rel doms_rel k u u' pre pre' t f a f' a' ->
           rec_arg_app_rel p D adm2 okr2 nparams_rel args_rel doms_rel k u u' pre pre' t f a f' a').
    Proof. intros * HO HK; apply ind_rel_mut_ind_all; intros; econstructor; eauto. Qed.

    Lemma ind_rel_sym_all : forall adm okr,
        (forall k u u' ns ns' x y, ind_rel p D adm okr nparams_rel args_rel doms_rel k u u' ns ns' x y ->
           ind_rel p D adm okr nparams_rel args_rel doms_rel k u' u ns' ns y x) /\
        (forall k u u' pre pre' gs vs vs', con_args_rel p D adm okr nparams_rel args_rel doms_rel k u u' pre pre' gs vs vs' ->
           forall Mk ms ms' c gsf gs1 vp vp', ind_member D k = Some Mk ->
             pre = ms ++ nonrec_arg_vals gs1 vp -> pre' = ms' ++ nonrec_arg_vals gs1 vp' ->
             List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
             tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ms ms' -> ind_con Mk c = Some gsf -> gsf = gs1 ++ gs ->
             tele_rel (args_rel k ms c) (cargs_nonrec gsf) (nonrec_arg_vals gsf (vp ++ vs)) (nonrec_arg_vals gsf (vp' ++ vs')) ->
             con_args_rel p D adm okr nparams_rel args_rel doms_rel k u' u pre' pre gs vs' vs) /\
        (forall k u u' pre pre' t v v', rec_arg_rel p D adm okr nparams_rel args_rel doms_rel k u u' pre pre' t v v' ->
           forall Mk ms ms' c gs1 t0 gs2 ws ws' kk ys ys', ind_member D k = Some Mk ->
             pre = ms ++ ws ++ ys -> pre' = ms' ++ ws' ++ ys' ->
             tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ms ms' -> ind_con Mk c = Some (gs1 ++ ca_rec t0 :: gs2) ->
             tele_prefix_rel (args_rel k ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
             ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
             tele_prefix_rel (shape_doms_rel (doms_rel k) ms ws (ptyp_doms t0)) kk ys ys' ->
             rec_arg_rel p D adm okr nparams_rel args_rel doms_rel k u' u pre' pre t v' v) /\
        (forall k u u' pre pre' t f a f' a', rec_arg_app_rel p D adm okr nparams_rel args_rel doms_rel k u u' pre pre' t f a f' a' ->
           forall Mk ms ms' c gs1 t0 gs2 ws ws' kk ys ys', ind_member D k = Some Mk ->
             pre = ms ++ ws ++ ys -> pre' = ms' ++ ws' ++ ys' ->
             tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ms ms' -> ind_con Mk c = Some (gs1 ++ ca_rec t0 :: gs2) ->
             tele_prefix_rel (args_rel k ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
             ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
             tele_prefix_rel (shape_doms_rel (doms_rel k) ms ws (ptyp_doms t0)) kk ys ys' ->
             rec_arg_app_rel p D adm okr nparams_rel args_rel doms_rel k u' u pre' pre t f' a' f a).
    Proof.
      intros adm okr; apply ind_rel_mut_ind_all.
      - intros * HM Hr Hn Hc Hb Hb' Hs Hs' Ha Hia IH.
        assert (Hm : tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) (List.skipn (im_unu D Mk) bs) (List.skipn (im_unu D Mk) bs'))
          by exact (nparams_rel_trans _ _ HM _ _ _ (nparams_rel_trans _ _ HM _ _ _ (nparams_rel_sym _ _ HM _ _ Hs) Hn) Hs').
        econstructor; [ exact HM | exact Hr | exact (nparams_rel_sym _ _ HM _ _ Hn) | exact Hc | exact Hb' | exact Hb | exact Hs' | exact Hs
                      | exact (args_rel_inst _ _ HM _ _ _ _ _ _ Hm Hc
                                 (args_rel_sym _ _ HM _ _ _ (nparams_rel_refl_l _ _ HM _ _ Hm) Hc _ _ Ha)) |].
        apply (IH Mk (List.skipn (im_unu D Mk) bs) (List.skipn (im_unu D Mk) bs') c gs nil nil nil HM);
          cbn; rewrite ?List.app_nil_r; try reflexivity; assumption.
      - intros * HM Hh Hn L1 L2 O1 O2 H1 H2 Hm.
        econstructor; try eassumption; [ exact (nparams_rel_sym _ _ HM _ _ Hn) |].
        intros s; destruct (Hm s) as (L & HL & HL'); eauto.
      - intros; constructor.
      - intros * Hia IH Mk ms ms' c gsf gs1 vp vp' HM Hρ Hρ' Hl Hl' Hn Hc Heq Ha.
        constructor.
        apply (IH Mk ms ms' c gsf (gs1 ++ ca_arg A :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil) HM);
          [ rewrite Hρ, nonrec_arg_vals_snoc_arg, List.app_assoc by assumption; reflexivity
          | rewrite Hρ', nonrec_arg_vals_snoc_arg, List.app_assoc by assumption; reflexivity
          | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
          | rewrite Heq, <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Ha ].
      - intros * Hsh IHs Hia IH Mk ms ms' c gsf gs1 vp vp' HM Hρ Hρ' Hl Hl' Hn Hc Heq Ha.
        pose proof (nonrec_prefix _ _ _ _ _ _ _ _ _ _ _ HM (nparams_rel_refl_l _ _ HM _ _ Hn) Hc Heq Hl Hl' Ha) as Hpre.
        constructor.
        + apply (IHs Mk ms ms' c gs1 t gs (nonrec_arg_vals gs1 vp) (nonrec_arg_vals gs1 vp') 0 nil nil HM);
            [ rewrite List.app_nil_r; exact Hρ | rewrite List.app_nil_r; exact Hρ' | exact Hn | rewrite <- Heq; exact Hc
            | exact Hpre | reflexivity | lia | apply tele_prefix_rel_nil ].
        + apply (IH Mk ms ms' c gsf (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil) HM);
            [ rewrite Hρ, nonrec_arg_vals_snoc_rec by assumption; reflexivity
            | rewrite Hρ', nonrec_arg_vals_snoc_rec by assumption; reflexivity
            | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
            | rewrite Heq, <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Ha ].
      - (** The recursive argument: the two evaluations are swapped. *)
        intros * E E' O O' Hr IHr.
        intros; econstructor; [ exact E' | exact E | exact O' | exact O | exact IHr ].
      - intros * Hf IH Mk ms ms' c gs1 t0 gs2 ws ws' k0 ys ys' HM Hρ Hρ' Hn Hc Hw Hs Hk Hy.
        pose proof (nparams_rel_refl_l _ _ HM _ _ Hn) as Hnn.
        destruct (shape_pi_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hnn Hc Hw Hs Hy) as (HB & Hs' & Hk' & HP & Hstep).
        subst pre pre'.
        constructor; intros a a' Haa.
        pose proof (proj2 (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hn Hc eq_refl Hw HB Hy _ _) Haa) as Haa0.
        assert (Hsym : doms_rel k (ms ++ ws ++ ys) B a' a) by (symmetry; exact Haa0).
        apply (IH a' a Hsym Mk ms ms' c gs1 t0 gs2 ws ws' (S k0) (ys ++ a' :: nil) (ys' ++ a :: nil) HM);
          [ rewrite <- !List.app_assoc; reflexivity | rewrite <- !List.app_assoc; reflexivity
          | exact Hn | exact Hc | exact Hw | exact Hs' | exact Hk' |].
        apply Hstep; exact Hsym.
      - intros * Ef Ef' Hsh IH; intros.
        econstructor; [ exact Ef' | exact Ef | eapply IH; eassumption ].
    Qed.

    (** Inverting an element on its left: its form fixes the constructor,
        the parameters and the arguments. *)
    Lemma ind_rel_con_inv : forall adm okr k u u' ns ns' Mk hd k' c bs vs z,
        ind_rel p D adm okr nparams_rel args_rel doms_rel k u u' ns ns' (d_con hd k' c (bs ++ vs)) z ->
        ind_member D k = Some Mk -> List.length bs = (im_unu D Mk + im_nn Mk)%nat ->
        exists gs bs' vs', z = d_con hd k' c (bs' ++ vs') /\ im_ref p k Mk = (hd, k') /\
          tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ns ns' /\ ind_con Mk c = Some gs /\
          List.length bs' = (im_unu D Mk + im_nn Mk)%nat /\
          tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ns (List.skipn (im_unu D Mk) bs) /\
          tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ns' (List.skipn (im_unu D Mk) bs') /\
          tele_rel (args_rel k (List.skipn (im_unu D Mk) bs) c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') /\
          con_args_rel p D adm okr nparams_rel args_rel doms_rel k u u'
            (List.skipn (im_unu D Mk) bs) (List.skipn (im_unu D Mk) bs') gs vs vs'.
    Proof.
      intros * H HM Hl; inversion H as [k0 Mk0 hd0 k'0 ns0 ns0' c0 gs bs0 bs' vs0 vs' u0 u0' HM0 Hr Hn Hc Hb Hb' Hs Hs' Ha Hia |]; subst.
      rewrite HM in HM0; injection HM0 as <-.
      match goal with He : _ ++ _ = bs ++ vs |- _ => destruct (app_split_eq _ _ _ _ He ltac:(congruence)) as [-> ->] end.
      exists gs, bs', vs'; exact (conj eq_refl (conj Hr (conj Hn (conj Hc (conj Hb' (conj Hs (conj Hs' (conj Ha Hia)))))))).
    Qed.

    (** Transitivity, at any indices: at a recursive argument the middle
        element's evaluation is literally shared, so no evaluation fact is
        used. *)
    Lemma ind_rel_trans_all : forall adm okr,
        (forall k u1 u2 ns1 ns2 x y, ind_rel p D adm okr nparams_rel args_rel doms_rel k u1 u2 ns1 ns2 x y ->
           forall u3 ns3 ns4 z, ind_rel p D adm okr nparams_rel args_rel doms_rel k u2 u3 ns3 ns4 y z ->
             ind_rel p D adm okr nparams_rel args_rel doms_rel k u1 u3 ns1 ns4 x z) /\
        (forall k u1 u2 pre1 pre2 gs vs1 vs2, con_args_rel p D adm okr nparams_rel args_rel doms_rel k u1 u2 pre1 pre2 gs vs1 vs2 ->
           forall u3 pre3 vs3 Mk ms1 ms2 c gsf gs1 vp1 vp2, ind_member D k = Some Mk ->
             pre1 = ms1 ++ nonrec_arg_vals gs1 vp1 -> pre2 = ms2 ++ nonrec_arg_vals gs1 vp2 ->
             List.length vp1 = List.length gs1 -> List.length vp2 = List.length gs1 ->
             tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ms1 ms2 -> ind_con Mk c = Some gsf -> gsf = gs1 ++ gs ->
             tele_rel (args_rel k ms1 c) (cargs_nonrec gsf) (nonrec_arg_vals gsf (vp1 ++ vs1)) (nonrec_arg_vals gsf (vp2 ++ vs2)) ->
             con_args_rel p D adm okr nparams_rel args_rel doms_rel k u2 u3 pre2 pre3 gs vs2 vs3 ->
             con_args_rel p D adm okr nparams_rel args_rel doms_rel k u1 u3 pre1 pre3 gs vs1 vs3) /\
        (forall k u1 u2 pre1 pre2 t v1 v2, rec_arg_rel p D adm okr nparams_rel args_rel doms_rel k u1 u2 pre1 pre2 t v1 v2 ->
           forall u3 pre3 v3 Mk ms1 ms2 c gs1 t0 gs2 ws1 ws2 kk ys1 ys2, ind_member D k = Some Mk ->
             pre1 = ms1 ++ ws1 ++ ys1 -> pre2 = ms2 ++ ws2 ++ ys2 ->
             tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ms1 ms2 -> ind_con Mk c = Some (gs1 ++ ca_rec t0 :: gs2) ->
             tele_prefix_rel (args_rel k ms1 c) (List.length (cargs_nonrec gs1)) ws1 ws2 ->
             ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
             tele_prefix_rel (shape_doms_rel (doms_rel k) ms1 ws1 (ptyp_doms t0)) kk ys1 ys2 ->
             rec_arg_rel p D adm okr nparams_rel args_rel doms_rel k u2 u3 pre2 pre3 t v2 v3 ->
             rec_arg_rel p D adm okr nparams_rel args_rel doms_rel k u1 u3 pre1 pre3 t v1 v3) /\
        (forall k u1 u2 pre1 pre2 t f1 a1 f2 a2, rec_arg_app_rel p D adm okr nparams_rel args_rel doms_rel k u1 u2 pre1 pre2 t f1 a1 f2 a2 ->
           forall u3 pre3 f3 a3 Mk ms1 ms2 c gs1 t0 gs2 ws1 ws2 kk ys1 ys2, ind_member D k = Some Mk ->
             pre1 = ms1 ++ ws1 ++ ys1 -> pre2 = ms2 ++ ws2 ++ ys2 ->
             tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ms1 ms2 -> ind_con Mk c = Some (gs1 ++ ca_rec t0 :: gs2) ->
             tele_prefix_rel (args_rel k ms1 c) (List.length (cargs_nonrec gs1)) ws1 ws2 ->
             ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
             tele_prefix_rel (shape_doms_rel (doms_rel k) ms1 ws1 (ptyp_doms t0)) kk ys1 ys2 ->
             rec_arg_app_rel p D adm okr nparams_rel args_rel doms_rel k u2 u3 pre2 pre3 t f2 a2 f3 a3 ->
             rec_arg_app_rel p D adm okr nparams_rel args_rel doms_rel k u1 u3 pre1 pre3 t f1 a1 f3 a3).
    Proof.
      intros adm okr; apply ind_rel_mut_ind_all.
      - intros k Mk hd k' ns1 ns2 c gs bs1 bs2 vs1 vs2 u1 u2 HM Hr Hn Hc Hb1 Hb2 Hs1 Hs2 Ha Hia IH u3 ns3 ns4 z Hz.
        destruct (ind_rel_con_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hz HM Hb2)
          as (gs0 & bs3 & vs3 & -> & _ & Hn' & Hc0 & Hb3 & Hs2' & Hs3 & Ha' & Hia').
        rewrite Hc in Hc0; injection Hc0 as <-.
        assert (H12 : tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) (List.skipn (im_unu D Mk) bs1) (List.skipn (im_unu D Mk) bs2))
          by exact (nparams_rel_trans _ _ HM _ _ _ (nparams_rel_trans _ _ HM _ _ _ (nparams_rel_sym _ _ HM _ _ Hs1) Hn) Hs2).
        eapply ind_rel_con with (gs := gs);
          [ exact HM | exact Hr
          | exact (nparams_rel_trans _ _ HM _ _ _ (nparams_rel_trans _ _ HM _ _ _ Hn
                     (nparams_rel_trans _ _ HM _ _ _ Hs2 (nparams_rel_sym _ _ HM _ _ Hs2'))) Hn')
          | exact Hc | exact Hb1 | exact Hb3 | exact Hs1 | exact Hs3
          | exact (args_rel_trans _ _ HM _ _ _ (nparams_rel_refl_l _ _ HM _ _ H12) Hc _ _ _ Ha
                     (args_rel_inst _ _ HM _ _ _ _ _ _ (nparams_rel_sym _ _ HM _ _ H12) Hc Ha')) |].
        apply (IH _ _ _ Mk (List.skipn (im_unu D Mk) bs1) (List.skipn (im_unu D Mk) bs2) c gs nil nil nil HM);
          cbn; rewrite ?List.app_nil_r; try reflexivity; assumption.
      - intros k Mk hd k' ns1 ns2 as1 as2 m1 m2 u1 u2 HM Hr Hn L1 L2 O1 O2 H1 H2 Hm u3 ns3 ns4 z Hz.
        inversion Hz as [| k0 Mk0 hd0 k0' ns3' ns4' as2' as3 m2' m3 u2' u3' HM' Hr' Hn' L2' L3 O2' O3 H2' H3 Hm']; subst.
        rewrite HM in HM'; injection HM' as <-.
        econstructor; try eassumption.
        + exact (nparams_rel_trans _ _ HM _ _ _ (nparams_rel_trans _ _ HM _ _ _ Hn
                   (nparams_rel_trans _ _ HM _ _ _ H2 (nparams_rel_sym _ _ HM _ _ H2'))) Hn').
        + intros s0; destruct (Hm s0) as (L & HL & HL'); destruct (Hm' s0) as (L' & HL0 & HL'').
          pose proof (functional_read_ne _ _ _ _ HL' HL0) as <-; eauto.
      - intros * _ _ _ _ _ _ _ _ _ Hz; inversion Hz; subst; constructor.
      - intros k u1 u2 pre1 v1 pre2 v2 gs vs1 vs2 A Hia IH u3 pre3 vs3 Mk ms1 ms2 c gsf gs1 vp1 vp2 HM Hρ1 Hρ2 Hl1 Hl2 Hn Hc Heq Ha Hz.
        inversion Hz; subst.
        constructor.
        eapply (IH _ _ _ Mk ms1 ms2 c (gs1 ++ ca_arg A :: gs) (gs1 ++ ca_arg A :: nil) (vp1 ++ v1 :: nil) (vp2 ++ v2 :: nil) HM);
          [ rewrite nonrec_arg_vals_snoc_arg, List.app_assoc by assumption; reflexivity
          | rewrite nonrec_arg_vals_snoc_arg, List.app_assoc by assumption; reflexivity
          | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
          | rewrite <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Ha | eassumption ].
      - intros k u1 u2 pre1 pre2 t v1 v2 gs vs1 vs2 Hsh IHs Hia IH u3 pre3 vs3 Mk ms1 ms2 c gsf gs1 vp1 vp2 HM Hρ1 Hρ2 Hl1 Hl2 Hn Hc Heq Ha Hz.
        subst pre1 pre2 gsf.
        inversion Hz; subst.
        pose proof (nonrec_prefix _ _ _ _ _ _ _ _ _ _ _ HM (nparams_rel_refl_l _ _ HM _ _ Hn) Hc eq_refl Hl1 Hl2 Ha) as Hpre.
        constructor.
        + eapply (IHs _ _ _ Mk ms1 ms2 c gs1 t gs (nonrec_arg_vals gs1 vp1) (nonrec_arg_vals gs1 vp2) 0 nil nil HM);
            [ rewrite List.app_nil_r; reflexivity | rewrite List.app_nil_r; reflexivity | exact Hn | exact Hc
            | exact Hpre | reflexivity | lia | apply tele_prefix_rel_nil | eassumption ].
        + eapply (IH _ _ _ Mk ms1 ms2 c (gs1 ++ ca_rec t :: gs) (gs1 ++ ca_rec t :: nil) (vp1 ++ v1 :: nil) (vp2 ++ v2 :: nil) HM);
            [ rewrite nonrec_arg_vals_snoc_rec by assumption; reflexivity
            | rewrite nonrec_arg_vals_snoc_rec by assumption; reflexivity
            | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
            | rewrite <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Ha | eassumption ].
      - (** The recursive argument: no evaluation fact is used. *)
        intros Ps u1 pre1 bs1 u2 pre2 bs2 j v1 v2 k E1 E2 O1 O2 Hr IHr u3 pre3 v3; intros.
        match goal with Hz : rec_arg_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => inversion Hz; subst end.
        econstructor; [ exact E1 | eassumption | exact O1 | eassumption | eapply IHr; eassumption ].
      - intros k pre1 B u1 u2 pre2 t f1 f2 Hf IH u3 pre3 f3 Mk ms1 ms2 c gs1 t0 gs2 ws1 ws2 k0 ys1 ys2 HM Hρ1 Hρ2 Hn Hc Hw Hs Hk Hy Hz.
        subst pre1 pre2; inversion Hz; subst.
        match goal with Hz0 : forall c c', doms_rel _ _ _ c c' -> _ |- _ => rename Hz0 into Hz' end.
        pose proof (nparams_rel_refl_l _ _ HM _ _ Hn) as Hnn.
        destruct (shape_pi_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hnn Hc Hw Hs Hy) as (HB & Hs' & Hk' & HP & Hstep).
        constructor; intros a a3 Haa.
        assert (H33 : doms_rel k (ms1 ++ ws1 ++ ys1) B a3 a3) by (etransitivity; [ symmetry; exact Haa | exact Haa ]).
        pose proof (proj1 (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hn Hc eq_refl Hw HB Hy _ _) H33) as H33'.
        specialize (Hz' _ _ H33').
        eapply (IH a a3 Haa _ _ _ _ Mk ms1 ms2 c gs1 t0 gs2 ws1 ws2 (S k0) (ys1 ++ a :: nil) (ys2 ++ a3 :: nil) HM);
          [ rewrite <- !List.app_assoc; reflexivity | rewrite <- !List.app_assoc; reflexivity
          | exact Hn | exact Hc | exact Hw | exact Hs' | exact Hk' | apply Hstep; exact Haa | exact Hz' ].
      - intros f1 a1 r1 f2 a2 r2 k u1 u2 pre1 pre2 t E1 E2 Hsh IH u3 pre3 f3 a3 Mk ms1 ms2 c gs1 t0 gs2 ws1 ws2 kk ys1 ys2
          HM Hρ1 Hρ2 Hn Hc Hw Hs Hk Hy Hz.
        inversion Hz; subst.
        match goal with
        | E : eval_app _ _ f2 a2 ?R, E' : eval_app _ _ f2 a2 ?R' |- _ =>
            assert_fails (unify R R'); pose proof (functional_eval_app _ _ _ _ E E') as <-
        end.
        econstructor; [ exact E1 | eassumption |].
        eapply IH; [ exact HM | reflexivity | reflexivity | exact Hn | exact Hc | exact Hw | reflexivity | exact Hk | exact Hy | eassumption ].
    Qed.

    (** Moving the indices: the top-level telescope facts only. *)
    Lemma ind_rel_idx : forall adm okr k Mk u u' ns ns' x y ns1 ns1', ind_member D k = Some Mk ->
        ind_rel p D adm okr nparams_rel args_rel doms_rel k u u' ns ns' x y ->
        tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ns ns1 -> tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ns' ns1' ->
        ind_rel p D adm okr nparams_rel args_rel doms_rel k u u' ns1 ns1' x y.
    Proof.
      intros * HM H H1 H1'.
      destruct H as [k0 Mk0 hd k' ns0 ns0' c gs bs bs' vs vs' u0 u0' HM0 Hr Hn Hc Hb Hb' Hs Hs' Ha Hia
                    | k0 Mk0 hd k' ns0 ns0' as1 as2 m m' u0 u0' HM0 Hr Hn L1 L2 O1 O2 Hs Hs' Hm];
        rewrite HM in HM0; injection HM0 as <-.
      - eapply ind_rel_con with (gs := gs); try eassumption;
          [ exact (nparams_rel_trans _ _ HM _ _ _ (nparams_rel_sym _ _ HM _ _ H1) (nparams_rel_trans _ _ HM _ _ _ Hn H1'))
          | exact (nparams_rel_trans _ _ HM _ _ _ (nparams_rel_sym _ _ HM _ _ H1) Hs)
          | exact (nparams_rel_trans _ _ HM _ _ _ (nparams_rel_sym _ _ HM _ _ H1') Hs') ].
      - eapply ind_rel_neut; try eassumption;
          [ exact (nparams_rel_trans _ _ HM _ _ _ (nparams_rel_sym _ _ HM _ _ H1) (nparams_rel_trans _ _ HM _ _ _ Hn H1'))
          | exact (nparams_rel_trans _ _ HM _ _ _ (nparams_rel_sym _ _ HM _ _ H1) Hs)
          | exact (nparams_rel_trans _ _ HM _ _ _ (nparams_rel_sym _ _ HM _ _ H1') Hs') ].
    Qed.

    (** The two indices of related elements are related. *)
    Lemma ind_rel_ns : forall adm okr k Mk u u' ns ns' x y, ind_member D k = Some Mk ->
        ind_rel p D adm okr nparams_rel args_rel doms_rel k u u' ns ns' x y ->
        tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ns ns'.
    Proof.
      intros * HM H; destruct H;
        match goal with H0 : ind_member D _ = Some _ |- _ => rewrite HM in H0; injection H0 as <- end; assumption.
    Qed.

    (** The admissibility the swapped type needs: of [ups] and of [ups']
        beside [ups']. *)
    Lemma adm_flip : forall ups', adm_uparams D ups nparams_rel args_rel doms_rel ups' -> adm_uparams D ups nparams_rel args_rel doms_rel ups -> adm_uparams D ups' nparams_rel args_rel doms_rel ups.
    Proof. intros * H' H; exact (adm_base _ _ H' H). Qed.

    Lemma adm_diag_r : forall ups', adm_uparams D ups nparams_rel args_rel doms_rel ups' -> adm_uparams D ups' nparams_rel args_rel doms_rel ups'.
    Proof. intros * H'; exact (adm_base _ _ H' H'). Qed.

    (** The bases admissible beside [ups] are those admissible beside a
        base admissible beside it. *)
    Lemma adm_iff : forall ups', adm_uparams D ups nparams_rel args_rel doms_rel ups' ->
        forall u, adm_uparams D ups nparams_rel args_rel doms_rel u <-> adm_uparams D ups' nparams_rel args_rel doms_rel u.
    Proof. intros * H' u; split; [ exact (adm_base _ _ H') | exact (adm_compose _ _ H') ]. Qed.

    (** *** Admissibility at the Fresh Variables, at Another Base

        A base [ups'] admissible beside [ups] at every prefix makes the
        fresh variables at [ups'] related to those at [ups], so a base
        admissible beside [ups] at the fresh variables is so beside
        [ups']. *)

    Section FreshBase.
      Variable (ups' : list domain).
      Hypothesis (Hcl : adm_uparams D ups nparams_rel args_rel doms_rel ups').

      (** The fresh variables of the non-uniform parameters at [ups] and at
          [ups'] are related. *)
      Lemma fresh_tele_pair : forall m Mm T0 T k pre pre0 s ws ws0, ind_member D m = Some Mm ->
          List.rev (im_nparams Mm) = T0 ++ T -> List.length T0 = k ->
          tele_prefix_rel (nparams_rel m) k pre pre0 ->
          Ftele T in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ⍮ s ↘ ws ->
          Ftele T in gc_deps ⍮ gc_stack ⍮ env_args nil (ups' ++ pre0) ⍮ s ↘ ws0 ->
          tele_prefix_rel (nparams_rel m) (k + List.length T) (pre ++ ws) (pre0 ++ ws0).
      Proof.
        intros m Mm T0 T; revert T0; induction T as [| e T IH]; intros T0 k pre pre0 s ws ws0 HM HT Hk Hp F F0; subst k.
        - inversion F; inversion F0; subst; rewrite !List.app_nil_r, Nat.add_0_r; exact Hp.
        - inversion F as [| A ρ0 a T' s0 vs Ea F' ]; subst; inversion F0 as [| A0 ρ1 a0 T'' s1 vs0 Ea0 F0' ]; subst.
          assert (HA : List.nth_error (List.rev (im_nparams Mm)) (List.length T0) = Some (ce_ass A))
            by (rewrite HT, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
          destruct (adm_nparam_vars _ _ _ _ _ _ Hcl m Mm (List.length T0) A pre pre0 s HM HA Hp) as [b b0 Eb Eb0 Rb].
          pose proof (functional_eval_exp _ _ _ _ Eb Ea) as ->; pose proof (functional_eval_exp _ _ _ _ Eb0 Ea0) as ->.
          rewrite <- env_args_snoc, <- List.app_assoc in F', F0'.
          pose proof (IH (T0 ++ ce_ass A :: nil) (S (List.length T0)) (pre ++ ⇑! a s :: nil) (pre0 ++ ⇑! a0 s :: nil) (S s) vs vs0 HM
                        ltac:(rewrite HT, <- List.app_assoc; reflexivity) ltac:(rewrite List.length_app; cbn; lia)
                        (tele_prefix_rel_snoc _ _ _ _ _ _ Hp Rb) F' F0') as H.
          rewrite <- !List.app_assoc in H; cbn in H.
          cbn [List.length]; rewrite <- plus_n_Sm; exact H.
      Qed.

      (** A telescope's fresh variables at [ups] related to those at [u]:
          so are those at [ups']. *)
      Lemma fresh_tele_rel_base : forall m Mm u T0 T k pre pre' s pre0, ind_member D m = Some Mm ->
          List.rev (im_nparams Mm) = T0 ++ T -> List.length T0 = k ->
          fresh_tele_rel (nparams_rel m) ups u k pre pre' s T ->
          tele_prefix_rel (nparams_rel m) k pre pre0 ->
          fresh_tele_rel (nparams_rel m) ups' u k pre0 pre' s T.
      Proof.
        intros m Mm u T0 T k pre pre' s pre0 HM HT Hk H; revert T0 pre0 HT Hk.
        induction H as [k pre pre' s | k pre pre' s A T a a' Ea Ea' Hr H IH]; intros T0 pre0 HT Hk Hp; [ constructor |].
        assert (HA : List.nth_error (List.rev (im_nparams Mm)) k = Some (ce_ass A))
          by (rewrite HT, List.nth_error_app2, <- Hk, Nat.sub_diag by lia; reflexivity).
        destruct (adm_nparam_vars _ _ _ _ _ _ Hcl m Mm k A pre pre0 s HM HA Hp) as [b b0 Eb Eb0 Rb].
        pose proof (functional_eval_exp _ _ _ _ Eb Ea) as ->.
        pose proof (HnP m Mm k A pre pre0 HM HA Hp) as HPer.
        assert (Rb' : nparams_rel m k pre (⇑! b0 s) (⇑! a' s)) by (etransitivity; [ symmetry; exact Rb | exact Hr ]).
        apply (HnI m Mm k A pre pre0 HM HA Hp) in Rb'.
        econstructor; [ exact Eb0 | exact Ea' | exact Rb' |].
        apply (IH (T0 ++ ce_ass A :: nil)); [ rewrite HT, <- List.app_assoc; reflexivity | rewrite List.length_app, Hk; cbn; lia |].
        apply tele_prefix_rel_snoc; [ exact Hp | exact Rb ].
      Qed.

      (** The fresh arguments of a constructor, likewise. *)
      Lemma fresh_cargs_rel_base : forall m Mm c gsf gs1 gs u ns ns0 ns' k ws ws' ws0 s, ind_member D m = Some Mm ->
          ind_con Mm c = Some gsf -> gsf = gs1 ++ gs -> List.length (cargs_nonrec gs1) = k ->
          tele_rel (nparams_rel m) (List.rev (im_nparams Mm)) ns ns0 ->
          fresh_cargs_rel D ups u nparams_rel (args_rel m ns c) (doms_rel m) ns ns' k ws ws' s gs ->
          tele_prefix_rel (args_rel m ns c) k ws ws0 ->
          fresh_cargs_rel D ups' u nparams_rel (args_rel m ns0 c) (doms_rel m) ns0 ns' k ws0 ws' s gs.
      Proof.
        intros m Mm c gsf gs1 gs u ns ns0 ns' k ws ws' ws0 s HM Hc Heq Hk Hn H; revert gs1 ws0 Heq Hk.
        pose proof (nparams_rel_refl_l _ _ HM _ _ Hn) as Hnn.
        pose proof (nparams_rel_sym _ _ HM _ _ Hn) as Hn'.
        pose proof (nparams_rel_refl_r _ _ HM _ _ Hn) as Hn00.
        induction H as [k ws ws' s | k ws ws' s A gs a a' Ea Ea' Hr H IH | k ws ws' s t gs Hix Hdo H IH];
          intros gs1 ws0 Heq Hk Hp; [ constructor | |].
        - assert (HA : List.nth_error (cargs_nonrec gsf) k = Some A)
            by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Hk, Nat.sub_diag by lia; reflexivity).
          assert (Hkl : k < List.length (cargs_nonrec gsf)) by (apply List.nth_error_Some; congruence).
          destruct (adm_arg_vars _ _ _ _ _ _ Hcl m Mm ns ns0 c gsf k A ws ws0 s HM Hn Hc HA Hp) as [b b0 Eb Eb0 Rb].
          pose proof (functional_eval_exp _ _ _ _ Eb Ea) as ->.
          pose proof (HaP _ _ _ _ _ _ _ _ _ _ HM Hn Hc HA Hp) as HPer.
          assert (Rb' : args_rel m ns c k ws (⇑! b0 s) (⇑! a' s)) by (etransitivity; [ symmetry; exact Rb | exact Hr ]).
          apply (HaI _ _ _ _ _ _ _ _ _ _ HM Hn Hc HA Hp) in Rb'.
          econstructor; [ exact Eb0 | exact Ea' | exact Rb' |].
          apply (IH (gs1 ++ ca_arg A :: nil)); [ rewrite Heq, <- List.app_assoc; reflexivity
                                              | rewrite cargs_nonrec_app, List.length_app, Hk; cbn; lia |].
          apply tele_prefix_rel_snoc; [ exact Hp | exact Rb ].
        - assert (Hk1 : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gsf))
            by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
          subst k.
          assert (Hc' : ind_con Mm c = Some (gs1 ++ ca_rec t :: gs)) by (rewrite <- Heq; exact Hc).
          pose proof (args_rel_pre_refl_l _ _ HM ns c gsf Hnn Hc _ _ _ Hk1 Hp) as Hww.
          assert (Hp0 : tele_prefix_rel (args_rel m ns0 c) (List.length (cargs_nonrec gs1)) ws0 ws).
          { eapply (args_prefix_rel_inst _ _ HM); [ exact Hn | exact Hc | exact Hk1 |].
            eapply (args_prefix_rel_sym _ _ HM); [ exact Hnn | exact Hc | exact Hk1 | exact Hp ]. }
          pose proof (args_rel_pre_refl_l _ _ HM ns0 c gsf Hn00 Hc _ _ _ Hk1 Hp0) as Hw00.
          econstructor.
          + (** The parameters at the end: through those at [ups]. *)
            intros ys ys' Hy.
            assert (Hy1 : tele_rel (shape_doms_rel (doms_rel m) ns ws (ptyp_doms t)) (ptyp_doms t) ys ys').
            { apply tele_rel_of_pre; eapply (doms_rel_inst _ _ HM); [ exact Hn' | exact Hc' | reflexivity | exact Hp0 | lia |].
              apply tele_rel_pre; exact Hy. }
            assert (Hyy : tele_rel (shape_doms_rel (doms_rel m) ns ws (ptyp_doms t)) (ptyp_doms t) ys ys).
            { apply tele_rel_of_pre; eapply (doms_rel_refl_l _ _ HM ns c _ gs1 t gs ws Hnn Hc' eq_refl Hww); [ lia |].
              apply tele_rel_pre; exact Hy1. }
            destruct (Hix _ _ Hy1) as [b b' F F' R].
            destruct (adm_rec_params _ _ _ _ _ _ Hcl m Mm ns ns0 c _ gs1 t gs ws ws0 ys ys HM Hn Hc' eq_refl Hp Hyy)
              as [b1 b0 F1 F0 R0].
            pose proof (functional_eval_exps' _ _ _ _ F F1) as <-.
            exists b0 b'; [ exact F0 | exact F' | exact (ntele_rel_trans _ _ _ _ (ntele_rel_sym _ _ _ R0) R) ].
          + (** Each domain: through the one at [ups]. *)
            intros j B ys ys' HB Hy.
            pose proof (nth_error_lt' _ _ _ HB) as Hjl.
            assert (Hy1 : tele_prefix_rel (shape_doms_rel (doms_rel m) ns ws (ptyp_doms t)) j ys ys')
              by (eapply (doms_rel_inst _ _ HM); [ exact Hn' | exact Hc' | reflexivity | exact Hp0 | lia | exact Hy ]).
            pose proof (doms_rel_refl_l _ _ HM ns c _ gs1 t gs ws Hnn Hc' eq_refl Hww j ys ys' ltac:(lia) Hy1) as Hyy.
            destruct (Hdo _ _ _ _ HB Hy1) as [b b' F F' T1].
            destruct (adm_shape_doms _ _ _ _ _ _ Hcl m Mm ns ns0 c _ gs1 t gs ws ws0 j B ys ys HM Hn Hc' eq_refl Hp HB Hyy)
              as [b1 b0 F1 F0 T0].
            pose proof (functional_eval_exp _ _ _ _ F1 F) as ->.
            pose proof (doms_rel_refl_l _ _ HM ns0 c _ gs1 t gs ws0 Hn00 Hc' eq_refl Hw00 j ys ys' ltac:(lia) Hy) as Hy00.
            pose proof (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hn' Hc' eq_refl Hp0 HB Hy00) as HdIe.
            pose proof (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hnn Hc' eq_refl Hww HB Hyy) as HPd.
            exists b0 b'; [ exact F0 | exact F' |].
            intros x x' Hx.
            apply (proj1 (HdIe _ _)) in Hx.
            assert (Hxx : doms_rel m (ns ++ ws ++ ys) B x x) by (etransitivity; [ exact Hx | symmetry; exact Hx ]).
            exact (per_top_trans' _ _ _ (per_top_sym' _ _ (T0 _ _ Hxx)) (T1 _ _ Hx)).
          + apply (IH (gs1 ++ ca_rec t :: nil)); [ rewrite Heq, <- List.app_assoc; reflexivity
                                                | rewrite cargs_nonrec_app, List.length_app; cbn; lia | exact Hp ].
      Qed.

      (** Admissibility at every related prefix gives it at the fresh
          variables: those of the non-uniform parameters, and after them
          those of each constructor's arguments, are related prefixes. *)
      Lemma fresh_tele_rel_of_adm : forall m Mm T0 T k pre pre0 s, ind_member D m = Some Mm ->
          List.rev (im_nparams Mm) = T0 ++ T -> List.length T0 = k ->
          tele_prefix_rel (nparams_rel m) k pre pre0 ->
          fresh_tele_rel (nparams_rel m) ups ups' k pre pre0 s T.
      Proof.
        intros m Mm T0 T; revert T0; induction T as [| e T IH]; intros T0 k pre pre0 s HM HT Hk Hp; [ constructor |].
        assert (Hkl : k < List.length (List.rev (im_nparams Mm))) by (rewrite HT, List.length_app; cbn; lia).
        destruct (nparams_lt_ass D m Mm k Hass HM Hkl) as [A HA].
        rewrite HT, List.nth_error_app2, <- Hk, Nat.sub_diag in HA by lia; cbn in HA; injection HA as ->.
        subst k.
        assert (HA' : List.nth_error (List.rev (im_nparams Mm)) (List.length T0) = Some (ce_ass A))
          by (rewrite HT, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
        destruct (adm_nparam_vars _ _ _ _ _ _ Hcl m Mm (List.length T0) A pre pre0 s HM HA' Hp) as [a a0 Ea Ea0 Ra].
        econstructor; [ exact Ea | exact Ea0 | exact Ra |].
        apply (IH (T0 ++ ce_ass A :: nil)); [ exact HM | rewrite HT, <- List.app_assoc; reflexivity
                                            | rewrite List.length_app; cbn; lia |].
        apply tele_prefix_rel_snoc; [ exact Hp | exact Ra ].
      Qed.

      Lemma fresh_cargs_rel_of_adm : forall m Mm c gsf gs1 gs ns ns' k ws ws' s, ind_member D m = Some Mm ->
          ind_con Mm c = Some gsf -> gsf = gs1 ++ gs -> List.length (cargs_nonrec gs1) = k ->
          tele_rel (nparams_rel m) (List.rev (im_nparams Mm)) ns ns' ->
          tele_prefix_rel (args_rel m ns c) k ws ws' ->
          fresh_cargs_rel D ups ups' nparams_rel (args_rel m ns c) (doms_rel m) ns ns' k ws ws' s gs.
      Proof.
        intros m Mm c gsf gs1 gs; revert gs1; induction gs as [| [A | t] gs IH];
          intros gs1 ns ns' k ws ws' s HM Hc Heq Hk Hn Hp; [ constructor | |].
        - assert (HA : List.nth_error (cargs_nonrec gsf) k = Some A)
            by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Hk, Nat.sub_diag by lia; reflexivity).
          destruct (adm_arg_vars _ _ _ _ _ _ Hcl m Mm ns ns' c gsf k A ws ws' s HM Hn Hc HA Hp) as [a a' Ea Ea' Ra].
          econstructor; [ exact Ea | exact Ea' | exact Ra |].
          apply (IH (gs1 ++ ca_arg A :: nil)); [ exact HM | exact Hc | rewrite Heq, <- List.app_assoc; reflexivity
                                              | rewrite cargs_nonrec_app, List.length_app, Hk; cbn; lia | exact Hn |].
          apply tele_prefix_rel_snoc; [ exact Hp | exact Ra ].
        - subst k.
          assert (Hc' : ind_con Mm c = Some (gs1 ++ ca_rec t :: gs)) by (rewrite <- Heq; exact Hc).
          econstructor.
          + intros ys ys' Hy; exact (adm_rec_params _ _ _ _ _ _ Hcl m Mm ns ns' c _ gs1 t gs ws ws' ys ys' HM Hn Hc' eq_refl Hp Hy).
          + intros j B ys ys' HB Hy.
            exact (adm_shape_doms _ _ _ _ _ _ Hcl m Mm ns ns' c _ gs1 t gs ws ws' j B ys ys' HM Hn Hc' eq_refl Hp HB Hy).
          + apply (IH (gs1 ++ ca_rec t :: nil)); [ exact HM | exact Hc | rewrite Heq, <- List.app_assoc; reflexivity
                                                | rewrite cargs_nonrec_app, List.length_app; cbn; lia | exact Hn | exact Hp ].
      Qed.

        (** The fields of [adm_fresh] at another base. *)
        Lemma adm_fresh_fields_base : forall u,
            (forall m Mm s, ind_member D m = Some Mm ->
               fresh_tele_rel (nparams_rel m) ups u 0 nil nil s (List.rev (im_nparams Mm))) ->
            (forall m Mm c gs s ns ns', ind_member D m = Some Mm -> ind_con Mm c = Some gs ->
               Ftele List.rev (im_nparams Mm) in gc_deps ⍮ gc_stack ⍮ env_args nil ups ⍮ s ↘ ns ->
               Ftele List.rev (im_nparams Mm) in gc_deps ⍮ gc_stack ⍮ env_args nil u ⍮ s ↘ ns' ->
               fresh_cargs_rel D ups u nparams_rel (args_rel m ns c) (doms_rel m) ns ns' 0 nil nil (s + im_nn Mm) gs) ->
            (forall m Mm s, ind_member D m = Some Mm ->
               fresh_tele_rel (nparams_rel m) ups' u 0 nil nil s (List.rev (im_nparams Mm))) /\
            (forall m Mm c gs s ns ns', ind_member D m = Some Mm -> ind_con Mm c = Some gs ->
               Ftele List.rev (im_nparams Mm) in gc_deps ⍮ gc_stack ⍮ env_args nil ups' ⍮ s ↘ ns ->
               Ftele List.rev (im_nparams Mm) in gc_deps ⍮ gc_stack ⍮ env_args nil u ⍮ s ↘ ns' ->
               fresh_cargs_rel D ups' u nparams_rel (args_rel m ns c) (doms_rel m) ns ns' 0 nil nil (s + im_nn Mm) gs).
        Proof.
          intros u Hn Ha; split.
          - intros m Mm s HM.
            apply (fresh_tele_rel_base m Mm u nil _ 0 nil nil s nil HM eq_refl eq_refl (Hn m Mm s HM) (tele_prefix_rel_nil _)).
          - intros m Mm c gs s ns0 ns' HM Hc F0 F'.
            destruct (fresh_tele_rel_ftele _ _ _ _ _ _ _ _ (Hn m Mm s HM)) as (ns & ns'' & F & F'' & _ & _).
            rewrite List.app_nil_r in F, F''; pose proof (functional_fresh_tele' _ _ _ _ _ F'' F') as <-.
            pose proof (fresh_tele_pair m Mm nil _ 0 nil nil s ns ns0 HM eq_refl eq_refl (tele_prefix_rel_nil _)
                          ltac:(rewrite List.app_nil_r; exact F) ltac:(rewrite List.app_nil_r; exact F0)) as Hp.
            apply tele_rel_of_pre in Hp; cbn in Hp.
            eapply (fresh_cargs_rel_base m Mm c gs nil gs u ns ns0 ns'' 0 nil nil nil); try reflexivity; try eassumption.
            + exact (Ha m Mm c gs s ns ns'' HM Hc F F'').
            + apply tele_prefix_rel_nil.
        Qed.

        Lemma adm_fresh_base : forall u, adm_fresh p D ups nparams_rel args_rel doms_rel u ->
            adm_fresh p D ups' nparams_rel args_rel doms_rel u.
        Proof.
          intros u [Hn Ha]; destruct (adm_fresh_fields_base u Hn Ha) as [Hn' Ha']; constructor; [ exact Hn' | exact Ha' ].
        Qed.

        Lemma grp_adm_base : forall k Y, grp_adm p D ups nparams_rel args_rel doms_rel k Y ->
            grp_adm p D ups' nparams_rel args_rel doms_rel k Y.
        Proof.
          unfold grp_adm; intros k Y H; destruct (ind_has_views D); [ exact H |].
          destruct (ind_member D k) as [Mk |]; [| exact H ].
          destruct (im_head Mk); [ exact (adm_fresh_base _ H) | exact H ].
        Qed.

      Lemma adm_fresh_of_uparams : adm_fresh p D ups nparams_rel args_rel doms_rel ups'.
      Proof.
        constructor.
        - intros m Mm s HM; exact (fresh_tele_rel_of_adm m Mm nil _ 0 nil nil s HM eq_refl eq_refl (tele_prefix_rel_nil _)).
        - intros m Mm c gs s ns ns' HM Hc F F'.
          pose proof (fresh_tele_pair m Mm nil _ 0 nil nil s ns ns' HM eq_refl eq_refl (tele_prefix_rel_nil _)
                        ltac:(rewrite List.app_nil_r; exact F) ltac:(rewrite List.app_nil_r; exact F')) as Hp.
          apply tele_rel_of_pre in Hp; cbn in Hp.
          exact (fresh_cargs_rel_of_adm m Mm c gs nil gs ns ns' 0 nil nil (s + im_nn Mm) HM Hc eq_refl eq_refl Hp
                   (tele_prefix_rel_nil _)).
      Qed.

      (** A recursive index admissible beside [ups] at a prefix related to
          itself is admissible beside [ups']. *)
      Lemma okr_at_base : forall m Mm ms c gs1 t0 gs2 ws ys bs, ind_member D m = Some Mm ->
          tele_rel (nparams_rel m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some (gs1 ++ ca_rec t0 :: gs2) ->
          tele_prefix_rel (args_rel m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
          tele_rel (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t0)) (ptyp_doms t0) ys ys ->
          okr_at D ups nparams_rel (ptyp_mem t0) (ms ++ ws ++ ys) (ptyp_ps t0) bs ->
          okr_at D ups' nparams_rel (ptyp_mem t0) (ms ++ ws ++ ys) (ptyp_ps t0) bs.
      Proof.
        intros * HM Hm Hc Hw Hy [idx E R].
        destruct (adm_rec_params _ _ _ _ _ _ Hcl m Mm ms ms c _ gs1 t0 gs2 ws ws ys ys HM Hm Hc eq_refl Hw Hy) as [b b' F F' R0].
        pose proof (functional_eval_exps' _ _ _ _ E F) as <-.
        exists b'; [ exact F' | exact (ntele_rel_trans _ _ _ _ (ntele_rel_sym _ _ _ R0) R) ].
      Qed.

      Lemma ind_rel_okr_base : forall adm,
          (forall k u u' ns ns' x y, ind_rel p D adm (okr_at D ups nparams_rel) nparams_rel args_rel doms_rel k u u' ns ns' x y ->
             ind_rel p D adm (okr_at D ups' nparams_rel) nparams_rel args_rel doms_rel k u u' ns ns' x y) /\
          (forall k u u' pre pre' gs vs vs',
             con_args_rel p D adm (okr_at D ups nparams_rel) nparams_rel args_rel doms_rel k u u' pre pre' gs vs vs' ->
             forall Mk ms ms' c gsf gs1 vp vp', ind_member D k = Some Mk ->
               pre = ms ++ nonrec_arg_vals gs1 vp -> pre' = ms' ++ nonrec_arg_vals gs1 vp' ->
               List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
               tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ms ms' -> ind_con Mk c = Some gsf -> gsf = gs1 ++ gs ->
               tele_rel (args_rel k ms c) (cargs_nonrec gsf) (nonrec_arg_vals gsf (vp ++ vs)) (nonrec_arg_vals gsf (vp' ++ vs')) ->
               con_args_rel p D adm (okr_at D ups' nparams_rel) nparams_rel args_rel doms_rel k u u' pre pre' gs vs vs') /\
          (forall k u u' pre pre' t v v',
             rec_arg_rel p D adm (okr_at D ups nparams_rel) nparams_rel args_rel doms_rel k u u' pre pre' t v v' ->
             forall Mk ms ms' c gs1 t0 gs2 ws ws' kk ys ys', ind_member D k = Some Mk ->
               pre = ms ++ ws ++ ys -> pre' = ms' ++ ws' ++ ys' ->
               tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ms ms' -> ind_con Mk c = Some (gs1 ++ ca_rec t0 :: gs2) ->
               tele_prefix_rel (args_rel k ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
               ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
               tele_prefix_rel (shape_doms_rel (doms_rel k) ms ws (ptyp_doms t0)) kk ys ys' ->
               rec_arg_rel p D adm (okr_at D ups' nparams_rel) nparams_rel args_rel doms_rel k u u' pre pre' t v v') /\
          (forall k u u' pre pre' t f a f' a',
             rec_arg_app_rel p D adm (okr_at D ups nparams_rel) nparams_rel args_rel doms_rel k u u' pre pre' t f a f' a' ->
             forall Mk ms ms' c gs1 t0 gs2 ws ws' kk ys ys', ind_member D k = Some Mk ->
               pre = ms ++ ws ++ ys -> pre' = ms' ++ ws' ++ ys' ->
               tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ms ms' -> ind_con Mk c = Some (gs1 ++ ca_rec t0 :: gs2) ->
               tele_prefix_rel (args_rel k ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
               ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
               tele_prefix_rel (shape_doms_rel (doms_rel k) ms ws (ptyp_doms t0)) kk ys ys' ->
               rec_arg_app_rel p D adm (okr_at D ups' nparams_rel) nparams_rel args_rel doms_rel k u u' pre pre' t f a f' a').
      Proof.
        intros adm; apply ind_rel_mut_ind_all.
        - intros * HM Hr Hn Hc Hb Hb' Hs Hs' Ha Hia IH.
          assert (Hm : tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) (List.skipn (im_unu D Mk) bs) (List.skipn (im_unu D Mk) bs'))
            by exact (nparams_rel_trans _ _ HM _ _ _ (nparams_rel_trans _ _ HM _ _ _ (nparams_rel_sym _ _ HM _ _ Hs) Hn) Hs').
          econstructor; try eassumption.
          apply (IH Mk (List.skipn (im_unu D Mk) bs) (List.skipn (im_unu D Mk) bs') c gs nil nil nil HM);
            cbn; rewrite ?List.app_nil_r; try reflexivity; assumption.
        - intros; econstructor; eassumption.
        - intros; constructor.
        - intros * Hia IH Mk ms ms' c gsf gs1 vp vp' HM Hρ Hρ' Hl Hl' Hn Hc Heq Ha.
          constructor.
          apply (IH Mk ms ms' c gsf (gs1 ++ ca_arg A :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil) HM);
            [ rewrite Hρ, nonrec_arg_vals_snoc_arg, List.app_assoc by assumption; reflexivity
            | rewrite Hρ', nonrec_arg_vals_snoc_arg, List.app_assoc by assumption; reflexivity
            | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
            | rewrite Heq, <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Ha ].
        - intros * Hsh IHs Hia IH Mk ms ms' c gsf gs1 vp vp' HM Hρ Hρ' Hl Hl' Hn Hc Heq Ha.
          pose proof (nonrec_prefix _ _ _ _ _ _ _ _ _ _ _ HM (nparams_rel_refl_l _ _ HM _ _ Hn) Hc Heq Hl Hl' Ha) as Hpre.
          constructor.
          + apply (IHs Mk ms ms' c gs1 t gs (nonrec_arg_vals gs1 vp) (nonrec_arg_vals gs1 vp') 0 nil nil HM);
              [ rewrite List.app_nil_r; exact Hρ | rewrite List.app_nil_r; exact Hρ' | exact Hn | rewrite <- Heq; exact Hc
              | exact Hpre | reflexivity | lia | apply tele_prefix_rel_nil ].
          + apply (IH Mk ms ms' c gsf (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil) HM);
              [ rewrite Hρ, nonrec_arg_vals_snoc_rec by assumption; reflexivity
              | rewrite Hρ', nonrec_arg_vals_snoc_rec by assumption; reflexivity
              | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
              | rewrite Heq, <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Ha ].
        - (** The end of a shape: each side's index at its own prefix. *)
          intros * E E' O O' Hr IHr Mk ms ms' c gs1 t0 gs2 ws ws' kk ys ys' HM Hρ Hρ' Hn Hc Hw Hs Hk Hy.
          destruct (ptyp_skip_self _ _ _ _ Hs) as (Hkd & Hj & HPs).
          assert (Hyf : tele_rel (shape_doms_rel (doms_rel k) ms ws (ptyp_doms t0)) (ptyp_doms t0) ys ys')
            by (destruct Hy as [Hyl Hya]; split; [ lia | exact Hya ]).
          pose proof (nparams_rel_refl_l _ _ HM _ _ Hn) as Hnn.
          pose proof (nparams_rel_refl_r _ _ HM _ _ Hn) as Hnn'.
          assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
            by (rewrite cargs_nonrec_app, List.length_app; lia).
          pose proof (args_rel_pre_refl_l _ _ HM _ _ _ Hnn Hc _ _ _ HK Hw) as Hww.
          pose proof (args_prefix_rel_refl_r _ _ HM _ _ _ _ _ _ _ Hn Hc HK Hw) as Hww'.
          assert (Hyy : tele_rel (shape_doms_rel (doms_rel k) ms ws (ptyp_doms t0)) (ptyp_doms t0) ys ys)
            by (apply tele_rel_of_pre; eapply (doms_rel_refl_l _ _ HM ms c _ gs1 t0 gs2 ws Hnn Hc eq_refl Hww);
                [ lia | apply tele_rel_pre; exact Hyf ]).
          assert (Hyy' : tele_rel (shape_doms_rel (doms_rel k) ms' ws' (ptyp_doms t0)) (ptyp_doms t0) ys' ys')
            by (apply tele_rel_of_pre; eapply (doms_rel_refl_inst _ _ HM);
                [ exact Hn | exact Hc | reflexivity | exact Hw | lia | apply tele_rel_pre; exact Hyf ]).
          subst pre pre' j Ps.
          econstructor; [ exact E | exact E' | | | exact IHr ].
          + exact (okr_at_base _ _ _ _ _ _ _ _ _ _ HM Hnn Hc Hww Hyy O).
          + exact (okr_at_base _ _ _ _ _ _ _ _ _ _ HM Hnn' Hc Hww' Hyy' O').
        - intros * Hf IH Mk ms ms' c gs1 t0 gs2 ws ws' k0 ys ys' HM Hρ Hρ' Hn Hc Hw Hs Hk Hy.
          pose proof (nparams_rel_refl_l _ _ HM _ _ Hn) as Hnn.
          destruct (shape_pi_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hnn Hc Hw Hs Hy) as (HB & Hs' & Hk' & HP & Hstep).
          subst pre pre'.
          constructor; intros a a' Haa.
          apply (IH a a' Haa Mk ms ms' c gs1 t0 gs2 ws ws' (S k0) (ys ++ a :: nil) (ys' ++ a' :: nil) HM);
            [ rewrite <- !List.app_assoc; reflexivity | rewrite <- !List.app_assoc; reflexivity
            | exact Hn | exact Hc | exact Hw | exact Hs' | exact Hk' |].
          apply Hstep; exact Haa.
        - intros * Ef Ef' Hsh IH; intros.
          econstructor; [ exact Ef | exact Ef' | eapply IH; eassumption ].
      Qed.

      (** The right type's base moved to [ups']: the right side's shapes
          are read at [ups'] instead of at [u1], both admissible beside
          [ups]; the right indices move by [ind_rel_idx]. *)
      Lemma ind_rel_base_r : forall adm u1, adm_uparams D ups nparams_rel args_rel doms_rel u1 ->
          (forall k u u' ns ns' x y, ind_rel p D adm (okr_at D ups nparams_rel) nparams_rel args_rel doms_rel k u u' ns ns' x y ->
             u' = u1 -> ind_rel p D adm (okr_at D ups nparams_rel) nparams_rel args_rel doms_rel k u ups' ns ns' x y) /\
          (forall k u u' pre pre' gs vs vs',
             con_args_rel p D adm (okr_at D ups nparams_rel) nparams_rel args_rel doms_rel k u u' pre pre' gs vs vs' ->
             forall Mk ms ms' c gsf gs1 vp vp', u' = u1 -> ind_member D k = Some Mk ->
               pre = ms ++ nonrec_arg_vals gs1 vp -> pre' = ms' ++ nonrec_arg_vals gs1 vp' ->
               List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
               tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ms ms' -> ind_con Mk c = Some gsf -> gsf = gs1 ++ gs ->
               tele_rel (args_rel k ms c) (cargs_nonrec gsf) (nonrec_arg_vals gsf (vp ++ vs)) (nonrec_arg_vals gsf (vp' ++ vs')) ->
               con_args_rel p D adm (okr_at D ups nparams_rel) nparams_rel args_rel doms_rel k u ups' pre pre' gs vs vs') /\
          (forall k u u' pre pre' t v v',
             rec_arg_rel p D adm (okr_at D ups nparams_rel) nparams_rel args_rel doms_rel k u u' pre pre' t v v' ->
             forall Mk ms ms' c gs1 t0 gs2 ws ws' kk ys ys', u' = u1 -> ind_member D k = Some Mk ->
               pre = ms ++ ws ++ ys -> pre' = ms' ++ ws' ++ ys' ->
               tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ms ms' -> ind_con Mk c = Some (gs1 ++ ca_rec t0 :: gs2) ->
               tele_prefix_rel (args_rel k ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
               ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
               tele_prefix_rel (shape_doms_rel (doms_rel k) ms ws (ptyp_doms t0)) kk ys ys' ->
               rec_arg_rel p D adm (okr_at D ups nparams_rel) nparams_rel args_rel doms_rel k u ups' pre pre' t v v') /\
          (forall k u u' pre pre' t f a f' a',
             rec_arg_app_rel p D adm (okr_at D ups nparams_rel) nparams_rel args_rel doms_rel k u u' pre pre' t f a f' a' ->
             forall Mk ms ms' c gs1 t0 gs2 ws ws' kk ys ys', u' = u1 -> ind_member D k = Some Mk ->
               pre = ms ++ ws ++ ys -> pre' = ms' ++ ws' ++ ys' ->
               tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ms ms' -> ind_con Mk c = Some (gs1 ++ ca_rec t0 :: gs2) ->
               tele_prefix_rel (args_rel k ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
               ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
               tele_prefix_rel (shape_doms_rel (doms_rel k) ms ws (ptyp_doms t0)) kk ys ys' ->
               rec_arg_app_rel p D adm (okr_at D ups nparams_rel) nparams_rel args_rel doms_rel k u ups' pre pre' t f a f' a').
      Proof.
        intros adm u1 Hu1; apply ind_rel_mut_ind_all.
        - intros * HM Hr Hn Hc Hb Hb' Hs Hs' Ha Hia IH Hu.
          assert (Hm : tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) (List.skipn (im_unu D Mk) bs) (List.skipn (im_unu D Mk) bs'))
            by exact (nparams_rel_trans _ _ HM _ _ _ (nparams_rel_trans _ _ HM _ _ _ (nparams_rel_sym _ _ HM _ _ Hs) Hn) Hs').
          econstructor; try eassumption.
          apply (IH Mk (List.skipn (im_unu D Mk) bs) (List.skipn (im_unu D Mk) bs') c gs nil nil nil Hu HM);
            cbn; rewrite ?List.app_nil_r; try reflexivity; assumption.
        - intros; econstructor; eassumption.
        - intros; constructor.
        - intros * Hia IH Mk ms ms' c gsf gs1 vp vp' Hu HM Hρ Hρ' Hl Hl' Hn Hc Heq Ha.
          constructor.
          apply (IH Mk ms ms' c gsf (gs1 ++ ca_arg A :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil) Hu HM);
            [ rewrite Hρ, nonrec_arg_vals_snoc_arg, List.app_assoc by assumption; reflexivity
            | rewrite Hρ', nonrec_arg_vals_snoc_arg, List.app_assoc by assumption; reflexivity
            | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
            | rewrite Heq, <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Ha ].
        - intros * Hsh IHs Hia IH Mk ms ms' c gsf gs1 vp vp' Hu HM Hρ Hρ' Hl Hl' Hn Hc Heq Ha.
          pose proof (nonrec_prefix _ _ _ _ _ _ _ _ _ _ _ HM (nparams_rel_refl_l _ _ HM _ _ Hn) Hc Heq Hl Hl' Ha) as Hpre.
          constructor.
          + apply (IHs Mk ms ms' c gs1 t gs (nonrec_arg_vals gs1 vp) (nonrec_arg_vals gs1 vp') 0 nil nil Hu HM);
              [ rewrite List.app_nil_r; exact Hρ | rewrite List.app_nil_r; exact Hρ' | exact Hn | rewrite <- Heq; exact Hc
              | exact Hpre | reflexivity | lia | apply tele_prefix_rel_nil ].
          + apply (IH Mk ms ms' c gsf (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil) Hu HM);
              [ rewrite Hρ, nonrec_arg_vals_snoc_rec by assumption; reflexivity
              | rewrite Hρ', nonrec_arg_vals_snoc_rec by assumption; reflexivity
              | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
              | rewrite Heq, <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Ha ].
        - (** The end of a shape: the right index at [ups'], related to the
              one at [u1] through the one at [ups]. *)
          intros * E E' O O' Hr IHr Mk ms ms' c gs1 t0 gs2 ws ws' kk ys ys' Hu HM Hρ Hρ' Hn Hc Hw Hs Hk Hy.
          subst u'.
          destruct (ptyp_skip_self _ _ _ _ Hs) as (Hkd & Hj & HPs).
          assert (Hyf : tele_rel (shape_doms_rel (doms_rel k) ms ws (ptyp_doms t0)) (ptyp_doms t0) ys ys')
            by (destruct Hy as [Hyl Hya]; split; [ lia | exact Hya ]).
          subst pre pre' j Ps.
          destruct (adm_rec_params _ _ _ _ _ _ Hu1 k Mk ms ms' c _ gs1 t0 gs2 ws ws' ys ys' HM Hn Hc eq_refl Hw Hyf)
            as [b0 b1 F0 F1 R1].
          destruct (adm_rec_params _ _ _ _ _ _ Hcl k Mk ms ms' c _ gs1 t0 gs2 ws ws' ys ys' HM Hn Hc eq_refl Hw Hyf)
            as [b0' b2 F0' F2 R2].
          pose proof (functional_eval_exps' _ _ _ _ F0 F0') as <-.
          pose proof (functional_eval_exps' _ _ _ _ F1 E') as ->.
          pose proof (ntele_rel_trans _ _ _ _ (ntele_rel_sym _ _ _ R1) R2) as R12.
          econstructor; [ exact E | exact F2 | exact O | |].
          + destruct O' as [idx Ei Ri]; exists idx; [ exact Ei | exact (ntele_rel_trans _ _ _ _ Ri R12) ].
          + destruct (ntele_rel_member _ _ _ R12) as (Mj & HMj & H12).
            pose proof (IHr eq_refl) as Hr'.
            destruct (ntele_rel_member _ _ _ (ntele_rel_refl_l _ _ _ R12)) as (Mj' & HMj' & _).
            eapply (ind_rel_idx _ _ _ _ _ _ _ _ _ _ _ _ HMj Hr'); [| exact H12 ].
            destruct O as [idx0 Ei0 Ri0].
            destruct (ntele_rel_member _ _ _ (ntele_rel_refl_r _ _ _ Ri0)) as (Mj0 & HMj0 & H00).
            rewrite HMj in HMj0; injection HMj0 as <-; exact H00.
        - intros * Hf IH Mk ms ms' c gs1 t0 gs2 ws ws' k0 ys ys' Hu HM Hρ Hρ' Hn Hc Hw Hs Hk Hy.
          pose proof (nparams_rel_refl_l _ _ HM _ _ Hn) as Hnn.
          destruct (shape_pi_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hnn Hc Hw Hs Hy) as (HB & Hs' & Hk' & HP & Hstep).
          subst pre pre'.
          constructor; intros a a' Haa.
          apply (IH a a' Haa Mk ms ms' c gs1 t0 gs2 ws ws' (S k0) (ys ++ a :: nil) (ys' ++ a' :: nil) Hu HM);
            [ rewrite <- !List.app_assoc; reflexivity | rewrite <- !List.app_assoc; reflexivity
            | exact Hn | exact Hc | exact Hw | exact Hs' | exact Hk' |].
          apply Hstep; exact Haa.
        - intros * Ef Ef' Hsh IH; intros.
          econstructor; [ exact Ef | exact Ef' | eapply IH; eassumption ].
      Qed.
    End FreshBase.

    (** Both types' bases moved, all admissible beside [ups]: the right one
        by [ind_rel_base_r], the left one by it between two swaps. *)
    Lemma ind_rel_bases : forall adm k u1 u2 v1 v2 ns ns' x y,
        adm_uparams D ups nparams_rel args_rel doms_rel u1 -> adm_uparams D ups nparams_rel args_rel doms_rel u2 ->
        adm_uparams D ups nparams_rel args_rel doms_rel v1 -> adm_uparams D ups nparams_rel args_rel doms_rel v2 ->
        ind_rel p D adm (okr_at D ups nparams_rel) nparams_rel args_rel doms_rel k u1 u2 ns ns' x y ->
        ind_rel p D adm (okr_at D ups nparams_rel) nparams_rel args_rel doms_rel k v1 v2 ns ns' x y.
    Proof.
      intros * H1 H2 H3 H4 H.
      pose proof (proj1 (ind_rel_base_r v2 H4 adm u2 H2) _ _ _ _ _ _ _ H eq_refl) as Hr.
      pose proof (proj1 (ind_rel_sym_all adm _) _ _ _ _ _ _ _ Hr) as Hs.
      pose proof (proj1 (ind_rel_base_r v1 H3 adm u1 H1) _ _ _ _ _ _ _ Hs eq_refl) as Hr'.
      exact (proj1 (ind_rel_sym_all adm _) _ _ _ _ _ _ _ Hr').
    Qed.
  End IndPER.

  (** ** Changing the Relations

      The elements depend on the relations only where they are used: at
      the left parameters and arguments. *)
  Section FamChange.
    #[local] Set Default Proof Using "All".
    Variable (p : qname) (D : ind_decl) (ups : list domain).
    Variable (nparams_rel1 nparams_rel2 : nat -> nat -> list domain -> relation domain).
    Variable (args_rel1 args_rel2 : nat -> list domain -> String.string -> nat -> list domain -> relation domain).
    Variable (doms_rel1 doms_rel2 : nat -> list domain -> exp -> relation domain).
    Hypothesis (Hn : forall m Mm k vs vs1 vs2, ind_member D m = Some Mm -> k < List.length (List.rev (im_nparams Mm)) ->
                     tele_prefix_rel (nparams_rel1 m) k vs vs1 -> tele_prefix_rel (nparams_rel2 m) k vs vs2 ->
                     (nparams_rel1 m k vs <~> nparams_rel2 m k vs)).
    Hypothesis (Ha : forall m Mm ms ms1 ms2 c gs k vs vs1 vs2, ind_member D m = Some Mm ->
                     tele_rel (nparams_rel1 m) (List.rev (im_nparams Mm)) ms ms1 -> tele_rel (nparams_rel2 m) (List.rev (im_nparams Mm)) ms ms2 ->
                     ind_con Mm c = Some gs -> k < List.length (cargs_nonrec gs) ->
                     tele_prefix_rel (args_rel1 m ms c) k vs vs1 -> tele_prefix_rel (args_rel2 m ms c) k vs vs2 ->
                     (args_rel1 m ms c k vs <~> args_rel2 m ms c k vs)).
    Hypothesis (Hd : forall m Mm ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 k ys ys1 ys2, ind_member D m = Some Mm ->
                     tele_rel (nparams_rel1 m) (List.rev (im_nparams Mm)) ms ms1 -> tele_rel (nparams_rel2 m) (List.rev (im_nparams Mm)) ms ms2 ->
                     ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                     tele_prefix_rel (args_rel1 m ms c) (List.length (cargs_nonrec gs1)) ws ws1 ->
                     tele_prefix_rel (args_rel2 m ms c) (List.length (cargs_nonrec gs1)) ws ws2 ->
                     k < List.length (ptyp_doms t) ->
                     tele_prefix_rel (shape_doms_rel (doms_rel1 m) ms ws (ptyp_doms t)) k ys ys1 ->
                     tele_prefix_rel (shape_doms_rel (doms_rel2 m) ms ws (ptyp_doms t)) k ys ys2 ->
                     (shape_doms_rel (doms_rel1 m) ms ws (ptyp_doms t) k ys <~> shape_doms_rel (doms_rel2 m) ms ws (ptyp_doms t) k ys)).

    Section Member.
      Variable (m : nat) (Mm : imember).
      Hypothesis (HM : ind_member D m = Some Mm).
      Let T := List.rev (im_nparams Mm).

    Lemma tele_rel_nr_change : forall a b, tele_rel (nparams_rel1 m) T a b -> tele_rel (nparams_rel2 m) T a b.
    Proof. intros * H; apply (tele_rel_map T (nparams_rel1 m)); [| exact H ]; intros; eapply Hn; eassumption. Qed.

    Lemma tele_rel_nr_change' : forall a b, tele_rel (nparams_rel2 m) T a b -> tele_rel (nparams_rel1 m) T a b.
    Proof. intros * H; apply (tele_rel_map T (nparams_rel2 m)); [| exact H ]; intros; eapply Hn; eassumption. Qed.

    Lemma tele_prefix_rel_nr_change : forall k a b, k <= List.length T -> tele_prefix_rel (nparams_rel1 m) k a b ->
        tele_prefix_rel (nparams_rel2 m) k a b.
    Proof.
      intros * Hk H; rewrite tele_prefix_rel_full_iff in H |- *.
      apply (tele_rel_map _ (nparams_rel1 m)); [| exact H ].
      intros j pa pb x y Hj Hp1 Hp2 Hr; rewrite List.repeat_length in Hj.
      eapply Hn; [ exact HM | unfold T in *; lia | exact Hp1 | exact Hp2 | exact Hr ].
    Qed.

    Lemma tele_prefix_rel_nr_change' : forall k a b, k <= List.length T -> tele_prefix_rel (nparams_rel2 m) k a b ->
        tele_prefix_rel (nparams_rel1 m) k a b.
    Proof.
      intros * Hk H; rewrite tele_prefix_rel_full_iff in H |- *.
      apply (tele_rel_map _ (nparams_rel2 m)); [| exact H ].
      intros j pa pb x y Hj Hp1 Hp2 Hr; rewrite List.repeat_length in Hj.
      eapply Hn; [ exact HM | unfold T in *; lia | exact Hp2 | exact Hp1 | exact Hr ].
    Qed.

    Lemma tele_prefix_rel_ar_change' : forall ms ms1 ms2 c gs k a b,
        tele_rel (nparams_rel1 m) T ms ms1 -> tele_rel (nparams_rel2 m) T ms ms2 ->
        ind_con Mm c = Some gs -> k <= List.length (cargs_nonrec gs) ->
        tele_prefix_rel (args_rel2 m ms c) k a b -> tele_prefix_rel (args_rel1 m ms c) k a b.
    Proof.
      intros * Hm1 Hm2 Hc Hk H; rewrite tele_prefix_rel_full_iff in H |- *.
      apply (tele_rel_map _ (args_rel2 m ms c)); [| exact H ].
      intros j pa pb x y Hj Hp1 Hp2 Hr; rewrite List.repeat_length in Hj.
      eapply Ha; [ exact HM | exact Hm1 | exact Hm2 | exact Hc | lia | exact Hp2 | exact Hp1 | exact Hr ].
    Qed.

    Lemma tele_prefix_rel_ar_change : forall ms ms1 ms2 c gs k a b,
        tele_rel (nparams_rel1 m) T ms ms1 -> tele_rel (nparams_rel2 m) T ms ms2 ->
        ind_con Mm c = Some gs -> k <= List.length (cargs_nonrec gs) ->
        tele_prefix_rel (args_rel1 m ms c) k a b -> tele_prefix_rel (args_rel2 m ms c) k a b.
    Proof.
      intros * Hm1 Hm2 Hc Hk H; rewrite tele_prefix_rel_full_iff in H |- *.
      apply (tele_rel_map _ (args_rel1 m ms c)); [| exact H ].
      intros j pa pb x y Hj Hp1 Hp2 Hr; rewrite List.repeat_length in Hj.
      eapply Ha; [ exact HM | exact Hm1 | exact Hm2 | exact Hc | lia | exact Hp1 | exact Hp2 | exact Hr ].
    Qed.

    Lemma tele_prefix_rel_sh_change : forall ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 k a b,
        tele_rel (nparams_rel1 m) T ms ms1 -> tele_rel (nparams_rel2 m) T ms ms2 -> ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        tele_prefix_rel (args_rel1 m ms c) (List.length (cargs_nonrec gs1)) ws ws1 ->
        tele_prefix_rel (args_rel2 m ms c) (List.length (cargs_nonrec gs1)) ws ws2 -> k <= List.length (ptyp_doms t) ->
        tele_prefix_rel (shape_doms_rel (doms_rel1 m) ms ws (ptyp_doms t)) k a b ->
        tele_prefix_rel (shape_doms_rel (doms_rel2 m) ms ws (ptyp_doms t)) k a b.
    Proof.
      intros * Hm1 Hm2 Hc Heq Hw1 Hw2 Hk H; rewrite tele_prefix_rel_full_iff in H |- *.
      apply (tele_rel_map _ (shape_doms_rel (doms_rel1 m) ms ws (ptyp_doms t))); [| exact H ].
      intros j pa pb x y Hj Hp1 Hp2 Hr; rewrite List.repeat_length in Hj.
      eapply Hd; [ exact HM | exact Hm1 | exact Hm2 | exact Hc | exact Heq | exact Hw1 | exact Hw2 | lia | exact Hp1 | exact Hp2 | exact Hr ].
    Qed.

    Lemma tele_prefix_rel_sh_change' : forall ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 k a b,
        tele_rel (nparams_rel1 m) T ms ms1 -> tele_rel (nparams_rel2 m) T ms ms2 -> ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        tele_prefix_rel (args_rel1 m ms c) (List.length (cargs_nonrec gs1)) ws ws1 ->
        tele_prefix_rel (args_rel2 m ms c) (List.length (cargs_nonrec gs1)) ws ws2 -> k <= List.length (ptyp_doms t) ->
        tele_prefix_rel (shape_doms_rel (doms_rel2 m) ms ws (ptyp_doms t)) k a b ->
        tele_prefix_rel (shape_doms_rel (doms_rel1 m) ms ws (ptyp_doms t)) k a b.
    Proof.
      intros * Hm1 Hm2 Hc Heq Hw1 Hw2 Hk H; rewrite tele_prefix_rel_full_iff in H |- *.
      apply (tele_rel_map _ (shape_doms_rel (doms_rel2 m) ms ws (ptyp_doms t))); [| exact H ].
      intros j pa pb x y Hj Hp1 Hp2 Hr; rewrite List.repeat_length in Hj.
      eapply Hd; [ exact HM | exact Hm1 | exact Hm2 | exact Hc | exact Heq | exact Hw1 | exact Hw2 | lia | exact Hp2 | exact Hp1 | exact Hr ].
    Qed.
    End Member.

    Lemma ntele_rel_nr_change : forall j a b, ntele_rel D nparams_rel1 j a b -> ntele_rel D nparams_rel2 j a b.
    Proof.
      unfold ntele_rel; intros j a b; destruct (ind_member D j) as [Mj |] eqn:Hj; [| auto ].
      exact (tele_rel_nr_change _ _ Hj a b).
    Qed.

    Lemma okr_at_change : forall j pre Ps bs, okr_at D ups nparams_rel1 j pre Ps bs -> okr_at D ups nparams_rel2 j pre Ps bs.
    Proof. intros * [idx E R]; exists idx; [ exact E | exact (ntele_rel_nr_change _ _ _ R) ]. Qed.

    Lemma adm_change : forall ua, adm_uparams D ups nparams_rel1 args_rel1 doms_rel1 ua -> adm_uparams D ups nparams_rel2 args_rel2 doms_rel2 ua.
    Proof.
      intros ua [H1 H2 H3 H4]; constructor.
      - intros m Mm k A vs vs' s HM Hk Hp.
        assert (Hkl : k < List.length (List.rev (im_nparams Mm))) by (apply List.nth_error_Some; congruence).
        pose proof (tele_prefix_rel_nr_change' _ _ HM k vs vs' ltac:(lia) Hp) as Hp1.
        destruct (H1 _ _ _ _ _ _ s HM Hk Hp1) as [a a' E E' R].
        exists a a'; [ exact E | exact E' |].
        eapply Hn; [ exact HM | exact Hkl | exact Hp1 | exact Hp | exact R ].
      - intros m Mm ms ms' c gs k A vs vs' s HM Hm Hc Hk Hp.
        assert (Hkl : k < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        pose proof (tele_rel_nr_change' _ _ HM _ _ Hm) as Hm1.
        pose proof (tele_prefix_rel_ar_change' _ _ HM ms ms' ms' c gs k vs vs' Hm1 Hm Hc ltac:(lia) Hp) as Hp1.
        destruct (H2 _ _ _ _ _ _ _ _ _ _ s HM Hm1 Hc Hk Hp1) as [a a' E E' R].
        exists a a'; [ exact E | exact E' |].
        eapply Ha; [ exact HM | exact Hm1 | exact Hm | exact Hc | exact Hkl | exact Hp1 | exact Hp | exact R ].
      - intros m Mm ms ms' c gs gs1 t gs2 ws ws' ys ys' HM Hm Hc Heq Hp Hy.
        assert (Hk : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
          by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
        pose proof (tele_rel_nr_change' _ _ HM _ _ Hm) as Hm1.
        pose proof (tele_prefix_rel_ar_change' _ _ HM _ _ _ _ _ _ _ _ Hm1 Hm Hc Hk Hp) as Hp1.
        assert (Hy1 : tele_rel (shape_doms_rel (doms_rel1 m) ms ws (ptyp_doms t)) (ptyp_doms t) ys ys').
        { apply tele_rel_of_pre; eapply (tele_prefix_rel_sh_change' _ _ HM);
            [ exact Hm1 | exact Hm | exact Hc | exact Heq | exact Hp1 | exact Hp | lia | apply tele_rel_pre; exact Hy ]. }
        destruct (H3 _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm1 Hc Heq Hp1 Hy1) as [bs bs' E E' R].
        exists bs bs'; [ exact E | exact E' | exact (ntele_rel_nr_change _ _ _ R) ].
      - intros m Mm ms ms' c gs gs1 t gs2 ws ws' k B ys ys' HM Hm Hc Heq Hp HB Hy.
        assert (Hk : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
          by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
        assert (Hkl : k < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
        pose proof (tele_rel_nr_change' _ _ HM _ _ Hm) as Hm1.
        pose proof (tele_prefix_rel_ar_change' _ _ HM _ _ _ _ _ _ _ _ Hm1 Hm Hc Hk Hp) as Hp1.
        pose proof (tele_prefix_rel_sh_change' _ _ HM ms ms' ms' c gs gs1 t gs2 ws ws' ws' k ys ys' Hm1 Hm Hc Heq Hp1 Hp ltac:(lia) Hy) as Hy1.
        pose proof (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm1 Hm Hc Heq Hp1 Hp Hkl Hy1 Hy) as Hdd.
        unfold shape_doms_rel in Hdd; rewrite (List.nth_error_nth _ _ _ HB) in Hdd.
        destruct (H4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm1 Hc Heq Hp1 HB Hy1) as [a a' E E' Ht].
        exists a a'; [ exact E | exact E' |].
        intros x x' Hx; exact (Ht _ _ (proj2 (Hdd _ _) Hx)).
    Qed.

    (** At the fresh variables, likewise: along the fresh variables, which
        are related by both families. *)
    Lemma fresh_tele_rel_change : forall m Mm (T0 T : list centry) u0 u k pre pre' s, ind_member D m = Some Mm ->
        List.length (T0 ++ T) = List.length (im_nparams Mm) -> List.length T0 = k ->
        fresh_tele_rel (nparams_rel1 m) u0 u k pre pre' s T ->
        tele_prefix_rel (nparams_rel1 m) k pre pre' -> tele_prefix_rel (nparams_rel2 m) k pre pre' ->
        fresh_tele_rel (nparams_rel2 m) u0 u k pre pre' s T.
    Proof.
      intros m Mm T0 T u0 u k pre pre' s HM HT Hk H; revert T0 HT Hk.
      induction H as [k pre pre' s | k pre pre' s A T a a' Ea Ea' Hr H IH]; intros T0 HT Hk Hp1 Hp2; [ constructor |].
      assert (Hkl : k < List.length (List.rev (im_nparams Mm))) by (rewrite List.length_rev, <- HT, List.length_app; cbn; lia).
      pose proof (proj1 (Hn _ _ _ _ _ _ HM Hkl Hp1 Hp2 _ _) Hr) as Hr2.
      econstructor; [ exact Ea | exact Ea' | exact Hr2 |].
      apply (IH (T0 ++ ce_ass A :: nil)); [ rewrite <- List.app_assoc; exact HT | rewrite List.length_app, Hk; cbn; lia
                                         | apply tele_prefix_rel_snoc; assumption | apply tele_prefix_rel_snoc; assumption ].
    Qed.

    Lemma fresh_cargs_rel_change : forall m Mm c gsf gs1 gs u ns ns' k ws ws' s, ind_member D m = Some Mm ->
        ind_con Mm c = Some gsf -> gsf = gs1 ++ gs -> List.length (cargs_nonrec gs1) = k ->
        tele_rel (nparams_rel1 m) (List.rev (im_nparams Mm)) ns ns' -> tele_rel (nparams_rel2 m) (List.rev (im_nparams Mm)) ns ns' ->
        fresh_cargs_rel D ups u nparams_rel1 (args_rel1 m ns c) (doms_rel1 m) ns ns' k ws ws' s gs ->
        tele_prefix_rel (args_rel1 m ns c) k ws ws' -> tele_prefix_rel (args_rel2 m ns c) k ws ws' ->
        fresh_cargs_rel D ups u nparams_rel2 (args_rel2 m ns c) (doms_rel2 m) ns ns' k ws ws' s gs.
    Proof.
      intros m Mm c gsf gs1 gs u ns ns' k ws ws' s HM Hc Heq Hk Hn1 Hn2 H; revert gs1 Heq Hk.
      induction H as [k ws ws' s | k ws ws' s A gs a a' Ea Ea' Hr H IH | k ws ws' s t gs Hix Hdo H IH];
        intros gs1 Heq Hk Hp1 Hp2; [ constructor | |].
      - assert (Hkl : k < List.length (cargs_nonrec gsf))
          by (rewrite Heq, cargs_nonrec_app, List.length_app; cbn; lia).
        pose proof (proj1 (Ha _ _ _ _ _ _ _ _ _ _ _ HM Hn1 Hn2 Hc Hkl Hp1 Hp2 _ _) Hr) as Hr2.
        econstructor; [ exact Ea | exact Ea' | exact Hr2 |].
        apply (IH (gs1 ++ ca_arg A :: nil)); [ rewrite Heq, <- List.app_assoc; reflexivity
                                            | rewrite cargs_nonrec_app, List.length_app, Hk; cbn; lia
                                            | apply tele_prefix_rel_snoc; assumption | apply tele_prefix_rel_snoc; assumption ].
      - assert (Hc' : ind_con Mm c = Some (gs1 ++ ca_rec t :: gs)) by (rewrite <- Heq; exact Hc).
        subst k.
        econstructor.
        + intros ys ys' Hy.
          assert (Hy1 : tele_rel (shape_doms_rel (doms_rel1 m) ns ws (ptyp_doms t)) (ptyp_doms t) ys ys').
          { apply tele_rel_of_pre; eapply (tele_prefix_rel_sh_change' _ _ HM);
              [ exact Hn1 | exact Hn2 | exact Hc' | reflexivity | exact Hp1 | exact Hp2 | lia | apply tele_rel_pre; exact Hy ]. }
          destruct (Hix _ _ Hy1) as [b b' F F' R]; exists b b'; [ exact F | exact F' | exact (ntele_rel_nr_change _ _ _ R) ].
        + intros j B ys ys' HB Hy.
          assert (Hjl : j < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
          pose proof (tele_prefix_rel_sh_change' _ _ HM ns ns' ns' c _ gs1 t gs ws ws' ws' j ys ys' Hn1 Hn2 Hc' eq_refl Hp1 Hp2
                        (Nat.lt_le_incl _ _ Hjl) Hy) as Hy1.
          pose proof (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hn1 Hn2 Hc' eq_refl Hp1 Hp2 Hjl Hy1 Hy) as Hdd.
          unfold shape_doms_rel in Hdd; rewrite (List.nth_error_nth _ _ _ HB) in Hdd.
          destruct (Hdo _ _ _ _ HB Hy1) as [b b' F F' Ht]; exists b b'; [ exact F | exact F' |].
          intros x x' Hx; exact (Ht _ _ (proj2 (Hdd _ _) Hx)).
        + apply (IH (gs1 ++ ca_rec t :: nil)); [ rewrite Heq, <- List.app_assoc; reflexivity
                                              | rewrite cargs_nonrec_app, List.length_app; cbn; lia | exact Hp1 | exact Hp2 ].
    Qed.

      Lemma adm_fresh_fields_change : forall ua,
          (forall m Mm s, ind_member D m = Some Mm ->
             fresh_tele_rel (nparams_rel1 m) ups ua 0 nil nil s (List.rev (im_nparams Mm))) ->
          (forall m Mm c gs s ns ns', ind_member D m = Some Mm -> ind_con Mm c = Some gs ->
             Ftele List.rev (im_nparams Mm) in gc_deps ⍮ gc_stack ⍮ env_args nil ups ⍮ s ↘ ns ->
             Ftele List.rev (im_nparams Mm) in gc_deps ⍮ gc_stack ⍮ env_args nil ua ⍮ s ↘ ns' ->
             fresh_cargs_rel D ups ua nparams_rel1 (args_rel1 m ns c) (doms_rel1 m) ns ns' 0 nil nil (s + im_nn Mm) gs) ->
          (forall m Mm s, ind_member D m = Some Mm ->
             fresh_tele_rel (nparams_rel2 m) ups ua 0 nil nil s (List.rev (im_nparams Mm))) /\
          (forall m Mm c gs s ns ns', ind_member D m = Some Mm -> ind_con Mm c = Some gs ->
             Ftele List.rev (im_nparams Mm) in gc_deps ⍮ gc_stack ⍮ env_args nil ups ⍮ s ↘ ns ->
             Ftele List.rev (im_nparams Mm) in gc_deps ⍮ gc_stack ⍮ env_args nil ua ⍮ s ↘ ns' ->
             fresh_cargs_rel D ups ua nparams_rel2 (args_rel2 m ns c) (doms_rel2 m) ns ns' 0 nil nil (s + im_nn Mm) gs).
      Proof.
        intros ua H1 H2; split.
        - intros m Mm s HM.
          apply (fresh_tele_rel_change m Mm nil _ ups ua 0 nil nil s HM ltac:(cbn; apply List.length_rev) eq_refl (H1 m Mm s HM));
            apply tele_prefix_rel_nil.
        - intros m Mm c gs s ns ns' HM Hc F F'.
          destruct (fresh_tele_rel_ftele _ _ _ _ _ _ _ _ (H1 m Mm s HM)) as (ws & ws' & G & G' & Hl & Hw).
          rewrite List.app_nil_r in G, G'.
          pose proof (functional_fresh_tele' _ _ _ _ _ G F) as <-; pose proof (functional_fresh_tele' _ _ _ _ _ G' F') as <-.
          assert (Hn1 : tele_rel (nparams_rel1 m) (List.rev (im_nparams Mm)) ws ws') by (split; assumption).
          pose proof (tele_rel_nr_change _ _ HM _ _ Hn1) as Hn2.
          eapply (fresh_cargs_rel_change m Mm c gs nil gs); try reflexivity; try eassumption.
          + exact (H2 m Mm c gs s ws ws' HM Hc G G').
          + apply tele_prefix_rel_nil.
          + apply tele_prefix_rel_nil.
      Qed.

      Lemma adm_fresh_change : forall ua, adm_fresh p D ups nparams_rel1 args_rel1 doms_rel1 ua ->
          adm_fresh p D ups nparams_rel2 args_rel2 doms_rel2 ua.
      Proof.
        intros ua [Hn0 Ha0]; destruct (adm_fresh_fields_change ua Hn0 Ha0) as [Hn' Ha']; constructor; [ exact Hn' | exact Ha' ].
      Qed.

      Lemma grp_adm_change : forall k Y, grp_adm p D ups nparams_rel1 args_rel1 doms_rel1 k Y ->
          grp_adm p D ups nparams_rel2 args_rel2 doms_rel2 k Y.
      Proof.
        unfold grp_adm; intros k Y H; destruct (ind_has_views D); [ exact H |].
        destruct (ind_member D k) as [Mk |]; [| exact H ].
        destruct (im_head Mk); [ exact (adm_fresh_change _ H) | exact H ].
      Qed.

    (** Changing the relations and the admissible bases; [Hr1] is the
        reflexivity of [nparams_rel1] on the right, which puts an element's own
        non-uniform parameters on the diagonal. *)
    Lemma ind_rel_change : forall (adm1 adm2 : nat -> list domain -> Prop) (okr1 okr2 : nat -> list domain -> list exp -> list domain -> Prop),
      (forall k u, adm1 k u -> adm2 k u) -> (forall j pre Ps bs, okr1 j pre Ps bs -> okr2 j pre Ps bs) ->
      (forall m Mm a b, ind_member D m = Some Mm ->
         tele_rel (nparams_rel1 m) (List.rev (im_nparams Mm)) a b -> tele_rel (nparams_rel1 m) (List.rev (im_nparams Mm)) b b) ->
      (forall k u u' ns ns' x y, ind_rel p D adm1 okr1 nparams_rel1 args_rel1 doms_rel1 k u u' ns ns' x y ->
         ind_rel p D adm2 okr2 nparams_rel2 args_rel2 doms_rel2 k u u' ns ns' x y) /\
      (forall k u u' pre pre' gs vs vs', con_args_rel p D adm1 okr1 nparams_rel1 args_rel1 doms_rel1 k u u' pre pre' gs vs vs' ->
         forall Mk ms c gsf gs1 vp vp', ind_member D k = Some Mk -> pre = ms ++ nonrec_arg_vals gs1 vp ->
           List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
           tele_rel (nparams_rel1 k) (List.rev (im_nparams Mk)) ms ms -> ind_con Mk c = Some gsf -> gsf = gs1 ++ gs ->
           tele_rel (args_rel1 k ms c) (cargs_nonrec gsf) (nonrec_arg_vals gsf (vp ++ vs)) (nonrec_arg_vals gsf (vp' ++ vs')) ->
           con_args_rel p D adm2 okr2 nparams_rel2 args_rel2 doms_rel2 k u u' pre pre' gs vs vs') /\
      (forall k u u' pre pre' t v v', rec_arg_rel p D adm1 okr1 nparams_rel1 args_rel1 doms_rel1 k u u' pre pre' t v v' ->
         forall Mk ms c gs1 t0 gs2 ws ws' kk ys ys', ind_member D k = Some Mk -> pre = ms ++ ws ++ ys ->
           tele_rel (nparams_rel1 k) (List.rev (im_nparams Mk)) ms ms -> ind_con Mk c = Some (gs1 ++ ca_rec t0 :: gs2) ->
           tele_prefix_rel (args_rel1 k ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
           ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
           tele_prefix_rel (shape_doms_rel (doms_rel1 k) ms ws (ptyp_doms t0)) kk ys ys' ->
           rec_arg_rel p D adm2 okr2 nparams_rel2 args_rel2 doms_rel2 k u u' pre pre' t v v') /\
      (forall k u u' pre pre' t f a f' a', rec_arg_app_rel p D adm1 okr1 nparams_rel1 args_rel1 doms_rel1 k u u' pre pre' t f a f' a' ->
         forall Mk ms c gs1 t0 gs2 ws ws' kk ys ys', ind_member D k = Some Mk -> pre = ms ++ ws ++ ys ->
           tele_rel (nparams_rel1 k) (List.rev (im_nparams Mk)) ms ms -> ind_con Mk c = Some (gs1 ++ ca_rec t0 :: gs2) ->
           tele_prefix_rel (args_rel1 k ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
           ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
           tele_prefix_rel (shape_doms_rel (doms_rel1 k) ms ws (ptyp_doms t0)) kk ys ys' ->
           rec_arg_app_rel p D adm2 okr2 nparams_rel2 args_rel2 doms_rel2 k u u' pre pre' t f a f' a').
    Proof.
      intros adm1 adm2 okr1 okr2 HO HK Hr1; apply ind_rel_mut_ind_all.
      - intros * HM Hr Hns Hc Hb Hb' Hs Hs' Har Hia IH.
        pose proof (Hr1 _ _ _ _ HM Hs) as Hss.
        econstructor; try eassumption; try (apply (tele_rel_nr_change _ _ HM); eassumption).
        + apply (tele_rel_map _ (args_rel1 k (List.skipn (im_unu D Mk) bs) c)); [| eassumption ].
          intros; eapply Ha; try eassumption; apply (tele_rel_nr_change _ _ HM); eassumption.
        + apply (IH Mk (List.skipn (im_unu D Mk) bs) c gs nil nil nil HM);
            [ cbn; rewrite List.app_nil_r; reflexivity | reflexivity | reflexivity | exact Hss | exact Hc | reflexivity | exact Har ].
      - intros * HM Hh Hn1 L1 L2 O1 O2 H1 H2 Hm.
        econstructor; try eassumption; try (apply (tele_rel_nr_change _ _ HM); eassumption); apply HO; eassumption.
      - intros; constructor.
      - intros * Hia IH Mk ms c gsf gs1 vp vp' HM Hρ Hl Hl' Hn' Hc Heq Har.
        constructor.
        apply (IH Mk ms c gsf (gs1 ++ ca_arg A :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil) HM);
          [ rewrite Hρ, nonrec_arg_vals_app, <- List.app_assoc by assumption; reflexivity
          | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
          | rewrite Heq, <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Har ].
      - intros * Hsh IHs Hia IH Mk ms c gsf gs1 vp vp' HM Hρ Hl Hl' Hn' Hc Heq Har.
        pose proof (nonrec_prefix_gen _ _ _ _ _ _ _ _ Heq Hl Hl' Har) as Hpre.
        constructor.
        + apply (IHs Mk ms c gs1 t gs (nonrec_arg_vals gs1 vp) (nonrec_arg_vals gs1 vp') 0 nil nil HM);
            [ rewrite List.app_nil_r; exact Hρ | exact Hn' | rewrite <- Heq; exact Hc | exact Hpre | reflexivity | lia
            | apply tele_prefix_rel_nil ].
        + apply (IH Mk ms c gsf (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil) HM);
            [ rewrite Hρ, nonrec_arg_vals_app by assumption; cbn; rewrite List.app_nil_r; reflexivity
            | rewrite !List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | assumption | assumption
            | rewrite Heq, <- List.app_assoc; reflexivity | rewrite <- !List.app_assoc; exact Har ].
      - intros * Hb Hb' O O' Hr IHr; intros; econstructor; [ exact Hb | exact Hb' | exact (HK _ _ _ _ O) | exact (HK _ _ _ _ O') | exact IHr ].
      - intros * Hf IH Mk ns c gs1 t0 gs2 ws ws' k0 ys ys' HM Hρ Hn' Hc Hw Hs Hk Hy.
        destruct (ptyp_skip_pi _ _ _ _ Hs) as [HB Hs'].
        assert (Hkl : k0 < List.length (ptyp_doms t0)) by (apply List.nth_error_Some; congruence).
        pose proof (tele_rel_nr_change _ _ HM _ _ Hn') as Hn2.
        assert (Hk1 : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
          by (rewrite cargs_nonrec_app, List.length_app; lia).
        pose proof (tele_prefix_rel_ar_change _ _ HM _ _ _ _ _ _ _ _ Hn' Hn2 Hc Hk1 Hw) as Hw2.
        pose proof (tele_prefix_rel_sh_change _ _ HM _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hn' Hn2 Hc eq_refl Hw Hw2 Hk Hy) as Hy2.
        pose proof (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hn' Hn2 Hc eq_refl Hw Hw2 Hkl Hy Hy2) as Hdd.
        unfold shape_doms_rel in Hdd; rewrite (List.nth_error_nth _ _ _ HB) in Hdd.
        constructor; intros a a' Haa.
        subst pre; pose proof (proj2 (Hdd _ _) Haa) as Haa1.
        apply (IH a a' Haa1 Mk ns c gs1 t0 gs2 ws ws' (S k0) (ys ++ a :: nil) (ys' ++ a' :: nil) HM);
          [ rewrite <- !List.app_assoc; reflexivity | exact Hn' | exact Hc | exact Hw | exact Hs' | lia |].
        apply tele_prefix_rel_snoc; [ exact Hy |]; unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Haa1.
      - intros * Ef Ef' Hsh IH; intros; econstructor; [ exact Ef | exact Ef' | eapply IH; eassumption ].
    Qed.
  End FamChange.
End Tele.
