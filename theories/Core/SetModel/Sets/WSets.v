(** * Well-Founded Trees

    The trees of a family of positions [positions] over a set of shapes
    [shapes]: an [ordered_pair a g] of a shape [a] and a function [g] on
    the positions of [a] into trees.  In a universe [U] the trees form a
    member of [U] ([grothendieck_wbound]), closed under tree formation,
    with an induction principle.  They bound the carriers of inductive
    types with function-shaped recursive arguments, which no ω-stage
    construction reaches. *)

From Mctt.Core.SetModel.Sets Require Export Grothendieck.

(** A constant function respects equality. *)
Lemma respects_set_eq_fun_const : forall T, respects_set_eq_fun (fun _ : aczel_set => T).
Proof. intros T x y _. apply set_eq_refl. Qed.

(** [g] is a function on [D], with any values. *)
Definition is_function_on (D g : aczel_set) : Prop :=
  (forall p, set_mem p g -> exists b y, set_mem b D /\ set_eq p (ordered_pair b y)) /\
  (forall b, set_mem b D -> exists y, set_mem (ordered_pair b y) g) /\ is_functional g.

Lemma is_function_on_resp : forall D D' g g', set_eq D D' -> set_eq g g' -> is_function_on D g -> is_function_on D' g'.
Proof.
  intros * ED Eg [H1 [H2 H3]]. split; [| split].
  - intros p Hp. destruct (H1 p (set_mem_eq_r _ _ _ (set_eq_sym _ _ Eg) Hp)) as [b [y [Hb Ep]]].
    exists b, y. split; [eapply set_mem_eq_r; eauto | exact Ep].
  - intros b Hb. destruct (H2 b (set_mem_eq_r _ _ _ (set_eq_sym _ _ ED) Hb)) as [y Hy]. exists y. eapply set_mem_eq_r; eauto.
  - intros x y y' Hy Hy'. apply (H3 x);
      eapply set_mem_eq_r; [apply set_eq_sym; exact Eg | exact Hy | apply set_eq_sym; exact Eg | exact Hy'].
Qed.

Lemma is_function_on_apply : forall D g b y, is_function_on D g -> set_mem (ordered_pair b y) g -> set_eq (set_apply g b) y.
Proof.
  intros D g b y [H1 [_ H3]] Hm. apply set_apply_char; [| exact H3 | exact Hm].
  intros p Hp. destruct (H1 p Hp) as [b' [y' [_ E]]]. eauto.
Qed.

Lemma function_set_is_function_on : forall D F g, respects_set_eq_fun F -> set_mem g (function_set D F) -> is_function_on D g.
Proof.
  intros D F g HF Hg. apply (set_mem_function _ _ _ HF) in Hg as [H1 [H2 H3]]. split; [| split].
  - intros p Hp. destruct (H1 p Hp) as [x [y [Hx [_ E]]]]. eauto.
  - intros b Hb. destruct (H2 b Hb) as [y [Hy _]]. eauto.
  - exact H3.
Qed.

(** A function on [D] whose values are in the sets [F b] is a member of
    the function set. *)
Lemma is_function_on_function_set : forall D F g, respects_set_eq_fun F -> is_function_on D g ->
    (forall b, set_mem b D -> set_mem (set_apply g b) (F b)) -> set_mem g (function_set D F).
Proof.
  intros D F g HF Hf Hv. pose proof Hf as [H1 [H2 H3]]. apply (set_mem_function _ _ _ HF). split; [| split; [| exact H3]].
  - intros p Hp. destruct (H1 p Hp) as [b [y [Hb Ep]]]. exists b, y. split; [exact Hb | split; [| exact Ep]].
    assert (Hm : set_mem (ordered_pair b y) g) by (eapply set_mem_eq_l; [exact Ep | exact Hp]).
    eapply set_mem_eq_l; [exact (is_function_on_apply _ _ _ _ Hf Hm) | exact (Hv b Hb)].
  - intros b Hb. destruct (H2 b Hb) as [y Hy]. exists y. split; [exact Hy |].
    eapply set_mem_eq_l; [exact (is_function_on_apply _ _ _ _ Hf Hy) | exact (Hv b Hb)].
Qed.

Section Trees.
  Variables (shapes : aczel_set) (positions : aczel_set -> aczel_set).

(** [v] is a well-founded tree: [ordered_pair a g], a shape [a] and a
    function [g] on its positions whose values are trees. *)
Inductive is_tree : aczel_set -> Prop :=
(** A node of shape [a] whose children [g] are trees *)
| is_tree_node : forall v a g, set_eq v (ordered_pair a g) -> set_mem a shapes -> is_function_on (positions a) g ->
    (forall b, set_mem b (positions a) -> is_tree (set_apply g b)) -> is_tree v.

Lemma is_tree_resp : respects_set_eq is_tree.
Proof.
  intros x y E H. destruct H as [v a g Ev Ha Hg Hc]. eapply is_tree_node; eauto.
  eapply set_eq_trans; [apply set_eq_sym; exact E | exact Ev].
Qed.

(** Every set closed under tree formation contains every tree. *)
Lemma is_tree_in_closed : forall T,
    (forall a g, set_mem a shapes -> set_mem g (function_set (positions a) (fun _ => T)) -> set_mem (ordered_pair a g) T) ->
    forall v, is_tree v -> set_mem v T.
Proof.
  intros T HT v H. induction H as [v a g Ev Ha Hg Hc IH].
  eapply set_mem_eq_l; [apply set_eq_sym; exact Ev |]. apply HT; [exact Ha |].
  apply is_function_on_function_set; [apply respects_set_eq_fun_const | exact Hg | exact IH].
Qed.

End Trees.

Section TreesInUniverse.
  Variable U : aczel_set.
  Hypothesis HU : grothendieck U.

Lemma grothendieck_apply : forall f x, set_mem f U -> set_mem (set_apply f x) U.
Proof.
  intros f x Hf. unfold set_apply. apply (grothendieck_union _ HU). apply (grothendieck_sub _ HU (replacement_set f pair_second)).
  - apply (grothendieck_replacement _ HU f Hf pair_second pair_second_resp). intros y Hy.
    apply (grothendieck_pair_second _ HU). apply (grothendieck_transitive _ HU f); auto.
  - intros z [[a Ha] Hz]. apply (set_mem_replacement _ _ _ pair_second_resp).
    exists (aczel_element f a). split; [exists a; apply set_eq_refl | exact Hz].
Qed.

Lemma grothendieck_ordered_pair_second : forall x y, set_mem (ordered_pair x y) U -> set_mem y U.
Proof.
  intros x y H. apply (grothendieck_transitive _ HU (unordered_pair_set x y)); [| apply set_mem_unordered_pair; right; apply set_eq_refl].
  apply (grothendieck_transitive _ HU (ordered_pair x y) _ H). apply set_mem_ordered_pair. right. apply set_eq_refl.
Qed.

(** The trees of the family that are members of [U]. *)
Definition tree_set (shapes : aczel_set) (positions : aczel_set -> aczel_set) : aczel_set :=
  separation_set U (is_tree shapes positions).

Lemma set_mem_tree : forall S P z, set_mem z (tree_set S P) <-> set_mem z U /\ is_tree S P z.
Proof. intros. apply set_mem_separation. apply is_tree_resp. Qed.

(** The trees are a member of [U]: the W-bound bounds them. *)
Lemma grothendieck_tree_set : forall S P, respects_set_eq_fun P -> set_mem S U -> (forall a, set_mem a S -> set_mem (P a) U) ->
    set_mem (tree_set S P) U.
Proof.
  intros S P HP HS HPa. destruct (grothendieck_wbound _ HU S HS P HP HPa) as [T [HT Hcl]].
  apply (grothendieck_sub _ HU T); [exact HT |]. intros z Hz. apply set_mem_tree in Hz as [_ Hz].
  exact (is_tree_in_closed S P T Hcl z Hz).
Qed.

(** The trees are closed under tree formation, by replacement alone. *)
Lemma tree_set_node : forall S P a g, respects_set_eq_fun P -> set_mem S U -> (forall a, set_mem a S -> set_mem (P a) U) ->
    set_mem a S -> set_mem g (function_set (P a) (fun _ => tree_set S P)) -> set_mem (ordered_pair a g) (tree_set S P).
Proof.
  intros * HP HS HPa Ha Hg. pose proof (function_set_is_function_on _ _ _ (respects_set_eq_fun_const _) Hg) as Hf.
  assert (Hv : forall b, set_mem b (P a) -> set_mem (set_apply g b) (tree_set S P))
    by (intros b Hb; exact (function_set_apply _ _ _ _ (respects_set_eq_fun_const _) Hg Hb)).
  apply set_mem_tree. split.
  - apply (grothendieck_ordered_pair _ HU); [apply (grothendieck_transitive _ HU S); auto |].
    assert (HF : respects_set_eq_fun (fun b => ordered_pair b (set_apply g b)))
      by (intros x y E; apply ordered_pair_resp; [exact E | apply set_apply_resp; [apply set_eq_refl | exact E]]).
    eapply set_mem_eq_l; [| apply (grothendieck_replacement _ HU (P a) (HPa a Ha) _ HF); intros b Hb;
        apply (grothendieck_ordered_pair _ HU);
        [apply (grothendieck_transitive _ HU (P a)); auto | apply (proj1 (proj1 (set_mem_tree _ _ _) (Hv b Hb)))]].
    apply set_eq_intro; intros z Hz.
    + apply (set_mem_replacement _ _ _ HF) in Hz as [b [Hb Ez]]. pose proof Hf as [_ [H2 _]]. destruct (H2 b Hb) as [y Hy].
      eapply set_mem_eq_l; [| exact Hy].
      eapply set_eq_trans; [apply ordered_pair_resp; [apply set_eq_refl | apply set_eq_sym; exact (is_function_on_apply _ _ _ _ Hf Hy)] |
                            apply set_eq_sym; exact Ez].
    + destruct Hf as [H1 [H2 H3]]. destruct (H1 z Hz) as [b [y [Hb Ez]]]. apply (set_mem_replacement _ _ _ HF). exists b.
      split; [exact Hb |].
      assert (Hm : set_mem (ordered_pair b y) g) by (eapply set_mem_eq_l; [exact Ez | exact Hz]).
      eapply set_eq_trans; [exact Ez | apply ordered_pair_resp;
        [apply set_eq_refl | apply set_eq_sym; exact (is_function_on_apply _ _ _ _ (conj H1 (conj H2 H3)) Hm)]].
  - eapply is_tree_node; [apply set_eq_refl | exact Ha | exact Hf |]. intros b Hb.
    exact (proj2 (proj1 (set_mem_tree _ _ _) (Hv b Hb))).
Qed.

(** Induction on the trees. *)
Lemma tree_set_ind : forall S P (Q : aczel_set -> Prop), respects_set_eq_fun P -> respects_set_eq Q ->
    (forall a g, set_mem a S -> set_mem g (function_set (P a) (fun _ => tree_set S P)) ->
       (forall b, set_mem b (P a) -> Q (set_apply g b)) -> Q (ordered_pair a g)) ->
    forall z, set_mem z (tree_set S P) -> Q z.
Proof.
  intros * HP HQ Hstep z Hz. pose proof Hz as Hz0. apply set_mem_tree in Hz as [HzU Hz]. revert Hz0 HzU.
  induction Hz as [v a g Ev Ha Hg Hc IH]; intros Hz0 HzU.
  assert (HgU : set_mem g U) by (apply (grothendieck_ordered_pair_second a g); eapply set_mem_eq_l; [exact Ev | exact HzU]).
  assert (HcW : forall b, set_mem b (P a) -> set_mem (set_apply g b) (tree_set S P))
    by (intros b Hb; apply set_mem_tree; split; [apply grothendieck_apply; exact HgU | exact (Hc b Hb)]).
  eapply HQ; [apply set_eq_sym; exact Ev |].
  apply Hstep; [exact Ha | apply is_function_on_function_set; [apply respects_set_eq_fun_const | exact Hg | exact HcW] |].
  intros b Hb. apply IH; [exact Hb | exact (HcW b Hb) | apply grothendieck_apply; exact HgU].
Qed.

End TreesInUniverse.
