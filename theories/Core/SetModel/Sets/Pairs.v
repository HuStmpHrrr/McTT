(** * Pairs and Functions of Sets

    Kuratowski ordered pairs and their projections, products, the graph of
    a function on sets, application of a set of pairs and the set of
    dependent functions ([function_set]). *)

From Mctt.Core.SetModel.Sets Require Export Aczel.

(** ** Ordered Pairs *)

(** The ordered pair of [x] and [y]: [{{x}, {x, y}}]. *)
Definition ordered_pair (x y : aczel_set) : aczel_set :=
  unordered_pair_set (singleton_set x) (unordered_pair_set x y).

Lemma ordered_pair_resp : forall x y x' y', set_eq x x' -> set_eq y y' -> set_eq (ordered_pair x y) (ordered_pair x' y').
Proof. intros. unfold ordered_pair. apply unordered_pair_set_resp; [apply singleton_set_resp | apply unordered_pair_set_resp]; auto. Qed.

(** The members of the union of a pair that are its first component: those
    in every member of the pair. *)
Definition is_pair_first (p : aczel_set) : aczel_set -> Prop :=
  fun z => forall w, set_mem w p -> set_mem z w.

(** The members of the union of a pair that are its second component:
    those in exactly one member of the pair. *)
Definition is_pair_second (p : aczel_set) : aczel_set -> Prop :=
  fun z => exists w, set_mem w p /\ set_mem z w /\ forall w', set_mem w' p -> set_mem z w' -> set_eq w' w.

Lemma is_pair_first_resp : forall p, respects_set_eq (is_pair_first p).
Proof. intros p x y E H w Hw. eapply set_mem_eq_l; [exact E | apply H; exact Hw]. Qed.

Lemma is_pair_second_resp : forall p, respects_set_eq (is_pair_second p).
Proof.
  intros p x y E [w [Hw [Hx H]]]. exists w. split; auto. split; [eapply set_mem_eq_l; eauto |].
  intros w' Hw' Hy. apply H; auto. eapply set_mem_eq_l; [apply set_eq_sym; exact E | exact Hy].
Qed.

(** The first component of a pair. *)
Definition pair_first (p : aczel_set) : aczel_set := union_set (separation_set (union_set p) (is_pair_first p)).

(** The second component of a pair. *)
Definition pair_second (p : aczel_set) : aczel_set := union_set (separation_set (union_set p) (is_pair_second p)).

Lemma set_mem_ordered_pair : forall w x y, set_mem w (ordered_pair x y) <-> set_eq w (singleton_set x) \/ set_eq w (unordered_pair_set x y).
Proof. intros. unfold ordered_pair. apply set_mem_unordered_pair. Qed.

Lemma set_mem_union_ordered_pair : forall z x y, set_mem z (union_set (ordered_pair x y)) <-> set_eq z x \/ set_eq z y.
Proof.
  intros z x y. rewrite set_mem_union. split.
  - intros [w [Hw Hz]]. apply set_mem_ordered_pair in Hw as [H | H].
    + left. apply set_mem_singleton. eapply set_mem_eq_r; eauto.
    + apply set_mem_unordered_pair. eapply set_mem_eq_r; eauto.
  - intros [H | H].
    + exists (singleton_set x). split; [apply set_mem_ordered_pair; left; apply set_eq_refl | apply set_mem_singleton; exact H].
    + exists (unordered_pair_set x y).
      split; [apply set_mem_ordered_pair; right; apply set_eq_refl | apply set_mem_unordered_pair; right; exact H].
Qed.

Lemma pair_first_ordered_pair : forall x y, set_eq (pair_first (ordered_pair x y)) x.
Proof.
  intros x y. unfold pair_first. apply union_set_const.
  - exists x. apply (set_mem_separation _ _ _ (is_pair_first_resp _)).
    split; [apply set_mem_union_ordered_pair; left; apply set_eq_refl |].
    intros w Hw. apply set_mem_ordered_pair in Hw as [H | H].
    + eapply set_mem_eq_r; [apply set_eq_sym; exact H | apply set_mem_singleton; apply set_eq_refl].
    + eapply set_mem_eq_r; [apply set_eq_sym; exact H | apply set_mem_unordered_pair; left; apply set_eq_refl].
  - intros w Hw. apply (set_mem_separation _ _ _ (is_pair_first_resp _)) in Hw as [_ H].
    assert (Hs : set_mem w (singleton_set x)) by (apply H; apply set_mem_ordered_pair; left; apply set_eq_refl).
    apply set_mem_singleton in Hs. exact Hs.
Qed.

Lemma pair_second_ordered_pair : forall x y, set_eq (pair_second (ordered_pair x y)) y.
Proof.
  intros x y. unfold pair_second. apply union_set_const.
  - exists y. apply (set_mem_separation _ _ _ (is_pair_second_resp _)).
    split; [apply set_mem_union_ordered_pair; right; apply set_eq_refl |].
    exists (unordered_pair_set x y). split; [apply set_mem_ordered_pair; right; apply set_eq_refl |].
    split; [apply set_mem_unordered_pair; right; apply set_eq_refl |].
    intros w' Hw' Hy. apply set_mem_ordered_pair in Hw' as [H | H]; [| exact H].
    (** [y] is in [w' = {x}]: so [y = x] and [{x} = {x, y}] *)
    pose proof (set_mem_eq_r _ _ _ H Hy) as Hyx. apply set_mem_singleton in Hyx.
    eapply set_eq_trans; [exact H |]. apply set_eq_intro; intros z Hz.
    + apply set_mem_singleton in Hz. apply set_mem_unordered_pair. left. exact Hz.
    + apply set_mem_singleton. apply set_mem_unordered_pair in Hz as [Hz | Hz]; [exact Hz | eapply set_eq_trans; eauto].
  - intros w Hw. apply (set_mem_separation _ _ _ (is_pair_second_resp _)) in Hw as [Hw [w0 [Hw0 [Hzw0 Huniq]]]].
    apply set_mem_union_ordered_pair in Hw as [Hx | Hy]; [| exact Hy].
    (** [w = x]: it is in both members, so they are equal and [y = x] *)
    assert (E1 : set_eq (singleton_set x) w0).
    { apply Huniq; [apply set_mem_ordered_pair; left; apply set_eq_refl | apply set_mem_singleton; exact Hx]. }
    assert (E2 : set_eq (unordered_pair_set x y) w0).
    { apply Huniq; [apply set_mem_ordered_pair; right; apply set_eq_refl | apply set_mem_unordered_pair; left; exact Hx]. }
    assert (Hy : set_mem y (singleton_set x)).
    { eapply set_mem_eq_r; [eapply set_eq_trans; [exact E2 | apply set_eq_sym; exact E1] |].
      apply set_mem_unordered_pair; right; apply set_eq_refl. }
    apply set_mem_singleton in Hy. eapply set_eq_trans; [exact Hx | apply set_eq_sym; exact Hy].
Qed.

Lemma pair_first_resp : forall p q, set_eq p q -> set_eq (pair_first p) (pair_first q).
Proof.
  intros p q E. unfold pair_first. apply union_set_resp.
  apply separation_set_resp; [apply is_pair_first_resp | apply is_pair_first_resp | apply union_set_resp; exact E |].
  intros z _. split; intros H w Hw; apply H.
  - eapply set_mem_eq_r; [apply set_eq_sym; exact E | exact Hw].
  - eapply set_mem_eq_r; [exact E | exact Hw].
Qed.

Lemma pair_second_resp : forall p q, set_eq p q -> set_eq (pair_second p) (pair_second q).
Proof.
  intros p q E. unfold pair_second. apply union_set_resp.
  apply separation_set_resp; [apply is_pair_second_resp | apply is_pair_second_resp | apply union_set_resp; exact E |].
  intros z _. split; intros [w [Hw [Hz H]]]; exists w.
  - split; [eapply set_mem_eq_r; eauto |]. split; auto.
    intros w' Hw' Hz'. apply H; auto. eapply set_mem_eq_r; [apply set_eq_sym; exact E | exact Hw'].
  - split; [eapply set_mem_eq_r; [apply set_eq_sym; exact E | exact Hw] |]. split; auto.
    intros w' Hw' Hz'. apply H; auto. eapply set_mem_eq_r; [exact E | exact Hw'].
Qed.

Lemma ordered_pair_inj : forall x y x' y', set_eq (ordered_pair x y) (ordered_pair x' y') -> set_eq x x' /\ set_eq y y'.
Proof.
  intros * E. split.
  - eapply set_eq_trans; [apply set_eq_sym; apply pair_first_ordered_pair |].
    eapply set_eq_trans; [apply pair_first_resp; exact E | apply pair_first_ordered_pair].
  - eapply set_eq_trans; [apply set_eq_sym; apply pair_second_ordered_pair |].
    eapply set_eq_trans; [apply pair_second_resp; exact E | apply pair_second_ordered_pair].
Qed.

(** An ordered pair is not empty. *)
Lemma ordered_pair_not_empty : forall x y, ~ set_eq (ordered_pair x y) empty_set.
Proof.
  intros x y E. apply (set_mem_empty (singleton_set x)).
  eapply set_mem_eq_r; [exact E | apply set_mem_ordered_pair; left; apply set_eq_refl].
Qed.

(** ** Products, Graphs and Application *)

(** The pairs of a member of [S] and a member of [T]. *)
Definition product_set (S T : aczel_set) : aczel_set :=
  family_set (aczel_index S * aczel_index T) (fun p => ordered_pair (aczel_element S (fst p)) (aczel_element T (snd p))).

Lemma set_mem_product : forall z S T, set_mem z (product_set S T) <->
    exists x y, set_mem x S /\ set_mem y T /\ set_eq z (ordered_pair x y).
Proof.
  intros z S T. split.
  - intros [[a b] H]. exists (aczel_element S a), (aczel_element T b). split; [exists a; apply set_eq_refl |].
    split; [exists b; apply set_eq_refl | exact H].
  - intros [x [y [[a Ha] [[b Hb] H]]]]. exists (a, b). cbn. eapply set_eq_trans; [exact H | apply ordered_pair_resp; auto].
Qed.

Lemma product_set_resp : forall S S' T T', set_eq S S' -> set_eq T T' -> set_eq (product_set S T) (product_set S' T').
Proof.
  intros * ES ET. apply set_eq_intro; intros z Hz; apply set_mem_product; apply set_mem_product in Hz as [x [y [Hx [Hy E]]]];
    exists x, y; (split; [| split; [| exact E]]).
  - eapply set_mem_eq_r; eauto.
  - eapply set_mem_eq_r; eauto.
  - eapply set_mem_eq_r; [apply set_eq_sym; exact ES | exact Hx].
  - eapply set_mem_eq_r; [apply set_eq_sym; exact ET | exact Hy].
Qed.

(** The graph of [F] on [S]: the pairs of each member [x] of [S] with
    [F x]. *)
Definition graph_set (S : aczel_set) (F : aczel_set -> aczel_set) : aczel_set :=
  family_set (aczel_index S) (fun a => ordered_pair (aczel_element S a) (F (aczel_element S a))).

Lemma set_mem_graph : forall z S F, respects_set_eq_fun F ->
    (set_mem z (graph_set S F) <-> exists x, set_mem x S /\ set_eq z (ordered_pair x (F x))).
Proof.
  intros z S F HF. split.
  - intros [a H]. exists (aczel_element S a). split; [exists a; apply set_eq_refl | exact H].
  - intros [x [[a Ha] H]]. exists a. cbn. eapply set_eq_trans; [exact H | apply ordered_pair_resp; [exact Ha | apply HF; exact Ha]].
Qed.

(** Two functions that agree on the members of [S]. *)
Definition agree_on (S : aczel_set) (F G : aczel_set -> aczel_set) : Prop := forall x, set_mem x S -> set_eq (F x) (G x).

Lemma graph_set_resp : forall S S' F G, respects_set_eq_fun F -> respects_set_eq_fun G -> set_eq S S' -> agree_on S F G ->
    set_eq (graph_set S F) (graph_set S' G).
Proof.
  intros * HF HG ES EFG. apply set_eq_intro; intros z Hz.
  - apply (set_mem_graph _ _ _ HF) in Hz as [x [Hx E]]. apply (set_mem_graph _ _ _ HG). exists x.
    split; [eapply set_mem_eq_r; eauto | eapply set_eq_trans; [exact E | apply ordered_pair_resp; [apply set_eq_refl | apply EFG; exact Hx]]].
  - apply (set_mem_graph _ _ _ HG) in Hz as [x [Hx E]].
    assert (HxS : set_mem x S) by (eapply set_mem_eq_r; [apply set_eq_sym; exact ES | exact Hx]).
    apply (set_mem_graph _ _ _ HF). exists x.
    split; [exact HxS | eapply set_eq_trans; [exact E | apply ordered_pair_resp; [apply set_eq_refl | apply set_eq_sym; apply EFG; exact HxS]]].
Qed.

(** The domain of a set of pairs: the first components of its pairs. *)
Definition relation_domain (f : aczel_set) : aczel_set :=
  family_set (aczel_index f) (fun a => pair_first (aczel_element f a)).

Lemma relation_domain_resp : forall f g, set_eq f g -> set_eq (relation_domain f) (relation_domain g).
Proof.
  intros f g E. apply set_eq_intro; intros z Hz; apply set_mem_family in Hz as [a Ea].
  - assert (Hm : set_mem (aczel_element f a) g) by (eapply set_mem_eq_r; [exact E | exists a; apply set_eq_refl]).
    destruct Hm as [b Eb]. apply set_mem_family. exists b. eapply set_eq_trans; [exact Ea | apply pair_first_resp; exact Eb].
  - assert (Hm : set_mem (aczel_element g a) f) by (eapply set_mem_eq_r; [apply set_eq_sym; exact E | exists a; apply set_eq_refl]).
    destruct Hm as [b Eb]. apply set_mem_family. exists b. eapply set_eq_trans; [exact Ea | apply pair_first_resp; exact Eb].
Qed.

(** The application of a set of pairs [f] to [x]: the union of the
    second components of its pairs whose first component is [x]. *)
Definition set_apply (f x : aczel_set) : aczel_set :=
  union_set (family_set {a : aczel_index f | set_eq (pair_first (aczel_element f a)) x}
                        (fun p => pair_second (aczel_element f (proj1_sig p)))).

(** Every member of [f] is an ordered pair. *)
Definition is_relation (f : aczel_set) : Prop := forall p, set_mem p f -> exists x y, set_eq p (ordered_pair x y).

(** No two pairs of [f] with the same first component have different second
    components. *)
Definition is_functional (f : aczel_set) : Prop :=
  forall x y y', set_mem (ordered_pair x y) f -> set_mem (ordered_pair x y') f -> set_eq y y'.

Lemma set_apply_char : forall f x y, is_relation f -> is_functional f -> set_mem (ordered_pair x y) f -> set_eq (set_apply f x) y.
Proof.
  intros f x y Hr Hf Hxy. unfold set_apply. destruct Hxy as [a0 Ha0]. apply union_set_const.
  - assert (H1 : set_eq (pair_first (aczel_element f a0)) x).
    { eapply set_eq_trans; [apply pair_first_resp; apply set_eq_sym; exact Ha0 | apply pair_first_ordered_pair]. }
    exists (pair_second (aczel_element f a0)). exists (exist _ a0 H1). apply set_eq_refl.
  - intros w [[a Ha] Hw]. cbn in Hw.
    destruct (Hr (aczel_element f a) (ex_intro _ a (set_eq_refl _))) as [x' [y' Hp]].
    assert (Hx' : set_eq x' x).
    { eapply set_eq_trans; [apply set_eq_sym; apply pair_first_ordered_pair |].
      eapply set_eq_trans; [apply pair_first_resp; apply set_eq_sym; exact Hp | exact Ha]. }
    assert (Hm : set_mem (ordered_pair x y') f).
    { exists a. eapply set_eq_trans; [apply ordered_pair_resp; [apply set_eq_sym; exact Hx' | apply set_eq_refl] | apply set_eq_sym; exact Hp]. }
    assert (Hm0 : set_mem (ordered_pair x y) f) by (exists a0; exact Ha0).
    eapply set_eq_trans; [exact Hw |]. eapply set_eq_trans; [apply pair_second_resp; exact Hp |].
    eapply set_eq_trans; [apply pair_second_ordered_pair | apply set_eq_sym; apply (Hf _ _ _ Hm0 Hm)].
Qed.

Lemma graph_set_relation : forall S F, respects_set_eq_fun F -> is_relation (graph_set S F).
Proof. intros S F HF p Hp. apply (set_mem_graph _ _ _ HF) in Hp as [x [_ H]]. eauto. Qed.

Lemma graph_set_functional : forall S F, respects_set_eq_fun F -> is_functional (graph_set S F).
Proof.
  intros S F HF x y y' H H'. apply (set_mem_graph _ _ _ HF) in H as [x1 [_ E1]]. apply (set_mem_graph _ _ _ HF) in H' as [x2 [_ E2]].
  apply ordered_pair_inj in E1 as [Ex1 Ey1]. apply ordered_pair_inj in E2 as [Ex2 Ey2].
  eapply set_eq_trans; [exact Ey1 |].
  eapply set_eq_trans; [apply HF; eapply set_eq_trans; [apply set_eq_sym; exact Ex1 | exact Ex2] | apply set_eq_sym; exact Ey2].
Qed.

Lemma set_apply_graph : forall S F x, respects_set_eq_fun F -> set_mem x S -> set_eq (set_apply (graph_set S F) x) (F x).
Proof.
  intros S F x HF Hx. apply set_apply_char; [apply graph_set_relation; auto | apply graph_set_functional; auto |].
  apply (set_mem_graph _ _ _ HF). exists x. split; [exact Hx | apply set_eq_refl].
Qed.

Lemma set_apply_resp : forall f f' x x', set_eq f f' -> set_eq x x' -> set_eq (set_apply f x) (set_apply f' x').
Proof.
  intros f f' x x' Ef Ex. unfold set_apply. apply union_set_resp. apply set_eq_intro.
  - intros z [[a Ha] Hz]. cbn in Hz. pose proof (proj1 (set_extensionality _ _) Ef) as Ef'.
    destruct (proj1 (Ef' (aczel_element f a)) (ex_intro _ a (set_eq_refl _))) as [b Hb].
    assert (Hb' : set_eq (pair_first (aczel_element f' b)) x').
    { eapply set_eq_trans; [apply pair_first_resp; apply set_eq_sym; exact Hb |]. eapply set_eq_trans; [exact Ha | exact Ex]. }
    exists (exist _ b Hb'). cbn. eapply set_eq_trans; [exact Hz | apply pair_second_resp; exact Hb].
  - intros z [[b Hb] Hz]. cbn in Hz. pose proof (proj1 (set_extensionality _ _) Ef) as Ef'.
    destruct (proj2 (Ef' (aczel_element f' b)) (ex_intro _ b (set_eq_refl _))) as [a Ha].
    assert (Ha' : set_eq (pair_first (aczel_element f a)) x).
    { eapply set_eq_trans; [apply pair_first_resp; apply set_eq_sym; exact Ha |].
      eapply set_eq_trans; [exact Hb | apply set_eq_sym; exact Ex]. }
    exists (exist _ a Ha'). cbn. eapply set_eq_trans; [exact Hz | apply pair_second_resp; exact Ha].
Qed.

(** Applying the empty set gives the empty set: so a proof, the empty
    set, applied to anything is a proof. *)
Lemma set_apply_empty : forall x, set_eq (set_apply empty_set x) empty_set.
Proof.
  intros x. apply set_eq_intro; intros z Hz; [| exfalso; exact (set_mem_empty _ Hz)].
  apply set_mem_union in Hz as [w [[[[] _] _] _]].
Qed.

(** ** Dependent Functions *)

(** [g] is a function on [S] whose value at each [x] is a member of
    [F x]. *)
Definition is_dependent_function (S : aczel_set) (F : aczel_set -> aczel_set) (g : aczel_set) : Prop :=
  (forall x, set_mem x S -> exists y, set_mem (ordered_pair x y) g /\ set_mem y (F x)) /\ is_functional g.

Lemma is_dependent_function_resp : forall S F, respects_set_eq (is_dependent_function S F).
Proof.
  intros S F g g' E [H1 H2]. split.
  - intros x Hx. destruct (H1 x Hx) as [y [Hy Hy']]. exists y. split; [eapply set_mem_eq_r; eauto | exact Hy'].
  - intros x y y' Hy Hy'. apply (H2 x);
      eapply set_mem_eq_r; [apply set_eq_sym; exact E | exact Hy | apply set_eq_sym; exact E | exact Hy'].
Qed.

(** The union of the sets [F x] for the members [x] of [S]. *)
Definition indexed_union_set (S : aczel_set) (F : aczel_set -> aczel_set) : aczel_set :=
  union_set (family_set (aczel_index S) (fun a => F (aczel_element S a))).

Lemma set_mem_indexed_union : forall z S F, respects_set_eq_fun F ->
    (set_mem z (indexed_union_set S F) <-> exists x, set_mem x S /\ set_mem z (F x)).
Proof.
  intros z S F HF. unfold indexed_union_set. rewrite set_mem_union. split.
  - intros [w [[a Ha] Hz]]. exists (aczel_element S a). split; [exists a; apply set_eq_refl | eapply set_mem_eq_r; eauto].
  - intros [x [[a Ha] Hz]]. exists (F (aczel_element S a)).
    split; [exists a; apply set_eq_refl | eapply set_mem_eq_r; [apply HF; exact Ha | exact Hz]].
Qed.

(** The dependent functions on [S] into [F]. *)
Definition function_set (S : aczel_set) (F : aczel_set -> aczel_set) : aczel_set :=
  separation_set (power_set (product_set S (indexed_union_set S F))) (is_dependent_function S F).

Lemma set_mem_function : forall g S F, respects_set_eq_fun F -> (set_mem g (function_set S F) <->
    (forall p, set_mem p g -> exists x y, set_mem x S /\ set_mem y (F x) /\ set_eq p (ordered_pair x y)) /\
    is_dependent_function S F g).
Proof.
  intros g S F HF. unfold function_set. rewrite (set_mem_separation _ _ _ (is_dependent_function_resp S F)), set_mem_power. split.
  - intros [Hs Hf]. split; [| exact Hf]. intros p Hp. pose proof (Hs _ Hp) as Hp2.
    apply set_mem_product in Hp2 as [x [y [Hx [Hy E]]]].
    exists x, y. split; [exact Hx |]. split; [| exact E].
    (** [y] is in some [F x']; functionality and totality put it in [F x] *)
    destruct Hf as [Ht Hu]. destruct (Ht x Hx) as [y' [Hy' Hy'F]].
    assert (Hpg : set_mem (ordered_pair x y) g) by (eapply set_mem_eq_l; [exact E | exact Hp]).
    pose proof (Hu _ _ _ Hpg Hy') as Eyy. eapply set_mem_eq_l; [apply set_eq_sym; exact Eyy | exact Hy'F].
  - intros [Hp Hf]. split; [| exact Hf]. intros p Hpg. destruct (Hp p Hpg) as [x [y [Hx [Hy E]]]].
    apply set_mem_product. exists x, y. split; [exact Hx |]. split; [| exact E].
    apply (set_mem_indexed_union _ _ _ HF). exists x. split; assumption.
Qed.

Lemma graph_set_function : forall S F G, respects_set_eq_fun F -> respects_set_eq_fun G ->
    (forall x, set_mem x S -> set_mem (G x) (F x)) -> set_mem (graph_set S G) (function_set S F).
Proof.
  intros S F G HF HG H. apply (set_mem_function _ _ _ HF). split.
  - intros p Hp. apply (set_mem_graph _ _ _ HG) in Hp as [x [Hx E]]. exists x, (G x). auto.
  - split; [| apply graph_set_functional; auto]. intros x Hx. exists (G x). split; [| auto].
    apply (set_mem_graph _ _ _ HG). exists x. split; [exact Hx | apply set_eq_refl].
Qed.

Lemma function_set_relation : forall g S F, respects_set_eq_fun F -> set_mem g (function_set S F) ->
    is_relation g /\ is_functional g.
Proof.
  intros g S F HF Hg. apply (set_mem_function _ _ _ HF) in Hg as [Hp [_ Hu]]. split; [| exact Hu].
  intros p Hpg. destruct (Hp p Hpg) as [x' [y' [_ [_ E]]]]. eauto.
Qed.

Lemma function_set_apply : forall g S F x, respects_set_eq_fun F -> set_mem g (function_set S F) -> set_mem x S ->
    set_mem (set_apply g x) (F x).
Proof.
  intros g S F x HF Hg Hx. pose proof (function_set_relation _ _ _ HF Hg) as [Hr Hu].
  apply (set_mem_function _ _ _ HF) in Hg as [_ [Ht _]].
  destruct (Ht x Hx) as [y [Hy HyF]].
  eapply set_mem_eq_l; [apply set_eq_sym; apply set_apply_char; eauto | exact HyF].
Qed.

(** Two functions of a function set are equal exactly when they are equal
    at every point. *)
Lemma function_set_ext : forall g h S F, respects_set_eq_fun F -> set_mem g (function_set S F) -> set_mem h (function_set S F) ->
    (forall x, set_mem x S -> set_eq (set_apply g x) (set_apply h x)) -> set_eq g h.
Proof.
  intros g h S F HF Hg Hh Hpt.
  pose proof (function_set_relation _ _ _ HF Hg) as [Rg Fg]. pose proof (function_set_relation _ _ _ HF Hh) as [Rh Fh].
  apply (set_mem_function _ _ _ HF) in Hg as [Pg [Tg _]]. apply (set_mem_function _ _ _ HF) in Hh as [Ph [Th _]].
  apply set_eq_intro.
  - intros p Hp. destruct (Pg p Hp) as [x [y [Hx [_ E]]]].
    assert (Hxy : set_mem (ordered_pair x y) g) by (eapply set_mem_eq_l; [exact E | exact Hp]).
    destruct (Th x Hx) as [y' [Hy' _]].
    assert (Ey : set_eq y y').
    { eapply set_eq_trans; [apply set_eq_sym; apply (set_apply_char g x y Rg Fg Hxy) |].
      eapply set_eq_trans; [apply Hpt; exact Hx | apply (set_apply_char h x y' Rh Fh Hy')]. }
    eapply set_mem_eq_l; [apply set_eq_sym; eapply set_eq_trans; [exact E | apply ordered_pair_resp; [apply set_eq_refl | exact Ey]] | exact Hy'].
  - intros p Hp. destruct (Ph p Hp) as [x [y [Hx [_ E]]]].
    assert (Hxy : set_mem (ordered_pair x y) h) by (eapply set_mem_eq_l; [exact E | exact Hp]).
    destruct (Tg x Hx) as [y' [Hy' _]].
    assert (Ey : set_eq y y').
    { eapply set_eq_trans; [apply set_eq_sym; apply (set_apply_char h x y Rh Fh Hxy) |].
      eapply set_eq_trans; [apply set_eq_sym; apply Hpt; exact Hx | apply (set_apply_char g x y' Rg Fg Hy')]. }
    eapply set_mem_eq_l; [apply set_eq_sym; eapply set_eq_trans; [exact E | apply ordered_pair_resp; [apply set_eq_refl | exact Ey]] | exact Hy'].
Qed.

Lemma function_set_resp : forall S S' F G, respects_set_eq_fun F -> respects_set_eq_fun G -> set_eq S S' -> agree_on S F G ->
    set_eq (function_set S F) (function_set S' G).
Proof.
  intros * HF HG ES EFG.
  assert (EFG' : forall x, set_mem x S' -> set_eq (F x) (G x))
    by (intros x Hx; apply EFG; eapply set_mem_eq_r; [apply set_eq_sym; exact ES | exact Hx]).
  apply set_eq_intro; intros g Hg.
  - apply (set_mem_function _ _ _ HF) in Hg as [Hp [Ht Hu]]. apply (set_mem_function _ _ _ HG). split; [| split; [| exact Hu]].
    + intros p Hpg. destruct (Hp p Hpg) as [x [y [Hx [Hy E]]]]. exists x, y.
      split; [eapply set_mem_eq_r; eauto | split; [eapply set_mem_eq_r; [apply EFG; exact Hx | exact Hy] | exact E]].
    + intros x Hx. assert (HxS : set_mem x S) by (eapply set_mem_eq_r; [apply set_eq_sym; exact ES | exact Hx]).
      destruct (Ht x HxS) as [y [Hy HyF]]. exists y. split; [exact Hy | eapply set_mem_eq_r; [apply EFG; exact HxS | exact HyF]].
  - apply (set_mem_function _ _ _ HG) in Hg as [Hp [Ht Hu]]. apply (set_mem_function _ _ _ HF). split; [| split; [| exact Hu]].
    + intros p Hpg. destruct (Hp p Hpg) as [x [y [Hx [Hy E]]]]. exists x, y.
      split; [eapply set_mem_eq_r; [apply set_eq_sym; exact ES | exact Hx] |
              split; [eapply set_mem_eq_r; [apply set_eq_sym; apply EFG'; exact Hx | exact Hy] | exact E]].
    + intros x Hx. destruct (Ht x (set_mem_eq_r _ _ _ ES Hx)) as [y [Hy HyG]]. exists y.
      split; [exact Hy | eapply set_mem_eq_r; [apply set_eq_sym; apply EFG; exact Hx | exact HyG]].
Qed.

(** A function set grows with its codomains. *)
Lemma function_set_mono : forall S F F', respects_set_eq_fun F -> respects_set_eq_fun F' ->
    (forall x, set_mem x S -> set_sub (F x) (F' x)) -> set_sub (function_set S F) (function_set S F').
Proof.
  intros S F F' HF HF' Hsub g Hg. apply (set_mem_function _ _ _ HF) in Hg as [Hp [Ht Hu]].
  apply (set_mem_function _ _ _ HF'). split; [| split; [| exact Hu]].
  - intros p Hpg. destruct (Hp p Hpg) as [x [y [Hx [Hy E]]]]. exists x, y. split; [exact Hx | split; [apply Hsub; assumption | exact E]].
  - intros x Hx. destruct (Ht x Hx) as [y [Hy HyF]]. exists y. split; [exact Hy | apply Hsub; assumption].
Qed.

Definition respects_on (S : aczel_set) (F : aczel_set -> aczel_set) : Prop :=
  forall x y, set_mem x S -> set_eq x y -> set_eq (F x) (F y).

(** The restriction of [F] to [S]: at [x], the union of the [F]s of the
    members of [S] equal to [x]. *)
Definition restrict_fun (S : aczel_set) (F : aczel_set -> aczel_set) (x : aczel_set) : aczel_set :=
  union_set (family_set {a : aczel_index S | set_eq (aczel_element S a) x} (fun p => F (aczel_element S (proj1_sig p)))).

Lemma set_mem_restrict_fun : forall S F x z, set_mem z (restrict_fun S F x) <->
    exists a, set_eq (aczel_element S a) x /\ set_mem z (F (aczel_element S a)).
Proof.
  intros. unfold restrict_fun. rewrite set_mem_union. split.
  - intros [w [Hw Hz]]. apply set_mem_family in Hw as [[a Ha] E]. exists a. split; [exact Ha | eapply set_mem_eq_r; eauto].
  - intros [a [Ha Hz]]. exists (F (aczel_element S a)). split; [apply set_mem_family; exists (exist _ a Ha); apply set_eq_refl | exact Hz].
Qed.

Lemma restrict_fun_resp : forall S F, respects_set_eq_fun (restrict_fun S F).
Proof.
  intros S F x y E. apply set_eq_intro; intros z Hz; apply set_mem_restrict_fun in Hz as [a [Ha Hz]];
    apply set_mem_restrict_fun; exists a; split; try exact Hz;
    [eapply set_eq_trans; [exact Ha | exact E] | eapply set_eq_trans; [exact Ha | apply set_eq_sym; exact E]].
Qed.

Lemma restrict_fun_agree : forall S F x, respects_on S F -> set_mem x S -> set_eq (restrict_fun S F x) (F x).
Proof.
  intros S F x HF Hx. apply set_eq_intro; intros z Hz.
  - apply set_mem_restrict_fun in Hz as [a [Ha Hz]].
    eapply set_mem_eq_r; [apply HF; [exists a; apply set_eq_refl | exact Ha] | exact Hz].
  - destruct Hx as [a Ha]. apply set_mem_restrict_fun. exists a. split; [apply set_eq_sym; exact Ha |].
    eapply set_mem_eq_r; [apply HF; [exists a; exact Ha | exact Ha] | exact Hz].
Qed.

(** Families of pointwise equal sets are equal. *)
Lemma family_set_pointwise : forall A f g, (forall a : A, set_eq (f a) (g a)) -> set_eq (family_set A f) (family_set A g).
Proof.
  intros A f g H. apply set_eq_intro; intros z Hz; apply set_mem_family in Hz as [a E]; apply set_mem_family; exists a;
    [eapply set_eq_trans; [exact E | apply H] | eapply set_eq_trans; [exact E | apply set_eq_sym; apply H]].
Qed.

(** A function crossing equal arguments of [S] to equal values. *)
Definition respects_across (S : aczel_set) (F G : aczel_set -> aczel_set) : Prop :=
  forall x x', set_mem x S -> set_eq x x' -> set_eq (F x) (G x').

Lemma respects_across_left : forall S F G, respects_across S F G -> respects_on S F.
Proof.
  intros S F G H x y Hx E. eapply set_eq_trans; [apply H; [exact Hx | exact E] |].
  apply set_eq_sym. apply H; [eapply set_mem_eq_l; [exact E | exact Hx] | apply set_eq_refl].
Qed.

Lemma respects_across_right : forall S S' F G, set_eq S S' -> respects_across S F G -> respects_on S' G.
Proof.
  intros S S' F G ES H x y Hx E. assert (HxS : set_mem x S) by (eapply set_mem_eq_r; [apply set_eq_sym; exact ES | exact Hx]).
  eapply set_eq_trans; [apply set_eq_sym; apply H; [exact HxS | apply set_eq_refl] |]. apply H; [exact HxS | exact E].
Qed.

Lemma graph_set_restrict : forall S F, respects_on S F -> set_eq (graph_set S F) (graph_set S (restrict_fun S F)).
Proof.
  intros S F HF. apply family_set_pointwise. intros a. apply ordered_pair_resp; [apply set_eq_refl |].
  apply set_eq_sym. apply restrict_fun_agree; [exact HF | exists a; apply set_eq_refl].
Qed.

Lemma graph_set_resp_on : forall S S' F G, set_eq S S' -> respects_across S F G -> set_eq (graph_set S F) (graph_set S' G).
Proof.
  intros S S' F G ES H. pose proof (respects_across_left _ _ _ H) as HF. pose proof (respects_across_right _ _ _ _ ES H) as HG.
  eapply set_eq_trans; [apply graph_set_restrict; exact HF |].
  eapply set_eq_trans; [| apply set_eq_sym; apply graph_set_restrict; exact HG].
  apply graph_set_resp; [apply restrict_fun_resp | apply restrict_fun_resp | exact ES |].
  intros x Hx. eapply set_eq_trans; [apply restrict_fun_agree; [exact HF | exact Hx] |].
  eapply set_eq_trans; [apply H; [exact Hx | apply set_eq_refl] |].
  apply set_eq_sym. apply restrict_fun_agree; [exact HG | eapply set_mem_eq_r; [exact ES | exact Hx]].
Qed.

Lemma function_set_restrict : forall S F, respects_on S F -> set_eq (function_set S F) (function_set S (restrict_fun S F)).
Proof.
  intros S F HF. unfold function_set.
  apply separation_set_resp; [apply is_dependent_function_resp | apply is_dependent_function_resp | |].
  - apply power_set_resp. apply product_set_resp; [apply set_eq_refl |]. unfold indexed_union_set. apply union_set_resp.
    apply family_set_pointwise. intros a. apply set_eq_sym. apply restrict_fun_agree; [exact HF | exists a; apply set_eq_refl].
  - intros g _. unfold is_dependent_function. split; intros [Ht Hu]; split; try exact Hu; intros x Hx; destruct (Ht x Hx) as [y [Hy HyF]];
      exists y; split; try exact Hy; eapply set_mem_eq_r; try exact HyF;
      [apply set_eq_sym; apply restrict_fun_agree | apply restrict_fun_agree]; assumption.
Qed.

Lemma function_set_resp_on : forall S S' F G, set_eq S S' -> respects_across S F G ->
    set_eq (function_set S F) (function_set S' G).
Proof.
  intros S S' F G ES H. pose proof (respects_across_left _ _ _ H) as HF. pose proof (respects_across_right _ _ _ _ ES H) as HG.
  eapply set_eq_trans; [apply function_set_restrict; exact HF |].
  eapply set_eq_trans; [| apply set_eq_sym; apply function_set_restrict; exact HG].
  apply function_set_resp; [apply restrict_fun_resp | apply restrict_fun_resp | exact ES |].
  intros x Hx. eapply set_eq_trans; [apply restrict_fun_agree; [exact HF | exact Hx] |].
  eapply set_eq_trans; [apply H; [exact Hx | apply set_eq_refl] |].
  apply set_eq_sym. apply restrict_fun_agree; [exact HG | eapply set_mem_eq_r; [exact ES | exact Hx]].
Qed.

Lemma graph_set_function_on : forall S F G, respects_on S F -> respects_on S G ->
    (forall x, set_mem x S -> set_mem (G x) (F x)) -> set_mem (graph_set S G) (function_set S F).
Proof.
  intros S F G HF HG H. eapply set_mem_eq_l; [apply set_eq_sym; apply graph_set_restrict; exact HG |].
  eapply set_mem_eq_r; [apply set_eq_sym; apply function_set_restrict; exact HF |].
  apply graph_set_function; [apply restrict_fun_resp | apply restrict_fun_resp |]. intros x Hx.
  eapply set_mem_eq_l; [apply set_eq_sym; apply restrict_fun_agree; [exact HG | exact Hx] |].
  eapply set_mem_eq_r; [apply set_eq_sym; apply restrict_fun_agree; [exact HF | exact Hx] | apply H; exact Hx].
Qed.

Lemma set_apply_graph_on : forall S F x, respects_on S F -> set_mem x S -> set_eq (set_apply (graph_set S F) x) (F x).
Proof.
  intros S F x HF Hx. eapply set_eq_trans; [apply set_apply_resp; [apply graph_set_restrict; exact HF | apply set_eq_refl] |].
  eapply set_eq_trans; [apply set_apply_graph; [apply restrict_fun_resp | exact Hx] |]. apply restrict_fun_agree; assumption.
Qed.

Lemma function_set_mono_on : forall S F F', respects_on S F -> respects_on S F' ->
    (forall x, set_mem x S -> set_sub (F x) (F' x)) -> set_sub (function_set S F) (function_set S F').
Proof.
  intros S F F' HF HF' H g Hg. eapply set_mem_eq_r in Hg; [| apply function_set_restrict; exact HF].
  eapply set_mem_eq_r; [apply set_eq_sym; apply function_set_restrict; exact HF' |].
  revert g Hg. apply function_set_mono; [apply restrict_fun_resp | apply restrict_fun_resp |]. intros x Hx z Hz.
  eapply set_mem_eq_r; [apply set_eq_sym; apply restrict_fun_agree; [exact HF' | exact Hx] |]. apply H; [exact Hx |].
  eapply set_mem_eq_r; [apply restrict_fun_agree; [exact HF | exact Hx] | exact Hz].
Qed.

(** A dependent function is the graph of its application. *)
Lemma function_set_graph_on : forall g S F, respects_on S F -> set_mem g (function_set S F) -> set_eq g (graph_set S (set_apply g)).
Proof.
  intros g S F HF Hg. eapply set_mem_eq_r in Hg; [| apply function_set_restrict; exact HF].
  assert (Hr : respects_set_eq_fun (set_apply g)) by (intros x y E; apply set_apply_resp; [apply set_eq_refl | exact E]).
  apply (function_set_ext _ _ _ _ (restrict_fun_resp S F) Hg).
  - apply graph_set_function; [apply restrict_fun_resp | exact Hr |]. intros x Hx.
    apply (function_set_apply _ _ _ _ (restrict_fun_resp S F) Hg Hx).
  - intros x Hx. apply set_eq_sym. apply set_apply_graph; [exact Hr | exact Hx].
Qed.

Lemma function_set_apply_on : forall g S F x, respects_on S F -> set_mem g (function_set S F) -> set_mem x S ->
    set_mem (set_apply g x) (F x).
Proof.
  intros g S F x HF Hg Hx. eapply set_mem_eq_r; [apply restrict_fun_agree; [exact HF | exact Hx] |].
  apply (function_set_apply g S (restrict_fun S F) x (restrict_fun_resp S F)); [| exact Hx].
  eapply set_mem_eq_r; [apply function_set_restrict; exact HF | exact Hg].
Qed.
