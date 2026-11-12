(** * Grothendieck Universes

    A universe of sets ([grothendieck]): transitive, containing ω, and
    closed under pairs, unions, power sets, replacement along functions
    that respect equality, and W-sets (a bound for the trees of a family).
    Rocq cannot build one without choice (replacement picks
    representatives), so the universes of the set model are a hypothesis
    ([Tower.v]).  This file states the record and derives the closure
    properties the model uses. *)

From Mctt.Core.SetModel.Sets Require Export Codes.

(** The image of [S] under [F]. *)
Definition replacement_set (S : aczel_set) (F : aczel_set -> aczel_set) : aczel_set :=
  family_set (aczel_index S) (fun a => F (aczel_element S a)).

Lemma set_mem_replacement : forall z S F, respects_set_eq_fun F ->
    (set_mem z (replacement_set S F) <-> exists x, set_mem x S /\ set_eq z (F x)).
Proof.
  intros z S F HF. split.
  - intros [a H]. exists (aczel_element S a). split; [exists a; apply set_eq_refl | exact H].
  - intros [x [[a Ha] H]]. exists a. cbn. eapply set_eq_trans; [exact H | apply HF; exact Ha].
Qed.

(** [U] is a universe of sets: a Grothendieck universe containing ω,
    closed under W-sets. *)
Record grothendieck (U : aczel_set) : Prop := mk_grothendieck
  { (** Every element of a member is a member *)
    grothendieck_transitive : forall x y, set_mem x U -> set_mem y x -> set_mem y U
    (** The natural numbers are a member *)
  ; grothendieck_omega : set_mem omega_set U
    (** The pair of two members is a member *)
  ; grothendieck_pair : forall x y, set_mem x U -> set_mem y U -> set_mem (unordered_pair_set x y) U
    (** The union of a member is a member *)
  ; grothendieck_union : forall x, set_mem x U -> set_mem (union_set x) U
    (** The power set of a member is a member *)
  ; grothendieck_power : forall x, set_mem x U -> set_mem (power_set x) U
    (** Replacement along a function on sets that respects equality: the
        image of a member is a member when every value is *)
  ; grothendieck_replacement : forall x, set_mem x U -> forall F, respects_set_eq_fun F ->
      (forall y, set_mem y x -> set_mem (F y) U) -> set_mem (replacement_set x F) U
    (** A W-bound: for a family of members [F] over a member [x], some
        member [T] is closed under forming the tree [ordered_pair a g] of a
        shape [a] of [x] and a function [g] from the positions [F a] into
        [T] *)
  ; grothendieck_wbound : forall x, set_mem x U -> forall F, respects_set_eq_fun F ->
      (forall a, set_mem a x -> set_mem (F a) U) ->
      exists T, set_mem T U /\
        (forall a g, set_mem a x -> set_mem g (function_set (F a) (fun _ => T)) -> set_mem (ordered_pair a g) T) }.

Section Closure.
  Variable U : aczel_set.
  Hypothesis HU : grothendieck U.

Lemma grothendieck_eq : forall x y, set_eq x y -> set_mem x U -> set_mem y U.
Proof. intros x y E H. eapply set_mem_eq_l; [exact E | exact H]. Qed.

Lemma grothendieck_sub : forall x y, set_mem x U -> set_sub y x -> set_mem y U.
Proof.
  intros x y Hx Hs. apply (grothendieck_transitive _ HU (power_set x)); [apply grothendieck_power; auto | apply set_mem_power; exact Hs].
Qed.

Lemma grothendieck_empty : set_mem empty_set U.
Proof.
  apply (grothendieck_transitive _ HU omega_set); [apply grothendieck_omega; exact HU |]. exists 0. apply set_eq_refl.
Qed.

Lemma grothendieck_numeral : forall n, set_mem (numeral_set n) U.
Proof.
  intros n. apply (grothendieck_transitive _ HU omega_set); [apply grothendieck_omega; exact HU | exists n; apply set_eq_refl].
Qed.

Lemma grothendieck_singleton : forall x, set_mem x U -> set_mem (singleton_set x) U.
Proof.
  intros x H. eapply set_mem_eq_l; [| apply (grothendieck_pair _ HU x x H H)].
  apply set_eq_intro; intros z Hz.
  - apply set_mem_unordered_pair in Hz as [Hz | Hz]; apply set_mem_singleton; exact Hz.
  - apply set_mem_singleton in Hz. apply set_mem_unordered_pair. left. exact Hz.
Qed.

Lemma grothendieck_ordered_pair : forall x y, set_mem x U -> set_mem y U -> set_mem (ordered_pair x y) U.
Proof. intros. unfold ordered_pair. apply (grothendieck_pair _ HU); [apply grothendieck_singleton | apply (grothendieck_pair _ HU)]; auto. Qed.

Lemma grothendieck_separation : forall X P, set_mem X U -> set_mem (separation_set X P) U.
Proof. intros X P H. apply (grothendieck_sub X); [exact H |]. intros z [[a Pa] Hz]. exists a. exact Hz. Qed.

Lemma grothendieck_successor : forall x, set_mem x U -> set_mem (successor_set x) U.
Proof. intros. unfold successor_set. apply (grothendieck_union _ HU). apply (grothendieck_pair _ HU); [| apply grothendieck_singleton]; auto. Qed.

Lemma grothendieck_pair_first : forall p, set_mem p U -> set_mem (pair_first p) U.
Proof. intros. unfold pair_first. apply (grothendieck_union _ HU). apply grothendieck_separation. apply (grothendieck_union _ HU). auto. Qed.

Lemma grothendieck_pair_second : forall p, set_mem p U -> set_mem (pair_second p) U.
Proof. intros. unfold pair_second. apply (grothendieck_union _ HU). apply grothendieck_separation. apply (grothendieck_union _ HU). auto. Qed.

Lemma grothendieck_type_code : forall t d c, set_mem d U -> set_mem c U -> set_mem (type_code t d c) U.
Proof. intros. unfold type_code. apply grothendieck_ordered_pair; [apply grothendieck_numeral | apply grothendieck_ordered_pair]; auto. Qed.

Lemma grothendieck_code_carrier : forall C, set_mem C U -> set_mem (code_carrier C) U.
Proof. intros. unfold code_carrier. apply grothendieck_pair_second. apply grothendieck_pair_second. auto. Qed.

(** Products, as a union of replacements. *)
Lemma grothendieck_product : forall S T, set_mem S U -> set_mem T U -> set_mem (product_set S T) U.
Proof.
  intros S T HS HT.
  assert (Hk : forall x, respects_set_eq_fun (fun y => ordered_pair x y))
    by (intros x y y' E; apply ordered_pair_resp; [apply set_eq_refl | exact E]).
  assert (HF : respects_set_eq_fun (fun x => replacement_set T (fun y => ordered_pair x y))).
  { intros x x' E. apply set_eq_intro; intros z Hz.
    - apply (set_mem_replacement _ _ _ (Hk x)) in Hz as [y [Hy Ez]]. apply (set_mem_replacement _ _ _ (Hk x')). exists y.
      split; [exact Hy | eapply set_eq_trans; [exact Ez | apply ordered_pair_resp; [exact E | apply set_eq_refl]]].
    - apply (set_mem_replacement _ _ _ (Hk x')) in Hz as [y [Hy Ez]]. apply (set_mem_replacement _ _ _ (Hk x)). exists y.
      split; [exact Hy | eapply set_eq_trans; [exact Ez | apply ordered_pair_resp; [apply set_eq_sym; exact E | apply set_eq_refl]]]. }
  eapply set_mem_eq_l; [| apply (grothendieck_union _ HU); apply (grothendieck_replacement _ HU S HS _ HF);
      intros x Hx; apply (grothendieck_replacement _ HU T HT _ (Hk x));
      intros y Hy; apply grothendieck_ordered_pair; [apply (grothendieck_transitive _ HU S); auto | apply (grothendieck_transitive _ HU T); auto]].
  apply set_eq_intro; intros z Hz.
  - apply set_mem_union in Hz as [w [Hw Hz]]. apply (set_mem_replacement _ _ _ HF) in Hw as [x [Hx Ew]].
    eapply set_mem_eq_r in Hz; [| exact Ew]. apply (set_mem_replacement _ _ _ (Hk x)) in Hz as [y [Hy Ez]].
    apply set_mem_product. exists x, y. auto.
  - apply set_mem_product in Hz as [x [y [Hx [Hy Ez]]]]. apply set_mem_union. exists (replacement_set T (fun y => ordered_pair x y)).
    split; [apply (set_mem_replacement _ _ _ HF); exists x; split; [exact Hx | apply set_eq_refl] |].
    apply (set_mem_replacement _ _ _ (Hk x)). exists y. auto.
Qed.

Lemma grothendieck_graph : forall S F, respects_set_eq_fun F -> set_mem S U -> (forall x, set_mem x S -> set_mem (F x) U) ->
    set_mem (graph_set S F) U.
Proof.
  intros S F HF HS HFx.
  assert (HK : respects_set_eq_fun (fun x => ordered_pair x (F x))) by (intros x y E; apply ordered_pair_resp; [exact E | apply HF; exact E]).
  apply (grothendieck_replacement _ HU S HS _ HK). intros x Hx. apply grothendieck_ordered_pair; [apply (grothendieck_transitive _ HU S); auto | auto].
Qed.

Lemma grothendieck_indexed_union : forall S F, respects_set_eq_fun F -> set_mem S U -> (forall x, set_mem x S -> set_mem (F x) U) ->
    set_mem (indexed_union_set S F) U.
Proof. intros. unfold indexed_union_set. apply (grothendieck_union _ HU). apply (grothendieck_replacement _ HU S); auto. Qed.

Lemma grothendieck_function : forall S F, respects_set_eq_fun F -> set_mem S U -> (forall x, set_mem x S -> set_mem (F x) U) ->
    set_mem (function_set S F) U.
Proof.
  intros. unfold function_set. apply grothendieck_separation. apply (grothendieck_power _ HU).
  apply grothendieck_product; [auto | apply grothendieck_indexed_union; auto].
Qed.

Lemma grothendieck_sigma : forall S F, respects_set_eq_fun F -> set_mem S U -> (forall x, set_mem x S -> set_mem (F x) U) ->
    set_mem (sigma_set S F) U.
Proof.
  intros S F HF HS HFx. apply (grothendieck_sub (product_set S (indexed_union_set S F))); [apply grothendieck_product; [auto | apply grothendieck_indexed_union; auto] |].
  intros z Hz. apply (set_mem_sigma _ _ _ HF) in Hz as [x [y [Hx [Hy Ez]]]].
  apply set_mem_product. exists x, y. split; [exact Hx | split; [| exact Ez]].
  apply (set_mem_indexed_union _ _ _ HF). exists x. auto.
Qed.

Lemma grothendieck_truth : forall P, set_mem (truth_set P) U.
Proof.
  intros P. apply (grothendieck_sub (singleton_set empty_set)); [apply grothendieck_singleton; exact grothendieck_empty |].
  intros z Hz. apply set_mem_truth in Hz as [_ Hz]. apply set_mem_singleton. exact Hz.
Qed.

Lemma grothendieck_prop_code : forall P, set_mem (prop_code P) U.
Proof. intros. apply grothendieck_type_code; [exact grothendieck_empty | apply grothendieck_truth]. Qed.

(** The carrier of [Prop]: the codes of propositions, as a replacement
    over the subsets of [{∅}]. *)
Lemma grothendieck_prop_codes : set_mem prop_codes_set U.
Proof.
  pose proof grothendieck_empty as Hemp.
  assert (HF : respects_set_eq_fun (fun x => type_code prop_tag empty_set x))
    by (intros x y E; apply type_code_resp; [apply set_eq_refl | exact E]).
  assert (Hp : set_mem (power_set (singleton_set empty_set)) U) by (apply (grothendieck_power _ HU); apply grothendieck_singleton; exact Hemp).
  eapply set_mem_eq_l; [| apply (grothendieck_replacement _ HU _ Hp _ HF);
      intros x Hx; apply grothendieck_type_code; [exact Hemp | apply (grothendieck_transitive _ HU _ _ Hp Hx)]].
  apply set_eq_intro; intros z Hz.
  - apply (set_mem_replacement _ _ _ HF) in Hz as [x [Hx Ez]]. apply set_mem_power in Hx.
    exists (set_mem empty_set x). cbn. eapply set_eq_trans; [exact Ez |]. unfold prop_code. apply type_code_resp; [apply set_eq_refl |].
    apply set_eq_intro; intros w Hw.
    + pose proof (Hx _ Hw) as Hw'. apply set_mem_singleton in Hw'. apply set_mem_truth. split; [eapply set_mem_eq_l; eauto | exact Hw'].
    + apply set_mem_truth in Hw as [He Hw]. eapply set_mem_eq_l; [apply set_eq_sym; exact Hw | exact He].
  - destruct Hz as [P Ez]. cbn in Ez. apply (set_mem_replacement _ _ _ HF). exists (truth_set P). split; [| exact Ez].
    apply set_mem_power. intros w Hw. apply set_mem_truth in Hw as [_ Hw]. apply set_mem_singleton. exact Hw.
Qed.

(** A family indexed by the natural numbers, by replacement over ω. *)
Lemma grothendieck_nat_family : forall (f : nat -> aczel_set), (forall n, set_mem (f n) U) -> set_mem (family_set nat f) U.
Proof.
  intros f Hf.
  set (F := fun y => union_set (family_set {n : nat | set_eq y (numeral_set n)} (fun p => f (proj1_sig p)))).
  assert (HF : respects_set_eq_fun F).
  { intros y y' E. apply set_eq_intro; intros z Hz; apply set_mem_union in Hz as [w [[[n Hn] Hw] Hz]]; apply set_mem_union.
    - exists (f n). split; [exists (exist _ n (set_eq_trans _ _ _ (set_eq_sym _ _ E) Hn)); apply set_eq_refl | eapply set_mem_eq_r; eauto].
    - exists (f n). split; [exists (exist _ n (set_eq_trans _ _ _ E Hn)); apply set_eq_refl | eapply set_mem_eq_r; eauto]. }
  assert (FN : forall n, set_eq (F (numeral_set n)) (f n)).
  { intros n. apply set_eq_intro; intros z Hz.
    - apply set_mem_union in Hz as [w [[[m Hm] Hw] Hz]]. cbn in Hw. apply numeral_set_inj in Hm. subst m. eapply set_mem_eq_r; eauto.
    - apply set_mem_union. exists (f n). split; [exists (exist _ n (set_eq_refl _)); apply set_eq_refl | exact Hz]. }
  eapply set_mem_eq_l; [| apply (grothendieck_replacement _ HU omega_set (grothendieck_omega _ HU) F HF)].
  - apply set_eq_intro; intros z Hz.
    + apply (set_mem_replacement _ _ _ HF) in Hz as [y [[n Hy] Ez]]. exists n. cbn. eapply set_eq_trans; [exact Ez |].
      eapply set_eq_trans; [apply HF; exact Hy | apply FN].
    + destruct Hz as [n Hz]. apply (set_mem_replacement _ _ _ HF). exists (numeral_set n). split; [exists n; apply set_eq_refl |].
      eapply set_eq_trans; [exact Hz | apply set_eq_sym; apply FN].
  - intros y [n Hy]. eapply set_mem_eq_l; [apply set_eq_sym; eapply set_eq_trans; [apply HF; exact Hy | apply FN] | apply Hf].
Qed.

End Closure.
