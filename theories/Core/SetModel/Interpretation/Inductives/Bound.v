(** * The Carriers Are Members of the Universe

    The carriers of a group ([Carriers.v]), drawn from the universe set
    [U], are subsets of [U]; this file shows they are members of it.  Each
    element has a construction tree: a node of the shape (member,
    constructor, non-uniform parameters, non-recursive arguments) whose
    children, at the positions (recursive argument, domain points), are
    the trees of the recursive arguments' values there.  The trees are a
    member of [U] by the W-bound ([grothendieck_tree_set]), and an
    element is the decoding ([tree_decodes]) of a tree, so the carriers
    lie in the image of the trees, a member of [U] by replacement. *)

From Stdlib Require Import String List Lia.
From Mctt.Core.SetModel.Interpretation.Inductives Require Export Carriers.
Import ListNotations.

Section Bound.
  Variable G : set_group.
  Variable us : list aczel_set.

  Let nuniform : nat := List.length (set_group_uniform_types G).

(** ** Telescopes of Values *)

(** The coded lists of points of the [domains], each read off the values
    [pre] and the points before it, after the points [points]. *)
Fixpoint domains_set (domains : list (list aczel_set -> aczel_set)) (pre points : list aczel_set) : aczel_set :=
  match domains with
  | nil => singleton_set (list_code points)
  | d :: ds => union_set (replacement_set (code_carrier (d (pre ++ points))) (fun b => domains_set ds pre (points ++ [b])))
  end.

(** The coded lists of the values of the [types], each read off the values
    [pre] and those before it, after the values [vals]. *)
Fixpoint telescope_set (types : list (list aczel_set -> aczel_set)) (pre vals : list aczel_set) : aczel_set :=
  match types with
  | nil => singleton_set (list_code vals)
  | t :: ts => union_set (replacement_set (code_carrier (t (pre ++ vals))) (fun a => telescope_set ts pre (vals ++ [a])))
  end.

(** The coded lists of the non-recursive arguments of [gs], after the
    values [pre], the earlier ones [vals]; a recursive argument is seen
    as the empty set by the arguments after it. *)
Fixpoint plain_arguments_set (gs : list set_argument) (pre vals : list aczel_set) : aczel_set :=
  match gs with
  | nil => singleton_set (list_code vals)
  | set_argument_plain _ t :: gs' =>
      union_set (replacement_set (code_carrier (t pre)) (fun a => plain_arguments_set gs' (pre ++ [a]) (vals ++ [a])))
  | set_argument_recursive _ _ _ _ _ :: gs' => plain_arguments_set gs' (pre ++ [empty_set]) vals
  end.

(** ** Shapes, Positions and Trees *)

(** The shape of a node: the member [k], its constructor [i], the
    non-uniform parameters [ns], the non-recursive arguments [pvals]. *)
Definition tree_shape (k i : nat) (ns pvals : list aczel_set) : aczel_set :=
  list_code [numeral_set k; numeral_set i; list_code ns; list_code pvals].

(** The position of the recursive argument [j] at the domain points
    [points]. *)
Definition tree_position (j : nat) (points : list aczel_set) : aczel_set := ordered_pair (numeral_set j) (list_code points).

(** The positions of the recursive arguments of [gs] numbered from [j],
    after the values [pre], the non-recursive arguments being [pvals]. *)
Fixpoint argument_positions (gs : list set_argument) (pvals pre : list aczel_set) (j : nat) : aczel_set :=
  match gs with
  | nil => empty_set
  | set_argument_plain _ _ :: gs' =>
      match pvals with
      | p :: pvals' => argument_positions gs' pvals' (pre ++ [p]) (S j)
      | nil => empty_set
      end
  | set_argument_recursive _ ds _ _ _ :: gs' =>
      union_set (unordered_pair_set (replacement_set (domains_set ds pre nil) (fun pts => ordered_pair (numeral_set j) pts))
                                    (argument_positions gs' pvals (pre ++ [empty_set]) (S j)))
  end.

(** The number of non-recursive arguments. *)
Fixpoint plain_count (gs : list set_argument) : nat :=
  match gs with
  | nil => 0
  | set_argument_plain _ _ :: gs' => S (plain_count gs')
  | set_argument_recursive _ _ _ _ _ :: gs' => plain_count gs'
  end.

(** The members and constructors of the group, as index pairs. *)
Definition constructor_index (k i : nat) : Prop :=
  exists Mk cs, List.nth_error (set_group_members G) k = Some Mk /\ List.nth_error (set_member_constructors Mk) i = Some cs.

(** The components of a shape. *)
Definition shape_member (a : aczel_set) : aczel_set := pair_first a.
Definition shape_constructor (a : aczel_set) : aczel_set := pair_first (pair_second a).
Definition shape_nparams (a : aczel_set) : aczel_set := pair_first (pair_second (pair_second a)).
Definition shape_plain (a : aczel_set) : aczel_set := pair_first (pair_second (pair_second (pair_second a))).

(** The positions of a node of the shape [a]: those of its constructor,
    read off its components. *)
Definition shape_positions (a : aczel_set) : aczel_set :=
  union_set (family_set {ki : nat * nat | constructor_index (fst ki) (snd ki)}
    (fun ki =>
       match List.nth_error (set_group_members G) (fst (proj1_sig ki)) with
       | Some Mk =>
           match List.nth_error (set_member_constructors Mk) (snd (proj1_sig ki)) with
           | Some cs =>
               let gs := set_constructor_arguments cs in
               cond (set_eq (shape_member a) (numeral_set (fst (proj1_sig ki))) /\
                     set_eq (shape_constructor a) (numeral_set (snd (proj1_sig ki))))
                 (argument_positions gs (list_decode (plain_count gs) (shape_plain a))
                    (us ++ list_decode (List.length (set_member_nparam_types Mk)) (shape_nparams a)) 0)
           | None => empty_set
           end
       | None => empty_set
       end)).

(** The shapes of the nodes. *)
Definition tree_shapes : aczel_set :=
  union_set (family_set {ki : nat * nat | constructor_index (fst ki) (snd ki)}
    (fun ki =>
       match List.nth_error (set_group_members G) (fst (proj1_sig ki)) with
       | Some Mk =>
           match List.nth_error (set_member_constructors Mk) (snd (proj1_sig ki)) with
           | Some cs =>
               union_set (replacement_set (telescope_set (set_member_nparam_types Mk) us nil)
                 (fun nsc => replacement_set
                    (plain_arguments_set (set_constructor_arguments cs) (us ++ list_decode (List.length (set_member_nparam_types Mk)) nsc) nil)
                    (fun pc => list_code [numeral_set (fst (proj1_sig ki)); numeral_set (snd (proj1_sig ki)); nsc; pc])))
           | None => empty_set
           end
       | None => empty_set
       end)).

(** ** Decoding *)

(** The values of the arguments [gs] from the non-recursive ones [pvals]
    and the recursive ones [rs], in order. *)
Fixpoint interleave_arguments (gs : list set_argument) (pvals rs : list aczel_set) : list aczel_set :=
  match gs with
  | nil => nil
  | set_argument_plain _ _ :: gs' =>
      match pvals with
      | p :: pvals' => p :: interleave_arguments gs' pvals' rs
      | nil => nil
      end
  | set_argument_recursive _ _ _ _ _ :: gs' =>
      match rs with
      | r :: rs' => r :: interleave_arguments gs' pvals rs'
      | nil => nil
      end
  end.

(** [tree_decodes k ns t v]: the tree [t], of the member [k] at [ns],
    decodes to the element [v]. *)
Inductive tree_decodes : nat -> list aczel_set -> aczel_set -> aczel_set -> Prop :=
(** A node: its children decode to the recursive arguments *)
| tree_decodes_node : forall k ns Mk i cs pvals g rs t v,
    List.nth_error (set_group_members G) k = Some Mk ->
    List.nth_error (set_member_constructors Mk) i = Some cs ->
    set_eq t (ordered_pair (tree_shape k i ns pvals) g) ->
    List.length pvals = plain_count (set_constructor_arguments cs) ->
    is_function_on (argument_positions (set_constructor_arguments cs) pvals (us ++ ns) 0) g ->
    children_decode g (set_constructor_arguments cs) pvals (us ++ ns) 0 rs ->
    set_eq v (constructed_element Mk cs ns (interleave_arguments (set_constructor_arguments cs) pvals rs)) ->
    tree_decodes k ns t v
(** [children_decode g gs pvals pre j rs]: the children [g] give the
    recursive arguments of [gs], numbered from [j], the values [rs] *)
with children_decode : aczel_set -> list set_argument -> list aczel_set -> list aczel_set -> nat -> list aczel_set -> Prop :=
(** No argument *)
| children_decode_nil : forall g pvals pre j, children_decode g nil pvals pre j nil
(** A non-recursive argument *)
| children_decode_plain : forall g κ t gs p pvals pre j rs,
    children_decode g gs pvals (pre ++ [p]) (S j) rs ->
    children_decode g (set_argument_plain κ t :: gs) (p :: pvals) pre j rs
(** A recursive argument: its value at every domain point the decoding of
    the child there *)
| children_decode_recursive : forall g type ds target tparams ls gs pvals pre j r rs,
    child_decodes g j ds target tparams pre nil r ->
    children_decode g gs pvals (pre ++ [empty_set]) (S j) rs ->
    children_decode g (set_argument_recursive type ds target tparams ls :: gs) pvals pre j (r :: rs)
(** [child_decodes g j ds target tparams pre points r]: over the domains
    [ds] left after the points [points], the recursive argument [j] has
    the value [r] *)
with child_decodes : aczel_set -> nat -> list (list aczel_set -> aczel_set) -> nat -> (list aczel_set -> list aczel_set) ->
    list aczel_set -> list aczel_set -> aczel_set -> Prop :=
(** At the end: the child at the position decodes to it *)
| child_decodes_end : forall g j target tparams pre points r,
    tree_decodes target (List.skipn nuniform (tparams (pre ++ points))) (set_apply g (tree_position j points)) r ->
    child_decodes g j nil target tparams pre points r
(** Through a domain: a function, at each point the value there *)
| child_decodes_domain : forall g j d ds target tparams pre points r,
    is_function_on (code_carrier (d (pre ++ points))) r ->
    (forall b, set_mem b (code_carrier (d (pre ++ points))) ->
       child_decodes g j ds target tparams pre (points ++ [b]) (set_apply r b)) ->
    child_decodes g j (d :: ds) target tparams pre points r.

Scheme tree_decodes_mut_ind := Minimality for tree_decodes Sort Prop
with children_decode_mut_ind := Minimality for children_decode Sort Prop
with child_decodes_mut_ind := Minimality for child_decodes Sort Prop.
Combined Scheme tree_decodes_combined_ind from tree_decodes_mut_ind, children_decode_mut_ind, child_decodes_mut_ind.

(** ** Respect of Equality *)

Lemma replacement_set_resp : forall S S' F F', respects_set_eq_fun F -> respects_set_eq_fun F' -> set_eq S S' ->
    agree_on S F F' -> set_eq (replacement_set S F) (replacement_set S' F').
Proof.
  intros * HF HF' ES EF. apply set_eq_intro; intros z Hz.
  - apply (set_mem_replacement _ _ _ HF) in Hz as [x [Hx Ez]]. apply (set_mem_replacement _ _ _ HF'). exists x.
    split; [eapply set_mem_eq_r; [exact ES | exact Hx] | eapply set_eq_trans; [exact Ez | apply EF; exact Hx]].
  - apply (set_mem_replacement _ _ _ HF') in Hz as [x [Hx Ez]].
    assert (HxS : set_mem x S) by (eapply set_mem_eq_r; [apply set_eq_sym; exact ES | exact Hx]).
    apply (set_mem_replacement _ _ _ HF). exists x.
    split; [exact HxS | eapply set_eq_trans; [exact Ez | apply set_eq_sym; apply EF; exact HxS]].
Qed.

Lemma domains_set_resp : forall ds, Forall list_function_respects ds ->
    forall pre pre' points points', list_set_eq pre pre' -> list_set_eq points points' ->
    set_eq (domains_set ds pre points) (domains_set ds pre' points').
Proof.
  intros ds Hds. induction Hds as [| d ds Hd Hds IH]; intros pre pre' points points' Hpre Hpts; cbn [domains_set].
  - apply singleton_set_resp. apply list_code_resp. exact Hpts.
  - apply union_set_resp. apply replacement_set_resp.
    + intros b b' Eb. apply IH; [apply list_set_eq_refl | apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact Eb | constructor]]].
    + intros b b' Eb. apply IH; [apply list_set_eq_refl | apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact Eb | constructor]]].
    + apply code_carrier_resp. apply Hd. apply list_set_eq_app; assumption.
    + intros b _. apply IH; [exact Hpre | apply list_set_eq_app; [exact Hpts | apply list_set_eq_refl]].
Qed.

Lemma telescope_set_resp : forall ts, Forall list_function_respects ts ->
    forall pre pre' vals vals', list_set_eq pre pre' -> list_set_eq vals vals' ->
    set_eq (telescope_set ts pre vals) (telescope_set ts pre' vals').
Proof.
  intros ts Hts. induction Hts as [| t ts Ht Hts IH]; intros pre pre' vals vals' Hpre Hv; cbn [telescope_set].
  - apply singleton_set_resp. apply list_code_resp. exact Hv.
  - apply union_set_resp. apply replacement_set_resp.
    + intros b b' Eb. apply IH; [apply list_set_eq_refl | apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact Eb | constructor]]].
    + intros b b' Eb. apply IH; [apply list_set_eq_refl | apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact Eb | constructor]]].
    + apply code_carrier_resp. apply Ht. apply list_set_eq_app; assumption.
    + intros b _. apply IH; [exact Hpre | apply list_set_eq_app; [exact Hv | apply list_set_eq_refl]].
Qed.

Lemma plain_arguments_set_resp : forall gs, Forall argument_respects gs ->
    forall pre pre' vals vals', list_set_eq pre pre' -> list_set_eq vals vals' ->
    set_eq (plain_arguments_set gs pre vals) (plain_arguments_set gs pre' vals').
Proof.
  intros gs Hgs. induction Hgs as [| g gs Hg Hgs IH]; intros pre pre' vals vals' Hpre Hv; cbn [plain_arguments_set].
  - apply singleton_set_resp. apply list_code_resp. exact Hv.
  - destruct g as [κ t | type ds target tparams ls]; cbn [argument_respects] in Hg.
    + apply union_set_resp. apply replacement_set_resp.
      * intros b b' Eb. apply IH; apply list_set_eq_app; try apply list_set_eq_refl; constructor; [exact Eb | constructor | exact Eb | constructor].
      * intros b b' Eb. apply IH; apply list_set_eq_app; try apply list_set_eq_refl; constructor; [exact Eb | constructor | exact Eb | constructor].
      * apply code_carrier_resp. apply Hg. exact Hpre.
      * intros b _. apply IH; apply list_set_eq_app; try assumption; apply list_set_eq_refl.
    + apply IH; [apply list_set_eq_app; [exact Hpre | apply list_set_eq_refl] | exact Hv].
Qed.

Lemma argument_positions_resp : forall gs, Forall argument_respects gs ->
    forall pvals pvals' pre pre' j, list_set_eq pvals pvals' -> list_set_eq pre pre' ->
    set_eq (argument_positions gs pvals pre j) (argument_positions gs pvals' pre' j).
Proof.
  intros gs Hgs. induction Hgs as [| g gs Hg Hgs IH]; intros pvals pvals' pre pre' j Hpv Hpre; cbn [argument_positions].
  - apply set_eq_refl.
  - destruct g as [κ t | type ds target tparams ls]; cbn [argument_respects] in Hg.
    + destruct Hpv as [| p p' pv pv' Hp Hpv]; [apply set_eq_refl |].
      apply IH; [exact Hpv | apply list_set_eq_app; [exact Hpre | constructor; [exact Hp | constructor]]].
    + destruct Hg as [Hds _]. apply union_set_resp. apply unordered_pair_set_resp.
      * apply replacement_set_resp; [intros x y E; apply ordered_pair_resp; [apply set_eq_refl | exact E] |
          intros x y E; apply ordered_pair_resp; [apply set_eq_refl | exact E] |
          apply domains_set_resp; [exact Hds | exact Hpre | apply list_set_eq_refl] | intros x _; apply set_eq_refl].
      * apply IH; [exact Hpv | apply list_set_eq_app; [exact Hpre | apply list_set_eq_refl]].
Qed.

Lemma family_set_pointwise : forall (A : Type) (f f' : A -> aczel_set), (forall a, set_eq (f a) (f' a)) ->
    set_eq (family_set A f) (family_set A f').
Proof.
  intros A f f' E. apply set_eq_intro; intros z [a Ha]; exists a; cbn in *;
    [eapply set_eq_trans; [exact Ha | apply E] | eapply set_eq_trans; [exact Ha | apply set_eq_sym; apply E]].
Qed.

Section Respecting.
  Hypothesis Hsig : signature_respects G.

Lemma shape_positions_resp : respects_set_eq_fun shape_positions.
Proof.
  intros a a' E. unfold shape_positions. apply union_set_resp. apply family_set_pointwise. intros [[k i] Hki]; cbn [fst snd proj1_sig].
  destruct (List.nth_error (set_group_members G) k) as [Mk |] eqn:HMk; [| apply set_eq_refl].
  destruct (List.nth_error (set_member_constructors Mk) i) as [cs |] eqn:Hcs; [| apply set_eq_refl].
  pose proof (Hsig _ _ _ HMk (nth_error_In _ _ Hcs)) as Hgs.
  assert (Em : set_eq (shape_member a) (shape_member a')) by (apply pair_first_resp; exact E).
  assert (Ec : set_eq (shape_constructor a) (shape_constructor a')) by (apply pair_first_resp, pair_second_resp; exact E).
  apply cond_resp.
  - split; intros [H1 H2]; split; eapply set_eq_trans; try eassumption; apply set_eq_sym; assumption.
  - apply argument_positions_resp; [exact Hgs | apply list_decode_resp; apply pair_first_resp, pair_second_resp, pair_second_resp, pair_second_resp; exact E |].
    apply list_set_eq_app; [apply list_set_eq_refl | apply list_decode_resp; apply pair_first_resp, pair_second_resp, pair_second_resp; exact E].
Qed.

Lemma tree_shape_inj : forall k i ns pvals k' i' ns' pvals', set_eq (tree_shape k i ns pvals) (tree_shape k' i' ns' pvals') ->
    k = k' /\ i = i' /\ list_set_eq ns ns' /\ list_set_eq pvals pvals'.
Proof.
  intros * E. apply list_code_inj in E.
  inversion E as [| ? ? ? ? Ek E1]; subst. inversion E1 as [| ? ? ? ? Ei E2]; subst.
  inversion E2 as [| ? ? ? ? En E3]; subst. inversion E3 as [| ? ? ? ? Ep _]; subst.
  apply numeral_set_inj in Ek, Ei. apply list_code_inj in En, Ep. auto.
Qed.

Lemma interleave_arguments_resp : forall gs pvals pvals' rs rs', list_set_eq pvals pvals' -> list_set_eq rs rs' ->
    list_set_eq (interleave_arguments gs pvals rs) (interleave_arguments gs pvals' rs').
Proof.
  induction gs as [| [κ t | type ds target tparams ls] gs IH]; intros pvals pvals' rs rs' Hp Hr; cbn [interleave_arguments].
  - constructor.
  - destruct Hp as [| p p' pv pv' Hpp Hpv]; [constructor | constructor; [exact Hpp | apply IH; assumption]].
  - destruct Hr as [| r r' rv rv' Hrr Hrv]; [constructor | constructor; [exact Hrr | apply IH; assumption]].
Qed.

(** Decoding is a function of the tree. *)
Lemma tree_decodes_functional_all :
  (forall k ns t v, tree_decodes k ns t v ->
     forall ns' t' v', list_set_eq ns ns' -> set_eq t t' -> tree_decodes k ns' t' v' -> set_eq v v') /\
  (forall g gs pvals pre j rs, children_decode g gs pvals pre j rs -> Forall argument_respects gs ->
     forall g' pvals' pre' rs', set_eq g g' -> list_set_eq pvals pvals' -> list_set_eq pre pre' ->
     children_decode g' gs pvals' pre' j rs' -> list_set_eq rs rs') /\
  (forall g j ds target tparams pre points r, child_decodes g j ds target tparams pre points r ->
     Forall list_function_respects ds -> list_list_function_respects tparams ->
     forall g' pre' points' r', set_eq g g' -> list_set_eq pre pre' -> list_set_eq points points' ->
     child_decodes g' j ds target tparams pre' points' r' -> set_eq r r').
Proof.
  apply tree_decodes_combined_ind.
  - (** a node *)
    intros k ns Mk i cs pvals g rs t v HMk Hcs Et _ _ _ IHc Ev ns' t' v' Hns Ett H'.
    inversion H' as [k0 ns0 Mk' i' cs' pvals' g' rs' t0 v0 HMk' Hcs' Et' _ _ Hc' Ev']; subst.
    rewrite HMk in HMk'; injection HMk' as <-.
    pose proof (set_eq_trans _ _ _ (set_eq_sym _ _ Et) (set_eq_trans _ _ _ Ett Et')) as E.
    apply ordered_pair_inj in E as [Es Eg]. apply tree_shape_inj in Es as (_ & <- & _ & Epv).
    rewrite Hcs in Hcs'; injection Hcs' as <-.
    pose proof (Hsig _ _ _ HMk (nth_error_In _ _ Hcs)) as Hgs.
    pose proof (IHc Hgs g' pvals' (us ++ ns') rs' Eg Epv (list_set_eq_app _ _ _ _ (list_set_eq_refl _) Hns) Hc') as Hrs.
    eapply set_eq_trans; [exact Ev |]. eapply set_eq_trans; [| apply set_eq_sym; exact Ev'].
    apply constructed_element_resp; [exact Hns | apply interleave_arguments_resp; assumption].
  - (** no argument *)
    intros g pvals pre j _ g' pvals' pre' rs' _ _ _ H'. inversion H'; subst. constructor.
  - (** a non-recursive argument *)
    intros g κ t gs p pvals pre j rs _ IH Hr g' pvals' pre' rs' Eg Hpv Hpre H'.
    inversion Hr as [| ? ? Hg Hgs]; subst.
    inversion Hpv as [| ? p' ? pv' Hpp Hpv']; subst. inversion H'; subst.
    eapply IH; [exact Hgs | exact Eg | exact Hpv' | apply list_set_eq_app; [exact Hpre | constructor; [exact Hpp | constructor]] | eassumption].
  - (** a recursive argument *)
    intros g type ds target tparams ls gs pvals pre j r rs _ IH1 _ IH2 Hr g' pvals' pre' rs' Eg Hpv Hpre H'.
    inversion Hr as [| ? ? Hg Hgs]; subst. destruct Hg as [Hds Htp].
    inversion H'; subst. constructor.
    + eapply IH1; [exact Hds | exact Htp | exact Eg | exact Hpre | constructor | eassumption].
    + eapply IH2; [exact Hgs | exact Eg | exact Hpv | apply list_set_eq_app; [exact Hpre | apply list_set_eq_refl] | eassumption].
  - (** the end *)
    intros g j target tparams pre points r _ IH _ Htp g' pre' points' r' Eg Hpre Hpts H'.
    inversion H'; subst. eapply IH; [| | eassumption].
    + apply list_set_eq_skipn. apply Htp. apply list_set_eq_app; assumption.
    + apply set_apply_resp; [exact Eg |]. apply ordered_pair_resp; [apply set_eq_refl | apply list_code_resp; exact Hpts].
  - (** through a domain *)
    intros g j d ds target tparams pre points r Hf _ IH Hds Htp g' pre' points' r' Eg Hpre Hpts H'.
    inversion Hds as [| ? ? Hd Hds']; subst.
    inversion H' as [| ? ? ? ? ? ? ? ? ? Hf' Hc']; subst.
    assert (Ed : set_eq (code_carrier (d (pre ++ points))) (code_carrier (d (pre' ++ points'))))
      by (apply code_carrier_resp; apply Hd; apply list_set_eq_app; assumption).
    apply (is_function_on_ext _ _ _ _ Ed Hf Hf'). intros b Hb.
    eapply IH; [exact Hb | exact Hds' | exact Htp | exact Eg | exact Hpre
               | apply list_set_eq_app; [exact Hpts | apply list_set_eq_refl] | apply Hc'; eapply set_mem_eq_r; [exact Ed | exact Hb]].
Qed.

(** ** Positions *)

(** [points_fit ds pre points pts]: [pts] are points of the domains [ds]
    after the points [points]. *)
Inductive points_fit : list (list aczel_set -> aczel_set) -> list aczel_set -> list aczel_set -> list aczel_set -> Prop :=
(** No domain left *)
| points_fit_nil : forall pre points, points_fit nil pre points nil
(** A point of the next domain, then the rest *)
| points_fit_cons : forall d ds pre points b pts,
    set_mem b (code_carrier (d (pre ++ points))) ->
    points_fit ds pre (points ++ [b]) pts ->
    points_fit (d :: ds) pre points (b :: pts).

Lemma set_mem_domains_set : forall ds, Forall list_function_respects ds -> forall pre points z,
    set_mem z (domains_set ds pre points) <-> exists pts, points_fit ds pre points pts /\ set_eq z (list_code (points ++ pts)).
Proof.
  intros ds Hds. induction Hds as [| d ds Hd Hds IH]; intros pre points z; cbn [domains_set].
  - rewrite set_mem_singleton. split.
    + intros E. exists nil. rewrite app_nil_r. split; [constructor | exact E].
    + intros [pts [Hf E]]. inversion Hf; subst. rewrite app_nil_r in E. exact E.
  - assert (HF : respects_set_eq_fun (fun b => domains_set ds pre (points ++ [b]))).
    { intros b b' Eb. apply domains_set_resp; [exact Hds | apply list_set_eq_refl |
        apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact Eb | constructor]]]. }
    rewrite set_mem_union. split.
    + intros [w [Hw Hz]]. apply (set_mem_replacement _ _ _ HF) in Hw as [b [Hb Ew]].
      eapply set_mem_eq_r in Hz; [| exact Ew]. apply IH in Hz as [pts [Hf E]].
      exists (b :: pts). split; [constructor; assumption |]. rewrite <- app_assoc in E. exact E.
    + intros [pts [Hf E]]. inversion Hf as [| ? ? ? ? b pts' Hb Hf']; subst.
      exists (domains_set ds pre (points ++ [b])). split; [apply (set_mem_replacement _ _ _ HF); exists b; split; [exact Hb | apply set_eq_refl] |].
      apply IH. exists pts'. split; [exact Hf' | rewrite <- app_assoc; exact E].
Qed.

(** [position_of gs pvals pre j pos]: [pos] is a position of a recursive
    argument of [gs], numbered from [j]. *)
Inductive position_of : list set_argument -> list aczel_set -> list aczel_set -> nat -> aczel_set -> Prop :=
(** A position of this recursive argument *)
| position_of_here : forall type ds target tparams ls gs pvals pre j pts pos,
    points_fit ds pre nil pts -> set_eq pos (tree_position j pts) ->
    position_of (set_argument_recursive type ds target tparams ls :: gs) pvals pre j pos
(** A position of a later argument, after a recursive one *)
| position_of_after_recursive : forall type ds target tparams ls gs pvals pre j pos,
    position_of gs pvals (pre ++ [empty_set]) (S j) pos ->
    position_of (set_argument_recursive type ds target tparams ls :: gs) pvals pre j pos
(** A position of a later argument, after a non-recursive one *)
| position_of_after_plain : forall κ t gs p pvals pre j pos,
    position_of gs pvals (pre ++ [p]) (S j) pos ->
    position_of (set_argument_plain κ t :: gs) (p :: pvals) pre j pos.

Lemma set_mem_argument_positions : forall gs, Forall argument_respects gs -> forall pvals pre j pos,
    set_mem pos (argument_positions gs pvals pre j) -> position_of gs pvals pre j pos.
Proof.
  intros gs Hgs. induction Hgs as [| g gs Hg Hgs IH]; intros pvals pre j pos Hpos; cbn [argument_positions] in Hpos.
  - exfalso. exact (set_mem_empty _ Hpos).
  - destruct g as [κ t | type ds target tparams ls]; cbn [argument_respects] in Hg.
    + destruct pvals as [| p pvals]; [exfalso; exact (set_mem_empty _ Hpos) |].
      apply position_of_after_plain. apply IH. exact Hpos.
    + destruct Hg as [Hds _]. apply set_mem_union in Hpos as [w [Hw Hpos]]. apply set_mem_unordered_pair in Hw as [Hw | Hw].
      * eapply set_mem_eq_r in Hpos; [| exact Hw].
        assert (HF : respects_set_eq_fun (fun pts => ordered_pair (numeral_set j) pts)) by (intros x y E; apply ordered_pair_resp; [apply set_eq_refl | exact E]).
        apply (set_mem_replacement _ _ _ HF) in Hpos as [z [Hz Ep]]. apply (set_mem_domains_set _ Hds) in Hz as [pts [Hf Ez]].
        eapply position_of_here; [exact Hf |]. eapply set_eq_trans; [exact Ep |]. apply ordered_pair_resp; [apply set_eq_refl | exact Ez].
      * eapply set_mem_eq_r in Hpos; [| exact Hw]. apply position_of_after_recursive. apply IH. exact Hpos.
Qed.

(** A curried function applied to a list of points, outermost first. *)
Fixpoint apply_points (r : aczel_set) (pts : list aczel_set) : aczel_set :=
  match pts with
  | nil => r
  | b :: pts' => apply_points (set_apply r b) pts'
  end.

Lemma apply_points_resp : forall pts pts' r r', list_set_eq pts pts' -> set_eq r r' -> set_eq (apply_points r pts) (apply_points r' pts').
Proof.
  intros pts pts' r r' H. revert r r'. induction H as [| b b' pts pts' Hb H IH]; intros r r' Er; cbn [apply_points]; [exact Er |].
  apply IH. apply set_apply_resp; assumption.
Qed.

(** Along the points of its domains, a decoded recursive argument reaches
    the decoding of the child there. *)
Lemma child_decodes_at : forall ds pre points pts, points_fit ds pre points pts ->
    forall g j target tparams r, child_decodes g j ds target tparams pre points r ->
    tree_decodes target (List.skipn nuniform (tparams (pre ++ points ++ pts))) (set_apply g (tree_position j (points ++ pts)))
      (apply_points r pts).
Proof.
  intros ds pre points pts Hf. induction Hf as [pre points | d ds pre points b pts Hb Hf IH]; intros g j target tparams r Hc.
  - inversion Hc; subst. rewrite !app_nil_r. cbn [apply_points]. assumption.
  - inversion Hc as [| ? ? ? ? ? ? ? ? ? _ Hc']; subst. cbn [apply_points].
    specialize (IH g j target tparams (set_apply r b) (Hc' b Hb)). rewrite <- !app_assoc in IH. exact IH.
Qed.

End Respecting.

(** ** Injectivity of the Elements *)

Lemma set_mem_tuple_code : forall z fs,
    set_mem z (tuple_code fs) <-> Exists (fun f => set_eq z (ordered_pair (string_code (fst f)) (snd f))) fs.
Proof.
  intros z fs. unfold tuple_code. rewrite set_mem_set_of_list. rewrite Exists_map. reflexivity.
Qed.

Lemma tuple_code_field_absent : forall f fl vals x, ~ In f fl ->
    ~ set_mem (ordered_pair (string_code f) x) (tuple_code (List.combine fl vals)).
Proof.
  intros f fl vals x Hf Hm. apply set_mem_tuple_code in Hm. apply Exists_exists in Hm as [[f' v'] [Hin E]].
  apply ordered_pair_inj in E as [Ef _]. apply string_code_inj in Ef; cbn in Ef; subst f'.
  apply Hf. exact (in_combine_l _ _ _ _ Hin).
Qed.

Lemma tuple_code_combine_inj : forall fl vals vals', NoDup fl -> List.length vals = List.length fl -> List.length vals' = List.length fl ->
    set_eq (tuple_code (List.combine fl vals)) (tuple_code (List.combine fl vals')) -> list_set_eq vals vals'.
Proof.
  induction fl as [| f fl IH]; intros [| v vals] [| v' vals'] Hnd Hl Hl' E; cbn in Hl, Hl'; try discriminate; [constructor |].
  inversion Hnd as [| ? ? Hnin Hnd']; subst.
  cbn [List.combine] in E. unfold tuple_code in E. cbn [List.map set_of_list] in E. fold (tuple_code (List.combine fl vals)) in E.
  fold (tuple_code (List.combine fl vals')) in E.
  set (R := tuple_code (List.combine fl vals)) in *. set (R' := tuple_code (List.combine fl vals')) in *.
  assert (Hmem : forall p x y X, set_mem p (union_set (unordered_pair_set (singleton_set (ordered_pair x y)) X)) <->
                                  set_eq p (ordered_pair x y) \/ set_mem p X).
  { intros p x y X. rewrite set_mem_union. split.
    - intros [w [Hw Hp]]. apply set_mem_unordered_pair in Hw as [Hw | Hw].
      + left. eapply set_mem_eq_r in Hp; [| exact Hw]. apply set_mem_singleton in Hp. exact Hp.
      + right. eapply set_mem_eq_r; [exact Hw | exact Hp].
    - intros [Hp | Hp].
      + exists (singleton_set (ordered_pair x y)). split; [apply set_mem_unordered_pair; left; apply set_eq_refl | apply set_mem_singleton; exact Hp].
      + exists X. split; [apply set_mem_unordered_pair; right; apply set_eq_refl | exact Hp]. }
  cbn [fst snd] in E.
  assert (Ev : set_eq v v').
  { assert (H1 : set_mem (ordered_pair (string_code f) v) (union_set (unordered_pair_set (singleton_set (ordered_pair (string_code f) v')) R')))
      by (eapply set_mem_eq_r; [exact E | apply Hmem; left; apply set_eq_refl]).
    apply Hmem in H1 as [H1 | H1]; [apply ordered_pair_inj in H1; tauto |].
    exfalso. exact (tuple_code_field_absent f fl vals' v Hnin H1). }
  constructor; [exact Ev |]. apply IH; [exact Hnd' | lia | lia |].
  apply set_eq_intro; intros z Hz.
  - assert (H1 : set_mem z (union_set (unordered_pair_set (singleton_set (ordered_pair (string_code f) v')) R')))
      by (eapply set_mem_eq_r; [exact E | apply Hmem; right; exact Hz]).
    apply Hmem in H1 as [H1 | H1]; [| exact H1].
    exfalso. apply (tuple_code_field_absent f fl vals v' Hnin). eapply set_mem_eq_l; [exact H1 | exact Hz].
  - assert (H1 : set_mem z (union_set (unordered_pair_set (singleton_set (ordered_pair (string_code f) v)) R)))
      by (eapply set_mem_eq_r; [apply set_eq_sym; exact E | apply Hmem; right; exact Hz]).
    apply Hmem in H1 as [H1 | H1]; [| exact H1].
    exfalso. apply (tuple_code_field_absent f fl vals' v Hnin). eapply set_mem_eq_l; [exact H1 | exact Hz].
Qed.

(** The number of recursive arguments. *)
Fixpoint recursive_count (gs : list set_argument) : nat :=
  match gs with
  | nil => 0
  | set_argument_plain _ _ :: gs' => recursive_count gs'
  | set_argument_recursive _ _ _ _ _ :: gs' => S (recursive_count gs')
  end.

Lemma length_interleave_arguments : forall gs pvals rs, List.length pvals = plain_count gs -> List.length rs = recursive_count gs ->
    List.length (interleave_arguments gs pvals rs) = List.length gs.
Proof.
  induction gs as [| [κ t | type ds target tparams ls] gs IH]; intros pvals rs Hp Hr; cbn in *; [reflexivity | |].
  - destruct pvals; cbn in Hp; [discriminate | cbn; f_equal; apply IH; [lia | exact Hr]].
  - destruct rs; cbn in Hr; [discriminate | cbn; f_equal; apply IH; [exact Hp | lia]].
Qed.

Lemma interleave_arguments_inj : forall gs pvals pvals' rs rs',
    List.length pvals = plain_count gs -> List.length pvals' = plain_count gs ->
    List.length rs = recursive_count gs -> List.length rs' = recursive_count gs ->
    list_set_eq (interleave_arguments gs pvals rs) (interleave_arguments gs pvals' rs') ->
    list_set_eq pvals pvals' /\ list_set_eq rs rs'.
Proof.
  induction gs as [| [κ t | type ds target tparams ls] gs IH]; intros pvals pvals' rs rs' Hp Hp' Hr Hr' E; cbn in *.
  - destruct pvals, pvals', rs, rs'; try discriminate. split; constructor.
  - destruct pvals as [| p pvals], pvals' as [| p' pvals']; cbn in Hp, Hp'; try discriminate.
    inversion E as [| ? ? ? ? Epp Erest]; subst.
    destruct (IH pvals pvals' rs rs' ltac:(lia) ltac:(lia) Hr Hr' Erest) as [Ep Er].
    split; [constructor; assumption | exact Er].
  - destruct rs as [| r rs], rs' as [| r' rs']; cbn in Hr, Hr'; try discriminate.
    inversion E as [| ? ? ? ? Err Erest]; subst.
    destruct (IH pvals pvals' rs rs' Hp Hp' ltac:(lia) ltac:(lia) Erest) as [Ep Er].
    split; [exact Ep | constructor; assumption].
Qed.

Lemma children_decode_length : forall g gs pvals pre j rs, children_decode g gs pvals pre j rs -> List.length rs = recursive_count gs.
Proof.
  intros g gs pvals pre j rs H. induction H; cbn; [reflexivity | exact IHchildren_decode | f_equal; exact IHchildren_decode].
Qed.

Section Injective.
  Hypothesis Hsig : signature_respects G.
  (** The constructor names of each member are distinct *)
  Hypothesis Hnames : forall k Mk, List.nth_error (set_group_members G) k = Some Mk ->
    NoDup (List.map set_constructor_name (set_member_constructors Mk)).
  (** A record view has one constructor, of one argument per field, and
      its field names are distinct *)
  Hypothesis Hrview : forall k Mk fl, List.nth_error (set_group_members G) k = Some Mk -> set_member_record_fields Mk = Some fl ->
    NoDup fl /\ List.length (set_member_constructors Mk) = 1 /\
    (forall cs, In cs (set_member_constructors Mk) -> List.length (set_constructor_arguments cs) = List.length fl).

Lemma nodup_map_index : forall {A B} (f : A -> B) (l : list A) i i' x x', NoDup (List.map f l) ->
    List.nth_error l i = Some x -> List.nth_error l i' = Some x' -> f x = f x' -> i = i'.
Proof.
  intros A B f l i i' x x' Hnd Hi Hi' Ef.
  apply (proj1 (NoDup_nth_error (List.map f l)) Hnd i i').
  - rewrite length_map. apply nth_error_Some. congruence.
  - rewrite !nth_error_map, Hi, Hi'. cbn. f_equal. exact Ef.
Qed.

(** At one member, two equal elements are built by one constructor at
    equal arguments. *)
Lemma constructed_element_inj : forall k Mk i i' cs cs' ns ns' vals vals',
    List.nth_error (set_group_members G) k = Some Mk ->
    List.nth_error (set_member_constructors Mk) i = Some cs -> List.nth_error (set_member_constructors Mk) i' = Some cs' ->
    List.length vals = List.length (set_constructor_arguments cs) -> List.length vals' = List.length (set_constructor_arguments cs') ->
    list_set_eq ns ns' ->
    set_eq (constructed_element Mk cs ns vals) (constructed_element Mk cs' ns' vals') -> i = i' /\ list_set_eq vals vals'.
Proof.
  intros * HMk Hi Hi' Hl Hl' Hns E. unfold constructed_element in E.
  destruct (set_member_record_fields Mk) as [fl |] eqn:Hfl.
  - destruct (Hrview _ _ _ HMk Hfl) as (Hnd & H1 & Hargs).
    assert (i = 0) as -> by (assert (i < 1) by (rewrite <- H1; apply nth_error_Some; congruence); lia).
    assert (i' = 0) as -> by (assert (i' < 1) by (rewrite <- H1; apply nth_error_Some; congruence); lia).
    rewrite Hi in Hi'. injection Hi' as <-. split; [reflexivity |].
    pose proof (Hargs cs (nth_error_In _ _ Hi)) as Ha.
    apply (tuple_code_combine_inj fl vals vals' Hnd); [lia | lia | exact E].
  - unfold con_val in E. apply ordered_pair_inj in E as [En El]. apply string_code_inj in En.
    pose proof (nodup_map_index _ _ _ _ _ _ (Hnames _ _ HMk) Hi Hi' En) as <-.
    rewrite Hi in Hi'. injection Hi' as <-. split; [reflexivity |].
    apply list_code_inj in El. exact (proj2 (list_set_eq_app_split _ _ _ _ El (list_set_eq_length _ _ Hns))).
Qed.

(** Decoding is injective at one member: equal elements have equal
    trees. *)
Lemma tree_decodes_injective_all :
  (forall k ns t v, tree_decodes k ns t v ->
     forall ns' t' v', list_set_eq ns ns' -> set_eq v v' -> tree_decodes k ns' t' v' -> set_eq t t') /\
  (forall g gs pvals pre j rs, children_decode g gs pvals pre j rs -> Forall argument_respects gs ->
     forall g' pvals' pre' rs', list_set_eq pvals pvals' -> list_set_eq pre pre' -> list_set_eq rs rs' ->
     children_decode g' gs pvals' pre' j rs' ->
     forall pos, position_of gs pvals pre j pos -> set_eq (set_apply g pos) (set_apply g' pos)) /\
  (forall g j ds target tparams pre points r, child_decodes g j ds target tparams pre points r ->
     Forall list_function_respects ds -> list_list_function_respects tparams ->
     forall g' pre' points' r', list_set_eq pre pre' -> list_set_eq points points' -> set_eq r r' ->
     child_decodes g' j ds target tparams pre' points' r' ->
     forall pts, points_fit ds pre points pts ->
     set_eq (set_apply g (tree_position j (points ++ pts))) (set_apply g' (tree_position j (points' ++ pts)))).
Proof.
  apply tree_decodes_combined_ind.
  - (** a node *)
    intros k ns Mk i cs pvals g rs t v HMk Hcs Et Hlp Hfg Hc IHc Ev ns' t' v' Hns Evv H'.
    inversion H' as [k0 ns0 Mk' i' cs' pvals' g' rs' t0 v0 HMk' Hcs' Et' Hlp' Hfg' Hc' Ev']; subst.
    rewrite HMk in HMk'; injection HMk' as <-.
    pose proof (children_decode_length _ _ _ _ _ _ Hc) as Hlr. pose proof (children_decode_length _ _ _ _ _ _ Hc') as Hlr'.
    destruct (constructed_element_inj k Mk i i' cs cs' ns ns' _ _ HMk Hcs Hcs'
                (length_interleave_arguments _ _ _ Hlp Hlr) (length_interleave_arguments _ _ _ Hlp' Hlr') Hns
                (set_eq_trans _ _ _ (set_eq_sym _ _ Ev) (set_eq_trans _ _ _ Evv Ev'))) as [<- Eargs].
    rewrite Hcs in Hcs'; injection Hcs' as <-.
    destruct (interleave_arguments_inj _ _ _ _ _ Hlp Hlp' Hlr Hlr' Eargs) as [Epv Ers].
    pose proof (Hsig _ _ _ HMk (nth_error_In _ _ Hcs)) as Hgs.
    assert (Hpre : list_set_eq (us ++ ns) (us ++ ns')) by (apply list_set_eq_app; [apply list_set_eq_refl | exact Hns]).
    assert (ED : set_eq (argument_positions (set_constructor_arguments cs) pvals (us ++ ns) 0)
                        (argument_positions (set_constructor_arguments cs) pvals' (us ++ ns') 0))
      by (apply argument_positions_resp; assumption).
    assert (Eg : set_eq g g').
    { apply (is_function_on_ext _ _ _ _ ED Hfg Hfg'). intros pos Hpos.
      eapply IHc; [exact Hgs | exact Epv | exact Hpre | exact Ers | exact Hc' |].
      exact (set_mem_argument_positions _ Hgs _ _ _ _ Hpos). }
    eapply set_eq_trans; [exact Et |]. eapply set_eq_trans; [| apply set_eq_sym; exact Et'].
    apply ordered_pair_resp; [| exact Eg]. unfold tree_shape. apply list_code_resp.
    repeat constructor; try apply set_eq_refl; apply list_code_resp; assumption.
  - (** no argument *)
    intros g pvals pre j _ g' pvals' pre' rs' _ _ _ _ pos Hpos. inversion Hpos.
  - (** a non-recursive argument *)
    intros g κ t gs p pvals pre j rs _ IH Hr g' pvals' pre' rs' Hpv Hpre Hrs H' pos Hpos.
    inversion Hr as [| ? ? _ Hgs]; subst.
    inversion Hpv as [| ? p' ? pv' Hpp Hpv']; subst. inversion H'; subst. inversion Hpos; subst.
    eapply IH; [exact Hgs | exact Hpv' | apply list_set_eq_app; [exact Hpre | constructor; [exact Hpp | constructor]] | exact Hrs | eassumption | eassumption].
  - (** a recursive argument *)
    intros g type ds target tparams ls gs pvals pre j r rs _ IH1 _ IH2 Hr g' pvals' pre' rs' Hpv Hpre Hrs H' pos Hpos.
    inversion Hr as [| ? ? Hg Hgs]; subst. destruct Hg as [Hds Htp].
    inversion Hrs as [| ? r' ? rs'' Hrr Hrs']; subst. inversion H'; subst. inversion Hpos as [? ? ? ? ? ? ? ? ? pts ? Hf Ep | |]; subst.
    + eapply set_eq_trans; [apply set_apply_resp; [apply set_eq_refl | exact Ep] |].
      eapply set_eq_trans; [| apply set_apply_resp; [apply set_eq_refl | apply set_eq_sym; exact Ep]].
      exact (IH1 Hds Htp g' pre' nil r' Hpre (list_set_eq_refl _) Hrr ltac:(eassumption) pts Hf).
    + eapply IH2; [exact Hgs | exact Hpv | apply list_set_eq_app; [exact Hpre | apply list_set_eq_refl] | exact Hrs' | eassumption | eassumption].
  - (** the end *)
    intros g j target tparams pre points r _ IH _ Htp g' pre' points' r' Hpre Hpts Hr H' pts Hf.
    inversion Hf; subst. inversion H'; subst. rewrite !app_nil_r.
    eapply IH; [| exact Hr | eassumption].
    apply list_set_eq_skipn. apply Htp. apply list_set_eq_app; assumption.
  - (** through a domain *)
    intros g j d ds target tparams pre points r _ _ IH Hds Htp g' pre' points' r' Hpre Hpts Hr H' pts Hf.
    inversion Hds as [| ? ? Hd Hds']; subst.
    inversion H' as [| ? ? ? ? ? ? ? ? ? _ Hc']; subst.
    inversion Hf as [| ? ? ? ? b pts' Hb Hf']; subst.
    assert (Ed : set_eq (code_carrier (d (pre ++ points))) (code_carrier (d (pre' ++ points'))))
      by (apply code_carrier_resp; apply Hd; apply list_set_eq_app; assumption).
    pose proof (IH b Hb Hds' Htp g' pre' (points' ++ [b]) (set_apply r' b) Hpre
                  (list_set_eq_app _ _ _ _ Hpts (list_set_eq_refl _)) (set_apply_resp _ _ _ _ Hr (set_eq_refl _))
                  (Hc' b (set_mem_eq_r _ _ _ Ed Hb)) pts' Hf') as E.
    rewrite <- !app_assoc in E. exact E.
Qed.

Corollary tree_decodes_injective : forall k ns t v ns' t' v', tree_decodes k ns t v ->
    list_set_eq ns ns' -> set_eq v v' -> tree_decodes k ns' t' v' -> set_eq t t'.
Proof. intros. eapply (proj1 tree_decodes_injective_all); eassumption. Qed.

End Injective.

(** ** Splitting Arguments *)

(** The non-recursive and the recursive values among the arguments. *)
Fixpoint split_arguments (gs : list set_argument) (vals : list aczel_set) : list aczel_set * list aczel_set :=
  match gs, vals with
  | set_argument_plain _ _ :: gs', a :: vals' => let '(p, r) := split_arguments gs' vals' in (a :: p, r)
  | set_argument_recursive _ _ _ _ _ :: gs', a :: vals' => let '(p, r) := split_arguments gs' vals' in (p, a :: r)
  | _, _ => (nil, nil)
  end.

Lemma split_arguments_spec : forall gs vals, List.length vals = List.length gs ->
    interleave_arguments gs (fst (split_arguments gs vals)) (snd (split_arguments gs vals)) = vals /\
    List.length (fst (split_arguments gs vals)) = plain_count gs /\
    List.length (snd (split_arguments gs vals)) = recursive_count gs.
Proof.
  induction gs as [| [κ t | type ds target tparams ls] gs IH]; intros [| a vals] Hl; cbn in Hl; try discriminate; cbn.
  - auto.
  - destruct (IH vals ltac:(lia)) as (H1 & H2 & H3). destruct (split_arguments gs vals) as [p r]. cbn in *. rewrite H1. auto.
  - destruct (IH vals ltac:(lia)) as (H1 & H2 & H3). destruct (split_arguments gs vals) as [p r]. cbn in *. rewrite H1. auto.
Qed.

Lemma arguments_fit_length : forall bound S pre gs vals, arguments_fit G bound S pre gs vals -> List.length vals = List.length gs.
Proof. intros * H. induction H; cbn; congruence. Qed.

(** ** Membership in the Telescopes *)

Lemma set_mem_telescope_set : forall ts, Forall list_function_respects ts -> forall pre vals z,
    set_mem z (telescope_set ts pre vals) <->
    exists ws, List.length ws = List.length ts /\ set_eq z (list_code (vals ++ ws)) /\
      (forall i t w, List.nth_error ts i = Some t -> List.nth_error ws i = Some w ->
         set_mem w (code_carrier (t (pre ++ vals ++ List.firstn i ws)))).
Proof.
  intros ts Hts. induction Hts as [| t ts Ht Hts IH]; intros pre vals z; cbn [telescope_set].
  - rewrite set_mem_singleton. split.
    + intros E. exists nil. rewrite app_nil_r. split; [reflexivity | split; [exact E | intros [] ? ? ? ?; discriminate]].
    + intros [ws [Hl [E _]]]. destruct ws; [rewrite app_nil_r in E; exact E | discriminate].
  - assert (HF : respects_set_eq_fun (fun a => telescope_set ts pre (vals ++ [a]))).
    { intros a a' Ea. apply telescope_set_resp; [exact Hts | apply list_set_eq_refl |
        apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact Ea | constructor]]]. }
    rewrite set_mem_union. split.
    + intros [w [Hw Hz]]. apply (set_mem_replacement _ _ _ HF) in Hw as [a [Ha Ew]].
      eapply set_mem_eq_r in Hz; [| exact Ew]. apply IH in Hz as [ws [Hl [E Hmem]]].
      exists (a :: ws). split; [cbn; lia |]. split; [rewrite <- app_assoc in E; exact E |].
      intros [| i] t' w' Ht' Hw'; cbn in Ht', Hw'.
      * injection Ht' as <-. injection Hw' as <-. rewrite app_nil_r. exact Ha.
      * specialize (Hmem i t' w' Ht' Hw'). rewrite <- app_assoc in Hmem. exact Hmem.
    + intros [[| a ws] [Hl [E Hmem]]]; [discriminate |].
      exists (telescope_set ts pre (vals ++ [a])). split.
      * apply (set_mem_replacement _ _ _ HF). exists a. split; [| apply set_eq_refl].
        specialize (Hmem 0 t a eq_refl eq_refl). cbn in Hmem. rewrite app_nil_r in Hmem. exact Hmem.
      * apply IH. exists ws. split; [cbn in Hl; lia |]. split; [rewrite <- app_assoc; exact E |].
        intros i t' w' Ht' Hw'. specialize (Hmem (S i) t' w' Ht' Hw'). cbn in Hmem. rewrite <- app_assoc. exact Hmem.
Qed.

(** The non-recursive arguments of fitting arguments are in their set. *)
Lemma plain_arguments_set_of_fit : forall bound S pre gs vals, arguments_fit G bound S pre gs vals -> Forall argument_respects gs ->
    forall prefix, set_mem (list_code (prefix ++ fst (split_arguments gs vals))) (plain_arguments_set gs pre prefix).
Proof.
  intros bound S pre gs vals H. induction H as [pre | pre κ type gs a vals Ha H IH | pre type ds target tparams ls gs a vals Ha H IH];
    intros Hr prefix; cbn [split_arguments plain_arguments_set]; inversion Hr as [| ? ? Hg Hgs]; subst.
  - rewrite app_nil_r. apply set_mem_singleton. apply set_eq_refl.
  - destruct (split_arguments gs vals) as [p r] eqn:Es. cbn [fst] in *.
    assert (HF : respects_set_eq_fun (fun a => plain_arguments_set gs (pre ++ [a]) (prefix ++ [a]))).
    { intros x y E. apply plain_arguments_set_resp; [exact Hgs | |];
        (apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact E | constructor]]). }
    apply set_mem_union. exists (plain_arguments_set gs (pre ++ [a]) (prefix ++ [a])). split.
    + apply (set_mem_replacement _ _ _ HF). exists a. split; [exact Ha | apply set_eq_refl].
    + specialize (IH Hgs (prefix ++ [a])). rewrite <- app_assoc in IH. exact IH.
  - destruct (split_arguments gs vals) as [p r] eqn:Es. cbn [fst] in *. exact (IH Hgs prefix).
Qed.

End Bound.
