(** * The Graph of an Eliminator

    The elements of an inductive type are flat: a constructor's name and
    the values of its non-uniform parameters and arguments ([con_val]),
    a record view's the tuple of its fields.  The eliminator of a group at
    given branches is a relation between an element and its result
    ([elim_graph]): at a constructor, the result is the branch at the
    non-uniform parameters, the arguments and the recursive results, one
    per leaf path of each recursive argument, each related to the
    argument's value at the end of its path.  It is the toy's [WR],
    generalized to groups, function-shaped arguments and record views. *)

From Stdlib Require Import String List.
From Mctt.Core.SetModel.Sets Require Export Encodings.
From Mctt.Core.SetModel.Interpretation.Global Require Export Valuation.
Import ListNotations.

(** The element of a constructor [c] at the values [vals] of the
    non-uniform parameters and the arguments. *)
Definition con_val (c : string) (vals : list aczel_set) : aczel_set := ordered_pair (string_code c) (list_code vals).

(** The tuple of the fields [fs], by name: a graph on the fields' names. *)
Definition tuple_code (fs : list (string * aczel_set)) : aczel_set :=
  set_of_list (List.map (fun f => ordered_pair (string_code (fst f)) (snd f)) fs).

(** The field [f] of a tuple: tuples are graphs on the fields' names. *)
Definition tuple_field (t : aczel_set) (f : string) : aczel_set := set_apply t (string_code f).

Section ElimGraph.
  (** The group *)
  Variable G : set_group.
  (** The branches, as a relation to their results: of the member, of the
      constructor, at the non-uniform parameters, the arguments and the
      recursive results *)
  Variable branch : nat -> string -> list aczel_set -> aczel_set -> Prop.

  (** The number of uniform parameters. *)
  Let nuniform : nat := List.length (set_group_uniform_types G).

(** [elim_graph k params v r]: the eliminator at the member [k], at the
    values [params] of its parameters (uniform, then non-uniform), takes
    the element [v] to [r]. *)
Inductive elim_graph : nat -> list aczel_set -> aczel_set -> aczel_set -> Prop :=
(** At a constructor of the member: its branch at the recursive results *)
| elim_graph_intro : forall k Mk cs params vals ihs v r,
    List.nth_error (set_group_members G) k = Some Mk ->
    In cs (set_member_constructors Mk) ->
    set_eq v (con_val (set_constructor_name cs) (List.skipn nuniform params ++ vals)) ->
    arguments_results params (set_constructor_arguments cs) vals ihs ->
    branch k (set_constructor_name cs) (List.skipn nuniform params ++ vals ++ ihs) r ->
    elim_graph k params v r
(** [arguments_results pre gs vals ihs]: the arguments [gs] at the values
    [vals], after the values [pre] (the parameters and the arguments before
    them), have the recursive results [ihs] *)
with arguments_results : list aczel_set -> list set_argument -> list aczel_set -> list aczel_set -> Prop :=
(** No argument: no result *)
| arguments_results_nil : forall pre, arguments_results pre nil nil nil
(** A non-recursive argument has no result *)
| arguments_results_plain : forall pre κ type gs a vals ihs,
    arguments_results (pre ++ [a]) gs vals ihs ->
    arguments_results pre (set_argument_plain κ type :: gs) (a :: vals) ihs
(** A recursive argument has one result per leaf path; no later type
    depends on it, so the values after it see the empty set in its place *)
| arguments_results_recursive : forall pre type ds target tparams ls gs a vals ihs1 ihs2,
    leaves_results pre a ls ihs1 ->
    arguments_results (pre ++ [empty_set]) gs vals ihs2 ->
    arguments_results pre (set_argument_recursive type ds target tparams ls :: gs) (a :: vals) (ihs1 ++ ihs2)
(** [leaves_results pre a ls ihs]: the leaf paths [ls] of the argument [a]
    have the results [ihs], one each *)
with leaves_results : list aczel_set -> aczel_set -> list set_leaf -> list aczel_set -> Prop :=
(** No path *)
| leaves_results_nil : forall pre a, leaves_results pre a nil nil
(** A path, then the others *)
| leaves_results_cons : forall pre a l ls ih ihs,
    leaf_result pre (set_leaf_steps l) l nil a ih ->
    leaves_results pre a ls ihs ->
    leaves_results pre a (l :: ls) (ih :: ihs)
(** [leaf_result pre steps l points a ih]: along the remaining [steps] of
    the path [l], at the domain points [points] passed so far, the value
    [a] has the result [ih] *)
with leaf_result : list aczel_set -> list set_leaf_step -> set_leaf -> list aczel_set -> aczel_set -> aczel_set -> Prop :=
(** At the end: the eliminator at the path's member *)
| leaf_result_end : forall pre l points a ih,
    elim_graph (set_leaf_target l) (set_leaf_target_params l (pre ++ points)) a ih ->
    leaf_result pre nil l points a ih
(** Through a domain: a function, at each point the result of the
    argument there *)
| leaf_result_domain : forall pre d steps l points a ih,
    is_function_on (code_carrier (d (pre ++ points))) ih ->
    (forall b, set_mem b (code_carrier (d (pre ++ points))) ->
       leaf_result pre steps l (points ++ [b]) (set_apply a b) (set_apply ih b)) ->
    leaf_result pre (set_leaf_step_domain d :: steps) l points a ih
(** Through a field: the result of the field *)
| leaf_result_field : forall pre f steps l points a ih,
    leaf_result pre steps l points (tuple_field a f) ih ->
    leaf_result pre (set_leaf_step_field f :: steps) l points a ih.

Scheme elim_graph_mut_ind := Minimality for elim_graph Sort Prop
with arguments_results_mut_ind := Minimality for arguments_results Sort Prop
with leaves_results_mut_ind := Minimality for leaves_results Sort Prop
with leaf_result_mut_ind := Minimality for leaf_result Sort Prop.
Combined Scheme elim_graph_combined_ind from elim_graph_mut_ind, arguments_results_mut_ind, leaves_results_mut_ind, leaf_result_mut_ind.

End ElimGraph.

(** ** Functionality *)

(** A function of a list of sets respects their equality. *)
Definition list_function_respects (f : list aczel_set -> aczel_set) : Prop :=
  forall l l', list_set_eq l l' -> set_eq (f l) (f l').

(** A list-valued function of a list of sets respects their equality. *)
Definition list_list_function_respects (f : list aczel_set -> list aczel_set) : Prop :=
  forall l l', list_set_eq l l' -> list_set_eq (f l) (f l').

(** What functionality needs of a group: its constructors' names tell them
    apart, and its leaf paths' domains and parameters respect equality. *)
Record group_respects (G : set_group) : Prop := mk_group_respects
  { (** Two constructors of a member with one name are the same *)
    group_respects_names : forall k Mk cs cs', List.nth_error (set_group_members G) k = Some Mk ->
      In cs (set_member_constructors Mk) -> In cs' (set_member_constructors Mk) ->
      set_constructor_name cs = set_constructor_name cs' -> cs = cs'
    (** Every domain of a leaf path respects equality *)
  ; group_respects_domains : forall l d, In (set_leaf_step_domain d) (set_leaf_steps l) -> list_function_respects d
    (** Every leaf path's parameters respect equality *)
  ; group_respects_target_params : forall l, list_list_function_respects (set_leaf_target_params l) }.

(** Two functions on equal sets, equal at every point, are equal. *)
Lemma is_function_on_ext : forall D D' g h, set_eq D D' -> is_function_on D g -> is_function_on D' h ->
    (forall b, set_mem b D -> set_eq (set_apply g b) (set_apply h b)) -> set_eq g h.
Proof.
  intros D D' g h ED Hg Hh Hpt.
  pose proof (is_function_on_resp _ _ _ _ (set_eq_sym _ _ ED) (set_eq_refl _) Hh) as Hh'.
  destruct Hg as [Pg [Tg Fg]]. destruct Hh' as [Ph [Th Fh]].
  apply set_eq_intro.
  - intros p Hp. destruct (Pg p Hp) as [b [y [Hb E]]].
    assert (Hby : set_mem (ordered_pair b y) g) by (eapply set_mem_eq_l; [exact E | exact Hp]).
    destruct (Th b Hb) as [y' Hy'].
    assert (Ey : set_eq y y').
    { eapply set_eq_trans; [apply set_eq_sym; apply (is_function_on_apply D g b y (conj Pg (conj Tg Fg)) Hby) |].
      eapply set_eq_trans; [apply Hpt; exact Hb | apply (is_function_on_apply D h b y' (conj Ph (conj Th Fh)) Hy')]. }
    eapply set_mem_eq_l; [apply set_eq_sym; eapply set_eq_trans; [exact E | apply ordered_pair_resp; [apply set_eq_refl | exact Ey]] | exact Hy'].
  - intros p Hp. destruct (Ph p Hp) as [b [y [Hb E]]].
    assert (Hby : set_mem (ordered_pair b y) h) by (eapply set_mem_eq_l; [exact E | exact Hp]).
    destruct (Tg b Hb) as [y' Hy'].
    assert (Ey : set_eq y y').
    { eapply set_eq_trans; [apply set_eq_sym; apply (is_function_on_apply D h b y (conj Ph (conj Th Fh)) Hby) |].
      eapply set_eq_trans; [apply set_eq_sym; apply Hpt; exact Hb | apply (is_function_on_apply D g b y' (conj Pg (conj Tg Fg)) Hy')]. }
    eapply set_mem_eq_l; [apply set_eq_sym; eapply set_eq_trans; [exact E | apply ordered_pair_resp; [apply set_eq_refl | exact Ey]] | exact Hy'].
Qed.

Section Functional.
  Variable G : set_group.
  Variable branch : nat -> string -> list aczel_set -> aczel_set -> Prop.
  Hypothesis HG : group_respects G.
  (** The branches are functional, up to equal inputs *)
  Hypothesis Hbranch : forall k c vs vs' r r', list_set_eq vs vs' -> branch k c vs r -> branch k c vs' r' -> set_eq r r'.

(** The eliminator is a function: equal elements at equal parameters have
    equal results. *)
Lemma elim_graph_functional_all :
  (forall k ps v r, elim_graph G branch k ps v r ->
     forall ps' v' r', list_set_eq ps ps' -> set_eq v v' -> elim_graph G branch k ps' v' r' -> set_eq r r') /\
  (forall pre gs vals ihs, arguments_results G branch pre gs vals ihs ->
     forall pre' vals' ihs', list_set_eq pre pre' -> list_set_eq vals vals' -> arguments_results G branch pre' gs vals' ihs' ->
     list_set_eq ihs ihs') /\
  (forall pre a ls ihs, leaves_results G branch pre a ls ihs ->
     forall pre' a' ihs', list_set_eq pre pre' -> set_eq a a' -> leaves_results G branch pre' a' ls ihs' -> list_set_eq ihs ihs') /\
  (forall pre steps l points a ih, leaf_result G branch pre steps l points a ih ->
     (forall d, In (set_leaf_step_domain d) steps -> In (set_leaf_step_domain d) (set_leaf_steps l)) ->
     forall pre' points' a' ih', list_set_eq pre pre' -> list_set_eq points points' -> set_eq a a' ->
     leaf_result G branch pre' steps l points' a' ih' -> set_eq ih ih').
Proof.
  apply (elim_graph_combined_ind G branch
    (fun k ps v r => forall ps' v' r', list_set_eq ps ps' -> set_eq v v' -> elim_graph G branch k ps' v' r' -> set_eq r r')
    (fun pre gs vals ihs => forall pre' vals' ihs', list_set_eq pre pre' -> list_set_eq vals vals' ->
       arguments_results G branch pre' gs vals' ihs' -> list_set_eq ihs ihs')
    (fun pre a ls ihs => forall pre' a' ihs', list_set_eq pre pre' -> set_eq a a' -> leaves_results G branch pre' a' ls ihs' ->
       list_set_eq ihs ihs')
    (fun pre steps l points a ih =>
       (forall d, In (set_leaf_step_domain d) steps -> In (set_leaf_step_domain d) (set_leaf_steps l)) ->
       forall pre' points' a' ih', list_set_eq pre pre' -> list_set_eq points points' -> set_eq a a' ->
       leaf_result G branch pre' steps l points' a' ih' -> set_eq ih ih')).
  - (** a constructor *)
    intros k Mk cs ps vals ihs v r HMk Hcs Ev _ IHa Er ps' v' r' Hps Evv' H'.
    inversion H' as [k0 Mk' cs' ps0 vals' ihs' v0 r0 HMk' Hcs' Ev' Ha' Er']; subst.
    rewrite HMk in HMk'; injection HMk' as <-.
    pose proof (set_eq_trans _ _ _ (set_eq_sym _ _ Ev) (set_eq_trans _ _ _ Evv' Ev')) as E.
    apply ordered_pair_inj in E as [En El]. apply string_code_inj in En.
    pose proof (group_respects_names _ HG _ _ _ _ HMk Hcs Hcs' En) as <-.
    apply list_code_inj in El.
    pose proof (list_set_eq_skipn (List.length (set_group_uniform_types G)) _ _ Hps) as Hns.
    destruct (list_set_eq_app_split _ _ _ _ El (list_set_eq_length _ _ Hns)) as [_ Hvals].
    pose proof (IHa ps' vals' ihs' Hps Hvals Ha') as Hihs.
    eapply Hbranch; [| exact Er | exact Er']. apply list_set_eq_app; [exact Hns | apply list_set_eq_app; assumption].
  - (** no argument *)
    intros pre pre' vals' ihs' _ Hv H'. inversion Hv; subst. inversion H'; subst. constructor.
  - (** a non-recursive argument *)
    intros pre κ type gs a vals ihs _ IH pre' vals' ihs' Hpre Hv H'.
    inversion Hv as [| x y l l' Ha Hl]; subst. inversion H'; subst.
    eapply IH; [apply list_set_eq_app; [exact Hpre | constructor; [exact Ha | constructor]] | exact Hl | eassumption].
  - (** a recursive argument *)
    intros pre type ds target tparams ls gs a vals ihs1 ihs2 _ IHl _ IHa pre' vals' ihs' Hpre Hv H'.
    inversion Hv as [| x y l l' Ha Hl]; subst. inversion H'; subst.
    apply list_set_eq_app.
    + eapply IHl; [exact Hpre | exact Ha | eassumption].
    + eapply IHa; [apply list_set_eq_app; [exact Hpre | apply list_set_eq_refl] | exact Hl | eassumption].
  - (** no leaf *)
    intros pre a pre' a' ihs' _ _ H'. inversion H'; subst. constructor.
  - (** a leaf, then the others *)
    intros pre a l ls ih ihs _ IH1 _ IH2 pre' a' ihs' Hpre Ha H'.
    inversion H'; subst. constructor.
    + eapply IH1; [intros d Hd; exact Hd | exact Hpre | constructor | exact Ha | eassumption].
    + eapply IH2; [exact Hpre | exact Ha | eassumption].
  - (** the end of a leaf *)
    intros pre l points a ih _ IH _ pre' points' a' ih' Hpre Hpts Ha H'.
    inversion H'; subst. eapply IH; [| exact Ha | eassumption].
    apply (group_respects_target_params _ HG). apply list_set_eq_app; assumption.
  - (** through a domain *)
    intros pre d steps l points a ih Hf _ IH Hsteps pre' points' a' ih' Hpre Hpts Ha H'.
    inversion H' as [| ? ? ? ? ? ? ? Hf' Hc' | ]; subst.
    assert (Ed : set_eq (code_carrier (d (pre ++ points))) (code_carrier (d (pre' ++ points'))))
      by (apply code_carrier_resp; apply (group_respects_domains _ HG l d (Hsteps d (or_introl eq_refl)));
          apply list_set_eq_app; assumption).
    apply (is_function_on_ext _ _ _ _ Ed Hf Hf'). intros b Hb.
    eapply IH; [exact Hb | intros d' Hd'; apply Hsteps; right; exact Hd'
               | exact Hpre | apply list_set_eq_app; [exact Hpts | constructor; [apply set_eq_refl | constructor]]
               | apply set_apply_resp; [exact Ha | apply set_eq_refl] | apply Hc'; eapply set_mem_eq_r; [exact Ed | exact Hb]].
  - (** through a field *)
    intros pre f steps l points a ih _ IH Hsteps pre' points' a' ih' Hpre Hpts Ha H'.
    inversion H'; subst. eapply IH; [intros d Hd; apply Hsteps; right; exact Hd | exact Hpre | exact Hpts | | eassumption].
    unfold tuple_field. apply set_apply_resp; [exact Ha | apply set_eq_refl].
Qed.

Corollary elim_graph_functional : forall k ps v r ps' v' r', elim_graph G branch k ps v r ->
    list_set_eq ps ps' -> set_eq v v' -> elim_graph G branch k ps' v' r' -> set_eq r r'.
Proof. intros. eapply (proj1 elim_graph_functional_all); eassumption. Qed.

End Functional.
