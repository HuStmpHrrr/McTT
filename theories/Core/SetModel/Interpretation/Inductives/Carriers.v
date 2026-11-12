(** * The Carriers of a Group of Inductive Types

    At fixed values [us] of the uniform parameters, the carriers of all
    the members of a group, at all values of their non-uniform parameters,
    are one least fixed point: a set of points [member_point k ns v], the
    element [v] of the member [k] at the non-uniform parameters [ns].  The
    operator adds the elements built by a constructor from arguments in
    their sets, a recursive argument in the candidate carrier of its
    target ([shape_set]).  Its elements are drawn from [bound], a set
    closed under the constructors ([Bound.v] gives one in the sort's
    universe), and their parameters from the universe [U]. *)

From Stdlib Require Import String List.
From Mctt.Core.SetModel.Interpretation.Inductives Require Export ElimGraph.
Import ListNotations.

(** The point of the element [v] of the member [k] at the non-uniform
    parameters [ns]. *)
Definition member_point (k : nat) (ns : list aczel_set) (v : aczel_set) : aczel_set :=
  ordered_pair (numeral_set k) (ordered_pair (list_code ns) v).

(** The element a constructor builds: its [con_val], or at a record view
    the tuple of its fields. *)
Definition constructed_element (Mk : set_member) (cs : set_constructor) (ns vals : list aczel_set) : aczel_set :=
  match set_member_record_fields Mk with
  | Some fl => tuple_code (List.combine fl vals)
  | None => con_val (set_constructor_name cs) (ns ++ vals)
  end.

Section Carriers.
  Variable G : set_group.
  (** The values of the uniform parameters *)
  Variable us : list aczel_set.
  (** The set the parameters' values are drawn from *)
  Variable U : aczel_set.
  (** The set the elements are drawn from *)
  Variable bound : aczel_set.

  Let nuniform : nat := List.length (set_group_uniform_types G).

(** The candidate carrier of the member [k] at [ns] in a set of points. *)
Definition candidate_carrier (S : aczel_set) (k : nat) (ns : list aczel_set) : aczel_set :=
  separation_set bound (fun v => set_mem (member_point k ns v) S).

(** The set of a recursive argument over the [domains], at the domain
    points [points] passed so far, into the target in [S]. *)
Fixpoint shape_set (S : aczel_set) (pre : list aczel_set) (domains : list (list aczel_set -> aczel_set)) (target : nat)
    (tparams : list aczel_set -> list aczel_set) (points : list aczel_set) : aczel_set :=
  match domains with
  | nil => candidate_carrier S target (List.skipn nuniform (tparams (pre ++ points)))
  | d :: ds => function_set (code_carrier (d (pre ++ points))) (fun b => shape_set S pre ds target tparams (points ++ [b]))
  end.

(** [arguments_fit S pre gs vals]: the values [vals] are arguments of the
    kinds and types [gs], after the values [pre], recursive ones in [S]. *)
Inductive arguments_fit (S : aczel_set) : list aczel_set -> list set_argument -> list aczel_set -> Prop :=
(** No argument *)
| arguments_fit_nil : forall pre, arguments_fit S pre nil nil
(** A non-recursive argument in its type's carrier *)
| arguments_fit_plain : forall pre κ type gs a vals,
    set_mem a (code_carrier (type pre)) ->
    arguments_fit S (pre ++ [a]) gs vals ->
    arguments_fit S pre (set_argument_plain κ type :: gs) (a :: vals)
(** A recursive argument in its shape's set; no later type depends on it,
    so the values after it see the empty set in its place *)
| arguments_fit_recursive : forall pre type ds target tparams ls gs a vals,
    set_mem a (shape_set S pre ds target tparams nil) ->
    arguments_fit S (pre ++ [empty_set]) gs vals ->
    arguments_fit S pre (set_argument_recursive type ds target tparams ls :: gs) (a :: vals).

(** [v] is built by a constructor of the member [k] at [ns] from
    arguments fitting [S]. *)
#[warnings="-cannot-define-projection"]
Record constructed_from (S : aczel_set) (k : nat) (ns : list aczel_set) (v : aczel_set) : Prop := mk_constructed_from
  { (** The member *)
    constructed_member : set_member
  ; constructed_member_at : List.nth_error (set_group_members G) k = Some constructed_member
    (** The constructor *)
  ; constructed_constructor : set_constructor
  ; constructed_constructor_in : In constructed_constructor (set_member_constructors constructed_member)
    (** The arguments, fitting [S] *)
  ; constructed_arguments : list aczel_set
  ; constructed_fit : arguments_fit S (us ++ ns) (set_constructor_arguments constructed_constructor) constructed_arguments
    (** The element is the constructor's at them *)
  ; constructed_element_eq : set_eq v (constructed_element constructed_member constructed_constructor ns constructed_arguments) }.

(** The points the operator draws from: a member, parameters of [U], an
    element of [bound]. *)
Definition carrier_points : aczel_set :=
  family_set {k : nat | k < List.length (set_group_members G)} (fun k => numeral_set (proj1_sig k)).

(** The operator: the points of the elements built from arguments in
    [S]. *)
Definition carrier_operator (S : aczel_set) : aczel_set :=
  separation_set (product_set carrier_points (product_set U bound))
    (fun t => exists k ns v, set_eq t (member_point k ns v) /\ constructed_from S k ns v).

(** ** Respect of Equality *)

(** What an argument's types need: to respect equality. *)
Definition argument_respects (g : set_argument) : Prop :=
  match g with
  | set_argument_plain _ type => list_function_respects type
  | set_argument_recursive _ ds _ tparams _ => Forall list_function_respects ds /\ list_list_function_respects tparams
  end.

(** Every argument of every constructor respects equality. *)
Definition signature_respects : Prop :=
  forall k Mk cs, List.nth_error (set_group_members G) k = Some Mk -> In cs (set_member_constructors Mk) ->
    Forall argument_respects (set_constructor_arguments cs).

Lemma member_point_resp : forall k ns ns' v v', list_set_eq ns ns' -> set_eq v v' ->
    set_eq (member_point k ns v) (member_point k ns' v').
Proof.
  intros. unfold member_point. apply ordered_pair_resp; [apply set_eq_refl |].
  apply ordered_pair_resp; [apply list_code_resp |]; assumption.
Qed.

Lemma member_point_inj : forall k ns v k' ns' v', set_eq (member_point k ns v) (member_point k' ns' v') ->
    k = k' /\ list_set_eq ns ns' /\ set_eq v v'.
Proof.
  intros * E. apply ordered_pair_inj in E as [Ek E]. apply ordered_pair_inj in E as [En Ev].
  apply numeral_set_inj in Ek. apply list_code_inj in En. auto.
Qed.

Lemma member_point_pred_resp : forall S k ns, respects_set_eq (fun v => set_mem (member_point k ns v) S).
Proof.
  intros S k ns x y E H. eapply set_mem_eq_l; [| exact H]. apply member_point_resp; [apply list_set_eq_refl | exact E].
Qed.

Lemma candidate_carrier_resp : forall S k ns ns', list_set_eq ns ns' -> set_eq (candidate_carrier S k ns) (candidate_carrier S k ns').
Proof.
  intros S k ns ns' E. unfold candidate_carrier.
  apply separation_set_resp; [apply member_point_pred_resp | apply member_point_pred_resp | apply set_eq_refl |].
  intros v _. split; intros H; (eapply set_mem_eq_l; [| exact H]); apply member_point_resp;
    [exact E | apply set_eq_refl | apply list_set_eq_sym; exact E | apply set_eq_refl].
Qed.

Lemma candidate_carrier_mono : forall S S' k ns, set_sub S S' -> set_sub (candidate_carrier S k ns) (candidate_carrier S' k ns).
Proof.
  intros S S' k ns Hs v Hv. unfold candidate_carrier in *.
  apply (set_mem_separation _ _ _ (member_point_pred_resp _ _ _)) in Hv as [Hb Hp].
  apply (set_mem_separation _ _ _ (member_point_pred_resp _ _ _)). split; [exact Hb | apply Hs; exact Hp].
Qed.

Lemma shape_set_resp : forall S ds target tparams, Forall list_function_respects ds -> list_list_function_respects tparams ->
    forall pre pre' points points', list_set_eq pre pre' -> list_set_eq points points' ->
    set_eq (shape_set S pre ds target tparams points) (shape_set S pre' ds target tparams points').
Proof.
  intros S ds target tparams Hds Htp. induction Hds as [| d ds Hd Hds IH]; intros pre pre' points points' Hpre Hpts; cbn [shape_set].
  - apply candidate_carrier_resp. apply list_set_eq_skipn. apply Htp. apply list_set_eq_app; assumption.
  - apply function_set_resp.
    + intros b b' Eb. apply IH; [apply list_set_eq_refl | apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact Eb | constructor]]].
    + intros b b' Eb. apply IH; [apply list_set_eq_refl | apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact Eb | constructor]]].
    + apply code_carrier_resp. apply Hd. apply list_set_eq_app; assumption.
    + intros b _. apply IH; [exact Hpre | apply list_set_eq_app; [exact Hpts | apply list_set_eq_refl]].
Qed.

Lemma shape_set_mono : forall S S' ds target tparams, set_sub S S' -> Forall list_function_respects ds -> list_list_function_respects tparams ->
    forall pre points, set_sub (shape_set S pre ds target tparams points) (shape_set S' pre ds target tparams points).
Proof.
  intros S S' ds target tparams Hs Hds Htp. induction Hds as [| d ds Hd Hds IH]; intros pre points; cbn [shape_set].
  - apply candidate_carrier_mono. exact Hs.
  - apply function_set_mono.
    + intros b b' Eb. apply shape_set_resp; [exact Hds | exact Htp | apply list_set_eq_refl |
        apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact Eb | constructor]]].
    + intros b b' Eb. apply shape_set_resp; [exact Hds | exact Htp | apply list_set_eq_refl |
        apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact Eb | constructor]]].
    + intros b _. apply IH.
Qed.

Lemma arguments_fit_mono : forall S S' pre gs vals, set_sub S S' -> Forall argument_respects gs ->
    arguments_fit S pre gs vals -> arguments_fit S' pre gs vals.
Proof.
  intros S S' pre gs vals Hs Hr H. induction H as [| pre κ type gs a vals Ha H IH | pre type ds target tparams ls gs a vals Ha H IH];
    inversion Hr as [| ? ? Hg Hgs]; subst; econstructor; try eassumption; try (apply IH; assumption).
  destruct Hg as [Hds Htp]. eapply shape_set_mono; eassumption.
Qed.

Lemma arguments_fit_resp : forall S pre pre' gs vals vals', Forall argument_respects gs ->
    list_set_eq pre pre' -> list_set_eq vals vals' -> arguments_fit S pre gs vals -> arguments_fit S pre' gs vals'.
Proof.
  intros S pre pre' gs vals vals' Hr Hpre Hv H. revert pre' vals' Hpre Hv.
  induction H as [pre | pre κ type gs a vals Ha H IH | pre type ds target tparams ls gs a vals Ha H IH]; intros pre' vals' Hpre Hv;
    inversion Hv as [| x y l l' Hxy Hl]; subst; inversion Hr as [| ? ? Hg Hgs]; subst.
  - constructor.
  - constructor.
    + eapply set_mem_eq_l; [exact Hxy |]. eapply set_mem_eq_r; [apply code_carrier_resp; apply Hg; exact Hpre | exact Ha].
    + apply IH; [exact Hgs | apply list_set_eq_app; [exact Hpre | constructor; [exact Hxy | constructor]] | exact Hl].
  - destruct Hg as [Hds Htp]. econstructor.
    + eapply set_mem_eq_l; [exact Hxy |]. eapply set_mem_eq_r; [apply shape_set_resp; [exact Hds | exact Htp | exact Hpre | apply list_set_eq_refl] | exact Ha].
    + apply IH; [exact Hgs | apply list_set_eq_app; [exact Hpre | apply list_set_eq_refl] | exact Hl].
Qed.

Lemma tuple_code_combine_resp : forall fl vals vals', list_set_eq vals vals' ->
    set_eq (tuple_code (List.combine fl vals)) (tuple_code (List.combine fl vals')).
Proof.
  intros fl vals vals' E. unfold tuple_code. apply set_of_list_resp. revert vals vals' E.
  induction fl as [| f fl IH]; intros vals vals' E; [constructor |].
  destruct E as [| x y l l' Hxy Hl]; cbn; constructor; [| apply IH; exact Hl].
  apply ordered_pair_resp; [apply set_eq_refl | exact Hxy].
Qed.

Lemma constructed_element_resp : forall Mk cs ns ns' vals vals', list_set_eq ns ns' -> list_set_eq vals vals' ->
    set_eq (constructed_element Mk cs ns vals) (constructed_element Mk cs ns' vals').
Proof.
  intros. unfold constructed_element. destruct (set_member_record_fields Mk) as [fl |].
  - apply tuple_code_combine_resp. assumption.
  - unfold con_val. apply ordered_pair_resp; [apply set_eq_refl | apply list_code_resp; apply list_set_eq_app; assumption].
Qed.

Section Respecting.
  Hypothesis Hsig : signature_respects.

Lemma constructed_from_resp : forall S k ns ns' v v', list_set_eq ns ns' -> set_eq v v' ->
    constructed_from S k ns v -> constructed_from S k ns' v'.
Proof.
  intros S k ns ns' v v' En Ev [Mk HMk cs Hcs vals Hfit Hel].
  apply (mk_constructed_from S k ns' v' Mk HMk cs Hcs vals).
  - eapply arguments_fit_resp; [exact (Hsig _ _ _ HMk Hcs) | apply list_set_eq_app; [apply list_set_eq_refl | exact En] | apply list_set_eq_refl | exact Hfit].
  - eapply set_eq_trans; [apply set_eq_sym; exact Ev |]. eapply set_eq_trans; [exact Hel |].
    apply constructed_element_resp; [exact En | apply list_set_eq_refl].
Qed.

Lemma constructed_from_mono : forall S S' k ns v, set_sub S S' -> constructed_from S k ns v -> constructed_from S' k ns v.
Proof.
  intros S S' k ns v Hs [Mk HMk cs Hcs vals Hfit Hel].
  apply (mk_constructed_from S' k ns v Mk HMk cs Hcs vals); [| exact Hel].
  eapply arguments_fit_mono; [exact Hs | exact (Hsig _ _ _ HMk Hcs) | exact Hfit].
Qed.

Lemma carrier_operator_pred_resp : forall S,
    respects_set_eq (fun t => exists k ns v, set_eq t (member_point k ns v) /\ constructed_from S k ns v).
Proof. intros S x y E [k [ns [v [Ht Hc]]]]. exists k, ns, v. split; [eapply set_eq_trans; [apply set_eq_sym; exact E | exact Ht] | exact Hc]. Qed.

(** The points the carriers are drawn from. *)
Definition carrier_ambient : aczel_set := product_set carrier_points (product_set U bound).

Lemma carrier_operator_monotone : monotone_operator carrier_ambient carrier_operator.
Proof.
  intros S S' _ _ Hs t Ht. unfold carrier_operator in *.
  apply (set_mem_separation _ _ _ (carrier_operator_pred_resp _)) in Ht as [Hamb [k [ns [v [Et Hc]]]]].
  apply (set_mem_separation _ _ _ (carrier_operator_pred_resp _)). split; [exact Hamb |].
  exists k, ns, v. split; [exact Et | eapply constructed_from_mono; eassumption].
Qed.

Lemma carrier_operator_bounded : bounded_operator carrier_ambient carrier_operator.
Proof.
  intros S _ t Ht. unfold carrier_operator in Ht.
  apply (set_mem_separation _ _ _ (carrier_operator_pred_resp _)) in Ht as [Hamb _]. exact Hamb.
Qed.

(** The least fixed point of the operator: the carriers of all members. *)
Definition carrier_fixed_point : aczel_set := least_fixed_point_set carrier_ambient carrier_operator.

(** The carrier of the member [k] at the non-uniform parameters [ns]. *)
Definition member_carrier (k : nat) (ns : list aczel_set) : aczel_set := candidate_carrier carrier_fixed_point k ns.

(** A constructed element of the bound, at parameters of [U], is in its
    member's carrier. *)
Lemma member_carrier_intro : forall k ns v, set_mem (list_code ns) U -> set_mem v bound ->
    constructed_from carrier_fixed_point k ns v -> set_mem v (member_carrier k ns).
Proof.
  intros k ns v HU Hb Hc. unfold member_carrier, candidate_carrier.
  apply (set_mem_separation _ _ _ (member_point_pred_resp _ _ _)). split; [exact Hb |].
  apply (least_fixed_point_closed carrier_ambient carrier_operator carrier_operator_monotone carrier_operator_bounded).
  unfold carrier_operator. apply (set_mem_separation _ _ _ (carrier_operator_pred_resp _)). split.
  - apply set_mem_product. exists (numeral_set k), (ordered_pair (list_code ns) v). split.
    + destruct Hc as [Mk HMk _ _ _ _ _]. assert (Hk : k < List.length (set_group_members G)) by (apply nth_error_Some; congruence).
      exists (exist _ k Hk). apply set_eq_refl.
    + split; [apply set_mem_product; exists (list_code ns), v; split; [exact HU | split; [exact Hb | apply set_eq_refl]] | apply set_eq_refl].
  - exists k, ns, v. split; [apply set_eq_refl | exact Hc].
Qed.

(** An element of a member's carrier is constructed from the carriers. *)
Lemma member_carrier_inversion : forall k ns v, set_mem v (member_carrier k ns) -> constructed_from carrier_fixed_point k ns v.
Proof.
  intros k ns v Hv. unfold member_carrier, candidate_carrier in Hv.
  apply (set_mem_separation _ _ _ (member_point_pred_resp _ _ _)) in Hv as [_ Hp].
  apply (least_fixed_point_unfold carrier_ambient carrier_operator carrier_operator_monotone carrier_operator_bounded) in Hp.
  unfold carrier_operator in Hp. apply (set_mem_separation _ _ _ (carrier_operator_pred_resp _)) in Hp as [_ [k' [ns' [v' [Et Hc]]]]].
  apply member_point_inj in Et as [<- [En Ev]].
  eapply constructed_from_resp; [apply list_set_eq_sym; exact En | apply set_eq_sym; exact Ev | exact Hc].
Qed.

End Respecting.

End Carriers.
