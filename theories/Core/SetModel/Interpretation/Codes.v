(** * The Codes of the Types of McTT

    Each type former has its tag; a code stores what the interpretation
    reads back from it (a Π's domain and codomains) and never a large
    parameter, so that a type of a universe has its code in that universe.
    A proposition's code stores nothing ([prop_code]): an impredicative
    [∀ (X : Type@5). X → X] would otherwise carry the code of [Type@5].

    [cond φ x] is [x] when [φ] holds and the empty set when it fails,
    without deciding [φ]. *)

From Mctt.Core.SetModel.Sets Require Export Fixpoints WSets.
From Mctt.Core.SetModel Require Export Tower.

(** ** Tags *)

(** The tag of a [Π] of a relevant codomain. *)
Definition pi_tag : nat := 1.
(** The tag of a universe [Type@{l}] or [Typeω@i]. *)
Definition universe_tag : nat := 2.
(** The tag of a type of levels [Level@n]. *)
Definition level_type_tag : nat := 3.
(** The tag of the sort of the types of levels [LevelSort]. *)
Definition level_sort_tag : nat := 4.
(** The tag of an inductive type. *)
Definition inductive_tag : nat := 5.
(** The tag of a record type. *)
Definition record_tag : nat := 6.
(** The tag of the universe of propositions [Prop]. *)
Definition prop_universe_tag : nat := 7.

(** ** Conditional Sets *)

(** [x] when [φ] holds, the empty set when it fails. *)
Definition cond (φ : Prop) (x : aczel_set) : aczel_set := union_set (separation_set (singleton_set x) (fun _ => φ)).

Lemma cond_true : forall (φ : Prop) x, φ -> set_eq (cond φ x) x.
Proof.
  intros φ x H. unfold cond. apply union_set_const.
  - exists x. apply set_mem_separation; [intros ? ? _ Hφ; exact Hφ |]. split; [apply set_mem_singleton; apply set_eq_refl | exact H].
  - intros w Hw. apply set_mem_separation in Hw as [Hw _]; [| intros ? ? _ Hφ; exact Hφ]. apply set_mem_singleton in Hw. exact Hw.
Qed.

Lemma cond_false : forall (φ : Prop) x, ~ φ -> set_eq (cond φ x) empty_set.
Proof.
  intros φ x H. apply set_eq_intro; intros z Hz; [| exfalso; exact (set_mem_empty _ Hz)].
  apply set_mem_union in Hz as [w [Hw _]]. apply set_mem_separation in Hw as [_ Hφ]; [| intros ? ? _ Hφ; exact Hφ].
  exfalso; exact (H Hφ).
Qed.

Lemma set_mem_cond : forall (φ : Prop) x z, set_mem z (cond φ x) <-> φ /\ set_mem z x.
Proof.
  intros φ x z. unfold cond. rewrite set_mem_union. split.
  - intros [w [Hw Hz]]. apply set_mem_separation in Hw as [Hw Hφ]; [| intros ? ? _ Hp; exact Hp].
    apply set_mem_singleton in Hw. split; [exact Hφ | eapply set_mem_eq_r; [exact Hw | exact Hz]].
  - intros [Hφ Hz]. exists x. split; [| exact Hz].
    apply set_mem_separation; [intros ? ? _ Hp; exact Hp |]. split; [apply set_mem_singleton; apply set_eq_refl | exact Hφ].
Qed.

Lemma cond_resp : forall (φ ψ : Prop) x y, (φ <-> ψ) -> set_eq x y -> set_eq (cond φ x) (cond ψ y).
Proof.
  intros * Hφ E. unfold cond. apply union_set_resp. apply separation_set_resp;
    [intros ? ? _ H; exact H | intros ? ? _ H; exact H | apply singleton_set_resp; exact E | intros _ _; exact Hφ].
Qed.

(** Conditional sets at equivalent conditions, equal where they hold. *)
Lemma cond_resp_cond : forall (φ ψ : Prop) x y, (φ <-> ψ) -> (φ -> set_eq x y) -> set_eq (cond φ x) (cond ψ y).
Proof.
  intros * Hφ E. apply set_eq_intro; intros z Hz; apply set_mem_cond in Hz as [Hc Hz]; apply set_mem_cond.
  - split; [apply Hφ; exact Hc | eapply set_mem_eq_r; [apply E; exact Hc | exact Hz]].
  - split; [apply Hφ; exact Hc | eapply set_mem_eq_r; [apply set_eq_sym; apply E; apply Hφ; exact Hc | exact Hz]].
Qed.

(** ** Π and ∀ *)

(** The [Π] over the domain code [dom] into the codomain codes [F]: its
    elements are the dependent functions. *)
Definition pi_code (dom : aczel_set) (F : aczel_set -> aczel_set) : aczel_set :=
  type_code pi_tag (ordered_pair dom (graph_set (code_carrier dom) F))
    (function_set (code_carrier dom) (fun x => code_carrier (F x))).

(** The domain code of a [Π] code. *)
Definition pi_domain (C : aczel_set) : aczel_set := pair_first (code_datum C).

(** The codomain code of a [Π] code at an argument. *)
Definition pi_codomain (C : aczel_set) (x : aczel_set) : aczel_set := set_apply (pair_second (code_datum C)) x.

(** The impredicative quantification over the domain code [dom] of the
    proposition codes [F]: true when every [F x] is. *)
Definition forall_code (dom : aczel_set) (F : aczel_set -> aczel_set) : aczel_set :=
  prop_code (forall x, set_mem x (code_carrier dom) -> prop_true (F x)).

Lemma pi_codomain_pi_code : forall dom F x, respects_set_eq_fun F -> set_mem x (code_carrier dom) ->
    set_eq (pi_codomain (pi_code dom F) x) (F x).
Proof.
  intros dom F x HF Hx. unfold pi_codomain, pi_code.
  eapply set_eq_trans; [apply set_apply_resp; [| apply set_eq_refl] |].
  - eapply set_eq_trans; [apply pair_second_resp; apply code_datum_type_code | apply pair_second_ordered_pair].
  - apply set_apply_graph; assumption.
Qed.

Lemma pi_domain_pi_code : forall dom F, set_eq (pi_domain (pi_code dom F)) dom.
Proof.
  intros. unfold pi_domain, pi_code. eapply set_eq_trans; [apply pair_first_resp; apply code_datum_type_code | apply pair_first_ordered_pair].
Qed.

Lemma pi_code_resp_on : forall dom dom' F G, set_eq dom dom' -> respects_across (code_carrier dom) F G ->
    set_eq (pi_code dom F) (pi_code dom' G).
Proof.
  intros * Ed H. pose proof (code_carrier_resp _ _ Ed) as Ec. unfold pi_code. apply type_code_resp.
  - apply ordered_pair_resp; [exact Ed | apply graph_set_resp_on; assumption].
  - apply function_set_resp_on; [exact Ec |]. intros x x' Hx E. apply code_carrier_resp. apply H; assumption.
Qed.

Lemma forall_code_resp_on : forall dom dom' F G, set_eq dom dom' -> respects_across (code_carrier dom) F G ->
    set_eq (forall_code dom F) (forall_code dom' G).
Proof.
  intros * Ed H. pose proof (code_carrier_resp _ _ Ed) as Ec. unfold forall_code. apply prop_code_eq. split.
  - intros HF x Hx. assert (HxS : set_mem x (code_carrier dom)) by (eapply set_mem_eq_r; [apply set_eq_sym; exact Ec | exact Hx]).
    eapply prop_true_resp; [apply H; [exact HxS | apply set_eq_refl] | apply HF; exact HxS].
  - intros HG x Hx. eapply prop_true_resp; [apply set_eq_sym; apply H; [exact Hx | apply set_eq_refl] |].
    apply HG. eapply set_mem_eq_r; [exact Ec | exact Hx].
Qed.

(** A [Π] over a member of a universe of sets into members is a member. *)
Lemma grothendieck_pi_code : forall V dom F, grothendieck V -> set_mem dom V -> respects_on (code_carrier dom) F ->
    (forall x, set_mem x (code_carrier dom) -> set_mem (F x) V) -> set_mem (pi_code dom F) V.
Proof.
  intros * HV Hd HF HFx. set (G := restrict_fun (code_carrier dom) F).
  assert (HG : respects_set_eq_fun G) by apply restrict_fun_resp.
  assert (HGx : forall x, set_mem x (code_carrier dom) -> set_mem (G x) V)
    by (intros x Hx; eapply set_mem_eq_l; [apply set_eq_sym; apply restrict_fun_agree; [exact HF | exact Hx] | apply HFx; exact Hx]).
  assert (Hc : set_mem (code_carrier dom) V) by (apply (grothendieck_code_carrier _ HV); exact Hd).
  eapply set_mem_eq_l.
  - apply pi_code_resp_on with (G := F); [apply set_eq_refl |]. intros x x' Hx E.
    eapply set_eq_trans; [apply restrict_fun_agree; [exact HF | exact Hx] |]. apply HF; assumption.
  - unfold pi_code. apply (grothendieck_type_code _ HV).
    + apply (grothendieck_ordered_pair _ HV); [exact Hd | apply (grothendieck_graph _ HV); assumption].
    + apply (grothendieck_function _ HV); [intros x y E; apply code_carrier_resp; apply HG; exact E | exact Hc |].
      intros x Hx. apply (grothendieck_code_carrier _ HV). apply HGx. exact Hx.
Qed.

Lemma pi_code_relevant : forall dom F, is_relevant_code (pi_code dom F).
Proof. intros. do 3 eexists. split; [apply set_eq_refl | discriminate]. Qed.

Lemma forall_code_prop : forall dom F, is_prop_code (forall_code dom F).
Proof. intros. eexists. apply set_eq_refl. Qed.

(** ** Inductive and Record Types *)

(** An inductive type whose elements are [carrier]: no datum, so that no
    parameter, small or large, is stored. *)
Definition inductive_code (carrier : aczel_set) : aczel_set := type_code inductive_tag empty_set carrier.

(** A record type whose elements are [carrier], with no datum. *)
Definition record_code (carrier : aczel_set) : aczel_set := type_code record_tag empty_set carrier.

(** ** Universes, Prop and Levels *)

(** The universe at the index set [l] whose universe of sets is [U]: its
    elements are the relevant codes of [U]. *)
Definition universe_code (l U : aczel_set) : aczel_set := type_code universe_tag l (separation_set U is_relevant_code).

(** The universe of propositions: its elements are the proposition codes. *)
Definition prop_universe_code : aczel_set := type_code prop_universe_tag empty_set prop_codes_set.

(** The type of levels [Level@n]: the ordinals [ω·a + b] with [a ≤ n]. *)
Definition level_type_code (n : nat) : aczel_set :=
  type_code level_type_tag (numeral_set n)
    (family_set {o : nat * nat | fst o <= n} (fun o => pair_ordinal_set (proj1_sig o))).

(** A type of levels is a member of every universe of sets. *)
Lemma grothendieck_level_type_code : forall V n, grothendieck V -> set_mem (level_type_code n) V.
Proof.
  intros V n HV. unfold level_type_code. apply (grothendieck_type_code _ HV); [apply (grothendieck_numeral _ HV) |].
  apply (grothendieck_sub _ HV omega_square_set); [apply (grothendieck_omega_square _ HV) |].
  intros z [[o Ho] Ez]. cbn in Ez. eapply set_mem_eq_l; [apply set_eq_sym; exact Ez |].
  exact (pair_ordinal_set_below_large o 0).
Qed.

(** A code is a type of levels: a [Level@n], or a [Π] between types of
    levels. *)
Inductive is_level_type_code : aczel_set -> Prop :=
(** [Level@n] *)
| is_level_type_code_level : forall C n, set_eq C (level_type_code n) -> is_level_type_code C
(** A [Π] from a type of levels into types of levels *)
| is_level_type_code_pi : forall C dom F, respects_set_eq_fun F -> set_eq C (pi_code dom F) -> is_level_type_code dom ->
    (forall x, set_mem x (code_carrier dom) -> is_level_type_code (F x)) -> is_level_type_code C.

Lemma is_level_type_code_resp : respects_set_eq is_level_type_code.
Proof.
  intros x y E H. destruct H as [C n HC | C dom F HF HC Hd Hc].
  - eapply is_level_type_code_level. eapply set_eq_trans; [apply set_eq_sym; exact E | exact HC].
  - eapply is_level_type_code_pi; [exact HF | eapply set_eq_trans; [apply set_eq_sym; exact E | exact HC] | exact Hd | exact Hc].
Qed.

(** The sort of the types of levels, [LevelSort], in the universe of sets
    [U]: its elements are the codes of types of levels of [U]. *)
Definition level_sort_code (U : aczel_set) : aczel_set :=
  type_code level_sort_tag empty_set (separation_set U is_level_type_code).
