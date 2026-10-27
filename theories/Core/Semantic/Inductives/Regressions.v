(** * Regressions for Mutual and Nested Inductive Types

    Closed lemmas about the groups that broke earlier designs.

    - [T := t : C T → T] with [C (B) := mk : Sigma (C B) (λ_. B) → C B]:
      [T] nests through a container that has a view of its own, and the
      inherited view [Sigma (C T) (λ_. T)] nests back into [T] at an
      argument that is not recursive in [C]'s group.  [T] is a type of the
      model ([t_over_c_in_model]).
    - [T := t : Rose T → T], [Rose] with its view [List (Rose A)]: the
      same through a container with a view of its own
      ([t_over_rose_in_model]).
    - [C (A) : A → Type | mk (a : A) : C A a ; T := t (x : T) (c : C T x) : T]:
      the view [C T] would have a non-uniform parameter of type [T], which
      mentions the group, so [view_nps] has no derivation
      ([view_nps_self_param_absurd]); and [run_cmd_ind_case] rejects the
      declaration, already at [c], whose type mentions the recursive
      argument [x] ([run_cmd_ind_self_param_rejected]).

    The model lemmas assume only the lookups of the groups involved: the
    groups' telescopes are abstract, and no well-formedness of the global
    context is used. *)

From Stdlib Require Import Lia List PeanoNat String Relation_Definitions RelationClasses.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Inductives Require Import Inductives Group.
From Mctt.Core.Semantic Require Import PER.Definitions PER.CoreTactics PER NbE.
From Mctt.Core.Syntactic.System Require Import Command.
Import Domain_Notations.
#[local] Open Scope list_scope.
#[local] Open Scope string_scope.

(** ** Concrete Groups

    One step of a case analysis on a concrete group: a member, a
    constructor, a container found by its lookup, a head. *)
Ltac grp_case_step :=
  match goal with
  | H : ind_member _ _ = Some _ |- _ => unfold ind_member in H
  | H : ind_con _ _ = Some _ |- _ => unfold ind_con in H
  | H : List.nth_error (ind_members ?D) _ = Some _ |- _ => unfold D in H; cbn [ind_members] in H
  | H : List.nth_error (_ :: _) ?k = Some _ |- _ => is_var k; destruct k
  | H : List.nth_error (_ :: _) _ = Some _ |- _ => progress cbn [List.nth_error] in H
  | H : List.nth_error nil ?k = Some _ |- _ => destruct k; discriminate H
  | H : Some ?x = Some ?y |- _ => is_var y; injection H; clear H; intros; subst y
  | H : Some ?x = Some ?y |- _ => is_var x; injection H; clear H; intros; subst x
  | H : None = Some _ |- _ => discriminate H
  | H : ind_lookup ?G ?S ?pq = Some ?D, HL : ind_lookup ?G ?S ?pq = Some ?D0 |- _ =>
      is_var D; assert_fails (is_var D0); rewrite HL in H
  | H : im_head _ = _ |- _ => cbn [im_head] in H; first [ discriminate H | injection H; clear H; intros; subst ]
  | H : cons_lookup _ _ = Some _ |- _ => progress cbn [cons_lookup im_cons] in H
  | H : (if String.eqb ?c ?s then _ else _) = Some _ |- _ =>
      let Ec := fresh "Ec" in
      destruct (String.eqb_spec c s) as [Ec | Ec];
        [ first [ subst c | discriminate Ec | clear Ec ] | first [ exact (False_ind _ (Ec eq_refl)) | idtac ] ]
  | H : _ = _ |- _ => discriminate H
  end.

Ltac grp_cases := repeat grp_case_step.

(** The components of a group without non-uniform parameters,
    non-recursive arguments or domains of shapes: each premise about one
    of them is vacuous. *)
Ltac grp_vacuous_step :=
  first [ grp_case_step
        | match goal with
          | H : List.nth_error (List.rev _) _ = Some _ |- _ => progress cbn [List.rev List.app im_nparams] in H
          | H : List.nth_error (cargs_nonrec _) _ = Some _ |- _ => progress cbn [cargs_nonrec] in H
          | H : List.nth_error (ptyp_doms _) _ = Some _ |- _ => progress cbn [ptyp_doms] in H
          | H : (_ :: _) = app ?l _ |- _ => is_var l; destruct l; cbn [List.app] in H
          | H : nil = app ?l _ |- _ => is_var l; destruct l; cbn [List.app] in H
          | H : (_ :: _) = (_ :: _) |- _ => injection H; clear H; intros; subst
          end ].

Ltac grp_vacuous := repeat grp_vacuous_step.

(** A view's rank above the members it nests through, along every leaf
    path not of its container's: in a group without record views, each
    argument has one leaf path, the container's. *)
Ltac grp_rank_nest :=
  cbn; repeat split; try lia;
  intros ? Hin Hn; cbn in Hin; repeat (destruct Hin as [<- | Hin]; [ vm_compute in Hn; discriminate Hn |]);
  contradiction.

(** A group without record views has its record views after every other
    member. *)
Ltac grp_suffix_none := intros ? ? ?; grp_cases; vm_compute; (split; intros Hx; [ discriminate Hx | lia ]).

(** A group without record views: the record views' facts hold
    vacuously. *)
Ltac grp_rstruct_none :=
  constructor; [ intros * ? ?; grp_cases | intros * ? ?; grp_cases | intros * ? ?; grp_cases | grp_suffix_none
               | hnf; intros * ? ?; grp_cases ].

(** A declared member, without parameters, of a group of that kind: its
    clause of the model, all but [grp_tele_ass]. *)
Ltac grp_in_model Hl Hta G :=
  match goal with |- DF d_ind ?p ?k nil ≈ _ ∈ _ ↘ _ => change (d_ind p k nil) with (d_ind p k (nil ++ nil)) end;
  basic_per_univ_elem_econstructor;
  try exact Hl; try exact Hta; try reflexivity;
  try (intros ?s; exists nil; split; constructor);
  try (red; intros; grp_vacuous; fail);
  try (cbn; split; [ reflexivity | exact I ]);
  try (constructor; intros; grp_vacuous;
       (econstructor; [ cbn; constructor | cbn; constructor | unfold ntele_rel, ind_member, G; cbn; split; [ reflexivity | exact I ] ])).

(** No non-uniform parameter, no non-recursive argument, no domain of a
    shape: the components' relations are never asked. *)
Definition no_nparams_rel : nat -> nat -> list domain -> relation domain := fun _ _ _ _ _ => False.
(** The empty relation of non-recursive arguments. *)
Definition no_args_rel : nat -> list domain -> string -> nat -> list domain -> relation domain := fun _ _ _ _ _ _ _ => False.
(** The empty relation of shape domains. *)
Definition no_doms_rel : nat -> list domain -> exp -> relation domain := fun _ _ _ _ _ => False.

(** ** [T] Nested Through a Container with a View

    [Sigma (A : TA) (P : TP) := pair (a : A) (b : P a)];
    [C (B : TB) := mk : Sigma (C B) (λ_. B) → C B], whose group has the
    view [Sigma (C B) (λ_. B)], where [b : B] is not recursive;
    [T := t : C T → T], whose group has the views [C T] and, inherited,
    [Sigma (C T) (λ_. T)], where [b : T] is recursive. *)

Section ChainedViews.
  Context {GC : GCtx}.
  Variables (pS pC pT pmS pmC pmT : qname) (TA TP TB SS SC ST : exp).

  (** The filed group of [Sigma]: one declared member, no view. *)
  Definition sigma_group : ind_decl :=
    mk_ind (ce_ass TP :: ce_ass TA :: nil) SS
      (mk_imember (mh_decl pmS) nil (("pair", ca_arg (a_var 1) :: ca_arg (a_app (a_var 1) (a_var 0)) :: nil) :: nil) :: nil).

  (** The instance [Sigma (C B) (λ_. B')] of [Sigma]'s uniform
      parameters. *)
  Definition sigma_inst (B B' : exp) : list exp := a_app (a_ind pC 0) B :: a_fn (a_app (a_ind pC 0) B) B' :: nil.

  (** The filed group of [C]: [C] itself, and the view
      [Sigma (C B) (λ_. B)]. *)
  Definition c_group : ind_decl :=
    mk_ind (ce_ass TB :: nil) SC
      (mk_imember (mh_decl pmC) nil (("mk", ca_rec (pt_self 1 nil) :: nil) :: nil)
       :: mk_imember (mh_view pS 0 (sigma_inst (a_var 0) (a_var 1)) (1 :: nil)) nil
            (("pair", ca_rec (pt_self 0 nil) :: ca_arg (a_var 0) :: nil) :: nil)
       :: nil).

  (** The filed group of [T]: [T], the view [C T], and the inherited view
      [Sigma (C T) (λ_. T)]. *)
  Definition t_over_c_group : ind_decl :=
    mk_ind nil ST
      (mk_imember (mh_decl pmT) nil (("t", ca_rec (pt_self 1 nil) :: nil) :: nil)
       :: mk_imember (mh_view pC 0 (a_ind pT 0 :: nil) (1 :: 2 :: nil)) nil (("mk", ca_rec (pt_self 2 nil) :: nil) :: nil)
       :: mk_imember (mh_view pS 0 (sigma_inst (a_ind pT 0) (a_ind pT 0)) (2 :: nil)) nil
            (("pair", ca_rec (pt_self 1 nil) :: ca_rec (pt_self 0 nil) :: nil) :: nil)
       :: nil).

  Hypothesis HlS : ind_lookup gc_deps gc_stack pS = Some sigma_group.
  Hypothesis HlC : ind_lookup gc_deps gc_stack pC = Some c_group.
  Hypothesis HlT : ind_lookup gc_deps gc_stack pT = Some t_over_c_group.

  (** A view's rank is its index: [C T] nests through [T], and
      [Sigma (C T) (λ_. T)] through [C T] and [T]. *)
  Lemma t_over_c_rank : view_rank_ok gc_deps gc_stack t_over_c_group (fun k => k).
  Proof.
    constructor.
    - intros k Mk pm Hk Hh; grp_cases; reflexivity.
    - intros * Hk Hh Hl Hi' Hv HMv Hc' Hc; grp_cases.
      all: grp_rank_nest.
    - intros * Hk Hh; grp_cases.
  Qed.

  Lemma t_over_c_vwrap : forall k Mk qc k' Is vm, ind_member t_over_c_group k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      exists D', ind_lookup gc_deps gc_stack qc = Some D' /\ vwrap_ok t_over_c_group D' vm.
  Proof.
    intros * Hk Hh; grp_cases.
    all: eexists; split; [ eassumption |].
    all: constructor; [ reflexivity |].
    all: intros i' Mi' v Hi' Hv; grp_cases.
    all: eexists; split; [ reflexivity | split; [ reflexivity | split; [ reflexivity |] ] ].
    all: intros c gs' gs Hin Hc; cbn in Hin; destruct Hin as [Hin | []]; injection Hin; intros; subst; grp_cases.
    all: cbn; repeat split.
  Qed.

  Lemma t_over_c_coherent : view_maps_coherent gc_deps gc_stack t_over_c_group.
  Proof. unfold view_maps_coherent; intros * Hk Hh Hl Hi' Hv HMv HMh; grp_cases; cbn; reflexivity. Qed.

  Lemma t_over_c_images : forall v Mv qc kc Is vm Dq i' Mi', ind_member t_over_c_group v = Some Mv ->
      im_head Mv = mh_view qc kc Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq -> ind_member Dq i' = Some Mi' ->
      view_member_image t_over_c_group qc Is vm i' Mi'.
  Proof.
    intros * Hv Hh Hl Hi'; grp_cases.
    all: eapply mk_view_member_image; [ reflexivity | reflexivity | reflexivity | cbn; eauto ].
  Qed.

  Lemma t_over_c_plen : forall k Mk c gs, ind_member t_over_c_group k = Some Mk -> In (c, gs) (im_cons Mk) ->
      cargs_plen t_over_c_group gs.
  Proof.
    intros * Hk Hin; grp_cases; cbn in Hin; destruct Hin as [Hin | []]; injection Hin; intros; subst.
    all: intros gs1 t0 gs2 Heq; destruct gs1 as [| g1 [| g2 gs1]]; cbn in Heq; injection Heq; intros; subst;
      try (destruct gs1; discriminate).
    all: try discriminate.
    all: eexists; split; reflexivity.
  Qed.

  Lemma t_over_c_container_plen : forall v Mv qc kc Is vm Dq i' Mi' c gs', ind_member t_over_c_group v = Some Mv ->
      im_head Mv = mh_view qc kc Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq -> ind_member Dq i' = Some Mi' ->
      In (c, gs') (im_cons Mi') -> cargs_plen Dq gs'.
  Proof.
    intros * Hv Hh Hl Hi' Hin; grp_cases; cbn in Hin; destruct Hin as [Hin | []]; injection Hin; intros; subst.
    all: intros gs1 t0 gs2 Heq; destruct gs1 as [| g1 [| g2 gs1]]; cbn in Heq; injection Heq; intros; subst;
      try (destruct gs1; discriminate).
    all: try discriminate.
    all: eexists; split; reflexivity.
  Qed.

  Lemma t_over_c_tele_ass : grp_tele_ass t_over_c_group.
  Proof.
    constructor.
    - constructor.
    - intros * Hk; grp_cases; constructor.
    - intros * Hv Hh; grp_cases.
      all: do 2 eexists; split; [ eassumption | split; [ reflexivity | split; reflexivity ] ].
    - exists (fun k => k); exact t_over_c_rank.
    - exact t_over_c_vwrap.
    - exact t_over_c_coherent.
    - exact t_over_c_images.
    - exact t_over_c_plen.
    - exact t_over_c_container_plen.
    - grp_rstruct_none.
    - intros * Hv Hh Hl; grp_cases; grp_suffix_none.
    - intros * Hv Hh Hl; grp_cases; grp_rstruct_none.
  Qed.

  (** [T] is a type of the model, its elements the group's relation. *)
  Theorem t_over_c_in_model : forall i,
      DF d_ind pT 0 nil ≈ d_ind pT 0 nil ∈ per_univ_elem i ↘
        grp_rel pT t_over_c_group nil no_nparams_rel no_args_rel no_doms_rel 0 nil nil nil nil.
  Proof. intros i; grp_in_model HlT t_over_c_tele_ass t_over_c_group. Qed.

End ChainedViews.

(** ** [T] Nested Through [Rose]

    [List (A : TL) := nil | cons (h : A) (t : List A)];
    [Rose (A : TR) := node (x : A) (ts : List (Rose A))], whose group has
    the view [List (Rose A)];
    [T := t : Rose T → T], whose group has the views [Rose T] and,
    inherited, [List (Rose T)]; [x : T] is recursive in [Rose T]. *)

Section RoseViews.
  Context {GC : GCtx}.
  Variables (pL pR pT pmL pmR pmT : qname) (TL TR SL SR ST : exp).

  (** The filed group of [List]: one declared member, no view. *)
  Definition list_group : ind_decl :=
    mk_ind (ce_ass TL :: nil) SL
      (mk_imember (mh_decl pmL) nil (("nil", nil) :: ("cons", ca_arg (a_var 0) :: ca_rec (pt_self 0 nil) :: nil) :: nil)
       :: nil).

  (** The filed group of [Rose]: [Rose], and the view [List (Rose A)]. *)
  Definition rose_group : ind_decl :=
    mk_ind (ce_ass TR :: nil) SR
      (mk_imember (mh_decl pmR) nil (("node", ca_arg (a_var 0) :: ca_rec (pt_self 1 nil) :: nil) :: nil)
       :: mk_imember (mh_view pL 0 (a_app (a_ind pR 0) (a_var 0) :: nil) (1 :: nil)) nil
            (("nil", nil) :: ("cons", ca_rec (pt_self 0 nil) :: ca_rec (pt_self 1 nil) :: nil) :: nil)
       :: nil).

  (** The filed group of [T]: [T], the view [Rose T], and the inherited
      view [List (Rose T)]. *)
  Definition t_over_rose_group : ind_decl :=
    mk_ind nil ST
      (mk_imember (mh_decl pmT) nil (("t", ca_rec (pt_self 1 nil) :: nil) :: nil)
       :: mk_imember (mh_view pR 0 (a_ind pT 0 :: nil) (1 :: 2 :: nil)) nil
            (("node", ca_rec (pt_self 0 nil) :: ca_rec (pt_self 2 nil) :: nil) :: nil)
       :: mk_imember (mh_view pL 0 (a_app (a_ind pR 0) (a_ind pT 0) :: nil) (2 :: nil)) nil
            (("nil", nil) :: ("cons", ca_rec (pt_self 1 nil) :: ca_rec (pt_self 2 nil) :: nil) :: nil)
       :: nil).

  Hypothesis HlL : ind_lookup gc_deps gc_stack pL = Some list_group.
  Hypothesis HlR : ind_lookup gc_deps gc_stack pR = Some rose_group.
  Hypothesis HlT : ind_lookup gc_deps gc_stack pT = Some t_over_rose_group.

  (** A view's rank is its index: [Rose T] nests through [T] at [x], and
      [List (Rose T)] through [Rose T] at [h]. *)
  Lemma t_over_rose_rank : view_rank_ok gc_deps gc_stack t_over_rose_group (fun k => k).
  Proof.
    constructor.
    - intros k Mk pm Hk Hh; grp_cases; reflexivity.
    - intros * Hk Hh Hl Hi' Hv HMv Hc' Hc; grp_cases.
      all: grp_rank_nest.
    - intros * Hk Hh; grp_cases.
  Qed.

  Lemma t_over_rose_vwrap : forall k Mk qc k' Is vm, ind_member t_over_rose_group k = Some Mk ->
      im_head Mk = mh_view qc k' Is vm ->
      exists D', ind_lookup gc_deps gc_stack qc = Some D' /\ vwrap_ok t_over_rose_group D' vm.
  Proof.
    intros * Hk Hh; grp_cases.
    all: eexists; split; [ eassumption |].
    all: constructor; [ reflexivity |].
    all: intros i' Mi' v Hi' Hv; grp_cases.
    all: eexists; split; [ reflexivity | split; [ reflexivity | split; [ reflexivity |] ] ].
    all: intros c gs' gs Hin Hc; cbn in Hin; repeat destruct Hin as [Hin | Hin]; try contradiction;
      injection Hin; intros; subst; grp_cases.
    all: cbn; repeat split.
  Qed.

  Lemma t_over_rose_coherent : view_maps_coherent gc_deps gc_stack t_over_rose_group.
  Proof. unfold view_maps_coherent; intros * Hk Hh Hl Hi' Hv HMv HMh; grp_cases; cbn; reflexivity. Qed.

  Lemma t_over_rose_images : forall v Mv qc kc Is vm Dq i' Mi', ind_member t_over_rose_group v = Some Mv ->
      im_head Mv = mh_view qc kc Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq -> ind_member Dq i' = Some Mi' ->
      view_member_image t_over_rose_group qc Is vm i' Mi'.
  Proof.
    intros * Hv Hh Hl Hi'; grp_cases.
    all: eapply mk_view_member_image; [ reflexivity | reflexivity | reflexivity | cbn; eauto ].
  Qed.

  Lemma t_over_rose_plen : forall k Mk c gs, ind_member t_over_rose_group k = Some Mk -> In (c, gs) (im_cons Mk) ->
      cargs_plen t_over_rose_group gs.
  Proof.
    intros * Hk Hin; grp_cases; cbn in Hin; repeat destruct Hin as [Hin | Hin]; try contradiction;
      injection Hin; intros; subst.
    all: intros gs1 t0 gs2 Heq; destruct gs1 as [| g1 [| g2 gs1]]; cbn in Heq; try discriminate; injection Heq; intros; subst;
      try (destruct gs1; discriminate).
    all: try discriminate.
    all: eexists; split; reflexivity.
  Qed.

  Lemma t_over_rose_container_plen : forall v Mv qc kc Is vm Dq i' Mi' c gs', ind_member t_over_rose_group v = Some Mv ->
      im_head Mv = mh_view qc kc Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq -> ind_member Dq i' = Some Mi' ->
      In (c, gs') (im_cons Mi') -> cargs_plen Dq gs'.
  Proof.
    intros * Hv Hh Hl Hi' Hin; grp_cases; cbn in Hin; repeat destruct Hin as [Hin | Hin]; try contradiction;
      injection Hin; intros; subst.
    all: intros gs1 t0 gs2 Heq; destruct gs1 as [| g1 [| g2 gs1]]; cbn in Heq; try discriminate; injection Heq; intros; subst;
      try (destruct gs1; discriminate).
    all: try discriminate.
    all: eexists; split; reflexivity.
  Qed.

  Lemma t_over_rose_tele_ass : grp_tele_ass t_over_rose_group.
  Proof.
    constructor.
    - constructor.
    - intros * Hk; grp_cases; constructor.
    - intros * Hv Hh; grp_cases.
      all: do 2 eexists; split; [ eassumption | split; [ reflexivity | split; reflexivity ] ].
    - exists (fun k => k); exact t_over_rose_rank.
    - exact t_over_rose_vwrap.
    - exact t_over_rose_coherent.
    - exact t_over_rose_images.
    - exact t_over_rose_plen.
    - exact t_over_rose_container_plen.
    - grp_rstruct_none.
    - intros * Hv Hh Hl; grp_cases; grp_suffix_none.
    - intros * Hv Hh Hl; grp_cases; grp_rstruct_none.
  Qed.

  (** [T] is a type of the model, its elements the group's relation. *)
  Theorem t_over_rose_in_model : forall i,
      DF d_ind pT 0 nil ≈ d_ind pT 0 nil ∈ per_univ_elem i ↘
        grp_rel pT t_over_rose_group nil no_nparams_rel no_args_rel no_doms_rel 0 nil nil nil nil.
  Proof. intros i; grp_in_model HlT t_over_rose_tele_ass t_over_rose_group. Qed.

End RoseViews.

(** ** [T] Nested Through a Phantom Parameter

    [Phantom (A : TA) (B : TB) := mk (a : A)];
    [T (f : TF) := node (p : Phantom (T f) (f Z))], whose group has the
    view [Phantom (T f) (f Z)], its second argument a phantom one.  [T] at
    two uniform parameters whose readbacks agree is one type of the
    model; the gluing of soundness moves along it
    ([Soundness.Inductives.Regressions]). *)

Section PhantomViews.
  Context {GC : GCtx}.
  Variables (pP pT pmP pmT : qname) (TA TB TF SP ST Z : exp).

  (** The filed group of [Phantom]: one declared member, no view. *)
  Definition phantom_group : ind_decl :=
    mk_ind (ce_ass TB :: ce_ass TA :: nil) SP
      (mk_imember (mh_decl pmP) nil (("mk", ca_arg (a_var 1) :: nil) :: nil) :: nil).

  (** The filed group of [T]: [T], and the view [Phantom (T f) (f Z)]. *)
  Definition t_over_phantom_group : ind_decl :=
    mk_ind (ce_ass TF :: nil) ST
      (mk_imember (mh_decl pmT) nil (("node", ca_rec (pt_self 1 nil) :: nil) :: nil)
       :: mk_imember (mh_view pP 0 (a_app (a_ind pT 0) (a_var 0) :: a_app (a_var 0) Z :: nil) (1 :: nil)) nil
            (("mk", ca_rec (pt_self 0 nil) :: nil) :: nil)
       :: nil).

  Hypothesis HlP : ind_lookup gc_deps gc_stack pP = Some phantom_group.
  Hypothesis HlT : ind_lookup gc_deps gc_stack pT = Some t_over_phantom_group.

  Lemma t_over_phantom_rank : view_rank_ok gc_deps gc_stack t_over_phantom_group (fun k => k).
  Proof.
    constructor.
    - intros k Mk pm Hk Hh; grp_cases; reflexivity.
    - intros * Hk Hh Hl Hi' Hv HMv Hc' Hc; grp_cases.
      all: grp_rank_nest.
    - intros * Hk Hh; grp_cases.
  Qed.

  Lemma t_over_phantom_vwrap : forall k Mk qc k' Is vm, ind_member t_over_phantom_group k = Some Mk ->
      im_head Mk = mh_view qc k' Is vm ->
      exists D', ind_lookup gc_deps gc_stack qc = Some D' /\ vwrap_ok t_over_phantom_group D' vm.
  Proof.
    intros * Hk Hh; grp_cases.
    all: eexists; split; [ eassumption |].
    all: constructor; [ reflexivity |].
    all: intros i' Mi' v Hi' Hv; grp_cases.
    all: eexists; split; [ reflexivity | split; [ reflexivity | split; [ reflexivity |] ] ].
    all: intros c gs' gs Hin Hc; cbn in Hin; repeat destruct Hin as [Hin | Hin]; try contradiction;
      injection Hin; intros; subst; grp_cases.
    all: cbn; repeat split.
  Qed.

  Lemma t_over_phantom_coherent : view_maps_coherent gc_deps gc_stack t_over_phantom_group.
  Proof. unfold view_maps_coherent; intros * Hk Hh Hl Hi' Hv HMv HMh; grp_cases; cbn; reflexivity. Qed.

  Lemma t_over_phantom_images : forall v Mv qc kc Is vm Dq i' Mi', ind_member t_over_phantom_group v = Some Mv ->
      im_head Mv = mh_view qc kc Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq -> ind_member Dq i' = Some Mi' ->
      view_member_image t_over_phantom_group qc Is vm i' Mi'.
  Proof.
    intros * Hv Hh Hl Hi'; grp_cases.
    all: eapply mk_view_member_image; [ reflexivity | reflexivity | reflexivity | cbn; eauto ].
  Qed.

  Lemma t_over_phantom_plen : forall k Mk c gs, ind_member t_over_phantom_group k = Some Mk -> In (c, gs) (im_cons Mk) ->
      cargs_plen t_over_phantom_group gs.
  Proof.
    intros * Hk Hin; grp_cases; cbn in Hin; repeat destruct Hin as [Hin | Hin]; try contradiction;
      injection Hin; intros; subst.
    all: intros gs1 t0 gs2 Heq; destruct gs1 as [| g1 [| g2 gs1]]; cbn in Heq; try discriminate; injection Heq; intros; subst;
      try (destruct gs1; discriminate).
    all: try discriminate.
    all: eexists; split; reflexivity.
  Qed.

  Lemma t_over_phantom_container_plen : forall v Mv qc kc Is vm Dq i' Mi' c gs', ind_member t_over_phantom_group v = Some Mv ->
      im_head Mv = mh_view qc kc Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq -> ind_member Dq i' = Some Mi' ->
      In (c, gs') (im_cons Mi') -> cargs_plen Dq gs'.
  Proof.
    intros * Hv Hh Hl Hi' Hin; grp_cases; cbn in Hin; repeat destruct Hin as [Hin | Hin]; try contradiction;
      injection Hin; intros; subst.
    all: intros gs1 t0 gs2 Heq; destruct gs1 as [| g1 [| g2 gs1]]; cbn in Heq; try discriminate; injection Heq; intros; subst;
      try (destruct gs1; discriminate).
    all: try discriminate.
    all: eexists; split; reflexivity.
  Qed.

  Lemma t_over_phantom_tele_ass : grp_tele_ass t_over_phantom_group.
  Proof.
    constructor.
    - constructor; [ eexists; reflexivity | constructor ].
    - intros * Hk; grp_cases; constructor.
    - intros * Hv Hh; grp_cases.
      all: do 2 eexists; split; [ eassumption | split; [ reflexivity | split; reflexivity ] ].
    - exists (fun k => k); exact t_over_phantom_rank.
    - exact t_over_phantom_vwrap.
    - exact t_over_phantom_coherent.
    - exact t_over_phantom_images.
    - exact t_over_phantom_plen.
    - exact t_over_phantom_container_plen.
    - grp_rstruct_none.
    - intros * Hv Hh Hl; grp_cases; grp_suffix_none.
    - intros * Hv Hh Hl; grp_cases; grp_rstruct_none.
  Qed.

  (** [T] at uniform parameters [g] and [g'] whose readbacks agree: related
      types of the model. *)
  Theorem t_over_phantom_related : forall i g g', per_top_ps (ce_ass TF :: nil) (g :: nil) (g' :: nil) ->
      DF d_ind pT 0 (g :: nil) ≈ d_ind pT 0 (g' :: nil) ∈ per_univ_elem i ↘
        grp_rel pT t_over_phantom_group (g :: nil) no_nparams_rel no_args_rel no_doms_rel 0 (g :: nil) (g' :: nil) nil nil.
  Proof.
    intros * Hg.
    change (d_ind pT 0 (g :: nil)) with (d_ind pT 0 ((g :: nil) ++ nil)).
    change (d_ind pT 0 (g' :: nil)) with (d_ind pT 0 ((g' :: nil) ++ nil)).
    basic_per_univ_elem_econstructor;
      try exact HlT; try exact t_over_phantom_tele_ass; try exact Hg; try reflexivity;
      try (red; intros; grp_vacuous; fail);
      try (cbn; split; [ reflexivity | exact I ]);
      try (constructor; intros; grp_vacuous;
           (econstructor; [ cbn; constructor | cbn; constructor
                          | unfold ntele_rel, ind_member, t_over_phantom_group; cbn; split; [ reflexivity | exact I ] ])).
  Qed.

End PhantomViews.

(** ** A Container Whose Non-Uniform Parameter Is of Its Uniform One

    [C (A : Typeω@iU) : A → Type] ([im_nparams = [ce_ass #0]]) and
    [T := t (x : T) (c : C T x) : T].  The view [C T] would have a
    non-uniform parameter of type [T]: its non-uniform parameters,
    normalized, mention the group, so [view_nps] has no derivation
    ([view_nps_self_param_absurd]).  The declaration does not get that
    far: [c]'s type mentions the recursive argument [x], so [c] is
    classified neither as written nor as its normal form, and [run_cmd_ind_case]
    rejects the declaration ([run_cmd_ind_self_param_rejected]). *)

Lemma nbe_ty_var0 : forall Θ Ξ A Γ W, nbe_ty Θ Ξ (ce_ass A :: Γ) (a_var 0) W -> W = nf_neut (ne_var 0).
Proof.
  intros * [ρ m Hi He Hr].
  inversion Hi; subst.
  inversion He; subst.
  inversion Hr; subst.
  match goal with H : read_ne _ _ _ _ _ |- _ => inversion H; subst end.
  cbn [List.length]; replace (S (Datatypes.length Γ) - Datatypes.length Γ - 1) with 0 by lia; reflexivity.
Qed.

Lemma view_nps_self_param_absurd : forall Θ Ξ R pC DC MC Nv,
    raw_decl_uparams R = nil -> rd_n R = 1 ->
    ind_lookup Θ Ξ pC = Some DC -> ind_member DC 0 = Some MC -> im_nparams MC = ce_ass (a_var 0) :: nil ->
    ~ view_nps Θ Ξ R (vk_ind pC 0 (a_var 0 :: nil)) Nv.
Proof.
  intros * Hu Hn Hl Hk Hnp Hv.
  inversion Hv as [? ? ? D' Mk' Ws ? Hl' Hk' Hnbe Himg |]; subst.
  rewrite Hl in Hl'; injection Hl' as <-; rewrite Hk in Hk'; injection Hk' as <-.
  rewrite Hnp in Hnbe; cbn in Hnbe.
  destruct R as [Us [| Mr [| ? ?]]]; cbn in Hu, Hn; try discriminate; subst Us.
  unfold rd_uctx, rd_selfs in Hnbe; cbn in Hnbe.
  inversion Hnbe as [| A Δ W Δ' _ HW Hrest]; subst.
  inversion Hrest; subst.
  (** The parameter's type normalizes to [Self], which is not in the
      image of the weakening past the [Self]s. *)
  cbn [List.app] in HW; apply nbe_ty_var0 in HW; subst W.
  vm_compute in Himg; discriminate.
Qed.

(** The container at [Self] and the argument before it, in normal form. *)
Lemma nbe_ty_container_at_self : forall Θ Ξ A B Γ pC DC MC iU W,
    ind_lookup Θ Ξ pC = Some DC -> ind_uparams DC = ce_ass (a_typ iU) :: nil -> ind_member DC 0 = Some MC ->
    im_nparams MC = ce_ass (a_var 0) :: nil ->
    nbe_ty Θ Ξ (ce_ass A :: ce_ass B :: Γ) (a_app (a_app (a_ind pC 0) (a_var 1)) (a_var 0)) W ->
    W = nf_indty pC 0 (cons (nf_neut (ne_var 1)) (cons (nf_neut (ne_var 0)) nil)).
Proof.
  intros * Hl Hu Hk Hnp [ρ m Hi He Hr].
  inversion Hi as [| ? ρ1 ? a1 Hi1 Ha1 | | |]; subst.
  inversion Hi1 as [| ? ρ0 ? a0 Hi0 Ha0 | | |]; subst.
  inversion He; subst.
  repeat match goal with
  | H : ⟦ a_app _ _ ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H; subst; clear H
  | H : ⟦ a_var _ ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H; subst; clear H
  | H : ⟦ a_ind _ _ ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H; subst; clear H
  | H : $| d_ind _ _ _ & _ | _ ⍮ _ ↘ _ |- _ => inversion H; subst; clear H
  end.
  cbn in Hr.
  inversion Hr as [| | | | | | | ? ? ? D3 M3 Rs Hl3 Hk3 Hlen3 Hps |]; subst; clear Hr.
  rewrite Hl in Hk3; injection Hk3 as <-; rewrite Hk in Hlen3; injection Hlen3 as <-.
  match goal with H : read_ps _ _ _ _ _ _ _ |- _ => rename H into Hps' end.
  unfold im_params in Hps'; rewrite Hnp, Hu in Hps'; cbn in Hps'.
  inversion Hps'; subst; clear Hps'.
  match goal with H : read_ps _ _ _ _ _ _ _ |- _ => inversion H; subst; clear H end.
  match goal with H : read_ps _ _ _ _ _ nil _ |- _ => inversion H; subst; clear H end.
  repeat match goal with
  | H : ⟦ a_typ _ ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H; subst; clear H
  | H : ⟦ a_var _ ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H; subst; clear H
  end.
  (** Each parameter is read back as the variable it is. *)
  repeat match goal with
  | H : read_nf _ _ _ _ _ |- _ => cbn in H; inversion H; subst; clear H
  | H : read_typ _ _ _ _ _ |- _ => inversion H; subst; clear H
  | H : read_ne _ _ _ _ _ |- _ => inversion H; subst; clear H
  end.
  replace (Datatypes.S (Datatypes.S (Datatypes.length Γ)) - Datatypes.length Γ - 1) with 1 by lia.
  replace (Datatypes.S (Datatypes.S (Datatypes.length Γ)) - Datatypes.S (Datatypes.length Γ) - 1) with 0 by lia.
  reflexivity.
Qed.

(** The container at [Self] and a recursive argument is no argument: the
    recursive argument is neither a uniform argument nor a [Self]-free
    non-uniform one, whatever the uniform parameters of the container. *)
Lemma cls_container_at_rec_none : forall grp recs pC,
    cls_arg grp recs 0 0 1 (true :: nil) (a_app (a_app (a_ind pC 0) (a_var 1)) (a_var 0)) = None.
Proof.
  intros grp recs pC; unfold cls_arg.
  unfold img_pat at 1.
  match goal with |- context [exp_eq_dec ?T ?T'] => destruct (exp_eq_dec T T') as [E | _] end.
  { exfalso; cbn in E; injection E; intros; discriminate. }
  cbn [cls_sh app_head app_args List.app]; unfold cls_nest.
  destruct (grp pC 0) as [[| [| [| m]]] |]; vm_compute; reflexivity.
Qed.

(** [T := t (x : T) (c : C T x) : T], of the sort [ST]. *)
Definition self_param_decl (pC : qname) (x : string) (ST : exp) : raw_decl :=
  mk_raw nil (mk_rmem x nil ST (("t", ("x", a_var 0) :: ("c", a_app (a_app (a_ind pC 0) (a_var 1)) (a_var 0)) :: nil) :: nil) :: nil) false.

Theorem run_cmd_ind_self_param_rejected : forall lp rd tc ch B Rb Θ Ξ pv B' Rb' Θ' Ξ' pC DC MC iU x ST,
    ind_lookup Θ Ξ pC = Some DC -> ind_uparams DC = ce_ass (a_typ iU) :: nil -> ind_member DC 0 = Some MC ->
    im_nparams MC = ce_ass (a_var 0) :: nil ->
    ~ (Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨lp ⍮ rd ⍮ tc⟩ cc_ind pv (self_param_decl pC x ST) ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb').
Proof.
  intros * Hl Hu Hk Hnp Hr.
  inversion Hr; subst.
  match goal with H : Forall2 (rm_cls _ _ _) _ _ |- _ => rename H into Hcls end.
  cbn in Hcls; inversion Hcls as [| ? cs ? ? Hc _]; subst.
  unfold rm_cls, cls_cons_in in Hc; cbn in Hc.
  inversion Hc as [| ? ? ? ? [_ Hargs] _]; subst.
  inversion Hargs as [| ? ? ? ? ? g1 ? Hg1 Hrest]; subst.
  inversion Hrest as [| ? ? ? ? ? g2 ? Hg2 _]; subst.
  (** The first argument, [x : T], is recursive. *)
  assert (Eg1 : g1 = rcarg_rec_case (rptyp_self 0 nil)).
  { inversion Hg1 as [? Hs | ? ? ? Hs]; subst; vm_compute in Hs; [ injection Hs as <-; reflexivity | discriminate ]. }
  subst g1; cbn [rcarg_bit] in Hg2.
  (** The second, [c : C T x], mentions it: it is classified neither as
      written nor as its normal form. *)
  inversion Hg2 as [? Hs | i W ? _ _ HW Hs]; subst.
  - rewrite cls_container_at_rec_none in Hs; discriminate.
  - cbn [rtele List.map List.rev List.app snd] in HW; unfold rm_pctx, rd_selfs in HW; cbn in HW.
    rewrite (nbe_ty_container_at_self _ _ _ _ _ _ _ _ _ _ Hl Hu Hk Hnp HW) in Hs.
    cbn in Hs; rewrite cls_container_at_rec_none in Hs; discriminate.
Qed.
