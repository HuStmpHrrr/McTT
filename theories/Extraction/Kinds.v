From Equations Require Import Equations.
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members Inductives.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Extraction Require Import Lookup.
Import Domain_Notations.

Generalizable All Variables.

(** * Computing the Kinds of Members

    Evaluation of a local open reads the kinds of the members its items
    name ([kgens]).  Both evaluators compute them with [kgens_impl], by
    recursion on a termination order. *)

(** The orders mirror the kinds relations, one for each; a chain
    of a global alias recurses into the alias's unit, and a body's member
    into the environment the kinds read off the body before it. *)

Inductive dkind_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
| dko_global_def :
  `( gc_resolve Θ Ξ (qname_app pq ch) = Some (ge_def b pv A B) ->
     dkind_order Θ Ξ (dm_global pq args) ch )
| dko_global_mod :
  `( gc_module Θ Ξ (qname_app pq ch) = Some (mr_body T oD) ->
     dkind_order Θ Ξ (dm_global pq args) ch )
| dko_global_alias :
  `( gc_module Θ Ξ (qname_app pq ch) = Some (mr_alias U r) ->
     ukind_order Θ Ξ nil U r ->
     dkind_order Θ Ξ (dm_global pq args) ch )
| dko_local :
  `( ukind_order Θ Ξ p U ch ->
     dkind_order Θ Ξ (dm_local p U args) ch )
| dko_member :
  `( dkind_order Θ Ξ h (ch0 ++ ch) ->
     dkind_order Θ Ξ (dm_member h ch0) ch )

with ukind_order (Θ : gdeps) (Ξ : gstack) : env -> gunit -> list string -> Prop :=
| uko_self :
  `( ukind_order Θ Ξ p (gu_body Δ Φ) nil )
| uko_def :
  `( gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A B)) ->
     ukind_order Θ Ξ p (gu_body Δ Φ) (x :: nil) )
| uko_mod :
  `( gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
     kenv_order Θ Ξ (kpad (List.length Δ) p) Φ' ->
     (forall p1, kenv Θ Ξ (kpad (List.length Δ) p) Φ' p1 -> ukind_order Θ Ξ p1 Uy ch) ->
     ukind_order Θ Ξ p (gu_body Δ Φ) (y :: ch) )
| uko_item :
  `( gm_item_upto Φ x = Some (Φ0, E, its1, it) ->
     kenv_order Θ Ξ (kpad (List.length Δ) p) Φ0 ->
     (forall p0, kenv Θ Ξ (kpad (List.length Δ) p) Φ0 p0 -> skind_order Θ Ξ p0 E (item_ch it ch)) ->
     ukind_order Θ Ξ p (gu_body Δ Φ) (x :: ch) )
| uko_alias :
  `( skind_order Θ Ξ (kpad (List.length Δ) p) E ch ->
     ukind_order Θ Ξ p (gu_mk Δ (md_alias E)) ch )

with skind_order (Θ : gdeps) (Ξ : gstack) : env -> modexp -> list string -> Prop :=
| sko_unit :
  `( dkind_order Θ Ξ (dm_global (q_abs fp nil) nil) ch ->
     skind_order Θ Ξ p (me_unit fp) ch )
| sko_var :
  `( dkind_order Θ Ξ (env_mod p x) ch ->
     skind_order Θ Ξ p (me_var x) ch )
| sko_lit :
  `( ukind_order Θ Ξ p U ch ->
     skind_order Θ Ξ p (me_lit U) ch )
| sko_mem :
  `( skind_order Θ Ξ p E (y :: ch) ->
     skind_order Θ Ξ p (me_mem E y) ch )
| sko_app :
  `( skind_order Θ Ξ p E ch ->
     skind_order Θ Ξ p (me_app E N) ch )

with kenv_order (Θ : gdeps) (Ξ : gstack) : env -> gmod -> Prop :=
| keo_nil :
  `( kenv_order Θ Ξ p gm_nil )
| keo_ext :
  `( kenv_order Θ Ξ p Φ ->
     kenv_order Θ Ξ p (gm_ext Φ y E) )
| keo_open :
  `( kenv_order Θ Ξ p Φ ->
     (forall p1, kenv Θ Ξ p Φ p1 -> kgens_order Θ Ξ p1 E its) ->
     kenv_order Θ Ξ p (gm_open Φ E its) )

with kgens_order (Θ : gdeps) (Ξ : gstack) : env -> modexp -> list iitem -> Prop :=
| kgo_nil :
  `( kgens_order Θ Ξ p E nil )
| kgo_self :
  `( kgens_order Θ Ξ p E its ->
     kgens_order Θ Ξ p E ((None, d, pv) :: its) )
| kgo_name :
  `( skind_order Θ Ξ p E (n :: nil) ->
     kgens_order Θ Ξ p E its ->
     kgens_order Θ Ξ p E ((Some n, d, pv) :: its) ).

#[local]
Hint Constructors dkind_order ukind_order skind_order kenv_order kgens_order : mctt.

Lemma kind_order_sound : forall Θ Ξ,
    (forall h ch k, dkind Θ Ξ h ch k -> dkind_order Θ Ξ h ch) /\
    (forall p U ch k, ukind Θ Ξ p U ch k -> ukind_order Θ Ξ p U ch) /\
    (forall p E ch k, skind Θ Ξ p E ch k -> skind_order Θ Ξ p E ch) /\
    (forall p Φ p1, kenv Θ Ξ p Φ p1 -> kenv_order Θ Ξ p Φ) /\
    (forall p E its gs, kgens Θ Ξ p E its gs -> kgens_order Θ Ξ p E its).
Proof.
  intros Θ Ξ; pose proof (@functional_kind Θ Ξ) as (_ & _ & _ & Fk & _).
  apply kind_mut_ind; intros; try solve [ econstructor; eauto ];
    econstructor; eauto; intros;
    match goal with H1 : kenv _ _ ?p ?Φ ?r1, H2 : kenv _ _ ?p ?Φ ?r2 |- _ =>
      assert_fails (constr_eq r1 r2); rewrite <- (Fk _ _ _ H1 _ H2) end; eauto.
Qed.

Lemma kgens_order_sound : forall Θ Ξ p E its gs, kgens Θ Ξ p E its gs -> kgens_order Θ Ξ p E its.
Proof. intros Θ Ξ; pose proof (kind_order_sound Θ Ξ); destruct_all; eauto. Qed.

#[export]
Hint Resolve kgens_order_sound : mctt.

Section KindImpl.
  Variables (Θ : gdeps) (Ξ : gstack).

  #[local]
  Ltac kd_inv :=
    match goal with
    | H : dkind_order _ _ _ _ |- _ => progressive_invert H
    | H : ukind_order _ _ _ _ _ |- _ => progressive_invert H
    | H : skind_order _ _ _ _ _ |- _ => progressive_invert H
    | H : kenv_order _ _ _ _ |- _ => progressive_invert H
    | H : kgens_order _ _ _ _ _ |- _ => progressive_invert H
    end.

  #[local]
  Ltac kd_glob :=
    repeat match goal with
      | H1 : gc_resolve _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_resolve _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gc_module _ _ ?p = Some _, H2 : gc_module _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_module _ _ ?p = Some _, H2 : gc_module _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gm_item_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gm_item_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = Some _ |- _ =>
          rewrite (gm_prefix_item_excl _ _ _ H1) in H2; discriminate H2

      | H1 : gc_module _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = Some _ |- _ =>
          rewrite (gc_module_resolve _ _ _ _ H1) in H2; discriminate H2
      end.

  #[local]
  Ltac kd_split :=
    match goal with
    | H : dkind_order _ _ _ _ |- _ => dependent destruction H
    | H : ukind_order _ _ _ _ _ |- _ => dependent destruction H
    | H : skind_order _ _ _ _ _ |- _ => dependent destruction H
    | H : kenv_order _ _ _ _ |- _ => dependent destruction H
    | H : kgens_order _ _ _ _ _ |- _ => dependent destruction H
    end.

  #[local]
  Ltac kd_finish :=
    kd_glob;
    try solve [ intuition discriminate ];
    try solve [ eauto 6 with mctt ];
    try econstructor; eauto with mctt.

  #[local]
  Ltac kd_obl :=
    intros; cbv beta in *; repeat kd_inv;
    first [ solve [ kd_finish ] | solve [ kd_split; kd_finish ] | kd_finish ].

  #[local]
  Ltac kd_obl_auto :=
    intros;
    lazymatch goal with
    | |- dkind_order _ _ _ _ => kd_obl
    | |- ukind_order _ _ _ _ _ => kd_obl
    | |- skind_order _ _ _ _ _ => kd_obl
    | |- kenv_order _ _ _ _ => kd_obl
    | |- kgens_order _ _ _ _ _ => kd_obl
    | |- _ => abstract kd_obl
    end.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations dkind_impl h ch (H : dkind_order Θ Ξ h ch) : { k | dkind Θ Ξ h ch k } by struct H :=
  | dm_global pq args, ch, H with inspect (gc_module Θ Ξ (qname_app pq ch)) := {
    | exist _ (Some (mr_body T oD)) E => exist _ mk_mod _
    | exist _ (Some (mr_alias U r)) E =>
        let (k, Hk) := ukind_impl nil U r _ in
        exist _ k _
    | exist _ None E with inspect (gc_resolve Θ Ξ (qname_app pq ch)) := {
      | exist _ (Some (ge_def b pv A B)) E2 => exist _ mk_term _
      | exist _ _ E2 => False_rect _ _ } }
  | dm_local p U args, ch, H =>
      let (k, Hk) := ukind_impl p U ch _ in
      exist _ k _
  | dm_member h ch0, ch, H =>
      let (k, Hk) := dkind_impl h (ch0 ++ ch) _ in
      exist _ k _

  with ukind_impl p U ch (H : ukind_order Θ Ξ p U ch) : { k | ukind Θ Ξ p U ch k } by struct H :=
  | p, gu_mk Δ (md_body Φ), nil, H => exist _ mk_mod _
  | p, gu_mk Δ (md_body Φ), x :: ch, H with inspect (gm_item_upto Φ x) := {
    | exist _ (Some (Φ0, E, its1, it)) Ei =>
        let (p0, Hp0) := kenv_impl (kpad (List.length Δ) p) Φ0 _ in
        let (k, Hk) := skind_impl p0 E (item_ch it ch) _ in
        exist _ k _
    | exist _ None Ei with inspect (gm_prefix_upto Φ x) := {
      | exist _ (Some (gm_ext Φ' _ (ge_def b pv A B))) P => exist _ mk_term _
      | exist _ (Some (gm_ext Φ' _ (ge_mod pm Uy))) P =>
          let (p1, Hp1) := kenv_impl (kpad (List.length Δ) p) Φ' _ in
          let (k, Hk) := ukind_impl p1 Uy ch _ in
          exist _ k _
      | exist _ _ P => False_rect _ _ } }
  | p, gu_mk Δ (md_alias E), ch, H =>
      let (k, Hk) := skind_impl (kpad (List.length Δ) p) E ch _ in
      exist _ k _

  with skind_impl p E ch (H : skind_order Θ Ξ p E ch) : { k | skind Θ Ξ p E ch k } by struct H :=
  | p, me_unit fp, ch, H =>
      let (k, Hk) := dkind_impl (dm_global (q_abs fp nil) nil) ch _ in
      exist _ k _
  | p, me_var x, ch, H =>
      let (k, Hk) := dkind_impl (env_mod p x) ch _ in
      exist _ k _
  | p, me_lit U, ch, H =>
      let (k, Hk) := ukind_impl p U ch _ in
      exist _ k _
  | p, me_mem E y, ch, H =>
      let (k, Hk) := skind_impl p E (y :: ch) _ in
      exist _ k _
  | p, me_app E N, ch, H =>
      let (k, Hk) := skind_impl p E ch _ in
      exist _ k _

  with kenv_impl p Φ (H : kenv_order Θ Ξ p Φ) : { p1 | kenv Θ Ξ p Φ p1 } by struct H :=
  | p, gm_nil, H => exist _ p _
  | p, gm_ext Φ y E, H =>
      let (p1, Hp1) := kenv_impl p Φ _ in
      exist _ (kbentry p1 E :: p1) _
  | p, gm_open Φ E its, H =>
      let (p1, Hp1) := kenv_impl p Φ _ in
      let (gs, Hgs) := kgens_impl p1 E its _ in
      exist _ (kgens_env p1 0 gs) _

  with kgens_impl p E its (H : kgens_order Θ Ξ p E its) : { gs | kgens Θ Ξ p E its gs } by struct H :=
  | p, E, nil, H => exist _ nil _
  | p, E, (None, d, pv) :: its, H =>
      let (gs, Hgs) := kgens_impl p E its _ in
      exist _ (ig_alias d pv E :: gs) _
  | p, E, (Some n, d, pv) :: its, H with skind_impl p E (n :: nil) _ := {
    | exist _ mk_term Hk =>
        let (gs, Hgs) := kgens_impl p E its _ in
        exist _ (ig_def d pv a_True (a_mem E n) :: gs) _
    | exist _ mk_mod Hk =>
        let (gs, Hgs) := kgens_impl p E its _ in
        exist _ (ig_alias d pv (me_mem E n) :: gs) _ }.

Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
Next Obligation. kd_obl_auto. Defined.
End KindImpl.
