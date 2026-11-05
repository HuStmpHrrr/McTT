From Equations Require Import Equations.
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Extraction Require Import Lookup.
From Mctt.Extraction Require Export FastDomain.
Import Domain_Notations.

Generalizable All Variables.

(** * Computing the Kinds of Members

    Evaluation reads a body expanded, every local open replaced by the
    entries it stores ([gunit_expand]), and the kinds of its members off
    the entries before each ([kinds_env]).  Both evaluators compute the
    kinds by recursion on a termination order. *)

(** The orders mirror the kinds relations, one for each; a chain of a
    global alias recurses into the alias's unit, expanded, and a body's
    member into the environment the kinds read off the body before it. *)

Inductive dmod_member_kind_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
(** The path names a definition ([dmod_member_kind_global_here_def]): no recursion *)
| dmod_member_kind_order_global_here_def :
  `( gc_resolve Θ Ξ pq = Some (ge_def b pv ra A B) ->
     dmod_member_kind_order Θ Ξ (dm_global pq args) nil )
(** The path names a body module or a frame ([dmod_member_kind_global_here_mod]): no
    recursion *)
| dmod_member_kind_order_global_here_mod :
  `( (exists T oD, gc_module Θ Ξ pq = Some (mr_body T oD)) \/ (exists TΦ, gc_frame Ξ pq = Some TΦ) ->
     dmod_member_kind_order Θ Ξ (dm_global pq args) nil )
(** The member [y] is a definition with a module part stored in place
    ([dmod_member_kind_global_here_dm]): no recursion *)
| dmod_member_kind_order_global_here_dm :
  `( dm_path Θ Ξ (qname_app pq (y :: nil)) ->
     gc_loc Θ Ξ (qname_app pq (y :: nil)) = Some TΦ ->
     dmod_member_kind_order Θ Ξ (dm_global pq args) (y :: nil) )
(** The member [y] is an alias read past ([dmod_member_kind_global_alias_case]): the order of
    the chain in the alias's unit, expanded *)
| dmod_member_kind_order_global_alias :
  `( gc_module Θ Ξ (qname_app pq (y :: nil)) = Some (mr_alias U) ->
     ch <> nil \/ ~ dm_path Θ Ξ (qname_app pq (y :: nil)) ->
     gunit_member_kind_order Θ Ξ nil (gunit_expand U) ch ->
     dmod_member_kind_order Θ Ξ (dm_global pq args) (y :: ch) )
(** The member [y] is a definition with a module part stored as an alias
    ([dmod_member_kind_global_alias_dm]): the order of the empty chain in the alias's
    unit, expanded *)
| dmod_member_kind_order_global_alias_dm :
  `( gc_module Θ Ξ (qname_app pq (y :: nil)) = Some (mr_alias U) ->
     dm_path Θ Ξ (qname_app pq (y :: nil)) ->
     gunit_member_kind_order Θ Ξ nil (gunit_expand U) nil ->
     dmod_member_kind_order Θ Ξ (dm_global pq args) (y :: nil) )
(** The member [y] is located in place ([dmod_member_kind_global_step]): the order of the
    rest of the chain at the path of [y] *)
| dmod_member_kind_order_global_step :
  `( (exists TΦ, gc_loc Θ Ξ (qname_app pq (y :: nil)) = Some TΦ) \/
     (exists b pv ra A B, gc_resolve Θ Ξ (qname_app pq (y :: nil)) = Some (ge_def b pv ra A B)) ->
     ch <> nil \/ ~ dm_path Θ Ξ (qname_app pq (y :: nil)) ->
     dmod_member_kind_order Θ Ξ (dm_global (qname_app pq (y :: nil)) args) ch ->
     dmod_member_kind_order Θ Ξ (dm_global pq args) (y :: ch) )
(** A closure ([dmod_member_kind_local]): the order of its unit, expanded *)
| dmod_member_kind_order_local :
  `( gunit_member_kind_order Θ Ξ p (gunit_expand (gu_mk Δ D)) ch ->
     dmod_member_kind_order Θ Ξ (dm_local Δ D p) ch )
(** A submodule closure ([dmod_member_kind_member], [dmod_member_kind_member_dm]): the order of the
    longer chain *)
| dmod_member_kind_order_member :
  `( dmod_member_kind_order Θ Ξ h (ch0 ++ ch) ->
     dmod_member_kind_order Θ Ξ (dm_member h ch0) ch )

with gunit_member_kind_order (Θ : gdeps) (Ξ : gstack) : env -> gunit -> list string -> Prop :=
(** A body at the empty chain ([gunit_member_kind_self]): no recursion *)
| gunit_member_kind_order_self :
  `( gunit_member_kind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) nil )
(** A definition of the body ([gunit_member_kind_def]): no recursion *)
| gunit_member_kind_order_def :
  `( gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv ra A B)) ->
     gunit_member_kind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) (x :: nil) )
(** A submodule of the body ([gunit_member_kind_mod]): the order of the entries before it,
    and of the rest of the chain in its unit, expanded, in each environment
    they make *)
| gunit_member_kind_order_mod :
  `( gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
     kinds_env_order Θ Ξ (kinds_pads (List.length Δ) p) Φ' ->
     (forall p1, kinds_env Θ Ξ (kinds_pads (List.length Δ) p) Φ' p1 -> gunit_member_kind_order Θ Ξ p1 (gunit_expand Uy) ch) ->
     gunit_member_kind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) (y :: ch) )
(** A definition with a module part of the body, at the end of the chain
    ([gunit_member_kind_dm_here]): the order of the entries before it, and of the empty
    chain in its module part, expanded, in each environment they make *)
| gunit_member_kind_order_dm_here :
  `( gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_def_mod pv A M Uy)) ->
     kinds_env_order Θ Ξ (kinds_pads (List.length Δ) p) Φ' ->
     (forall p1, kinds_env Θ Ξ (kinds_pads (List.length Δ) p) Φ' p1 -> gunit_member_kind_order Θ Ξ p1 (gunit_expand Uy) nil) ->
     gunit_member_kind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) (y :: nil) )
(** A definition with a module part of the body, the chain going on
    ([gunit_member_kind_dm_step]): the order of the entries before it, and of the rest of
    the chain in its module part, expanded, in each environment they make *)
| gunit_member_kind_order_dm_step :
  `( gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_def_mod pv A M Uy)) ->
     ch <> nil ->
     kinds_env_order Θ Ξ (kinds_pads (List.length Δ) p) Φ' ->
     (forall p1, kinds_env Θ Ξ (kinds_pads (List.length Δ) p) Φ' p1 -> gunit_member_kind_order Θ Ξ p1 (gunit_expand Uy) ch) ->
     gunit_member_kind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) (y :: ch) )
(** An alias unit ([gunit_member_kind_alias]): the order of the chain in its target *)
| gunit_member_kind_order_alias :
  `( modexp_member_kind_order Θ Ξ (kinds_pads (List.length Δ) p) E ch ->
     gunit_member_kind_order Θ Ξ p (gu_mk Δ (md_alias E)) ch )

with modexp_member_kind_order (Θ : gdeps) (Ξ : gstack) : env -> modexp -> list string -> Prop :=
(** A unit ([modexp_member_kind_unit]): the order of the chain in its global module *)
| modexp_member_kind_order_unit :
  `( dmod_member_kind_order Θ Ξ (dm_global (q_abs fp nil) nil) ch ->
     modexp_member_kind_order Θ Ξ p (me_unit fp) ch )
(** A module slot ([modexp_member_kind_var]): the order of the chain in its value *)
| modexp_member_kind_order_var :
  `( dmod_member_kind_order Θ Ξ (env_mod p x) ch ->
     modexp_member_kind_order Θ Ξ p (me_var x) ch )
(** A literal unit ([modexp_member_kind_lit]): the order of the chain in the unit, expanded *)
| modexp_member_kind_order_lit :
  `( gunit_member_kind_order Θ Ξ p (gunit_expand U) ch ->
     modexp_member_kind_order Θ Ξ p (me_lit U) ch )
(** A selection ([modexp_member_kind_mem], [modexp_member_kind_mem_dm]): the order of the longer chain *)
| modexp_member_kind_order_mem :
  `( modexp_member_kind_order Θ Ξ p E (y :: ch) ->
     modexp_member_kind_order Θ Ξ p (me_mem E y) ch )
(** An application ([modexp_member_kind_app]): the order of the chain in the module
    applied *)
| modexp_member_kind_order_app :
  `( modexp_member_kind_order Θ Ξ p E ch ->
     modexp_member_kind_order Θ Ξ p (me_app E N) ch )

with kinds_env_order (Θ : gdeps) (Ξ : gstack) : env -> gmod -> Prop :=
(** The empty body ([kinds_env_nil]) *)
| kinds_env_order_nil :
  `( kinds_env_order Θ Ξ p gm_nil )
(** An entry ([kinds_env_ext]): the order of the body before it *)
| kinds_env_order_ext :
  `( kinds_env_order Θ Ξ p Φ ->
     kinds_env_order Θ Ξ p (gm_ext Φ y E) ).

#[local]
Hint Constructors dmod_member_kind_order gunit_member_kind_order modexp_member_kind_order kinds_env_order : mctt.

Lemma kind_order_sound : forall Θ Ξ,
    (forall h ch k, dmod_member_kind Θ Ξ h ch k -> dmod_member_kind_order Θ Ξ h ch) /\
    (forall p U ch k, gunit_member_kind Θ Ξ p U ch k -> gunit_member_kind_order Θ Ξ p U ch) /\
    (forall p E ch k, modexp_member_kind Θ Ξ p E ch k -> modexp_member_kind_order Θ Ξ p E ch) /\
    (forall p Φ p1, kinds_env Θ Ξ p Φ p1 -> kinds_env_order Θ Ξ p Φ).
Proof.
  intros Θ Ξ; pose proof (@functional_kind Θ Ξ) as (_ & _ & _ & Fk).
  apply kind_mut_ind; intros; try solve [ econstructor; eauto ].
  all: lazymatch goal with
    | _ : gm_prefix_upto _ _ = Some (gm_ext _ _ (ge_mod _ _)) |- gunit_member_kind_order _ _ _ _ _ => eapply gunit_member_kind_order_mod
    | _ : gm_prefix_upto _ _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)), _ : _ <> nil |- gunit_member_kind_order _ _ _ _ _ =>
        eapply gunit_member_kind_order_dm_step
    | _ : gm_prefix_upto _ _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- gunit_member_kind_order _ _ _ _ _ => eapply gunit_member_kind_order_dm_here
    | _ : gc_module _ _ _ = Some (mr_alias _), _ : dm_path _ _ _ |- dmod_member_kind_order _ _ _ (_ :: nil) => eapply dmod_member_kind_order_global_alias_dm
    | |- _ => econstructor
    end; eauto; intros;
    repeat match goal with
      | H1 : kinds_env _ _ ?p ?Φ ?r1, H2 : kinds_env _ _ ?p ?Φ ?r2 |- _ =>
          assert_fails (constr_eq r1 r2); rewrite <- (Fk _ _ _ H1 _ H2) in *; clear H2
      end;
    first [ solve [ rewrite List.app_nil_r; eauto ]
          | solve [ match goal with Hn : ?a <> ?a |- _ => exfalso; exact (Hn eq_refl) end ]
          | eauto ].
Qed.

(** Whether a global path names a member with a term part and a module
    part, decided by its lookups. *)
Definition dm_path_dec (Θ : gdeps) (Ξ : gstack) (p : qname) : {dm_path Θ Ξ p} + {~ dm_path Θ Ξ p}.
Proof.
  destruct (ind_mlookup Θ Ξ p) as [r |] eqn:Ei; [ left; left; eauto |].
  destruct (record_lookup Θ Ξ p) as [R |] eqn:Er; [ left; right; left; eauto |].
  destruct (gc_entry Θ Ξ p) as [[| | | pv A M U |] |] eqn:Ee;
    try (right; intros [(r0 & H) | [(R0 & H) | (pv0 & A0 & M0 & U0 & H)]]; congruence).
  left; right; right; eauto.
Defined.

(** The same, through the lookups of a fast context *)
Definition dm_path_fast_dec (F : FCtx) (p : qname) : {dm_path (fc_deps F) (fc_stack F) p} + {~ dm_path (fc_deps F) (fc_stack F) p}.
Proof.
  destruct (fc_mlookup F p) as [r |] eqn:Ei; [ left; left; exists r; rewrite fc_mlookup_ok; exact Ei |].
  destruct (fc_record F p) as [R |] eqn:Er; [ left; right; left; exists R; rewrite fc_record_ok; exact Er |].
  destruct (fc_entry F p) as [[| | | pv A M u |] |] eqn:Ee;
    try (right; intros [(r0 & H) | [(R0 & H) | (pv0 & A0 & M0 & U0 & H)]];
         rewrite ?fc_mlookup_ok, ?fc_record_ok, ?fc_entry_ok, ?Ei, ?Er, ?Ee in H; cbn in H; congruence).
  left; right; right; exists pv, A, M, (decode_unit u); rewrite fc_entry_ok, Ee; reflexivity.
Defined.

(** The operations on fast values, read through their erasure equations *)
#[local] Opaque fenv_var fenv_type fenv_mod fextend_env fextend_env_mod fextend_env_dm fenv_extend_typed fenv_tele
  fdomain_level_suc fdomain_level_max fdomain_level_lit fdm_clo fkinds_pads fkinds_body_entry carry.

(** The kinds, computed through the fast context [F] *)
Section KindImpl.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  #[local]
  Ltac kinds_obligation_inv :=
    match goal with
    | H : dmod_member_kind_order _ _ _ _ |- _ => progressive_invert H
    | H : gunit_member_kind_order _ _ _ _ _ |- _ => progressive_invert H
    | H : modexp_member_kind_order _ _ _ _ _ |- _ => progressive_invert H
    | H : kinds_env_order _ _ _ _ |- _ => progressive_invert H
    end.

  #[local]
  Ltac kinds_obligation_glob :=
    repeat match goal with
      | H : (exists _ _, gc_module _ _ _ = Some _) \/ (exists _, gc_frame _ _ = Some _) |- _ =>
          destruct H as [(? & ? & ?) | (? & ?)]
      | H : (exists _, gc_loc _ _ _ = Some _) \/ (exists _ _ _ _ _, gc_resolve _ _ _ = Some _) |- _ =>
          destruct H as [(? & ?) | (? & ? & ? & ? & ? & ?)]
      | H1 : gc_loc _ _ ?p = Some _, H2 : gc_module _ _ ?p = Some (mr_alias _) |- _ =>
          exfalso; exact (gc_loc_not_alias _ _ _ _ _ H1 H2)
      | H1 : gc_resolve _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_resolve _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gc_module _ _ ?p = Some _, H2 : gc_module _ _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_module _ _ ?p = Some _, H2 : gc_module _ _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gc_frame _ ?p = Some _, H2 : gc_frame _ ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_frame _ ?p = Some _, H2 : gc_frame _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = Some _ |- _ =>
          rewrite H1 in H2; first [ discriminate H2 | injection H2; clear H2; intros; subst ]
      | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gc_module _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = Some _ |- _ =>
          rewrite (gc_module_resolve _ _ _ _ H1) in H2; discriminate H2
      | H1 : gc_frame _ ?p = Some _, H2 : gc_resolve _ _ ?p = Some _ |- _ =>
          rewrite (gc_frame_resolve _ _ _ _ H1) in H2; discriminate H2
      | H1 : dm_path _ _ ?p, H2 : ~ dm_path _ _ ?p |- _ => exfalso; exact (H2 H1)
      | H1 : gc_resolve _ _ ?p = Some (ge_def _ _ _ _ _), H2 : dm_path _ _ ?p |- _ =>
          exfalso; exact (gc_resolve_def_not_dm _ _ _ _ _ _ _ _ H1 H2)
      | H : (@nil ?T) <> nil \/ _ |- _ => destruct H as [H | H]; [ exfalso; exact (H eq_refl) |]
      | H : (@nil ?T) <> nil |- _ => exfalso; exact (H eq_refl)
      end.

  #[local]
  Ltac kinds_obligation_split :=
    match goal with
    | H : dmod_member_kind_order _ _ _ _ |- _ => dependent destruction H
    | H : gunit_member_kind_order _ _ _ _ _ |- _ => dependent destruction H
    | H : modexp_member_kind_order _ _ _ _ _ |- _ => dependent destruction H
    | H : kinds_env_order _ _ _ _ |- _ => dependent destruction H
    end.

  #[local]
  Ltac kinds_obligation_finish :=
    kinds_obligation_glob;
    try solve [ intuition discriminate ];
    try solve [ eapply dmod_member_kind_global_step;
                [ first [ left; eexists; eassumption | right; do 5 eexists; eassumption ]
                | first [ left; discriminate | right; assumption ] | eassumption ] ];
    (** a selection away from the empty chain, or of no member with a term
        part and a module part *)
    try solve [ first [ eapply dmod_member_kind_member | eapply modexp_member_kind_mem ]; [ eassumption | first [ left; discriminate | right; discriminate ] ] ];
    try solve [ first [ apply dmod_member_kind_member_dm | apply modexp_member_kind_mem_dm ]; rewrite ?List.app_nil_r in *; eassumption ];
    try solve [ eauto 6 with mctt ];
    try econstructor; eauto with mctt.

  #[local]
  Ltac kinds_obligation :=
    intros; cbv beta in *; cbn [option_map decode_loc fst snd] in *; ferase_norm; repeat kinds_obligation_inv;
    first [ solve [ kinds_obligation_finish ] | solve [ kinds_obligation_split; kinds_obligation_finish ] | kinds_obligation_finish ].

  #[local]
  Ltac kinds_obligation_auto :=
    intros;
    lazymatch goal with
    | |- dmod_member_kind_order _ _ _ _ => kinds_obligation
    | |- gunit_member_kind_order _ _ _ _ _ => kinds_obligation
    | |- modexp_member_kind_order _ _ _ _ _ => kinds_obligation
    | |- kinds_env_order _ _ _ _ => kinds_obligation
    | |- _ => abstract kinds_obligation
    end.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations dmod_member_kind_impl (h : fdmod) ch (H : dmod_member_kind_order Θ Ξ (fdmod_erase h) ch) :
      { k | dmod_member_kind Θ Ξ (fdmod_erase h) ch k } by struct H :=
  | fdm_global pq args, nil, H with gc_frame_f F pq := {
    | exist _ (Some TΦ) Ef => exist _ member_kind_mod _
    | exist _ None Ef with gc_module_f F pq := {
      | exist _ (Some (mr_body T oD)) E => exist _ member_kind_mod _
      | exist _ _ E with gc_resolve_f F pq := {
        | exist _ (Some (ge_def b pv ra A B)) E2 => exist _ (member_kind_term ra) _
        | exist _ _ E2 => False_rect _ _ } } }
  | fdm_global pq args, y :: ch, H with dm_path_fast_dec F (qname_app pq (y :: nil)), ch := {
    | left Hd, nil with gc_module_f F (qname_app pq (y :: nil)) := {
      (** a definition with a module part stored as an alias: [dm_of] its
          alias's kind *)
      | exist _ (Some (mr_alias U)) E =>
          let (k, Hk) := gunit_member_kind_impl nil (gunit_expand U) nil _ in
          exist _ (dm_of k) _
      | exist _ _ E => exist _ member_kind_dm _ }
    | _, ch' with gc_module_f F (qname_app pq (y :: nil)) := {
      | exist _ (Some (mr_alias U)) E =>
          let (k, Hk) := gunit_member_kind_impl nil (gunit_expand U) ch' _ in
          exist _ k _
      | exist _ _ E =>
          let (k, Hk) := dmod_member_kind_impl (fdm_global (qname_app pq (y :: nil)) args) ch' _ in
          exist _ k _ } }
  | fdm_local Δ D p, ch, H =>
      let (k, Hk) := gunit_member_kind_impl p (gunit_expand (gu_mk Δ D)) ch _ in
      exist _ k _
  | fdm_member h ch0, ch, H with dmod_member_kind_impl h (ch0 ++ ch) _ := {
    (** at the empty chain, a member with a term part and a module part is
        selected as a module *)
    | exist _ member_kind_dm Hk with ch := {
      | nil => exist _ member_kind_mod _
      | _ :: _ => exist _ member_kind_dm _ }
    | exist _ k Hk => exist _ k _ }

  with gunit_member_kind_impl (p : fenv) U ch (H : gunit_member_kind_order Θ Ξ (fenv_erase p) U ch) :
      { k | gunit_member_kind Θ Ξ (fenv_erase p) U ch k } by struct H :=
  | p, gu_mk Δ (md_body sm Φ), nil, H => exist _ member_kind_mod _
  | p, gu_mk Δ (md_body sm Φ), x :: ch, H with inspect (gm_prefix_upto Φ x) := {
    | exist _ (Some (gm_ext Φ' _ (ge_def b pv ra A B))) P => exist _ (member_kind_term ra) _
    | exist _ (Some (gm_ext Φ' _ (ge_mod pm Uy))) P =>
        let (p1, Hp1) := kinds_env_impl (fkinds_pads (List.length Δ) p) Φ' _ in
        let (k, Hk) := gunit_member_kind_impl p1 (gunit_expand Uy) ch _ in
        exist _ k _
    | exist _ (Some (gm_ext Φ' _ (ge_def_mod pv A M Uy))) P with ch := {
      (** itself: [dm_of] its module part's kind *)
      | nil =>
          let (p1, Hp1) := kinds_env_impl (fkinds_pads (List.length Δ) p) Φ' _ in
          let (k, Hk) := gunit_member_kind_impl p1 (gunit_expand Uy) nil _ in
          exist _ (dm_of k) _
      | c :: ch' =>
          let (p1, Hp1) := kinds_env_impl (fkinds_pads (List.length Δ) p) Φ' _ in
          let (k, Hk) := gunit_member_kind_impl p1 (gunit_expand Uy) (c :: ch') _ in
          exist _ k _ }
    | exist _ _ P => False_rect _ _ }
  | p, gu_mk Δ (md_alias E), ch, H =>
      let (k, Hk) := modexp_member_kind_impl (fkinds_pads (List.length Δ) p) E ch _ in
      exist _ k _

  with modexp_member_kind_impl (p : fenv) E ch (H : modexp_member_kind_order Θ Ξ (fenv_erase p) E ch) :
      { k | modexp_member_kind Θ Ξ (fenv_erase p) E ch k } by struct H :=
  | p, me_unit fp, ch, H =>
      let (k, Hk) := dmod_member_kind_impl (fdm_global (q_abs fp nil) nil) ch _ in
      exist _ k _
  | p, me_var x, ch, H =>
      let (k, Hk) := dmod_member_kind_impl (fenv_mod p x) ch _ in
      exist _ k _
  | p, me_lit U, ch, H =>
      let (k, Hk) := gunit_member_kind_impl p (gunit_expand U) ch _ in
      exist _ k _
  | p, me_mem E y, ch, H with modexp_member_kind_impl p E (y :: ch) _ := {
    (** at the empty chain, a member with a term part and a module part is
        selected as a module *)
    | exist _ member_kind_dm Hk with ch := {
      | nil => exist _ member_kind_mod _
      | _ :: _ => exist _ member_kind_dm _ }
    | exist _ k Hk => exist _ k _ }
  | p, me_app E N, ch, H =>
      let (k, Hk) := modexp_member_kind_impl p E ch _ in
      exist _ k _

  with kinds_env_impl (p : fenv) Φ (H : kinds_env_order Θ Ξ (fenv_erase p) Φ) :
      { p1 : fenv | kinds_env Θ Ξ (fenv_erase p) Φ (fenv_erase p1) } by struct H :=
  | p, gm_nil, H => exist _ p _
  | p, gm_ext Φ y E, H =>
      let (p1, Hp1) := kinds_env_impl p Φ _ in
      exist _ (fkinds_body_entry p1 y E :: p1) _
  (** an open: no order, as kinds read bodies expanded *)
  | p, gm_open Φ E its Φg, H => False_rect _ _.

  Solve All Obligations with kinds_obligation_auto.
End KindImpl.

(** ** The Outermost Missing Parameter

    A closure lacking the parameters [Δ ++ e :: nil] takes an argument for
    [e], the outermost one; both evaluators find it with [tele_snoc]. *)
Definition tele_snoc (Δ : ctx) : option (ctx * centry) :=
  match rev Δ with
  | nil => None
  | e :: r => Some (rev r, e)
  end.

Lemma tele_snoc_some : forall Δ Δ0 e, tele_snoc Δ = Some (Δ0, e) -> Δ = Δ0 ++ e :: nil.
Proof.
  unfold tele_snoc; intros * H.
  destruct (rev Δ) as [| e' r] eqn:E; [ discriminate |]; injection H as <- <-.
  rewrite <- (rev_involutive Δ), E; reflexivity.
Qed.

Lemma tele_snoc_app : forall Δ0 e, tele_snoc (Δ0 ++ e :: nil) = Some (Δ0, e).
Proof. intros; unfold tele_snoc; rewrite rev_unit, rev_involutive; reflexivity. Qed.
