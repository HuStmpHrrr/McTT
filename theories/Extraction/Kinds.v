From Equations Require Import Equations.
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Extraction Require Import Lookup.
Import Domain_Notations.

Generalizable All Variables.

(** * Computing the Kinds of Members

    Evaluation reads a saturated body through the entries its local opens
    generate ([kinds_body_xp]), which the kinds of the members its items name
    determine ([kinds_items_gen]).  Both evaluators compute them with [kinds_body_xp_impl], by
    recursion on a termination order. *)

(** The orders mirror the kinds relations, one for each; a chain of a
    global alias recurses into the alias's unit, and a body's member into
    the environment the kinds read off the body before it.  An item naming
    a member of a target is ordered by that member's kind, which decides
    whether the chain goes on into it. *)

Inductive dmod_member_kind_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
(** The path names a definition ([dmod_member_kind_global_here_def]): no recursion *)
| dmod_member_kind_order_global_here_def :
  `( gc_resolve Θ Ξ pq = Some (ge_def b pv A B) ->
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
    the chain in the alias's unit *)
| dmod_member_kind_order_global_alias :
  `( gc_module Θ Ξ (qname_app pq (y :: nil)) = Some (mr_alias U) ->
     ch <> nil \/ ~ dm_path Θ Ξ (qname_app pq (y :: nil)) ->
     gunit_member_kind_order Θ Ξ nil U ch ->
     dmod_member_kind_order Θ Ξ (dm_global pq args) (y :: ch) )
(** The member [y] is a definition with a module part stored as an alias
    ([dmod_member_kind_global_alias_dm]): the order of the empty chain in the alias's
    unit *)
| dmod_member_kind_order_global_alias_dm :
  `( gc_module Θ Ξ (qname_app pq (y :: nil)) = Some (mr_alias U) ->
     dm_path Θ Ξ (qname_app pq (y :: nil)) ->
     gunit_member_kind_order Θ Ξ nil U nil ->
     dmod_member_kind_order Θ Ξ (dm_global pq args) (y :: nil) )
(** The member [y] is located in place ([dmod_member_kind_global_step]): the order of the
    rest of the chain at the path of [y] *)
| dmod_member_kind_order_global_step :
  `( (exists TΦ, gc_loc Θ Ξ (qname_app pq (y :: nil)) = Some TΦ) \/
     (exists b pv A B, gc_resolve Θ Ξ (qname_app pq (y :: nil)) = Some (ge_def b pv A B)) ->
     ch <> nil \/ ~ dm_path Θ Ξ (qname_app pq (y :: nil)) ->
     dmod_member_kind_order Θ Ξ (dm_global (qname_app pq (y :: nil)) args) ch ->
     dmod_member_kind_order Θ Ξ (dm_global pq args) (y :: ch) )
(** A closure ([dmod_member_kind_local]): the order of its unit *)
| dmod_member_kind_order_local :
  `( gunit_member_kind_order Θ Ξ p (gu_mk Δ D) ch ->
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
  `( gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A B)) ->
     gunit_member_kind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) (x :: nil) )
(** A submodule of the body ([gunit_member_kind_mod]): the order of the entries before it,
    and of the rest of the chain in its unit, in each environment they
    make *)
| gunit_member_kind_order_mod :
  `( gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
     kinds_env_order Θ Ξ (kinds_placeholders (List.length Δ) p) Φ' ->
     (forall p1, kinds_env Θ Ξ (kinds_placeholders (List.length Δ) p) Φ' p1 -> gunit_member_kind_order Θ Ξ p1 Uy ch) ->
     gunit_member_kind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) (y :: ch) )
(** A definition with a module part of the body, at the end of the chain
    ([gunit_member_kind_dm_here]): the order of the entries before it, and of the empty
    chain in its module part, in each environment they make *)
| gunit_member_kind_order_dm_here :
  `( gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_def_mod pv A M Uy)) ->
     kinds_env_order Θ Ξ (kinds_placeholders (List.length Δ) p) Φ' ->
     (forall p1, kinds_env Θ Ξ (kinds_placeholders (List.length Δ) p) Φ' p1 -> gunit_member_kind_order Θ Ξ p1 Uy nil) ->
     gunit_member_kind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) (y :: nil) )
(** A definition with a module part of the body, the chain going on
    ([gunit_member_kind_dm_step]): the order of the entries before it, and of the rest of
    the chain in its module part, in each environment they make *)
| gunit_member_kind_order_dm_step :
  `( gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_def_mod pv A M Uy)) ->
     ch <> nil ->
     kinds_env_order Θ Ξ (kinds_placeholders (List.length Δ) p) Φ' ->
     (forall p1, kinds_env Θ Ξ (kinds_placeholders (List.length Δ) p) Φ' p1 -> gunit_member_kind_order Θ Ξ p1 Uy ch) ->
     gunit_member_kind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) (y :: ch) )
(** An item naming a member of the target ([gunit_member_kind_item_def], [gunit_member_kind_item_mod],
    [gunit_member_kind_item_dm]): the order of the entries before the open, of the
    member's kind, and of the chain in the member when the member is a
    module or has a module part *)
| gunit_member_kind_order_item_some :
  `( gm_item_upto Φ x = Some (Φ0, E, its1, (Some n, d, pv)) ->
     kinds_env_order Θ Ξ (kinds_placeholders (List.length Δ) p) Φ0 ->
     (forall p0, kinds_env Θ Ξ (kinds_placeholders (List.length Δ) p) Φ0 p0 ->
        modexp_member_kind_order Θ Ξ p0 E (n :: nil) /\
        ((modexp_member_kind Θ Ξ p0 E (n :: nil) member_kind_term /\ ch = nil) \/
         (modexp_member_kind Θ Ξ p0 E (n :: nil) member_kind_mod /\ modexp_member_kind_order Θ Ξ p0 E (n :: ch)) \/
         (modexp_member_kind Θ Ξ p0 E (n :: nil) member_kind_dm /\ modexp_member_kind_order Θ Ξ p0 E (n :: ch)))) ->
     gunit_member_kind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) (x :: ch) )
(** An item naming the target itself ([gunit_member_kind_item_self]): the order of the
    entries before the open, and of the chain in the target *)
| gunit_member_kind_order_item_none :
  `( gm_item_upto Φ x = Some (Φ0, E, its1, (None, d, pv)) ->
     kinds_env_order Θ Ξ (kinds_placeholders (List.length Δ) p) Φ0 ->
     (forall p0, kinds_env Θ Ξ (kinds_placeholders (List.length Δ) p) Φ0 p0 -> modexp_member_kind_order Θ Ξ p0 E ch) ->
     gunit_member_kind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) (x :: ch) )
(** An alias unit ([gunit_member_kind_alias]): the order of the chain in its target *)
| gunit_member_kind_order_alias :
  `( modexp_member_kind_order Θ Ξ (kinds_placeholders (List.length Δ) p) E ch ->
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
(** A literal unit ([modexp_member_kind_lit]): the order of the chain in the unit *)
| modexp_member_kind_order_lit :
  `( gunit_member_kind_order Θ Ξ p U ch ->
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
     kinds_env_order Θ Ξ p (gm_ext Φ y E) )
(** An open ([kinds_env_open]): the order of the body before it, and of its items
    in each environment that body makes *)
| kinds_env_order_open :
  `( kinds_env_order Θ Ξ p Φ ->
     (forall p1, kinds_env Θ Ξ p Φ p1 -> kinds_items_gen_order Θ Ξ p1 E its) ->
     kinds_env_order Θ Ξ p (gm_open Φ E its) )

with kinds_items_gen_order (Θ : gdeps) (Ξ : gstack) : env -> modexp -> list iitem -> Prop :=
(** No items ([kinds_items_gen_nil]) *)
| kinds_items_gen_order_nil :
  `( kinds_items_gen_order Θ Ξ p E nil )
(** An item naming the target itself ([kinds_items_gen_self]): the order of the other
    items *)
| kinds_items_gen_order_self :
  `( kinds_items_gen_order Θ Ξ p E its ->
     kinds_items_gen_order Θ Ξ p E ((None, d, pv) :: its) )
(** An item naming a member ([kinds_items_gen_def], [kinds_items_gen_mod], [kinds_items_gen_dm]): the order of
    the member's kind, and of the other items *)
| kinds_items_gen_order_name :
  `( modexp_member_kind_order Θ Ξ p E (n :: nil) ->
     kinds_items_gen_order Θ Ξ p E its ->
     kinds_items_gen_order Θ Ξ p E ((Some n, d, pv) :: its) ).

(** The order of reading a body through the entries its opens generate. *)
Inductive kinds_body_xp_order (Θ : gdeps) (Ξ : gstack) : env -> gmod -> Prop :=
(** The empty body ([kinds_body_xp_nil]) *)
| kinds_body_xp_order_nil :
  `( kinds_body_xp_order Θ Ξ p gm_nil )
(** An entry ([kinds_body_xp_ext]): the order of the body before it *)
| kinds_body_xp_order_ext :
  `( kinds_body_xp_order Θ Ξ p Φ ->
     kinds_body_xp_order Θ Ξ p (gm_ext Φ y E) )
(** An open ([kinds_body_xp_open]): the order of the body before it, and, for each
    expansion of that body, of the environment it makes and of the items in
    each such environment *)
| kinds_body_xp_order_open :
  `( kinds_body_xp_order Θ Ξ p Φ ->
     (forall Φx, kinds_body_xp Θ Ξ p Φ Φx -> kinds_env_order Θ Ξ p Φx /\
        forall p1, kinds_env Θ Ξ p Φx p1 -> kinds_items_gen_order Θ Ξ p1 E its) ->
     kinds_body_xp_order Θ Ξ p (gm_open Φ E its) ).

#[local]
Hint Constructors dmod_member_kind_order gunit_member_kind_order modexp_member_kind_order kinds_env_order kinds_items_gen_order kinds_body_xp_order : mctt.

Lemma kind_order_sound : forall Θ Ξ,
    (forall h ch k, dmod_member_kind Θ Ξ h ch k -> dmod_member_kind_order Θ Ξ h ch) /\
    (forall p U ch k, gunit_member_kind Θ Ξ p U ch k -> gunit_member_kind_order Θ Ξ p U ch) /\
    (forall p E ch k, modexp_member_kind Θ Ξ p E ch k -> modexp_member_kind_order Θ Ξ p E ch) /\
    (forall p Φ p1, kinds_env Θ Ξ p Φ p1 -> kinds_env_order Θ Ξ p Φ) /\
    (forall p Φ Φx, kinds_body_xp Θ Ξ p Φ Φx -> kinds_body_xp_order Θ Ξ p Φ) /\
    (forall p E its gs, kinds_items_gen Θ Ξ p E its gs -> kinds_items_gen_order Θ Ξ p E its).
Proof.
  intros Θ Ξ; pose proof (@functional_kind Θ Ξ) as (_ & _ & _ & Fk & Fb & _).
  apply kind_mut_ind; intros; try solve [ econstructor; eauto ].
  all: lazymatch goal with
    | _ : gm_item_upto _ _ = Some (_, _, _, (Some _, _, _)) |- gunit_member_kind_order _ _ _ _ _ => eapply gunit_member_kind_order_item_some
    | _ : gm_item_upto _ _ = Some (_, _, _, (None, _, _)) |- gunit_member_kind_order _ _ _ _ _ =>
        eapply gunit_member_kind_order_item_none
    | _ : gm_prefix_upto _ _ = Some (gm_ext _ _ (ge_mod _ _)) |- gunit_member_kind_order _ _ _ _ _ => eapply gunit_member_kind_order_mod
    | _ : gm_prefix_upto _ _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)), _ : _ <> nil |- gunit_member_kind_order _ _ _ _ _ =>
        eapply gunit_member_kind_order_dm_step
    | _ : gm_prefix_upto _ _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- gunit_member_kind_order _ _ _ _ _ => eapply gunit_member_kind_order_dm_here
    | |- kinds_body_xp_order _ _ _ (gm_open _ _ _) => eapply kinds_body_xp_order_open
    | _ : gc_module _ _ _ = Some (mr_alias _), _ : dm_path _ _ _ |- dmod_member_kind_order _ _ _ (_ :: nil) => eapply dmod_member_kind_order_global_alias_dm
    | |- _ => econstructor
    end; eauto; intros;
    repeat match goal with
      | H1 : kinds_env _ _ ?p ?Φ ?r1, H2 : kinds_env _ _ ?p ?Φ ?r2 |- _ =>
          assert_fails (constr_eq r1 r2); rewrite <- (Fk _ _ _ H1 _ H2) in *; clear H2
      | H1 : kinds_body_xp _ _ ?p ?Φ ?r1, H2 : kinds_body_xp _ _ ?p ?Φ ?r2 |- _ =>
          assert_fails (constr_eq r1 r2); rewrite <- (Fb _ _ _ H1 _ H2) in *; clear H2
      end;
    first [ split; [ eauto | first [ left; split; [ eassumption | reflexivity ]
                                   | solve [ right; left; split; eauto ] | solve [ right; right; split; eauto ] ] ]
          | split; [ eauto | intros;
              repeat match goal with
                | H1 : kinds_env _ _ ?p ?Φ ?r1, H2 : kinds_env _ _ ?p ?Φ ?r2 |- _ =>
                    assert_fails (constr_eq r1 r2); rewrite <- (Fk _ _ _ H1 _ H2) in *; clear H2
                end; eauto ]
          | solve [ rewrite List.app_nil_r; eauto ]
          | solve [ match goal with Hn : ?a <> ?a |- _ => exfalso; exact (Hn eq_refl) end ]
          | eauto ].
Qed.

Lemma kinds_items_gen_order_sound : forall Θ Ξ p E its gs, kinds_items_gen Θ Ξ p E its gs -> kinds_items_gen_order Θ Ξ p E its.
Proof. intros Θ Ξ; pose proof (kind_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma kinds_body_xp_order_sound : forall Θ Ξ p Φ Φx, kinds_body_xp Θ Ξ p Φ Φx -> kinds_body_xp_order Θ Ξ p Φ.
Proof. intros Θ Ξ; pose proof (kind_order_sound Θ Ξ); destruct_all; eauto. Qed.

#[export]
Hint Resolve kinds_items_gen_order_sound kinds_body_xp_order_sound : mctt.

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
Definition dm_path_fdec (F : FCtx) (p : qname) : {dm_path (fc_deps F) (fc_stack F) p} + {~ dm_path (fc_deps F) (fc_stack F) p}.
Proof.
  destruct (fc_mlookup F p) as [r |] eqn:Ei; [ left; left; exists r; rewrite fc_mlookup_ok; exact Ei |].
  destruct (fc_record F p) as [R |] eqn:Er; [ left; right; left; exists R; rewrite fc_record_ok; exact Er |].
  destruct (fc_entry F p) as [[| | | pv A M u |] |] eqn:Ee;
    try (right; intros [(r0 & H) | [(R0 & H) | (pv0 & A0 & M0 & U0 & H)]];
         rewrite ?fc_mlookup_ok, ?fc_record_ok, ?fc_entry_ok, ?Ei, ?Er, ?Ee in H; cbn in H; congruence).
  left; right; right; exists pv, A, M, (dec_unit u); rewrite fc_entry_ok, Ee; reflexivity.
Defined.

(** The kinds, computed through the fast context [F] *)
Section KindImpl.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  #[local]
  Ltac kd_inv :=
    match goal with
    | H : dmod_member_kind_order _ _ _ _ |- _ => progressive_invert H
    | H : gunit_member_kind_order _ _ _ _ _ |- _ => progressive_invert H
    | H : modexp_member_kind_order _ _ _ _ _ |- _ => progressive_invert H
    | H : kinds_env_order _ _ _ _ |- _ => progressive_invert H
    | H : kinds_items_gen_order _ _ _ _ _ |- _ => progressive_invert H
    | H : kinds_body_xp_order _ _ _ _ |- _ => progressive_invert H
    end.

  #[local]
  Ltac kd_glob :=
    repeat match goal with
      | H : (exists _ _, gc_module _ _ _ = Some _) \/ (exists _, gc_frame _ _ = Some _) |- _ =>
          destruct H as [(? & ? & ?) | (? & ?)]
      | H : (exists _, gc_loc _ _ _ = Some _) \/ (exists _ _ _ _, gc_resolve _ _ _ = Some _) |- _ =>
          destruct H as [(? & ?) | (? & ? & ? & ? & ?)]
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
      | H1 : gm_item_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = Some _ |- _ =>
          rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gm_item_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = Some _ |- _ =>
          rewrite (gm_prefix_item_excl _ _ _ H1) in H2; discriminate H2
      | H1 : gc_module _ _ ?p = Some _, H2 : gc_resolve _ _ ?p = Some _ |- _ =>
          rewrite (gc_module_resolve _ _ _ _ H1) in H2; discriminate H2
      | H1 : gc_frame _ ?p = Some _, H2 : gc_resolve _ _ ?p = Some _ |- _ =>
          rewrite (gc_frame_resolve _ _ _ _ H1) in H2; discriminate H2
      | H1 : dm_path _ _ ?p, H2 : ~ dm_path _ _ ?p |- _ => exfalso; exact (H2 H1)
      | H1 : gc_resolve _ _ ?p = Some (ge_def _ _ _ _), H2 : dm_path _ _ ?p |- _ =>
          exfalso; exact (gc_resolve_def_not_dm _ _ _ _ _ _ _ H1 H2)
      | H : (@nil ?T) <> nil \/ _ |- _ => destruct H as [H | H]; [ exfalso; exact (H eq_refl) |]
      | H : (@nil ?T) <> nil |- _ => exfalso; exact (H eq_refl)
      | H : forall p0, kinds_env _ _ ?qe ?Φ p0 -> _ /\ _, Hk : kinds_env _ _ ?qe ?Φ ?p0 |- _ =>
          let Ha := fresh "Ha" in let Hb := fresh "Hb" in destruct (H _ Hk) as [Ha Hb]; clear H
      | H : forall Φx, kinds_body_xp _ _ ?qe ?Φ Φx -> _ /\ _, Hk : kinds_body_xp _ _ ?qe ?Φ ?Φx |- _ =>
          let Ha := fresh "Ha" in let Hb := fresh "Hb" in destruct (H _ Hk) as [Ha Hb]; clear H
      | H : (modexp_member_kind _ _ ?p0 ?E ?ch member_kind_term /\ _) \/ (modexp_member_kind _ _ ?p0 ?E ?ch member_kind_mod /\ _) \/ (modexp_member_kind _ _ ?p0 ?E ?ch member_kind_dm /\ _),
        Hk : modexp_member_kind _ _ ?p0 ?E ?ch member_kind_term |- _ =>
          destruct H as [[_ ?] | [[Hk' _] | [Hk' _]]];
          [ subst
          | exfalso; pose proof (proj1 (proj2 (proj2 (@functional_kind Θ Ξ))) _ _ _ _ Hk _ Hk'); discriminate
          | exfalso; pose proof (proj1 (proj2 (proj2 (@functional_kind Θ Ξ))) _ _ _ _ Hk _ Hk'); discriminate ]
      | H : (modexp_member_kind _ _ ?p0 ?E ?ch member_kind_term /\ _) \/ (modexp_member_kind _ _ ?p0 ?E ?ch member_kind_mod /\ _) \/ (modexp_member_kind _ _ ?p0 ?E ?ch member_kind_dm /\ _),
        Hk : modexp_member_kind _ _ ?p0 ?E ?ch member_kind_mod |- _ =>
          destruct H as [[Hk' _] | [[_ ?] | [Hk' _]]];
          [ exfalso; pose proof (proj1 (proj2 (proj2 (@functional_kind Θ Ξ))) _ _ _ _ Hk _ Hk'); discriminate
          |
          | exfalso; pose proof (proj1 (proj2 (proj2 (@functional_kind Θ Ξ))) _ _ _ _ Hk _ Hk'); discriminate ]
      | H : (modexp_member_kind _ _ ?p0 ?E ?ch member_kind_term /\ _) \/ (modexp_member_kind _ _ ?p0 ?E ?ch member_kind_mod /\ _) \/ (modexp_member_kind _ _ ?p0 ?E ?ch member_kind_dm /\ _),
        Hk : modexp_member_kind _ _ ?p0 ?E ?ch member_kind_dm |- _ =>
          destruct H as [[Hk' _] | [[Hk' _] | [_ ?]]];
          [ exfalso; pose proof (proj1 (proj2 (proj2 (@functional_kind Θ Ξ))) _ _ _ _ Hk _ Hk'); discriminate
          | exfalso; pose proof (proj1 (proj2 (proj2 (@functional_kind Θ Ξ))) _ _ _ _ Hk _ Hk'); discriminate
          | ]
      end.

  #[local]
  Ltac kd_split :=
    match goal with
    | H : dmod_member_kind_order _ _ _ _ |- _ => dependent destruction H
    | H : gunit_member_kind_order _ _ _ _ _ |- _ => dependent destruction H
    | H : modexp_member_kind_order _ _ _ _ _ |- _ => dependent destruction H
    | H : kinds_env_order _ _ _ _ |- _ => dependent destruction H
    | H : kinds_items_gen_order _ _ _ _ _ |- _ => dependent destruction H
    | H : kinds_body_xp_order _ _ _ _ |- _ => dependent destruction H
    end.

  #[local]
  Ltac kd_finish :=
    kd_glob;
    try solve [ intuition discriminate ];
    try solve [ eapply dmod_member_kind_global_step;
                [ first [ left; eexists; eassumption | right; do 4 eexists; eassumption ]
                | first [ left; discriminate | right; assumption ] | eassumption ] ];
    (** a selection away from the empty chain, or of no member with a term
        part and a module part *)
    try solve [ first [ eapply dmod_member_kind_member | eapply modexp_member_kind_mem ]; [ eassumption | first [ left; discriminate | right; discriminate ] ] ];
    try solve [ first [ apply dmod_member_kind_member_dm | apply modexp_member_kind_mem_dm ]; rewrite ?List.app_nil_r in *; eassumption ];
    try solve [ eauto 6 with mctt ];
    try econstructor; eauto with mctt.

  #[local]
  Ltac kd_obl :=
    intros; cbv beta in *; cbn [option_map dec_loc fst snd] in *; repeat kd_inv;
    first [ solve [ kd_finish ] | solve [ kd_split; kd_finish ] | kd_finish ].

  #[local]
  Ltac kd_obl_auto :=
    intros;
    lazymatch goal with
    | |- dmod_member_kind_order _ _ _ _ => kd_obl
    | |- gunit_member_kind_order _ _ _ _ _ => kd_obl
    | |- modexp_member_kind_order _ _ _ _ _ => kd_obl
    | |- kinds_env_order _ _ _ _ => kd_obl
    | |- kinds_items_gen_order _ _ _ _ _ => kd_obl
    | |- kinds_body_xp_order _ _ _ _ => kd_obl
    | |- _ => abstract kd_obl
    end.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations dmod_member_kind_impl h ch (H : dmod_member_kind_order Θ Ξ h ch) : { k | dmod_member_kind Θ Ξ h ch k } by struct H :=
  | dm_global pq args, nil, H with gc_frame_f F pq := {
    | exist _ (Some TΦ) Ef => exist _ member_kind_mod _
    | exist _ None Ef with gc_module_f F pq := {
      | exist _ (Some (mr_body T oD)) E => exist _ member_kind_mod _
      | exist _ _ E with gc_resolve_f F pq := {
        | exist _ (Some (ge_def b pv A B)) E2 => exist _ member_kind_term _
        | exist _ _ E2 => False_rect _ _ } } }
  | dm_global pq args, y :: ch, H with dm_path_fdec F (qname_app pq (y :: nil)), ch := {
    | left Hd, nil with gc_module_f F (qname_app pq (y :: nil)) := {
      (** a definition with a module part stored as an alias: [dm_of] its
          alias's kind *)
      | exist _ (Some (mr_alias U)) E =>
          let (k, Hk) := gunit_member_kind_impl nil U nil _ in
          exist _ (dm_of k) _
      | exist _ _ E => exist _ member_kind_dm _ }
    | _, ch' with gc_module_f F (qname_app pq (y :: nil)) := {
      | exist _ (Some (mr_alias U)) E =>
          let (k, Hk) := gunit_member_kind_impl nil U ch' _ in
          exist _ k _
      | exist _ _ E =>
          let (k, Hk) := dmod_member_kind_impl (dm_global (qname_app pq (y :: nil)) args) ch' _ in
          exist _ k _ } }
  | dm_local Δ D p, ch, H =>
      let (k, Hk) := gunit_member_kind_impl p (gu_mk Δ D) ch _ in
      exist _ k _
  | dm_member h ch0, ch, H with dmod_member_kind_impl h (ch0 ++ ch) _ := {
    (** at the empty chain, a member with a term part and a module part is
        selected as a module *)
    | exist _ member_kind_dm Hk with ch := {
      | nil => exist _ member_kind_mod _
      | _ :: _ => exist _ member_kind_dm _ }
    | exist _ k Hk => exist _ k _ }

  with gunit_member_kind_impl p U ch (H : gunit_member_kind_order Θ Ξ p U ch) : { k | gunit_member_kind Θ Ξ p U ch k } by struct H :=
  | p, gu_mk Δ (md_body sm Φ), nil, H => exist _ member_kind_mod _
  | p, gu_mk Δ (md_body sm Φ), x :: ch, H with inspect (gm_item_upto Φ x) := {
    | exist _ (Some (Φ0, E, its1, (Some n, d, pv))) Ei with kinds_env_impl (kinds_placeholders (List.length Δ) p) Φ0 _ := {
      | exist _ p0 Hp0 with modexp_member_kind_impl p0 E (n :: nil) _ := {
        | exist _ member_kind_term Hk0 => exist _ member_kind_term _
        | exist _ member_kind_mod Hk0 =>
            let (k, Hk) := modexp_member_kind_impl p0 E (n :: ch) _ in
            exist _ k _
        | exist _ member_kind_dm Hk0 =>
            let (k, Hk) := modexp_member_kind_impl p0 E (n :: ch) _ in
            exist _ k _ } }
    | exist _ (Some (Φ0, E, its1, (None, d, pv))) Ei =>
        let (p0, Hp0) := kinds_env_impl (kinds_placeholders (List.length Δ) p) Φ0 _ in
        let (k, Hk) := modexp_member_kind_impl p0 E ch _ in
        exist _ k _
    | exist _ None Ei with inspect (gm_prefix_upto Φ x) := {
      | exist _ (Some (gm_ext Φ' _ (ge_def b pv A B))) P => exist _ member_kind_term _
      | exist _ (Some (gm_ext Φ' _ (ge_mod pm Uy))) P =>
          let (p1, Hp1) := kinds_env_impl (kinds_placeholders (List.length Δ) p) Φ' _ in
          let (k, Hk) := gunit_member_kind_impl p1 Uy ch _ in
          exist _ k _
      | exist _ (Some (gm_ext Φ' _ (ge_def_mod pv A M Uy))) P with ch := {
        (** itself: [dm_of] its module part's kind *)
        | nil =>
            let (p1, Hp1) := kinds_env_impl (kinds_placeholders (List.length Δ) p) Φ' _ in
            let (k, Hk) := gunit_member_kind_impl p1 Uy nil _ in
            exist _ (dm_of k) _
        | c :: ch' =>
            let (p1, Hp1) := kinds_env_impl (kinds_placeholders (List.length Δ) p) Φ' _ in
            let (k, Hk) := gunit_member_kind_impl p1 Uy (c :: ch') _ in
            exist _ k _ }
      | exist _ _ P => False_rect _ _ } }
  | p, gu_mk Δ (md_alias E), ch, H =>
      let (k, Hk) := modexp_member_kind_impl (kinds_placeholders (List.length Δ) p) E ch _ in
      exist _ k _

  with modexp_member_kind_impl p E ch (H : modexp_member_kind_order Θ Ξ p E ch) : { k | modexp_member_kind Θ Ξ p E ch k } by struct H :=
  | p, me_unit fp, ch, H =>
      let (k, Hk) := dmod_member_kind_impl (dm_global (q_abs fp nil) nil) ch _ in
      exist _ k _
  | p, me_var x, ch, H =>
      let (k, Hk) := dmod_member_kind_impl (env_mod p x) ch _ in
      exist _ k _
  | p, me_lit U, ch, H =>
      let (k, Hk) := gunit_member_kind_impl p U ch _ in
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

  with kinds_env_impl p Φ (H : kinds_env_order Θ Ξ p Φ) : { p1 | kinds_env Θ Ξ p Φ p1 } by struct H :=
  | p, gm_nil, H => exist _ p _
  | p, gm_ext Φ y E, H =>
      let (p1, Hp1) := kinds_env_impl p Φ _ in
      exist _ (kinds_body_entry p1 E :: p1) _
  | p, gm_open Φ E its, H =>
      let (p1, Hp1) := kinds_env_impl p Φ _ in
      let (gs, Hgs) := kinds_items_gen_impl p1 E its _ in
      exist _ (kinds_items_gen_env p1 0 gs) _

  with kinds_items_gen_impl p E its (H : kinds_items_gen_order Θ Ξ p E its) : { gs | kinds_items_gen Θ Ξ p E its gs } by struct H :=
  | p, E, nil, H => exist _ nil _
  | p, E, (None, d, pv) :: its, H =>
      let (gs, Hgs) := kinds_items_gen_impl p E its _ in
      exist _ (generated_item_alias d pv E :: gs) _
  | p, E, (Some n, d, pv) :: its, H with modexp_member_kind_impl p E (n :: nil) _ := {
    | exist _ member_kind_term Hk =>
        let (gs, Hgs) := kinds_items_gen_impl p E its _ in
        exist _ (generated_item_def d pv a_True (a_mem E n) :: gs) _
    | exist _ member_kind_mod Hk =>
        let (gs, Hgs) := kinds_items_gen_impl p E its _ in
        exist _ (generated_item_alias d pv (me_mem E n) :: gs) _
    | exist _ member_kind_dm Hk =>
        let (gs, Hgs) := kinds_items_gen_impl p E its _ in
        exist _ (generated_item_def_mod d pv a_True (a_mem E n) (me_mem E n) :: gs) _ }.

  Solve All Obligations with kd_obl_auto.

  (** A body read through the entries its opens generate. *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations kinds_body_xp_impl p Φ (H : kinds_body_xp_order Θ Ξ p Φ) : { Φx | kinds_body_xp Θ Ξ p Φ Φx } by struct H :=
  | p, gm_nil, H => exist _ gm_nil _
  | p, gm_ext Φ y E, H =>
      let (Φx, HΦx) := kinds_body_xp_impl p Φ _ in
      exist _ (gm_ext Φx y E) _
  | p, gm_open Φ E its, H =>
      let (Φx, HΦx) := kinds_body_xp_impl p Φ _ in
      let (p1, Hp1) := kinds_env_impl p Φx _ in
      let (gs, Hgs) := kinds_items_gen_impl p1 E its _ in
      exist _ (gens_append Φx 0 gs) _.

  Solve All Obligations with kd_obl_auto.
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
