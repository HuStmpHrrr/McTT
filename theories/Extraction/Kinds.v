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
    generate ([kbody]), which the kinds of the members its items name
    determine ([kgens]).  Both evaluators compute them with [kbody_impl], by
    recursion on a termination order. *)

(** The orders mirror the kinds relations, one for each; a chain of a
    global alias recurses into the alias's unit, and a body's member into
    the environment the kinds read off the body before it.  An item naming
    a member of a target is ordered by that member's kind, which decides
    whether the chain goes on into it. *)

Inductive dkind_order (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> Prop :=
(** The path names a definition ([dk_global_here_def]): no recursion *)
| dko_global_here_def :
  `( gc_resolve Θ Ξ pq = Some (ge_def b pv A B) ->
     dkind_order Θ Ξ (dm_global pq args) nil )
(** The path names a body module or a frame ([dk_global_here_mod]): no
    recursion *)
| dko_global_here_mod :
  `( (exists T oD, gc_module Θ Ξ pq = Some (mr_body T oD)) \/ (exists TΦ, gc_frame Ξ pq = Some TΦ) ->
     dkind_order Θ Ξ (dm_global pq args) nil )
(** The member [y] is a definition with a module part stored in place
    ([dk_global_here_dm]): no recursion *)
| dko_global_here_dm :
  `( dm_path Θ Ξ (qname_app pq (y :: nil)) ->
     gc_loc Θ Ξ (qname_app pq (y :: nil)) = Some TΦ ->
     dkind_order Θ Ξ (dm_global pq args) (y :: nil) )
(** The member [y] is an alias read past ([dk_global_alias]): the order of
    the chain in the alias's unit *)
| dko_global_alias :
  `( gc_module Θ Ξ (qname_app pq (y :: nil)) = Some (mr_alias U) ->
     ch <> nil \/ ~ dm_path Θ Ξ (qname_app pq (y :: nil)) ->
     ukind_order Θ Ξ nil U ch ->
     dkind_order Θ Ξ (dm_global pq args) (y :: ch) )
(** The member [y] is a definition with a module part stored as an alias
    ([dk_global_alias_dm]): the order of the empty chain in the alias's
    unit *)
| dko_global_alias_dm :
  `( gc_module Θ Ξ (qname_app pq (y :: nil)) = Some (mr_alias U) ->
     dm_path Θ Ξ (qname_app pq (y :: nil)) ->
     ukind_order Θ Ξ nil U nil ->
     dkind_order Θ Ξ (dm_global pq args) (y :: nil) )
(** The member [y] is located in place ([dk_global_step]): the order of the
    rest of the chain at the path of [y] *)
| dko_global_step :
  `( (exists TΦ, gc_loc Θ Ξ (qname_app pq (y :: nil)) = Some TΦ) \/
     (exists b pv A B, gc_resolve Θ Ξ (qname_app pq (y :: nil)) = Some (ge_def b pv A B)) ->
     ch <> nil \/ ~ dm_path Θ Ξ (qname_app pq (y :: nil)) ->
     dkind_order Θ Ξ (dm_global (qname_app pq (y :: nil)) args) ch ->
     dkind_order Θ Ξ (dm_global pq args) (y :: ch) )
(** A closure ([dk_local]): the order of its unit *)
| dko_local :
  `( ukind_order Θ Ξ p (gu_mk Δ D) ch ->
     dkind_order Θ Ξ (dm_local Δ D p) ch )
(** A submodule closure ([dk_member], [dk_member_dm]): the order of the
    longer chain *)
| dko_member :
  `( dkind_order Θ Ξ h (ch0 ++ ch) ->
     dkind_order Θ Ξ (dm_member h ch0) ch )

with ukind_order (Θ : gdeps) (Ξ : gstack) : env -> gunit -> list string -> Prop :=
(** A body at the empty chain ([uk_self]): no recursion *)
| uko_self :
  `( ukind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) nil )
(** A definition of the body ([uk_def]): no recursion *)
| uko_def :
  `( gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A B)) ->
     ukind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) (x :: nil) )
(** A submodule of the body ([uk_mod]): the order of the entries before it,
    and of the rest of the chain in its unit, in each environment they
    make *)
| uko_mod :
  `( gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
     kenv_order Θ Ξ (kpad (List.length Δ) p) Φ' ->
     (forall p1, kenv Θ Ξ (kpad (List.length Δ) p) Φ' p1 -> ukind_order Θ Ξ p1 Uy ch) ->
     ukind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) (y :: ch) )
(** A definition with a module part of the body, at the end of the chain
    ([uk_dm_here]): the order of the entries before it, and of the empty
    chain in its module part, in each environment they make *)
| uko_dm_here :
  `( gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_def_mod pv A M Uy)) ->
     kenv_order Θ Ξ (kpad (List.length Δ) p) Φ' ->
     (forall p1, kenv Θ Ξ (kpad (List.length Δ) p) Φ' p1 -> ukind_order Θ Ξ p1 Uy nil) ->
     ukind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) (y :: nil) )
(** A definition with a module part of the body, the chain going on
    ([uk_dm_step]): the order of the entries before it, and of the rest of
    the chain in its module part, in each environment they make *)
| uko_dm_step :
  `( gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_def_mod pv A M Uy)) ->
     ch <> nil ->
     kenv_order Θ Ξ (kpad (List.length Δ) p) Φ' ->
     (forall p1, kenv Θ Ξ (kpad (List.length Δ) p) Φ' p1 -> ukind_order Θ Ξ p1 Uy ch) ->
     ukind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) (y :: ch) )
(** An item naming a member of the target ([uk_item_def], [uk_item_mod],
    [uk_item_dm]): the order of the entries before the open, of the
    member's kind, and of the chain in the member when the member is a
    module or has a module part *)
| uko_item_some :
  `( gm_item_upto Φ x = Some (Φ0, E, its1, (Some n, d, pv)) ->
     kenv_order Θ Ξ (kpad (List.length Δ) p) Φ0 ->
     (forall p0, kenv Θ Ξ (kpad (List.length Δ) p) Φ0 p0 ->
        skind_order Θ Ξ p0 E (n :: nil) /\
        ((skind Θ Ξ p0 E (n :: nil) mk_term /\ ch = nil) \/
         (skind Θ Ξ p0 E (n :: nil) mk_mod /\ skind_order Θ Ξ p0 E (n :: ch)) \/
         (skind Θ Ξ p0 E (n :: nil) mk_dm /\ skind_order Θ Ξ p0 E (n :: ch)))) ->
     ukind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) (x :: ch) )
(** An item naming the target itself ([uk_item_self]): the order of the
    entries before the open, and of the chain in the target *)
| uko_item_none :
  `( gm_item_upto Φ x = Some (Φ0, E, its1, (None, d, pv)) ->
     kenv_order Θ Ξ (kpad (List.length Δ) p) Φ0 ->
     (forall p0, kenv Θ Ξ (kpad (List.length Δ) p) Φ0 p0 -> skind_order Θ Ξ p0 E ch) ->
     ukind_order Θ Ξ p (gu_mk Δ (md_body sm Φ)) (x :: ch) )
(** An alias unit ([uk_alias]): the order of the chain in its target *)
| uko_alias :
  `( skind_order Θ Ξ (kpad (List.length Δ) p) E ch ->
     ukind_order Θ Ξ p (gu_mk Δ (md_alias E)) ch )

with skind_order (Θ : gdeps) (Ξ : gstack) : env -> modexp -> list string -> Prop :=
(** A unit ([sk_unit]): the order of the chain in its global module *)
| sko_unit :
  `( dkind_order Θ Ξ (dm_global (q_abs fp nil) nil) ch ->
     skind_order Θ Ξ p (me_unit fp) ch )
(** A module slot ([sk_var]): the order of the chain in its value *)
| sko_var :
  `( dkind_order Θ Ξ (env_mod p x) ch ->
     skind_order Θ Ξ p (me_var x) ch )
(** A literal unit ([sk_lit]): the order of the chain in the unit *)
| sko_lit :
  `( ukind_order Θ Ξ p U ch ->
     skind_order Θ Ξ p (me_lit U) ch )
(** A selection ([sk_mem], [sk_mem_dm]): the order of the longer chain *)
| sko_mem :
  `( skind_order Θ Ξ p E (y :: ch) ->
     skind_order Θ Ξ p (me_mem E y) ch )
(** An application ([sk_app]): the order of the chain in the module
    applied *)
| sko_app :
  `( skind_order Θ Ξ p E ch ->
     skind_order Θ Ξ p (me_app E N) ch )

with kenv_order (Θ : gdeps) (Ξ : gstack) : env -> gmod -> Prop :=
(** The empty body ([ke_nil]) *)
| keo_nil :
  `( kenv_order Θ Ξ p gm_nil )
(** An entry ([ke_ext]): the order of the body before it *)
| keo_ext :
  `( kenv_order Θ Ξ p Φ ->
     kenv_order Θ Ξ p (gm_ext Φ y E) )
(** An open ([ke_open]): the order of the body before it, and of its items
    in each environment that body makes *)
| keo_open :
  `( kenv_order Θ Ξ p Φ ->
     (forall p1, kenv Θ Ξ p Φ p1 -> kgens_order Θ Ξ p1 E its) ->
     kenv_order Θ Ξ p (gm_open Φ E its) )

with kgens_order (Θ : gdeps) (Ξ : gstack) : env -> modexp -> list iitem -> Prop :=
(** No items ([kg_nil]) *)
| kgo_nil :
  `( kgens_order Θ Ξ p E nil )
(** An item naming the target itself ([kg_self]): the order of the other
    items *)
| kgo_self :
  `( kgens_order Θ Ξ p E its ->
     kgens_order Θ Ξ p E ((None, d, pv) :: its) )
(** An item naming a member ([kg_def], [kg_mod], [kg_dm]): the order of
    the member's kind, and of the other items *)
| kgo_name :
  `( skind_order Θ Ξ p E (n :: nil) ->
     kgens_order Θ Ξ p E its ->
     kgens_order Θ Ξ p E ((Some n, d, pv) :: its) ).

(** The order of reading a body through the entries its opens generate. *)
Inductive kbody_order (Θ : gdeps) (Ξ : gstack) : env -> gmod -> Prop :=
(** The empty body ([kb_nil]) *)
| kbo_nil :
  `( kbody_order Θ Ξ p gm_nil )
(** An entry ([kb_ext]): the order of the body before it *)
| kbo_ext :
  `( kbody_order Θ Ξ p Φ ->
     kbody_order Θ Ξ p (gm_ext Φ y E) )
(** An open ([kb_open]): the order of the body before it, and, for each
    expansion of that body, of the environment it makes and of the items in
    each such environment *)
| kbo_open :
  `( kbody_order Θ Ξ p Φ ->
     (forall Φx, kbody Θ Ξ p Φ Φx -> kenv_order Θ Ξ p Φx /\
        forall p1, kenv Θ Ξ p Φx p1 -> kgens_order Θ Ξ p1 E its) ->
     kbody_order Θ Ξ p (gm_open Φ E its) ).

#[local]
Hint Constructors dkind_order ukind_order skind_order kenv_order kgens_order kbody_order : mctt.

Lemma kind_order_sound : forall Θ Ξ,
    (forall h ch k, dkind Θ Ξ h ch k -> dkind_order Θ Ξ h ch) /\
    (forall p U ch k, ukind Θ Ξ p U ch k -> ukind_order Θ Ξ p U ch) /\
    (forall p E ch k, skind Θ Ξ p E ch k -> skind_order Θ Ξ p E ch) /\
    (forall p Φ p1, kenv Θ Ξ p Φ p1 -> kenv_order Θ Ξ p Φ) /\
    (forall p Φ Φx, kbody Θ Ξ p Φ Φx -> kbody_order Θ Ξ p Φ) /\
    (forall p E its gs, kgens Θ Ξ p E its gs -> kgens_order Θ Ξ p E its).
Proof.
  intros Θ Ξ; pose proof (@functional_kind Θ Ξ) as (_ & _ & _ & Fk & Fb & _).
  apply kind_mut_ind; intros; try solve [ econstructor; eauto ].
  all: lazymatch goal with
    | _ : gm_item_upto _ _ = Some (_, _, _, (Some _, _, _)) |- ukind_order _ _ _ _ _ => eapply uko_item_some
    | _ : gm_item_upto _ _ = Some (_, _, _, (None, _, _)) |- ukind_order _ _ _ _ _ =>
        eapply uko_item_none
    | _ : gm_prefix_upto _ _ = Some (gm_ext _ _ (ge_mod _ _)) |- ukind_order _ _ _ _ _ => eapply uko_mod
    | _ : gm_prefix_upto _ _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)), _ : _ <> nil |- ukind_order _ _ _ _ _ =>
        eapply uko_dm_step
    | _ : gm_prefix_upto _ _ = Some (gm_ext _ _ (ge_def_mod _ _ _ _)) |- ukind_order _ _ _ _ _ => eapply uko_dm_here
    | |- kbody_order _ _ _ (gm_open _ _ _) => eapply kbo_open
    | _ : gc_module _ _ _ = Some (mr_alias _), _ : dm_path _ _ _ |- dkind_order _ _ _ (_ :: nil) => eapply dko_global_alias_dm
    | |- _ => econstructor
    end; eauto; intros;
    repeat match goal with
      | H1 : kenv _ _ ?p ?Φ ?r1, H2 : kenv _ _ ?p ?Φ ?r2 |- _ =>
          assert_fails (constr_eq r1 r2); rewrite <- (Fk _ _ _ H1 _ H2) in *; clear H2
      | H1 : kbody _ _ ?p ?Φ ?r1, H2 : kbody _ _ ?p ?Φ ?r2 |- _ =>
          assert_fails (constr_eq r1 r2); rewrite <- (Fb _ _ _ H1 _ H2) in *; clear H2
      end;
    first [ split; [ eauto | first [ left; split; [ eassumption | reflexivity ]
                                   | solve [ right; left; split; eauto ] | solve [ right; right; split; eauto ] ] ]
          | split; [ eauto | intros;
              repeat match goal with
                | H1 : kenv _ _ ?p ?Φ ?r1, H2 : kenv _ _ ?p ?Φ ?r2 |- _ =>
                    assert_fails (constr_eq r1 r2); rewrite <- (Fk _ _ _ H1 _ H2) in *; clear H2
                end; eauto ]
          | solve [ rewrite List.app_nil_r; eauto ]
          | solve [ match goal with Hn : ?a <> ?a |- _ => exfalso; exact (Hn eq_refl) end ]
          | eauto ].
Qed.

Lemma kgens_order_sound : forall Θ Ξ p E its gs, kgens Θ Ξ p E its gs -> kgens_order Θ Ξ p E its.
Proof. intros Θ Ξ; pose proof (kind_order_sound Θ Ξ); destruct_all; eauto. Qed.

Lemma kbody_order_sound : forall Θ Ξ p Φ Φx, kbody Θ Ξ p Φ Φx -> kbody_order Θ Ξ p Φ.
Proof. intros Θ Ξ; pose proof (kind_order_sound Θ Ξ); destruct_all; eauto. Qed.

#[export]
Hint Resolve kgens_order_sound kbody_order_sound : mctt.

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
    | H : kbody_order _ _ _ _ |- _ => progressive_invert H
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
      | H : forall p0, kenv _ _ ?qe ?Φ p0 -> _ /\ _, Hk : kenv _ _ ?qe ?Φ ?p0 |- _ =>
          let Ha := fresh "Ha" in let Hb := fresh "Hb" in destruct (H _ Hk) as [Ha Hb]; clear H
      | H : forall Φx, kbody _ _ ?qe ?Φ Φx -> _ /\ _, Hk : kbody _ _ ?qe ?Φ ?Φx |- _ =>
          let Ha := fresh "Ha" in let Hb := fresh "Hb" in destruct (H _ Hk) as [Ha Hb]; clear H
      | H : (skind _ _ ?p0 ?E ?ch mk_term /\ _) \/ (skind _ _ ?p0 ?E ?ch mk_mod /\ _) \/ (skind _ _ ?p0 ?E ?ch mk_dm /\ _),
        Hk : skind _ _ ?p0 ?E ?ch mk_term |- _ =>
          destruct H as [[_ ?] | [[Hk' _] | [Hk' _]]];
          [ subst
          | exfalso; pose proof (proj1 (proj2 (proj2 (@functional_kind Θ Ξ))) _ _ _ _ Hk _ Hk'); discriminate
          | exfalso; pose proof (proj1 (proj2 (proj2 (@functional_kind Θ Ξ))) _ _ _ _ Hk _ Hk'); discriminate ]
      | H : (skind _ _ ?p0 ?E ?ch mk_term /\ _) \/ (skind _ _ ?p0 ?E ?ch mk_mod /\ _) \/ (skind _ _ ?p0 ?E ?ch mk_dm /\ _),
        Hk : skind _ _ ?p0 ?E ?ch mk_mod |- _ =>
          destruct H as [[Hk' _] | [[_ ?] | [Hk' _]]];
          [ exfalso; pose proof (proj1 (proj2 (proj2 (@functional_kind Θ Ξ))) _ _ _ _ Hk _ Hk'); discriminate
          |
          | exfalso; pose proof (proj1 (proj2 (proj2 (@functional_kind Θ Ξ))) _ _ _ _ Hk _ Hk'); discriminate ]
      | H : (skind _ _ ?p0 ?E ?ch mk_term /\ _) \/ (skind _ _ ?p0 ?E ?ch mk_mod /\ _) \/ (skind _ _ ?p0 ?E ?ch mk_dm /\ _),
        Hk : skind _ _ ?p0 ?E ?ch mk_dm |- _ =>
          destruct H as [[Hk' _] | [[Hk' _] | [_ ?]]];
          [ exfalso; pose proof (proj1 (proj2 (proj2 (@functional_kind Θ Ξ))) _ _ _ _ Hk _ Hk'); discriminate
          | exfalso; pose proof (proj1 (proj2 (proj2 (@functional_kind Θ Ξ))) _ _ _ _ Hk _ Hk'); discriminate
          | ]
      end.

  #[local]
  Ltac kd_split :=
    match goal with
    | H : dkind_order _ _ _ _ |- _ => dependent destruction H
    | H : ukind_order _ _ _ _ _ |- _ => dependent destruction H
    | H : skind_order _ _ _ _ _ |- _ => dependent destruction H
    | H : kenv_order _ _ _ _ |- _ => dependent destruction H
    | H : kgens_order _ _ _ _ _ |- _ => dependent destruction H
    | H : kbody_order _ _ _ _ |- _ => dependent destruction H
    end.

  #[local]
  Ltac kd_finish :=
    kd_glob;
    try solve [ intuition discriminate ];
    try solve [ eapply dk_global_step;
                [ first [ left; eexists; eassumption | right; do 4 eexists; eassumption ]
                | first [ left; discriminate | right; assumption ] | eassumption ] ];
    (** a selection away from the empty chain, or of no member with a term
        part and a module part *)
    try solve [ first [ eapply dk_member | eapply sk_mem ]; [ eassumption | first [ left; discriminate | right; discriminate ] ] ];
    try solve [ first [ apply dk_member_dm | apply sk_mem_dm ]; rewrite ?List.app_nil_r in *; eassumption ];
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
    | |- kbody_order _ _ _ _ => kd_obl
    | |- _ => abstract kd_obl
    end.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations dkind_impl h ch (H : dkind_order Θ Ξ h ch) : { k | dkind Θ Ξ h ch k } by struct H :=
  | dm_global pq args, nil, H with inspect (gc_frame Ξ pq) := {
    | exist _ (Some TΦ) F => exist _ mk_mod _
    | exist _ None F with inspect (gc_module Θ Ξ pq) := {
      | exist _ (Some (mr_body T oD)) E => exist _ mk_mod _
      | exist _ _ E with inspect (gc_resolve Θ Ξ pq) := {
        | exist _ (Some (ge_def b pv A B)) E2 => exist _ mk_term _
        | exist _ _ E2 => False_rect _ _ } } }
  | dm_global pq args, y :: ch, H with dm_path_dec Θ Ξ (qname_app pq (y :: nil)), ch := {
    | left Hd, nil with inspect (gc_module Θ Ξ (qname_app pq (y :: nil))) := {
      (** a definition with a module part stored as an alias: [dm_of] its
          alias's kind *)
      | exist _ (Some (mr_alias U)) E =>
          let (k, Hk) := ukind_impl nil U nil _ in
          exist _ (dm_of k) _
      | exist _ _ E => exist _ mk_dm _ }
    | _, ch' with inspect (gc_module Θ Ξ (qname_app pq (y :: nil))) := {
      | exist _ (Some (mr_alias U)) E =>
          let (k, Hk) := ukind_impl nil U ch' _ in
          exist _ k _
      | exist _ _ E =>
          let (k, Hk) := dkind_impl (dm_global (qname_app pq (y :: nil)) args) ch' _ in
          exist _ k _ } }
  | dm_local Δ D p, ch, H =>
      let (k, Hk) := ukind_impl p (gu_mk Δ D) ch _ in
      exist _ k _
  | dm_member h ch0, ch, H with dkind_impl h (ch0 ++ ch) _ := {
    (** at the empty chain, a member with a term part and a module part is
        selected as a module *)
    | exist _ mk_dm Hk with ch := {
      | nil => exist _ mk_mod _
      | _ :: _ => exist _ mk_dm _ }
    | exist _ k Hk => exist _ k _ }

  with ukind_impl p U ch (H : ukind_order Θ Ξ p U ch) : { k | ukind Θ Ξ p U ch k } by struct H :=
  | p, gu_mk Δ (md_body sm Φ), nil, H => exist _ mk_mod _
  | p, gu_mk Δ (md_body sm Φ), x :: ch, H with inspect (gm_item_upto Φ x) := {
    | exist _ (Some (Φ0, E, its1, (Some n, d, pv))) Ei with kenv_impl (kpad (List.length Δ) p) Φ0 _ := {
      | exist _ p0 Hp0 with skind_impl p0 E (n :: nil) _ := {
        | exist _ mk_term Hk0 => exist _ mk_term _
        | exist _ mk_mod Hk0 =>
            let (k, Hk) := skind_impl p0 E (n :: ch) _ in
            exist _ k _
        | exist _ mk_dm Hk0 =>
            let (k, Hk) := skind_impl p0 E (n :: ch) _ in
            exist _ k _ } }
    | exist _ (Some (Φ0, E, its1, (None, d, pv))) Ei =>
        let (p0, Hp0) := kenv_impl (kpad (List.length Δ) p) Φ0 _ in
        let (k, Hk) := skind_impl p0 E ch _ in
        exist _ k _
    | exist _ None Ei with inspect (gm_prefix_upto Φ x) := {
      | exist _ (Some (gm_ext Φ' _ (ge_def b pv A B))) P => exist _ mk_term _
      | exist _ (Some (gm_ext Φ' _ (ge_mod pm Uy))) P =>
          let (p1, Hp1) := kenv_impl (kpad (List.length Δ) p) Φ' _ in
          let (k, Hk) := ukind_impl p1 Uy ch _ in
          exist _ k _
      | exist _ (Some (gm_ext Φ' _ (ge_def_mod pv A M Uy))) P with ch := {
        (** itself: [dm_of] its module part's kind *)
        | nil =>
            let (p1, Hp1) := kenv_impl (kpad (List.length Δ) p) Φ' _ in
            let (k, Hk) := ukind_impl p1 Uy nil _ in
            exist _ (dm_of k) _
        | c :: ch' =>
            let (p1, Hp1) := kenv_impl (kpad (List.length Δ) p) Φ' _ in
            let (k, Hk) := ukind_impl p1 Uy (c :: ch') _ in
            exist _ k _ }
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
  | p, me_mem E y, ch, H with skind_impl p E (y :: ch) _ := {
    (** at the empty chain, a member with a term part and a module part is
        selected as a module *)
    | exist _ mk_dm Hk with ch := {
      | nil => exist _ mk_mod _
      | _ :: _ => exist _ mk_dm _ }
    | exist _ k Hk => exist _ k _ }
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
        exist _ (ig_alias d pv (me_mem E n) :: gs) _
    | exist _ mk_dm Hk =>
        let (gs, Hgs) := kgens_impl p E its _ in
        exist _ (ig_def_mod d pv a_True (a_mem E n) (me_mem E n) :: gs) _ }.

  Solve All Obligations with kd_obl_auto.

  (** A body read through the entries its opens generate. *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations kbody_impl p Φ (H : kbody_order Θ Ξ p Φ) : { Φx | kbody Θ Ξ p Φ Φx } by struct H :=
  | p, gm_nil, H => exist _ gm_nil _
  | p, gm_ext Φ y E, H =>
      let (Φx, HΦx) := kbody_impl p Φ _ in
      exist _ (gm_ext Φx y E) _
  | p, gm_open Φ E its, H =>
      let (Φx, HΦx) := kbody_impl p Φ _ in
      let (p1, Hp1) := kenv_impl p Φx _ in
      let (gs, Hgs) := kgens_impl p1 E its _ in
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
