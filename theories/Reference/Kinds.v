From Equations Require Import Equations.
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Extraction Require Import Lookup Kinds.
Import Domain_Notations.

Generalizable All Variables.

(** * The Reference Kinds of Members

    The kinds of [Extraction.Kinds] computed with the Core lookups of [Θ ⍮ Ξ],
    for the reference evaluator ([Reference.Evaluation]), which is stated at
    any global context.  It is not extracted; [Extraction.Kinds] computes the
    same kinds through the fast context. *)

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
    try solve [ eapply dkind_global_step;
                [ first [ left; eexists; eassumption | right; do 4 eexists; eassumption ]
                | first [ left; discriminate | right; assumption ] | eassumption ] ];
    (** a selection away from the empty chain, or of no member with a term
        part and a module part *)
    try solve [ first [ eapply dkind_member | eapply skind_mem ]; [ eassumption | first [ left; discriminate | right; discriminate ] ] ];
    try solve [ first [ apply dkind_member_dm | apply skind_mem_dm ]; rewrite ?List.app_nil_r in *; eassumption ];
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

  (** The kind of a selection from a module value *)
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
