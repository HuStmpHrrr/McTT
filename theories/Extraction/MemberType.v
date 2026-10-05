(** * Computing Member Types

    [member_type_impl] decides [member_type] by recursion on a termination
    order ([mt_order]), which mirrors its recursion: a slot is read in the
    context after it, so the context gets shorter as the syntax grows, and a
    unit of the global context is read in the empty context, where the order
    asks for the unit's own order.  Every unit of a well-formed global
    context has one ([gctx_units_ordered]), since a unit can only name units
    filed below it, so every module expression has an order
    ([mt_order_total]). *)

From Stdlib Require Import Lia List PeanoNat String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members Imports.
From Mctt.Core.Syntactic.System Require Import MemberLemmas GlobalPresup MemberWf.
From Mctt.Core.Completeness Require Import MemberSem.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Sizes

    The size of a module expression or a unit counts its nested units, and
    the size of a context counts the units of its slots: the terms of either
    are never looked at.  A submodule entry counts one more than its unit,
    so a submodule read under its self slot, which holds the body before
    it, is smaller than its body. *)

Fixpoint msize (H : modexp) : nat :=
  match H with
  | me_unit _ | me_var _ => 1
  | me_mem H _ | me_app H _ => S (msize H)
  | me_lit U => S (usize U)
  end
with usize (U : gunit) : nat :=
  match U with
  | gu_mk Δ D =>
      S ((fix cs (Δ : list centry) : nat :=
            match Δ with
            | nil => 0
            | cons (ce_mod U) Δ' => usize U + cs Δ'
            | cons _ Δ' => cs Δ'
            end) Δ + dsize D)
  end
with dsize (D : moddef) : nat :=
  match D with
  | md_body Φ => gsize Φ
  | md_alias E => msize E
  end
with gsize (Φ : gmod) : nat :=
  match Φ with
  | gm_nil => 0
  | gm_ext Φ _ (ge_mod _ U) => S (gsize Φ + usize U)
  | gm_ext Φ _ _ => gsize Φ
  | gm_open Φ H _ _ => S (gsize Φ + msize H)
  end.

Fixpoint csize (Γ : ctx) : nat :=
  match Γ with
  | nil => 0
  | ce_mod U :: Γ' => usize U + csize Γ'
  | _ :: Γ' => csize Γ'
  end.

Lemma usize_mk : forall Δ D, usize (gu_mk Δ D) = S (csize Δ + dsize D).
Proof.
  intros Δ D; cbn [usize]; f_equal; f_equal;
    try (induction Δ as [| [A | A M | U] Δ IH]; cbn; congruence).
Qed.

Lemma csize_app : forall Ψ Γ, csize (Ψ ++ Γ) = csize Ψ + csize Γ.
Proof. induction Ψ as [| [A | A M | U] Ψ IH]; intros; cbn; rewrite ?IH; lia. Qed.

Lemma gsize_prefix : forall Φ x Φx, gm_prefix_upto Φ x = Some Φx -> gsize Φx <= gsize Φ.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H0 oz its]; intros * H; cbn in H; try discriminate.
  - destruct (String.eqb x y); [ injection H as <-; lia |].
    specialize (IH _ _ H); destruct E as [? ? ? | U]; cbn; lia.
  - specialize (IH _ _ H); cbn; lia.
Qed.

Lemma gm_prefix_upto_name : forall Φ x Φ' y E, gm_prefix_upto Φ x = Some (gm_ext Φ' y E) -> y = x.
Proof.
  induction Φ as [| Φ IH z E0 | Φ IH H0 oz its]; intros * H; cbn in H; try discriminate; eauto.
  destruct (String.eqb_spec x z) as [-> |]; [ congruence | eauto ].
Qed.

(** ** Slots, Read after Themselves *)

Fixpoint ctx_find_slot (Γ : ctx) (x : nat) : option (gunit * ctx) :=
  match Γ with
  | nil => None
  | e :: Γ' =>
      match x with
      | 0 => match e with ce_mod U => Some (U, Γ') | _ => None end
      | S y => ctx_find_slot Γ' y
      end
  end.

Fixpoint uwk_n (n : nat) (U : gunit) : gunit :=
  match n with
  | 0 => U
  | S n => gunit_wk (uwk_n n U) wk_shift
  end.

Fixpoint rwk_n (n : nat) (R : mres) : mres :=
  match n with
  | 0 => R
  | S n => mres_wk (rwk_n n R) wk_shift
  end.

Arguments uwk_n : simpl never.
Arguments rwk_n : simpl never.

Lemma ctx_find_slot_mod : forall Γ x U0 Γ', ctx_find_slot Γ x = Some (U0, Γ') ->
    ctx_find_mod Γ x = Some (uwk_n (S x) U0).
Proof.
  induction Γ as [| e Γ IH]; intros [| y] * H; cbn in H |- *; try discriminate.
  - destruct e; try discriminate; injection H as -> ->; reflexivity.
  - rewrite (IH _ _ _ H); reflexivity.
Qed.

Lemma ctx_find_slot_none : forall Γ x, ctx_find_slot Γ x = None -> ctx_find_mod Γ x = None.
Proof.
  induction Γ as [| e Γ IH]; intros [| y] H; cbn in H |- *; try reflexivity.
  - destruct e; [ reflexivity | reflexivity | discriminate ].
  - rewrite (IH _ H); reflexivity.
Qed.

Lemma ctx_find_slot_split : forall Γ x U0 Γ', ctx_find_slot Γ x = Some (U0, Γ') ->
    exists Ψ, Γ = Ψ ++ ce_mod U0 :: Γ'.
Proof.
  induction Γ as [| e Γ IH]; intros [| y] * H; cbn in H; try discriminate.
  - destruct e; try discriminate; injection H as -> ->; exists nil; reflexivity.
  - destruct (IH _ _ _ H) as [Ψ ->]; exists (e :: Ψ); reflexivity.
Qed.

Section Slots.
  Variables (Θ : gctx).
  Hypothesis Hc : gctx_closed Θ.

  Lemma ctx_find_slot_wk : forall Γ x U0 Γ' ch R0, ctx_find_slot Γ x = Some (U0, Γ') ->
      unit_member_type Θ Γ' U0 ch R0 ->
      unit_member_type Θ Γ (uwk_n (S x) U0) ch (rwk_n (S x) R0).
  Proof.
    induction Γ as [| e Γ IH]; intros [| y] * H Hu; cbn in H; try discriminate.
    - destruct e; try discriminate; injection H as -> ->.
      exact (proj2 (member_type_wk _ Hc) _ _ _ _ Hu _ _ (fun x U Hl => mod_there _ _ _ _ Hl)).
    - specialize (IH _ _ _ _ _ H Hu).
      exact (proj2 (member_type_wk _ Hc) _ _ _ _ IH _ _ (fun x U Hl => mod_there _ _ _ _ Hl)).
  Qed.

  Lemma ctx_find_slot_strengthen : forall Γ x U0 Γ' ch R, ctx_find_slot Γ x = Some (U0, Γ') ->
      unit_member_type Θ Γ (uwk_n (S x) U0) ch R ->
      exists R0, unit_member_type Θ Γ' U0 ch R0 /\ R = rwk_n (S x) R0.
  Proof.
    induction Γ as [| e Γ IH]; intros [| y] * H Hu; cbn in H; try discriminate.
    - destruct e; try discriminate; injection H as -> ->.
      exact (proj2 (member_type_strengthen _ Hc) _ _ _ _ Hu _ _ _ eq_refl (wk_mod_inv_shift _ _)).
    - destruct (proj2 (member_type_strengthen _ Hc) _ _ _ _ Hu _ _ _ eq_refl (wk_mod_inv_shift _ _))
        as (R1 & HR1 & ->).
      destruct (IH _ _ _ _ _ H HR1) as (R0 & HR0 & ->); eauto.
  Qed.
End Slots.

(** ** The Termination Order *)

Inductive mt_order (Θ : gctx) : ctx -> modexp -> list string -> Prop :=
| mto_unit : forall Γ fp ch,
    (forall U, gc_unit Θ fp = Some U -> umt_order Θ nil U ch) ->
    mt_order Θ Γ (me_unit fp) ch
| mto_var : forall Γ x ch,
    (forall U0 Γ', ctx_find_slot Γ x = Some (U0, Γ') -> umt_order Θ Γ' U0 ch) ->
    mt_order Θ Γ (me_var x) ch
| mto_lit : forall Γ U ch,
    umt_order Θ Γ U ch ->
    mt_order Θ Γ (me_lit U) ch
| mto_mem : forall Γ H y ch,
    mt_order Θ Γ H (y :: ch) ->
    mt_order Θ Γ (me_mem H y) ch
| mto_app : forall Γ H N ch,
    mt_order Θ Γ H ch ->
    mt_order Θ Γ (me_app H N) ch
with umt_order (Θ : gctx) : ctx -> gunit -> list string -> Prop :=
| umto_body_nil : forall Γ Δ Φ,
    umt_order Θ Γ (gu_body Δ Φ) nil
| umto_body_cons : forall Γ Δ Φ y ch,
    (forall Φ' pm Uy, gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
       umt_order Θ (self_ent Φ' :: Δ ++ Γ) Uy ch) ->
    umt_order Θ Γ (gu_body Δ Φ) (y :: ch)
| umto_alias : forall Γ Δ E ch,
    mt_order Θ (Δ ++ Γ) E ch ->
    umt_order Θ Γ (gu_mk Δ (md_alias E)) ch.

(** ** The Decision Procedure

    The lookups are made by functions, so that the procedure matches on
    their results only. *)

(** Whether a member type may stand at a chain: a definition is not the
    module a chain names. *)
Definition mt_side (R : mres) (ch : list string) : bool :=
  match R, ch with
  | mr_term _, nil => false
  | _, _ => true
  end.

Lemma mt_side_true : forall R ch, mt_side R ch = true -> mres_kind R = mk_term -> ch <> nil.
Proof. intros [A | T] [| y ch] H Hk; cbn in *; congruence. Qed.

Lemma mt_side_false : forall R ch, mt_side R ch = false -> mres_kind R = mk_term /\ ch = nil.
Proof. intros [A | T] [| y ch] H; cbn in *; auto; discriminate. Qed.

Inductive blookup : Set :=
| bl_def : gmod -> typ -> blookup
| bl_mod : gmod -> bool -> gunit -> blookup
| bl_none : blookup.

Definition body_lookup (Φ : gmod) (y : string) : blookup :=
  match gm_prefix_upto Φ y with
  | Some (gm_ext Φ' _ (ge_def _ A _)) => bl_def Φ' A
  | Some (gm_ext Φ' _ (ge_mod pm Uy)) => bl_mod Φ' pm Uy
  | _ => bl_none
  end.

Lemma body_lookup_def : forall Φ y Φ' A, body_lookup Φ y = bl_def Φ' A ->
    exists pv B, gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_def pv A B)).
Proof.
  intros * H; unfold body_lookup in H.
  destruct (gm_prefix_upto Φ y) as [[| Φ0 z [pv A0 B0 | pm0 U] | Φ0 H0 oz its] |] eqn:E; try discriminate.
  injection H as -> ->; pose proof (gm_prefix_upto_name _ _ _ _ _ E) as ->; eauto.
Qed.

Lemma body_lookup_mod : forall Φ y Φ' pm Uy, body_lookup Φ y = bl_mod Φ' pm Uy ->
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)).
Proof.
  intros * H; unfold body_lookup in H.
  destruct (gm_prefix_upto Φ y) as [[| Φ0 z [pv A0 B0 | pm0 U] | Φ0 H0 oz its] |] eqn:E; try discriminate.
  injection H as -> -> ->; pose proof (gm_prefix_upto_name _ _ _ _ _ E) as ->; reflexivity.
Qed.

Lemma body_lookup_none_def : forall Φ y Φ' pv A B, body_lookup Φ y = bl_none ->
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_def pv A B)) -> False.
Proof. intros * H E; unfold body_lookup in H; rewrite E in H; discriminate. Qed.

Lemma body_lookup_none_mod : forall Φ y Φ' pm Uy, body_lookup Φ y = bl_none ->
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) -> False.
Proof. intros * H E; unfold body_lookup in H; rewrite E in H; discriminate. Qed.

#[local] Opaque mt_side.

Section MemberTypeImpl.
  Variables (Θ : gctx).
  Hypothesis Hc : gctx_closed Θ.

  Definition inspect {A} (a : A) : { b | a = b } := exist _ a eq_refl.

  #[local]
  Ltac lookups :=
    repeat match goal with
      | H : body_lookup _ _ = bl_def _ _ |- _ =>
          destruct (body_lookup_def _ _ _ _ H) as (? & ? & ?); clear H
      | H : body_lookup _ _ = bl_mod _ _ _ |- _ =>
          pose proof (body_lookup_mod _ _ _ _ _ H); clear H
      | H : mt_side _ _ = true |- _ => pose proof (mt_side_true _ _ H); clear H
      | H : mt_side _ _ = false |- _ => destruct (mt_side_false _ _ H) as [? ?]; clear H; subst
      | H : ctx_find_slot _ _ = None |- _ => pose proof (ctx_find_slot_none _ _ H); clear H
      end.

  #[local]
  Ltac pos_tac :=
    first [ eapply mt_unit; solve [ eauto ]
          | eapply mt_lit; solve [ eauto ]
          | match goal with Hf : ctx_find_slot ?G ?x = Some (?U0, ?G') |- member_type _ ?G (me_var ?x) _ _ =>
              eapply mt_var with (U := uwk_n (S x) U0);
                [ apply ctx_find_mod_sound, (ctx_find_slot_mod _ _ _ _ Hf) | eapply ctx_find_slot_wk; eassumption ] end
          | eapply mt_mem; cycle 1; [ solve [ eauto ] | solve [ eauto ] ]
          | eapply mt_app; solve [ eauto ]
          | eapply umt_self
          | eapply umt_def; solve [ eauto ]
          | eapply umt_mod; cycle 1; [ solve [ eauto ] | solve [ eauto ] | solve [ eauto ] ]
          | eapply umt_alias; solve [ eauto ] ].

  #[local]
  Ltac invert_concrete :=
    match goal with
    | Hm : member_type _ _ (me_unit _) _ _ |- False => inversion Hm; subst; clear Hm
    | Hm : member_type _ _ (me_var _) _ _ |- False => inversion Hm; subst; clear Hm
    | Hm : member_type _ _ (me_lit _) _ _ |- False => inversion Hm; subst; clear Hm
    | Hm : member_type _ _ (me_mem _ _) _ _ |- False => inversion Hm; subst; clear Hm
    | Hm : member_type _ _ (me_app _ _) _ _ |- False => inversion Hm; subst; clear Hm
    | Hm : unit_member_type _ _ (gu_mk _ _) _ _ |- False => inversion Hm; subst; clear Hm
    end.

  #[local]
  Ltac neg_close :=
    repeat match goal with
      | H1 : member_type ?T ?G ?M ?c ?A1, H2 : member_type ?T ?G ?M ?c ?A2 |- _ =>
          assert_fails (constr_eq A1 A2);
          pose proof (proj1 (member_type_functional _) _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : unit_member_type ?T ?G ?U ?c ?A1, H2 : unit_member_type ?T ?G ?U ?c ?A2 |- _ =>
          assert_fails (constr_eq A1 A2);
          pose proof (proj2 (member_type_functional _) _ _ _ _ H1 _ H2); subst; clear H2
      | Hl : ctx_lookup_mod ?x ?U ?G, Hf : ctx_find_slot ?G ?x = Some (?U0, ?G') |- _ =>
          apply ctx_find_mod_complete in Hl; rewrite (ctx_find_slot_mod _ _ _ _ Hf) in Hl; injection Hl as <-
      | Hl : ctx_lookup_mod ?x ?U ?G, Hf : ctx_find_mod ?G ?x = None |- _ =>
          apply ctx_find_mod_complete in Hl; rewrite Hf in Hl; discriminate Hl
      | H1 : gc_unit _ ?p = Some ?a, H2 : gc_unit _ ?p = Some ?b |- _ =>
          assert_fails (constr_eq a b); rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_unit _ ?p = Some ?a, H2 : gc_unit _ ?p = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | H1 : gm_prefix_upto ?Φ ?y = Some ?a, H2 : gm_prefix_upto ?Φ ?y = Some ?b |- _ =>
          assert_fails (constr_eq a b); rewrite H1 in H2; injection H2; clear H2; intros; subst
      | Hf : ctx_find_slot ?G ?x = Some (?U0, ?G'), Hu : unit_member_type _ ?G (uwk_n (S ?x) ?U0) _ _ |- _ =>
          destruct (ctx_find_slot_strengthen _ Hc _ _ _ _ _ _ Hf Hu) as (? & ? & ?); clear Hu
      end;
    first [ congruence
          | match goal with HN : forall R, ~ _ |- _ => eapply HN; eassumption end
          | intuition congruence
          | match goal with Eb : body_lookup ?Φ ?y = bl_none, Hp : gm_prefix_upto ?Φ ?y = Some (gm_ext _ ?y (ge_def _ _ _)) |- _ =>
              exact (body_lookup_none_def _ _ _ _ _ _ Eb Hp) end
          | match goal with Eb : body_lookup ?Φ ?y = bl_none, Hp : gm_prefix_upto ?Φ ?y = Some (gm_ext _ ?y (ge_mod _ _)) |- _ =>
              exact (body_lookup_none_mod _ _ _ _ _ Eb Hp) end
          | match goal with Eb : body_lookup ?Φ ?y = _, Hp : gm_prefix_upto ?Φ ?y = Some _ |- _ =>
              unfold body_lookup in Eb; rewrite Hp in Eb; discriminate Eb end ].

  #[local]
  Ltac impl_obl_tac :=
    intros; cbv beta in *;
    repeat match goal with
      | H : mt_order _ _ _ _ |- _ => progressive_invert H
      | H : umt_order _ _ _ _ |- _ => progressive_invert H
      end;
    lookups;
    repeat match goal with H : ?a = ?a -> _ |- _ => specialize (H eq_refl) end;
    try solve [ eauto ];
    lazymatch goal with
    | |- False => invert_concrete; neg_close
    | _ => try pos_tac
    end.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations member_type_impl Γ H ch (Ho : mt_order Θ Γ H ch) :
      { R | member_type Θ Γ H ch R } + { forall R, ~ member_type Θ Γ H ch R } by struct Ho :=
  | Γ, me_unit fp, ch, Ho with inspect (gc_unit Θ fp) := {
    | exist _ (Some U) Er with unit_member_type_impl nil U ch _ := {
      | inleft (exist _ R HR) => inleft (exist _ R _)
      | inright HN => inright _ }
    | exist _ None Er => inright _ }
  | Γ, me_var x, ch, Ho with inspect (ctx_find_slot Γ x) := {
    | exist _ (Some (U0, Γ')) Ef with unit_member_type_impl Γ' U0 ch _ := {
      | inleft (exist _ R0 HR0) => inleft (exist _ (rwk_n (S x) R0) _)
      | inright HN => inright _ }
    | exist _ None Ef => inright _ }
  | Γ, me_lit U, ch, Ho with unit_member_type_impl Γ U ch _ := {
    | inleft (exist _ R HR) => inleft (exist _ R _)
    | inright HN => inright _ }
  | Γ, me_mem M y, ch, Ho with member_type_impl Γ M (y :: ch) _ := {
    | inleft (exist _ R HR) with inspect (mt_side R ch) := {
      | exist _ true Es => inleft (exist _ R _)
      | exist _ false Es => inright _ }
    | inright HN => inright _ }
  | Γ, me_app M N, ch, Ho with member_type_impl Γ M ch _ := {
    | inleft (exist _ R HR) with inspect (mres_app R N) := {
      | exist _ (Some R') Ea => inleft (exist _ R' _)
      | exist _ None Ea => inright _ }
    | inright HN => inright _ }

  with unit_member_type_impl Γ U ch (Ho : umt_order Θ Γ U ch) :
      { R | unit_member_type Θ Γ U ch R } + { forall R, ~ unit_member_type Θ Γ U ch R } by struct Ho :=
  | Γ, gu_mk Δ (md_body Φ), nil, Ho => inleft (exist _ (mr_mod Δ) _)
  | Γ, gu_mk Δ (md_body Φ), y :: ch, Ho with inspect (body_lookup Φ y) := {
    | exist _ (bl_def Φ' A) Eb with inspect (mt_side (mr_term A) ch) := {
      | exist _ true Es => inright _
      | exist _ false Es => inleft (exist _ (mr_term (ctx_pi (self_ent Φ' :: Δ) A)) _) }
    | exist _ (bl_mod Φ' pm Uy) Eb with unit_member_type_impl (self_ent Φ' :: Δ ++ Γ) Uy ch _ := {
      | inleft (exist _ R HR) with inspect (mt_side R ch) := {
        | exist _ true Es => inleft (exist _ (mres_gen (self_ent Φ' :: Δ) R) _)
        | exist _ false Es => inright _ }
      | inright HN => inright _ }
    | exist _ bl_none Eb => inright _ }
  | Γ, gu_mk Δ (md_alias E), ch, Ho with member_type_impl (Δ ++ Γ) E ch _ := {
    | inleft (exist _ R HR) => inleft (exist _ (mres_gen Δ R) _)
    | inright HN => inright _ }.
  (** The obligations [Equations] leaves are solved by the same tactic, run
      on each in turn. *)
  Next Obligation. impl_obl_tac. Qed.
  Next Obligation. impl_obl_tac. Qed.
  Next Obligation. impl_obl_tac. Qed.
  Next Obligation. impl_obl_tac. Qed.
  Next Obligation. impl_obl_tac. Qed.
  Next Obligation. impl_obl_tac. Qed.
  Next Obligation. impl_obl_tac. Qed.
  Next Obligation. impl_obl_tac. Qed.
  Next Obligation. impl_obl_tac. Qed.
  Next Obligation. impl_obl_tac. Qed.
  Next Obligation. impl_obl_tac. Qed.
  Next Obligation. impl_obl_tac. Qed.
  Next Obligation. impl_obl_tac. Qed.
  Next Obligation. impl_obl_tac. Qed.
End MemberTypeImpl.

(** ** Every Module Expression Has an Order *)

(** Every unit of [Θ1] has an order at [Θ2], at every chain. *)
Definition units_ordered (Θ1 : gctx) (Θ2 : gctx) : Prop :=
  forall fp U, gc_unit Θ1 fp = Some U -> forall ch, umt_order Θ2 nil U ch.

Lemma ctx_find_slot_size : forall Γ x U0 Γ', ctx_find_slot Γ x = Some (U0, Γ') ->
    usize U0 + csize Γ' <= csize Γ.
Proof.
  intros * Hf; destruct (ctx_find_slot_split _ _ _ _ Hf) as [Ψ ->].
  rewrite csize_app; cbn; lia.
Qed.

Lemma msize_pos : forall H, 1 <= msize H.
Proof. destruct H; cbn; lia. Qed.

Lemma usize_pos : forall U, 1 <= usize U.
Proof. destruct U; rewrite usize_mk; lia. Qed.

(** A submodule under its self slot is smaller than the body it is in. *)
Lemma self_size : forall Φ y Φ' pm Uy Δ Γ, gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
    usize Uy + csize (self_ent Φ' :: Δ ++ Γ) < usize (gu_body Δ Φ) + csize Γ.
Proof.
  intros * Hp; pose proof (gsize_prefix _ _ _ Hp) as Hsz; cbn in Hsz.
  unfold self_ent; cbn [csize]; rewrite !usize_mk, csize_app; cbn [csize dsize]; lia.
Qed.

(** A well-formed module expression of [Θ1] has an order at [Θ2], if the
    units of [Θ1] have. *)
Theorem mt_order_exists : forall Θ1 Θ2, gc_sub Θ1 Θ2 -> units_ordered Θ1 Θ2 ->
    forall n,
      (forall Γ H, msize H + csize Γ <= n -> Θ1 ⍮ Γ ⊢ᵐ H ≈ H ->
         forall ch, mt_order Θ2 Γ H ch) /\
      (forall Γ U, usize U + csize Γ <= n -> Θ1 ⍮ Γ ⊢ᵘ U ≈ U ->
         forall ch, umt_order Θ2 Γ U ch).
Proof.
  intros * Hs Ha.
  induction n as [| n [IHm IHu]].
  { split; intros * Hn; [ pose proof (msize_pos H) | pose proof (usize_pos U) ]; lia. }
  split.
  - intros Γ H Hn HH ch.
    destruct H as [fp | x | H y | H N | U]; cbn [msize] in Hn.
    + destruct (modexp_parts_of_wf _ _ _ HH) as [U0 HU0].
      constructor; intros U Hl.
      rewrite (gc_sub_unit _ _ _ _ Hs HU0) in Hl; injection Hl as <-.
      exact (Ha _ _ HU0 ch).
    + constructor; intros U0 Γ' Hf.
      pose proof (ctx_find_slot_size _ _ _ _ Hf).
      destruct (ctx_find_slot_split _ _ _ _ Hf) as [Ψ EΓ].
      pose proof (presup_modexp_eq_ctx HH) as HΓ; rewrite EΓ in HΓ.
      apply ctx_app_wf_right in HΓ.
      apply IHu; [ lia | exact (proj2 (ctx_decomp_mod HΓ)) ].
    + destruct (modexp_parts_of_wf _ _ _ HH) as [HH' _].
      constructor; apply IHm; [ lia | exact HH' ].
    + destruct (modexp_parts_of_wf _ _ _ HH) as [HH' _].
      constructor; apply IHm; [ lia | exact HH' ].
    + pose proof (modexp_parts_of_wf _ _ _ HH) as HU; cbn in HU.
      constructor; apply IHu; [ lia | exact HU ].
  - intros Γ U Hn HU ch.
    destruct U as [Δ [Φ | E]].
    + destruct (unit_parts_of_wf _ _ _ HU) as (HC & _ & Hb).
      destruct ch as [| y ch]; [ constructor |].
      constructor; intros Φ' pm Uy Hp.
      pose proof (self_size _ _ _ _ _ Δ Γ Hp) as Hsz.
      destruct (body_ok_prefix _ _ _ _ _ _ Hb Hp) as [_ HUy].
      apply IHu; [ lia | exact HUy ].
    + rewrite usize_mk in Hn; cbn [dsize] in Hn.
      destruct (unit_parts_of_wf _ _ _ HU) as (_ & _ & HE).
      constructor; apply IHm; [ rewrite csize_app; lia | exact HE ].
Qed.

(** Every unit of a well-formed global context has an order, wherever the
    context embeds: it names only units filed below it. *)
Definition unit_V (Θ2 : gctx) (U : gunit) : Prop := forall ch, umt_order Θ2 nil U ch.

Lemma unit_V_of : forall Θ U Θ2, Θ ⍮ ⋅ ⊢ᵘ U ≈ U -> Good (fun _ _ _ => True) unit_V Θ -> Emb Θ Θ2 -> unit_V Θ2 U.
Proof.
  intros * HU HG He ch.
  assert (Ha : units_ordered Θ Θ2) by (intros fp U0 Hl; exact (proj2 (HG _ He) _ _ Hl)).
  eapply (proj2 (mt_order_exists _ _ (em_res _ _ He) Ha _)); [ reflexivity | exact HU ].
Qed.

Theorem gctx_units_ordered : forall Θ, ⊢g Θ -> units_ordered Θ Θ.
Proof.
  intros * Hg fp U Hl ch.
  exact (proj2 (global_induction (fun _ _ _ => True) unit_V ltac:(intros; exact I) unit_V_of _ Hg) _ _ Hl ch).
Qed.

Lemma gctx_closed_of_wf : forall Θ, ⊢g Θ -> gctx_closed Θ.
Proof. intros * Hg; eapply wf_gctx_closed; constructor; exact Hg. Qed.

Corollary mt_order_unit : forall Θ Γ fp ch, ⊢g Θ -> mt_order Θ Γ (me_unit fp) ch.
Proof. intros * Hg; constructor; intros U Hl; exact (gctx_units_ordered _ Hg _ _ Hl ch). Qed.

(** The recursion of [member_type_impl] is on sizes: a slot is read in the
    context after it, and a submodule under the self slot of the body before
    it, both smaller; only a unit needs the global context, whose units have
    an order ([gctx_units_ordered]).  So no well-formedness of [H] is
    needed. *)
Theorem mt_order_total_n : forall Θ, ⊢g Θ -> forall n,
    (forall Γ H, msize H + csize Γ <= n -> forall ch, mt_order Θ Γ H ch) /\
    (forall Γ U, usize U + csize Γ <= n -> forall ch, umt_order Θ Γ U ch).
Proof.
  intros * Hg; induction n as [| n [IHm IHu]].
  { split; intros * Hn; [ pose proof (msize_pos H) | pose proof (usize_pos U) ]; lia. }
  split.
  - intros Γ H Hn ch; destruct H as [fp | x | H y | H N | U]; cbn [msize] in Hn.
    + apply mt_order_unit, Hg.
    + constructor; intros U0 Γ' Hf; pose proof (ctx_find_slot_size _ _ _ _ Hf); apply IHu; lia.
    + constructor; apply IHm; lia.
    + constructor; apply IHm; lia.
    + constructor; apply IHu; lia.
  - intros Γ U Hn ch; destruct U as [Δ [Φ | E]].
    + destruct ch as [| y ch]; [ constructor |].
      constructor; intros Φ' pm Uy Hp.
      pose proof (self_size _ _ _ _ _ Δ Γ Hp); apply IHu; lia.
    + rewrite usize_mk in Hn; cbn [dsize] in Hn.
      constructor; apply IHm; rewrite csize_app; lia.
Qed.

Corollary mt_order_total : forall Θ, ⊢g Θ -> forall Γ H ch, mt_order Θ Γ H ch.
Proof. intros * Hg Γ H; exact (proj1 (mt_order_total_n _ Hg _) Γ H (le_n _)). Qed.

Corollary mt_order_of_wf : forall Θ Γ H, ⊢g Θ -> Θ ⍮ Γ ⊢ᵐ H ≈ H ->
    forall ch, mt_order Θ Γ H ch.
Proof. intros * Hg _ ch; exact (mt_order_total _ Hg _ _ ch). Qed.

(** ** The Oracle of a Well-Formed Global Context *)

Definition mt_of (Θ : gctx) (Hg : ⊢g Θ) : mt_oracle :=
  fun Γ H ch =>
    match member_type_impl Θ (gctx_closed_of_wf _ Hg) Γ H ch (mt_order_total _ Hg Γ H ch) with
    | inleft (exist _ R _) => Some R
    | inright _ => None
    end.

Lemma mt_of_spec : forall Θ (Hg : ⊢g Θ), mt_spec Θ (mt_of Θ Hg).
Proof.
  intros * Γ H ch R; unfold mt_of.
  destruct (member_type_impl _ _ _ _ _ _) as [[R' HR'] | HN]; split; intros HR.
  - injection HR as <-; exact HR'.
  - f_equal; exact (proj1 (member_type_functional _) _ _ _ _ HR' _ HR).
  - discriminate.
  - exfalso; exact (HN _ HR).
Qed.
