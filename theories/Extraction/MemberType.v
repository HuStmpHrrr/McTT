(** * Computing Member Types

    [member_type_impl] decides [member_type] by recursion on a termination
    order ([mt_order]), which mirrors its recursion: a slot is read in the
    context after it, so the context gets shorter as the syntax grows, and an
    alias is read in the empty context, where the order asks for the alias's
    own order.  Every alias of a well-formed global context has one
    ([gctx_aliases_ordered]), since an alias can only name modules that are
    already there, so every well-formed module expression has an order
    ([mt_order_of_wf]). *)

From Stdlib Require Import Lia List PeanoNat String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Syntactic.System Require Import MemberLemmas GlobalModules MemberWf.
From Mctt.Core.Completeness Require Import MemberSem.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Sizes

    The size of a module expression or a unit counts its nested units, and
    the size of a context counts the units of its slots: the terms of either
    are never looked at. *)

Fixpoint msize (H : modexp) : nat :=
  match H with
  | me_path _ | me_var _ => 1
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
  | gm_ext Φ _ (ge_mod U) => gsize Φ + usize U
  | gm_ext Φ _ _ | gm_check Φ _ => gsize Φ
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

Lemma csize_body_ctx : forall Φ, csize (body_ctx Φ) = gsize Φ.
Proof.
  induction Φ as [| Φ IH x [b pv A [M |] | U] | Φ IH c]; cbn; rewrite ?IH; lia.
Qed.

Lemma gsize_prefix : forall Φ x Φx, gm_prefix_upto Φ x = Some Φx -> gsize Φx <= gsize Φ.
Proof.
  induction Φ as [| Φ IH y E | Φ IH c]; intros * H; cbn in H; try discriminate.
  - destruct (String.eqb x y); [ injection H as <-; lia |].
    specialize (IH _ _ H); destruct E as [? ? ? ? | U]; cbn; lia.
  - specialize (IH _ _ H); cbn; lia.
Qed.

Lemma gm_prefix_upto_name : forall Φ x Φ' y E, gm_prefix_upto Φ x = Some (gm_ext Φ' y E) -> y = x.
Proof.
  induction Φ as [| Φ IH z E0 | Φ IH c]; intros * H; cbn in H; try discriminate; eauto.
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

Fixpoint ewk_n (n : nat) (A : typ) : typ :=
  match n with
  | 0 => A
  | S n => (ewk_n n A)[wk_shift]ʷ
  end.

Arguments uwk_n : simpl never.
Arguments ewk_n : simpl never.

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
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hc : gctx_closed Θ Ξ.

  Lemma ctx_find_slot_wk : forall Γ x U0 Γ' ch k A0, ctx_find_slot Γ x = Some (U0, Γ') ->
      unit_member_type Θ Ξ Γ' U0 ch k A0 ->
      unit_member_type Θ Ξ Γ (uwk_n (S x) U0) ch k (ewk_n (S x) A0).
  Proof.
    induction Γ as [| e Γ IH]; intros [| y] * H Hu; cbn in H; try discriminate.
    - destruct e; try discriminate; injection H as -> ->.
      exact (proj2 (member_type_wk _ _ Hc) _ _ _ _ _ Hu _ _ (fun x U Hl => mod_there _ _ _ _ Hl)).
    - specialize (IH _ _ _ _ _ _ H Hu).
      exact (proj2 (member_type_wk _ _ Hc) _ _ _ _ _ IH _ _ (fun x U Hl => mod_there _ _ _ _ Hl)).
  Qed.

  Lemma ctx_find_slot_strengthen : forall Γ x U0 Γ' ch k A, ctx_find_slot Γ x = Some (U0, Γ') ->
      unit_member_type Θ Ξ Γ (uwk_n (S x) U0) ch k A ->
      exists A0, unit_member_type Θ Ξ Γ' U0 ch k A0 /\ A = ewk_n (S x) A0.
  Proof.
    induction Γ as [| e Γ IH]; intros [| y] * H Hu; cbn in H; try discriminate.
    - destruct e; try discriminate; injection H as -> ->.
      exact (proj2 (member_type_strengthen _ _ Hc) _ _ _ _ _ Hu _ _ _ eq_refl (wk_mod_inv_shift _ _)).
    - destruct (proj2 (member_type_strengthen _ _ Hc) _ _ _ _ _ Hu _ _ _ eq_refl (wk_mod_inv_shift _ _))
        as (A1 & HA1 & ->).
      destruct (IH _ _ _ _ _ _ H HA1) as (A0 & HA0 & ->); eauto.
  Qed.
End Slots.

(** ** The Termination Order *)

Inductive mt_order (Θ : gdeps) (Ξ : gstack) : ctx -> modexp -> list string -> mkind -> Prop :=
| mto_path : forall Γ pq ch k,
    (forall U r, gc_module Θ Ξ (path_app pq ch) = Some (mr_alias U r) -> umt_order Θ Ξ nil U r k) ->
    mt_order Θ Ξ Γ (me_path pq) ch k
| mto_var : forall Γ x ch k,
    (forall U0 Γ', ctx_find_slot Γ x = Some (U0, Γ') -> umt_order Θ Ξ Γ' U0 ch k) ->
    mt_order Θ Ξ Γ (me_var x) ch k
| mto_lit : forall Γ U ch k,
    umt_order Θ Ξ Γ U ch k ->
    mt_order Θ Ξ Γ (me_lit U) ch k
| mto_mem : forall Γ H y ch k,
    mt_order Θ Ξ Γ H (y :: ch) k ->
    mt_order Θ Ξ Γ (me_mem H y) ch k
| mto_app : forall Γ H N ch k,
    mt_order Θ Ξ Γ H ch k ->
    mt_order Θ Ξ Γ (me_app H N) ch k
with umt_order (Θ : gdeps) (Ξ : gstack) : ctx -> gunit -> list string -> mkind -> Prop :=
| umto_body_nil : forall Γ Δ Φ k,
    umt_order Θ Ξ Γ (gu_body Δ Φ) nil k
| umto_body_cons : forall Γ Δ Φ y ch k,
    (forall Φ' Uy, gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod Uy)) ->
       umt_order Θ Ξ (body_ctx Φ' ++ Δ ++ Γ) Uy ch k) ->
    umt_order Θ Ξ Γ (gu_body Δ Φ) (y :: ch) k
| umto_alias : forall Γ Δ E ch k,
    mt_order Θ Ξ (Δ ++ Γ) E ch k ->
    umt_order Θ Ξ Γ (gu_mk Δ (md_alias E)) ch k.

(** ** The Decision Procedure

    The lookups are made by functions, so that the procedure matches on
    their results only. *)

Definition mt_side (k : mkind) (ch : list string) : bool :=
  match k, ch with
  | mk_term, nil => false
  | _, _ => true
  end.

Lemma mt_side_true : forall k ch, mt_side k ch = true -> k = mk_term -> ch <> nil.
Proof. intros [] [] H; cbn in H; congruence. Qed.

Lemma mt_side_false : forall k ch, mt_side k ch = false -> k = mk_term /\ ch = nil.
Proof. intros [] [] H; cbn in H; auto; discriminate. Qed.

Inductive plookup : Set :=
| pl_def : typ -> plookup
| pl_alias : gunit -> list string -> plookup
| pl_none : plookup.

(** A term member of a path: a filed public definition, or a member of an
    alias with a non-empty rest of the chain. *)
Definition path_lookup_term (Θ : gdeps) (Ξ : gstack) (p : path) : plookup :=
  match gc_resolve Θ Ξ p with
  | Some (ge_def _ false A _) => pl_def A
  | _ =>
      match gc_module Θ Ξ p with
      | Some (mr_alias U (y :: r)) => pl_alias U (y :: r)
      | _ => pl_none
      end
  end.

Inductive blookup : Set :=
| bl_def : gmod -> typ -> blookup
| bl_mod : gmod -> gunit -> blookup
| bl_none : blookup.

Definition body_lookup (Φ : gmod) (y : string) : blookup :=
  match gm_prefix_upto Φ y with
  | Some (gm_ext Φ' _ (ge_def _ false A _)) => bl_def Φ' A
  | Some (gm_ext Φ' _ (ge_mod Uy)) => bl_mod Φ' Uy
  | _ => bl_none
  end.

Lemma path_lookup_term_def : forall Θ Ξ p A, path_lookup_term Θ Ξ p = pl_def A ->
    exists b B, gc_resolve Θ Ξ p = Some (ge_def b false A B).
Proof.
  intros * H; unfold path_lookup_term in H.
  destruct (gc_resolve Θ Ξ p) as [[b [|] A0 B0 | U0] |]; try (injection H as ->; eauto; fail);
    destruct (gc_module Θ Ξ p) as [[T | U1 [| y r]] |]; discriminate.
Qed.

Lemma path_lookup_term_alias : forall Θ Ξ p U r, path_lookup_term Θ Ξ p = pl_alias U r ->
    gc_module Θ Ξ p = Some (mr_alias U r) /\ r <> nil.
Proof.
  intros * H; unfold path_lookup_term in H.
  destruct (gc_resolve Θ Ξ p) as [[b [|] A0 B0 | U1] |]; try discriminate;
    destruct (gc_module Θ Ξ p) as [[T | U0 [| y r0]] |] eqn:Em; try discriminate;
    injection H as <- <-; split; try reflexivity; discriminate.
Qed.

Lemma path_lookup_term_none : forall Θ Ξ p, path_lookup_term Θ Ξ p = pl_none ->
    (forall b A B, gc_resolve Θ Ξ p <> Some (ge_def b false A B)) /\
    (forall U r, r <> nil -> gc_module Θ Ξ p <> Some (mr_alias U r)).
Proof.
  intros * H; unfold path_lookup_term in H.
  destruct (gc_resolve Θ Ξ p) as [[b [|] A0 B0 | U1] |] eqn:Er; try discriminate;
    (destruct (gc_module Θ Ξ p) as [[T | U0 [| y r0]] |] eqn:Em; try discriminate);
    split; intros * E; try congruence; intros E'; congruence.
Qed.

Lemma body_lookup_def : forall Φ y Φ' A, body_lookup Φ y = bl_def Φ' A ->
    exists b B, gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_def b false A B)).
Proof.
  intros * H; unfold body_lookup in H.
  destruct (gm_prefix_upto Φ y) as [[| Φ0 z [b [|] A0 B0 | U] | Φ0 c] |] eqn:E; try discriminate.
  injection H as -> ->; pose proof (gm_prefix_upto_name _ _ _ _ _ E) as ->; eauto.
Qed.

Lemma body_lookup_mod : forall Φ y Φ' Uy, body_lookup Φ y = bl_mod Φ' Uy ->
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod Uy)).
Proof.
  intros * H; unfold body_lookup in H.
  destruct (gm_prefix_upto Φ y) as [[| Φ0 z [b [|] A0 B0 | U] | Φ0 c] |] eqn:E; try discriminate.
  injection H as -> ->; pose proof (gm_prefix_upto_name _ _ _ _ _ E) as ->; reflexivity.
Qed.

Lemma body_lookup_none_def : forall Φ y Φ' b A B, body_lookup Φ y = bl_none ->
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_def b false A B)) -> False.
Proof. intros * H E; unfold body_lookup in H; rewrite E in H; discriminate. Qed.

Lemma body_lookup_none_mod : forall Φ y Φ' Uy, body_lookup Φ y <> bl_mod Φ' Uy ->
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod Uy)) -> False.
Proof. intros * H E; unfold body_lookup in H; rewrite E in H; auto. Qed.

Lemma body_lookup_not_def : forall Φ y Φ' b A B, (forall Φ0 A0, body_lookup Φ y <> bl_def Φ0 A0) ->
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_def b false A B)) -> False.
Proof. intros * H E; unfold body_lookup in H; rewrite E in H; eapply H; reflexivity. Qed.

#[local] Opaque mt_side.

Section MemberTypeImpl.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hc : gctx_closed Θ Ξ.

  Definition inspect {A} (a : A) : { b | a = b } := exist _ a eq_refl.

  #[local]
  Ltac lookups :=
    repeat match goal with
      | H : path_lookup_term _ _ _ = pl_def _ |- _ =>
          destruct (path_lookup_term_def _ _ _ _ H) as (? & ? & ?); clear H
      | H : path_lookup_term _ _ _ = pl_alias _ _ |- _ =>
          destruct (path_lookup_term_alias _ _ _ _ _ H) as [? ?]; clear H
      | H : path_lookup_term _ _ _ = pl_none |- _ =>
          destruct (path_lookup_term_none _ _ _ H) as [? ?]; clear H
      | H : body_lookup _ _ = bl_def _ _ |- _ =>
          destruct (body_lookup_def _ _ _ _ H) as (? & ? & ?); clear H
      | H : body_lookup _ _ = bl_mod _ _ |- _ =>
          pose proof (body_lookup_mod _ _ _ _ H); clear H
      | H : mt_side _ _ = true |- _ => pose proof (mt_side_true _ _ H); clear H
      | H : mt_side _ _ = false |- _ => destruct (mt_side_false _ _ H) as [? ?]; clear H; subst
      | H : ctx_find_slot _ _ = None |- _ => pose proof (ctx_find_slot_none _ _ H); clear H
      end.

  #[local]
  Ltac pos_tac :=
    first [ eapply mt_path_def; solve [ eauto ]
          | eapply mt_path_mod; solve [ eauto ]
          | eapply mt_path_alias; cycle 1; [ solve [ eauto ] | solve [ eauto ] | solve [ intros _; assumption | intros; discriminate ] ]
          | eapply mt_lit; solve [ eauto ]
          | match goal with Hf : ctx_find_slot ?G ?x = Some (?U0, ?G') |- member_type _ _ ?G (me_var ?x) _ _ _ =>
              eapply mt_var with (U := uwk_n (S x) U0);
                [ apply ctx_find_mod_sound, (ctx_find_slot_mod _ _ _ _ Hf) | eapply ctx_find_slot_wk; eassumption ] end
          | eapply mt_mem; cycle 1; [ solve [ eauto ] | solve [ assumption | intros; discriminate ] ]
          | eapply mt_app; solve [ eauto ]
          | eapply umt_self
          | eapply umt_def; solve [ eauto ]
          | eapply umt_mod; cycle 1; [ solve [ eauto ] | solve [ eauto ] | solve [ assumption | intros; discriminate ] ]
          | eapply umt_alias; solve [ eauto ] ].

  #[local]
  Ltac invert_concrete :=
    match goal with
    | Hm : member_type _ _ _ (me_path _) _ _ _ |- False => inversion Hm; subst; clear Hm
    | Hm : member_type _ _ _ (me_var _) _ _ _ |- False => inversion Hm; subst; clear Hm
    | Hm : member_type _ _ _ (me_lit _) _ _ _ |- False => inversion Hm; subst; clear Hm
    | Hm : member_type _ _ _ (me_mem _ _) _ _ _ |- False => inversion Hm; subst; clear Hm
    | Hm : member_type _ _ _ (me_app _ _) _ _ _ |- False => inversion Hm; subst; clear Hm
    | Hm : unit_member_type _ _ _ (gu_mk _ _) _ _ _ |- False => inversion Hm; subst; clear Hm
    end.

  #[local]
  Ltac neg_close :=
    repeat match goal with
      | H1 : member_type ?T ?X ?G ?M ?c ?k ?A1, H2 : member_type ?T ?X ?G ?M ?c ?k ?A2 |- _ =>
          assert_fails (constr_eq A1 A2);
          pose proof (proj1 (member_type_functional _ _) _ _ _ _ _ H1 _ H2); subst; clear H2
      | Hl : ctx_lookup_mod ?x ?U ?G, Hf : ctx_find_slot ?G ?x = Some (?U0, ?G') |- _ =>
          apply ctx_find_mod_complete in Hl; rewrite (ctx_find_slot_mod _ _ _ _ Hf) in Hl; injection Hl as <-
      | Hl : ctx_lookup_mod ?x ?U ?G, Hf : ctx_find_mod ?G ?x = None |- _ =>
          apply ctx_find_mod_complete in Hl; rewrite Hf in Hl; discriminate Hl
      | H1 : gc_module _ _ ?p = Some ?a, H2 : gc_module _ _ ?p = Some ?b |- _ =>
          assert_fails (constr_eq a b); rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gc_resolve _ _ ?p = Some ?a, H2 : gc_resolve _ _ ?p = Some ?b |- _ =>
          assert_fails (constr_eq a b); rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : gm_prefix_upto ?Φ ?y = Some ?a, H2 : gm_prefix_upto ?Φ ?y = Some ?b |- _ =>
          assert_fails (constr_eq a b); rewrite H1 in H2; injection H2; clear H2; intros; subst
      | Hf : ctx_find_slot ?G ?x = Some (?U0, ?G'), Hu : unit_member_type _ _ ?G (uwk_n (S ?x) ?U0) _ _ _ |- _ =>
          destruct (ctx_find_slot_strengthen _ _ Hc _ _ _ _ _ _ _ Hf Hu) as (? & ? & ?); clear Hu
      end;
    first [ congruence
          | exfalso; eapply gc_resolve_module_alias_excl; eassumption
          | match goal with HN : forall A, ~ _ |- _ => eapply HN; eassumption end
          | intuition congruence
          | match goal with H : forall b A B, ?f <> Some (ge_def b false A B), H' : ?f = Some (ge_def _ false _ _) |- _ =>
              exact (H _ _ _ H') end
          | match goal with H : forall U r, r <> nil -> ?f <> Some (mr_alias U r), H' : ?f = Some (mr_alias _ _) |- _ =>
              eapply H; [| exact H' ]; eauto end
          | match goal with Eb : body_lookup ?Φ ?y = bl_none, Hp : gm_prefix_upto ?Φ ?y = Some (gm_ext _ ?y (ge_def _ false _ _)) |- _ =>
              exact (body_lookup_none_def _ _ _ _ _ _ Eb Hp) end
          | match goal with Eb : body_lookup ?Φ ?y = _, Hp : gm_prefix_upto ?Φ ?y = Some _ |- _ =>
              unfold body_lookup in Eb; rewrite Hp in Eb; discriminate Eb end ].

  #[local]
  Ltac impl_obl_tac :=
    intros; cbv beta in *;
    repeat match goal with
      | H : mt_order _ _ _ _ _ _ |- _ => progressive_invert H
      | H : umt_order _ _ _ _ _ _ |- _ => progressive_invert H
      end;
    lookups;
    repeat match goal with H : ?a = ?a -> _ |- _ => specialize (H eq_refl) end;
    try solve [ eauto ];
    lazymatch goal with
    | |- False => invert_concrete; neg_close
    | _ => try pos_tac
    end.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations member_type_impl Γ H ch k (Ho : mt_order Θ Ξ Γ H ch k) :
      { A | member_type Θ Ξ Γ H ch k A } + { forall A, ~ member_type Θ Ξ Γ H ch k A } by struct Ho :=
  | Γ, me_path pq, ch, mk_term, Ho with inspect (path_lookup_term Θ Ξ (path_app pq ch)) := {
    | exist _ (pl_def A) Er with inspect (mt_side mk_term ch) := {
      | exist _ true Es => inleft (exist _ A _)
      | exist _ false Es => inright _ }
    | exist _ (pl_alias U r) Er with unit_member_type_impl nil U r mk_term _ := {
      | inleft (exist _ A HA) => inleft (exist _ A _)
      | inright HN => inright _ }
    | exist _ pl_none Er => inright _ }
  | Γ, me_path pq, ch, mk_mod, Ho with inspect (gc_module Θ Ξ (path_app pq ch)) := {
    | exist _ (Some (mr_body T)) Em => inleft (exist _ (ctx_pi T a_True) _)
    | exist _ (Some (mr_alias U r)) Em with unit_member_type_impl nil U r mk_mod _ := {
      | inleft (exist _ A HA) => inleft (exist _ A _)
      | inright HN => inright _ }
    | exist _ None Em => inright _ }
  | Γ, me_var x, ch, k, Ho with inspect (ctx_find_slot Γ x) := {
    | exist _ (Some (U0, Γ')) Ef with unit_member_type_impl Γ' U0 ch k _ := {
      | inleft (exist _ A0 HA0) => inleft (exist _ (ewk_n (S x) A0) _)
      | inright HN => inright _ }
    | exist _ None Ef => inright _ }
  | Γ, me_lit U, ch, k, Ho with unit_member_type_impl Γ U ch k _ := {
    | inleft (exist _ A HA) => inleft (exist _ A _)
    | inright HN => inright _ }
  | Γ, me_mem M y, ch, k, Ho with inspect (mt_side k ch) := {
    | exist _ false Es => inright _
    | exist _ true Es with member_type_impl Γ M (y :: ch) k _ := {
      | inleft (exist _ A HA) => inleft (exist _ A _)
      | inright HN => inright _ } }
  | Γ, me_app M N, ch, k, Ho with member_type_impl Γ M ch k _ := {
    | inleft (exist _ A HA) with inspect (pi_view A) := {
      | exist _ (Some (B, C)) Ep => inleft (exist _ C[Id,,N] _)
      | exist _ None Ep => inright _ }
    | inright HN => inright _ }

  with unit_member_type_impl Γ U ch k (Ho : umt_order Θ Ξ Γ U ch k) :
      { A | unit_member_type Θ Ξ Γ U ch k A } + { forall A, ~ unit_member_type Θ Ξ Γ U ch k A } by struct Ho :=
  | Γ, gu_mk Δ (md_body Φ), nil, mk_mod, Ho => inleft (exist _ (ctx_pi Δ a_True) _)
  | Γ, gu_mk Δ (md_body Φ), nil, mk_term, Ho => inright _
  | Γ, gu_mk Δ (md_body Φ), y :: ch, k, Ho with inspect (body_lookup Φ y) := {
    | exist _ (bl_def Φ' A) Eb with inspect (mt_side k ch) := {
      | exist _ true Es => inright _
      | exist _ false Es => inleft (exist _ (ctx_pi (body_ctx Φ' ++ Δ) A) _) }
    | exist _ (bl_mod Φ' Uy) Eb with inspect (mt_side k ch) := {
      | exist _ false Es => inright _
      | exist _ true Es with unit_member_type_impl (body_ctx Φ' ++ Δ ++ Γ) Uy ch k _ := {
        | inleft (exist _ A HA) => inleft (exist _ (ctx_pi (body_ctx Φ' ++ Δ) A) _)
        | inright HN => inright _ } }
    | exist _ bl_none Eb => inright _ }
  | Γ, gu_mk Δ (md_alias E), ch, k, Ho with member_type_impl (Δ ++ Γ) E ch k _ := {
    | inleft (exist _ A HA) => inleft (exist _ (ctx_pi Δ A) _)
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
  Next Obligation. impl_obl_tac. Qed.
  Next Obligation. impl_obl_tac. Qed.
  Next Obligation. impl_obl_tac. Qed.
  Next Obligation. impl_obl_tac. Qed.
End MemberTypeImpl.

(** ** Every Well-Formed Module Expression Has an Order *)

(** What resolves below a module resolves the same in a larger global
    context. *)
Lemma gc_module_below : forall Θ1 Ξ1 Θ2 Ξ2, ⊢g Θ1 ⍮ Ξ1 -> ⊢g Θ2 ⍮ Ξ2 -> gc_sub Θ1 Ξ1 Θ2 Ξ2 ->
    forall pq r0, gc_module Θ1 Ξ1 pq = Some r0 ->
    forall ch, gc_module Θ2 Ξ2 (path_app pq ch) = gc_module Θ1 Ξ1 (path_app pq ch).
Proof.
  intros * Hg1 Hg2 Hs * Hq ch.
  destruct r0 as [T | U r0].
  - destruct (gc_module_body _ _ _ _ Hq) as [Φ HΦ].
    rewrite (proj1 (closed_read _ _ Hg1 _ _ _ HΦ ch)).
    exact (proj1 (closed_read _ _ Hg2 _ _ _ (gc_sub_body _ _ _ _ _ _ Hs HΦ) ch)).
  - rewrite (proj1 (gc_module_alias_app _ _ Hg1 _ _ _ Hq ch)).
    exact (proj1 (gc_module_alias_app _ _ Hg2 _ _ _ (gc_sub_module _ _ _ _ _ _ Hs Hq) ch)).
Qed.

Lemma wf_path_module : forall Θ Ξ Γ pq, wf_modexp_eq Θ Ξ Γ (me_path pq) (me_path pq) ->
    exists r0, gc_module Θ Ξ pq = Some r0.
Proof.
  intros * HH; destruct (modexp_parts_of_wf _ _ _ _ HH) as [A0 Hm0].
  assert (Hq : path_app pq nil = pq) by (destruct pq; unfold path_app; cbn; rewrite app_nil_r; reflexivity).
  inversion Hm0; subst; rewrite Hq in *; eauto.
Qed.

(** Every alias of [Θ1 ⍮ Ξ1] has an order at [Θ2 ⍮ Ξ2], at every chain. *)
Definition aliases_ordered (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  forall p U r, gc_module Θ1 Ξ1 p = Some (mr_alias U r) -> forall r' k, umt_order Θ2 Ξ2 nil U r' k.

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

Theorem mt_order_exists : forall Θ1 Ξ1 Θ2 Ξ2, ⊢g Θ1 ⍮ Ξ1 -> ⊢g Θ2 ⍮ Ξ2 -> gc_sub Θ1 Ξ1 Θ2 Ξ2 ->
    aliases_ordered Θ1 Ξ1 Θ2 Ξ2 ->
    forall n,
      (forall Γ H, msize H + csize Γ <= n -> wf_modexp_eq Θ1 Ξ1 Γ H H ->
         forall ch k, mt_order Θ2 Ξ2 Γ H ch k) /\
      (forall Γ U, usize U + csize Γ <= n -> wf_unit_eq Θ1 Ξ1 Γ U U ->
         forall ch k, umt_order Θ2 Ξ2 Γ U ch k).
Proof.
  intros * Hg1 Hg2 Hs Ha.
  induction n as [| n [IHm IHu]].
  { split; intros * Hn; [ pose proof (msize_pos H) | pose proof (usize_pos U) ]; lia. }
  split.
  - intros Γ H Hn HH ch k.
    destruct H as [pq | x | H y | H N | U]; cbn [msize] in Hn.
    + destruct (wf_path_module _ _ _ _ HH) as [r0 Hq].
      constructor; intros U r Hm.
      rewrite (gc_module_below _ _ _ _ Hg1 Hg2 Hs _ _ Hq) in Hm.
      exact (Ha _ _ _ Hm r k).
    + constructor; intros U0 Γ' Hf.
      pose proof (ctx_find_slot_size _ _ _ _ Hf).
      destruct (ctx_find_slot_split _ _ _ _ Hf) as [Ψ EΓ].
      pose proof (presup_modexp_eq_ctx HH) as HΓ; rewrite EΓ in HΓ.
      apply ctx_app_wf_right in HΓ.
      apply IHu; [ lia | exact (proj2 (ctx_decomp_mod HΓ)) ].
    + destruct (modexp_parts_of_wf _ _ _ _ HH) as [HH' _].
      constructor; apply IHm; [ lia | exact HH' ].
    + destruct (modexp_parts_of_wf _ _ _ _ HH) as [HH' _].
      constructor; apply IHm; [ lia | exact HH' ].
    + pose proof (modexp_parts_of_wf _ _ _ _ HH) as HU; cbn in HU.
      constructor; apply IHu; [ lia | exact HU ].
  - intros Γ U Hn HU ch k.
    destruct U as [Δ [Φ | E]]; rewrite usize_mk in Hn; cbn [dsize] in Hn.
    + destruct (unit_parts_of_wf _ _ _ _ HU) as (HC & _ & _).
      destruct ch as [| y ch]; [ constructor |].
      constructor; intros Φ' Uy Hp.
      pose proof (gsize_prefix _ _ _ Hp) as Hsz; cbn in Hsz.
      apply IHu; [| exact (body_prefix_mod_wf _ _ _ _ _ _ _ _ HC Hp) ].
      rewrite !csize_app, csize_body_ctx; lia.
    + destruct (unit_parts_of_wf _ _ _ _ HU) as (_ & _ & HE).
      constructor; apply IHm; [ rewrite csize_app; lia | exact HE ].
Qed.

(** Every alias of a well-formed global context has an order, wherever the
    context embeds: it names only modules that were there before it. *)
Definition alias_V (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (E : gentry) : Prop :=
  match E with
  | ge_mod U => forall r k, umt_order Θ2 Ξ2 nil U r k
  | _ => True
  end.

Definition alias_F (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) : Prop := True.

Lemma alias_V_alias : forall Θ Ξ Δ E Θ2 Ξ2,
    tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    GoodV alias_V alias_F Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    alias_V Θ2 Ξ2 (gs_tele Ξ) (ge_mod (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))).
Proof.
  intros * _ _ HE HG He r k; cbn.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HE)) as Hg.
  assert (Ha : aliases_ordered Θ Ξ Θ2 Ξ2).
  { intros p U r0 Hm r' k'.
    destruct (good_alias _ _ _ _ _ _ _ _ _ HG He Hm) as [T HV]; exact (HV r' k'). }
  constructor; rewrite app_nil_r.
  eapply (proj1 (mt_order_exists _ _ _ _ Hg (em_wf _ _ _ _ He) (em_res _ _ _ _ He) Ha _)); [ reflexivity | exact HE ].
Qed.

Theorem gctx_aliases_ordered : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> aliases_ordered Θ Ξ Θ Ξ.
Proof.
  intros * Hg p U r Hm r' k.
  pose proof (global_valid alias_V alias_F
                ltac:(intros; exact I) ltac:(intros; exact I)
                alias_V_alias ltac:(intros; exact I) _ _ Hg) as HG.
  destruct (good_alias _ _ _ _ _ _ _ _ _ HG (Emb_refl _ _ Hg) Hm) as [T HV]; exact (HV r' k).
Qed.

Corollary mt_order_of_wf : forall Θ Ξ Γ H, ⊢g Θ ⍮ Ξ -> wf_modexp_eq Θ Ξ Γ H H ->
    forall ch k, mt_order Θ Ξ Γ H ch k.
Proof.
  intros * Hg HH.
  eapply (proj1 (mt_order_exists _ _ _ _ Hg Hg (gc_sub_refl _ _) (gctx_aliases_ordered _ _ Hg) _));
    [ reflexivity | exact HH ].
Qed.

Corollary mt_order_path : forall Θ Ξ Γ pq ch k, ⊢g Θ ⍮ Ξ -> mt_order Θ Ξ Γ (me_path pq) ch k.
Proof.
  intros * Hg; constructor; intros U r Hm; exact (gctx_aliases_ordered _ _ Hg _ _ _ Hm r k).
Qed.

Lemma gctx_closed_of_wf : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> gctx_closed Θ Ξ.
Proof. intros * Hg; eapply wf_gctx_closed; constructor; exact Hg. Qed.
