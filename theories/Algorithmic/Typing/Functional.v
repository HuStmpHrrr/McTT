(** * Inference Is Functional

    A term infers at most one type.  The proof reads only the syntax:
    normalisation is functional, and so is what a module expression
    denotes; so it stands below the metatheory, where the static semantics
    of commands, whose access fill infers types, can use it. *)

From Mctt Require Import LibTactics.
From Mctt.Algorithmic.Typing Require Import Definitions.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Corollaries.
From Mctt.Core.Syntactic.System.Global Require Import Paths.
Import Domain_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** A term infers one type.  A member's is read off what its module
    denotes, which of a well-formed global context is one description
    ([mdenote_functional_all]). *)
Lemma functional_alg_type_infer : forall {Γ A A' M},
    ⊢ᵍ gc_deps ⍮ gc_stack ->
    Γ ⊢a M ⟹ A ->
    Γ ⊢a M ⟹ A' ->
    A = A'.
Proof.
  intros * Hg HM1 HM2. gen A'.
  induction HM1; intros;
    inversion_clear HM2;
    (** The eliminator: the scrutinee infers one type, so the member's
        non-uniform parameters and the block are the same. *)
    try solve [ match goal with
      | IH : forall A'0, ?G ⊢a ?M ⟹ A'0 -> nf_indty _ _ _ = A'0, H : ?G ⊢a ?M ⟹ nf_indty _ _ _ |- _ =>
          specialize (IH _ H); injection IH; clear H; intros; subst;
          repeat match goal with H1 : List.nth_error ?B ?m = Some ?b1, H2 : List.nth_error ?B ?m = Some ?b2 |- _ =>
            assert_fails constr_eq b1 b2; assert (b1 = b2) as <- by congruence; clear H2 end;
          repeat match goal with H1 : ind_lookup _ _ ?p = Some ?D1, H2 : ind_lookup _ _ ?p = Some ?D2 |- _ =>
            assert_fails constr_eq D1 D2; assert (D1 = D2) as <- by congruence; clear H2 end;
          functional_nbe_rewrite_clear; reflexivity
      end ];
    functional_nbe_rewrite_clear;
    f_equiv;
    try reflexivity;
    intuition.
  (** A member: the same description, so the same type. *)
  all: try solve [ match goal with
    | H1 : mdenote _ _ ?G ?H ?R1, H2 : mdenote _ _ ?G ?H ?R2 |- _ =>
        pose proof (proj1 (mdenote_functional_all _ _ Hg) _ _ _ H1 _ H2) as <-;
        match goal with E1 : ds_ty _ _ R1 = Some ?A1, E2 : ds_ty _ _ R1 = Some ?A2 |- _ =>
          assert (A1 = A2) as <- by congruence end;
        functional_nbe_rewrite_clear; reflexivity end ].
  (** The level operations: the arguments infer the same types of levels. *)
  all: try solve [ repeat match goal with
    | IH : forall A'0, ?G ⊢a ?M ⟹ A'0 -> Levelⁿ@?k = A'0, H : ?G ⊢a ?M ⟹ Levelⁿ@?k' |- _ =>
        specialize (IH _ H); injection IH as ->; clear H end; reflexivity ].
  (** The type former and a constructor: the declaration and the member
      are looked up once, and the types are normal forms of the same
      types. *)
  all: try solve [
    repeat match goal with H1 : ind_lookup _ _ ?p = Some ?D1, H2 : ind_lookup _ _ ?p = Some ?D2 |- _ =>
      assert_fails constr_eq D1 D2; assert (D1 = D2) as <- by congruence; clear H2 end;
    repeat match goal with H1 : ind_member ?D ?k = Some ?M1, H2 : ind_member ?D ?k = Some ?M2 |- _ =>
      assert_fails constr_eq M1 M2; assert (M1 = M2) as <- by congruence; clear H2 end;
    repeat match goal with H1 : ind_con ?D ?c = Some ?g1, H2 : ind_con ?D ?c = Some ?g2 |- _ =>
      assert (g1 = g2) as <- by congruence; clear H2 end;
    functional_nbe_rewrite_clear; reflexivity ].
  (** A record's type former, a tuple and a projection: the record is
      looked up once; a projection's element infers one record type, the
      field is found once, and the type is the normal form of the same
      type. *)
  all: try solve [
    try match goal with
      | IH : forall A'0, ?G ⊢a ?M ⟹ A'0 -> nf_record _ _ = A'0, H : ?G ⊢a ?M ⟹ nf_record _ _ |- _ =>
          specialize (IH _ H); injection IH; clear H; intros; subst
    end;
    repeat match goal with H1 : record_lookup _ _ ?p = Some ?R1, H2 : record_lookup _ _ ?p = Some ?R2 |- _ =>
      assert_fails constr_eq R1 R2; assert (R1 = R2) as <- by congruence; clear H2 end;
    repeat match goal with H1 : field_index ?fl ?f = Some ?k1, H2 : field_index ?fl ?f = Some ?k2 |- _ =>
      assert_fails constr_eq k1 k2; assert (k1 = k2) as <- by congruence; clear H2 end;
    repeat match goal with H1 : List.nth_error ?fl ?k = Some (?f, ?U1), H2 : List.nth_error ?fl ?k = Some (?f, ?U2) |- _ =>
      assert_fails constr_eq U1 U2; assert (U1 = U2) as <- by congruence; clear H2 end;
    functional_nbe_rewrite_clear; reflexivity ].
  (** A module [let]: the same type of the rest. *)
  4:{ assert (C = C0) as <- by eauto. functional_nbe_rewrite_clear. reflexivity. }
  (** [Π]: the two parts infer the same universes, so the two universes the
      side conditions normalise are the same. *)
  - assert (UA = UA0) as <- by intuition.
    assert (UB = UB0) as <- by intuition.
    functional_nbe_rewrite_clear.
    assert (u = u0) as <- by (eapply is_univ_nf_functional; eassumption).
    assert (v = v0) as <- by (eapply is_univ_nf_functional; eassumption).
    functional_nbe_rewrite_clear.
    reflexivity.
  - assert (Πⁿ A B = Πⁿ A0 B0) as [= <- <-] by intuition.
    functional_nbe_rewrite_clear.
    reflexivity.
  (** [let]: both derivations read the same annotation; without one, the
      body's type, then the type of the rest. *)
  - destruct H as [-> | ->]; destruct H8 as [[=] | [= <-]]; simpl_let_guards.
    + assert (W = W0) as <- by eauto. assert (C = C0) as <- by eauto.
      functional_nbe_rewrite_clear. reflexivity.
    + assert (C = C0) as <- by eauto.
      functional_nbe_rewrite_clear. reflexivity.
  - assert (A = A0) as <- by mauto using ctx_lookup_functional.
    functional_nbe_rewrite_clear.
    reflexivity.
Qed.

End Fixed_GCtx.
