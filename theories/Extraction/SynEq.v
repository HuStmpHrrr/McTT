(** * Syntactic Equality of Terms

    A boolean test of syntactic equality, sound for [=].  The checker uses
    it to recognize a type it has computed before, so as not to check that
    type again. *)

From Stdlib Require Import Bool List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax GlobalCtx.
Import Syntax_Notations.

Definition opt_beq {A} (f : A -> A -> bool) (o1 o2 : option A) : bool :=
  match o1, o2 with
  | Some a1, Some a2 => f a1 a2
  | None, None => true
  | _, _ => false
  end.

Definition list_beq {A} (f : A -> A -> bool) :=
  fix go (l1 l2 : list A) : bool :=
    match l1, l2 with
    | nil, nil => true
    | a1 :: l1', a2 :: l2' => f a1 a2 && go l1' l2'
    | _, _ => false
    end.

Definition iitem_beq (i1 i2 : iitem) : bool :=
  let '(n1, d1, p1) := i1 in
  let '(n2, d2, p2) := i2 in
  String.eqb n1 n2 && String.eqb d1 d2 && Bool.eqb p1 p2.

Fixpoint exp_beq (M1 M2 : exp) {struct M1} : bool :=
  match M1, M2 with
  | a_typ i, a_typ j => Nat.eqb i j
  | a_nat, a_nat | a_zero, a_zero | a_True, a_True | a_true, a_true | a_False, a_False => true
  | a_succ M, a_succ N => exp_beq M N
  | a_natrec A MZ MS M, a_natrec A' MZ' MS' M' =>
      exp_beq A A' && exp_beq MZ MZ' && exp_beq MS MS' && exp_beq M M'
  | a_exfalso A M, a_exfalso A' M' => exp_beq A A' && exp_beq M M'
  | a_pi A B, a_pi A' B' => exp_beq A A' && exp_beq B B'
  | a_fn A M, a_fn A' M' => exp_beq A A' && exp_beq M M'
  | a_app M N, a_app M' N' => exp_beq M M' && exp_beq N N'
  | a_var x, a_var y => Nat.eqb x y
  | a_let b B, a_let b' B' => bnd_beq b b' && exp_beq B B'
  | a_mem H x, a_mem H' y => modexp_beq H H' && String.eqb x y
  | a_const c1, a_const c2 => qname_beq c1 c2
  | _, _ => false
  end
with modexp_beq (H1 H2 : modexp) {struct H1} : bool :=
  match H1, H2 with
  | me_unit p1, me_unit p2 => path_beq p1 p2
  | me_var x, me_var y => Nat.eqb x y
  | me_mem H y, me_mem H' y' => modexp_beq H H' && String.eqb y y'
  | me_app H N, me_app H' N' => modexp_beq H H' && exp_beq N N'
  | me_lit U, me_lit U' => gunit_beq U U'
  | _, _ => false
  end
with bnd_beq (b1 b2 : bnd) {struct b1} : bool :=
  match b1, b2 with
  | b_def oA M, b_def oA' M' => opt_beq exp_beq oA oA' && exp_beq M M'
  | b_mod U, b_mod U' => gunit_beq U U'
  | _, _ => false
  end
with gunit_beq (U1 U2 : gunit) {struct U1} : bool :=
  match U1, U2 with
  | gu_mk Δ D, gu_mk Δ' D' => list_beq centry_beq Δ Δ' && moddef_beq D D'
  end
with moddef_beq (D1 D2 : moddef) {struct D1} : bool :=
  match D1, D2 with
  | md_body Φ, md_body Φ' => gmod_beq Φ Φ'
  | md_alias E, md_alias E' => modexp_beq E E'
  | _, _ => false
  end
with gmod_beq (Φ1 Φ2 : gmod) {struct Φ1} : bool :=
  match Φ1, Φ2 with
  | gm_nil, gm_nil => true
  | gm_ext Φ x E, gm_ext Φ' x' E' => gmod_beq Φ Φ' && String.eqb x x' && gentry_beq E E'
  | gm_open Φ H oz its, gm_open Φ' H' oz' its' =>
      gmod_beq Φ Φ' && modexp_beq H H' && opt_beq String.eqb oz oz' && list_beq iitem_beq its its'
  | _, _ => false
  end
with gentry_beq (E1 E2 : gentry) {struct E1} : bool :=
  match E1, E2 with
  | ge_def pv A oM, ge_def pv' A' oM' => Bool.eqb pv pv' && exp_beq A A' && opt_beq exp_beq oM oM'
  | ge_mod pv U, ge_mod pv' U' => Bool.eqb pv pv' && gunit_beq U U'
  | _, _ => false
  end
with centry_beq (e1 e2 : centry) {struct e1} : bool :=
  match e1, e2 with
  | ce_ass A, ce_ass A' => exp_beq A A'
  | ce_def A M, ce_def A' M' => exp_beq A A' && exp_beq M M'
  | ce_mod U, ce_mod U' => gunit_beq U U'
  | _, _ => false
  end.

Lemma opt_beq_sound : forall {A} (f : A -> A -> bool) o1 o2,
    (forall a1, o1 = Some a1 -> forall a2, f a1 a2 = true -> a1 = a2) -> opt_beq f o1 o2 = true -> o1 = o2.
Proof. intros A f [a1 |] [a2 |] Hf H; cbn in H; try discriminate; [ f_equal; eauto | reflexivity ]. Qed.

Lemma list_beq_sound : forall {A} (P : A -> Prop) (f : A -> A -> bool) l1 l2,
    List.Forall (fun a1 => forall a2, f a1 a2 = true -> a1 = a2) l1 -> list_beq f l1 l2 = true -> l1 = l2.
Proof.
  intros A P f; induction l1 as [| a1 l1 IH]; intros [| a2 l2] Hf H; cbn in H; try discriminate; [ reflexivity |].
  inversion Hf; subst; apply andb_true_iff in H as [Hx Hy]; f_equal; auto.
Qed.

Lemma iitem_beq_sound : forall i1 i2, iitem_beq i1 i2 = true -> i1 = i2.
Proof.
  intros [[n1 d1] p1] [[n2 d2] p2] H; cbn in H.
  apply andb_true_iff in H as [H Hc]; apply andb_true_iff in H as [Ha Hb].
  apply String.eqb_eq in Ha, Hb; apply Bool.eqb_prop in Hc; subst; reflexivity.
Qed.

Ltac beq_split :=
  repeat match goal with
    | H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?]
    | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
    | H : String.eqb _ _ = true |- _ => apply String.eqb_eq in H
    | H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
    | H : path_beq _ _ = true |- _ => apply path_beq_true in H
    | H : qname_beq _ _ = true |- _ => apply qname_beq_true in H
    end.

Lemma syn_beq_sound :
  (forall M1 M2, exp_beq M1 M2 = true -> M1 = M2) /\
  (forall H1 H2, modexp_beq H1 H2 = true -> H1 = H2) /\
  (forall b1 b2, bnd_beq b1 b2 = true -> b1 = b2) /\
  (forall U1 U2, gunit_beq U1 U2 = true -> U1 = U2) /\
  (forall D1 D2, moddef_beq D1 D2 = true -> D1 = D2) /\
  (forall Φ1 Φ2, gmod_beq Φ1 Φ2 = true -> Φ1 = Φ2) /\
  (forall E1 E2, gentry_beq E1 E2 = true -> E1 = E2) /\
  (forall e1 e2, centry_beq e1 e2 = true -> e1 = e2).
Proof.
  apply (syn_mut_ind
           (fun M1 => forall M2, exp_beq M1 M2 = true -> M1 = M2)
           (fun H1 => forall H2, modexp_beq H1 H2 = true -> H1 = H2)
           (fun b1 => forall b2, bnd_beq b1 b2 = true -> b1 = b2)
           (fun U1 => forall U2, gunit_beq U1 U2 = true -> U1 = U2)
           (fun D1 => forall D2, moddef_beq D1 D2 = true -> D1 = D2)
           (fun Φ1 => forall Φ2, gmod_beq Φ1 Φ2 = true -> Φ1 = Φ2)
           (fun E1 => forall E2, gentry_beq E1 E2 = true -> E1 = E2)
           (fun e1 => forall e2, centry_beq e1 e2 = true -> e1 = e2));
    intros; match goal with H : _ = true |- _ => revert H end;
    match goal with |- ?l _ ?r = true -> _ => destruct r end; cbn; intros Hb;
    try discriminate; beq_split; subst; try reflexivity;
    repeat match goal with
      | IH : forall _, ?f ?a _ = true -> ?a = _, Hf : ?f ?a _ = true |- _ => apply IH in Hf; subst
      end;
    try reflexivity.
  - (* an optional annotation *)
    f_equal; eapply opt_beq_sound; [| eassumption ]; intros ? -> ?; eauto.
  - (* a telescope *)
    f_equal; eapply (list_beq_sound (fun _ => True)); eassumption.
  - (* the items of an open *)
    f_equal; [ eapply opt_beq_sound; [| eassumption ]; intros ? -> ? ?; apply String.eqb_eq; assumption |].
    eapply (list_beq_sound (fun _ => True)); [| eassumption ].
    apply Forall_forall; intros; apply iitem_beq_sound; assumption.
  - (* an optional body *)
    f_equal; eapply opt_beq_sound; [| eassumption ]; intros ? -> ?; eauto.
Qed.

Corollary exp_beq_sound : forall M1 M2, exp_beq M1 M2 = true -> M1 = M2.
Proof. exact (proj1 syn_beq_sound). Qed.

(** As a decision of [=], up to completeness: [false] says nothing. *)
Definition exp_eq_test (M1 M2 : exp) : {M1 = M2} + {True} :=
  match exp_beq M1 M2 as b return exp_beq M1 M2 = b -> {M1 = M2} + {True} with
  | true => fun E => left (exp_beq_sound _ _ E)
  | false => fun _ => right I
  end eq_refl.
