From Stdlib Require Import Lia PeanoNat Relation_Definitions RelationClasses Wf_nat.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export PER.
From Mctt.Core.Syntactic Require Export SystemOpt.
From Mctt.Core.Soundness.Weakening Require Export Definitions.

Import Domain_Notations Wk_Notations Fixed_Notations.

Global Open Scope predicate_scope.

(** The rewrite database of [simp glu_univ_elem]. *)
Create Rewrite HintDb glu_univ_elem.

Generalizable All Variables.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Notation "'glu_typ_pred_args'" := (Tcons ctx (Tcons typ Tnil)).
Notation "'glu_typ_pred'" := (predicate glu_typ_pred_args).
Notation "'glu_typ_pred_equivalence'" := (@predicate_equivalence glu_typ_pred_args) (only parsing).
(** This type annotation distinguishes this notation from others. *)
Notation "Γ ⊢ A ® R" := ((R Γ A : (Prop : Type)) : (Prop : (Type : Type))) (at level 70, A at level 69, R constr).

Notation "'glu_exp_pred_args'" := (Tcons ctx (Tcons typ (Tcons exp (Tcons domain Tnil)))).
Notation "'glu_exp_pred'" := (predicate glu_exp_pred_args).
Notation "'glu_exp_pred_equivalence'" := (@predicate_equivalence glu_exp_pred_args) (only parsing).
Notation "Γ ⊢ M : A ® m ∈ R" := (R Γ A M m : (Prop : (Type : Type))) (at level 70, M at level 69, m at level 69, R constr).

Notation "'glu_sub_pred_args'" := (Tcons ctx (Tcons sub (Tcons env Tnil))).
Notation "'glu_sub_pred'" := (predicate glu_sub_pred_args).
Notation "'glu_sub_pred_equivalence'" := (@predicate_equivalence glu_sub_pred_args) (only parsing).
Notation "Γ ⊢s σ ® ρ ∈ R" := ((R Γ σ ρ : Prop) : (Prop : (Type : Type))) (at level 70, σ at level 69, ρ at level 69, R constr).

Notation "'DG' a ∈ R ↘ P ↘ El" := (R P El a : ((Prop : Type) : (Type : Type))) (at level 70, a at level 69, R constr, P constr, El constr).
Notation "'EG' A ∈ R ↘ Sb " := (R Sb A : ((Prop : (Type : Type)) : (Type : Type))) (at level 70, A at level 69, R constr, Sb constr).

Inductive glu_nat : ctx -> exp -> domain -> Prop :=
| glu_nat_zero :
  `{ Γ ⊢ M ≈ zero : ℕ ->
     glu_nat Γ M zeroᵈ }
| glu_nat_succ :
  `{ Γ ⊢ M ≈ succ M' : ℕ ->
     glu_nat Γ M' m' ->
     glu_nat Γ M succᵈ m' }
| glu_nat_neut :
  `{ per_bot m m ->
     (forall {Δ φ M'}, Δ ⊢k φ : Γ -> Rne m in length Δ ↘ M' -> Δ ⊢ M[φ]ʷ ≈ M' : ℕ) ->
     glu_nat Γ M ⇑ a m }.

Hint Constructors glu_nat : mctt.

Definition nat_glu_typ_pred i : glu_typ_pred := fun Γ A => Γ ⊢ A ≈ ℕ : Type@i.
#[global] Arguments nat_glu_typ_pred i Γ A/.

Definition nat_glu_exp_pred i : glu_exp_pred := fun Γ A M m => Γ ⊢ A ® nat_glu_typ_pred i /\ glu_nat Γ M m.
#[global] Arguments nat_glu_exp_pred i Γ A M m/.

Definition True_glu_typ_pred i : glu_typ_pred := fun Γ A => Γ ⊢ A ≈ ⊤ : Type@i.
#[global] Arguments True_glu_typ_pred i Γ A/.

(** A term of type [⊤] is glued to every value: by η, all its terms are
    equal to [⋆], which is what every value reads back as. *)
Definition True_glu_exp_pred i : glu_exp_pred := fun Γ A M m => Γ ⊢ A ® True_glu_typ_pred i /\ Γ ⊢ M : ⊤.
#[global] Arguments True_glu_exp_pred i Γ A M m/.

(** [⊥] has no canonical values, so its gluing is that of the neutrals of
    [glu_nat]. *)
Inductive glu_False : ctx -> exp -> domain -> Prop :=
| glu_False_neut :
  `{ per_bot m m ->
     (forall {Δ φ M'}, Δ ⊢k φ : Γ -> Rne m in length Δ ↘ M' -> Δ ⊢ M[φ]ʷ ≈ M' : ⊥) ->
     glu_False Γ M ⇑ a m }.

Hint Constructors glu_False : mctt.

Definition False_glu_typ_pred i : glu_typ_pred := fun Γ A => Γ ⊢ A ≈ ⊥ : Type@i.
#[global] Arguments False_glu_typ_pred i Γ A/.

Definition False_glu_exp_pred i : glu_exp_pred := fun Γ A M m => Γ ⊢ A ® False_glu_typ_pred i /\ glu_False Γ M m.
#[global] Arguments False_glu_exp_pred i Γ A M m/.

Definition neut_glu_typ_pred i a : glu_typ_pred :=
  fun Γ A => Γ ⊢ A : Type@i /\
            (forall Δ φ A', Δ ⊢k φ : Γ -> Rne a in length Δ ↘ A' -> Δ ⊢ A[φ]ʷ ≈ A' : Type@i).
#[global] Arguments neut_glu_typ_pred i a Γ A/.

Variant neut_glu_exp_pred i a : glu_exp_pred :=
| mk_neut_glu_exp_pred :
  `{ Γ ⊢ A ® neut_glu_typ_pred i a ->
     Γ ⊢ M : A ->
     Dom m ≈ m ∈ per_bot ->
     (forall Δ φ M', Δ ⊢k φ : Γ ->
                   Rne m in length Δ ↘ M' ->
                   Δ ⊢ M[φ]ʷ ≈ M' : A[φ]ʷ) ->
     Γ ⊢ M : A ® ⇑ b m ∈ neut_glu_exp_pred i a }.

Variant pi_glu_typ_pred i
  (IR : relation domain)
  (IP : glu_typ_pred)
  (IEl : glu_exp_pred)
  (OP : forall c (equiv_c : Dom c ≈ c ∈ IR), glu_typ_pred) : glu_typ_pred :=
| mk_pi_glu_typ_pred :
  `{ Γ ⊢ A ≈ Π IT OT : Type@i ->
     Γ ⊢ IT : Type@i ->
     Γ ▹ IT ⊢ OT : Type@i ->
     (forall Δ φ, Δ ⊢k φ : Γ -> Δ ⊢ IT[φ]ʷ ® IP) ->
     (forall Δ φ M m,
         Δ ⊢k φ : Γ ->
         Δ ⊢ M : IT[φ]ʷ ® m ∈ IEl ->
         forall (equiv_m : Dom m ≈ m ∈ IR),
           Δ ⊢ OT[(ι φ),,M] ® OP _ equiv_m) ->
     Γ ⊢ A ® pi_glu_typ_pred i IR IP IEl OP }.

Variant pi_glu_exp_pred i
  (IR : relation domain)
  (IP : glu_typ_pred)
  (IEl : glu_exp_pred)
  (elem_rel : relation domain)
  (OEl : forall c (equiv_c : Dom c ≈ c ∈ IR), glu_exp_pred): glu_exp_pred :=
| mk_pi_glu_exp_pred :
  `{ Γ ⊢ M : A ->
     Dom m ≈ m ∈ elem_rel ->
     Γ ⊢ A ≈ Π IT OT : Type@i ->
     Γ ⊢ IT : Type@i ->
     Γ ▹ IT ⊢ OT : Type@i ->
     (forall Δ φ, Δ ⊢k φ : Γ -> Δ ⊢ IT[φ]ʷ ® IP) ->
     (forall Δ φ N n,
         Δ ⊢k φ : Γ ->
         Δ ⊢ N : IT[φ]ʷ ® n ∈ IEl ->
         forall (equiv_n : Dom n ≈ n ∈ IR),
         exists mn, $| m & n |↘ mn /\ Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® mn ∈ OEl _ equiv_n) ->
     Γ ⊢ M : A ® m ∈ pi_glu_exp_pred i IR IP IEl elem_rel OEl }.

Hint Constructors neut_glu_exp_pred pi_glu_typ_pred pi_glu_exp_pred : mctt.

Definition univ_glu_typ_pred j i : glu_typ_pred := fun Γ A => Γ ⊢ A ≈ Type@j :  Type@i.
#[global] Arguments univ_glu_typ_pred j i Γ A/.
Transparent univ_glu_typ_pred.

Section Gluing.
  Variable
    (i : nat)
      (glu_univ_typ_rec : nat -> domain -> glu_typ_pred).

  (** [univ_typ] is the entry [glu_univ_typ_rec j] of the family, passed
      applied so that [glu_univ_below_spec] can restate it. *)
  Definition univ_glu_exp_pred' j (univ_typ : domain -> glu_typ_pred) : glu_exp_pred :=
    fun Γ A M m =>
      Γ ⊢ M : A /\
        Γ ⊢ A ≈ Type@j : Type@i /\
        Γ ⊢ M ® univ_typ m.

#[global] Arguments univ_glu_exp_pred' j univ_typ Γ A M m/.

  Inductive glu_univ_elem_core : glu_typ_pred -> glu_exp_pred -> domain -> Prop :=
  | glu_univ_elem_core_univ :
    `{ forall typ_rel
         el_rel
         (lt_j_i : j < i),
          typ_rel <∙> univ_glu_typ_pred j i ->
          el_rel <∙> univ_glu_exp_pred' j (glu_univ_typ_rec j) ->
          DG 𝕌@j ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  | glu_univ_elem_core_nat :
    `{ forall typ_rel el_rel,
          typ_rel <∙> nat_glu_typ_pred i ->
          el_rel <∙> nat_glu_exp_pred i ->
          DG ℕᵈ ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  | glu_univ_elem_core_True :
    `{ forall typ_rel el_rel,
          typ_rel <∙> True_glu_typ_pred i ->
          el_rel <∙> True_glu_exp_pred i ->
          DG ⊤ᵈ ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  | glu_univ_elem_core_False :
    `{ forall typ_rel el_rel,
          typ_rel <∙> False_glu_typ_pred i ->
          el_rel <∙> False_glu_exp_pred i ->
          DG ⊥ᵈ ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  | glu_univ_elem_core_pi :
    `{ forall (in_rel : relation domain)
         IP IEl
         (OP : forall c (equiv_c_c : Dom c ≈ c ∈ in_rel), glu_typ_pred)
         (OEl : forall c (equiv_c_c : Dom c ≈ c ∈ in_rel), glu_exp_pred)
         typ_rel el_rel
         (elem_rel : relation domain),
          DG a ∈ glu_univ_elem_core ↘ IP ↘ IEl ->
          DF a ≈ a ∈ per_univ_elem i ↘ in_rel ->
          (forall {c} (equiv_c : Dom c ≈ c ∈ in_rel) b,
              ⟦ B ⟧ ρ ↦ c ↘ b ->
              DG b ∈ glu_univ_elem_core ↘ OP _ equiv_c ↘ OEl _ equiv_c) ->
          DF Πᵈ a ρ B ≈ Πᵈ a ρ B ∈ per_univ_elem i ↘ elem_rel ->
          typ_rel <∙> pi_glu_typ_pred i in_rel IP IEl OP ->
          el_rel <∙> pi_glu_exp_pred i in_rel IP IEl elem_rel OEl ->
          DG Πᵈ a ρ B ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  | glu_univ_elem_core_neut :
    `{ forall typ_rel el_rel,
          Dom b ≈ b ∈ per_bot ->
          typ_rel <∙> neut_glu_typ_pred i b ->
          el_rel <∙> neut_glu_exp_pred i b ->
          DG ⇑ a b ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }.
End Gluing.

Hint Constructors glu_univ_elem_core : mctt.

(** The universes below level [i], indexed by their level, as for
    [per_univ_below]: the recursion is structural, so [glu_univ_elem] unfolds
    by computation. *)
Fixpoint glu_univ_below (i : nat) : nat -> domain -> glu_typ_pred :=
  match i with
  | 0 => fun _ _ _ _ => False
  | S i' => fun j =>
      if Nat.eqb j i'
      then fun a Γ A => exists P El, DG a ∈ glu_univ_elem_core i' (glu_univ_below i') ↘ P ↘ El /\ Γ ⊢ A ® P
      else glu_univ_below i' j
  end.

Definition glu_univ_elem (i : nat) : glu_typ_pred -> glu_exp_pred -> domain -> Prop :=
  glu_univ_elem_core i (glu_univ_below i).
#[global] Arguments glu_univ_elem : simpl never.

Lemma glu_univ_elem_equation_1 : forall i,
    glu_univ_elem i = glu_univ_elem_core i (glu_univ_below i).
Proof. reflexivity. Qed.

Hint Rewrite glu_univ_elem_equation_1 : glu_univ_elem.

Lemma glu_univ_below_spec : forall i j,
    j < i ->
    glu_univ_below i j = fun a Γ A => exists P El, DG a ∈ glu_univ_elem j ↘ P ↘ El /\ Γ ⊢ A ® P.
Proof.
  induction i as [| i IHi]; intros j Hlt; [lia |].
  simpl.
  destruct (Nat.eqb_spec j i) as [-> | Hneq]; [reflexivity |].
  apply IHi; lia.
Qed.

Definition glu_univ_typ (i : nat) (a : domain) : glu_typ_pred :=
  fun Γ A => exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El /\ Γ ⊢ A ® P.
#[global] Arguments glu_univ_typ i a Γ A/.

Definition univ_glu_exp_pred j i : glu_exp_pred :=
    fun Γ A M m =>
      Γ ⊢ M : A /\ Γ ⊢ A ≈ Type@j : Type@i /\
        Γ ⊢ M ® glu_univ_typ j m.
#[global] Arguments univ_glu_exp_pred j i Γ A M m/.

Section GluingInduction.
  Hypothesis
    (motive : nat -> glu_typ_pred -> glu_exp_pred -> domain -> Prop)

      (case_univ :
        forall i j
          (P : glu_typ_pred) (El : glu_exp_pred) (lt_j_i : j < i),
          (forall P' El' a, DG a ∈ glu_univ_elem j ↘ P' ↘ El' -> motive j P' El' a) ->
          P <∙> univ_glu_typ_pred j i ->
          El <∙> univ_glu_exp_pred j i ->
          motive i P El 𝕌@j)

      (case_nat :
        forall i (P : glu_typ_pred) (El : glu_exp_pred),
          P <∙> nat_glu_typ_pred i ->
          El <∙> nat_glu_exp_pred i ->
          motive i P El ℕᵈ)

      (case_True :
        forall i (P : glu_typ_pred) (El : glu_exp_pred),
          P <∙> True_glu_typ_pred i ->
          El <∙> True_glu_exp_pred i ->
          motive i P El ⊤ᵈ)

      (case_False :
        forall i (P : glu_typ_pred) (El : glu_exp_pred),
          P <∙> False_glu_typ_pred i ->
          El <∙> False_glu_exp_pred i ->
          motive i P El ⊥ᵈ)

      (case_pi :
        forall i a B (ρ : env) (in_rel : relation domain) (IP : glu_typ_pred)
          (IEl : glu_exp_pred) (OP : forall c : domain, Dom c ≈ c ∈ in_rel -> glu_typ_pred)
          (OEl : forall c : domain, Dom c ≈ c ∈ in_rel -> glu_exp_pred) (P : glu_typ_pred) (El : glu_exp_pred)
          (elem_rel : relation domain),
          DG a ∈ glu_univ_elem i ↘ IP ↘ IEl ->
          motive i IP IEl a ->
          DF a ≈ a ∈ per_univ_elem i ↘ in_rel ->
          (forall (c : domain) (equiv_c : Dom c ≈ c ∈ in_rel) (b : domain),
              ⟦ B ⟧ ρ ↦ c ↘ b ->
              DG b ∈ glu_univ_elem i ↘ OP c equiv_c ↘ OEl c equiv_c) ->
          (forall (c : domain) (equiv_c : Dom c ≈ c ∈ in_rel) (b : domain),
              ⟦ B ⟧ ρ ↦ c ↘ b ->
              motive i (OP c equiv_c) (OEl c equiv_c) b) ->
          DF Πᵈ a ρ B ≈ Πᵈ a ρ B ∈ per_univ_elem i ↘ elem_rel ->
          P <∙> pi_glu_typ_pred i in_rel IP IEl OP ->
          El <∙> pi_glu_exp_pred i in_rel IP IEl elem_rel OEl ->
          motive i P El Πᵈ a ρ B)

      (case_neut :
        forall i b a
          (P : glu_typ_pred)
          (El : glu_exp_pred),
          Dom b ≈ b ∈ per_bot ->
          P <∙> neut_glu_typ_pred i b ->
          El <∙> neut_glu_exp_pred i b ->
          motive i P El ⇑ a b)
  .

  Lemma glu_univ_elem_ind i P El a
    (H : glu_univ_elem i P El a) : motive i P El a.
  Proof.
    revert P El a H.
    induction i as [i IHi] using lt_wf_ind.
    intros P El a H.
    induction H.
    - rewrite glu_univ_below_spec in * by assumption.
      eapply case_univ; eauto.
    - eapply case_nat; eassumption.
    - eapply case_True; eassumption.
    - eapply case_False; eassumption.
    - eapply case_pi; eassumption.
    - eapply case_neut; eassumption.
  Qed.
End GluingInduction.

Variant glu_elem_bot i a Γ A M m : Prop :=
| glu_elem_bot_make : forall P El,
    Γ ⊢ M : A ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Γ ⊢ A ® P ->
    Dom m ≈ m ∈ per_bot ->
    (forall Δ φ M', Δ ⊢k φ : Γ -> Rne m in length Δ ↘ M' -> Δ ⊢ M[φ]ʷ ≈ M' : A[φ]ʷ) ->
    Γ ⊢ M : A ® m ∈ glu_elem_bot i a.
Hint Constructors glu_elem_bot : mctt.

Variant glu_elem_top i a Γ A M m : Prop :=
| glu_elem_top_make : forall P El,
    Γ ⊢ M : A ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Γ ⊢ A ® P ->
    Dom ⇓ a m ≈ ⇓ a m ∈ per_top ->
    (forall Δ φ w, Δ ⊢k φ : Γ -> Rnf ⇓ a m in length Δ ↘ w -> Δ ⊢ M[φ]ʷ ≈ w : A[φ]ʷ) ->
    Γ ⊢ M : A ® m ∈ glu_elem_top i a.
Hint Constructors glu_elem_top : mctt.

Variant glu_typ_top i a Γ A : Prop :=
| glu_typ_top_make :
    Γ ⊢ A : Type@i ->
    Dom a ≈ a ∈ per_top_typ ->
    (forall Δ φ A', Δ ⊢k φ : Γ -> Rtyp a in length Δ ↘ A' -> Δ ⊢ A[φ]ʷ ≈ A' : Type@i) ->
    Γ ⊢ A ® glu_typ_top i a.
Hint Constructors glu_typ_top : mctt.

Variant glu_rel_typ_with_sub i Δ A σ ρ : Prop :=
| mk_glu_rel_typ_with_sub :
  `{ forall P El,
        ⟦ A ⟧ ρ ↘ a ->
        DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ ⊢ A[σ] ® P ->
        glu_rel_typ_with_sub i Δ A σ ρ }.

Variant glu_rel_exp_with_sub i Δ M A σ ρ : Prop :=
| mk_glu_rel_exp_with_sub :
  `{ forall P El,
        ⟦ A ⟧ ρ ↘ a ->
        ⟦ M ⟧ ρ ↘ m ->
        DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ ⊢ M[σ] : A[σ] ® m ∈ El ->
        glu_rel_exp_with_sub i Δ M A σ ρ }.

Definition nil_glu_sub_pred : glu_sub_pred :=
  fun Δ σ ρ => Δ ⊢s σ : ⋅.
#[global] Arguments nil_glu_sub_pred Δ σ ρ/.

(** The parameters are ordered differently from the Agda version
    so that we can return [glu_sub_pred]. *)
Variant cons_glu_sub_pred i Γ A (TSb : glu_sub_pred) : glu_sub_pred :=
| mk_cons_glu_sub_pred :
  `{ forall P El,
        Δ ⊢s σ : Γ ▹ A ->
        ⟦ A ⟧ ρ↯ ↘ a ->
        DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        (** [A[↑]ʷ[σ]] rather than [A[Wk ⨟ σ]]: it is the direct instance of
            [Γ ▹ A ⊢ #0 : A[↑]ʷ] along [σ]. *)
        Δ ⊢ #0[σ] : A[↑]ʷ[σ] ® (ρ 0) ∈ El ->
        Δ ⊢s Wk ⨟ σ ® ρ↯ ∈ TSb ->
        Δ ⊢s σ ® ρ ∈ cons_glu_sub_pred i Γ A TSb }.

(** A definition entry glues as an assumption entry whose head is also tied
    to the value of the body in the tail ([def_tie]).  The syntactic half of
    the tie is part of [Δ ⊢s σ : Γ ▸ A ≔ M]. *)
Variant cons_def_glu_sub_pred i Γ A M (TSb : glu_sub_pred) : glu_sub_pred :=
| mk_cons_def_glu_sub_pred :
  `{ forall P El,
        Δ ⊢s σ : Γ ▸ A ≔ M ->
        ⟦ A ⟧ ρ↯ ↘ a ->
        DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ ⊢ #0[σ] : A[↑]ʷ[σ] ® (ρ 0) ∈ El ->
        def_tie A M ρ ->
        Δ ⊢s Wk ⨟ σ ® ρ↯ ∈ TSb ->
        Δ ⊢s σ ® ρ ∈ cons_def_glu_sub_pred i Γ A M TSb }.

(** A module slot glues by its syntactic typing and by the tie of its value
    to the closure of its unit over the tail, which is the slot clause of the
    environment PER.  Module values themselves are not glued: their members
    are reached through δ, whose reducts are terms. *)
Variant cons_mod_glu_sub_pred Γ U (TSb : glu_sub_pred) : glu_sub_pred :=
| mk_cons_mod_glu_sub_pred :
  `{ Δ ⊢s σ : Γ ▹ₘ U ->
     per_dmod (env_mod ρ 0) (dm_local ρ↯ U nil) ->
     Δ ⊢s Wk ⨟ σ ® ρ↯ ∈ TSb ->
     Δ ⊢s σ ® ρ ∈ cons_mod_glu_sub_pred Γ U TSb }.

(** As with [wf_ctx_empty], the base case carries what the judgment is relative
    to: without it, [⊢ ⋅] would not follow ([glu_ctx_env_wf_ctx]). *)
Inductive glu_ctx_env : glu_sub_pred -> ctx -> Prop :=
| glu_ctx_env_nil :
  `{ forall Sb,
        Sb <∙> nil_glu_sub_pred ->
        ⊢g gc_deps ⍮ gc_stack ->
        EG ⋅ ∈ glu_ctx_env ↘ Sb }
| glu_ctx_env_cons :
  `{ forall i TSb Sb,
        EG Γ ∈ glu_ctx_env ↘ TSb ->
        Γ ⊢ A : Type@i ->
        (forall Δ σ ρ,
            Δ ⊢s σ ® ρ ∈ TSb ->
            glu_rel_typ_with_sub i Δ A σ ρ) ->
        Sb <∙> cons_glu_sub_pred i Γ A TSb ->
        EG Γ ▹ A ∈ glu_ctx_env ↘ Sb }
| glu_ctx_env_cons_def :
  `{ forall i TSb Sb,
        EG Γ ∈ glu_ctx_env ↘ TSb ->
        Γ ⊢ A : Type@i ->
        Γ ⊢ M : A ->
        (forall Δ σ ρ,
            Δ ⊢s σ ® ρ ∈ TSb ->
            glu_rel_typ_with_sub i Δ A σ ρ) ->
        (forall Δ σ ρ,
            Δ ⊢s σ ® ρ ∈ TSb ->
            glu_rel_exp_with_sub i Δ M A σ ρ) ->
        Sb <∙> cons_def_glu_sub_pred i Γ A M TSb ->
        EG Γ ▸ A ≔ M ∈ glu_ctx_env ↘ Sb }
| glu_ctx_env_cons_mod :
  `{ forall TSb Sb,
        EG Γ ∈ glu_ctx_env ↘ TSb ->
        gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U ->
        Sb <∙> cons_mod_glu_sub_pred Γ U TSb ->
        EG Γ ▹ₘ U ∈ glu_ctx_env ↘ Sb }.

Definition glu_rel_ctx Γ : Prop := exists Sb, EG Γ ∈ glu_ctx_env ↘ Sb.
#[global] Arguments glu_rel_ctx Γ/.

Definition glu_rel_exp Γ M A : Prop :=
  exists Sb,
    EG Γ ∈ glu_ctx_env ↘ Sb /\
      exists i,
      forall Δ σ ρ,
        Δ ⊢s σ ® ρ ∈ Sb ->
        glu_rel_exp_with_sub i Δ M A σ ρ.
#[global] Arguments glu_rel_exp Γ M A/.

(** There is no gluing judgment for substitutions, so the fundamental theorem
    has two parts. A gluing predicate is indexed by a value, and
    [⟦τ ⨟ σ⟧(ρ) = ⟦τ⟧(⟦σ⟧ρ)] is not an equation when substitution is an
    operation, so such a judgment cannot be stated. Concrete substitutions are
    handled by lemmas about [glu_rel_exp] instead, just as
    [completeness_fundamental] has no substitution part. *)

Notation "⊩ Γ" := (glu_rel_ctx Γ) (at level 70, Γ at level 69).
Notation "Γ ⊩ M : A" := (glu_rel_exp Γ M A) (at level 70, M at level 69, A at level 69).

End Fixed_GCtx.

#[export]
Hint Rewrite @glu_univ_elem_equation_1 : glu_univ_elem.

Notation "'glu_typ_pred_args'" := (Tcons ctx (Tcons typ Tnil)).
Notation "'glu_typ_pred'" := (predicate glu_typ_pred_args).
Notation "'glu_typ_pred_equivalence'" := (@predicate_equivalence glu_typ_pred_args) (only parsing).
Notation "Γ ⊢ A ® R" := ((R Γ A : (Prop : Type)) : (Prop : (Type : Type))) (at level 70, A at level 69, R constr).
Notation "'glu_exp_pred_args'" := (Tcons ctx (Tcons typ (Tcons exp (Tcons domain Tnil)))).
Notation "'glu_exp_pred'" := (predicate glu_exp_pred_args).
Notation "'glu_exp_pred_equivalence'" := (@predicate_equivalence glu_exp_pred_args) (only parsing).
Notation "Γ ⊢ M : A ® m ∈ R" := (R Γ A M m : (Prop : (Type : Type))) (at level 70, M at level 69, m at level 69, R constr).
Notation "'glu_sub_pred_args'" := (Tcons ctx (Tcons sub (Tcons env Tnil))).
Notation "'glu_sub_pred'" := (predicate glu_sub_pred_args).
Notation "'glu_sub_pred_equivalence'" := (@predicate_equivalence glu_sub_pred_args) (only parsing).
Notation "Γ ⊢s σ ® ρ ∈ R" := ((R Γ σ ρ : Prop) : (Prop : (Type : Type))) (at level 70, σ at level 69, ρ at level 69, R constr).
Notation "'DG' a ∈ R ↘ P ↘ El" := (R P El a : ((Prop : Type) : (Type : Type))) (at level 70, a at level 69, R constr, P constr, El constr).
Notation "'EG' A ∈ R ↘ Sb " := (R Sb A : ((Prop : (Type : Type)) : (Type : Type))) (at level 70, A at level 69, R constr, Sb constr).
#[export]
Hint Constructors glu_nat : mctt.
#[export]
Hint Constructors glu_False : mctt.
#[export]
Hint Constructors neut_glu_exp_pred pi_glu_typ_pred pi_glu_exp_pred : mctt.
#[export]
Hint Constructors glu_univ_elem_core : mctt.
#[export]
Hint Constructors glu_elem_bot : mctt.
#[export]
Hint Constructors glu_elem_top : mctt.
#[export]
Hint Constructors glu_typ_top : mctt.
Notation "⊩ Γ" := (glu_rel_ctx Γ) (at level 70, Γ at level 69).
Notation "Γ ⊩ M : A" := (glu_rel_exp Γ M A) (at level 70, M at level 69, A at level 69).

(** [induction H using glu_univ_elem_ind] does not apply, for the reason
    [per_univ_elem_induction] explains. The tactics below perform the same
    induction. *)
Ltac glu_induction_hintro := let H := fresh "H" in intro H.

Ltac glu_univ_elem_induction_core HH ih :=
  lazymatch type of HH with
  | glu_univ_elem ?i ?P ?El ?a =>
      repeat match goal with
             | Hd : ?T |- _ =>
                 lazymatch Hd with HH => fail | i => fail | P => fail | El => fail | a => fail | _ => idtac end;
                 lazymatch T with
                 | context [i] => revert Hd | context [P] => revert Hd
                 | context [El] => revert Hd | context [a] => revert Hd
                 end
             end;
      revert HH; revert i P El a;
      refine (glu_univ_elem_ind _ _ _ _ _ _ _);
      [ do 5 intro; do 3 glu_induction_hintro | do 3 intro; do 2 glu_induction_hintro
      | do 3 intro; do 2 glu_induction_hintro | do 3 intro; do 2 glu_induction_hintro
      | do 12 intro; glu_induction_hintro; ih; do 6 glu_induction_hintro | do 5 intro; do 3 glu_induction_hintro ]; cbv beta
  end.

(** As [induction H using glu_univ_elem_ind]: the hypothesis on the motive at
    the domain of a [Π] is [IHH]; those under a binder are [H]s, as
    [induction] does not see them as inductive hypotheses. *)
Ltac glu_univ_elem_induction H :=
  let IHn := fresh "IH" H in
  let HH := fresh "Hglue" in
  rename H into HH;
  glu_univ_elem_induction_core HH ltac:(idtac; let n := fresh IHn in intro n).

(** As [induction 1 using glu_univ_elem_ind]. *)
Ltac glu_univ_elem_induction1 :=
  intros until 1;
  match goal with
  | H : glu_univ_elem _ _ _ _ |- _ =>
      glu_univ_elem_induction_core H ltac:(idtac; let n := fresh "IH" in intro n)
  end.
