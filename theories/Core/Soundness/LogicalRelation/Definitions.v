From Stdlib Require Import Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export PER.
From Mctt.Core.Syntactic Require Export SystemOpt.
From Mctt.Core.Soundness.Weakening Require Export Definitions.

Import Domain_Notations Wk_Notations.
Global Open Scope predicate_scope.

Generalizable All Variables.

Notation "'glu_typ_pred_args'" := (Tcons ctx (Tcons typ Tnil)).
Notation "'glu_typ_pred'" := (predicate glu_typ_pred_args).
Notation "'glu_typ_pred_equivalence'" := (@predicate_equivalence glu_typ_pred_args) (only parsing).
(** This type annotation is to distinguish this notation from others *)
Notation "Γ ⊢ A ® R" := ((R Γ A : (Prop : Type)) : (Prop : (Type : Type))) (in custom judg at level 80, Γ custom exp, A custom exp, R constr).

Notation "'glu_exp_pred_args'" := (Tcons ctx (Tcons typ (Tcons exp (Tcons domain Tnil)))).
Notation "'glu_exp_pred'" := (predicate glu_exp_pred_args).
Notation "'glu_exp_pred_equivalence'" := (@predicate_equivalence glu_exp_pred_args) (only parsing).
Notation "Γ ⊢ M : A ® m ∈ R" := (R Γ A M m : (Prop : (Type : Type))) (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp, m custom domain, R constr).

Notation "'glu_sub_pred_args'" := (Tcons ctx (Tcons sub (Tcons env Tnil))).
Notation "'glu_sub_pred'" := (predicate glu_sub_pred_args).
Notation "'glu_sub_pred_equivalence'" := (@predicate_equivalence glu_sub_pred_args) (only parsing).
Notation "Γ ⊢s σ ® ρ ∈ R" := ((R Γ σ ρ : Prop) : (Prop : (Type : Type))) (in custom judg at level 80, Γ custom exp, σ custom exp, ρ custom domain, R constr).

Notation "'DG' a ∈ R ↘ P ↘ El" := (R P El a : ((Prop : Type) : (Type : Type))) (in custom judg at level 90, a custom domain, R constr, P constr, El constr).
Notation "'EG' A ∈ R ↘ Sb " := (R Sb A : ((Prop : (Type : Type)) : (Type : Type))) (in custom judg at level 90, A custom exp, R constr, Sb constr).

Inductive glu_nat : ctx -> exp -> domain -> Prop :=
| glu_nat_zero :
  `{ {{ Γ ⊢ M ≈ zero : ℕ }} ->
     glu_nat Γ M d{{{ zero }}} }
| glu_nat_succ :
  `{ {{ Γ ⊢ M ≈ succ M' : ℕ }} ->
     glu_nat Γ M' m' ->
     glu_nat Γ M d{{{ succ m' }}} }
| glu_nat_neut :
  `{ per_bot m m ->
     (forall {Δ φ M'}, {{ Δ ⊢k φ : Γ }} -> {{ Rne m in length Δ ↘ M' }} -> {{ Δ ⊢ M⟨φ⟩ ≈ M' : ℕ }}) ->
     glu_nat Γ M d{{{ ⇑ a m }}} }.

#[export]
Hint Constructors glu_nat : mctt.

Definition nat_glu_typ_pred i : glu_typ_pred := fun Γ A => {{ Γ ⊢ A ≈ ℕ : Type@i }}.
Arguments nat_glu_typ_pred i Γ A/.

Definition nat_glu_exp_pred i : glu_exp_pred := fun Γ A M m => {{ Γ ⊢ A ® nat_glu_typ_pred i }} /\ glu_nat Γ M m.
Arguments nat_glu_exp_pred i Γ A M m/.

Definition neut_glu_typ_pred i a : glu_typ_pred :=
  fun Γ A => {{ Γ ⊢ A : Type@i }} /\
            (forall Δ φ A', {{ Δ ⊢k φ : Γ }} -> {{ Rne a in length Δ ↘ A' }} -> {{ Δ ⊢ A⟨φ⟩ ≈ A' : Type@i }}).
Arguments neut_glu_typ_pred i a Γ A/.

Variant neut_glu_exp_pred i a : glu_exp_pred :=
| mk_neut_glu_exp_pred :
  `{ {{ Γ ⊢ A ® neut_glu_typ_pred i a }} ->
     {{ Γ ⊢ M : A }} ->
     {{ Dom m ≈ m ∈ per_bot }} ->
     (forall Δ φ M', {{ Δ ⊢k φ : Γ }} ->
                   {{ Rne m in length Δ ↘ M' }} ->
                   {{ Δ ⊢ M⟨φ⟩ ≈ M' : A⟨φ⟩ }}) ->
     {{ Γ ⊢ M : A ® ⇑ b m ∈ neut_glu_exp_pred i a }} }.

Variant pi_glu_typ_pred i
  (IR : relation domain)
  (IP : glu_typ_pred)
  (IEl : glu_exp_pred)
  (OP : forall c (equiv_c : {{ Dom c ≈ c ∈ IR }}), glu_typ_pred) : glu_typ_pred :=
| mk_pi_glu_typ_pred :
  `{ {{ Γ ⊢ A ≈ Π IT OT : Type@i }} ->
     {{ Γ ⊢ IT : Type@i }} ->
     {{ Γ , IT ⊢ OT : Type@i }} ->
     (forall Δ φ, {{ Δ ⊢k φ : Γ }} -> {{ Δ ⊢ IT⟨φ⟩ ® IP }}) ->
     (forall Δ φ M m,
         {{ Δ ⊢k φ : Γ }} ->
         {{ Δ ⊢ M : IT⟨φ⟩ ® m ∈ IEl }} ->
         forall (equiv_m : {{ Dom m ≈ m ∈ IR }}),
           {{ Δ ⊢ OT[^(ι φ),,M] ® OP _ equiv_m }}) ->
     {{ Γ ⊢ A ® pi_glu_typ_pred i IR IP IEl OP }} }.

Variant pi_glu_exp_pred i
  (IR : relation domain)
  (IP : glu_typ_pred)
  (IEl : glu_exp_pred)
  (elem_rel : relation domain)
  (OEl : forall c (equiv_c : {{ Dom c ≈ c ∈ IR }}), glu_exp_pred): glu_exp_pred :=
| mk_pi_glu_exp_pred :
  `{ {{ Γ ⊢ M : A }} ->
     {{ Dom m ≈ m ∈ elem_rel }} ->
     {{ Γ ⊢ A ≈ Π IT OT : Type@i }} ->
     {{ Γ ⊢ IT : Type@i }} ->
     {{ Γ , IT ⊢ OT : Type@i }} ->
     (forall Δ φ, {{ Δ ⊢k φ : Γ }} -> {{ Δ ⊢ IT⟨φ⟩ ® IP }}) ->
     (forall Δ φ N n,
         {{ Δ ⊢k φ : Γ }} ->
         {{ Δ ⊢ N : IT⟨φ⟩ ® n ∈ IEl }} ->
         forall (equiv_n : {{ Dom n ≈ n ∈ IR }}),
         exists mn, {{ $| m & n |↘ mn }} /\ {{ Δ ⊢ M⟨φ⟩ N : OT[^(ι φ),,N] ® mn ∈ OEl _ equiv_n }}) ->
     {{ Γ ⊢ M : A ® m ∈ pi_glu_exp_pred i IR IP IEl elem_rel OEl }} }.

#[export]
Hint Constructors neut_glu_exp_pred pi_glu_typ_pred pi_glu_exp_pred : mctt.

Definition univ_glu_typ_pred j i : glu_typ_pred := fun Γ A => {{ Γ ⊢ A ≈ Type@j :  Type@i }}.
Arguments univ_glu_typ_pred j i Γ A/.
Transparent univ_glu_typ_pred.

Section Gluing.
  Variable
    (i : nat)
      (glu_univ_typ_rec : forall {j}, j < i -> domain -> glu_typ_pred).

  Definition univ_glu_exp_pred' {j} (lt_j_i : j < i) : glu_exp_pred :=
    fun Γ A M m =>
      {{ Γ ⊢ M : A }} /\
        {{ Γ ⊢ A ≈ Type@j : Type@i }} /\
        {{ Γ ⊢ M ® glu_univ_typ_rec lt_j_i m }}.

  #[global]
  Arguments univ_glu_exp_pred' {j} lt_j_i Γ A M m/.

  Inductive glu_univ_elem_core : glu_typ_pred -> glu_exp_pred -> domain -> Prop :=
  | glu_univ_elem_core_univ :
    `{ forall typ_rel
         el_rel
         (lt_j_i : j < i),
          typ_rel <∙> univ_glu_typ_pred j i ->
          el_rel <∙> univ_glu_exp_pred' lt_j_i ->
          {{ DG 𝕌@j ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }} }

  | glu_univ_elem_core_nat :
    `{ forall typ_rel el_rel,
          typ_rel <∙> nat_glu_typ_pred i ->
          el_rel <∙> nat_glu_exp_pred i ->
          {{ DG ℕ ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }} }

  | glu_univ_elem_core_pi :
    `{ forall (in_rel : relation domain)
         IP IEl
         (OP : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_typ_pred)
         (OEl : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_exp_pred)
         typ_rel el_rel
         (elem_rel : relation domain),
          {{ DG a ∈ glu_univ_elem_core ↘ IP ↘ IEl }} ->
          {{ DF a ≈ a ∈ per_univ_elem i ↘ in_rel }} ->
          (forall {c} (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) b,
              {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
              {{ DG b ∈ glu_univ_elem_core ↘ OP _ equiv_c ↘ OEl _ equiv_c }}) ->
          {{ DF Π a ρ B ≈ Π a ρ B ∈ per_univ_elem i ↘ elem_rel }} ->
          typ_rel <∙> pi_glu_typ_pred i in_rel IP IEl OP ->
          el_rel <∙> pi_glu_exp_pred i in_rel IP IEl elem_rel OEl ->
          {{ DG Π a ρ B ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }} }

  | glu_univ_elem_core_neut :
    `{ forall typ_rel el_rel,
          {{ Dom b ≈ b ∈ per_bot }} ->
          typ_rel <∙> neut_glu_typ_pred i b ->
          el_rel <∙> neut_glu_exp_pred i b ->
          {{ DG ⇑ a b ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }} }.
End Gluing.

#[export]
Hint Constructors glu_univ_elem_core : mctt.

Equations glu_univ_elem (i : nat) : glu_typ_pred -> glu_exp_pred -> domain -> Prop by wf i :=
| i => glu_univ_elem_core i (fun j lt_j_i a Γ A => exists P El, {{ DG a ∈ glu_univ_elem j ↘ P ↘ El }} /\ {{ Γ ⊢ A ® P }}).

Definition glu_univ_typ (i : nat) (a : domain) : glu_typ_pred :=
  fun Γ A => exists P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} /\ {{ Γ ⊢ A ® P }}.
Arguments glu_univ_typ i a Γ A/.

Definition univ_glu_exp_pred j i : glu_exp_pred :=
    fun Γ A M m =>
      {{ Γ ⊢ M : A }} /\ {{ Γ ⊢ A ≈ Type@j : Type@i }} /\
        {{ Γ ⊢ M ® glu_univ_typ j m }}.
Arguments univ_glu_exp_pred j i Γ A M m/.

Section GluingInduction.
  Hypothesis
    (motive : nat -> glu_typ_pred -> glu_exp_pred -> domain -> Prop)

      (case_univ :
        forall i j
          (P : glu_typ_pred) (El : glu_exp_pred) (lt_j_i : j < i),
          (forall P' El' a, {{ DG a ∈ glu_univ_elem j ↘ P' ↘ El' }} -> motive j P' El' a) ->
          P <∙> univ_glu_typ_pred j i ->
          El <∙> univ_glu_exp_pred j i ->
          motive i P El d{{{ 𝕌 @ j }}})

      (case_nat :
        forall i (P : glu_typ_pred) (El : glu_exp_pred),
          P <∙> nat_glu_typ_pred i ->
          El <∙> nat_glu_exp_pred i ->
          motive i P El d{{{ ℕ }}})

      (case_pi :
        forall i a B (ρ : env) (in_rel : relation domain) (IP : glu_typ_pred)
          (IEl : glu_exp_pred) (OP : forall c : domain, {{ Dom c ≈ c ∈ in_rel }} -> glu_typ_pred)
          (OEl : forall c : domain, {{ Dom c ≈ c ∈ in_rel }} -> glu_exp_pred) (P : glu_typ_pred) (El : glu_exp_pred)
          (elem_rel : relation domain),
          {{ DG a ∈ glu_univ_elem i ↘ IP ↘ IEl }} ->
          motive i IP IEl a ->
          {{ DF a ≈ a ∈ per_univ_elem i ↘ in_rel }} ->
          (forall (c : domain) (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) (b : domain),
              {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
              {{ DG b ∈ glu_univ_elem i ↘ OP c equiv_c ↘ OEl c equiv_c }}) ->
          (forall (c : domain) (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) (b : domain),
              {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
              motive i (OP c equiv_c) (OEl c equiv_c) b) ->
          {{ DF Π a ρ B ≈ Π a ρ B ∈ per_univ_elem i ↘ elem_rel }} ->
          P <∙> pi_glu_typ_pred i in_rel IP IEl OP ->
          El <∙> pi_glu_exp_pred i in_rel IP IEl elem_rel OEl ->
          motive i P El d{{{ Π a ρ B }}})

      (case_neut :
        forall i b a
          (P : glu_typ_pred)
          (El : glu_exp_pred),
          {{ Dom b ≈ b ∈ per_bot }} ->
          P <∙> neut_glu_typ_pred i b ->
          El <∙> neut_glu_exp_pred i b ->
          motive i P El d{{{ ⇑ a b }}})
  .

  #[local]
  Ltac def_simp := simp glu_univ_elem in *; mauto 3.

  #[derive(equations=no, eliminator=no), tactic="def_simp"]
  Equations glu_univ_elem_ind i P El a
    (H : glu_univ_elem i P El a) : motive i P El a by wf i :=
  | i, P, El, a, H =>
      glu_univ_elem_core_ind
        i
        (fun j lt_j_i a Γ A => glu_univ_typ j a Γ A)
        (motive i)
        (fun j P' El' lt_j_i HP' HEl' =>
           case_univ i j P' El' lt_j_i
             (fun P'' El'' A H => glu_univ_elem_ind j P'' El'' A H)
             HP'
             HEl')
        (case_nat i)
        _ (* (case_pi i) *)
        (case_neut i)
        P El a
        _.
  Next Obligation.
    eapply (case_pi i); def_simp; eauto.
  Qed.
End GluingInduction.

Variant glu_elem_bot i a Γ A M m : Prop :=
| glu_elem_bot_make : forall P El,
    {{ Γ ⊢ M : A }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Dom m ≈ m ∈ per_bot }} ->
    (forall Δ φ M', {{ Δ ⊢k φ : Γ }} -> {{ Rne m in length Δ ↘ M' }} -> {{ Δ ⊢ M⟨φ⟩ ≈ M' : A⟨φ⟩ }}) ->
    {{ Γ ⊢ M : A ® m ∈ glu_elem_bot i a }}.
#[export]
Hint Constructors glu_elem_bot : mctt.

Variant glu_elem_top i a Γ A M m : Prop :=
| glu_elem_top_make : forall P El,
    {{ Γ ⊢ M : A }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Dom ⇓ a m ≈ ⇓ a m ∈ per_top }} ->
    (forall Δ φ w, {{ Δ ⊢k φ : Γ }} -> {{ Rnf ⇓ a m in length Δ ↘ w }} -> {{ Δ ⊢ M⟨φ⟩ ≈ w : A⟨φ⟩ }}) ->
    {{ Γ ⊢ M : A ® m ∈ glu_elem_top i a }}.
#[export]
Hint Constructors glu_elem_top : mctt.

Variant glu_typ_top i a Γ A : Prop :=
| glu_typ_top_make :
    {{ Γ ⊢ A : Type@i }} ->
    {{ Dom a ≈ a ∈ per_top_typ }} ->
    (forall Δ φ A', {{ Δ ⊢k φ : Γ }} -> {{ Rtyp a in length Δ ↘ A' }} -> {{ Δ ⊢ A⟨φ⟩ ≈ A' : Type@i }}) ->
    {{ Γ ⊢ A ® glu_typ_top i a }}.
#[export]
Hint Constructors glu_typ_top : mctt.

Variant glu_rel_typ_with_sub i Δ A σ ρ : Prop :=
| mk_glu_rel_typ_with_sub :
  `{ forall P El,
        {{ ⟦ A ⟧ ρ ↘ a }} ->
        {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
        {{ Δ ⊢ A[σ] ® P }} ->
        glu_rel_typ_with_sub i Δ A σ ρ }.

Definition nil_glu_sub_pred : glu_sub_pred :=
  fun Δ σ ρ => {{ Δ ⊢s σ : ⋅ }}.
Arguments nil_glu_sub_pred Δ σ ρ/.

(** The parameters are ordered differently from the Agda version
    so that we can return [glu_sub_pred]. *)
Variant cons_glu_sub_pred i Γ A (TSb : glu_sub_pred) : glu_sub_pred :=
| mk_cons_glu_sub_pred :
  `{ forall P El,
        {{ Δ ⊢s σ : Γ, A }} ->
        {{ ⟦ A ⟧ ρ ↯ ↘ a }} ->
        {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
        (** [A⟨↑⟩[σ]] rather than [A[Wk ⨟ σ]]: it is the direct instance of
            [{{ Γ, A ⊢ #0 : A⟨↑⟩ }}] along [σ]. *)
        {{ Δ ⊢ #0[σ] : A⟨↑⟩[σ] ® ^(ρ 0) ∈ El }} ->
        {{ Δ ⊢s Wk ⨟ σ ® ρ ↯ ∈ TSb }} ->
        {{ Δ ⊢s σ ® ρ ∈ cons_glu_sub_pred i Γ A TSb }} }.

Inductive glu_ctx_env : glu_sub_pred -> ctx -> Prop :=
| glu_ctx_env_nil :
  `{ forall Sb,
        Sb <∙> nil_glu_sub_pred ->
        {{ EG ⋅ ∈ glu_ctx_env ↘ Sb }} }
| glu_ctx_env_cons :
  `{ forall i TSb Sb,
        {{ EG Γ ∈ glu_ctx_env ↘ TSb }} ->
        {{ Γ ⊢ A : Type@i }} ->
        (forall Δ σ ρ,
            {{ Δ ⊢s σ ® ρ ∈ TSb }} ->
            glu_rel_typ_with_sub i Δ A σ ρ) ->
        Sb <∙> cons_glu_sub_pred i Γ A TSb ->
        {{ EG Γ, A ∈ glu_ctx_env ↘ Sb }} }.

Variant glu_rel_exp_with_sub i Δ M A σ ρ : Prop :=
| mk_glu_rel_exp_with_sub :
  `{ forall P El,
        {{ ⟦ A ⟧ ρ ↘ a }} ->
        {{ ⟦ M ⟧ ρ ↘ m }} ->
        {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
        {{ Δ ⊢ M[σ] : A[σ] ® m ∈ El }} ->
        glu_rel_exp_with_sub i Δ M A σ ρ }.

Definition glu_rel_ctx Γ : Prop := exists Sb, {{ EG Γ ∈ glu_ctx_env ↘ Sb }}.
Arguments glu_rel_ctx Γ/.

Definition glu_rel_exp Γ M A : Prop :=
  exists Sb,
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} /\
      exists i,
      forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        glu_rel_exp_with_sub i Δ M A σ ρ.
Arguments glu_rel_exp Γ M A/.

(** There is no [Γ ⊩s τ : Γ'], and the fundamental theorem has two parts, not
    three: a gluing predicate is indexed by a *value*, and
    [⟦τ ⨟ σ⟧(ρ) = ⟦τ⟧(⟦σ⟧ρ)] is not an equation once
    substitution is an operation, so [glu_rel_sub_with_sub] cannot be stated.
    Concrete substitutions are handled by [glu_rel_exp]-level lemmas instead,
    exactly as [{{ Γ ⊨s σ : Δ }}] is absent from [completeness_fundamental]. *)

Notation "⊩ Γ" := (glu_rel_ctx Γ) (in custom judg at level 80, Γ custom exp).
Notation "Γ ⊩ M : A" := (glu_rel_exp Γ M A) (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp).
