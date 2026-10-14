(** * Inverting the Typing Rules

    Every term former is introduced by exactly one rule, so a typing derivation
    for a term whose head is known says exactly what that rule says — except that
    [wf_exp_subtyp] may have been applied any number of times afterwards, which
    replaces "the type is [A]" by "the type refines to [A]".  Each lemma below is
    that observation for one former, proved by induction on the derivation with
    only two cases: the introduction rule, where refinement is reflexivity, and
    [wf_exp_subtyp], where it is transitivity.

    Substitutions need no inversion lemmas:

    - [M[σ]] is not a term former, so there is nothing to invert;
    - [wf_sub] is a record, not an inductive family, so a derivation of
      [Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ] carries no information beyond its two fields;
      in particular [Θ ⍮ Ξ ⍮ Γ ⊢s Id : Δ] is itself a context refinement. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export SubEq.
From Mctt.Core.Syntactic.System Require Import MemberWf.
Import Syntax_Notations Wk_Notations.

Lemma wf_typ_inversion : forall {Θ Ξ Γ i A},
    Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@i : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@(S i) ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve.
Qed.

#[export]
Hint Resolve wf_typ_inversion : mctt.

Lemma wf_univ_inversion : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨succl M⟩ ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve.
Qed.

(** The level of a universe that is a type is a level of some sort: the only
    rule that gives a universe a type asks for it. *)
Lemma wf_univ_lvl_inversion : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ : A ->
    exists n, Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n.
Proof.
  intros * H.
  dependent induction H; [ eexists; eassumption | apply (IHwf_exp1 _ eq_refl) ].
Qed.

#[export]
Hint Resolve wf_univ_inversion wf_univ_lvl_inversion : mctt.

Lemma wf_nat_inversion : forall Θ Ξ Γ A,
    Θ ⍮ Ξ ⍮ Γ ⊢ ℕ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@0 ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_nat_inversion : mctt.

Corollary wf_zero_inversion : forall Θ Ξ Γ A,
    Θ ⍮ Ξ ⍮ Γ ⊢ zero : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℕ ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp eq_refl); mautosolve 4.
Qed.

#[export]
Hint Resolve wf_zero_inversion : mctt.

Corollary wf_succ_inversion : forall Θ Ξ Γ A M,
    Θ ⍮ Ξ ⍮ Γ ⊢ succ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ℕ /\ Θ ⍮ Ξ ⍮ Γ ⊢ ℕ ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ eq_refl);
    destruct_conjs; mautosolve.
Qed.

#[export]
Hint Resolve wf_succ_inversion : mctt.

(** The level forms.  A level is of type [Level] up to subtyping, and so is
    every argument of [succl] and [maxl]. *)
Lemma wf_level_inversion : forall Θ Ξ Γ A n,
    Θ ⍮ Ξ ⍮ Γ ⊢ Level@n : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@0 ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_level_inversion : mctt.

Corollary wf_llit_inversion : forall Θ Ξ Γ A o,
    Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ o : A ->
    exists n, Θ ⍮ Ξ ⍮ Γ ⊢ Level@n ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    [ eexists; mauto 3
    | specialize (IHwf_exp1 _ eq_refl) as (n & Hs); exists n; mauto 3 ].
Qed.

#[export]
Hint Resolve wf_llit_inversion : mctt.

(** The same with the bound of the sort the literal is typed at. *)
Corollary wf_llit_inversion_sort : forall Θ Ξ Γ A o,
    Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ o : A ->
    exists n, fst o <= n /\ Θ ⍮ Ξ ⍮ Γ ⊢ Level@n ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    [ eexists; split; [ eassumption | mauto 3 ]
    | specialize (IHwf_exp1 _ eq_refl) as (n & Hn & Hs); exists n; split; [ exact Hn | mauto 3 ] ].
Qed.

Corollary wf_succl_inversion : forall Θ Ξ Γ A M,
    Θ ⍮ Ξ ⍮ Γ ⊢ succl M : A ->
    exists n, Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n /\ Θ ⍮ Ξ ⍮ Γ ⊢ Level@n ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    [ eexists; split; [ eassumption | mauto 3 ]
    | specialize (IHwf_exp1 _ eq_refl) as (n & HM & Hs);
      exists n; split; [ exact HM | mauto 3 ] ].
Qed.

#[export]
Hint Resolve wf_succl_inversion : mctt.

Corollary wf_maxl_inversion : forall Θ Ξ Γ A M N,
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl M N : A ->
    exists n, Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n /\ Θ ⍮ Ξ ⍮ Γ ⊢ N : Level@n /\ Θ ⍮ Ξ ⍮ Γ ⊢ Level@n ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    [ eexists; repeat split; [ eassumption | eassumption | mauto 3 ]
    | specialize (IHwf_exp1 _ _ eq_refl) as (n & HM & HN & Hs);
      exists n; repeat split; [ exact HM | exact HN | mauto 3 ] ].
Qed.

#[export]
Hint Resolve wf_maxl_inversion : mctt.

Lemma wf_natrec_inversion : forall Θ Ξ Γ A M A' MZ MS,
    Θ ⍮ Ξ ⍮ Γ ⊢ rec M return A' | zero -> MZ | succ -> MS end : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ MZ : A'[Id,,zero] /\
    Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A' ⊢ MS : A'[Wk ⨟ Wk,,succ #1] /\
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ℕ /\
    Θ ⍮ Ξ ⍮ Γ ⊢ A'[Id,,M] ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp1 _ _ _ _ eq_refl));
    destruct_conjs; gen_core_presups; repeat split; mautosolve.
Qed.

#[export]
Hint Resolve wf_natrec_inversion : mctt.

Lemma wf_True_inversion : forall Θ Ξ Γ A,
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@0 ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_True_inversion : mctt.

Corollary wf_true_inversion : forall Θ Ξ Γ A,
    Θ ⍮ Ξ ⍮ Γ ⊢ ⋆ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp eq_refl); mautosolve 4.
Qed.

#[export]
Hint Resolve wf_true_inversion : mctt.

Lemma wf_False_inversion : forall Θ Ξ Γ A,
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@0 ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_False_inversion : mctt.

Lemma wf_exfalso_inversion : forall Θ Ξ Γ A M A',
    Θ ⍮ Ξ ⍮ Γ ⊢ efq M return A' : A ->
    (exists i, Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ A' : Typeω@i) /\
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ⊥ /\
    Θ ⍮ Ξ ⍮ Γ ⊢ A'[Id,,M] ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp1 _ _ eq_refl));
    destruct_conjs; gen_core_presups; repeat split; mautosolve.
Qed.

#[export]
Hint Resolve wf_exfalso_inversion : mctt.

(** A [Π] is in a large universe, or in a small one at a level. *)
Lemma wf_pi_inversion : forall {Θ Ξ Γ A B C},
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : C ->
    (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@i ⊆ C) \/
    (exists L n, Θ ⍮ Ξ ⍮ Γ ⊢ L : Level@n /\ Θ ⍮ Ξ ⍮ Γ ⊢ A : Type⟨L⟩ /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type⟨L[↑]ʷ⟩ /\
               Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨L⟩ ⊆ C).
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    try destruct IHwf_exp1 as [(j & ? & ? & ?) | (L' & n' & ? & ? & ? & ?)];
    gen_core_presups.
  - left; eexists; mautosolve 4.
  - right; exists L, n; repeat split; try assumption; mautosolve 4.
  - left; exists j; repeat split; try assumption; mautosolve 4.
  - right; exists L', n'; repeat split; try assumption; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_pi_inversion : mctt.

(** The level the domain and the codomain are checked at can always be taken to
    be the level of the [Π]-type itself.  Moving the refinement [Typeω@j ⊆ Typeω@i]
    from [Γ] into [Γ ▹ A] is a weakening, and it is the only step that needs any
    work: both sides are unchanged by it ([Typeω@j[↑]ʷ] is [Typeω@j]), but only by
    computation, so the step is taken by hand. *)
Corollary wf_pi_inversion' : forall {Θ Ξ Γ A B i},
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i.
Proof.
  intros * [[j [? []]] | [L [n [? [? []]]]]]%wf_pi_inversion.
  2:{ assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A) by mauto 3.
      assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢w ↑ : Γ) by mauto 2.
      assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ L[↑]ʷ : Level@n) by (eapply (wk_preserves_exp _ _ _ _ (Level@n)); eassumption).
      split; eapply wf_exp_suniv_large; eassumption. }
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A) by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢w ↑ : Γ) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ exp_wk Typeω@j ↑ ⊆ exp_wk Typeω@i ↑) as H'
      by (eapply wk_preserves_subtyp; eassumption).
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ Typeω@j ⊆ Typeω@i) by exact H'.
  split; mauto 3.
Qed.

#[export]
Hint Resolve wf_pi_inversion' : mctt.

Corollary wf_fn_inversion : forall {Θ Ξ Γ A M C},
    Θ ⍮ Ξ ⍮ Γ ⊢ λ A M : C ->
    exists B, Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M : B /\ Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ⊆ C.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs; gen_core_presups;
    eexists; split; mautosolve 3.
Qed.

#[export]
Hint Resolve wf_fn_inversion : mctt.

Lemma wf_app_inversion : forall {Θ Ξ Γ M N C},
    Θ ⍮ Ξ ⍮ Γ ⊢ M $ N : C ->
    exists A B, Θ ⍮ Ξ ⍮ Γ ⊢ M : Π A B /\ Θ ⍮ Ξ ⍮ Γ ⊢ N : A /\ Θ ⍮ Ξ ⍮ Γ ⊢ B[Id,,N] ⊆ C.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs;
    do 2 eexists; repeat split; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_app_inversion : mctt.

Lemma wf_let_inversion : forall {Θ Ξ Γ oA M B T},
    Θ ⍮ Ξ ⍮ Γ ⊢ a_let (b_def oA M) B : T ->
    exists A i C, let_ann oA A /\ Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ⊢ M : A /\
           Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C /\ Θ ⍮ Ξ ⍮ Γ ⊢ C[Id,,M] ⊆ T.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ _ eq_refl);
    destruct_conjs; gen_core_presups;
    do 3 eexists; repeat split; first [ solve [ eassumption ] | mautosolve 4 ].
Qed.

(** For an annotated definition, the type is the annotation. *)
Corollary wf_let_ann_inversion : forall {Θ Ξ Γ A M B T},
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B : T ->
    exists i C, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ⊢ M : A /\
           Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C /\ Θ ⍮ Ξ ⍮ Γ ⊢ C[Id,,M] ⊆ T.
Proof.
  intros * H; destruct (wf_let_inversion H) as (A' & i & C & [[=] | [= <-]] & ?); eauto.
Qed.

#[export]
Hint Resolve wf_let_inversion : mctt.

Lemma wf_let_mod_inversion : forall {Θ Ξ Γ U B T},
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B : T ->
    exists C, Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U /\
         Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : C /\ Θ ⍮ Ξ ⍮ Γ ⊢ C[Id ,,ₘ me_lit U] ⊆ T.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs; gen_core_presups;
    eexists; repeat split; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_let_mod_inversion : mctt.

Lemma wf_vlookup_inversion : forall {Θ Ξ Γ x A},
    Θ ⍮ Ξ ⍮ Γ ⊢ #x : A ->
    exists A', Γ ∋ #x : A' /\ Θ ⍮ Ξ ⍮ Γ ⊢ A' ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp1 _ eq_refl));
    destruct_conjs; gen_core_presups; eexists; split; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_vlookup_inversion : mctt.

(** We omit [wf_exp_subtyp] as it does not give a useful inversion. *)

(** ** Inductive Types

    The type former, a constructor and the eliminator are each introduced by
    one rule; the inversion of an application of a head is
    [wf_apps_head]. *)

Lemma wf_apps_head : forall {Θ Ξ Γ} Ns M T, Θ ⍮ Ξ ⍮ Γ ⊢ apps_exp M Ns : T -> exists T', Θ ⍮ Ξ ⍮ Γ ⊢ M : T'.
Proof.
  intros Θ Ξ Γ Ns; induction Ns as [| N Ns IH]; intros * H; cbn in H; [ eauto |].
  destruct (IH _ _ H) as (T' & HT'); destruct (wf_app_inversion HT') as (X & Y & HM & _); eauto.
Qed.

Lemma wf_subtyp_of_typed : forall {Θ Ξ Γ M A}, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A.
Proof.
  intros * H; destruct (presup_exp_typ H) as [i Hi].
  eapply wf_subtyp_refl; [ exact Hi | apply wf_exp_eq_refl; exact Hi ].
Qed.

Lemma wf_ind_inversion : forall {Θ Ξ Γ p T},
    Θ ⍮ Ξ ⍮ Γ ⊢ a_ind p : T ->
    exists D, ind_lookup Θ Ξ p = Some D /\ Θ ⍮ Ξ ⍮ Γ ⊢ ind_ty D ⊆ T.
Proof.
  intros * H; dependent induction H.
  - exists D; split; [ assumption | eapply wf_subtyp_of_typed; econstructor; eassumption ].
  - destruct (IHwf_exp1 _ eq_refl) as (D & HD & Hs); exists D; split; [ exact HD | eapply wf_subtyp_trans; eassumption ].
Qed.

Lemma wf_con_inversion : forall {Θ Ξ Γ p c T},
    Θ ⍮ Ξ ⍮ Γ ⊢ a_con p c : T ->
    exists D gs, ind_lookup Θ Ξ p = Some D /\ ind_con D c = Some gs /\ Θ ⍮ Ξ ⍮ Γ ⊢ con_ty p D gs ⊆ T.
Proof.
  intros * H; dependent induction H.
  - exists D, gs; split; [ assumption | split; [ assumption | eapply wf_subtyp_of_typed; econstructor; eassumption ] ].
  - destruct (IHwf_exp1 _ _ eq_refl) as (D & gs & HD & Hc & Hs); exists D, gs.
    split; [ exact HD | split; [ exact Hc | eapply wf_subtyp_trans; eassumption ] ].
Qed.

(** The head of an eliminator is the canonical one at arguments [Ns], or a
    module resolving to it at them. *)
Definition elim_head_rel (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (H : modexp) (p : qname) (Ns : list exp) : Prop :=
  H = me_apps (qname_mod p) Ns \/
  exists H0 T, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H0 ≈ H0 /\ member_type Θ Ξ Γ H0 nil (mr_ind p T) /\ H = me_apps H0 Ns.

Lemma elim_head_rel_canon : forall Θ Ξ Γ p T D pL Ns Ns',
    gc_module Θ Ξ p = Some (mr_body T (Some D)) ->
    elim_head_rel Θ Ξ Γ (me_apps (qname_mod p) Ns) pL Ns' -> pL = p /\ Ns' = Ns.
Proof.
  intros * Hp [Heq | (H0 & T0 & _ & Hm & Heq)].
  - destruct (me_apps_inj _ _ _ _ (qname_mod_noapp _) (qname_mod_noapp _) Heq) as [Hq ->].
    apply (f_equal mod_qname) in Hq; rewrite !qname_mod_qname in Hq; injection Hq as ->; split; reflexivity.
  - destruct (me_apps_inj _ _ _ _ (qname_mod_noapp _) (member_type_ind_noapp' _ _ _ _ _ _ Hm) Heq) as [<- ->].
    split; [ exact (path_ind_self _ _ _ _ _ _ _ _ Hp Hm) | reflexivity ].
Qed.

(** A head naming a path: the path itself, or a path resolving to the
    module of the inductive type. *)
Lemma elim_head_rel_path : forall Θ Ξ Γ pq pL Ns,
    elim_head_rel Θ Ξ Γ (qname_mod pq) pL Ns ->
    Ns = nil /\ (pL = pq \/ exists T, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ qname_mod pq ≈ qname_mod pq /\
                                    member_type Θ Ξ Γ (qname_mod pq) nil (mr_ind pL T)).
Proof.
  intros * [Heq | (H0 & T0 & HH0 & Hm & Heq)].
  - symmetry in Heq; destruct (me_apps_qname _ _ _ Heq) as [-> Hq].
    apply (f_equal mod_qname) in Hq; rewrite !qname_mod_qname in Hq; injection Hq as ->; auto.
  - symmetry in Heq; destruct (me_apps_qname _ _ _ Heq) as [-> ->].
    split; [ reflexivity | right; eauto ].
Qed.

Lemma wf_elim_inversion : forall {Θ Ξ Γ H nm A Bs M T},
    Θ ⍮ Ξ ⍮ Γ ⊢ a_elim H nm A Bs M : T ->
    exists p D Ps i Ns nh,
      ind_lookup Θ Ξ p = Some D /\
      List.length Ps = ind_np D /\
      elim_head_rel Θ Ξ Γ H p Ns /\ List.length Ns = nh /\
      Θ ⍮ Ξ ⍮ Γ ⊢ apps (a_ind p) Ns : ind_ty_at D (List.firstn nh Ps) /\
      Θ ⍮ Ξ ⍮ Γ ⊢ apps (a_ind p) Ns ≈ apps (a_ind p) (List.firstn nh Ps) : ind_ty_at D (List.firstn nh Ps) /\ nh <= ind_nu D /\
      (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
         Θ ⍮ Ξ ⍮ Γ ⊢ P : T) /\
      Θ ⍮ Ξ ⍮ Γ ⊢ M : apps (a_ind p) Ps /\
      nm = S (ind_nn D) /\
      Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊢ A : Typeω@i /\
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D (List.firstn (ind_nu D) Ps) /\
      brs_names (ind_cons D) Bs /\
      (forall c gs, ind_con D c = Some gs ->
         Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) /\
      (forall c gs n B, ind_con D c = Some gs -> List.In (c, n, B) Bs ->
         n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) /\
      (forall c gs n B, ind_con D c = Some gs -> List.In (c, n, B) Bs ->
         Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
           : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) /\
      Θ ⍮ Ξ ⍮ Γ ⊢ A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] ⊆ T.
Proof.
  intros * HE; dependent induction HE.
  - exists p, D, Ps, i, Ns, (List.length Ns); unfold elim_head_rel; repeat (split; [ first [ assumption | exact eq_refl | left; exact eq_refl ] |]).
    eapply wf_subtyp_of_typed; eapply wf_elim; first [ exact eq_refl | eassumption ].
  - destruct (IHHE2 _ _ _ _ _ eq_refl)
      as (pL & D & Ps & i0 & NsL & nh & Hl & ? & Hh & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
    match goal with Hm : member_type _ _ _ _ nil (mr_ind _ _) |- _ =>
      destruct (proj1 (member_type_ind_canon _ _) _ _ _ _ Hm _ _ eq_refl) as (T' & D' & Hp) end.
    destruct (elim_head_rel_canon _ _ _ _ _ _ _ _ _ Hp Hh) as [-> ->].
    exists p, D, Ps, i0, Ns, nh; unfold elim_head_rel; repeat (split; [ first [ assumption | right; do 2 eexists; split; [ eassumption | split; [ eassumption | reflexivity ] ] ] |]).
    eapply wf_subtyp_trans; [ eassumption | eapply wf_subtyp_of_typed; eassumption ].
  - destruct (IHHE1 _ _ _ _ _ eq_refl)
      as (p & D & Ps & i0 & Ns & nh & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
    exists p, D, Ps, i0, Ns, nh; repeat (split; [ first [ assumption | reflexivity ] |]); eapply wf_subtyp_trans; eassumption.
Qed.
