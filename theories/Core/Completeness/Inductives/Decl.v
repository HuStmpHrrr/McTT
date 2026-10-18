(** * Telescopes in the PER Model

    The types of an inductive declaration live in closed contexts, and its
    eliminator binds telescopes of them.  This file relates the three ways
    the proofs meet a telescope:

    - as arguments related at it, one at a time ([per_gargs]);
    - as an environment of a context extended by it ([per_ctx_env]);
    - as the argument of the [Π] it makes ([ctx_pi]).

    A closed telescope is read in any base environment: arguments related at
    it over one pair of bases are related over any other ([per_gargs_base]),
    which is how the proofs move between the environments of a judgment and
    the empty environment the PER clause of an inductive type reads its
    telescopes in. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax.
From Mctt.Core.Semantic.PER Require Import Tele.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Arguments at a Telescope *)

Lemma per_gargs_length : forall ts ρ ρ' xs xs', per_gargs ts ρ ρ' xs xs' ->
    List.length xs = List.length xs' /\ List.length xs <= List.length ts.
Proof. induction 1; cbn; [ split; lia |]; destruct IHper_gargs; split; lia. Qed.

Lemma per_gargs_app : forall ts1 ts2 ρ ρ' xs1 xs1' xs2 xs2',
    List.length xs1 = List.length ts1 ->
    per_gargs (ts1 ++ ts2) ρ ρ' (xs1 ++ xs2) (xs1' ++ xs2') ->
    List.length xs1' = List.length ts1 ->
    per_gargs ts1 ρ ρ' xs1 xs1' /\ per_gargs ts2 (env_args ρ xs1) (env_args ρ' xs1') xs2 xs2'.
Proof.
  induction ts1 as [| e ts1 IH]; intros * Hl H Hl'.
  - destruct xs1, xs1'; cbn in *; try discriminate; split; [ constructor | exact H ].
  - destruct xs1 as [| x xs1], xs1' as [| x' xs1']; cbn in *; try discriminate.
    inversion H; subst.
    match goal with H' : per_gargs (ts1 ++ ts2) (ρ ↦ x) (ρ' ↦ x') _ _ |- _ =>
      destruct (IH ts2 (ρ ↦ x) (ρ' ↦ x') xs1 xs1' xs2 xs2' ltac:(lia) H' ltac:(lia)) as [H1 H2] end.
    split; [ econstructor; eassumption | exact H2 ].
Qed.

Lemma per_gargs_app_intro : forall ts1 ts2 ρ ρ' xs1 xs1' xs2 xs2',
    List.length xs1 = List.length ts1 ->
    per_gargs ts1 ρ ρ' xs1 xs1' -> per_gargs ts2 (env_args ρ xs1) (env_args ρ' xs1') xs2 xs2' ->
    per_gargs (ts1 ++ ts2) ρ ρ' (xs1 ++ xs2) (xs1' ++ xs2').
Proof.
  induction ts1 as [| e ts1 IH]; intros * Hl H1 H2.
  - destruct xs1; cbn in *; try discriminate; inversion H1; subst; exact H2.
  - destruct xs1 as [| x xs1]; cbn in *; try discriminate.
    inversion H1; subst; cbn; econstructor; [ eassumption | eassumption |].
    apply IH; [ lia | eassumption | exact H2 ].
Qed.

Lemma per_gargs_snoc : forall ts A ρ ρ' xs xs' x x' i R,
    List.length xs = List.length ts ->
    per_gargs ts ρ ρ' xs xs' ->
    rel_typ i A (env_args ρ xs) A (env_args ρ' xs') R -> R x x' ->
    per_gargs (ts ++ ce_ass A :: nil) ρ ρ' (xs ++ x :: nil) (xs' ++ x' :: nil).
Proof.
  intros * Hl H HA Hx; apply per_gargs_app_intro; [ exact Hl | exact H |].
  econstructor; [ exact HA | exact Hx | constructor ].
Qed.

(** A type at a small index is also one at a large index. *)
Lemma per_univ_elem_to_nat : forall (i : uidx) R a a', DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    exists n : nat, DF a ≈ a' ∈ per_univ_elem n ↘ R.
Proof. intros [o | n] * H; [ exists 0; eapply per_univ_elem_cumu_uidx; [ exact H | exact I ] | exists n; exact H ]. Qed.

(** ** The Elements of a [Π] over a Telescope

    A family [f] of values, one per list of arguments, that applies by
    taking the next argument, and whose full applications are related at
    the codomain, is an element of the [Π]. *)
Lemma ctx_pi_rel_elem : forall N (f : list domain -> domain) B,
    (forall xs x, List.length xs < N -> $| f xs & x | gc_deps ⍮ gc_stack ↘ f (xs ++ x :: nil)) ->
    forall ts, tele_ass ts ->
    forall ρ ρ' xs xs' a a' (i : uidx) R,
      List.length xs + List.length ts = N -> List.length xs' = List.length xs ->
      ⟦ ctx_pi (List.rev ts) B ⟧ env_args ρ xs ↘ a -> ⟦ ctx_pi (List.rev ts) B ⟧ env_args ρ' xs' ↘ a' ->
      DF a ≈ a' ∈ per_univ_elem i ↘ R ->
      (forall ys ys', per_gargs ts (env_args ρ xs) (env_args ρ' xs') ys ys' -> List.length ys = List.length ts ->
         Dom f (xs ++ ys) ≈ f (xs' ++ ys') ∈ per_head B B (env_args ρ (xs ++ ys)) (env_args ρ' (xs' ++ ys'))) ->
      Dom f xs ≈ f xs' ∈ R.
Proof.
  intros N f B Happ ts; induction ts as [| e ts IH]; intros Hts * Hl Hl' Ha Ha' HR Hbase.
  - cbn [List.rev ctx_pi] in Ha, Ha'.
    specialize (Hbase nil nil ltac:(constructor) eq_refl); rewrite !List.app_nil_r in Hbase.
    exact (Hbase _ _ _ _ Ha Ha' HR).
  - assert (He : exists A, e = ce_ass A) by (inversion Hts as [| ? ? He _]; exact He).
    destruct He as [A ->].
    assert (Hts' : tele_ass ts) by (inversion Hts; assumption).
    cbn [List.rev] in Ha, Ha'; rewrite ctx_pi_snoc in Ha, Ha'.
    inversion Ha; subst a; inversion Ha'; subst a'.
    basic_invert_per_univ_elem HR.
    apply_relation_equivalence.
    intros c c' Hc.
    cbn [List.length] in Hl.
    destruct_rel_mod_eval.
    econstructor; [ apply Happ; lia | apply Happ; lia |].
    rewrite <- !env_args_snoc in *.
    eapply (IH Hts' ρ ρ' (xs ++ c :: nil) (xs' ++ c' :: nil));
      [ rewrite List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | eassumption | eassumption | eassumption |].
    intros ys ys' Hys Hlys.
    rewrite <- !List.app_assoc; cbn [List.app].
    apply Hbase; [| cbn; lia ].
    match goal with E1 : ⟦ A ⟧ env_args ρ xs ↘ ?b, E2 : ⟦ A ⟧ env_args ρ' xs' ↘ ?b' |- _ =>
      destruct (per_univ_elem_to_nat _ _ _ _ equiv_a_a') as [n Hn];
      econstructor; [ exact (mk_rel_mod_eval b b' E1 E2 Hn) | exact Hc |] end.
    rewrite <- !env_args_snoc; exact Hys.
Qed.

(** ** Arguments over Another Base

    The types of a telescope valid over [Tb] are related at related bases,
    so arguments related at it over one pair of bases are over another
    related pair. *)
Lemma per_gargs_base : forall ts Tb RTb,
    EF Tb ≈ Tb ∈ per_ctx_env ↘ RTb -> ⊨ List.rev ts ++ Tb -> tele_ass ts ->
    forall ρ1 ρ2 ρ3 ρ4 xs xs', RTb ρ1 ρ2 -> RTb ρ1 ρ3 -> RTb ρ2 ρ4 ->
      per_gargs ts ρ1 ρ2 xs xs' -> per_gargs ts ρ3 ρ4 xs xs'.
Proof.
  induction ts as [| e ts IH]; intros * HTb HC Hts * H12 H13 H24 Hg; [ inversion Hg; subst; constructor |].
  assert (He : exists A, e = ce_ass A) by (inversion Hts as [| ? ? He _]; exact He).
  destruct He as [A ->].
  assert (Hts' : tele_ass ts) by (inversion Hts; assumption).
  inversion Hg as [| ? A0 ? ? x x' ? ys ys' R HA Hx Hg']; subst; [ constructor |].
  cbn [List.rev] in HC; rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
  destruct (rel_ctx_wf_ass_inv (rel_ctx_wf_app_r _ _ HC)) as [j HAv].
  pose proof (per_ctx_env_of_typ HTb HAv) as HTb'.
  assert (HP : PER RTb) by (eapply per_env_PER; exact HTb).
  assert (H34 : RTb ρ3 ρ4) by (etransitivity; [ symmetry; exact H13 | etransitivity; [ exact H12 | exact H24 ] ]).
  destruct HA as [a1 a2 Ea1 Ea2 HR].
  destruct (rel_exp_of_typ_inversion_simple_at HTb HAv _ _ H13) as (b1 & a3 & Eb1 & Ea3 & [R13 HR13]).
  destruct (rel_exp_of_typ_inversion_simple_at HTb HAv _ _ H24) as (b2 & a4 & Eb2 & Ea4 & [R24 HR24]).
  destruct (rel_exp_of_typ_inversion_simple_at HTb HAv _ _ H34) as (b3 & b4 & Eb3 & Eb4 & [R34 HR34]).
  assert (b1 = a1) as -> by (eapply functional_eval_exp; eassumption).
  assert (b2 = a2) as -> by (eapply functional_eval_exp; eassumption).
  assert (b3 = a3) as -> by (eapply functional_eval_exp; eassumption).
  assert (b4 = a4) as -> by (eapply functional_eval_exp; eassumption).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR13 HR34) as (R14 & HR14 & E14).
  assert (E34 : R34 <~> R14) by (eapply per_univ_elem_left_irrel; [ exact HR34 | exact HR14 ]).
  assert (E13 : R <~> R14) by (eapply per_univ_elem_right_irrel; [ exact HR | exact HR14 ]).
  assert (E24 : R24 <~> R14) by (eapply per_univ_elem_left_irrel; [ exact HR24 | exact HR14 ]).
  assert (HPR : PER R) by (eapply per_elem_PER; exact HR).
  assert (Hxx : R x x) by (etransitivity; [ exact Hx | symmetry; exact Hx ]).
  assert (Hx'x' : R x' x') by (etransitivity; [ symmetry; exact Hx | exact Hx ]).
  econstructor; [ exact (mk_rel_mod_eval a3 a4 Ea3 Ea4 HR34) | exact (proj2 (E34 _ _) (proj1 (E13 _ _) Hx)) |].
  eapply (IH _ _ HTb' HC Hts' (ρ1 ↦ x) (ρ2 ↦ x')); [ | | | exact Hg' ].
  - apply per_env_extend_intro'; [ exact H12 | exact (per_head_of Ea1 Ea2 HR Hx) ].
  - apply per_env_extend_intro'; [ exact H13 | exact (per_head_of Ea1 Ea3 HR13 (proj2 (E14 _ _) (proj1 (E13 _ _) Hxx))) ].
  - apply per_env_extend_intro'; [ exact H24 | ].
    exact (per_head_of Ea2 Ea4 HR24 (proj2 (E24 _ _) (proj1 (E13 _ _) Hx'x'))).
Qed.

(** The left arguments are related to themselves, over the left base. *)
Lemma per_gargs_refl_l : forall ts Tb RTb,
    EF Tb ≈ Tb ∈ per_ctx_env ↘ RTb -> ⊨ List.rev ts ++ Tb -> tele_ass ts ->
    forall ρ ρ' xs xs', RTb ρ ρ' -> per_gargs ts ρ ρ' xs xs' -> per_gargs ts ρ ρ xs xs.
Proof.
  induction ts as [| e ts IH]; intros * HTb HC Hts * Hρ Hg; [ inversion Hg; subst; constructor |].
  assert (He : exists A, e = ce_ass A) by (inversion Hts as [| ? ? He _]; exact He).
  destruct He as [A ->].
  assert (Hts' : tele_ass ts) by (inversion Hts; assumption).
  inversion Hg as [| ? A0 ? ? x x' ? ys ys' R HA Hx Hg']; subst; [ constructor |].
  cbn [List.rev] in HC; rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
  destruct (rel_ctx_wf_ass_inv (rel_ctx_wf_app_r _ _ HC)) as [j HAv].
  pose proof (per_ctx_env_of_typ HTb HAv) as HTb'.
  assert (HP : PER RTb) by (eapply per_env_PER; exact HTb).
  assert (Hρρ : RTb ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  destruct HA as [a1 a2 Ea1 Ea2 HR].
  destruct (rel_exp_of_typ_inversion_simple_at HTb HAv _ _ Hρρ) as (b1 & b1' & Eb1 & Eb1' & [R11 HR11]).
  assert (b1 = a1) as -> by (eapply functional_eval_exp; eassumption).
  assert (b1' = a1) as -> by (eapply functional_eval_exp; eassumption).
  assert (E : R <~> R11) by (eapply per_univ_elem_right_irrel; [ exact HR | exact HR11 ]).
  assert (HPR : PER R) by (eapply per_elem_PER; exact HR).
  assert (Hxx : R x x) by (etransitivity; [ exact Hx | symmetry; exact Hx ]).
  econstructor; [ exact (mk_rel_mod_eval a1 a1 Ea1 Ea1 HR11) | apply E, Hxx |].
  eapply (IH _ _ HTb' HC Hts' (ρ ↦ x) (ρ' ↦ x')); [ | exact Hg' ].
  apply per_env_extend_intro'; [ exact Hρ | exact (per_head_of Ea1 Ea2 HR Hx) ].
Qed.

(** Environments related at an extension are arguments related at its
    telescope. *)
Lemma rel_gargs : forall ts Tb RTb R,
    EF Tb ≈ Tb ∈ per_ctx_env ↘ RTb -> ⊨ List.rev ts ++ Tb -> tele_ass ts ->
    EF List.rev ts ++ Tb ≈ List.rev ts ++ Tb ∈ per_ctx_env ↘ R ->
    forall ρ ρ' xs xs', List.length xs = List.length ts -> List.length xs' = List.length ts ->
      R (env_args ρ xs) (env_args ρ' xs') -> RTb ρ ρ' /\ per_gargs ts ρ ρ' xs xs'.
Proof.
  induction ts as [| e ts IH]; intros * HTb HC Hts HR * Hl Hl' Hρ.
  - destruct xs, xs'; cbn in *; try discriminate. split; [| constructor ].
    assert (E : R <~> RTb) by (eapply per_ctx_env_right_irrel; eassumption). apply E; exact Hρ.
  - assert (He : exists A, e = ce_ass A) by (inversion Hts as [| ? ? He _]; exact He).
    destruct He as [A ->].
    assert (Hts' : tele_ass ts) by (inversion Hts; assumption).
    destruct xs as [| x xs], xs' as [| x' xs']; cbn in Hl, Hl'; try discriminate.
    cbn [List.rev] in HC, HR; rewrite <- List.app_assoc in HC, HR; cbn [List.app] in HC, HR.
    destruct (rel_ctx_wf_ass_inv (rel_ctx_wf_app_r _ _ HC)) as [j HAv].
    pose proof (per_ctx_env_of_typ HTb HAv) as HTb'.
    destruct (IH _ _ _ HTb' HC Hts' HR (ρ ↦ x) (ρ' ↦ x') xs xs' ltac:(lia) ltac:(lia) Hρ) as [[Hb Hh] Hg].
    split; [ exact Hb |].
    destruct (rel_exp_of_typ_inversion_simple_at HTb HAv _ _ Hb) as (a & a' & Ea & Ea' & [R0 HR0]).
    econstructor; [ exact (mk_rel_mod_eval a a' Ea Ea' HR0) | | exact Hg ].
    exact (Hh _ _ _ _ Ea Ea' HR0).
Qed.

(** Arguments related at a telescope read back alike. *)
Lemma per_gargs_top : forall ts ρ ρ' xs xs', per_gargs ts ρ ρ' xs xs' -> List.length xs = List.length ts ->
    forall s, exists Ms, Rps xs at ts in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Ms /\ Rps xs' at ts in gc_deps ⍮ gc_stack ⍮ ρ' ⍮ s ↘ Ms.
Proof.
  induction 1 as [ts ρ ρ' | i A ρ ρ' a a' ts args args' R HA Ha Hg IH]; intros Hl s.
  - destruct ts; cbn in Hl; try discriminate; exists nfs_nil; split; constructor.
  - destruct HA as [b b' Eb Eb' HR].
    destruct (IH ltac:(cbn in Hl; lia) s) as (Ms & HM & HM').
    destruct (per_elem_then_per_top HR Ha s) as (V & HV & HV').
    exists (nfs_cons V Ms); split; econstructor; eassumption.
Qed.

(** ** Environments of Arguments *)

Lemma eval_sb_of_list : forall Ms σ ρ ρσ ms,
    ⟦ σ ⟧s ρ ↘ ρσ -> ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms -> ⟦ sb_of_list σ Ms ⟧s ρ ↘ env_args ρσ ms.
Proof.
  induction Ms as [| M Ms IH]; intros * Hσ HMs; inversion HMs; subst; cbn [sb_of_list]; [ exact Hσ |].
  change (env_args ρσ (m :: ms0)) with (env_args (ρσ ↦ m) ms0).
  apply IH; [ apply eval_sub_extend; assumption | assumption ].
Qed.



(** ** Universes *)

(** The index of the elements of a universe. *)
Definition univ_idx (a : domain) : uidx :=
  match a with
  | d_univ j => ul j
  | d_suniv l => us (dlvl_real l)
  | _ => ul 0
  end.

Definition is_univ (a : domain) : Prop := (exists j, a = d_univ j) \/ (exists l, a = d_suniv l).

Lemma per_univ_elem_univ : forall (i : uidx) R a a', DF a ≈ a' ∈ per_univ_elem i ↘ R -> is_univ a ->
    univ_idx a' = univ_idx a /\ (R <~> per_univ (univ_idx a)).
Proof.
  intros * H [[j ->] | [l ->]]; basic_invert_per_univ_elem H; cbn [univ_idx].
  - split; [ reflexivity | assumption ].
  - match goal with Hl : per_lvl l ?l' |- _ => split; [ f_equal; symmetry; apply per_lvl_real; exact Hl | assumption ] end.
Qed.

(** ** Closed Terms

    A closed term of a closed type is valid at [⋅] when its values at any
    two environments are related at the type's values there. *)
Lemma rel_exp_closed_intro : forall T N (i : nat),
    (forall σ, T[σ] = T) -> (forall σ, N[σ] = N) ->
    (forall ρ ρ', exists a a' R n n', ⟦ T ⟧ ρ ↘ a /\ ⟦ T ⟧ ρ' ↘ a' /\ DF a ≈ a' ∈ per_univ_elem i ↘ R /\
       ⟦ N ⟧ ρ ↘ n /\ ⟦ N ⟧ ρ' ↘ n' /\ Dom n ≈ n' ∈ R) ->
    ⋅ ⊨ N : T.
Proof.
  intros * HT HN H.
  refine (mk_rel_exp_under_ctx _ _ _ _ (fun _ _ => True) per_ctx_env_nil_true i _).
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (H ρ ρσ) as (a1 & a2 & R12 & n1 & n2 & Ea1 & Ea2 & HR12 & En1 & En2 & Hn12).
  destruct (H ρσ ρ'σ') as (b2 & a3 & R23 & m2 & n3 & Eb2 & Ea3 & HR23 & Em2 & En3 & Hn23).
  destruct (H ρ'σ' ρ') as (b3 & a4 & R34 & m3 & n4 & Eb3 & Ea4 & HR34 & Em3 & En4 & Hn34).
  assert (b2 = a2) as -> by (eapply functional_eval_exp; eassumption).
  assert (b3 = a3) as -> by (eapply functional_eval_exp; eassumption).
  assert (m2 = n2) as -> by (eapply functional_eval_exp; eassumption).
  assert (m3 = n3) as -> by (eapply functional_eval_exp; eassumption).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR12 HR23) as (R13 & HR13 & E13).
  assert (E12 : R12 <~> R23) by (etransitivity; [ exact E13 | eapply per_univ_elem_left_irrel; [ exact HR13 | exact HR23 ] ]).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR23 HR34) as (R24 & HR24 & E24).
  assert (E34 : R34 <~> R23) by (etransitivity; [ eapply per_univ_elem_left_irrel; [ exact HR34 | exact HR24 ] | symmetry; exact E24 ]).
  exists R23; split.
  - apply (mk_rel_exp a1 a2 a3 a4); [ rewrite HT; exact Ea1 | exact Ea2 | exact Ea3 | rewrite HT; exact Ea4 |].
    apply rel_chain_4; [ eapply per_univ_elem_resp_iff; [ exact HR12 | exact E12 ] | exact HR23
                       | eapply per_univ_elem_resp_iff; [ exact HR34 | exact E34 ] ].
  - apply (mk_rel_exp n1 n2 n3 n4); [ rewrite HN; exact En1 | exact En2 | exact En3 | rewrite HN; exact En4 |].
    apply rel_chain_4; [ apply E12, Hn12 | exact Hn23 | apply E34, Hn34 ].
Qed.

(** The index of a universe shifted past a context is that of the
    universe, and the index of a universe is the same at related
    environments. *)
Lemma univ_idx_wk : forall Pre Up S (i : nat) R E E' b a,
    ⊨ Pre ++ Up -> Up ⊨ S : Typeω@i ->
    EF Pre ++ Up ≈ Pre ++ Up ∈ per_ctx_env ↘ R -> R E E' ->
    ⟦ S[wk_shiftn (List.length Pre)]ʷ ⟧ E ↘ b -> ⟦ S ⟧ ⟪wk_shiftn (List.length Pre)⟫ E' ↘ a ->
    is_univ b -> univ_idx a = univ_idx b.
Proof.
  intros * HC HS HR HE Eb Ea Hb.
  destruct (rel_exp_under_ctx_wk_simple (rel_wk_under_ctx_shiftn _ _ HC) HS) as (RΓ & HΓ & j & Hwk).
  assert (ER : R <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hwk _ _ (proj1 (ER _ _) HE)) as (x & x' & Rx & Ex & Ex' & HRx & m & m' & Em & Em' & Hmm).
  assert (m = b) as -> by (eapply functional_eval_exp; eassumption).
  assert (m' = a) as -> by (eapply functional_eval_exp; eassumption).
  cbn in Ex; inversion Ex; subst.
  basic_invert_per_univ_elem HRx.
  match goal with Hm : ?r b a, H : ?r <~> _ |- _ => apply H in Hm; destruct Hm as [Rm HRm] end.
  exact (proj1 (per_univ_elem_univ _ _ _ _ HRm Hb)).
Qed.

Lemma univ_idx_rel : forall Up S (i : nat) R E E' a a',
    EF Up ≈ Up ∈ per_ctx_env ↘ R -> Up ⊨ S : Typeω@i -> R E E' ->
    ⟦ S ⟧ E ↘ a -> ⟦ S ⟧ E' ↘ a' -> is_univ a -> univ_idx a' = univ_idx a.
Proof.
  intros * HR HS HE Ea Ea' Hu.
  destruct (rel_exp_of_typ_inversion_simple_at HR HS _ _ HE) as (b & b' & Eb & Eb' & [Rb HRb]).
  assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
  assert (b' = a') as -> by (eapply functional_eval_exp; eassumption).
  exact (proj1 (per_univ_elem_univ _ _ _ _ HRb Hu)).
Qed.

(** ** The Weakenings of Constructor Arguments *)

Lemma wk_mono_pat : forall pat, wk_mono (wk_pat pat).
Proof.
  induction pat as [| [] pat IH]; cbn [wk_pat];
    [ apply wk_mono_id | apply wk_mono_compose; [ exact IH | apply wk_mono_shift ] | apply wk_mono_q, IH ].
Qed.

#[export] Instance WkMono_pat (pat : list bool) : WkMono (wk_pat pat) := wk_mono_pat pat.

Lemma eval_wk_q_cons : forall φ `{WkMono φ} ρ v, ⟪wk_q φ⟫ (ρ ↦ v) = ⟪φ⟫ ρ ↦ v.
Proof.
  intros φ Hφ ρ v; cbn [extend_env].
  pose proof (eval_wk_q_tail φ (de_term v :: ρ)) as Ht.
  pose proof (eval_wk_q_zero_entry φ (de_term v :: ρ)) as Hh.
  assert (Hl : List.length (⟪wk_q φ⟫ (de_term v :: ρ)) = wk_len (wk_q φ) (S (List.length ρ))) by apply eval_wk_length.
  assert (H0 : 0 < wk_len (wk_q φ) (S (List.length ρ)))
    by (apply wk_len_spec; [ apply wk_mono_q; exact Hφ | cbn; lia ]).
  destruct (⟪wk_q φ⟫ (de_term v :: ρ)) as [| h t] eqn:E.
  - change (List.length (@nil dentry)) with 0 in Hl; lia.
  - cbn [drop_env List.tl] in Ht; subst t; simpl in Hh; subst h; reflexivity.
Qed.

(** [wk_pat] drops the recursive arguments of an environment of arguments. *)
Lemma eval_wk_pat_args : forall gs1 E vs, List.length vs = List.length gs1 ->
    ⟪wk_pat (cargs_pat gs1)⟫ (env_args E vs) = env_args E (nonrec_vals gs1 vs).
Proof.
  induction gs1 as [| g gs1 IH] using List.rev_ind; intros E vs Hl.
  - destruct vs; cbn in *; try discriminate; apply eval_wk_id.
  - rewrite List.length_app in Hl; cbn in Hl.
    assert (Hvs : exists vs0 v, vs = vs0 ++ v :: nil)
      by (destruct vs as [| v vs0] using List.rev_ind; [ cbn in Hl; lia | eauto ]).
    destruct Hvs as (vs0 & v & ->); rewrite List.length_app in Hl; cbn in Hl.
    rewrite cargs_pat_snoc, nonrec_vals_app by lia.
    rewrite env_args_snoc.
    destruct g as [A | Ps]; cbn [wk_pat nonrec_vals].
    + rewrite eval_wk_q_cons by typeclasses eauto; rewrite IH by lia.
      rewrite env_args_snoc; reflexivity.
    + rewrite eval_wk_compose by typeclasses eauto.
      rewrite eval_wk_shift; cbn [drop_env List.tl extend_env].
      rewrite IH by lia; rewrite List.app_nil_r; reflexivity.
Qed.

Lemma rel_wk_under_ctx_compose : forall Γ Δ Θ' φ ψ,
    Γ ⊨ʷ ψ : Δ -> Δ ⊨ʷ φ : Θ' -> Γ ⊨ʷ (wk_compose φ ψ) : Θ'.
Proof.
  intros * [R1 H1 R2 H2 Hψ] [R3 H3 R4 H4 Hφ].
  assert (E : R2 <~> R3) by (eapply per_ctx_env_right_irrel; eassumption).
  eapply rel_wk_under_ctx_intro; [ exact H1 | exact H4 |].
  eapply rel_wk_compose; [ exact Hψ |].
  destruct Hφ as [Hm Hφ]; split; [ exact Hm | intros; apply Hφ, E; assumption ].
Qed.

(** ** Variables of an Environment of Arguments *)

Lemma env_entry_args_app : forall ρ zs i, env_entry (env_args ρ zs) (List.length zs + i) = env_entry ρ i.
Proof.
  intros; rewrite env_args_rev, !env_entry_nth, List.app_nth2 by (rewrite List.length_rev, List.length_map; lia).
  rewrite List.length_rev, List.length_map; f_equal; lia.
Qed.

Lemma eval_vars_from_args : forall xs E ys,
    ⟦ vars_from (List.length ys) (List.length xs) ⟧* gc_deps ⍮ gc_stack ⍮ env_args E (xs ++ ys) ↘ xs.
Proof.
  induction xs as [| x xs IH]; intros; cbn [List.length]; [ unfold vars_from; cbn; constructor |].
  rewrite vars_from_S; econstructor; [| exact (IH (E ↦ x) ys) ].
  pose proof (env_entry_args_app (E ↦ x) (xs ++ ys) 0) as H.
  rewrite List.length_app, Nat.add_0_r in H.
  change (env_args E ((x :: xs) ++ ys)) with (env_args (E ↦ x) (xs ++ ys)).
  replace (List.length ys + List.length xs) with (List.length xs + List.length ys) by lia.
  assert (Hv : env_var (env_args (E ↦ x) (xs ++ ys)) (List.length xs + List.length ys) = x)
    by (unfold env_var; rewrite H; reflexivity).
  rewrite <- Hv at 2; constructor.
Qed.

End Fixed_GCtx.
