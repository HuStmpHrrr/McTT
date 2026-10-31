From Stdlib Require Import List ListDec Morphisms_Relations String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base Completeness.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core Require Import Consequences.Consistency Semantic.Realizability.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf.
From Mctt.Core.Syntactic Require Import Fresh.
From Mctt.Core.Semantic Require Import MemberWf.
From Mctt.Extraction Require Import FastEval FastDomain Simulation Evaluation Readback NbE PseudoMonadic Subtyping MemberType.
From Mctt.Extraction Require Export TypeCheckBase.
From Mctt.Extraction Require Import IndCheck RecordCheck.
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
Variable F : FCtx.
#[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.

(** * The Checker

    The checker of [Reference.TypeCheck], with two refinements, each of which
    computes the result of a rule of [⊢a] in another way:

    - An application spine [M $ N1 $ ⋯ $ Nk] is checked against the value of
      the type of its head ([type_infer_val_in]): each argument of a [Π] over
      a relevant domain instantiates the codomain closure of the current
      [Π] value with the argument's value ([type_infer_app_in]), where
      [alg_type_infer_app] substitutes the argument into the normal form of
      the codomain and normalizes that.  The type of the whole spine is read
      back once, at the end.  An argument of a [∀], or of a [Π] over a
      proposition, a proof, is never evaluated: its step is the rule's.
    - The inferred type of a checked term is a normal form, its own normal
      form ([alg_type_infer_self]), so [type_check_in] normalizes only the
      type it checks against.

    Both normalize with [Extraction.NbE], whose evaluation skips the
    recursive results nobody reads.  [Reference/Refinement.v] proves that
    both checkers compute the same. *)

(** ** The Type of an Application as a Value

    The type of a term as a value [v] stands for its normal form [T] when it
    is related to [⟦ T ⟧ ρ] by [per_univ], [ρ] the initial environment: it
    then reads back to [T] ([typ_val_read]), and a [Π] value, applied to an
    argument through its closure, stands for the instantiated codomain
    ([typ_val_pi_step]). *)

Lemma typ_val_conv : forall G ρ X Y (i : nat) v a,
    initial_env_f G ρ ->
    G ⊢ X ≈ Y : Typeω@i ->
    ⟦ X ⟧ ρ ↘ a ->
    Dom v ≈ a ∈ per_univ i ->
    exists b, ⟦ Y ⟧ ρ ↘ b /\ Dom v ≈ b ∈ per_univ i.
Proof.
  intros * Hρ HXY Ha Hv.
  destruct (rel_typ_under_ctx_at_initial_env (completeness_fundamental_exp_eq _ _ _ _ HXY))
    as (ρ0 & a0 & b & Hρ0 & Ha0 & Hb & Hab).
  assert (ρ0 = ρ) as -> by (eapply functional_initial_env; eassumption).
  assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
  exists b; split; [ assumption | etransitivity; eassumption ].
Qed.

(** The value of a type of either sort is related to itself in a universe. *)
Lemma typ_val_self : forall G ρ X,
    initial_env_f G ρ ->
    G ⊢ᵗ X ->
    exists a (i : nat), ⟦ X ⟧ ρ ↘ a /\ Dom a ≈ a ∈ per_univ i.
Proof.
  intros * Hρ [S HS HX].
  destruct (rel_typ_sort_at_initial_env HS (wf_exp_eq_refl HX)) as (ρ0 & a & a' & i & Hρ0 & Ha & Ha' & Haa).
  assert (ρ0 = ρ) as -> by (eapply functional_initial_env; eassumption).
  assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
  exists a, i; split; assumption.
Qed.

(** A term of a type of a large universe evaluates. *)
Lemma eval_of_typing : forall G ρ M A (i : nat),
    initial_env_f G ρ ->
    G ⊢ M : A ->
    G ⊢ A : Typeω@i ->
    exists m, ⟦ M ⟧ ρ ↘ m.
Proof.
  intros * Hρ HM HA.
  destruct (soundness HM) as (W & [ρ0 a Hi Ha Hw] & _).
  functional_initial_env_rewrite_clear.
  destruct Hw as [Hp | m w _ Hm _]; [| eauto ].
  exfalso; destruct (typed_at_sort_of_initial_relevance (type_sort_universe i) HA Hρ Ha) as [k Hk].
  rewrite Hp in Hk; exact (typ_prop_absurd HA Hk).
Qed.

Lemma typ_val_read : forall G ρ (T : nf) (i : nat) v a,
    initial_env_f G ρ ->
    nbe_ty_f G T T ->
    ⟦ T ⟧ ρ ↘ a ->
    Dom v ≈ a ∈ per_univ i ->
    Rtyp v in List.length G ↘ T.
Proof.
  intros * Hρ Hn Ha [R Hv].
  destruct (per_univ_then_per_top_typ Hv (List.length G)) as (C & HC & HC').
  inversion Hn; subst.
  functional_initial_env_rewrite_clear.
  functional_eval_rewrite_clear.
  functional_read_rewrite_clear.
  assumption.
Qed.

(** The step of an application: [⟦ b ⟧ ρ' ↦ ⟦ N ⟧ ρ] stands for
    [B[Id,,N]] when [Πᵈ a ρ' b] stands for [Π A B], over a domain of a
    large universe. *)
Lemma typ_val_pi_step : forall G ρ A B N (i : nat) a ρ' b a0 n,
    initial_env_f G ρ ->
    G ⊢ Π A B : Typeω@i ->
    G ⊢ A : Typeω@i ->
    ⟦ Π A B ⟧ ρ ↘ a0 ->
    Dom Πᵈ a ρ' b ≈ a0 ∈ per_univ i ->
    G ⊢ N : A ->
    ⟦ N ⟧ ρ ↘ n ->
    exists v c, ⟦ b ⟧ ρ' ↦ n ↘ v /\ ⟦ B[Id,,N] ⟧ ρ ↘ c /\ Dom v ≈ c ∈ per_univ i.
Proof.
  intros * Hρ HΠ HA Ha0 [R HR] HN Hn.
  assert (HB : G ▹ A ⊢ B : Typeω@i) by exact (proj2 (wf_pi_inversion' HΠ)).
  inversion Ha0; subst.
  assert (HB' : G ▹ A ⊨ B ≈ B : Typeω@i) by (apply completeness_fundamental_exp_eq; mauto 3).
  assert (HN' : G ⊨ N ≈ N : A) by (apply completeness_fundamental_exp_eq; mauto 3).
  assert (HA' : G ⊨ A ≈ A : Typeω@i) by (apply completeness_fundamental_exp_eq; mauto 3).
  pose proof HN' as [env_relΓ HΓr _ _].
  pose proof (per_ctx_then_per_env_initial_env HΓr) as [ρ1 [ρ2 [Hρ1 [Hρ2 Hrel]]]].
  assert (ρ1 = ρ) by (eapply functional_initial_env; eassumption); subst.
  assert (ρ2 = ρ) by (eapply functional_initial_env; eassumption); subst.
  destruct (per_univ_of_instance HΓr HA' HB' HN' _ _ Hrel Hn) as (c & d & Hc & Hd & Hcc & Hcd).
  destruct (rel_exp_under_ctx_at_initial_env HN') as [ρ0 j elem_rel aA Hρ0 HaA HaAel Hterms].
  functional_initial_env_rewrite_clear.
  functional_eval_rewrite_clear.
  destruct Hterms as [Hp | n1 n2 Hn1 Hn2 Hnn].
  - exfalso; destruct (typed_at_sort_of_initial_relevance (type_sort_universe i) HA Hρ ltac:(eassumption)) as [k Hk].
    rewrite Hp in Hk; exact (typ_prop_absurd HA Hk).
  - functional_eval_rewrite_clear.
    basic_invert_per_univ_elem HR.
    handle_per_univ_elem_irrel.
    match goal with Hcod : forall c c' (e : _), rel_mod_eval _ _ _ _ _ _ |- _ =>
      destruct (Hcod _ _ Hnn) as [v d' Hv Hd' Hvd] end.
    functional_eval_rewrite_clear.
    exists v, c; repeat split; try assumption.
    eapply per_univ_trans'; [ eexists; exact Hvd | apply per_univ_sym'; exact Hcd ].
Qed.

Section type_check.
  #[local]
  Hint Constructors type_check_order type_infer_order app_order ext_order unit_order modexp_order : mctt.

  (** The type of a term as a value at the environment [P]: a fast value
      related ([fast_value_simulation]) to one that stands for the normal
      form [T] at the initial environment. *)
  #[warnings="-cannot-define-projection"]
  Record typ_val G (P : checker_env G) (v : fdomain) (T : nf) : Prop := mk_typ_val
    { (** The universe the reference value is related in *)
      typ_val_lvl : nat
    ; (** The initial environment of [G] *)
      typ_val_env : env
    ; (** The value of [T] there *)
      typ_val_sem : domain
    ; (** The reference value [v] stands for *)
      typ_val_rel : domain
    ; (** [typ_val_env] is the initial environment *)
      typ_val_init : initial_env_f G typ_val_env
    ; (** [P] agrees with it *)
      typ_val_agree : fast_env_agree gc_deps gc_stack (fun _ => True) typ_val_env (proj1_sig P)
    ; (** [T] is a type *)
      typ_val_typ : G ⊢ᵗ T
    ; (** [T]'s value *)
      typ_val_eval : ⟦ T ⟧ typ_val_env ↘ typ_val_sem
    ; (** The reference value is related to it in the universe *)
      typ_val_per : Dom typ_val_rel ≈ typ_val_sem ∈ per_univ typ_val_lvl
    ; (** [v] stands for the reference value *)
      typ_val_sim : fast_value_simulation gc_deps gc_stack typ_val_rel v }.

  (** The same for a [Π] over a domain of a large universe, at the universe
      the [Π] and its domain are of: the case whose step instantiates the
      codomain closure. *)
  #[warnings="-cannot-define-projection"]
  Record typ_val_pi G (P : checker_env G) (v : fdomain) (A B : nf) : Prop := mk_typ_val_pi
    { (** The universe of the [Π] *)
      typ_val_pi_lvl : nat
    ; (** The initial environment of [G] *)
      typ_val_pi_env : env
    ; (** The value of the [Π] there *)
      typ_val_pi_sem : domain
    ; (** The reference value [v] stands for *)
      typ_val_pi_rel : domain
    ; (** [typ_val_pi_env] is the initial environment *)
      typ_val_pi_init : initial_env_f G typ_val_pi_env
    ; (** [P] agrees with it *)
      typ_val_pi_agree : fast_env_agree gc_deps gc_stack (fun _ => True) typ_val_pi_env (proj1_sig P)
    ; (** The [Π] is a type of the universe *)
      typ_val_pi_typ : G ⊢ Π A B : Typeω@typ_val_pi_lvl
    ; (** So is its domain *)
      typ_val_pi_dom : G ⊢ A : Typeω@typ_val_pi_lvl
    ; (** The [Π]'s value *)
      typ_val_pi_eval : ⟦ Π A B ⟧ typ_val_pi_env ↘ typ_val_pi_sem
    ; (** The reference value is related to it in the universe *)
      typ_val_pi_per : Dom typ_val_pi_rel ≈ typ_val_pi_sem ∈ per_univ typ_val_pi_lvl
    ; (** [v] stands for the reference value *)
      typ_val_pi_sim : fast_value_simulation gc_deps gc_stack typ_val_pi_rel v }.

  (** A type as a value is right. *)
  Lemma typ_val_ok : forall G P v T, typ_val G P v T -> fdomain_ok gc_deps gc_stack v.
  Proof. intros * [_ _ _ _ _ _ _ _ _ [_ Hok]]; exact Hok. Qed.

  Lemma typ_val_pi_ok : forall G P v A B, typ_val_pi G P v A B -> fdomain_ok gc_deps gc_stack v.
  Proof. intros * [_ _ _ _ _ _ _ _ _ _ [_ Hok]]; exact Hok. Qed.

  (** The same, from a result of the checker *)
  Lemma typ_val_ok_of : forall G P (Q : nf -> Prop) v, (exists T, Q T /\ typ_val G P v T) -> fdomain_ok gc_deps gc_stack v.
  Proof. intros * (T & _ & Hv); eapply typ_val_ok; exact Hv. Qed.

  (** The domain and the environment of a [Π] value, from a result of the
      checker, are right. *)
  Lemma typ_val_pi_dom_ok : forall G P (Q : nf -> Prop) v r a ρ b,
      (exists T, Q T /\ typ_val G P v T) -> v = fd_pi r a ρ b -> fdomain_ok gc_deps gc_stack a.
  Proof. intros * Hv ->; apply typ_val_ok_of in Hv; inversion Hv; assumption. Qed.

  Lemma typ_val_pi_env_ok : forall G P (Q : nf -> Prop) v r a ρ b,
      (exists T, Q T /\ typ_val G P v T) -> v = fd_pi r a ρ b -> fenv_ok gc_deps gc_stack ρ.
  Proof. intros * Hv ->; apply typ_val_ok_of in Hv; inversion Hv; assumption. Qed.

  (** A type as a value reads back to the type it stands for. *)
  Lemma typ_val_rtyp : forall G P M v T,
      ⊢ G -> G ⊢a M ⟹ T -> typ_val G P v T -> Rtypᶠ fdomain_erase v in gc_deps ⍮ gc_stack ⍮ (List.length G) ↘ T.
  Proof.
    intros * HG HM [i p a v0 Hp _ HT Ha Hv0 [Hs _]].
    eapply fast_read_typ_sim; [| exact Hs ].
    eapply typ_val_read; [ eassumption | eapply alg_type_infer_self; eassumption | eassumption | eassumption ].
  Qed.

  (** A [Π] value stands for a [Π] normal form of its tag. *)
  Lemma typ_val_pi_parts : forall G P M T r a ρ b,
      ⊢ G -> G ⊢a M ⟹ T -> typ_val G P (fd_pi r a ρ b) T ->
      exists A B, T = nf_pi r A B /\ Rtypᶠ fdomain_erase a in gc_deps ⍮ gc_stack ⍮ (List.length G) ↘ A.
  Proof.
    intros * HG HM Hv.
    pose proof (typ_val_rtyp _ _ _ _ _ HG HM Hv) as Hr; cbn in Hr.
    inversion Hr; subst; do 2 eexists; split; first [ reflexivity | eassumption ].
  Qed.

  (** A [Π] value over a domain of a large universe: its universe. *)
  Lemma typ_val_pi_of : forall G P A B a ρ b,
      typ_val G P (fd_pi relevant a ρ b) (Πⁿ A B) -> nbe_ty_relevance G A relevant ->
      typ_val_pi G P (fd_pi relevant a ρ b) A B.
  Proof.
    intros * [i p a1 v0 Hp Hag HT Ha1 [R Hv0] Hs] Hr.
    destruct HT as [S HS HT]; cbn [nf_to_exp] in HT.
    destruct (wf_pi_typed_large HT) as [k Hk].
    destruct (wf_pi_inversion' Hk) as [HAs _].
    assert (exists kA, G ⊢ A : Typeω@kA) as [kA HA].
    { destruct Hr as (ρ0 & a0 & Hρ0 & Ha0 & Hr0).
      destruct HAs as [HAs | HAs];
        [ edestruct (typed_at_sort_of_initial_relevance (type_sort_universe k) HAs Hρ0 Ha0) as [kA HkA]
        | edestruct (typed_at_sort_of_initial_relevance type_sort_prop HAs Hρ0 Ha0) as [kA HkA] ];
        rewrite Hr0 in HkA; exists kA; exact HkA. }
    pose (m := Nat.max (Nat.max k kA) i).
    apply (mk_typ_val_pi _ _ _ _ _ m p a1 v0); try assumption.
    - eapply lift_exp_ge; [| exact Hk ]; lia.
    - eapply lift_exp_ge; [| exact HA ]; lia.
    - exists R; eapply per_univ_elem_cumu_ge; [| exact Hv0 ]; lia.
  Qed.

  (** The argument of an application, and the codomain closure at its value,
      evaluate. *)
  Lemma typ_val_app_order : forall G P N A B a ρ b,
      ⊢ G -> typ_val_pi G P (fd_pi relevant a ρ b) A B -> G ⊢a N ⟸ A ->
      fast_eval_exp_order gc_deps gc_stack N (fenv_erase (proj1_sig P)) /\
      forall n', ⟦ N ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase (proj1_sig P) ↘ n' ->
            fast_eval_exp_order gc_deps gc_stack b (fenv_erase ρ ↦ n').
  Proof.
    intros G [p' Hp'] * HG [i p a1 v0 Hp Hag HT HA Ha1 Hv0 [Hs _]] HN; cbn in *.
    assert (HN' : G ⊢ N : A) by (eapply alg_type_check_sound; eassumption).
    destruct (eval_of_typing _ _ _ _ _ Hp HN' HA) as [n Hn].
    destruct (fast_eval_of_ref _ _ _ _ _ _ Hn (fast_env_agree_all _ _ _ _ _ Hag)) as [HoN HsN].
    split; [ exact HoN |].
    intros n' Hn'.
    inversion Hs; subst.
    destruct (typ_val_pi_step _ _ _ _ _ _ _ _ _ _ _ Hp HT HA Ha1 Hv0 HN' Hn) as (v1 & c & Hv1 & _).
    match goal with Hρ0 : forall x : nat, ~ exp_fresh (S x) _ -> _ |- _ =>
      destruct (fast_eval_clo_sim _ _ _ _ _ _ _ _ Hρ0 (HsN _ Hn') Hv1) as (v1' & Hv1' & _) end.
    eapply fast_eval_exp_order_sound; exact Hv1'.
  Qed.

  (** The value of the type of an application: [alg_type_infer_app]'s type stands for
      the codomain closure applied to the argument's value. *)
  Lemma typ_val_app_step : forall G P M N A B a ρ b n v,
      ⊢ G -> G ⊢a M ⟹ Πⁿ A B -> typ_val_pi G P (fd_pi relevant a ρ b) A B -> G ⊢a N ⟸ A ->
      ⟦ N ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase (proj1_sig P) ↘ n ->
      ⟦ b ⟧ᶠ gc_deps ⍮ gc_stack ⍮ (fenv_erase ρ ↦ n) ↘ fdomain_erase v -> fdomain_ok gc_deps gc_stack v ->
      exists T, G ⊢a M $ N ⟹ T /\ typ_val G P v T.
  Proof.
    intros G [p' Hp'] * HG HM [i p a1 v0 Hp Hag HΠ HA Ha1 Hv0 [Hs _]] HN Hn' Hv' Hok; cbn in *.
    assert (HN' : G ⊢ N : A) by (eapply alg_type_check_sound; eassumption).
    destruct (eval_of_typing _ _ _ _ _ Hp HN' HA) as [n0 Hn0].
    pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Hn0 (fast_env_agree_all _ _ _ _ _ Hag)) _ Hn') as HsN.
    inversion Hs; subst.
    destruct (typ_val_pi_step _ _ _ _ _ _ _ _ _ _ _ Hp HΠ HA Ha1 Hv0 HN' Hn0) as (v1 & c & Hv1 & Hc & Hv1c).
    match goal with Hρ0 : forall x : nat, ~ exp_fresh (S x) _ -> _ |- _ =>
      destruct (fast_eval_clo_sim _ _ _ _ _ _ _ _ Hρ0 HsN Hv1) as (v1' & Hv1' & Hs1) end.
    rewrite <- (functional_fast_eval_exp _ _ _ _ Hv' Hv1') in Hs1.
    assert (HB : G ▹ A ⊢ B : Typeω@i) by exact (proj2 (wf_pi_inversion' HΠ)).
    assert (HBN : G ⊢ B[Id,,N] : Typeω@i) by mauto 3.
    destruct (soundness_ty HBN) as (W & HW & HeqW).
    destruct (typ_val_conv _ _ _ _ _ _ _ Hp HeqW Hc Hv1c) as (c' & Hc' & Hvc').
    exists W; split; [ econstructor; eassumption |].
    apply (mk_typ_val _ _ _ _ i p c' v1); try assumption; try (split; assumption).
    apply (@wf_type_univ _ _ _ _ i); gen_presups; assumption.
  Qed.

  (** The codomain of an application at its argument, without evaluating
      the argument when the codomain does not read it ([exp_freshb]): its
      entry is then [𝕌ω@0], which nothing reads.  A numeral, a chain of
      [succ]s, is thus typed in linear time. *)
  Record app_cod_order G (P : checker_env G) N (ρ : fenv) b : Prop := mk_app_cod_order
    { (** The argument evaluates *)
      app_cod_order_arg : fast_eval_exp_order gc_deps gc_stack N (fenv_erase (proj1_sig P))
    ; (** The codomain, at the argument's value *)
      app_cod_order_cod : forall n', ⟦ N ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase (proj1_sig P) ↘ n' ->
                            fast_eval_exp_order gc_deps gc_stack b (fenv_erase ρ ↦ n')
    ; (** The codomain, at [𝕌ω@0], when it does not read the argument *)
      app_cod_order_unread : exp_freshb 0 b = true -> fast_eval_exp_order gc_deps gc_stack b (fenv_erase ρ ↦ 𝕌ω@0) }.

  Definition app_cod_val G (P : checker_env G) N (ρ : fenv) b (v : fdomain) : Prop :=
    (exp_freshb 0 b = true /\ ⟦ b ⟧ᶠ gc_deps ⍮ gc_stack ⍮ (fenv_erase ρ ↦ 𝕌ω@0) ↘ fdomain_erase v) \/
    (exists n, ⟦ N ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase (proj1_sig P) ↘ fdomain_erase n /\
          ⟦ b ⟧ᶠ gc_deps ⍮ gc_stack ⍮ (fenv_erase ρ ↦ fdomain_erase n) ↘ fdomain_erase v).

  #[derive(equations=no,eliminator=no)]
  Equations app_cod G (P : checker_env G) N (ρ : fenv) b (Hρ : fenv_ok gc_deps gc_stack ρ) (H : app_cod_order G P N ρ b) :
      { v | app_cod_val G P N ρ b v /\ fdomain_ok gc_deps gc_stack v } :=
  | G, P, N, ρ, b, Hρ, H with inspect (exp_freshb 0 b) := {
    | exist _ true E =>
        let (v, Hv) := fast_eval_exp_impl F b (fextend_env ρ (fd_univ 0))
                         (fextend_env_ok _ _ _ _ Hρ (fdomain_ok_univ _ _ 0)) (app_cod_order_unread _ _ _ _ _ H E) in
        exist _ v (conj (or_introl (conj E (proj1 Hv))) (proj2 Hv))
    | exist _ false E =>
        let (n, Hn) := fast_eval_exp_impl F N (proj1_sig P) (checker_env_ok G (proj1_sig P) (proj2_sig P)) (app_cod_order_arg _ _ _ _ _ H) in
        let (v, Hv) := fast_eval_exp_impl F b (fextend_env ρ n) (fextend_env_ok _ _ _ _ Hρ (proj2 Hn))
                         (app_cod_order_cod _ _ _ _ _ H _ (proj1 Hn)) in
        exist _ v (conj (or_intror (ex_intro _ n (conj (proj1 Hn) (proj1 Hv)))) (proj2 Hv)) }.

  Lemma typ_val_app_cod_order : forall G P N A B a ρ b,
      ⊢ G -> typ_val_pi G P (fd_pi relevant a ρ b) A B -> G ⊢a N ⟸ A ->
      app_cod_order G P N ρ b.
  Proof.
    intros * HG Hv HN.
    destruct (typ_val_app_order _ _ _ _ _ _ _ _ HG Hv HN) as [Ho1 Ho2].
    constructor; [ exact Ho1 | exact Ho2 |].
    intros Ef; apply exp_freshb_sound in Ef.
    destruct P as [p' Hp']; destruct Hv as [i p a1 v0 Hp Hag HT HA Ha1 Hv0 [Hs _]]; cbn in *.
    assert (HN' : G ⊢ N : A) by (eapply alg_type_check_sound; eassumption).
    destruct (eval_of_typing _ _ _ _ _ Hp HN' HA) as [n Hn].
    inversion Hs; subst.
    destruct (typ_val_pi_step _ _ _ _ _ _ _ _ _ _ _ Hp HT HA Ha1 Hv0 HN' Hn) as (v1 & c & Hv1 & _).
    match goal with Hρ0 : forall x : nat, ~ exp_fresh (S x) _ -> _ |- _ =>
      destruct (fast_eval_clo_unread _ _ _ _ _ _ 𝕌ω@0 _ Hρ0 Ef Hv1) as (v1' & Hv1' & _) end.
    eapply fast_eval_exp_order_sound; exact Hv1'.
  Qed.

  Lemma typ_val_app_cod_step : forall G P M N A B a ρ b v,
      ⊢ G -> G ⊢a M ⟹ Πⁿ A B -> typ_val_pi G P (fd_pi relevant a ρ b) A B -> G ⊢a N ⟸ A ->
      app_cod_val G P N ρ b v -> fdomain_ok gc_deps gc_stack v ->
      exists T, G ⊢a M $ N ⟹ T /\ typ_val G P v T.
  Proof.
    intros * HG HM Hv HN [(Ef & Hv') | (n & Hn' & Hv')] Hok; [| eapply typ_val_app_step; eassumption ].
    apply exp_freshb_sound in Ef.
    destruct P as [p' Hp']; destruct Hv as [i p a1 v0 Hp Hag HΠ HA Ha1 Hv0 [Hs _]]; cbn in *.
    assert (HN' : G ⊢ N : A) by (eapply alg_type_check_sound; eassumption).
    destruct (eval_of_typing _ _ _ _ _ Hp HN' HA) as [n0 Hn0].
    inversion Hs; subst.
    destruct (typ_val_pi_step _ _ _ _ _ _ _ _ _ _ _ Hp HΠ HA Ha1 Hv0 HN' Hn0) as (v1 & c & Hv1 & Hc & Hv1c).
    match goal with Hρ0 : forall x : nat, ~ exp_fresh (S x) _ -> _ |- _ =>
      destruct (fast_eval_clo_unread _ _ _ _ _ _ 𝕌ω@0 _ Hρ0 Ef Hv1) as (v1' & Hv1' & Hs1) end.
    rewrite <- (functional_fast_eval_exp _ _ _ _ Hv' Hv1') in Hs1.
    assert (HB : G ▹ A ⊢ B : Typeω@i) by exact (proj2 (wf_pi_inversion' HΠ)).
    assert (HBN : G ⊢ B[Id,,N] : Typeω@i) by mauto 3.
    destruct (soundness_ty HBN) as (W & HW & HeqW).
    destruct (typ_val_conv _ _ _ _ _ _ _ Hp HeqW Hc Hv1c) as (c' & Hc' & Hvc').
    exists W; split; [ econstructor; eassumption |].
    apply (mk_typ_val _ _ _ _ i p c' v1); try assumption; try (split; assumption).
    apply (@wf_type_univ _ _ _ _ i); gen_presups; assumption.
  Qed.

  (** The type of a term as a value, from its normal form. *)
  Lemma typ_val_of_eval : forall G P (T : nf) v,
      G ⊢ᵗ T -> ⟦ T ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase (proj1_sig P) ↘ fdomain_erase v ->
      fdomain_ok gc_deps gc_stack v -> typ_val G P v T.
  Proof.
    intros G [p' (p & Hp & Hag)] * HT Hv Hok; cbn in *.
    destruct (typ_val_self _ _ _ Hp HT) as (a & i & Ha & Haa).
    pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Ha (fast_env_agree_all _ _ _ _ _ Hag)) _ Hv).
    apply (mk_typ_val _ _ _ _ i p a a); try assumption; split; assumption.
  Qed.

  (** The type of a term as a value evaluates. *)
  Lemma typ_val_eval_order : forall G (P : checker_env G) (T : nf),
      G ⊢ᵗ T -> fast_eval_exp_order gc_deps gc_stack T (fenv_erase (proj1_sig P)).
  Proof.
    intros G [p' (p & Hp & Hag)] * HT; cbn in *.
    destruct (typ_val_self _ _ _ Hp HT) as (a & i & Ha & _).
    exact (proj1 (fast_eval_of_ref _ _ _ _ _ _ Ha (fast_env_agree_all _ _ _ _ _ Hag))).
  Qed.

  (** Whether a term is an application, and a value a [Π]. *)
  #[derive(equations=no,eliminator=no)]
  Equations get_app_parts (M : exp) : { M1 & { N1 | M = M1 $ N1 } } + { forall M1 N1, M <> M1 $ N1 } :=
  | M1 $ N1 => pureo (existT _ M1 (exist _ N1 _))
  | _       => inright _
  .

  #[derive(equations=no,eliminator=no)]
  Equations get_pi_val (v : fdomain) : { r & { a & { ρ & { b | v = fd_pi r a ρ b } } } } + { forall r a ρ b, v <> fd_pi r a ρ b } :=
  | fd_pi r a ρ b => pureo (existT _ r (existT _ a (existT _ ρ (exist _ b _))))
  | _        => inright _
  .

  (** Whether an application steps through the codomain closure: the [Π]
      and its domain are relevant. *)
  Definition both_relevant_dec (r r' : relevance) : { r = relevant /\ r' = relevant } + { ~ (r = relevant /\ r' = relevant) }.
  Proof.
    destruct r, r'; first [ left; split; reflexivity | right; intros [? ?]; discriminate ].
  Defined.

  Extraction Inline get_app_parts get_pi_val both_relevant_dec.

  (** ** Obligations of the Refined Cases *)

  (** The parts of the [Π] value an application's head has as its type. *)
  #[local]
  Ltac obligation_pi_parts :=
    match goal with
    | HG : ⊢ ?G, HM : ?G ⊢a ?M ⟹ ?T, Hv : typ_val ?G ?P (fd_pi ?r ?a ?ρ ?b) ?T |- _ =>
        let A0 := fresh "A0" in let B0 := fresh "B0" in
        destruct (typ_val_pi_parts _ _ _ _ _ _ _ _ HG HM Hv) as (A0 & B0 & -> & ?)
    end;
    functional_fast_read_rewrite_clear.

  (** The failure of the side condition of [type_check_in]: the inferred
      type is its own normal form, so the judgment would compare the same
      two normal forms. *)
  #[local]
  Ltac obligation_check_nf_failure :=
    match goal with H : _ ⊢a _ ⟸ _ |- False => inversion H; subst; clear H end;
    match goal with H : _ ⊢a _ ⊆ _ |- _ => inversion H; subst; clear H end;
    functional_alg_type_infer_rewrite_clear;
    match goal with
    | Hn : nbe_ty_f ?G (nf_to_exp ?B) ?B', HM : ?G ⊢a _ ⟹ ?B, HA : ?G ⊢ᵗ _ |- _ =>
        assert (B = B') as <- by (eapply alg_type_infer_normal; [ eapply checker_env_ctx_of_typ; exact HA | exact HM | exact Hn ])
    end;
    functional_nbe_rewrite_clear;
    contradiction.

  (** Its success: the rule [alg_type_check_ati], with the inferred type as its own
      normal form. *)
  #[local]
  Ltac obligation_check_nf :=
    match goal with HM : ?G ⊢a ?M ⟹ ?B, HA : ?G ⊢ᵗ _, Hs : ⊢anf ?B ⊆ _ |- ?G ⊢a ?M ⟸ _ =>
      assert (nbe_ty_f G B B) by (eapply alg_type_infer_self; [ eapply checker_env_ctx_of_typ; exact HA | exact HM ])
    end;
    econstructor; [ eassumption | econstructor; eassumption ].

  (** A step by the rule: the head's type, as a value, read back to the
      [Π] or [∀] normal form it stands for, its domain the checked one. *)
  #[local]
  Ltac spine_rule_prelude :=
    match goal with HG : ⊢ ?G, Hi : ?G ⊢a ?M ⟹ ?T, Hv : typ_val ?G _ (fd_pi _ _ _ _) ?T |- _ =>
      pose proof (typ_val_rtyp _ _ _ _ _ HG Hi Hv);
      let Hv' := fresh "Hv" in pose proof Hv as Hv'; destruct Hv'
    end;
    cbn [fdomain_erase] in *; functional_fast_read_rewrite_clear; subst;
    match goal with Hr : Rtypᶠ d_pi _ _ _ _ in _ ⍮ _ ⍮ _ ↘ nf_pi _ _ _ |- _ => inversion Hr; subst end;
    functional_fast_read_rewrite_clear.

  (** The obligations of the application spine, then those the reference
      checker has too ([checker_obligation]). *)
  #[local]
  Ltac spine_obligation :=
    program_simplify; intros; cbv beta; repeat match goal with |- ~ _ => intro end;
    clear_defs; destruct_conjs; try subst; cbn [fdomain_erase] in *; checker_unify;
    lazymatch goal with
    (** The type of an application's head is no [Π] *)
    | Hn : forall r a ρ b, ?v <> fd_pi r a ρ b, H' : ?G ⊢a ?M $ _ ⟹ _, HG : ⊢ ?G |- False =>
        inversion H'; subst; clear H';
        functional_alg_type_infer_rewrite_clear;
        match goal with Hi : G ⊢a M ⟹ ?T, Hv : typ_val G _ v ?T |- _ =>
          let Hr := fresh "Hr" in pose proof (typ_val_rtyp _ _ _ _ _ HG Hi Hv) as Hr;
          destruct v; cbn [fdomain_erase] in Hr; inversion Hr; subst; eapply Hn; reflexivity
        end
    (** A [Π] value reads back to a [Π] *)
    | Hr : Rtypᶠ d_pi _ _ _ _ in _ ⍮ _ ⍮ _ ↘ ?T, Hn : forall r B C, ?T <> nf_pi r B C |- False =>
        inversion Hr; subst; eapply Hn; reflexivity
    (** The type of an application: the spine's value read back *)
    | HG : ⊢ ?G, Hi : ?G ⊢a ?M ⟹ ?T, Hv : typ_val ?G _ ?v ?T,
      Hr : Rtypᶠ fdomain_erase ?v in _ ⍮ _ ⍮ _ ↘ ?W |- ?G ⊢a ?M ⟹ ?W /\ _ =>
        pose proof (typ_val_rtyp _ _ _ _ _ HG Hi Hv); functional_fast_read_rewrite_clear;
        destruct Hv; split; [ assumption | apply infer_post_of_type; assumption ]
    (** The argument does not check *)
    | HN : ~ ?G ⊢a ?N ⟸ _, H' : ?G ⊢a _ $ ?N ⟹ _ |- False =>
        obligation_pi_parts; inversion H'; subst; clear H';
        functional_alg_type_infer_rewrite_clear; autoinjections; subst; contradiction
    | |- fast_read_typ_order _ _ _ _ =>
        first [ obligation_pi_parts; eapply fast_read_typ_order_sound; eassumption
              | match goal with HG : ⊢ ?G, Hi : ?G ⊢a _ ⟹ ?T, Hv : typ_val ?G _ ?v ?T |- _ =>
                  eapply fast_read_typ_order_sound; exact (typ_val_rtyp _ _ _ _ _ HG Hi Hv) end ]
    | |- _ ⊢ᵗ _ =>
        obligation_pi_parts;
        match goal with Hv : typ_val _ _ (fd_pi _ _ _ _) _ |- _ =>
          let Hv' := fresh "Hv" in pose proof Hv as Hv'; destruct Hv' end;
        checker_type
    | |- app_cod_order _ _ _ _ _ =>
        obligation_pi_parts; eapply typ_val_app_cod_order; [ eassumption | eapply typ_val_pi_of; eassumption | eassumption ]
    | |- exists T, _ ⊢a _ $ _ ⟹ T /\ typ_val _ _ _ T =>
        first [ obligation_pi_parts;
                eapply typ_val_app_cod_step; [ eassumption | eassumption | eapply typ_val_pi_of; eassumption
                                            | eassumption | eassumption | eassumption ]
              (** By the rule *)
              | spine_rule_prelude;
                match goal with Hn : nbe_ty _ _ ?G ?X ?W |- exists T, ?G ⊢a _ $ _ ⟹ T /\ _ =>
                  assert (G ⊢ᵗ X) by checker_type;
                  eexists; split; [ eapply alg_type_infer_app; eassumption
                                  | eapply typ_val_of_eval; [ checker_type | eassumption | eassumption ] ]
                end ]
    (** An application's head, as a value, from its type's normal form *)
    | |- exists T, _ ⊢a _ ⟹ T /\ typ_val _ _ _ T =>
        eexists; split; [ eassumption | eapply typ_val_of_eval; [ checker_type | eassumption | eassumption ] ]
    | |- nbe_ty_order _ _ _ _ => spine_rule_prelude; apply nbe_order_of_type; checker_type
    | |- fast_eval_exp_order _ _ _ _ =>
        first [ eapply typ_val_eval_order; checker_type
              | spine_rule_prelude;
                match goal with Hn : nbe_ty _ _ ?G ?X ?W |- fast_eval_exp_order _ _ (nf_to_exp ?W) _ =>
                  assert (G ⊢ᵗ X) by checker_type; eapply typ_val_eval_order; checker_type
                end ]
    (** The check of [type_check_in], against the checked type's normal form *)
    | |- _ ⊢a _ ⟸ _ => obligation_check_nf
    | H : ~ ⊢anf _ ⊆ _ |- False => obligation_check_nf_failure
    end.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations type_check_in G A (HA : G ⊢ᵗ A) (P : checker_env G) M (H : type_check_order M) : { G ⊢a M ⟸ A } + { ~ G ⊢a M ⟸ A } by struct H :=
  | G, A, HA, P, M, H =>
      let*o->b (exist _ B _) := type_infer_in G _ P M _ while _ in
      let (A', _) := nbe_ty_env_impl F G P A _ in
      let*b _ := subtyping_nf_impl B A' while _ in
      pureb _
  with type_infer_in G (HG : ⊢ G) (P : checker_env G) M (H : type_infer_order M) :
      { A : nf | G ⊢a M ⟹ A /\ (exists UA r u, G ⊢a A ⟹ UA /\ is_sort_nf UA r u) /\ G ⊢ᵗ A } + { forall A, ~ G ⊢a M ⟹ A } by struct H :=
  | G, HG, P, M, H with M => {
    | Typeω@j =>
        pureo (exist _ Typeωⁿ@(S j) _)
    | Type⟨M'⟩ =>
        let*o (exist _ LM _) := type_infer_in G _ P M' _ while _ in
        let*o (exist _ k _) := get_level_sort_nf LM while _ in
        let (W, _) := nbe_ty_env_impl F G P Type⟨succl M'⟩ _ in
        pureo (exist _ W _)
    | Level@k =>
        pureo (exist _ Typeⁿ@0 _)
    | 𝕃ᵒ m =>
        pureo (exist _ Levelⁿ@(fst m) _)
    | succl M' =>
        let*o (exist _ LM _) := type_infer_in G _ P M' _ while _ in
        let*o (exist _ k _) := get_level_sort_nf LM while _ in
        pureo (exist _ Levelⁿ@k _)
    | maxl M' N' =>
        let*o (exist _ LM _) := type_infer_in G _ P M' _ while _ in
        let*o (exist _ k _) := get_level_sort_nf LM while _ in
        let*o (exist _ LN _) := type_infer_in G _ P N' _ while _ in
        let*o (exist _ k' _) := get_level_sort_nf LN while _ in
        pureo (exist _ Levelⁿ@(Nat.max k k') _)
    (** [Prop] and the closed propositions *)
    | Propₘ =>
        pureo (exist _ Typeⁿ@0 _)
    | ⊤ =>
        pureo (exist _ Propⁿ _)
    | ⋆ =>
        pureo (exist _ ⊤ⁿ _)
    | ⊥ =>
        pureo (exist _ Propⁿ _)
    (** Ex falso: the target is a type of either sort, the proof is checked
        at [⊥] *)
    | efq M' return C' =>
        let*o (exist _ UC _) := type_infer_in G _ P C' _ while _ in
        let*o (existT _ rC (exist _ uC _)) := sort_nf_dec UC while _ in
        let*b->o _ := type_check_in G ⊥ _ P M' _ while _ in
        let (C'', _) := nbe_ty_env_impl F G P C' _ in
        pureo (exist _ C'' _)
    (** A conjunction of two propositions *)
    | Σₚ P' Q' =>
        let*o (exist _ UP _) := type_infer_in G _ P P' _ while _ in
        let*b->o _ := prop_nf_dec UP while _ in
        let HGP : ⊢ G ▹ P' := _ in
        let*o (exist _ UQ _) := type_infer_in (G ▹ P') HGP (checker_env_ass F G P P' HGP) Q' _ while _ in
        let*b->o _ := prop_nf_dec UQ while _ in
        pureo (exist _ Propⁿ _)
    (** A proof of a conjunction: the annotation is a proposition whose
        normal form is a conjunction, and the components check at its parts *)
    | a_conj T' M' N' =>
        let*o (exist _ UT _) := type_infer_in G _ P T' _ while _ in
        let*b->o _ := prop_nf_dec UT while _ in
        let (W, _) := nbe_ty_env_impl F G P T' _ in
        let*o (existT _ Pc (exist _ Qc _)) := get_and_nf W while _ in
        let*b->o _ := type_check_in G (Pc : nf) _ P M' _ while _ in
        let*b->o _ := type_check_in G (Qc : nf)[Id,,M'] _ P N' _ while _ in
        pureo (exist _ (Σₚⁿ Pc Qc) _)
    (** The components of a proof of a conjunction *)
    | a_left M' =>
        let*o (exist _ T _) := type_infer_in G _ P M' _ while _ in
        let*o (existT _ Pc (exist _ Qc _)) := get_and_nf T while _ in
        pureo (exist _ Pc _)
    | a_right M' =>
        let*o (exist _ T _) := type_infer_in G _ P M' _ while _ in
        let*o (existT _ Pc (exist _ Qc _)) := get_and_nf T while _ in
        let (W, _) := nbe_ty_env_impl F G P (Qc : nf)[Id,,a_left M'] _ in
        pureo (exist _ W _)
    (** The placeholder type and its element *)
    | a_placeholder_type =>
        pureo (exist _ Typeⁿ@0 _)
    | a_placeholder =>
        pureo (exist _ nf_placeholder_type _)
    (** A [Π] over a type of either sort *)
    | Π B C =>
        let*o (exist _ UB _) := type_infer_in G _ P B _ while _ in
        let*o (existT _ rB (exist _ u _)) := sort_nf_dec UB while _ in
        let HGB : ⊢ G ▹ B := _ in
        let*o (exist _ UC _) := type_infer_in (G ▹ B) HGB (checker_env_ass F G P B HGB) C _ while _ in
        let (UC', _) := nbe_ty_env_impl F (G ▹ B) (checker_env_ass F G P B HGB) UC _ in
        let*o (exist _ v _) :=  univ_nf_idx_dec UC' while _ in
        let (W, _) := nbe_ty_env_impl F G P (universe_nf_pi_tm u v) _ in
        pureo (exist _ W _)
    (** A [∀]: over a type of either sort, into propositions *)
    | ∀ₚ B C =>
        let*o (exist _ UB _) := type_infer_in G _ P B _ while _ in
        let*o (existT _ rB (exist _ u _)) := sort_nf_dec UB while _ in
        let HGB : ⊢ G ▹ B := _ in
        let*o (exist _ UC _) := type_infer_in (G ▹ B) HGB (checker_env_ass F G P B HGB) C _ while _ in
        let*b->o _ := prop_nf_dec UC while _ in
        pureo (exist _ Propⁿ _)
    (** The forms of inductive types ([Extraction.IndCheck]); the
        eliminator's recursive calls are passed on. *)
    | a_ind pq k => ind_infer F G HG P pq k
    | a_con pq k c => con_infer F G HG P pq k c
    (** The forms of record types ([Extraction.RecordCheck]); the
        recursive calls on a tuple's parts and a projection's element are
        passed on. *)
    | a_record pq => record_infer F G HG P pq
    | a_tuple T' fs =>
        tuple_infer F G HG P T' fs (type_infer_in G HG P T' ltac:(obligation_order_record))
          (fun fm Hfm A'' HA'' => type_check_in G A'' HA'' P (snd fm) ltac:(obligation_order_record))
    | a_proj f M' => proj_infer F G HG P f M' (type_infer_in G HG P M' ltac:(obligation_order_record))
    | a_nlit n => inright (fun A HA => alg_nlit_no_infer G n A HA)
    | a_ntok => inright (fun A HA => alg_ntok_no_infer G A HA)
    | a_elim r oq Us m Bks M' =>
        elim_infer F G HG P r oq Us m Bks M'
          (type_infer_in G HG P M' ltac:(obligation_order_elim))
          (fun U HU G' A'' HA'' P' => type_check_in G' A'' HA'' P' U ltac:(obligation_order_elim))
          (fun b Z Hb HZ G' HG' P' => type_infer_in G' HG' P' Z ltac:(obligation_order_elim))
          (fun b Hb G' HG' P' => type_infer_in G' HG' P' (eb_motive b) ltac:(obligation_order_elim))
          (fun b br Hb Hbr G' A'' HA'' P' => type_check_in G' A'' HA'' P' (snd br) ltac:(obligation_order_elim))
    (** A λ over a type of either sort: a function, or a proof of a [∀], by
        the sort of its body's type *)
    | λ A' M' =>
        let*o (exist _ UA' _) := type_infer_in G _ P A' _ while _ in
        let*o (existT _ rA (exist _ u _)) := sort_nf_dec UA' while _ in
        let HGA : ⊢ G ▹ A' := _ in
        let*o (exist _ B' _) := type_infer_in (G ▹ A') HGA (checker_env_ass F G P A' HGA) M' _ while _ in
        let (r, _) := checker_relevance F (G ▹ A') (checker_env_ass F G P A' HGA) B' _ in
        let (A'', _) := nbe_ty_env_impl F G P A' _ in
        pureo (exist _ (nf_pi r A'' B') _)
    (** An application: the type of the spine as a value, read back *)
    | M' $ N' =>
        let*o (exist _ v Hv) := type_infer_app_in G HG P M' N' _ while _ in
        let (W, _) := fast_read_typ_impl F (List.length G) v (typ_val_ok_of _ _ _ _ Hv) _ in
        pureo (exist _ W _)
    | ℓ A' ≔ M' in B' =>
        let*o (exist _ UA' _) := type_infer_in G _ P A' _ while _ in
        let*o (existT _ rA (exist _ u _)) := sort_nf_dec UA' while _ in
        let*b->o _ := type_check_in G A' _ P M' _ while _ in
        let HGD : ⊢ G ▸ A' ≔ M' := _ in
        let*o (exist _ C _) := type_infer_in (G ▸ A' ≔ M') HGD (checker_env_def F G P A' M' HGD) B' _ while _ in
        let (D, _) := nbe_ty_env_impl F G P (C : nf)[Id,,M'] _ in
        pureo (exist _ D _)
    (** Without an annotation, the definiens's type is inferred, and is a
        relevant type. *)
    | ℓ ≔ M' in B' =>
        let*o (exist _ A _) := type_infer_in G _ P M' _ while _ in
        let (r, _) := checker_relevance F G P (A : nf) _ in
        let*b->o _ := relevance_eq_dec r relevant while _ in
        let HGD : ⊢ G ▸ (A : nf) ≔ M' := _ in
        let*o (exist _ C _) := type_infer_in (G ▸ (A : nf) ≔ M') HGD (checker_env_def F G P (A : nf) M' HGD) B' _ while _ in
        let (D, _) := nbe_ty_env_impl F G P (C : nf)[Id,,M'] _ in
        pureo (exist _ D _)
    | ℓₘ U in B' =>
        let*b->o _ := unit_check G HG U _ while _ in
        let HGU : ⊢ G ▹ₘ U := _ in
        let*o (exist _ C _) := type_infer_in (G ▹ₘ U) HGU (checker_env_mod F G P U HGU) B' _ while _ in
        let (D, _) := nbe_ty_env_impl F G P (C : nf)[Id ,,ₘ me_lit U] _ in
        pureo (exist _ D _)
    (** A member infers the normal form of the type that the description of
        its module reads. *)
    | a_mem M' x =>
        let*b->o HM := modexp_check G HG M' _ while _ in
        let*o (exist _ R _) := mem_denote_dec F _ G M' x _ while _ in
        let*o (exist _ A _) := mdesc_type_dec R while _ in
        let (B, _) := nbe_ty_env_impl F G P A _ in
        pureo (exist _ B _)
    | #x =>
        let*o (exist _ A _) := lookup F G _ x while _ in
        let (A', _) := nbe_ty_env_impl F G P A _ in
        pureo (exist _ A' _)
    }
  with ext_check G (HG : ⊢ G) Ψ (H : ext_order Ψ) : { G ⊢aˣ Ψ } + { ~ G ⊢aˣ Ψ } by struct H :=
  | G, HG, nil, H => left _
  (** An assumption of a type of either sort *)
  | G, HG, ce_ass A :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let HΨ : ⊢ Ψ ++ G := _ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ (checker_env_of F (Ψ ++ G) HΨ) A _ while _ in
      let*o->b (existT _ rA (exist _ u _)) := sort_nf_dec UA while _ in
      pureb _
  (** A definition of a type of either sort *)
  | G, HG, ce_def A M :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let HΨ : ⊢ Ψ ++ G := _ in
      let PΨ := checker_env_of F (Ψ ++ G) HΨ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ PΨ A _ while _ in
      let*o->b (existT _ rA (exist _ u _)) := sort_nf_dec UA while _ in
      let*b _ := type_check_in (Ψ ++ G) A _ PΨ M _ while _ in
      pureb _
  | G, HG, ce_mod U :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let*b _ := unit_check (Ψ ++ G) _ U _ while _ in
      pureb _
  (** A definition with a module part: as a definition, then its unit. *)
  | G, HG, ce_dm A M U :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let HΨ : ⊢ Ψ ++ G := _ in
      let PΨ := checker_env_of F (Ψ ++ G) HΨ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ PΨ A _ while _ in
      let*o->b (exist _ u _) := univ_nf_idx_dec UA while _ in
      let*b _ := type_check_in (Ψ ++ G) A _ PΨ M _ while _ in
      let*b _ := unit_check (Ψ ++ G) HΨ U _ while _ in
      pureb _
  (** The parameters of a unit: assumptions of types of universes. *)
  with params_check G (HG : ⊢ G) Δ (H : ext_order Δ) : { G ⊢aᵖ Δ } + { ~ G ⊢aᵖ Δ } by struct H :=
  | G, HG, nil, H => left _
  | G, HG, ce_ass A :: Δ, H =>
      let*b _ := params_check G HG Δ _ while _ in
      let HΔ : ⊢ Δ ++ G := _ in
      let*o->b (exist _ UA _) := type_infer_in (Δ ++ G) HΔ (checker_env_of F (Δ ++ G) HΔ) A _ while _ in
      let*o->b (exist _ u _) := univ_nf_idx_dec UA while _ in
      pureb _
  | G, HG, _ :: Δ, H => right _
  with unit_check G (HG : ⊢ G) U (H : unit_order U) : { G ⊢aᵘ U } + { ~ G ⊢aᵘ U } by struct H :=
  | G, HG, gu_mk Δ (md_body sm_closed Φ), H => right (alg_unit_closed_no G Δ Φ)
  | G, HG, gu_mk Δ (md_body sm_open Φ), H =>
      let*b _ := params_check G HG Δ _ while _ in
      let*b _ := tele_ass_dec Δ while _ in
      let*o->b (exist _ Φx _) := body_check (Δ ++ G) _ Φ _ while _ in
      let*b _ := body_shape_dec Φ Φ while _ in
      let*b _ := body_shape_dec Φx Φx while _ in
      let*b _ := names_nodup_dec (gm_names Φ) while _ in
      pureb _
  | G, HG, gu_mk Δ (md_alias E), H =>
      let*b _ := params_check G HG Δ _ while _ in
      let*b _ := tele_ass_dec Δ while _ in
      let*b _ := modexp_check (Δ ++ G) _ E _ while _ in
      pureb _
  with modexp_check G (HG : ⊢ G) M (H : modexp_order M) : { G ⊢aᵐ M } + { ~ G ⊢aᵐ M } by struct H :=
  | G, HG, me_unit fp, H =>
      let*o->b (exist _ R _) := path_denote_dec F _ G fp while _ in
      let*o->b (exist _ T _) := mdesc_mod_tele_dec R while _ in
      pureb _
  | G, HG, me_var x, H with inspect (ctx_find_mod G x) := {
    | exist _ (Some U) E => left _
    | exist _ None E => right _ }
  | G, HG, me_lit U, H =>
      let*b _ := unit_check G HG U _ while _ in
      pureb _
  | G, HG, me_mem M y, H =>
      let*b HM := modexp_check G HG M _ while _ in
      let*o->b (exist _ R _) := mem_denote_dec F _ G M y _ while _ in
      let*o->b (exist _ T _) := mdesc_mod_tele_dec R while _ in
      pureb _
  | G, HG, me_app M N, H =>
      let*b HM := modexp_check G HG M _ while _ in
      let*o->b (exist _ R _) := mdenote_dec F _ G M _ while _ in
      let*o->b (exist _ T _) := mdesc_mod_tele_dec R while _ in
      let*o->b (existT _ B (exist _ T1 _)) := tele_view_dec T while _ in
      let*b _ := type_check_in G B _ (checker_env_of F G HG) N _ while _ in
      pureb _
  (** The type of an application [M $ N], as a value.  A step of a [Π] over
      a relevant domain instantiates the codomain closure with the
      argument's value; any other, the argument a proof, is the rule's. *)
  with type_infer_app_in G (HG : ⊢ G) (P : checker_env G) M N (H : app_order M N) :
      { v : fdomain | exists T, G ⊢a M $ N ⟹ T /\ typ_val G P v T } + { forall A, ~ G ⊢a M $ N ⟹ A } by struct H :=
  | G, HG, P, M, N, H =>
      let*o (exist _ v Hv) := type_infer_val_in G HG P M _ while _ in
      let*o (existT _ r (existT _ a (existT _ ρ' (exist _ b Eb)))) := get_pi_val v while _ in
      let (A, _) := fast_read_typ_impl F (List.length G) a (typ_val_pi_dom_ok _ _ _ _ _ _ _ _ Hv Eb) _ in
      let*b->o _ := type_check_in G (A : nf) _ P N _ while _ in
      let (rA, _) := checker_relevance F G P (A : nf) _ in
      match both_relevant_dec r rA with
      | left Er =>
          let (v', _) := app_cod G P N ρ' b (typ_val_pi_env_ok _ _ _ _ _ _ _ _ Hv Eb) _ in
          pureo (exist _ v' _)
      | right _ =>
          let (T, _) := fast_read_typ_impl F (List.length G) v (typ_val_ok_of _ _ _ _ Hv) _ in
          let*o (existT _ rT (existT _ AT (exist _ BT _))) := get_pi_nf T while _ in
          let (W, _) := nbe_ty_env_impl F G P (BT : nf)[Id,,N] _ in
          let (v', _) := fast_eval_exp_impl F W (proj1_sig P) (checker_env_ok G (proj1_sig P) (proj2_sig P)) _ in
          pureo (exist _ v' _)
      end
  (** The type of the head of an application, as a value: an application's
      directly, any other term's by evaluating its normal form. *)
  with type_infer_val_in G (HG : ⊢ G) (P : checker_env G) M (H : type_check_order M) :
      { v : fdomain | exists T, G ⊢a M ⟹ T /\ typ_val G P v T } + { forall A, ~ G ⊢a M ⟹ A } by struct H :=
  | G, HG, P, M, H with get_app_parts M => {
    | inleft (existT _ M1 (exist _ N1 _)) =>
        let*o (exist _ v _) := type_infer_app_in G HG P M1 N1 _ while _ in
        pureo (exist _ v _)
    | inright _ =>
        let*o (exist _ T _) := type_infer_in G HG P M _ while _ in
        let (v, _) := fast_eval_exp_impl F T (proj1_sig P) (checker_env_ok G (proj1_sig P) (proj2_sig P)) _ in
        pureo (exist _ v _) }
  (** A body, entry by entry, as the entries its opens generate: each in the
      context of the expanded body before it. *)
  with body_check G (HG : ⊢ G) Φ (H : body_order Φ) :
      { Φx | G ⊢aᵇ Φ ⇝ Φx /\ ⊢ body_ctx Φx ++ G } + { forall Φx, ~ G ⊢aᵇ Φ ⇝ Φx } by struct H :=
  | G, HG, gm_nil, H => inleft (exist _ gm_nil _)
  (** A definition, of a type of the sort its tag says *)
  | G, HG, gm_ext Φ x (ge_def b pv r A (Some M)), H =>
      let*o (exist _ Φx _) := body_check G HG Φ _ while _ in
      let HGx : ⊢ body_ctx Φx ++ G := _ in
      let*o (exist _ UA _) := type_infer_in (body_ctx Φx ++ G) HGx (checker_env_of F _ HGx) A _ while _ in
      let*o (existT _ rA (exist _ u _)) := sort_nf_dec UA while _ in
      let*b->o _ := relevance_eq_dec rA r while _ in
      let*b->o _ := type_check_in (body_ctx Φx ++ G) A _ (checker_env_of F _ HGx) M _ while _ in
      pureo (exist _ (gm_ext Φx x (ge_def b pv r A (Some M))) _)
  | G, HG, gm_ext Φ x (ge_mod pm U), H =>
      let*o (exist _ Φx _) := body_check G HG Φ _ while _ in
      let*b->o _ := unit_check (body_ctx Φx ++ G) _ U _ while _ in
      pureo (exist _ (gm_ext Φx x (ge_mod pm U)) _)
  (** A definition with a module part: its term part as a definition, then
      its unit. *)
  | G, HG, gm_ext Φ x (ge_def_mod pv A M U), H =>
      let*o (exist _ Φx _) := body_check G HG Φ _ while _ in
      let HGx : ⊢ body_ctx Φx ++ G := _ in
      let*o (exist _ UA _) := type_infer_in (body_ctx Φx ++ G) HGx (checker_env_of F _ HGx) A _ while _ in
      let*o (exist _ u _) := univ_nf_idx_dec UA while _ in
      let*b->o _ := type_check_in (body_ctx Φx ++ G) A _ (checker_env_of F _ HGx) M _ while _ in
      let*b->o _ := unit_check (body_ctx Φx ++ G) HGx U _ while _ in
      pureo (exist _ (gm_ext Φx x (ge_def_mod pv A M U)) _)
  | G, HG, gm_ext Φ x E, H => inright _
  | G, HG, gm_open Φ M its, H =>
      let*o (exist _ Φx _) := body_check G HG Φ _ while _ in
      let*b->o HM := modexp_check (body_ctx Φx ++ G) _ M _ while _ in
      let*o (exist _ R _) := mdenote_dec F _ (body_ctx Φx ++ G) M _ while _ in
      let*o (exist _ Rm _) := mdesc_mod_dec R while _ in
      let*o (exist _ gs _) := items_gen_dec F _ (body_ctx Φx ++ G) M its _ while _ in
      let*b->o _ := items_ok_dec its while _ in
      pureo (exist _ (gens_append Φx 0 gs) _)
  .
  Solve All Obligations with first [ solve [ spine_obligation ] | checker_obligation ].

  Extraction Inline type_check_in_functional type_infer_in_functional ext_check_functional
    params_check_functional unit_check_functional body_check_functional modexp_check_functional.

  (** The checker from scratch: the initial environment of the context is
      computed once, at the start. *)
  Definition type_check G A (HA : G ⊢ᵗ A) M (H : type_check_order M) :
      { G ⊢a M ⟸ A } + { ~ G ⊢a M ⟸ A } :=
    type_check_in G A HA (checker_env_of F G (checker_env_ctx_of_typ _ _ HA)) M H.

  Definition type_infer G (HG : ⊢ G) M (H : type_infer_order M) :
      { A : nf | G ⊢a M ⟹ A /\ (exists UA r u, G ⊢a A ⟹ UA /\ is_sort_nf UA r u) /\ G ⊢ᵗ A } +
      { forall A, ~ G ⊢a M ⟹ A } :=
    type_infer_in G HG (checker_env_of F G HG) M H.

  Lemma type_infer_order_soundness : forall G M A,
      G ⊢a M ⟹ A ->
      type_infer_order M.
  Proof. intros; apply type_infer_order_all. Qed.

  Lemma type_check_order_soundness : forall G M A,
      G ⊢a M ⟸ A ->
      type_check_order M.
  Proof. intros; constructor; apply type_infer_order_all. Qed.
End type_check.

#[local]
Hint Resolve type_check_order_soundness type_infer_order_soundness : mctt.

Lemma type_check_complete' : forall G M A (HA : G ⊢ᵗ A),
    G ⊢a M ⟸ A ->
    exists H H', type_check G A HA M H = left H'.
Proof.
  intros ? ? ? ? ?.
  assert (Horder : type_check_order M) by mauto.
  exists Horder.
  decision_complete.
Qed.

Lemma type_infer_complete : forall G M A (HG : ⊢ G),
    G ⊢a M ⟹ A ->
    exists H H', type_infer G HG M H = inleft (exist _ A H').
Proof.
  intros.
  assert (Horder : type_infer_order M) by mauto.
  exists Horder.
  destruct (type_infer G HG M Horder) as [[? []] |].
  - functional_alg_type_infer_rewrite_clear.
    eexists; reflexivity.
  - contradict H; intuition.
Qed.

Lemma ext_check_complete : forall G Ψ (HG : ⊢ G),
    G ⊢aˣ Ψ ->
    exists H H', ext_check G HG Ψ H = left H'.
Proof.
  intros * HΨ.
  exists (ext_order_all Ψ); destruct (ext_check G HG Ψ (ext_order_all Ψ)); [ eexists; reflexivity | contradiction ].
Qed.

Lemma unit_check_complete : forall G U (HG : ⊢ G),
    G ⊢aᵘ U ->
    exists H H', unit_check G HG U H = left H'.
Proof.
  intros * HU; exists (unit_order_all U).
  destruct (unit_check G HG U (unit_order_all U)); [ eexists; reflexivity | contradiction ].
Qed.

Lemma modexp_check_complete : forall G M (HG : ⊢ G),
    G ⊢aᵐ M ->
    exists H H', modexp_check G HG M H = left H'.
Proof.
  intros * HM; exists (modexp_order_all M).
  destruct (modexp_check G HG M (modexp_order_all M)); [ eexists; reflexivity | contradiction ].
Qed.

Section type_check_closed.
  #[local]
  Ltac impl_obligation_tac :=
    unfold not in *;
    intros;
    mauto 3 using user_exp_to_type_infer_order, type_check_order, type_infer_order.

  (** A closed term at a closed type of either sort. *)
  #[tactic="impl_obligation_tac",derive(equations=no,eliminator=no)]
  Equations type_check_closed (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) A (HA : user_exp A) M (HM : user_exp M) : { ⋅ ⊢ M : A } + { ~ ⋅ ⊢ M : A } :=
  | Hg, A, HA, M, HM =>
      let*o->b (exist _ UA _) := type_infer ⋅ _ A _ while _ in
      let*o->b (existT _ r (exist _ u _)) := sort_nf_dec UA while _ in
      let*b _ := type_check ⋅ A _ M _ while _ in
      pureb _
  .
  Next Obligation. (* False: the type infers no sort *)
    assert (⊢ ⋅) by mauto 2.
    match goal with HM' : ⋅ ⊢ M : A |- _ => destruct (presup_exp_typ HM') as [S HS HA'] end.
    destruct (alg_type_check_sort_infer ltac:(eassumption) HS (alg_type_check_complete HA HA')) as (UA' & r' & u' & HUA' & _).
    firstorder.
  Qed.
  Next Obligation. (* False: the type's inferred type is no sort *)
    assert (⊢ ⋅) by mauto 2.
    match goal with HM' : ⋅ ⊢ M : A |- _ => destruct (presup_exp_typ HM') as [S HS HA'] end.
    destruct (alg_type_check_sort_infer ltac:(eassumption) HS (alg_type_check_complete HA HA')) as (UA' & r' & u' & HUA' & Hs').
    functional_alg_type_infer_rewrite_clear.
    match goal with HN : forall r u, ~ is_sort_nf ?UA r u |- _ => exact (HN _ _ Hs') end.
  Qed.
  Next Obligation. (* ⋅ ⊢ᵗ A *)
    assert (Hemp : ⊢ ⋅) by mauto 2.
    match goal with Ha : ⋅ ⊢a A ⟹ ?UA, Hs : is_sort_nf ?UA _ _ |- _ => exact (type_of_sort_infer _ _ _ _ _ Hemp Ha Hs) end.
  Qed.
  Next Obligation. (* ⋅ ⊢ M : A *)
    assert (Hemp : ⊢ ⋅) by mauto 2.
    match goal with Ha : ⋅ ⊢a A ⟹ ?UA, Hs : is_sort_nf ?UA _ _ |- _ =>
      destruct (type_of_sort_infer _ _ _ _ _ Hemp Ha Hs) as [S HS HA'] end.
    eapply alg_type_check_sound_sort; eassumption.
  Qed.
End type_check_closed.

Lemma type_check_closed_complete : forall (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) A (HA : user_exp A) M (HM : user_exp M),
    ⋅ ⊢ M : A ->
    exists H', type_check_closed Hg A HA M HM = left H'.
Proof. intros; decision_complete. Qed.

(** What an unascribed [eval] needs: a type for a closed term, rather than a
    type to check it against. *)
Section type_infer_closed.
  #[local]
  Ltac impl_obligation_tac :=
    unfold not in *;
    intros;
    destruct_conjs;
    try assert (⊢ ⋅) by mauto 2;
    solve [ mauto 3 using user_exp_to_type_infer_order, alg_type_infer_sound
          | firstorder ].

  #[tactic="impl_obligation_tac",derive(equations=no,eliminator=no)]
  Equations type_infer_closed (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) M (HM : user_exp M) : { A : nf | ⋅ ⊢ M : A } + { forall A, ~ ⋅ ⊢a M ⟹ A } :=
  | Hg, M, HM =>
      let*o (exist _ A _) := type_infer ⋅ _ M _ while _ in
      pureo (exist _ A _)
  .
End type_infer_closed.

(** The same in a well-formed context, for an [eval] inside a module, which
    sees the parameters of its enclosing frames. *)
Section type_infer_at.
  #[local]
  Ltac impl_obligation_tac :=
    unfold not in *;
    intros;
    destruct_conjs;
    solve [ mauto 3 using user_exp_to_type_infer_order, alg_type_infer_sound
          | firstorder ].

  #[tactic="impl_obligation_tac",derive(equations=no,eliminator=no)]
  Equations type_infer_at G (HG : ⊢ G) M (HM : user_exp M) : { A : nf | G ⊢ M : A } + { forall A, ~ G ⊢a M ⟹ A } :=
  | G, HG, M, HM =>
      let*o (exist _ A _) := type_infer G HG M _ while _ in
      pureo (exist _ A _)
  .
End type_infer_at.

End Fixed_GCtx.
