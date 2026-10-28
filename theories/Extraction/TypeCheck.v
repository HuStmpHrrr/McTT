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
      the type of its head ([type_infer_val_in]): each argument instantiates
      the codomain closure of the current [Π] value with the argument's value
      ([type_infer_app_in]), where [alg_type_infer_app] substitutes the argument into the
      normal form of the codomain and normalizes that.  The type of the
      whole spine is read back once, at the end.
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
    ([typ_val_pi]). *)

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

Lemma typ_val_self : forall G ρ X (i : nat),
    initial_env_f G ρ ->
    G ⊢ X : Typeω@i ->
    exists a, ⟦ X ⟧ ρ ↘ a /\ Dom a ≈ a ∈ per_univ i.
Proof.
  intros * Hρ HX.
  destruct (rel_typ_under_ctx_at_initial_env (completeness_fundamental_exp_eq _ _ _ _ (wf_exp_eq_refl HX)))
    as (ρ0 & a & a' & Hρ0 & Ha & Ha' & Haa).
  assert (ρ0 = ρ) as -> by (eapply functional_initial_env; eassumption).
  assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
  exists a; split; assumption.
Qed.

Lemma eval_of_typing : forall G ρ M A,
    initial_env_f G ρ ->
    G ⊢ M : A ->
    exists m, ⟦ M ⟧ ρ ↘ m.
Proof.
  intros * Hρ HM.
  destruct (soundness HM) as (W & HW & _).
  inversion HW; subst.
  functional_initial_env_rewrite_clear.
  eexists; eassumption.
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
    [B[Id,,N]] when [Πᵈ a ρ' b] stands for [Π A B]. *)
Lemma typ_val_pi : forall G ρ A B N (i : nat) a ρ' b a0 n,
    initial_env_f G ρ ->
    G ⊢ Π A B : Typeω@i ->
    ⟦ Π A B ⟧ ρ ↘ a0 ->
    Dom Πᵈ a ρ' b ≈ a0 ∈ per_univ i ->
    G ⊢ N : A ->
    ⟦ N ⟧ ρ ↘ n ->
    exists v c, ⟦ b ⟧ ρ' ↦ n ↘ v /\ ⟦ B[Id,,N] ⟧ ρ ↘ c /\ Dom v ≈ c ∈ per_univ i.
Proof.
  intros * Hρ HΠ Ha0 [R HR] HN Hn.
  assert (G ⊢ A : Typeω@i /\ G ▹ A ⊢ B : Typeω@i) as [HA HB] by mauto 3.
  inversion Ha0; subst.
  assert (HB' : G ▹ A ⊨ B ≈ B : Typeω@i) by (apply completeness_fundamental_exp_eq; mauto 3).
  assert (HN' : G ⊨ N ≈ N : A) by (apply completeness_fundamental_exp_eq; mauto 3).
  pose proof HN' as [env_relΓ HΓr _ _].
  pose proof (per_ctx_then_per_env_initial_env HΓr) as [ρ1 [ρ2 [Hρ1 [Hρ2 Hrel]]]].
  assert (ρ1 = ρ) by (eapply functional_initial_env; eassumption); subst.
  assert (ρ2 = ρ) by (eapply functional_initial_env; eassumption); subst.
  destruct (per_univ_of_instance HΓr HB' HN' _ _ Hrel Hn) as (c & d & Hc & Hd & Hcc & Hcd).
  destruct (rel_exp_under_ctx_at_initial_env HN')
    as (ρ0 & j & elem_rel & aA & n1 & n2 & Hρ0 & HaA & Hn1 & Hn2 & HaAel & Hnn).
  functional_initial_env_rewrite_clear.
  functional_eval_rewrite_clear.
  basic_invert_per_univ_elem HR.
  handle_per_univ_elem_irrel.
  destruct (H0 _ _ Hnn) as [v d' Hv Hd' Hvd].
  functional_eval_rewrite_clear.
  exists v, c; repeat split; try assumption.
  eapply per_univ_trans'; [ eexists; exact Hvd | apply per_univ_sym'; exact Hcd ].
Qed.

(** The last two components of [type_infer_in]'s postcondition, for a type
    that is a type. *)
Lemma infer_post_of_typ : forall G (T : nf) (i : nat),
    G ⊢ T : Typeω@i ->
    (exists UA u, G ⊢a T ⟹ UA /\ is_univ_nf UA u) /\ (exists j : nat, G ⊢ T : Typeω@j).
Proof.
  intros * HT.
  destruct (alg_type_infer_large_typ_complete (user_exp_nf T) HT) as (UA & u & HUA & Hu & _).
  split; [ exists UA, u; split; assumption | exists i; assumption ].
Qed.

Section type_check.
  #[local]
  Hint Constructors type_check_order type_infer_order app_order ext_order unit_order modexp_order : mctt.

  (** The type of a term as a value at the environment [P]: a fast value
      related ([fast_value_simulation]) to one that stands for the normal
      form [T] at the initial environment. *)
  #[warnings="-cannot-define-projection"]
  Record typ_val G (P : tenv G) (v : fdomain) (T : nf) : Prop := mk_typ_val
    { (** The universe level of [T] *)
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
      typ_val_typ : G ⊢ T : Typeω@typ_val_lvl
    ; (** [T]'s value *)
      typ_val_eval : ⟦ T ⟧ typ_val_env ↘ typ_val_sem
    ; (** The reference value is related to it in the universe *)
      typ_val_per : Dom typ_val_rel ≈ typ_val_sem ∈ per_univ typ_val_lvl
    ; (** [v] stands for the reference value *)
      typ_val_sim : fast_value_simulation gc_deps gc_stack typ_val_rel v }.

  (** A type as a value is right. *)
  Lemma typ_val_ok : forall G P v T, typ_val G P v T -> fdomain_ok gc_deps gc_stack v.
  Proof. intros * [_ _ _ _ _ _ _ _ _ [_ Hok]]; exact Hok. Qed.

  (** The same, from a result of the checker *)
  Lemma typ_val_ok_of : forall G P (Q : nf -> Prop) v, (exists T, Q T /\ typ_val G P v T) -> fdomain_ok gc_deps gc_stack v.
  Proof. intros * (T & _ & Hv); eapply typ_val_ok; exact Hv. Qed.

  (** The domain and the environment of a [Π] value, from a result of the
      checker, are right. *)
  Lemma typ_val_pi_dom_ok : forall G P (Q : nf -> Prop) v a ρ b,
      (exists T, Q T /\ typ_val G P v T) -> v = fd_pi a ρ b -> fdomain_ok gc_deps gc_stack a.
  Proof. intros * Hv ->; apply typ_val_ok_of in Hv; inversion Hv; assumption. Qed.

  Lemma typ_val_pi_env_ok : forall G P (Q : nf -> Prop) v a ρ b,
      (exists T, Q T /\ typ_val G P v T) -> v = fd_pi a ρ b -> fenv_ok gc_deps gc_stack ρ.
  Proof. intros * Hv ->; apply typ_val_ok_of in Hv; inversion Hv; assumption. Qed.

  (** A type as a value reads back to the type it stands for. *)
  Lemma typ_val_rtyp : forall G P M v T,
      ⊢ G -> G ⊢a M ⟹ T -> typ_val G P v T -> Rtypᶠ fdomain_erase v in gc_deps ⍮ gc_stack ⍮ (List.length G) ↘ T.
  Proof.
    intros * HG HM [i p a v0 Hp _ HT Ha Hv0 [Hs _]].
    eapply fast_read_typ_sim; [| exact Hs ].
    eapply typ_val_read; [ eassumption | eapply alg_type_infer_self; eassumption | eassumption | eassumption ].
  Qed.

  (** A [Π] value stands for a [Π] normal form. *)
  Lemma typ_val_pi_parts : forall G P M T a ρ b,
      ⊢ G -> G ⊢a M ⟹ T -> typ_val G P (fd_pi a ρ b) T ->
      exists A B (i : nat), T = Πⁿ A B /\ Rtypᶠ fdomain_erase a in gc_deps ⍮ gc_stack ⍮ (List.length G) ↘ A /\ G ⊢ Π A B : Typeω@i.
  Proof.
    intros * HG HM Hv.
    pose proof (typ_val_rtyp _ _ _ _ _ HG HM Hv) as Hr; cbn in Hr.
    inversion Hr; subst.
    destruct Hv as [i _ _ _ _ _ HT _ _ _].
    do 3 eexists; repeat split; eassumption.
  Qed.

  (** The argument of an application, and the codomain closure at its value,
      evaluate. *)
  Lemma typ_val_app_order : forall G P M N A B a ρ b,
      ⊢ G -> G ⊢a M ⟹ Πⁿ A B -> typ_val G P (fd_pi a ρ b) (Πⁿ A B) -> G ⊢a N ⟸ A ->
      fast_eval_exp_order gc_deps gc_stack N (fenv_erase (proj1_sig P)) /\
      forall n', ⟦ N ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase (proj1_sig P) ↘ n' ->
            fast_eval_exp_order gc_deps gc_stack b (fenv_erase ρ ↦ n').
  Proof.
    intros G [p' Hp'] * HG HM [i p a1 v0 Hp Hag HT Ha1 Hv0 [Hs _]] HN; cbn in *.
    assert (G ⊢ A : Typeω@i /\ G ▹ A ⊢ B : Typeω@i) as [HA HB] by mauto 3.
    assert (HN' : G ⊢ N : A) by (eapply alg_type_check_sound; eassumption).
    destruct (eval_of_typing _ _ _ _ Hp HN') as [n Hn].
    destruct (fast_eval_of_ref _ _ _ _ _ _ Hn (fast_env_agree_all _ _ _ _ _ Hag)) as [HoN HsN].
    split; [ exact HoN |].
    intros n' Hn'.
    inversion Hs as [? ? ? ? ? ? Hρ0 | | | | | | | | | | | | | | | | |]; subst.
    destruct (typ_val_pi _ _ _ _ _ _ _ _ _ _ _ Hp HT Ha1 Hv0 HN' Hn) as (v1 & c & Hv1 & _).
    destruct (fast_eval_clo_sim _ _ _ _ _ _ _ _ Hρ0 (HsN _ Hn') Hv1) as (v1' & Hv1' & _).
    eapply fast_eval_exp_order_sound; exact Hv1'.
  Qed.

  (** The value of the type of an application: [alg_type_infer_app]'s type stands for
      the codomain closure applied to the argument's value. *)
  Lemma typ_val_app_step : forall G P M N A B a ρ b n v,
      ⊢ G -> G ⊢a M ⟹ Πⁿ A B -> typ_val G P (fd_pi a ρ b) (Πⁿ A B) -> G ⊢a N ⟸ A ->
      ⟦ N ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase (proj1_sig P) ↘ n ->
      ⟦ b ⟧ᶠ gc_deps ⍮ gc_stack ⍮ (fenv_erase ρ ↦ n) ↘ fdomain_erase v -> fdomain_ok gc_deps gc_stack v ->
      exists T, G ⊢a M $ N ⟹ T /\ typ_val G P v T.
  Proof.
    intros G [p' Hp'] * HG HM [i p a1 v0 Hp Hag HΠ Ha1 Hv0 [Hs _]] HN Hn' Hv' Hok; cbn in *.
    assert (G ⊢ A : Typeω@i /\ G ▹ A ⊢ B : Typeω@i) as [HA HB] by mauto 3.
    assert (HN' : G ⊢ N : A) by (eapply alg_type_check_sound; eassumption).
    destruct (eval_of_typing _ _ _ _ Hp HN') as [n0 Hn0].
    pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Hn0 (fast_env_agree_all _ _ _ _ _ Hag)) _ Hn') as HsN.
    inversion Hs as [? ? ? ? ? ? Hρ0 | | | | | | | | | | | | | | | | |]; subst.
    destruct (typ_val_pi _ _ _ _ _ _ _ _ _ _ _ Hp HΠ Ha1 Hv0 HN' Hn0) as (v1 & c & Hv1 & Hc & Hv1c).
    destruct (fast_eval_clo_sim _ _ _ _ _ _ _ _ Hρ0 HsN Hv1) as (v1' & Hv1' & Hs1).
    rewrite <- (functional_fast_eval_exp _ _ _ _ Hv' Hv1') in Hs1.
    assert (HBN : G ⊢ B[Id,,N] : Typeω@i) by mauto 3.
    destruct (soundness_ty HBN) as (W & HW & HeqW).
    destruct (typ_val_conv _ _ _ _ _ _ _ Hp HeqW Hc Hv1c) as (c' & Hc' & Hvc').
    exists W; split; [ econstructor; eassumption |].
    apply (mk_typ_val _ _ _ _ i p c' v1); try assumption; try (split; assumption).
    gen_presups; assumption.
  Qed.

  (** The codomain of an application at its argument, without evaluating
      the argument when the codomain does not read it ([exp_freshb]): its
      entry is then [𝕌ω@0], which nothing reads.  A numeral, a chain of
      [succ]s, is thus typed in linear time. *)
  Record app_cod_order G (P : tenv G) N (ρ : fenv) b : Prop := mk_app_cod_order
    { (** The argument evaluates *)
      app_cod_order_arg : fast_eval_exp_order gc_deps gc_stack N (fenv_erase (proj1_sig P))
    ; (** The codomain, at the argument's value *)
      app_cod_order_cod : forall n', ⟦ N ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase (proj1_sig P) ↘ n' ->
                            fast_eval_exp_order gc_deps gc_stack b (fenv_erase ρ ↦ n')
    ; (** The codomain, at [𝕌ω@0], when it does not read the argument *)
      app_cod_order_unread : exp_freshb 0 b = true -> fast_eval_exp_order gc_deps gc_stack b (fenv_erase ρ ↦ 𝕌ω@0) }.

  Definition app_cod_val G (P : tenv G) N (ρ : fenv) b (v : fdomain) : Prop :=
    (exp_freshb 0 b = true /\ ⟦ b ⟧ᶠ gc_deps ⍮ gc_stack ⍮ (fenv_erase ρ ↦ 𝕌ω@0) ↘ fdomain_erase v) \/
    (exists n, ⟦ N ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase (proj1_sig P) ↘ fdomain_erase n /\
          ⟦ b ⟧ᶠ gc_deps ⍮ gc_stack ⍮ (fenv_erase ρ ↦ fdomain_erase n) ↘ fdomain_erase v).

  #[derive(equations=no,eliminator=no)]
  Equations app_cod G (P : tenv G) N (ρ : fenv) b (Hρ : fenv_ok gc_deps gc_stack ρ) (H : app_cod_order G P N ρ b) :
      { v | app_cod_val G P N ρ b v /\ fdomain_ok gc_deps gc_stack v } :=
  | G, P, N, ρ, b, Hρ, H with inspect (exp_freshb 0 b) := {
    | exist _ true E =>
        let (v, Hv) := fast_eval_exp_impl F b (fextend_env ρ (fd_univ 0))
                         (fextend_env_ok _ _ _ _ Hρ (fdomain_ok_univ _ _ 0)) (app_cod_order_unread _ _ _ _ _ H E) in
        exist _ v (conj (or_introl (conj E (proj1 Hv))) (proj2 Hv))
    | exist _ false E =>
        let (n, Hn) := fast_eval_exp_impl F N (proj1_sig P) (tenv_ok G (proj1_sig P) (proj2_sig P)) (app_cod_order_arg _ _ _ _ _ H) in
        let (v, Hv) := fast_eval_exp_impl F b (fextend_env ρ n) (fextend_env_ok _ _ _ _ Hρ (proj2 Hn))
                         (app_cod_order_cod _ _ _ _ _ H _ (proj1 Hn)) in
        exist _ v (conj (or_intror (ex_intro _ n (conj (proj1 Hn) (proj1 Hv)))) (proj2 Hv)) }.

  Lemma typ_val_app_cod_order : forall G P M N A B a ρ b,
      ⊢ G -> G ⊢a M ⟹ Πⁿ A B -> typ_val G P (fd_pi a ρ b) (Πⁿ A B) -> G ⊢a N ⟸ A ->
      app_cod_order G P N ρ b.
  Proof.
    intros * HG HM Hv HN.
    destruct (typ_val_app_order _ _ _ _ _ _ _ _ _ HG HM Hv HN) as [Ho1 Ho2].
    constructor; [ exact Ho1 | exact Ho2 |].
    intros Ef; apply exp_freshb_sound in Ef.
    destruct P as [p' Hp']; destruct Hv as [i p a1 v0 Hp Hag HT Ha1 Hv0 [Hs _]]; cbn in *.
    assert (G ⊢ A : Typeω@i /\ G ▹ A ⊢ B : Typeω@i) as [HA HB] by mauto 3.
    assert (HN' : G ⊢ N : A) by (eapply alg_type_check_sound; eassumption).
    destruct (eval_of_typing _ _ _ _ Hp HN') as [n Hn].
    inversion Hs as [? ? ? ? ? ? Hρ0 | | | | | | | | | | | | | | | | |]; subst.
    destruct (typ_val_pi _ _ _ _ _ _ _ _ _ _ _ Hp HT Ha1 Hv0 HN' Hn) as (v1 & c & Hv1 & _).
    destruct (fast_eval_clo_unread _ _ _ _ _ _ 𝕌ω@0 _ Hρ0 Ef Hv1) as (v1' & Hv1' & _).
    eapply fast_eval_exp_order_sound; exact Hv1'.
  Qed.

  Lemma typ_val_app_cod_step : forall G P M N A B a ρ b v,
      ⊢ G -> G ⊢a M ⟹ Πⁿ A B -> typ_val G P (fd_pi a ρ b) (Πⁿ A B) -> G ⊢a N ⟸ A ->
      app_cod_val G P N ρ b v -> fdomain_ok gc_deps gc_stack v ->
      exists T, G ⊢a M $ N ⟹ T /\ typ_val G P v T.
  Proof.
    intros * HG HM Hv HN [(Ef & Hv') | (n & Hn' & Hv')] Hok; [| eapply typ_val_app_step; eassumption ].
    apply exp_freshb_sound in Ef.
    destruct P as [p' Hp']; destruct Hv as [i p a1 v0 Hp Hag HΠ Ha1 Hv0 [Hs _]]; cbn in *.
    assert (G ⊢ A : Typeω@i /\ G ▹ A ⊢ B : Typeω@i) as [HA HB] by mauto 3.
    assert (HN' : G ⊢ N : A) by (eapply alg_type_check_sound; eassumption).
    destruct (eval_of_typing _ _ _ _ Hp HN') as [n0 Hn0].
    inversion Hs as [? ? ? ? ? ? Hρ0 | | | | | | | | | | | | | | | | |]; subst.
    destruct (typ_val_pi _ _ _ _ _ _ _ _ _ _ _ Hp HΠ Ha1 Hv0 HN' Hn0) as (v1 & c & Hv1 & Hc & Hv1c).
    destruct (fast_eval_clo_unread _ _ _ _ _ _ 𝕌ω@0 _ Hρ0 Ef Hv1) as (v1' & Hv1' & Hs1).
    rewrite <- (functional_fast_eval_exp _ _ _ _ Hv' Hv1') in Hs1.
    assert (HBN : G ⊢ B[Id,,N] : Typeω@i) by mauto 3.
    destruct (soundness_ty HBN) as (W & HW & HeqW).
    destruct (typ_val_conv _ _ _ _ _ _ _ Hp HeqW Hc Hv1c) as (c' & Hc' & Hvc').
    exists W; split; [ econstructor; eassumption |].
    apply (mk_typ_val _ _ _ _ i p c' v1); try assumption; try (split; assumption).
    gen_presups; assumption.
  Qed.

  (** The type of a term as a value, from its normal form. *)
  Lemma typ_val_of_eval : forall G P (T : nf) (i : nat) v,
      G ⊢ T : Typeω@i -> ⟦ T ⟧ᶠ gc_deps ⍮ gc_stack ⍮ fenv_erase (proj1_sig P) ↘ fdomain_erase v ->
      fdomain_ok gc_deps gc_stack v -> typ_val G P v T.
  Proof.
    intros G [p' (p & Hp & Hag)] * HT Hv Hok; cbn in *.
    destruct (typ_val_self _ _ _ _ Hp HT) as (a & Ha & Haa).
    pose proof (proj2 (fast_eval_of_ref _ _ _ _ _ _ Ha (fast_env_agree_all _ _ _ _ _ Hag)) _ Hv).
    apply (mk_typ_val _ _ _ _ i p a a); try assumption; split; assumption.
  Qed.

  (** The type of a term as a value evaluates. *)
  Lemma typ_val_eval_order : forall G (P : tenv G) (T : nf) (i : nat),
      G ⊢ T : Typeω@i -> fast_eval_exp_order gc_deps gc_stack T (fenv_erase (proj1_sig P)).
  Proof.
    intros G [p' (p & Hp & Hag)] * HT; cbn in *.
    destruct (typ_val_self _ _ _ _ Hp HT) as (a & Ha & _).
    exact (proj1 (fast_eval_of_ref _ _ _ _ _ _ Ha (fast_env_agree_all _ _ _ _ _ Hag))).
  Qed.

  (** Whether a term is an application, and a value a [Π]. *)
  #[derive(equations=no,eliminator=no)]
  Equations get_app_parts (M : exp) : { M1 & { N1 | M = M1 $ N1 } } + { forall M1 N1, M <> M1 $ N1 } :=
  | M1 $ N1 => pureo (existT _ M1 (exist _ N1 _))
  | _       => inright _
  .

  #[derive(equations=no,eliminator=no)]
  Equations get_pi_val (v : fdomain) : { a & { ρ & { b | v = fd_pi a ρ b } } } + { forall a ρ b, v <> fd_pi a ρ b } :=
  | fd_pi a ρ b => pureo (existT _ a (existT _ ρ (exist _ b _)))
  | _        => inright _
  .

  Extraction Inline get_app_parts get_pi_val.


  (** ** Obligations of the Refined Cases *)

  (** A failure that the failure of a premise rules out directly. *)
  #[local]
  Ltac ob_neg_direct := clear_defs; intros; destruct_conjs; subst; firstorder.

  (** The parts of the [Π] value an application's head has as its type. *)
  #[local]
  Ltac ob_pi_parts :=
    clear_defs; destruct_conjs; subst;
    match goal with
    | HG : ⊢ ?G, HM : ?G ⊢a ?M ⟹ ?T, Hv : typ_val ?G ?P (fd_pi ?a ?ρ ?b) ?T |- _ =>
        let A0 := fresh "A0" in let B0 := fresh "B0" in let i := fresh "i" in
        destruct (typ_val_pi_parts _ _ _ _ _ _ _ HG HM Hv) as (A0 & B0 & i & -> & ? & ?)
    end;
    functional_fast_read_rewrite_clear.

  (** The failure of the side condition of [type_check_in]: the inferred
      type is its own normal form, so the judgment would compare the same
      two normal forms. *)
  #[local]
  Ltac ob_check_nf_neg :=
    clear_defs; intros; destruct_conjs;
    match goal with H : _ ⊢a _ ⟸ _ |- False => inversion H; subst; clear H end;
    match goal with H : _ ⊢a _ ⊆ _ |- _ => inversion H; subst; clear H end;
    functional_alg_type_infer_rewrite_clear;
    match goal with
    | Hn : nbe_ty_f ?G (nf_to_exp ?B) ?B', HM : ?G ⊢a _ ⟹ ?B, HA : ?G ⊢ _ : Typeω@_ |- _ =>
        assert (B = B') as <- by (eapply alg_type_infer_normal; [ eapply tenv_ctx_of_typ; eexists; exact HA | exact HM | exact Hn ])
    end;
    functional_nbe_rewrite_clear;
    contradiction.

  (** Its success: the rule [alg_type_check_ati], with the inferred type as its own
      normal form. *)
  #[local]
  Ltac ob_check_nf :=
    clear_defs; destruct_conjs;
    match goal with HM : ?G ⊢a ?M ⟹ ?B, HA : ?G ⊢ _ : Typeω@_, Hs : ⊢anf ?B ⊆ _ |- ?G ⊢a ?M ⟸ _ =>
      assert (nbe_ty_f G B B) by (eapply alg_type_infer_self; [ eapply tenv_ctx_of_typ; eexists; exact HA | exact HM ])
    end;
    econstructor; [ eassumption | econstructor; eassumption ].


  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations type_check_in G A (HA : (exists i, G ⊢ A : Typeω@i)) (P : tenv G) M (H : type_check_order M) : { G ⊢a M ⟸ A } + { ~ G ⊢a M ⟸ A } by struct H :=
  | G, A, HA, P, M, H =>
      let*o->b (exist _ B _) := type_infer_in G _ P M _ while _ in
      let (A', _) := nbe_ty_env_impl F G P A _ in
      let*b _ := subtyping_nf_impl B A' while _ in
      pureb _
  with type_infer_in G (HG : ⊢ G) (P : tenv G) M (H : type_infer_order M) : { A : nf | G ⊢a M ⟹ A /\ (exists UA u, G ⊢a A ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ A : Typeω@i) } + { forall A, ~ G ⊢a M ⟹ A } by struct H :=
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
    | ⊤ =>
        pureo (exist _ Typeⁿ@0 _)
    | ⋆ =>
        pureo (exist _ ⊤ⁿ _)
    | ⊥ =>
        pureo (exist _ Typeⁿ@0 _)
    | efq M' return A' =>
        let*b->o _ := type_check_in G ⊥ _ P M' _ while _ in
        let HGF : ⊢ G ▹ ⊥ := _ in
        let*o (exist _ UA' _) := type_infer_in (G ▹ ⊥) HGF (tenv_ass F G P ⊥ HGF) A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let (A'', _) := nbe_ty_env_impl F G P A'[Id,,M'] _ in
        pureo (exist _ A'' _)
    | Π B C =>
        let*o (exist _ UB _) := type_infer_in G _ P B _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UB while _ in
        let HGB : ⊢ G ▹ B := _ in
        let*o (exist _ UC _) := type_infer_in (G ▹ B) HGB (tenv_ass F G P B HGB) C _ while _ in
        let (UC', _) := nbe_ty_env_impl F (G ▹ B) (tenv_ass F G P B HGB) UC _ in
        let*o (exist _ v _) :=  univ_nf_idx_dec UC' while _ in
        let (W, _) := nbe_ty_env_impl F G P (unf_pi_tm u v) _ in
        pureo (exist _ W _)
    (** The forms of inductive types ([Extraction.IndCheck]); the
        eliminator's recursive calls are passed on. *)
    | a_ind r k => ind_infer F G HG P r k
    | a_con r k c => con_infer F G HG P r k c
    (** The forms of record types ([Extraction.RecordCheck]); the
        recursive calls on a tuple's parts and a projection's element are
        passed on. *)
    | a_record r => record_infer F G HG P r
    | a_tuple T' fs =>
        tuple_infer F G HG P T' fs (type_infer_in G HG P T' ltac:(ob_ord_record))
          (fun fm Hfm A'' HA'' => type_check_in G A'' HA'' P (snd fm) ltac:(ob_ord_record))
    | a_proj f M' => proj_infer F G HG P f M' (type_infer_in G HG P M' ltac:(ob_ord_record))
    | a_nlit n => inright (fun A HA => alg_nlit_no_infer G n A HA)
    | a_ntok => inright (fun A HA => alg_ntok_no_infer G A HA)
    | a_elim oq Us m Bks M' =>
        elim_infer F G HG P oq Us m Bks M'
          (type_infer_in G HG P M' ltac:(ob_ord_elim))
          (fun U HU G' A'' HA'' P' => type_check_in G' A'' HA'' P' U ltac:(ob_ord_elim))
          (fun b Z Hb HZ G' HG' P' => type_infer_in G' HG' P' Z ltac:(ob_ord_elim))
          (fun b Hb G' HG' P' => type_infer_in G' HG' P' (eb_motive b) ltac:(ob_ord_elim))
          (fun b br Hb Hbr G' A'' HA'' P' => type_check_in G' A'' HA'' P' (snd br) ltac:(ob_ord_elim))
    | λ A' M' =>
        let*o (exist _ UA' _) := type_infer_in G _ P A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let HGA : ⊢ G ▹ A' := _ in
        let*o (exist _ B' _) := type_infer_in (G ▹ A') HGA (tenv_ass F G P A' HGA) M' _ while _ in
        let (A'', _) := nbe_ty_env_impl F G P A' _ in
        pureo (exist _ (Πⁿ A'' B') _)
    | M' $ N' =>
        let*o (exist _ v Hv) := type_infer_app_in G HG P M' N' _ while _ in
        let (W, _) := fast_read_typ_impl F (List.length G) v (typ_val_ok_of _ _ _ _ Hv) _ in
        pureo (exist _ W _)
    | ℓ A' ≔ M' in B' =>
        let*o (exist _ UA' _) := type_infer_in G _ P A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let*b->o _ := type_check_in G A' _ P M' _ while _ in
        let HGD : ⊢ G ▸ A' ≔ M' := _ in
        let*o (exist _ C _) := type_infer_in (G ▸ A' ≔ M') HGD (tenv_def F G P A' M' HGD) B' _ while _ in
        let (D, _) := nbe_ty_env_impl F G P (C : nf)[Id,,M'] _ in
        pureo (exist _ D _)
    (** Without an annotation, the definiens's type is inferred. *)
    | ℓ ≔ M' in B' =>
        let*o (exist _ A _) := type_infer_in G _ P M' _ while _ in
        let HGD : ⊢ G ▸ (A : nf) ≔ M' := _ in
        let*o (exist _ C _) := type_infer_in (G ▸ (A : nf) ≔ M') HGD (tenv_def F G P (A : nf) M' HGD) B' _ while _ in
        let (D, _) := nbe_ty_env_impl F G P (C : nf)[Id,,M'] _ in
        pureo (exist _ D _)
    | ℓₘ U in B' =>
        let*b->o _ := unit_check G HG U _ while _ in
        let HGU : ⊢ G ▹ₘ U := _ in
        let*o (exist _ C _) := type_infer_in (G ▹ₘ U) HGU (tenv_mod F G P U HGU) B' _ while _ in
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
  | G, HG, ce_ass A :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let HΨ : ⊢ Ψ ++ G := _ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ (tenv_of F (Ψ ++ G) HΨ) A _ while _ in
      let*o->b (exist _ u _) := univ_nf_idx_dec UA while _ in
      pureb _
  | G, HG, ce_def A M :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let HΨ : ⊢ Ψ ++ G := _ in
      let PΨ := tenv_of F (Ψ ++ G) HΨ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ PΨ A _ while _ in
      let*o->b (exist _ u _) := univ_nf_idx_dec UA while _ in
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
      let PΨ := tenv_of F (Ψ ++ G) HΨ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ PΨ A _ while _ in
      let*o->b (exist _ u _) := univ_nf_idx_dec UA while _ in
      let*b _ := type_check_in (Ψ ++ G) A _ PΨ M _ while _ in
      let*b _ := unit_check (Ψ ++ G) HΨ U _ while _ in
      pureb _
  with unit_check G (HG : ⊢ G) U (H : unit_order U) : { G ⊢aᵘ U } + { ~ G ⊢aᵘ U } by struct H :=
  | G, HG, gu_mk Δ (md_body sm_closed Φ), H => right (alg_unit_closed_no G Δ Φ)
  | G, HG, gu_mk Δ (md_body sm_open Φ), H =>
      let*b _ := ext_check G HG Δ _ while _ in
      let*b _ := tele_ass_dec Δ while _ in
      let*o->b (exist _ Φx _) := body_check (Δ ++ G) _ Φ _ while _ in
      let*b _ := body_shape_dec Φ Φ while _ in
      let*b _ := body_shape_dec Φx Φx while _ in
      let*b _ := names_nodup_dec (gm_names Φ) while _ in
      pureb _
  | G, HG, gu_mk Δ (md_alias E), H =>
      let*b _ := ext_check G HG Δ _ while _ in
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
      let*b _ := type_check_in G B _ (tenv_of F G HG) N _ while _ in
      pureb _
  (** The type of an application [M $ N], as a value. *)
  with type_infer_app_in G (HG : ⊢ G) (P : tenv G) M N (H : app_order M N) :
      { v : fdomain | exists T, G ⊢a M $ N ⟹ T /\ typ_val G P v T } + { forall A, ~ G ⊢a M $ N ⟹ A } by struct H :=
  | G, HG, P, M, N, H =>
      let*o (exist _ v Hv) := type_infer_val_in G HG P M _ while _ in
      let*o (existT _ a (existT _ ρ' (exist _ b Eb))) := get_pi_val v while _ in
      let (A, _) := fast_read_typ_impl F (List.length G) a (typ_val_pi_dom_ok _ _ _ _ _ _ _ Hv Eb) _ in
      let*b->o _ := type_check_in G (A : nf) _ P N _ while _ in
      let (v', _) := app_cod G P N ρ' b (typ_val_pi_env_ok _ _ _ _ _ _ _ Hv Eb) _ in
      pureo (exist _ v' _)
  (** The type of the head of an application, as a value: an application's
      directly, any other term's by evaluating its normal form. *)
  with type_infer_val_in G (HG : ⊢ G) (P : tenv G) M (H : type_check_order M) :
      { v : fdomain | exists T, G ⊢a M ⟹ T /\ typ_val G P v T } + { forall A, ~ G ⊢a M ⟹ A } by struct H :=
  | G, HG, P, M, H with get_app_parts M => {
    | inleft (existT _ M1 (exist _ N1 _)) =>
        let*o (exist _ v _) := type_infer_app_in G HG P M1 N1 _ while _ in
        pureo (exist _ v _)
    | inright _ =>
        let*o (exist _ T _) := type_infer_in G HG P M _ while _ in
        let (v, _) := fast_eval_exp_impl F T (proj1_sig P) (tenv_ok G (proj1_sig P) (proj2_sig P)) _ in
        pureo (exist _ v _) }
  (** A body, entry by entry, as the entries its opens generate: each in the
      context of the expanded body before it. *)
  with body_check G (HG : ⊢ G) Φ (H : body_order Φ) :
      { Φx | G ⊢aᵇ Φ ⇝ Φx /\ ⊢ body_ctx Φx ++ G } + { forall Φx, ~ G ⊢aᵇ Φ ⇝ Φx } by struct H :=
  | G, HG, gm_nil, H => inleft (exist _ gm_nil _)
  | G, HG, gm_ext Φ x (ge_def b pv A (Some M)), H =>
      let*o (exist _ Φx _) := body_check G HG Φ _ while _ in
      let HGx : ⊢ body_ctx Φx ++ G := _ in
      let*o (exist _ UA _) := type_infer_in (body_ctx Φx ++ G) HGx (tenv_of F _ HGx) A _ while _ in
      let*o (exist _ u _) := univ_nf_idx_dec UA while _ in
      let*b->o _ := type_check_in (body_ctx Φx ++ G) A _ (tenv_of F _ HGx) M _ while _ in
      pureo (exist _ (gm_ext Φx x (ge_def b pv A (Some M))) _)
  | G, HG, gm_ext Φ x (ge_mod pm U), H =>
      let*o (exist _ Φx _) := body_check G HG Φ _ while _ in
      let*b->o _ := unit_check (body_ctx Φx ++ G) _ U _ while _ in
      pureo (exist _ (gm_ext Φx x (ge_mod pm U)) _)
  (** A definition with a module part: its term part as a definition, then
      its unit. *)
  | G, HG, gm_ext Φ x (ge_def_mod pv A M U), H =>
      let*o (exist _ Φx _) := body_check G HG Φ _ while _ in
      let HGx : ⊢ body_ctx Φx ++ G := _ in
      let*o (exist _ UA _) := type_infer_in (body_ctx Φx ++ G) HGx (tenv_of F _ HGx) A _ while _ in
      let*o (exist _ u _) := univ_nf_idx_dec UA while _ in
      let*b->o _ := type_check_in (body_ctx Φx ++ G) A _ (tenv_of F _ HGx) M _ while _ in
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

  (** One obligation per hole of the program, in order, each proved by the
      tactic for its kind (see the [ob_*] and [mo_*] tactics above). *)
  Obligation 1. (* ⊢ G *) ob_ctx_ext. Qed.
  Obligation 2. (* type_infer_order M *) ob_ord. Defined.
  Obligation 3. (* False *) ob_neg. Qed.
  Obligation 4. (* nbe_ty_order gc_deps gc_stack G A *)
    clear_defs; destruct_conjs; eapply nbe_order_of_typ; eassumption.
  Qed.
  Obligation 5. (* False: the inferred type is not below [A] *) ob_check_nf_neg. Qed.
  Obligation 6. (* G ⊢a M ⟸ A *) ob_check_nf. Qed.
  Obligation 7. (* G ⊢a Typeω@j ⟹ Typeωⁿ@(S j) /\ (exists (UA : nf) (u : unf),... *) ob_post. Qed.
  Obligation 8. (* ⊢ G *) Qed.
  Obligation 9. (* type_infer_order M' *) ob_ord. Defined.
  Obligation 10. (* False *) ob_neg. Qed.
  Obligation 11. (* False *) ob_neg. Qed.
  Obligation 12. (* nbe_ty_order gc_deps gc_stack G Type⟨succl M'⟩ *) ob_suniv_nbe. Qed.
  Obligation 13. (* G ⊢a Type⟨M'⟩ ⟹ W /\ (exists (UA : nf) (u : unf), G ⊢a W... *) ob_suniv_post. Qed.
  Obligation 14. (* G ⊢a Level@k ⟹ Typeⁿ@0 /\ (exists (UA : nf) (u : unf), G ⊢... *) ob_post_suniv0. Qed.
  Obligation 15. (* G ⊢a 𝕃ᵒ m ⟹ Levelⁿ@(fst m) /\ (exists (UA : nf) (u : unf), G ⊢a Le... *) ob_post_lvl. Qed.
  Obligation 16. (* ⊢ G *) Qed.
  Obligation 17. (* type_infer_order M' *) ob_ord. Defined.
  Obligation 18. (* False *) ob_neg. Qed.
  Obligation 19. (* False *) ob_neg. Qed.
  Obligation 20. (* G ⊢a succl M' ⟹ Levelⁿ@k /\ (exists (UA : nf) (u : unf), G ... *) ob_post_lvl. Qed.
  Obligation 21. (* ⊢ G *) Qed.
  Obligation 22. (* type_infer_order M' *) ob_ord. Defined.
  Obligation 23. (* False *) ob_neg. Qed.
  Obligation 24. (* False *) ob_neg. Qed.
  Obligation 25. (* ⊢ G *) Qed.
  Obligation 26. (* type_infer_order N' *) ob_ord. Defined.
  Obligation 27. (* False *) ob_neg. Qed.
  Obligation 28. (* False *) ob_neg. Qed.
  Obligation 29. (* G ⊢a maxl M' N' ⟹ Levelⁿ@(max k k') /\ (exists (UA : nf) (u : unf), ... *) ob_post_lvl. Qed.
  Obligation 30. (* G ⊢a ⊤ ⟹ Typeⁿ@0 /\ (exists (UA : nf) (u : unf), G ⊢a Ty... *) ob_post_suniv0. Qed.
  Obligation 31. (* G ⊢a ⋆ ⟹ ⊤ⁿ /\ (exists (UA : nf) (u : unf), G ⊢a ⊤ ⟹ UA /... *) ob_post. Qed.
  Obligation 32. (* G ⊢a ⊥ ⟹ Typeⁿ@0 /\ (exists (UA : nf) (u : unf), G ⊢a Ty... *) ob_post_suniv0. Qed.
  Obligation 33. (* exists i : nat, G ⊢ ⊥ : Typeω@i *) ob_typ_closed. Qed.
  Obligation 34. (* type_check_order M' *) ob_ord. Defined.
  Obligation 35. (* False *) ob_neg. Qed.
  Obligation 36. (* ⊢ G ▹ ⊥ *) ob_ctx_ext. Qed.
  Obligation 37. (* type_infer_order A' *) ob_ord. Defined.
  Obligation 38. (* False *) ob_neg. Qed.
  Obligation 39. (* False *) ob_neg. Qed.
  Obligation 40. (* nbe_ty_order gc_deps gc_stack G A'[Id,,M'] *)
    clear_defs.
    enough (exists i, G ⊢ A'[Id,,M'] : Typeω@i) as [? [? []]%wf_exp_eq_refl%completeness_ty]
        by eauto 3 using nbe_ty_order_sound.
    assert (G ⊢ ⊥ : Typeω@0) by mauto 2.
    assert (⊢ G ▹ ⊥) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢ M' : ⊥) by mauto 3 using alg_type_check_sound.
    assert (G ⊢ˢ Id,,M' : G ▹ ⊥) as Hσ by mauto 3.
    match goal with HA' : G ▹ ⊥ ⊢ A' : Typeω@?k |- _ =>
      exists k; exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
  Qed.
  Obligation 41. (* G ⊢a efq M' return A' ⟹ A'', and [A''] is a type *)
    clear_defs.
    split; [ mauto 3 |].
    assert (G ⊢ ⊥ : Typeω@0) by mauto 2.
    assert (⊢ G ▹ ⊥) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢ M' : ⊥) by mauto 3 using alg_type_check_sound.
    assert (G ⊢ˢ Id,,M' : G ▹ ⊥) as Hσ by mauto 3.
    match goal with HA' : G ▹ ⊥ ⊢ A' : Typeω@?k |- _ =>
      assert (G ⊢ A'[Id,,M'] : Typeω@k) by exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 42. Qed.
  Obligation 43. (* type_infer_order B *) ob_ord. Defined.
  Obligation 44. (* False *) ob_neg. Qed.
  Obligation 45. (* False *) ob_neg. Qed.
  Obligation 46. (* ⊢ G ▹ B *) ob_ctx. Qed.
  Obligation 47. (* type_infer_order C *) ob_ord. Defined.
  Obligation 48. (* False *) ob_neg. Qed.
  Obligation 49. (* nbe_ty_order gc_deps gc_stack (G ▹ B) UC *)
    clear_defs.
    destruct_conjs.
    match goal with H : G ▹ B ⊢ (?UC : exp) : Typeω@?i |- nbe_ty_order _ _ _ ?UC =>
      destruct (soundness_ty H) as [W [HW _]] end.
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 50. (* False: the codomain's universe, normalised, is no universe *)
    clear_defs.
    lazymatch goal with H : _ ⊢a _ ⟹ _ |- False => inversion H; subst; clear H end.
    destruct_conjs.
    functional_alg_type_infer_rewrite_clear.
    functional_nbe_rewrite_clear.
    firstorder.
  Qed.
  Obligation 51. (* nbe_ty_order gc_deps gc_stack G (unf_pi_tm u v) *)
    clear_defs.
    destruct_conjs.
    match goal with
    | HB : G ⊢a B ⟹ ?UB, Hu : is_univ_nf ?UB u, HC : G ▹ B ⊢a C ⟹ ?UC,
      HnC : nbe_ty gc_deps gc_stack (G ▹ B) (nf_to_exp ?UC) ?UC', Hv : is_univ_nf ?UC' v |- _ =>
        destruct (alg_pi_parts_sound HG HB Hu HC HnC Hv) as (HBu & HCv & Hvw)
    end.
    destruct (wf_unf_pi_tm HBu HCv Hvw) as [k Hk].
    destruct (soundness_ty Hk) as [W [HW _]].
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 52. (* G ⊢a Π B C ⟹ W, the normal form of its universe, and that is a type *)
    clear_defs.
    destruct_conjs.
    match goal with
    | HB : G ⊢a B ⟹ ?UB, Hu : is_univ_nf ?UB u, HC : G ▹ B ⊢a C ⟹ ?UC,
      HnC : nbe_ty gc_deps gc_stack (G ▹ B) (nf_to_exp ?UC) ?UC', Hv : is_univ_nf ?UC' v |- _ =>
        destruct (alg_pi_parts_sound HG HB Hu HC HnC Hv) as (HBu & HCv & Hvw)
    end.
    destruct (wf_unf_pi_tm HBu HCv Hvw) as [k Hk].
    assert (G ⊢ unf_pi_tm u v ≈ W : Typeω@k) by (eapply soundness_ty'; eassumption).
    assert (HWk : G ⊢ W : Typeω@k) by (gen_presups; assumption).
    split; [ eapply alg_type_infer_pi; eassumption |].
    split; [| eexists; exact HWk ].
    destruct (alg_type_infer_large_typ_complete (user_exp_nf W) HWk) as [? [? [? [? _]]]].
    do 2 eexists; split; eassumption.
  Qed.
  Obligation 53. Qed.
  Obligation 54. (* type_infer_order A' *) ob_ord. Defined.
  Obligation 55. (* False *) ob_neg. Qed.
  Obligation 56. (* False *) ob_neg. Qed.
  Obligation 57. (* ⊢ G ▹ A' *) ob_ctx. Qed.
  Obligation 58. (* type_infer_order M' *) ob_ord. Defined.
  Obligation 59. (* False *) ob_neg. Qed.
  Obligation 60. (* nbe_ty_order gc_deps gc_stack G A' *)
    clear_defs.
    saturate_infer_univ.
    match goal with H : G ⊢ A' : Typeω@?k |- _ =>
      assert (G ⊢ A' : Typeω@k) as [? []]%soundness_ty by exact H end.
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 61. (* G ⊢a λ A' M' ⟹ Πⁿ A'' B', and [Π A'' B'] is a type *)
    clear_defs.
    saturate_infer_univ.
    (** The annotation's normal form is a type at the same level, and the
        body's type is one in the context of that normal form. *)
    assert (⊢ G ▹ A') by mauto 2.
    assert (G ⊢ A' ≈ A'' : Typeω@(unf_large u)) by (eapply soundness_ty'; mauto 4 using alg_type_check_sound).
    assert (G ⊢ A'' : Typeω@(unf_large u)) by (gen_presups; mauto 2).
    assert (⊢ G ▹ (A'' : exp)) by mauto 2.
    assert (exists l, G ▹ (A'' : exp) ⊢ B' : Typeω@l) as [l HB'] by (eexists; mauto 4).
    split; [ mauto 3 | split ].
    - destruct (alg_type_infer_large_typ_complete (user_exp_nf A'') ltac:(eassumption)) as [UA'' [w [HUA'' [HwA'' _]]]].
      destruct (alg_type_infer_large_typ_complete (user_exp_nf B') HB') as [UB' [w' [HUB' [HwB' _]]]].
      destruct (alg_pi_infer_univ G _ _ _ _ _ _ HG HUA'' HUB' HwA'' HwB') as (W0 & w0 & HW0 & Hw0 & _).
      do 2 eexists; split; eassumption.
    - exists (max (unf_large u) l); apply wf_pi_large;
        [ mauto 3 using lift_exp_max_left | mauto 3 using lift_exp_max_right ].
  Qed.
  Obligation 62. (* app_order M' N' *) ob_ord. Defined.
  Obligation 63. (* False *) ob_neg_direct. Qed.
  Obligation 64. (* read_typ_order gc_deps gc_stack (List.length G) v *)
    clear_defs; destruct_conjs.
    eapply fast_read_typ_order_sound, typ_val_rtyp; eassumption.
  Qed.
  Obligation 65. (* G ⊢a M' $ N' ⟹ W, and [W] is a type *)
    clear_defs; destruct_conjs.
    match goal with Hi : G ⊢a _ ⟹ ?T, Hv : typ_val G P ?v ?T |- _ =>
      pose proof (typ_val_rtyp _ _ _ _ _ HG Hi Hv); destruct Hv as [? ? ? ? ? ? ? ? ? ?] end.
    functional_fast_read_rewrite_clear.
    split; [ assumption | eapply infer_post_of_typ; eassumption ].
  Qed.
  Obligation 66. Qed.
  Obligation 67. (* False *) ob_neg. Qed.
  Obligation 68. (* nbe_ty_order gc_deps gc_stack G A *)
    clear_defs.
    assert (exists i, G ⊢ A : Typeω@i) as [? [? []]%soundness_ty] by mauto 3.
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 69. (* G ⊢a #x ⟹ A', and [A'] is a type *)
    clear_defs.
    assert (exists i, G ⊢ A : Typeω@i) as [i] by mauto 3.
    split; [ mauto 3 |].
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 70. Qed.
  Obligation 71. (* type_infer_order A' *) ob_ord. Defined.
  Obligation 72. (* False *) ob_neg. Qed.
  Obligation 73. (* False *) ob_neg. Qed.
  Obligation 74. (* exists i, G ⊢ A' : Typeω@i *)
    clear_defs.
    eexists; saturate_infer_univ; eassumption.
  Qed.
  Obligation 75. (* type_check_order M' *) ob_ord. Defined.
  Obligation 76. (* False *) ob_neg. Qed.
  Obligation 77. (* ⊢ G ▸ A' ≔ M' *) ob_ctx. Qed.
  Obligation 78. (* type_infer_order B' *) ob_ord. Defined.
  Obligation 79. (* False *) ob_neg. Qed.
  Obligation 80. (* nbe_ty_order gc_deps gc_stack G C[Id,,M'] *)
    clear_defs.
    destruct_conjs.
    saturate_infer_univ.
    assert (G ⊢ M' : A') by mauto 3 using alg_type_check_sound.
    assert (⊢ G ▸ A' ≔ M') by mauto 3.
    assert (G ⊢ˢ Id,,M' : G ▸ A' ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Typeω@k) as [? [? []]%soundness_ty] by (eexists; mauto 3).
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 81. (* G ⊢a ℓ A' ≔ M' in B' ⟹ D /\ (D is a type) *)
    clear_defs.
    split; [mauto 3 |].
    destruct_conjs.
    saturate_infer_univ.
    assert (G ⊢ M' : A') by mauto 3 using alg_type_check_sound.
    assert (⊢ G ▸ A' ≔ M') by mauto 3.
    assert (G ⊢ˢ Id,,M' : G ▸ A' ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Typeω@k) as [? ?] by (eexists; mauto 3).
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 82. Qed.
  Obligation 83. (* type_infer_order M' *) ob_ord. Defined.
  Obligation 84. (* False *) ob_neg. Qed.
  Obligation 85. (* ⊢ G ▸ A ≔ M' *)
    clear_defs.
    destruct_conjs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    mauto 3.
  Qed.
  Obligation 86. (* type_infer_order B' *) ob_ord. Defined.
  Obligation 87. (* False *) ob_neg. Qed.
  Obligation 88. (* nbe_ty_order gc_deps gc_stack G C[Id,,M'] *)
    clear_defs.
    destruct_conjs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    assert (⊢ G ▸ A ≔ M') by mauto 3.
    assert (G ⊢ˢ Id,,M' : G ▸ A ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Typeω@k) as [? [? []]%soundness_ty] by (eexists; mauto 3).
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 89. (* G ⊢a ℓ ≔ M' in B' ⟹ D /\ (D is a type) *)
    clear_defs.
    split; [mauto 3 |].
    destruct_conjs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    assert (⊢ G ▸ A ≔ M') by mauto 3.
    assert (G ⊢ˢ Id,,M' : G ▸ A ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Typeω@k) as [? ?] by (eexists; mauto 3).
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 90. (* unit_order U *) ob_ord. Defined.
  Obligation 91. (* False *) ob_neg. Qed.
  Obligation 92. (* ⊢ G ▹ₘ U *) ob_ctx. Qed.
  Obligation 93. (* type_infer_order B' *) ob_ord. Defined.
  Obligation 94. (* False *) ob_neg. Qed.
  Obligation 95. (* nbe_ty_order gc_deps gc_stack G C[Id ,,ₘ me_lit U] *)
    clear_defs.
    assert (gc_deps ⍮ gc_stack ⍮ G ⊢ᵘ U ≈ U) by (eapply alg_unit_sound; eassumption).
    assert (⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; eassumption).
    assert (G ⊢ˢ Id ,,ₘ me_lit U : G ▹ₘ U) by (eapply wf_sub_single_mod; eassumption).
    assert (exists k, G ⊢ C[Id ,,ₘ me_lit U] : Typeω@k) as [? [? []]%soundness_ty]
        by (eexists; mauto 3).
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 96. (* G ⊢a ℓₘ U in B' ⟹ D, and [D] is a type *)
    clear_defs.
    split; [ mauto 3 |].
    assert (gc_deps ⍮ gc_stack ⍮ G ⊢ᵘ U ≈ U) by (eapply alg_unit_sound; eassumption).
    assert (⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; eassumption).
    assert (G ⊢ˢ Id ,,ₘ me_lit U : G ▹ₘ U) by (eapply wf_sub_single_mod; eassumption).
    assert (exists k, G ⊢ C[Id ,,ₘ me_lit U] : Typeω@k) as [? ?] by (eexists; mauto 3).
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 97. (* modexp_order M' *) ob_ord. Defined.
  Obligation 98. (* False *) ob_mem_neg. Qed.
  Obligation 99. (* ⊢ᵍ gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 100. (* gc_deps ⍮ gc_stack ⍮ G ⊢ᵐ M' ≈ M' *) mo_18. Qed.
  Obligation 101. (* False: the member denotes nothing *) ob_mem_neg. Qed.
  Obligation 102. (* False: what it denotes has no type *) ob_mem_neg. Qed.
  Obligation 103. (* nbe_ty_order gc_deps gc_stack G A *) mo_7. Qed.
  Obligation 104. (* G ⊢a a_mem M' x ⟹ B /\ (exists (UA : nf) (u : unf), G ⊢a ... *) mo_8. Qed.
  Obligation 105. (* G ⊢aˣ ⋅ *) ob_check. Qed.
  Obligation 106. (* ext_order Ψ *) ob_ord. Defined.
  Obligation 107. (* False *) mo_10. Qed.
  Obligation 108. (* ⊢ Ψ ++ G *) ob_ctx. Qed.
  Obligation 109. (* type_infer_order A *) ob_ord. Defined.
  Obligation 110. (* False *) mo_10. Qed.
  Obligation 111. (* False *) mo_10. Qed.
  Obligation 112. (* G ⊢aˣ Ψ ▹ A *) ob_check. Qed.
  Obligation 113. (* ext_order Ψ *) ob_ord. Defined.
  Obligation 114. (* False *) mo_10. Qed.
  Obligation 115. (* ⊢ Ψ ++ G *) ob_ctx. Qed.
  Obligation 116. (* type_infer_order A *) ob_ord. Defined.
  Obligation 117. (* False *) mo_10. Qed.
  Obligation 118. (* False *) mo_10. Qed.
  Obligation 119. (* exists i0 : nat, Ψ ++ G ⊢ A : Typeω@i0 *) mo_14. Qed.
  Obligation 120. (* type_check_order M *) ob_ord. Defined.
  Obligation 121. (* False *) mo_10. Qed.
  Obligation 122. (* G ⊢aˣ Ψ ▸ A ≔ M *) ob_check. Qed.
  Obligation 123. (* ext_order Ψ *) ob_ord. Defined.
  Obligation 124. (* False *) mo_10. Qed.
  Obligation 125. (* ⊢ Ψ ++ G *) ob_ctx. Qed.
  Obligation 126. (* unit_order U *) ob_ord. Defined.
  Obligation 127. (* False *) mo_10. Qed.
  Obligation 128. (* G ⊢aˣ Ψ ▹ₘ U *) ob_check. Qed.
  Obligation 129. (* ext_order Ψ *) ob_ord. Defined.
  Obligation 130. (* False *) mo_10. Qed.
  Obligation 131. (* ⊢ Ψ ++ G *) ob_ctx. Qed.
  Obligation 132. (* type_infer_order A *) ob_ord. Defined.
  Obligation 133. (* False *) mo_10. Qed.
  Obligation 134. (* False *) mo_10. Qed.
  Obligation 135. (* exists i0 : nat, Ψ ++ G ⊢ A : Typeω@i0 *) mo_14. Qed.
  Obligation 136. (* type_check_order M *) ob_ord. Defined.
  Obligation 137. (* False *) mo_10. Qed.
  Obligation 138. (* unit_order U *) ob_ord. Defined.
  Obligation 139. (* False *) mo_10. Qed.
  Obligation 140. (* G ⊢aˣ Ψ ▸ₘ A ≔ M ‖ U *) ob_check. Qed.
  Obligation 141. (* ext_order Δ *) ob_ord. Defined.
  Obligation 142. (* False *) mo_10. Qed.
  Obligation 143. (* False *) mo_10. Qed.
  Obligation 144. (* ⊢ Δ ++ G *) ob_ctx. Qed.
  Obligation 145. (* body_order Φ *) ob_ord. Defined.
  Obligation 146. (* False: the body does not check *) bc_obl. Qed.
  Obligation 147. (* False *) mo_10. Qed.
  Obligation 148. (* False: its expansion is of no shape *) bc_obl. Qed.
  Obligation 149. (* False *) mo_10. Qed.
  Obligation 150. (* G ⊢aᵘ gu_open Δ Φ *) ob_check. Qed.
  Obligation 151. (* ext_order Δ *) ob_ord. Defined.
  Obligation 152. (* False *) mo_10. Qed.
  Obligation 153. (* False *) mo_10. Qed.
  Obligation 154. (* ⊢ Δ ++ G *) ob_ctx. Qed.
  Obligation 155. (* modexp_order E *) ob_ord. Defined.
  Obligation 156. (* False *) mo_10. Qed.
  Obligation 157. (* G ⊢aᵘ gu_mk Δ (md_alias E) *) ob_check. Qed.
  Obligation 158. (* ⊢ᵍ gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 159. (* False: the path denotes nothing *) mo_10. Qed.
  Obligation 160. (* False: it is no module *) mo_10. Qed.
  Obligation 161. (* G ⊢aᵐ me_unit fp *) mo_2. Qed.
  Obligation 162. (* G ⊢aᵐ me_var x *) mo_19. Qed.
  Obligation 163. (* False *) mo_20. Qed.
  Obligation 164. (* modexp_order M *) ob_ord. Defined.
  Obligation 165. (* False *) mo_10. Qed.
  Obligation 166. (* ⊢ᵍ gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 167. (* gc_deps ⍮ gc_stack ⍮ G ⊢ᵐ M ≈ M *) mo_18. Qed.
  Obligation 168. (* False: the selection denotes nothing *) mo_3. Qed.
  Obligation 169. (* False: it is no module *) mo_3. Qed.
  Obligation 170. (* G ⊢aᵐ me_mem M y *) ob_check. Qed.
  Obligation 171. (* modexp_order M *) ob_ord. Defined.
  Obligation 172. (* False *) mo_10. Qed.
  Obligation 173. (* ⊢ᵍ gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 174. (* gc_deps ⍮ gc_stack ⍮ G ⊢ᵐ M ≈ M *) mo_18. Qed.
  Obligation 175. (* False: the module expression denotes nothing *) mo_10. Qed.
  Obligation 176. (* False: it is no module *) mo_10. Qed.
  Obligation 177. (* False: it takes no parameter *) mo_21. Qed.
  Obligation 178. (* exists i : nat, G ⊢ B : Typeω@i *) mo_22. Qed.
  Obligation 179. (* type_check_order N *) ob_ord. Defined.
  Obligation 180. (* False *) mo_21. Qed.
  Obligation 181. (* G ⊢aᵐ me_app M N *) ob_check. Qed.
  Obligation 182. (* unit_order U *) ob_ord. Defined.
  Obligation 183. (* False *) mo_10. Qed.
  Obligation 184. (* G ⊢aᵐ me_lit U *) ob_check. Qed.
  Obligation 185. (* type_check_order M *) ob_ord. Defined.
  Obligation 186. (* False *) ob_neg. Qed.
  Obligation 187. (* False: the head's type is not a [Π] *)
    clear_defs; intros; destruct_conjs.
    try match goal with |- ~ _ => intro end.
    match goal with H : _ ⊢a _ $ _ ⟹ _ |- False => inversion H; subst; clear H end.
    functional_alg_type_infer_rewrite_clear.
    match goal with Hi : G ⊢a M ⟹ ?T, Hv : typ_val G P ?v ?T |- _ =>
      pose proof (typ_val_rtyp _ _ _ _ _ HG Hi Hv) as Hr end.
    (** The value, read back to a [Π], is one *)
    match goal with Hr : Rtypᶠ fdomain_erase ?v in _ ⍮ _ ⍮ _ ↘ _ |- _ =>
      destruct v; cbn [fdomain_erase] in Hr; inversion Hr; subst end.
    firstorder congruence.
  Qed.
  Obligation 188. (* read_typ_order gc_deps gc_stack (List.length G) a *)
    ob_pi_parts; eapply fast_read_typ_order_sound; eassumption.
  Qed.
  Obligation 189. (* exists i, G ⊢ A : Typeω@i *)
    ob_pi_parts.
    match goal with H : G ⊢ Π ?A0 ?B0 : Typeω@?i |- _ =>
      assert (G ⊢ A0 : Typeω@i /\ G ▹ A0 ⊢ B0 : Typeω@i) as [? ?] by mauto 3; eexists; eassumption end.
  Qed.
  Obligation 190. (* type_check_order N *) ob_ord. Defined.
  Obligation 191. (* False: the argument does not check *)
    ob_pi_parts; try match goal with |- ~ _ => intro end.
    match goal with H : _ ⊢a _ $ _ ⟹ _ |- False => inversion H; subst; clear H end.
    functional_alg_type_infer_rewrite_clear.
    autoinjections; subst; contradiction.
  Qed.
  Obligation 192. (* app_cod_order G P N ρ' b *)
    ob_pi_parts; eapply typ_val_app_cod_order; eassumption.
  Qed.
  Obligation 193. (* exists T, G ⊢a M $ N ⟹ T /\ typ_val G P v' T *)
    ob_pi_parts; eapply typ_val_app_cod_step; eassumption.
  Qed.
  Obligation 194. (* app_order M1 N1 *) clear_defs; subst; ob_ord. Defined.
  Obligation 195. (* False *) ob_neg_direct. Qed.
  Obligation 196. (* exists T, G ⊢a M1 $ N1 ⟹ T /\ typ_val G P v T *) clear_defs; destruct_conjs; subst; eexists; split; eassumption. Qed.
  Obligation 197. (* type_infer_order M *) ob_ord. Defined.
  Obligation 198. (* False *) ob_neg_direct. Qed.
  Obligation 199. (* fast_eval_exp_order gc_deps gc_stack T (proj1_sig P) *)
    clear_defs; destruct_conjs; eapply typ_val_eval_order; eassumption.
  Qed.
  Obligation 200. (* exists T0, G ⊢a M ⟹ T0 /\ typ_val G P v T0 *)
    clear_defs; destruct_conjs.
    eexists; split; [ eassumption | eapply typ_val_of_eval; eassumption ].
  Qed.
  Obligation 201. all: bc_obl. Qed.
  Obligation 202. ob_ord. Defined.
  Obligation 203. all: bc_obl. Qed.
  Obligation 204. all: bc_obl. Qed.
  Obligation 205. ob_ord. Defined.
  Obligation 206. all: bc_obl. Qed.
  Obligation 207. all: bc_obl. Qed.
  Obligation 208. all: bc_obl. Qed.
  Obligation 209. ob_ord. Defined.
  Obligation 210. all: bc_obl. Qed.
  Obligation 211. all: bc_obl. Qed.
  Obligation 212. all: bc_obl. Qed.
  Obligation 213. ob_ord. Defined.
  Obligation 214. all: bc_obl. Qed.
  Obligation 215. all: bc_obl. Qed.
  Obligation 216. ob_ord. Defined.
  Obligation 217. all: bc_obl. Qed.
  Obligation 218. all: bc_obl. Qed.
  Obligation 219. (* no body holds an inductive type *) all: bc_obl. Qed.
  (* a definition with a module part *)
  Obligation 220. ob_ord. Defined.
  Obligation 221. all: bc_obl. Qed.
  Obligation 222. all: bc_obl. Qed.
  Obligation 223. ob_ord. Defined.
  Obligation 224. all: bc_obl. Qed.
  Obligation 225. all: bc_obl. Qed.
  Obligation 226. all: bc_obl. Qed.
  Obligation 227. ob_ord. Defined.
  Obligation 228. all: bc_obl. Qed.
  Obligation 229. ob_ord. Defined.
  Obligation 230. all: bc_obl. Qed.
  Obligation 231. all: bc_obl. Qed.
  Obligation 232. (* no body holds a record entry *) all: bc_obl. Qed.
  Obligation 233. ob_ord. Defined.
  Obligation 234. all: bc_obl. Qed.
  Obligation 235. all: bc_obl. Qed.
  Obligation 236. ob_ord. Defined.
  Obligation 237. all: bc_obl. Qed.
  Obligation 238. all: bc_obl. Qed.
  Obligation 239. all: bc_obl. Qed.
  Obligation 240. all: bc_obl. Qed.
  Obligation 241. all: bc_obl. Qed.
  Obligation 242. all: bc_obl. Qed.
  Obligation 243. all: bc_obl. Qed.
  Obligation 244. all: bc_obl. Qed.
  Obligation 245. all: bc_obl. Qed.
  Obligation 246. all: bc_obl. Qed.


  Extraction Inline type_check_in_functional type_infer_in_functional ext_check_functional
    unit_check_functional body_check_functional modexp_check_functional.

  (** The checker from scratch: the initial environment of the context is
      computed once, at the start. *)
  Definition type_check G A (HA : exists i, G ⊢ A : Typeω@i) M (H : type_check_order M) :
      { G ⊢a M ⟸ A } + { ~ G ⊢a M ⟸ A } :=
    type_check_in G A HA (tenv_of F G (tenv_ctx_of_typ _ _ HA)) M H.

  Definition type_infer G (HG : ⊢ G) M (H : type_infer_order M) :
      { A : nf | G ⊢a M ⟹ A /\ (exists UA u, G ⊢a A ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ A : Typeω@i) } +
      { forall A, ~ G ⊢a M ⟹ A } :=
    type_infer_in G HG (tenv_of F G HG) M H.

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

Lemma type_check_complete' : forall G M A (HA : exists i, G ⊢ A : Typeω@i),
    G ⊢a M ⟸ A ->
    exists H H', type_check G A HA M H = left H'.
Proof.
  intros ? ? ? [] ?.
  assert (Horder : type_check_order M) by mauto.
  exists Horder.
  dec_complete.
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
  assert (Horder : ext_order Ψ).
  { induction Ψ as [| [A | A M | U | A M U] Ψ IH]; inversion HΨ; subst; constructor;
      eauto using type_infer_order_all, unit_order_all, type_check_order_ti. }
  exists Horder; destruct (ext_check G HG Ψ Horder); [ eexists; reflexivity | contradiction ].
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
  Ltac impl_obl_tac :=
    unfold not in *;
    intros;
    mauto 3 using user_exp_to_type_infer_order, type_check_order, type_infer_order.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations type_check_closed (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) A (HA : user_exp A) M (HM : user_exp M) : { ⋅ ⊢ M : A } + { ~ ⋅ ⊢ M : A } :=
  | Hg, A, HA, M, HM =>
      let*o->b (exist _ UA _) := type_infer ⋅ _ A _ while _ in
      let*o->b (exist _ u _) :=  univ_nf_idx_dec UA while _ in
      let*b _ := type_check ⋅ A _ M _ while _ in
      pureb _
  .
  Next Obligation. (* False *)
    assert (⊢ ⋅) by mauto 2.
    assert (exists i, ⋅ ⊢ A : Typeω@i) as [i] by (gen_presups; eauto 2).
    assert (exists UA' w, ⋅ ⊢a A ⟹ UA' /\ is_univ_nf UA' w /\ unf_le w (unl i)) as [UA' [w [? []]]]
        by mauto 3.
    firstorder.
  Qed.
  Next Obligation. (* False *)
    assert (exists i, ⋅ ⊢ A : Typeω@i) as [i] by (gen_presups; eauto 2).
    assert (exists UA' w, ⋅ ⊢a A ⟹ UA' /\ is_univ_nf UA' w /\ unf_le w (unl i)) as [UA' [w [? []]]]
        by mauto 3.
    functional_alg_type_infer_rewrite_clear.
    match goal with
    | HN : forall u : unf, ~ is_univ_nf ?UA u, Hu : is_univ_nf ?UA ?w |- _ => exact (HN w Hu)
    end.
  Qed.
  Next Obligation. (* exists i, ⋅ ⊢ A : Typeω@i *)
    assert (⊢ ⋅) by mauto 2.
    match goal with Hu : is_univ_nf ?UA u |- _ => rewrite (is_univ_nf_eq _ _ Hu) in * end.
    assert (⋅ ⊢ A : (univ_nf u : exp)) by mauto 2 using alg_type_infer_sound.
    rewrite nf_to_exp_univ_nf in *.
    exists (unf_large u); apply wf_exp_unf_large; eassumption.
  Qed.
  Next Obligation. (* ⋅ ⊢ M : A *)
    assert (⊢ ⋅) by mauto 2.
    match goal with Hu : is_univ_nf ?UA u |- _ => rewrite (is_univ_nf_eq _ _ Hu) in * end.
    assert (⋅ ⊢ A : (univ_nf u : exp)) by mauto 3 using alg_type_infer_sound.
    rewrite nf_to_exp_univ_nf in *.
    assert (⋅ ⊢ A : Typeω@(unf_large u))
      by (apply wf_exp_unf_large; eassumption).
    mauto 3 using alg_type_check_sound.
  Qed.
End type_check_closed.

Lemma type_check_closed_complete : forall (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) A (HA : user_exp A) M (HM : user_exp M),
    ⋅ ⊢ M : A ->
    exists H', type_check_closed Hg A HA M HM = left H'.
Proof. intros; dec_complete. Qed.

(** What an unascribed [eval] needs: a type for a closed term, rather than a
    type to check it against. *)
Section type_infer_closed.
  #[local]
  Ltac impl_obl_tac :=
    unfold not in *;
    intros;
    destruct_conjs;
    try assert (⊢ ⋅) by mauto 2;
    solve [ mauto 3 using user_exp_to_type_infer_order, alg_type_infer_sound
          | firstorder ].

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
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
  Ltac impl_obl_tac :=
    unfold not in *;
    intros;
    destruct_conjs;
    solve [ mauto 3 using user_exp_to_type_infer_order, alg_type_infer_sound
          | firstorder ].

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations type_infer_at G (HG : ⊢ G) M (HM : user_exp M) : { A : nf | G ⊢ M : A } + { forall A, ~ G ⊢a M ⟹ A } :=
  | G, HG, M, HM =>
      let*o (exist _ A _) := type_infer G HG M _ while _ in
      pureo (exist _ A _)
  .
End type_infer_at.

End Fixed_GCtx.
