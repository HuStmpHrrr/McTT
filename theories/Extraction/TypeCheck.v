From Stdlib Require Import List ListDec Morphisms_Relations String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base Completeness.
From Mctt.Core.Completeness Require Import FundamentalTheorem SubstitutionCases.
From Mctt.Core.Semantic Require Import Consequences Realizability.
From Mctt.Core.Syntactic.System Require Import MemberWf.
From Mctt.Core.Syntactic Require Import Fresh.
From Mctt.Core.Semantic Require Import MemberWf.
From Mctt.Extraction Require Import FastEval Simulation Evaluation Readback NbE PseudoMonadic Subtyping MemberType.
From Mctt.Extraction Require Export TypeCheckBase.
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
Context {GC : GCtx}.

(** * The Checker

    The checker of [Reference.TypeCheck], with two refinements, each of which
    computes the result of a rule of [⊢a] in another way:

    - An application spine [M $ N1 $ ⋯ $ Nk] is checked against the value of
      the type of its head ([type_infer_val_in]): each argument instantiates
      the codomain closure of the current [Π] value with the argument's value
      ([type_infer_app_in]), where [ati_app] substitutes the argument into the
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
  pose proof HN' as [env_relΓ [HΓr _]].
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

  (** The type of a term as a value at the environment [P]: a value related
      ([dsim]) to one that stands for the normal form [T] at the initial
      environment. *)
  Definition typ_val G (P : tenv G) (v : domain) (T : nf) : Prop :=
    exists (i : nat) p a v0, initial_env_f G p /\ env_agree (fun _ => True) p (proj1_sig P) /\
      G ⊢ T : Typeω@i /\ ⟦ T ⟧ p ↘ a /\ Dom v0 ≈ a ∈ per_univ i /\ dsim v0 v.

  (** A type as a value reads back to the type it stands for. *)
  Lemma typ_val_rtyp : forall G P M v T,
      ⊢ G -> G ⊢a M ⟹ T -> typ_val G P v T -> Rtypᶠ v in gc_deps ⍮ gc_stack ⍮ (List.length G) ↘ T.
  Proof.
    intros * HG HM (i & p & a & v0 & Hp & _ & HT & Ha & Hv0 & Hs).
    eapply fread_typ_sim; [| exact Hs ].
    eapply typ_val_read; [ eassumption | eapply alg_type_infer_self; eassumption | eassumption | eassumption ].
  Qed.

  (** A [Π] value stands for a [Π] normal form. *)
  Lemma typ_val_pi_parts : forall G P M T a ρ b,
      ⊢ G -> G ⊢a M ⟹ T -> typ_val G P (Πᵈ a ρ b) T ->
      exists A B (i : nat), T = Πⁿ A B /\ Rtypᶠ a in gc_deps ⍮ gc_stack ⍮ (List.length G) ↘ A /\ G ⊢ Π A B : Typeω@i.
  Proof.
    intros * HG HM Hv.
    pose proof (typ_val_rtyp _ _ _ _ _ HG HM Hv) as Hr.
    inversion Hr; subst.
    destruct Hv as (i & _ & _ & _ & _ & _ & HT & _).
    do 3 eexists; repeat split; eassumption.
  Qed.

  (** The argument of an application, and the codomain closure at its value,
      evaluate. *)
  Lemma typ_val_app_order : forall G P M N A B a ρ b,
      ⊢ G -> G ⊢a M ⟹ Πⁿ A B -> typ_val G P (Πᵈ a ρ b) (Πⁿ A B) -> G ⊢a N ⟸ A ->
      feval_exp_order gc_deps gc_stack N (proj1_sig P) /\
      forall n', ⟦ N ⟧ᶠ gc_deps ⍮ gc_stack ⍮ (proj1_sig P) ↘ n' -> feval_exp_order gc_deps gc_stack b (ρ ↦ n').
  Proof.
    intros G [p' Hp'] * HG HM (i & p & a1 & v0 & Hp & Hag & HT & Ha1 & Hv0 & Hs) HN; cbn in *.
    assert (G ⊢ A : Typeω@i /\ G ▹ A ⊢ B : Typeω@i) as [HA HB] by mauto 3.
    assert (HN' : G ⊢ N : A) by (eapply alg_type_check_sound; eassumption).
    destruct (eval_of_typing _ _ _ _ Hp HN') as [n Hn].
    destruct (feval_of_ref _ _ _ _ _ _ Hn (agree_all _ _ _ Hag)) as [HoN HsN].
    split; [ exact HoN |].
    intros n' Hn'.
    inversion Hs as [| ? ? ? ? ? ? Hρ0 | | | | | | | | | | | |]; subst.
    destruct (typ_val_pi _ _ _ _ _ _ _ _ _ _ _ Hp HT Ha1 Hv0 HN' Hn) as (v1 & c & Hv1 & _).
    destruct (feval_clo_sim _ _ _ _ _ _ _ _ Hρ0 (HsN _ Hn') Hv1) as (v1' & Hv1' & _).
    eapply feval_exp_order_sound; exact Hv1'.
  Qed.

  (** The value of the type of an application: [ati_app]'s type stands for
      the codomain closure applied to the argument's value. *)
  Lemma typ_val_app_step : forall G P M N A B a ρ b n v,
      ⊢ G -> G ⊢a M ⟹ Πⁿ A B -> typ_val G P (Πᵈ a ρ b) (Πⁿ A B) -> G ⊢a N ⟸ A ->
      ⟦ N ⟧ᶠ gc_deps ⍮ gc_stack ⍮ (proj1_sig P) ↘ n -> ⟦ b ⟧ᶠ gc_deps ⍮ gc_stack ⍮ (ρ ↦ n) ↘ v ->
      exists T, G ⊢a M $ N ⟹ T /\ typ_val G P v T.
  Proof.
    intros G [p' Hp'] * HG HM (i & p & a1 & v0 & Hp & Hag & HΠ & Ha1 & Hv0 & Hs) HN Hn' Hv'; cbn in *.
    assert (G ⊢ A : Typeω@i /\ G ▹ A ⊢ B : Typeω@i) as [HA HB] by mauto 3.
    assert (HN' : G ⊢ N : A) by (eapply alg_type_check_sound; eassumption).
    destruct (eval_of_typing _ _ _ _ Hp HN') as [n0 Hn0].
    pose proof (proj2 (feval_of_ref _ _ _ _ _ _ Hn0 (agree_all _ _ _ Hag)) _ Hn') as HsN.
    inversion Hs as [| ? ? ? ? ? ? Hρ0 | | | | | | | | | | | |]; subst.
    destruct (typ_val_pi _ _ _ _ _ _ _ _ _ _ _ Hp HΠ Ha1 Hv0 HN' Hn0) as (v1 & c & Hv1 & Hc & Hv1c).
    destruct (feval_clo_sim _ _ _ _ _ _ _ _ Hρ0 HsN Hv1) as (v1' & Hv1' & Hs1).
    rewrite (functional_feval_exp _ _ _ _ Hv' Hv1') in *.
    assert (HBN : G ⊢ B[Id,,N] : Typeω@i) by mauto 3.
    destruct (soundness_ty HBN) as (W & HW & HeqW).
    destruct (typ_val_conv _ _ _ _ _ _ _ Hp HeqW Hc Hv1c) as (c' & Hc' & Hvc').
    exists W; split; [ econstructor; eassumption |].
    exists i, p, c', v1; repeat split; try assumption.
    gen_presups; assumption.
  Qed.

  (** The type of a term as a value, from its normal form. *)
  Lemma typ_val_of_eval : forall G P (T : nf) (i : nat) v,
      G ⊢ T : Typeω@i -> ⟦ T ⟧ᶠ gc_deps ⍮ gc_stack ⍮ (proj1_sig P) ↘ v -> typ_val G P v T.
  Proof.
    intros G [p' (p & Hp & Hag)] * HT Hv; cbn in *.
    destruct (typ_val_self _ _ _ _ Hp HT) as (a & Ha & Haa).
    pose proof (proj2 (feval_of_ref _ _ _ _ _ _ Ha (agree_all _ _ _ Hag)) _ Hv).
    exists i, p, a, a; repeat split; assumption.
  Qed.

  (** The type of a term as a value evaluates. *)
  Lemma typ_val_eval_order : forall G (P : tenv G) (T : nf) (i : nat),
      G ⊢ T : Typeω@i -> feval_exp_order gc_deps gc_stack T (proj1_sig P).
  Proof.
    intros G [p' (p & Hp & Hag)] * HT; cbn in *.
    destruct (typ_val_self _ _ _ _ Hp HT) as (a & Ha & _).
    exact (proj1 (feval_of_ref _ _ _ _ _ _ Ha (agree_all _ _ _ Hag))).
  Qed.

  (** Whether a term is an application, and a value a [Π]. *)
  #[derive(equations=no,eliminator=no)]
  Equations get_app_parts (M : exp) : { M1 & { N1 | M = M1 $ N1 } } + { forall M1 N1, M <> M1 $ N1 } :=
  | M1 $ N1 => pureo (existT _ M1 (exist _ N1 _))
  | _       => inright _
  .

  #[derive(equations=no,eliminator=no)]
  Equations get_pi_val (v : domain) : { a & { ρ & { b | v = Πᵈ a ρ b } } } + { forall a ρ b, v <> Πᵈ a ρ b } :=
  | Πᵈ a ρ b => pureo (existT _ a (existT _ ρ (exist _ b _)))
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
    | HG : ⊢ ?G, HM : ?G ⊢a ?M ⟹ ?T, Hv : typ_val ?G ?P (Πᵈ ?a ?ρ ?b) ?T |- _ =>
        let A0 := fresh "A0" in let B0 := fresh "B0" in let i := fresh "i" in
        destruct (typ_val_pi_parts _ _ _ _ _ _ _ HG HM Hv) as (A0 & B0 & i & -> & ? & ?)
    end;
    functional_fread_rewrite_clear.

  (** The argument of an application, and the codomain at its value,
      evaluate. *)
  #[local]
  Ltac ob_app_order :=
    match goal with
    | HG : ⊢ ?G, HM : ?G ⊢a ?M ⟹ Πⁿ ?A ?B, Hv : typ_val ?G ?P (Πᵈ ?a ?ρ ?b) _, HN : ?G ⊢a ?N ⟸ (nf_to_exp ?A) |- _ =>
        let Ho1 := fresh "Ho" in let Ho2 := fresh "Ho" in
        destruct (typ_val_app_order _ _ _ _ _ _ _ _ _ HG HM Hv HN) as [Ho1 Ho2];
        first [ exact Ho1 | apply Ho2; assumption ]
    end.

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

  (** Its success: the rule [atc_ati], with the inferred type as its own
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
      let (A', _) := nbe_ty_env_impl gc_deps gc_stack G P A _ in
      let*b _ := subtyping_nf_impl B A' while _ in
      pureb _
  with type_infer_in G (HG : ⊢ G) (P : tenv G) M (H : type_infer_order M) : { A : nf | G ⊢a M ⟹ A /\ (exists UA u, G ⊢a A ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ A : Typeω@i) } + { forall A, ~ G ⊢a M ⟹ A } by struct H :=
  | G, HG, P, M, H with M => {
    | Typeω@j =>
        pureo (exist _ Typeωⁿ@(S j) _)
    | Type⟨M'⟩ =>
        let*o (exist _ LM _) := type_infer_in G _ P M' _ while _ in
        let*o (exist _ k _) := get_level_sort_nf LM while _ in
        let (W, _) := nbe_ty_env_impl gc_deps gc_stack G P Type⟨succl M'⟩ _ in
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
    | ℕ =>
        pureo (exist _ Typeⁿ@0 _)
    | zero =>
        pureo (exist _ ℕⁿ _)
    | succ M' =>
        let*b->o _ := type_check_in G ℕ _ P M' _ while _ in
        pureo (exist _ ℕⁿ _)
    | rec M' return A' | zero -> MZ | succ -> MS end =>
        let*b->o _ := type_check_in G ℕ _ P M' _ while _ in
        let HGN : ⊢ G ▹ ℕ := _ in
        let PN := tenv_ass G P ℕ HGN in
        let*o (exist _ UA' _) := type_infer_in (G ▹ ℕ) HGN PN A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let*b->o _ := type_check_in G A'[Id,,zero] _ P MZ _ while _ in
        let HAS : exists i, G ▹ ℕ ▹ A' ⊢ A'[Wk ⨟ Wk,,succ #1] : Typeω@i := _ in
        let*b->o _ := type_check_in (G ▹ ℕ ▹ A') A'[Wk ⨟ Wk,,succ #1] HAS
                        (tenv_ass (G ▹ ℕ) PN A' (tenv_ctx_of_typ _ _ HAS)) MS _ while _ in
        let (A'', _) := nbe_ty_env_impl gc_deps gc_stack G P A'[Id,,M'] _ in
        pureo (exist _ A'' _)
    | ⊤ =>
        pureo (exist _ Typeⁿ@0 _)
    | ⋆ =>
        pureo (exist _ ⊤ⁿ _)
    | ⊥ =>
        pureo (exist _ Typeⁿ@0 _)
    | efq M' return A' =>
        let*b->o _ := type_check_in G ⊥ _ P M' _ while _ in
        let HGF : ⊢ G ▹ ⊥ := _ in
        let*o (exist _ UA' _) := type_infer_in (G ▹ ⊥) HGF (tenv_ass G P ⊥ HGF) A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let (A'', _) := nbe_ty_env_impl gc_deps gc_stack G P A'[Id,,M'] _ in
        pureo (exist _ A'' _)
    | Π B C =>
        let*o (exist _ UB _) := type_infer_in G _ P B _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UB while _ in
        let HGB : ⊢ G ▹ B := _ in
        let*o (exist _ UC _) := type_infer_in (G ▹ B) HGB (tenv_ass G P B HGB) C _ while _ in
        let (UC', _) := nbe_ty_env_impl gc_deps gc_stack (G ▹ B) (tenv_ass G P B HGB) UC _ in
        let*o (exist _ v _) :=  univ_nf_idx_dec UC' while _ in
        let (W, _) := nbe_ty_env_impl gc_deps gc_stack G P (unf_pi_tm u v) _ in
        pureo (exist _ W _)
    | λ A' M' =>
        let*o (exist _ UA' _) := type_infer_in G _ P A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let HGA : ⊢ G ▹ A' := _ in
        let*o (exist _ B' _) := type_infer_in (G ▹ A') HGA (tenv_ass G P A' HGA) M' _ while _ in
        let (A'', _) := nbe_ty_env_impl gc_deps gc_stack G P A' _ in
        pureo (exist _ (Πⁿ A'' B') _)
    | M' $ N' =>
        let*o (exist _ v _) := type_infer_app_in G HG P M' N' _ while _ in
        let (W, _) := fread_typ_impl gc_deps gc_stack (List.length G) v _ in
        pureo (exist _ W _)
    | ℓ A' ≔ M' in B' =>
        let*o (exist _ UA' _) := type_infer_in G _ P A' _ while _ in
        let*o (exist _ u _) :=  univ_nf_idx_dec UA' while _ in
        let*b->o _ := type_check_in G A' _ P M' _ while _ in
        let HGD : ⊢ G ▸ A' ≔ M' := _ in
        let*o (exist _ C _) := type_infer_in (G ▸ A' ≔ M') HGD (tenv_def G P A' M' HGD) B' _ while _ in
        let (D, _) := nbe_ty_env_impl gc_deps gc_stack G P (C : nf)[Id,,M'] _ in
        pureo (exist _ D _)
    (** Without an annotation, the definiens's type is inferred. *)
    | ℓ ≔ M' in B' =>
        let*o (exist _ A _) := type_infer_in G _ P M' _ while _ in
        let HGD : ⊢ G ▸ (A : nf) ≔ M' := _ in
        let*o (exist _ C _) := type_infer_in (G ▸ (A : nf) ≔ M') HGD (tenv_def G P (A : nf) M' HGD) B' _ while _ in
        let (D, _) := nbe_ty_env_impl gc_deps gc_stack G P (C : nf)[Id,,M'] _ in
        pureo (exist _ D _)
    | ℓₘ U in B' =>
        let*b->o _ := unit_check G HG U _ while _ in
        let*o (exist _ C _) := type_infer_in (G ▹ₘ U) _ (tenv_mod G P U) B' _ while _ in
        let (D, _) := nbe_ty_env_impl gc_deps gc_stack G P (C : nf)[Id ,,ₘ me_lit U] _ in
        pureo (exist _ D _)
    (** A global infers the closed type that resolution returns for it,
        normalized at [G]; any other member, through its module. *)
    | a_mem M' x with inspect (modexp_spine M') => {
      | exist _ (R, nil, pre) Es with inspect (glob_lookup R pre x) => {
        | exist _ (Some A) Eg =>
            let (C, _) := nbe_ty_env_impl gc_deps gc_stack G P A _ in
            pureo (exist _ C _)
        | exist _ None Eg =>
          let*b->o HM := modexp_check G HG M' _ while _ in
          let*o (exist _ A _) := member_term_dec _ G M' (x :: nil) _ while _ in
          let (B, _) := nbe_ty_env_impl gc_deps gc_stack G P A _ in
          pureo (exist _ B _) }
      | exist _ (R, N :: args, pre) Es =>
          let*b->o HM := modexp_check G HG M' _ while _ in
          let*o (exist _ A _) := type_infer_in G HG P (apps (member_ref R (pre ++ x :: nil)) (N :: args)) _ while _ in
          pureo (exist _ A _) }
    | #x =>
        let*o (exist _ A _) := lookup G _ x while _ in
        let (A', _) := nbe_ty_env_impl gc_deps gc_stack G P A _ in
        pureo (exist _ A' _)
    }
  with ext_check G (HG : ⊢ G) Ψ (H : ext_order Ψ) : { G ⊢aˣ Ψ } + { ~ G ⊢aˣ Ψ } by struct H :=
  | G, HG, nil, H => left _
  | G, HG, ce_ass A :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let HΨ : ⊢ Ψ ++ G := _ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ (tenv_of (Ψ ++ G) HΨ) A _ while _ in
      let*o->b (exist _ u _) := univ_nf_idx_dec UA while _ in
      pureb _
  | G, HG, ce_def A M :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let HΨ : ⊢ Ψ ++ G := _ in
      let PΨ := tenv_of (Ψ ++ G) HΨ in
      let*o->b (exist _ UA _) := type_infer_in (Ψ ++ G) HΨ PΨ A _ while _ in
      let*o->b (exist _ u _) := univ_nf_idx_dec UA while _ in
      let*b _ := type_check_in (Ψ ++ G) A _ PΨ M _ while _ in
      pureb _
  | G, HG, ce_mod U :: Ψ, H =>
      let*b _ := ext_check G HG Ψ _ while _ in
      let*b _ := unit_check (Ψ ++ G) _ U _ while _ in
      pureb _
  with unit_check G (HG : ⊢ G) U (H : unit_order U) : { G ⊢aᵘ U } + { ~ G ⊢aᵘ U } by struct H :=
  | G, HG, gu_mk Δ (md_body Φ), H =>
      let*b _ := ext_check G HG (body_ctx Φ ++ Δ) _ while _ in
      let*b _ := tele_ass_dec Δ while _ in
      let*b _ := body_shape_dec Φ Φ while _ in
      let*b _ := names_nodup_dec (gm_names Φ) while _ in
      pureb _
  | G, HG, gu_mk Δ (md_alias E), H =>
      let*b _ := ext_check G HG Δ _ while _ in
      let*b _ := tele_ass_dec Δ while _ in
      let*b _ := modexp_check (Δ ++ G) _ E _ while _ in
      pureb _
  with modexp_check G (HG : ⊢ G) M (H : modexp_order M) : { G ⊢aᵐ M } + { ~ G ⊢aᵐ M } by struct H :=
  | G, HG, me_unit fp, H =>
      let*o->b (exist _ T _) := member_chain_mod_dec _ G (me_unit fp) (q_abs fp nil) eq_refl while _ in
      pureb _
  | G, HG, me_var x, H with inspect (ctx_find_mod G x) := {
    | exist _ (Some U) E => left _
    | exist _ None E => right _ }
  | G, HG, me_lit U, H =>
      let*b _ := unit_check G HG U _ while _ in
      pureb _
  | G, HG, me_mem M y, H with inspect (mod_qname (me_mem M y)) := {
    | exist _ (Some mq) Ep =>
        let*o->b (exist _ T _) := member_chain_mod_dec _ G (me_mem M y) mq Ep while _ in
        pureb _
    | exist _ None Ep =>
        let*b HM := modexp_check G HG M _ while _ in
        let*o->b (exist _ T _) := member_mod_dec _ G M (y :: nil) _ while _ in
        pureb _ }
  | G, HG, me_app M N, H =>
      let*b HM := modexp_check G HG M _ while _ in
      let*o->b (exist _ T _) := member_mod_dec _ G M nil _ while _ in
      let*o->b (existT _ B (exist _ T1 _)) := tele_view_dec T while _ in
      let*b _ := type_check_in G B _ (tenv_of G HG) N _ while _ in
      pureb _
  (** The type of an application [M $ N], as a value. *)
  with type_infer_app_in G (HG : ⊢ G) (P : tenv G) M N (H : app_order M N) :
      { v : domain | exists T, G ⊢a M $ N ⟹ T /\ typ_val G P v T } + { forall A, ~ G ⊢a M $ N ⟹ A } by struct H :=
  | G, HG, P, M, N, H =>
      let*o (exist _ v _) := type_infer_val_in G HG P M _ while _ in
      let*o (existT _ a (existT _ ρ' (exist _ b _))) := get_pi_val v while _ in
      let (A, _) := fread_typ_impl gc_deps gc_stack (List.length G) a _ in
      let*b->o _ := type_check_in G (A : nf) _ P N _ while _ in
      let (n, _) := feval_exp_impl gc_deps gc_stack N (proj1_sig P) _ in
      let (v', _) := feval_exp_impl gc_deps gc_stack b (ρ' ↦ n) _ in
      pureo (exist _ v' _)
  (** The type of the head of an application, as a value: an application's
      directly, any other term's by evaluating its normal form. *)
  with type_infer_val_in G (HG : ⊢ G) (P : tenv G) M (H : type_check_order M) :
      { v : domain | exists T, G ⊢a M ⟹ T /\ typ_val G P v T } + { forall A, ~ G ⊢a M ⟹ A } by struct H :=
  | G, HG, P, M, H with get_app_parts M => {
    | inleft (existT _ M1 (exist _ N1 _)) =>
        let*o (exist _ v _) := type_infer_app_in G HG P M1 N1 _ while _ in
        pureo (exist _ v _)
    | inright _ =>
        let*o (exist _ T _) := type_infer_in G HG P M _ while _ in
        let (v, _) := feval_exp_impl gc_deps gc_stack T (proj1_sig P) _ in
        pureo (exist _ v _) }
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
  Obligation 30. (* G ⊢a ℕ ⟹ Typeⁿ@0 /\ (exists (UA : nf) (u : unf), G ⊢a Ty... *) ob_post_suniv0. Qed.
  Obligation 31. (* G ⊢a zero ⟹ ℕⁿ /\ (exists (UA : nf) (u : unf), G ⊢a ℕ ⟹ U... *) ob_post. Qed.
  Obligation 32. (* exists i : nat, G ⊢ ℕ : Typeω@i *) ob_typ_closed. Qed.
  Obligation 33. (* type_check_order M' *) ob_ord. Defined.
  Obligation 34. (* False *) ob_neg. Qed.
  Obligation 35. (* G ⊢a succ M' ⟹ ℕⁿ /\ (exists (UA : nf) (u : unf), G ⊢a ℕ ... *) ob_post. Qed.
  Obligation 36. (* exists i : nat, G ⊢ ℕ : Typeω@i *) ob_typ_closed. Qed.
  Obligation 37. (* type_check_order M' *) ob_ord. Defined.
  Obligation 38. (* False *) ob_neg. Qed.
  Obligation 39. (* ⊢ G ▹ ℕ *) ob_ctx_ext. Qed.
  Obligation 40. (* type_infer_order A' *) ob_ord. Defined.
  Obligation 41. (* False *) ob_neg. Qed.
  Obligation 42. (* False *) ob_neg. Qed.
  Obligation 43. (* exists j, G ⊢ A'[Id,,zero] : Typeω@j *)
    clear_defs.
    assert (G ⊢ ℕ : Typeω@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢s Id,,zero : G ▹ ℕ) as Hσ by mauto 3.
    (** [sub_preserves_exp] is applied by hand: unifying its conclusion would
        require solving [?A[?σ] ≟ Typeω@i], which [eapply] cannot do. *)
    match goal with HA' : G ▹ ℕ ⊢ A' : Typeω@?k |- _ =>
      exists k; exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
  Qed.
  Obligation 44. (* type_check_order MZ *) ob_ord. Defined.
  Obligation 45. (* False *) ob_neg. Qed.
  Obligation 46. (* exists j, G ▹ ℕ ▹ A' ⊢ A'[Wk ⨟ Wk,,succ #1] : Typeω@j *)
    clear_defs.
    assert (G ⊢ ℕ : Typeω@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    saturate_infer_univ.
    assert (⊢ G ▹ ℕ ▹ A') by mauto 2.
    assert (G ▹ ℕ ▹ A' ⊢s Wk ⨟ Wk,,succ #1 : G ▹ ℕ) as Hσ by mauto 3.
    match goal with HA' : G ▹ ℕ ⊢ A' : Typeω@?k |- _ =>
      exists k; exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
  Qed.
  Obligation 47. (* type_check_order MS *) ob_ord. Defined.
  Obligation 48. (* False *) ob_neg. Qed.
  Obligation 49. (* nbe_ty_order gc_deps gc_stack G A'[Id,,M'] *)
    clear_defs.
    enough (exists i, G ⊢ A'[Id,,M'] : Typeω@i) as [? [? []]%wf_exp_eq_refl%completeness_ty]
        by eauto 3 using nbe_ty_order_sound.
    assert (G ⊢ ℕ : Typeω@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢ M' : ℕ) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ℕ) as Hσ by mauto 3.
    match goal with HA' : G ▹ ℕ ⊢ A' : Typeω@?k |- _ =>
      exists k; exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
  Qed.
  Obligation 50. (* G ⊢a rec M' … end ⟹ A'', and [A''] is a type *)
    clear_defs.
    split; [ mauto 3 |].
    assert (G ⊢ ℕ : Typeω@0) by mauto 2.
    assert (⊢ G ▹ ℕ) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢ M' : ℕ) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ℕ) as Hσ by mauto 3.
    (** The motive at the scrutinee is a type, so its normal form is one too,
        and [level_of_nbe] gives both halves at once. *)
    match goal with HA' : G ▹ ℕ ⊢ A' : Typeω@?k |- _ =>
      assert (G ⊢ A'[Id,,M'] : Typeω@k) by exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 51. (* G ⊢a ⊤ ⟹ Typeⁿ@0 /\ (exists (UA : nf) (u : unf), G ⊢a Ty... *) ob_post_suniv0. Qed.
  Obligation 52. (* G ⊢a ⋆ ⟹ ⊤ⁿ /\ (exists (UA : nf) (u : unf), G ⊢a ⊤ ⟹ UA /... *) ob_post. Qed.
  Obligation 53. (* G ⊢a ⊥ ⟹ Typeⁿ@0 /\ (exists (UA : nf) (u : unf), G ⊢a Ty... *) ob_post_suniv0. Qed.
  Obligation 54. (* exists i : nat, G ⊢ ⊥ : Typeω@i *) ob_typ_closed. Qed.
  Obligation 55. (* type_check_order M' *) ob_ord. Defined.
  Obligation 56. (* False *) ob_neg. Qed.
  Obligation 57. (* ⊢ G ▹ ⊥ *) ob_ctx_ext. Qed.
  Obligation 58. (* type_infer_order A' *) ob_ord. Defined.
  Obligation 59. (* False *) ob_neg. Qed.
  Obligation 60. (* False *) ob_neg. Qed.
  Obligation 61. (* nbe_ty_order gc_deps gc_stack G A'[Id,,M'] *)
    clear_defs.
    enough (exists i, G ⊢ A'[Id,,M'] : Typeω@i) as [? [? []]%wf_exp_eq_refl%completeness_ty]
        by eauto 3 using nbe_ty_order_sound.
    assert (G ⊢ ⊥ : Typeω@0) by mauto 2.
    assert (⊢ G ▹ ⊥) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢ M' : ⊥) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ⊥) as Hσ by mauto 3.
    match goal with HA' : G ▹ ⊥ ⊢ A' : Typeω@?k |- _ =>
      exists k; exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
  Qed.
  Obligation 62. (* G ⊢a efq M' return A' ⟹ A'', and [A''] is a type *)
    clear_defs.
    split; [ mauto 3 |].
    assert (G ⊢ ⊥ : Typeω@0) by mauto 2.
    assert (⊢ G ▹ ⊥) by mauto 2.
    saturate_infer_univ.
    assert (G ⊢ M' : ⊥) by mauto 3 using alg_type_check_sound.
    assert (G ⊢s Id,,M' : G ▹ ⊥) as Hσ by mauto 3.
    match goal with HA' : G ▹ ⊥ ⊢ A' : Typeω@?k |- _ =>
      assert (G ⊢ A'[Id,,M'] : Typeω@k) by exact (sub_preserves_exp _ _ _ _ _ _ _ HA' Hσ) end.
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 63. Qed.
  Obligation 64. (* type_infer_order B *) ob_ord. Defined.
  Obligation 65. (* False *) ob_neg. Qed.
  Obligation 66. (* False *) ob_neg. Qed.
  Obligation 67. (* ⊢ G ▹ B *) ob_ctx. Qed.
  Obligation 68. (* type_infer_order C *) ob_ord. Defined.
  Obligation 69. (* False *) ob_neg. Qed.
  Obligation 70. (* nbe_ty_order gc_deps gc_stack (G ▹ B) UC *)
    clear_defs.
    destruct_conjs.
    match goal with H : G ▹ B ⊢ (?UC : exp) : Typeω@?i |- nbe_ty_order _ _ _ ?UC =>
      destruct (soundness_ty H) as [W [HW _]] end.
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 71. (* False: the codomain's universe, normalised, is no universe *)
    clear_defs.
    lazymatch goal with H : _ ⊢a _ ⟹ _ |- False => inversion H; subst; clear H end.
    destruct_conjs.
    functional_alg_type_infer_rewrite_clear.
    functional_nbe_rewrite_clear.
    firstorder.
  Qed.
  Obligation 72. (* nbe_ty_order gc_deps gc_stack G (unf_pi_tm u v) *)
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
  Obligation 73. (* G ⊢a Π B C ⟹ W, the normal form of its universe, and that is a type *)
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
    split; [ eapply ati_pi; eassumption |].
    split; [| eexists; exact HWk ].
    destruct (alg_type_infer_large_typ_complete (user_exp_nf W) HWk) as [? [? [? [? _]]]].
    do 2 eexists; split; eassumption.
  Qed.
  Obligation 74. Qed.
  Obligation 75. (* type_infer_order A' *) ob_ord. Defined.
  Obligation 76. (* False *) ob_neg. Qed.
  Obligation 77. (* False *) ob_neg. Qed.
  Obligation 78. (* ⊢ G ▹ A' *) ob_ctx. Qed.
  Obligation 79. (* type_infer_order M' *) ob_ord. Defined.
  Obligation 80. (* False *) ob_neg. Qed.
  Obligation 81. (* nbe_ty_order gc_deps gc_stack G A' *)
    clear_defs.
    saturate_infer_univ.
    match goal with H : G ⊢ A' : Typeω@?k |- _ =>
      assert (G ⊢ A' : Typeω@k) as [? []]%soundness_ty by exact H end.
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 82. (* G ⊢a λ A' M' ⟹ Πⁿ A'' B', and [Π A'' B'] is a type *)
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
    - exists (max (unf_large u) l); apply wf_pi;
        [ mauto 3 using lift_exp_max_left | mauto 3 using lift_exp_max_right ].
  Qed.
  Obligation 83. (* app_order M' N' *) ob_ord. Defined.
  Obligation 84. (* False *) ob_neg_direct. Qed.
  Obligation 85. (* read_typ_order gc_deps gc_stack (List.length G) v *)
    clear_defs; destruct_conjs.
    eapply fread_typ_order_sound, typ_val_rtyp; eassumption.
  Qed.
  Obligation 86. (* G ⊢a M' $ N' ⟹ W, and [W] is a type *)
    clear_defs; destruct_conjs.
    match goal with Hi : G ⊢a _ ⟹ ?T, Hv : typ_val G P ?v ?T |- _ =>
      pose proof (typ_val_rtyp _ _ _ _ _ HG Hi Hv); destruct Hv as (? & ? & ? & ? & ? & ? & ? & _) end.
    functional_fread_rewrite_clear.
    split; [ assumption | eapply infer_post_of_typ; eassumption ].
  Qed.
  Obligation 87. Qed.
  Obligation 88. (* False *) ob_neg. Qed.
  Obligation 89. (* nbe_ty_order gc_deps gc_stack G A *)
    clear_defs.
    assert (exists i, G ⊢ A : Typeω@i) as [? [? []]%soundness_ty] by mauto 3.
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 90. (* G ⊢a #x ⟹ A', and [A'] is a type *)
    clear_defs.
    assert (exists i, G ⊢ A : Typeω@i) as [i] by mauto 3.
    split; [ mauto 3 |].
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 91. Qed.
  Obligation 92. (* type_infer_order A' *) ob_ord. Defined.
  Obligation 93. (* False *) ob_neg. Qed.
  Obligation 94. (* False *) ob_neg. Qed.
  Obligation 95. (* exists i, G ⊢ A' : Typeω@i *)
    clear_defs.
    eexists; saturate_infer_univ; eassumption.
  Qed.
  Obligation 96. (* type_check_order M' *) ob_ord. Defined.
  Obligation 97. (* False *) ob_neg. Qed.
  Obligation 98. (* ⊢ G ▸ A' ≔ M' *) ob_ctx. Qed.
  Obligation 99. (* type_infer_order B' *) ob_ord. Defined.
  Obligation 100. (* False *) ob_neg. Qed.
  Obligation 101. (* nbe_ty_order gc_deps gc_stack G C[Id,,M'] *)
    clear_defs.
    destruct_conjs.
    saturate_infer_univ.
    assert (G ⊢ M' : A') by mauto 3 using alg_type_check_sound.
    assert (⊢ G ▸ A' ≔ M') by mauto 3.
    assert (G ⊢s Id,,M' : G ▸ A' ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Typeω@k) as [? [? []]%soundness_ty] by (eexists; mauto 3).
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 102. (* G ⊢a ℓ A' ≔ M' in B' ⟹ D /\ (D is a type) *)
    clear_defs.
    split; [mauto 3 |].
    destruct_conjs.
    saturate_infer_univ.
    assert (G ⊢ M' : A') by mauto 3 using alg_type_check_sound.
    assert (⊢ G ▸ A' ≔ M') by mauto 3.
    assert (G ⊢s Id,,M' : G ▸ A' ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Typeω@k) as [? ?] by (eexists; mauto 3).
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 103. Qed.
  Obligation 104. (* type_infer_order M' *) ob_ord. Defined.
  Obligation 105. (* False *) ob_neg. Qed.
  Obligation 106. (* ⊢ G ▸ A ≔ M' *)
    clear_defs.
    destruct_conjs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    mauto 3.
  Qed.
  Obligation 107. (* type_infer_order B' *) ob_ord. Defined.
  Obligation 108. (* False *) ob_neg. Qed.
  Obligation 109. (* nbe_ty_order gc_deps gc_stack G C[Id,,M'] *)
    clear_defs.
    destruct_conjs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    assert (⊢ G ▸ A ≔ M') by mauto 3.
    assert (G ⊢s Id,,M' : G ▸ A ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Typeω@k) as [? [? []]%soundness_ty] by (eexists; mauto 3).
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 110. (* G ⊢a ℓ ≔ M' in B' ⟹ D /\ (D is a type) *)
    clear_defs.
    split; [mauto 3 |].
    destruct_conjs.
    assert (G ⊢ M' : A) by mauto 3 using alg_type_infer_sound.
    assert (⊢ G ▸ A ≔ M') by mauto 3.
    assert (G ⊢s Id,,M' : G ▸ A ≔ M') by (eapply wf_sub_single_def; eassumption).
    assert (exists k, G ⊢ C[Id,,M'] : Typeω@k) as [? ?] by (eexists; mauto 3).
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 111. (* unit_order U *) ob_ord. Defined.
  Obligation 112. (* False *) ob_neg. Qed.
  Obligation 113. (* ⊢ G ▹ₘ U *) ob_ctx. Qed.
  Obligation 114. (* type_infer_order B' *) ob_ord. Defined.
  Obligation 115. (* False *) ob_neg. Qed.
  Obligation 116. (* nbe_ty_order gc_deps gc_stack G C[Id ,,ₘ me_lit U] *)
    clear_defs.
    assert (gc_deps ⍮ gc_stack ⍮ G ⊢ᵘ U ≈ U) by (eapply alg_unit_sound; eassumption).
    assert (⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; eassumption).
    assert (G ⊢s Id ,,ₘ me_lit U : G ▹ₘ U) by (eapply wf_sub_single_mod; eassumption).
    assert (exists k, G ⊢ C[Id ,,ₘ me_lit U] : Typeω@k) as [? [? []]%soundness_ty]
        by (eexists; mauto 3).
    mauto 3 using nbe_ty_order_sound.
  Qed.
  Obligation 117. (* G ⊢a ℓₘ U in B' ⟹ D, and [D] is a type *)
    clear_defs.
    split; [ mauto 3 |].
    assert (gc_deps ⍮ gc_stack ⍮ G ⊢ᵘ U ≈ U) by (eapply alg_unit_sound; eassumption).
    assert (⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; eassumption).
    assert (G ⊢s Id ,,ₘ me_lit U : G ▹ₘ U) by (eapply wf_sub_single_mod; eassumption).
    assert (exists k, G ⊢ C[Id ,,ₘ me_lit U] : Typeω@k) as [? ?] by (eexists; mauto 3).
    eapply level_of_nbe; eassumption.
  Qed.
  Obligation 118. (* nbe_ty_order gc_deps gc_stack G A *) mo_1. Qed.
  Obligation 119. (* G ⊢a a_mem M' x ⟹ C /\ (exists (UA : nf) (u : unf), G ⊢a ... *) mo_1. Qed.
  Obligation 120. (* modexp_order M' *) ob_ord. Defined.
  Obligation 121. (* False *) ob_mem_neg. Qed.
  Obligation 122. (* ⊢g gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 123. (* gc_deps ⍮ gc_stack ⍮ G ⊢ᵐ M' ≈ M' *) mo_18. Qed.
  Obligation 124. (* False *) ob_mem_neg. Qed.
  Obligation 125. (* nbe_ty_order gc_deps gc_stack G A *) mo_7. Qed.
  Obligation 126. (* G ⊢a a_mem M' x ⟹ B /\ (exists (UA : nf) (u : unf), G ⊢a ... *) mo_8. Qed.
  Obligation 127. (* modexp_order M' *) ob_ord. Defined.
  Obligation 128. (* False *) ob_mem_neg. Qed.
  Obligation 129. (* type_infer_order (apps (member_ref R (pre ++ x :: nil) $ ... *) ob_ord_apps. Defined.
  Obligation 130. (* False *) ob_mem_neg. Qed.
  Obligation 131. (* G ⊢a a_mem M' x ⟹ A /\ (exists (UA : nf) (u : unf), G ⊢a ... *) mo_9. Qed.
  Obligation 132. (* G ⊢aˣ ⋅ *) ob_check. Qed.
  Obligation 133. (* ext_order Ψ *) ob_ord. Defined.
  Obligation 134. (* False *) mo_10. Qed.
  Obligation 135. (* ⊢ Ψ ++ G *) ob_ctx. Qed.
  Obligation 136. (* type_infer_order A *) ob_ord. Defined.
  Obligation 137. (* False *) mo_10. Qed.
  Obligation 138. (* False *) mo_10. Qed.
  Obligation 139. (* G ⊢aˣ Ψ ▹ A *) ob_check. Qed.
  Obligation 140. (* ext_order Ψ *) ob_ord. Defined.
  Obligation 141. (* False *) mo_10. Qed.
  Obligation 142. (* ⊢ Ψ ++ G *) ob_ctx. Qed.
  Obligation 143. (* type_infer_order A *) ob_ord. Defined.
  Obligation 144. (* False *) mo_10. Qed.
  Obligation 145. (* False *) mo_10. Qed.
  Obligation 146. (* exists i0 : nat, Ψ ++ G ⊢ A : Typeω@i0 *) mo_14. Qed.
  Obligation 147. (* type_check_order M *) ob_ord. Defined.
  Obligation 148. (* False *) mo_10. Qed.
  Obligation 149. (* G ⊢aˣ Ψ ▸ A ≔ M *) ob_check. Qed.
  Obligation 150. (* ext_order Ψ *) ob_ord. Defined.
  Obligation 151. (* False *) mo_10. Qed.
  Obligation 152. (* ⊢ Ψ ++ G *) ob_ctx. Qed.
  Obligation 153. (* unit_order U *) ob_ord. Defined.
  Obligation 154. (* False *) mo_10. Qed.
  Obligation 155. (* G ⊢aˣ Ψ ▹ₘ U *) ob_check. Qed.
  Obligation 156. (* ext_order (body_ctx Φ ++ Δ) *) ob_ord. Defined.
  Obligation 157. (* False *) mo_10. Qed.
  Obligation 158. (* False *) mo_10. Qed.
  Obligation 159. (* False *) mo_10. Qed.
  Obligation 160. (* False *) mo_10. Qed.
  Obligation 161. (* G ⊢aᵘ gu_body Δ Φ *) ob_check. Qed.
  Obligation 162. (* ext_order Δ *) ob_ord. Defined.
  Obligation 163. (* False *) mo_10. Qed.
  Obligation 164. (* False *) mo_10. Qed.
  Obligation 165. (* ⊢ Δ ++ G *) ob_ctx. Qed.
  Obligation 166. (* modexp_order E *) ob_ord. Defined.
  Obligation 167. (* False *) mo_10. Qed.
  Obligation 168. (* G ⊢aᵘ gu_mk Δ (md_alias E) *) ob_check. Qed.
  Obligation 169. (* ⊢g gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 170. (* False *) mo_10. Qed.
  Obligation 171. (* G ⊢aᵐ me_unit fp *) mo_2. Qed.
  Obligation 172. (* G ⊢aᵐ me_var x *) mo_19. Qed.
  Obligation 173. (* False *) mo_20. Qed.
  Obligation 174. (* ⊢g gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 175. (* False *) mo_3. Qed.
  Obligation 176. (* G ⊢aᵐ me_mem M y *) ob_check. Qed.
  Obligation 177. (* modexp_order M *) ob_ord. Defined.
  Obligation 178. (* False *) mo_3. Qed.
  Obligation 179. (* ⊢g gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 180. (* gc_deps ⍮ gc_stack ⍮ G ⊢ᵐ M ≈ M *) mo_18. Qed.
  Obligation 181. (* False *) mo_10. Qed.
  Obligation 182. (* G ⊢aᵐ me_mem M y *) ob_check. Qed.
  Obligation 183. (* modexp_order M *) ob_ord. Defined.
  Obligation 184. (* False *) mo_10. Qed.
  Obligation 185. (* ⊢g gc_deps ⍮ gc_stack *) ob_check. Qed.
  Obligation 186. (* gc_deps ⍮ gc_stack ⍮ G ⊢ᵐ M ≈ M *) mo_18. Qed.
  Obligation 187. (* False *) mo_10. Qed.
  Obligation 188. (* False *) mo_21. Qed.
  Obligation 189. (* exists i : nat, G ⊢ B : Typeω@i *) mo_22. Qed.
  Obligation 190. (* type_check_order N *) ob_ord. Defined.
  Obligation 191. (* False *) mo_21. Qed.
  Obligation 192. (* G ⊢aᵐ me_app M N *) ob_check. Qed.
  Obligation 193. (* unit_order U *) ob_ord. Defined.
  Obligation 194. (* False *) mo_10. Qed.
  Obligation 195. (* G ⊢aᵐ me_lit U *) ob_check. Qed.
  Obligation 196. (* type_check_order M *) ob_ord. Defined.
  Obligation 197. (* False *) ob_neg. Qed.
  Obligation 198. (* False: the head's type is not a [Π] *)
    clear_defs; intros; destruct_conjs.
    try match goal with |- ~ _ => intro end.
    match goal with H : _ ⊢a _ $ _ ⟹ _ |- False => inversion H; subst; clear H end.
    functional_alg_type_infer_rewrite_clear.
    match goal with Hi : G ⊢a M ⟹ ?T, Hv : typ_val G P ?v ?T |- _ =>
      pose proof (typ_val_rtyp _ _ _ _ _ HG Hi Hv) as Hr end.
    inversion Hr; subst.
    firstorder congruence.
  Qed.
  Obligation 199. (* read_typ_order gc_deps gc_stack (List.length G) a *)
    ob_pi_parts; eapply fread_typ_order_sound; eassumption.
  Qed.
  Obligation 200. (* exists i, G ⊢ A : Typeω@i *)
    ob_pi_parts.
    match goal with H : G ⊢ Π ?A0 ?B0 : Typeω@?i |- _ =>
      assert (G ⊢ A0 : Typeω@i /\ G ▹ A0 ⊢ B0 : Typeω@i) as [? ?] by mauto 3; eexists; eassumption end.
  Qed.
  Obligation 201. (* type_check_order N *) ob_ord. Defined.
  Obligation 202. (* False: the argument does not check *)
    ob_pi_parts; try match goal with |- ~ _ => intro end.
    match goal with H : _ ⊢a _ $ _ ⟹ _ |- False => inversion H; subst; clear H end.
    functional_alg_type_infer_rewrite_clear.
    autoinjections; subst; contradiction.
  Qed.
  Obligation 203. (* feval_exp_order gc_deps gc_stack N (proj1_sig P) *)
    ob_pi_parts; ob_app_order.
  Qed.
  Obligation 204. (* feval_exp_order gc_deps gc_stack b (ρ' ↦ n) *)
    ob_pi_parts; ob_app_order.
  Qed.
  Obligation 205. (* exists T, G ⊢a M $ N ⟹ T /\ typ_val G P v' T *)
    ob_pi_parts; eapply typ_val_app_step; eassumption.
  Qed.
  Obligation 206. (* app_order M1 N1 *) clear_defs; subst; ob_ord. Defined.
  Obligation 207. (* False *) ob_neg_direct. Qed.
  Obligation 208. (* exists T, G ⊢a M1 $ N1 ⟹ T /\ typ_val G P v T *) clear_defs; destruct_conjs; subst; eexists; split; eassumption. Qed.
  Obligation 209. (* type_infer_order M *) ob_ord. Defined.
  Obligation 210. (* False *) ob_neg_direct. Qed.
  Obligation 211. (* feval_exp_order gc_deps gc_stack T (proj1_sig P) *)
    clear_defs; destruct_conjs; eapply typ_val_eval_order; eassumption.
  Qed.
  Obligation 212. (* exists T0, G ⊢a M ⟹ T0 /\ typ_val G P v T0 *)
    clear_defs; destruct_conjs.
    eexists; split; [ eassumption | eapply typ_val_of_eval; eassumption ].
  Qed.


  Extraction Inline type_check_in_functional type_infer_in_functional ext_check_functional
    unit_check_functional modexp_check_functional.

  (** The checker from scratch: the initial environment of the context is
      computed once, at the start. *)
  Definition type_check G A (HA : exists i, G ⊢ A : Typeω@i) M (H : type_check_order M) :
      { G ⊢a M ⟸ A } + { ~ G ⊢a M ⟸ A } :=
    type_check_in G A HA (tenv_of G (tenv_ctx_of_typ _ _ HA)) M H.

  Definition type_infer G (HG : ⊢ G) M (H : type_infer_order M) :
      { A : nf | G ⊢a M ⟹ A /\ (exists UA u, G ⊢a A ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ A : Typeω@i) } +
      { forall A, ~ G ⊢a M ⟹ A } :=
    type_infer_in G HG (tenv_of G HG) M H.

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
  { induction Ψ as [| [A | A M | U] Ψ IH]; inversion HΨ; subst; constructor;
      eauto using type_infer_order_all, unit_order_all, tc_ti. }
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
  Equations type_check_closed (Hg : ⊢g gc_deps ⍮ gc_stack) A (HA : user_exp A) M (HM : user_exp M) : { ⋅ ⊢ M : A } + { ~ ⋅ ⊢ M : A } :=
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

Lemma type_check_closed_complete : forall (Hg : ⊢g gc_deps ⍮ gc_stack) A (HA : user_exp A) M (HM : user_exp M),
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
  Equations type_infer_closed (Hg : ⊢g gc_deps ⍮ gc_stack) M (HM : user_exp M) : { A : nf | ⋅ ⊢ M : A } + { forall A, ~ ⋅ ⊢a M ⟹ A } :=
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
