(** * Glued Arguments along a Telescope

    The machinery the gluing of the inductive types is built from: lists of
    terms glued positionwise to lists of values along a telescope
    ([glu_args]) make glued substitutions ([glu_sub_of_list]); a closed
    constant whose applications to glued arguments are glued, with values
    given by a relation along the arguments, is glued at a [Π] over the
    telescope ([ctx_pi_glu_elem_by]).  The rest are facts about the
    instances of the telescopes of a group's members. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  LevelCases
  LogicalRelation
  SubtypingCases
  VariableCases
  UniverseCases.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Glued Arguments

    A list of terms glued positionwise to a list of values along a
    telescope [C] (innermost first), each at the instance of its type at the
    terms before it, over a base [τ] and [ρ]. *)
(** One argument: the type [A], evaluated in [ρ], is glued at a universe,
    and the term [M] at its instance [T] to the value [v]. *)
#[warnings="-cannot-define-projection"]
Record glu_arg (Δ : ctx) (ρ : env) (A T M : exp) (v : domain) : Prop := mk_glu_arg
  { (** The universe index *)
    ga_lvl : uidx
    (** The type's value *)
  ; ga_val : domain
    (** Its type predicate *)
  ; ga_typ : glu_typ_pred
    (** Its element predicate *)
  ; ga_exp : glu_exp_pred
    (** [A] evaluates in [ρ] to it *)
  ; ga_eval : ⟦ A ⟧ ρ ↘ ga_val
    (** It is glued at the universe *)
  ; ga_elem : DG ga_val ∈ glu_univ_elem ga_lvl ↘ ga_typ ↘ ga_exp
    (** [T] is glued to it *)
  ; ga_glu_typ : Δ ⊢ T ® ga_typ
    (** [M] at [T] is glued to [v] *)
  ; ga_glu : Δ ⊢ M : T ® v ∈ ga_exp }.

(** The terms [Ms] glued to the values [vs] along [C], positionwise. *)
Record glu_args (Δ : ctx) (C : ctx) (τ : sub) (ρ : env) (Ms : list exp) (vs : list domain) : Prop := mk_glu_args
  { (** One term per entry *)
    gas_len : List.length Ms = List.length C
    (** One value per entry *)
  ; gas_vals_len : List.length vs = List.length C
    (** Each term glued to its value at its type, after those before *)
  ; gas_glu : forall k M T v A, List.nth_error Ms k = Some M -> List.nth_error (tele_insts C τ Ms) k = Some T ->
      List.nth_error vs k = Some v -> List.nth_error (List.rev C) k = Some (ce_ass A) ->
      glu_arg Δ (env_args ρ (List.firstn k vs)) A T M v }.

Lemma glu_args_nil : forall Δ τ ρ, glu_args Δ nil τ ρ nil nil.
Proof. intros; constructor; [ reflexivity | reflexivity |]; intros [] *; discriminate. Qed.

Lemma glu_args_snoc : forall Δ C A τ ρ M Ms v vs,
    glu_args Δ (C ++ ⋅ ▹ A) τ ρ (M :: Ms) (v :: vs) <->
    glu_arg Δ ρ A A[τ] M v /\ glu_args Δ C (τ,,M) (ρ ↦ v) Ms vs.
Proof.
  intros; split.
  - intros [L1 L2 H]; rewrite tele_insts_snoc, List.rev_app_distr, !List.length_app in *;
      cbn [List.rev List.app List.length] in *.
    split; [ exact (H 0 _ _ _ _ eq_refl eq_refl eq_refl eq_refl) |].
    constructor; [ lia | lia |].
    intros k M' T v' A' HM HT Hv HA; exact (H (S k) _ _ _ _ HM HT Hv HA).
  - intros [H0 [L1 L2 H]]; constructor;
      rewrite ?tele_insts_snoc, ?List.rev_app_distr, ?List.length_app; cbn [List.rev List.app List.length];
      [ lia | lia |].
    intros [| k] M' T v' A' HM HT Hv HA; cbn in HM, HT, Hv, HA.
    + injection HM as <-; injection HT as <-; injection Hv as <-; injection HA as <-; exact H0.
    + exact (H k _ _ _ _ HM HT Hv HA).
Qed.

Lemma glu_args_typed : forall Δ C τ ρ Ms vs, tele_ass C -> glu_args Δ C τ ρ Ms vs ->
    forall k M T, List.nth_error Ms k = Some M -> List.nth_error (tele_insts C τ Ms) k = Some T -> Δ ⊢ M : T.
Proof.
  intros * Hass [L1 L2 H] k M T HM HT.
  assert (Hk : k < List.length C) by (rewrite <- L1; apply List.nth_error_Some; congruence).
  destruct (nth_error_lt_some vs k ltac:(lia)) as [v Hv].
  assert (HA : exists A, List.nth_error (List.rev C) k = Some (ce_ass A)).
  { destruct (nth_error_lt_some (List.rev C) k ltac:(rewrite List.length_rev; lia)) as [e He].
    pose proof (List.nth_error_In _ _ He) as Hin; apply List.in_rev in Hin.
    unfold tele_ass in Hass; rewrite List.Forall_forall in Hass; destruct (Hass _ Hin) as [A ->]; eauto. }
  destruct HA as [A HA].
  destruct (H _ _ _ _ _ HM HT Hv HA) as [i a P El _ Hglu _ HMg].
  eapply glu_univ_elem_trm_escape; eassumption.
Qed.

Lemma glu_args_sb_eq : forall Δ C τ τ' ρ Ms vs, sb_eq τ τ' -> glu_args Δ C τ ρ Ms vs -> glu_args Δ C τ' ρ Ms vs.
Proof. intros * Hτ [L1 L2 H]; constructor; [ exact L1 | exact L2 |]; rewrite <- (tele_insts_sb_eq _ _ _ _ Hτ); exact H. Qed.

Lemma glu_args_length : forall Δ C τ ρ Ms vs, glu_args Δ C τ ρ Ms vs ->
    List.length Ms = List.length C /\ List.length vs = List.length C.
Proof. intros * [L1 L2 _]; split; assumption. Qed.

(** ** Glued Substitutions from Glued Arguments *)

Lemma glu_ctx_env_suffix : forall C Γ Sb, tele_ass C -> EG C ++ Γ ∈ glu_ctx_env ↘ Sb ->
    exists Sb', EG Γ ∈ glu_ctx_env ↘ Sb'.
Proof.
  induction C as [| e C IH]; intros * Hass H; [ eauto |].
  apply List.Forall_cons_iff in Hass as [[A ->] Hass].
  cbn [List.app] in H; inversion H; subst; eauto.
Qed.

Lemma glu_sub_of_list : forall C Γ0 Sb Sb0 Δ σ0 ρ0 Ms vs,
    tele_ass C -> EG C ++ Γ0 ∈ glu_ctx_env ↘ Sb -> EG Γ0 ∈ glu_ctx_env ↘ Sb0 ->
    Δ ⊢ˢ σ0 ® ρ0 ∈ Sb0 -> glu_args Δ C σ0 ρ0 Ms vs ->
    Δ ⊢ˢ sb_of_list σ0 Ms ® env_args ρ0 vs ∈ Sb.
Proof.
  induction C as [| e C IH] using List.rev_ind; intros * Hass HC H0 Hσ Hg.
  - destruct (glu_args_length _ _ _ _ _ _ Hg) as [L1 L2].
    destruct Ms; [| discriminate ]; destruct vs; [| discriminate ]; cbn.
    apply (functional_glu_ctx_env H0 HC); exact Hσ.
  - unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A ->] _].
    destruct (glu_args_length _ _ _ _ _ _ Hg) as [L1 L2]; rewrite List.length_app in L1, L2; cbn in L1, L2.
    destruct Ms as [| M0 Ms]; [ cbn in L1; lia |]; destruct vs as [| v0 vs]; [ cbn in L2; lia |].
    apply glu_args_snoc in Hg as [[i a P El Ha Hglu HP HM] Hg].
    rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
    destruct (glu_ctx_env_suffix _ _ _ Hass HC) as [Sb1 HC1].
    destruct (glu_ctx_env_cons_clean_inversion H0 HC1) as (i' & HA & HT & HSb1).
    destruct (HT _ _ _ Hσ) as [a' P' El' Ha' Hglu' HP'].
    assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (glu_univ_elem_cumu_ge_uidx (i := i) (j := ul (ulvl i)) (uidx_le_ulvl i) Hglu) as (P1 & El1 & Hglu1).
    assert (HM1 : Δ ⊢ M0 : A[σ0] ® v0 ∈ El1) by (eapply glu_univ_elem_exp_cumu_ge_uidx; [ apply uidx_le_ulvl | exact Hglu | exact Hglu1 | exact HM ]).
    assert (HM' : Δ ⊢ M0 : A[σ0] ® v0 ∈ El')
      by (eapply glu_univ_elem_exp_conv; [ eapply glu_univ_elem_per_univ; exact Hglu1 | exact Hglu1 | exact Hglu' | exact HM1 | exact HP' ]).
    assert (Hσ1 : Δ ⊢ˢ σ0,,M0 ® ρ0 ↦ v0 ∈ Sb1)
      by (apply HSb1; eapply cons_glu_sub_pred_helper; eassumption).
    cbn [sb_of_list env_args List.fold_left].
    exact (IH _ _ _ _ _ _ _ _ Hass HC HC1 Hσ1 Hg).
Qed.

(** ** Constants of [Π]-Types over Telescopes *)

Lemma exp_wk_q_sub_extend : forall C σ φ N, C[q σ][wk_q φ]ʷ[Id,,N] = C[(sb_wk σ φ),,N].
Proof.
  intros; rewrite exp_wk_sub, exp_sub_sub; apply exp_sub_sb_eq.
  intros [| x]; cbn; [ reflexivity |].
  change ((q σ) (S x)) with (sentry_wk (σ x) wk_shift).
  rewrite sentry_wk_wk, sentry_sub_wk, <- sentry_sub_of_wk; apply sentry_sub_sb_eq; intros y; reflexivity.
Qed.

Lemma wf_app_wk_q : forall Δ Δ' σ φ A C M N,
    Δ ⊢ M : Π A[σ] C[q σ] -> Δ' ⊢ᵏ φ : Δ -> Δ' ⊢ N : A[σ][φ]ʷ ->
    Δ' ⊢ M[φ]ʷ $ N : C[(sb_wk σ φ),,N].
Proof.
  intros * HM Hφ HN.
  assert (Hw : Δ' ⊢ M[φ]ʷ : (Π A[σ] C[q σ])[φ]ʷ) by mauto 3.
  cbn [exp_wk] in Hw.
  pose proof (wf_app' _ _ _ _ _ _ _ Hw HN) as H.
  rewrite exp_wk_q_sub_extend in H.
  exact H.
Qed.

(** A type of a glued context, glued at a glued substitution. *)
Lemma glu_rel_typ_at : forall Γ Sb A (i : nat) Δ σ ρ, EG Γ ∈ glu_ctx_env ↘ Sb -> Γ ⊩ A : Typeω@i ->
    Δ ⊢ˢ σ ® ρ ∈ Sb ->
    Δ ⊢ A[σ] : Typeω@i /\ exists a, ⟦ A ⟧ ρ ↘ a /\ Dom a ≈ a ∈ per_univ i /\
      forall P El, DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ A[σ] ® P.
Proof.
  intros * HΓ HA Hσ.
  destruct (glu_rel_exp_of_univ_inversion (u := ul i) HΓ HA _ _ _ Hσ) as (HAσ & a & Ha & Hper & HP & _).
  split; [ exact HAσ | exists a; split; [ exact Ha | split; [ exact Hper | exact HP ] ] ].
Qed.

(** A constant [X] of a [Π] over the telescope [Δt], whose values along its
    arguments are given by the relation [Fr], is glued at the [Π] when its
    applications to glued arguments are glued at the codomain.  The
    arguments so far are the values [xs] of the context [Γb] already
    consumed, a suffix of the full telescope [T]; [Fr] extends along an
    argument whose values so far are those of a glued substitution of a
    suffix of [T] ([Happ]): the value of a view's constructor at its last
    uniform parameter needs the uniform parameters related. *)
Lemma ctx_pi_glu_elem_by : forall (Fr : list domain -> domain -> Prop) X T,
    (forall φ, X[φ]ʷ = X) ->
    (forall Δ1 Γ' Sb' Δ' σ' xs x w, T = Δ1 ++ Γ' -> EG Γ' ∈ glu_ctx_env ↘ Sb' ->
       Δ' ⊢ˢ σ' ® env_args nil (xs ++ x :: nil) ∈ Sb' -> List.length Γ' = S (List.length xs) -> Fr xs w ->
       exists u, $| w & x | gc_deps ⍮ gc_stack ↘ u /\ Fr (xs ++ x :: nil) u) ->
    forall Δt Γb Sb_b Sb B (i : nat), tele_ass Δt -> EG Γb ∈ glu_ctx_env ↘ Sb_b -> EG Δt ++ Γb ∈ glu_ctx_env ↘ Sb ->
    (exists Δ0, T = Δ0 ++ Δt ++ Γb) ->
    (forall Δ1 A Δ2, Δt = Δ1 ++ ce_ass A :: Δ2 -> Δ2 ++ Γb ⊩ A : Typeω@i) ->
    (forall Δ1 Δ2, Δt = Δ1 ++ Δ2 -> Δ2 ++ Γb ⊢ ctx_pi Δ1 B : Typeω@i) ->
    forall Δ σ xs Xs w, Δ ⊢ˢ σ ® env_args nil xs ∈ Sb_b -> List.length Γb = List.length xs -> Fr xs w ->
      Δ ⊢ apps X Xs : (ctx_pi Δt B)[σ] ->
      (forall R a, ⟦ ctx_pi Δt B ⟧ env_args nil xs ↘ a -> DF a ≈ a ∈ per_univ_elem i ↘ R -> R w w) ->
      (forall Δ' φ Ms vs w', Δ' ⊢ᵏ φ : Δ -> glu_args Δ' Δt (sb_wk σ φ) (env_args nil xs) Ms vs -> Fr (xs ++ vs) w' ->
         forall b P El, ⟦ B ⟧ env_args nil (xs ++ vs) ↘ b -> DG b ∈ glu_univ_elem i ↘ P ↘ El ->
           (forall R, DF b ≈ b ∈ per_univ_elem i ↘ R -> R w' w') ->
           Δ' ⊢ apps X (List.map (fun N => N[φ]ʷ) Xs ++ Ms) : B[sb_of_list (sb_wk σ φ) Ms] ® w' ∈ El) ->
      forall a P El, ⟦ ctx_pi Δt B ⟧ env_args nil xs ↘ a -> DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ ⊢ apps X Xs : (ctx_pi Δt B)[σ] ® w ∈ El.
Proof.
  intros Fr X T HXw Happ Δt.
  induction Δt as [| e Δt IH] using List.rev_ind;
    intros * Hass HCb HC [Δ0 HT] HA HCs * Hσ Hlen Hw HXt HPER Hbase * Ha Hglu.
  - cbn [ctx_pi] in *.
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape HCb _ _ _ Hσ)).
    pose proof (Hbase Δ wk_id nil nil w (kripke_id _ HΔ) (glu_args_nil _ _ _) ltac:(rewrite List.app_nil_r; exact Hw)
                  _ _ _ ltac:(rewrite List.app_nil_r; exact Ha) Hglu) as H.
    cbn [sb_of_list] in H; rewrite <- exp_wk_sub, exp_wk_id, map_wk_id, !List.app_nil_r in H.
    apply H; intros R HR; exact (HPER _ _ Ha HR).
  - assert (Hass' := Hass); unfold tele_ass in Hass'; apply List.Forall_app in Hass' as [HassΔ He].
    apply List.Forall_cons_iff in He as [[A ->] _].
    rewrite ctx_pi_snoc in Ha, HXt, HPER.
    inversion Ha; subst.
    invert_glu_univ_elem Hglu.
    pose proof (HPER _ _ Ha H2) as Hfx.
    pose proof H2 as H2'.
    basic_invert_per_univ_elem H2'.
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape HCb _ _ _ Hσ)).
    assert (Hσt : Δ ⊢ˢ σ : Γb) by exact (glu_ctx_env_sub_escape HCb _ _ _ Hσ).
    pose proof (HCs (Δt ++ ⋅ ▹ A) nil (eq_sym (List.app_nil_r _))) as HCp; cbn [List.app] in HCp.
    assert (HPit : Δ ⊢ (ctx_pi (Δt ++ ⋅ ▹ A) B)[σ] : Typeω@i) by mauto 3.
    rewrite ctx_pi_snoc in HPit; cbn [exp_sub] in HPit.
    pose proof (HA Δt A nil eq_refl) as HAp; cbn [List.app] in HAp.
    destruct (glu_rel_typ_at _ _ _ _ _ _ _ HCb HAp Hσ) as (HAt & _).
    pose proof (HCs Δt (⋅ ▹ A) eq_refl) as HCqw; cbn [List.app] in HCqw.
    assert (HAw : Γb ⊢ A : Typeω@i) by (eapply glu_rel_exp_to_wf_exp; exact HAp).
    assert (HCqt : Δ ▹ A[σ] ⊢ (ctx_pi Δt B)[q σ] : Typeω@i) by mauto 3.
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ H0 equiv_a_a') as Hin.
    rewrite ctx_pi_snoc; apply H4; cbn [exp_sub] in HXt |- *.
    eapply mk_pi_glu_exp_pred with (IT := A[σ]) (OT := (ctx_pi Δt B)[q σ]);
      [ exact HXt | exact Hfx | apply wf_exp_eq_refl; exact HPit | exact HAt | exact HCqt | |].
    + intros Δ' φ Hφ.
      pose proof (glu_ctx_env_sub_monotone _ _ HCb _ _ _ _ _ Hσ Hφ) as Hσφ.
      destruct (glu_rel_typ_at _ _ _ _ _ _ _ HCb HAp Hσφ) as (_ & a1 & Ha1 & _ & HP1).
      assert (a1 = a0) as -> by (eapply functional_eval_exp; eassumption).
      rewrite exp_wk_sub; exact (HP1 _ _ H).
    + intros Δ' φ N n Hφ HN equiv_n.
      assert (Hn0 : in_rel0 n n) by (apply Hin; exact equiv_n).
      destruct (H7 _ _ Hn0) as [b b' Hb Hb' Hbb].
      destruct (proj1 (H8 _ _) Hfx n n Hn0) as [r r' Er Er' Hrr].
      rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
      destruct (glu_ctx_env_suffix _ _ _ HassΔ HC) as [Sb1 HC1].
      destruct (glu_ctx_env_cons_clean_inversion HCb HC1) as (i' & HAi' & HTi' & HSb1).
      pose proof (glu_ctx_env_sub_monotone _ _ HCb _ _ _ _ _ Hσ Hφ) as Hσφ.
      destruct (HTi' _ _ _ Hσφ) as [a1 P1 El1 Ha1 Hg1 HP1].
      assert (a1 = a0) as -> by (eapply functional_eval_exp; eassumption).
      assert (HN1 : Δ' ⊢ N : A[σ][φ]ʷ ® n ∈ El1)
        by (eapply glu_univ_elem_exp_conv;
            [ eapply glu_univ_elem_per_univ; exact H | exact H | exact Hg1 | exact HN | rewrite exp_wk_sub; exact HP1 ]).
      assert (Hσ1 : Δ' ⊢ˢ (sb_wk σ φ),,N ® env_args nil xs ↦ n ∈ Sb1)
        by (apply HSb1; eapply cons_glu_sub_pred_pi_helper; eassumption).
      assert (Hσ1' : Δ' ⊢ˢ (sb_wk σ φ),,N ® env_args nil (xs ++ n :: nil) ∈ Sb1) by (rewrite env_args_snoc; exact Hσ1).
      destruct (Happ (Δ0 ++ Δt) (Γb ▹ A) Sb1 Δ' _ xs n w ltac:(rewrite <- !List.app_assoc; reflexivity) HC1 Hσ1'
                  ltac:(cbn; lia) Hw) as (u & Eu & Hu).
      assert (r = u) as -> by (eapply functional_eval_app; eassumption).
      assert (r' = u) as -> by (eapply functional_eval_app; eassumption).
      exists u; split; [ exact Eu |].
      rewrite exp_sub_q_extend_wk.
      assert (HNt : Δ' ⊢ N : A[σ][φ]ʷ) by (eapply glu_univ_elem_trm_escape; eassumption).
      pose proof (wf_app_wk_q _ _ _ _ _ _ _ _ HXt Hφ HNt) as HXt'.
      replace ((apps X Xs)[φ]ʷ $ N) with (apps X (List.map (fun M => M[φ]ʷ) Xs ++ N :: nil)) in HXt' |- *
        by (rewrite apps_exp_snoc, apps_wk, HXw; reflexivity).
      assert (HA' : forall Δ1 A0 Δ2, Δt = Δ1 ++ ce_ass A0 :: Δ2 -> Δ2 ++ Γb ▹ A ⊩ A0 : Typeω@i).
      { intros Δ1 A0 Δ2 Heq.
        pose proof (HA Δ1 A0 (Δ2 ++ ⋅ ▹ A) ltac:(rewrite Heq, <- List.app_assoc; reflexivity)) as H'.
        rewrite <- List.app_assoc in H'; exact H'. }
      assert (HCs' : forall Δ1 Δ2, Δt = Δ1 ++ Δ2 -> Δ2 ++ Γb ▹ A ⊢ ctx_pi Δ1 B : Typeω@i).
      { intros Δ1 Δ2 Heq.
        pose proof (HCs Δ1 (Δ2 ++ ⋅ ▹ A) ltac:(rewrite Heq, <- List.app_assoc; reflexivity)) as H'.
        rewrite <- List.app_assoc in H'; exact H'. }
      assert (HPER' : forall R a', ⟦ ctx_pi Δt B ⟧ env_args nil (xs ++ n :: nil) ↘ a' -> DF a' ≈ a' ∈ per_univ_elem i ↘ R ->
                        R u u).
      { intros R a' Ha' HR.
        rewrite env_args_snoc in Ha'.
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hbb HR); exact Hrr. }
      assert (Hb1 : ⟦ ctx_pi Δt B ⟧ env_args nil (xs ++ n :: nil) ↘ b) by (rewrite env_args_snoc; exact Hb).
      refine (IH (Γb ▹ A) Sb1 Sb B i HassΔ HC1 HC ltac:(exists Δ0; rewrite <- !List.app_assoc; reflexivity) HA' HCs'
                Δ' _ (xs ++ n :: nil) _ u Hσ1' ltac:(cbn; rewrite List.length_app; cbn; lia) Hu HXt' HPER' _
                b _ _ Hb1 (H1 _ _ _ Hb)).
      * intros Δ'' φ' Ms vs w' Hφ' Hg Hw' b0 P0 El0 Hb0 Hg0 HPb0.
        pose proof (kripke_compose _ _ _ _ _ Hφ' Hφ) as Hφφ.
        assert (Hsb : sb_eq (sb_wk ((sb_wk σ φ),,N) φ') ((sb_wk σ (φ ⊙ φ')),,N[φ']ʷ))
          by (intros [| x]; cbn; [ reflexivity | apply sentry_wk_wk ]).
        assert (Hg' : glu_args Δ'' (Δt ++ ⋅ ▹ A) (sb_wk σ (φ ⊙ φ')) (env_args nil xs) (N[φ']ʷ :: Ms) (n :: vs)).
        { apply glu_args_snoc; split; [| rewrite <- env_args_snoc; eapply glu_args_sb_eq; [ exact Hsb | exact Hg ] ].
          pose proof (glu_ctx_env_sub_monotone _ _ HCb _ _ _ _ _ Hσ Hφφ) as Hσφφ.
          destruct (glu_rel_typ_at _ _ _ _ _ _ _ HCb HAp Hσφφ) as (_ & a2 & Ha2 & _ & HP2).
          assert (a2 = a0) as -> by (eapply functional_eval_exp; eassumption).
          apply (mk_glu_arg _ _ _ _ _ _ i a0 IP IEl H5 H (HP2 _ _ H)).
          rewrite <- exp_wk_sub, <- exp_wk_wk.
          eapply glu_univ_elem_exp_monotone; eassumption. }
        rewrite <- List.app_assoc in Hw', Hb0; cbn [List.app] in Hw', Hb0.
        pose proof (Hbase Δ'' (φ ⊙ φ') (N[φ']ʷ :: Ms) (n :: vs) w' Hφφ Hg' Hw' b0 P0 El0 Hb0 Hg0 HPb0) as Hr.
        cbn [sb_of_list] in Hr.
        rewrite <- (exp_sub_sb_eq _ _ _ (sb_of_list_cong Ms _ _ Hsb)) in Hr.
        rewrite List.map_app, map_wk_wk, <- List.app_assoc; cbn [List.map List.app].
        exact Hr.
Qed.

(** ** Closed Constants *)

Lemma typ_nil_rel' : forall T (i : nat) ρ ρ',
    ⋅ ⊢ T : Typeω@i ->
    exists a a', ⟦ T ⟧ ρ ↘ a /\ ⟦ T ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * HT%completeness_fundamental_exp.
  destruct (rel_exp_of_typ_inversion_simple HT) as [env_rel [Hnil H]].
  apply H.
  inversion Hnil as [? Heq | | | |]; subst.
  apply Heq; exact I.
Qed.

(** A closed constant glued at the value of its closed type at the empty
    environment is glued at the empty context. *)
Lemma glu_closed_const : forall X T (i : nat) m0,
    (forall σ, X[σ] = X) -> (forall σ, T[σ] = T) -> ⋅ ⊢ T : Typeω@i ->
    (forall ρ, ⟦ X ⟧ ρ ↘ m0) ->
    (forall Δ σ, Δ ⊢ˢ σ : ⋅ -> forall a P El, ⟦ T ⟧ nil ↘ a -> DG a ∈ glu_univ_elem i ↘ P ↘ El ->
       Δ ⊢ X : T ® m0 ∈ El) ->
    ⋅ ⊩ X : T.
Proof.
  intros * HXs HTs HT HXe H.
  assert (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) by (eapply ctx_wf_gctx; eapply presup_exp_ctx; exact HT).
  eapply mk_glu_rel_exp with (gre_lvl := i); [ econstructor; [ reflexivity | exact Hg ] |].
  intros Δ σ ρ Hσ; cbn in Hσ.
  destruct (typ_nil_rel' _ _ ρ nil HT) as (a & a0 & Ha & Ha0 & Haa).
  assert (Ha00 : Dom a0 ≈ a0 ∈ per_univ i) by (etransitivity; [ symmetry; exact Haa | exact Haa ]).
  destruct (per_univ_glu_univ_elem _ _ Ha00) as (P & El & Hglu).
  assert (Hglu' : DG a ∈ glu_univ_elem i ↘ P ↘ El) by (eapply glu_univ_elem_resp_per_univ; [ symmetry; exact Haa | exact Hglu ]).
  econstructor; [ exact Ha | apply HXe | exact Hglu' |].
  rewrite HXs, HTs; exact (H _ _ Hσ _ _ _ Ha0 Hglu).
Qed.

(** A closed constant whose value depends on the environment only through
    a relation: glued at the empty context when every value it takes is
    glued at the value of its type at the empty environment. *)
Lemma glu_closed_const_by : forall X T (i : nat) (V : domain -> Prop),
    (forall σ, X[σ] = X) -> (forall σ, T[σ] = T) -> ⋅ ⊢ T : Typeω@i ->
    (forall ρ, exists m0, ⟦ X ⟧ ρ ↘ m0 /\ V m0) ->
    (forall Δ σ m0, Δ ⊢ˢ σ : ⋅ -> V m0 -> forall a P El, ⟦ T ⟧ nil ↘ a -> DG a ∈ glu_univ_elem i ↘ P ↘ El ->
       Δ ⊢ X : T ® m0 ∈ El) ->
    ⋅ ⊩ X : T.
Proof.
  intros * HXs HTs HT HXe H.
  assert (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) by (eapply ctx_wf_gctx; eapply presup_exp_ctx; exact HT).
  eapply mk_glu_rel_exp with (gre_lvl := i); [ econstructor; [ reflexivity | exact Hg ] |].
  intros Δ σ ρ Hσ; cbn in Hσ.
  destruct (typ_nil_rel' _ _ ρ nil HT) as (a & a0 & Ha & Ha0 & Haa).
  assert (Ha00 : Dom a0 ≈ a0 ∈ per_univ i) by (etransitivity; [ symmetry; exact Haa | exact Haa ]).
  destruct (per_univ_glu_univ_elem _ _ Ha00) as (P & El & Hglu).
  assert (Hglu' : DG a ∈ glu_univ_elem i ↘ P ↘ El) by (eapply glu_univ_elem_resp_per_univ; [ symmetry; exact Haa | exact Hglu ]).
  destruct (HXe ρ) as (m0 & Hm0 & HV).
  econstructor; [ exact Ha | exact Hm0 | exact Hglu' |].
  rewrite HXs, HTs; exact (H _ _ _ Hσ HV _ _ _ Ha0 Hglu).
Qed.

(** ** The Entries of a Glued Telescope *)

Lemma glu_rel_exp_lift_nat : forall Γ A (i j : nat), i <= j -> Γ ⊩ A : Typeω@i -> Γ ⊩ A : Typeω@j.
Proof. intros * Hle HA; exact (glu_rel_exp_lift_uidx (u := ul i) (v := ul j) Hle HA). Qed.

Lemma glu_ctx_env_head_valid : forall Γ A Sb, EG Γ ▹ A ∈ glu_ctx_env ↘ Sb -> exists i, Γ ⊩ A : Typeω@i.
Proof.
  intros * H; inversion H as [| ? ? i TSb ? HΓ HA HT HSb | | |]; subst.
  exists i; eapply glu_rel_exp_of_typ; [ exact HΓ |].
  intros Δ σ ρ Hσ; destruct (HT _ _ _ Hσ) as [a P El Ha Hglu HP].
  split; [ mauto 3 |].
  exists a; split; [ exact Ha | split; [ eapply glu_univ_elem_per_univ; exact Hglu |] ].
  intros P' El' Hglu'; handle_functional_glu_univ_elem; exact HP.
Qed.

Lemma glu_ctx_env_entries_valid : forall C Γb Sb, tele_ass C -> EG C ++ Γb ∈ glu_ctx_env ↘ Sb ->
    forall (i0 : nat), exists (i : nat), i0 <= i /\
      forall Δ1 A Δ2, C = Δ1 ++ ce_ass A :: Δ2 -> Δ2 ++ Γb ⊩ A : Typeω@i.
Proof.
  induction C as [| e C IH]; intros * Hass H i0.
  - exists i0; split; [ lia |]; intros [] *; discriminate.
  - apply List.Forall_cons_iff in Hass as [[A ->] Hass].
    cbn [List.app] in H; pose proof H as H'; inversion H' as [| ? ? ? ? ? HC _ _ _ | | |]; subst.
    destruct (glu_ctx_env_head_valid _ _ _ H) as [k Hk].
    destruct (IH _ _ Hass HC (Nat.max i0 k)) as (i1 & Hle & Hi).
    exists i1; split; [ lia |].
    intros [| e' Δ1] A' Δ2 Heq; cbn [List.app] in Heq; injection Heq; intros; subst;
      [ eapply glu_rel_exp_lift_nat; [| exact Hk ]; lia | eauto ].
Qed.

(** ** Glued Arguments of Closed Telescopes *)

Lemma uidx_le_max : forall u j, uidx_le u (ul (Nat.max (ulvl u) j)).
Proof. intros [] j; cbn; [ exact I | lia ]. Qed.

Lemma wf_sub_nil' : forall Δ σ, ⊢ Δ -> Δ ⊢ˢ σ : ⋅.
Proof.
  intros * HΔ; constructor; [ exact HΔ | apply wf_ctx_empty; eapply ctx_wf_gctx; exact HΔ | | |];
    intros * Hx; inversion Hx.
Qed.

Lemma tele_insts_closed_base : forall C σ σ' Ms, tele_ass C -> ctx_scoped 0 C ->
    tele_insts C σ Ms = tele_insts C σ' Ms.
Proof.
  intros * Hass Hs.
  pose proof (tele_insts_sub C 0 σ σ' Id Ms Hass Hs ltac:(intros; lia)) as H.
  rewrite (List.map_ext _ (fun T => T) exp_sub_id), List.map_id in H.
  rewrite (List.map_ext _ (fun T => T) exp_sub_id), List.map_id in H.
  exact H.
Qed.

Lemma glu_args_closed_base : forall Δ C τ τ' ρ Ms vs, tele_ass C -> ctx_scoped 0 C ->
    glu_args Δ C τ ρ Ms vs -> glu_args Δ C τ' ρ Ms vs.
Proof.
  intros * Hass Hs [L1 L2 H]; constructor; [ exact L1 | exact L2 |].
  rewrite <- (tele_insts_closed_base _ τ τ'); assumption.
Qed.

Lemma glu_args_wk : forall Δ Δ' φ C ρ Ms vs, tele_ass C -> ctx_scoped 0 C -> Δ' ⊢ᵏ φ : Δ ->
    glu_args Δ C Id ρ Ms vs -> glu_args Δ' C Id ρ (List.map (fun M => M[φ]ʷ) Ms) vs.
Proof.
  intros * Hass Hs Hφ [L1 L2 H]; constructor; [ rewrite List.length_map; exact L1 | exact L2 |].
  intros k M T v A HM HT Hv HA.
  rewrite List.nth_error_map in HM.
  destruct (List.nth_error Ms k) as [M0 |] eqn:HM0; [| discriminate ]; injection HM as <-.
  rewrite <- (tele_insts_closed_wk _ _ _ Hass Hs), List.nth_error_map in HT.
  destruct (List.nth_error (tele_insts C Id Ms) k) as [T0 |] eqn:HT0; [| discriminate ]; injection HT as <-.
  destruct (H _ _ _ _ _ HM0 HT0 Hv HA) as [i a P El Ha Hglu HP HMg].
  apply (mk_glu_arg _ _ _ _ _ _ i a P El Ha Hglu).
  - eapply glu_univ_elem_typ_monotone; eassumption.
  - eapply glu_univ_elem_exp_monotone; eassumption.
Qed.

Lemma glu_args_resp_eq : forall Δ C ρ Ms Ms' vs, tele_ass C -> ⊢ C -> ⊢ Δ ->
    exps_eq_at Δ C Ms Ms' -> glu_args Δ C Id ρ Ms vs -> glu_args Δ C Id ρ Ms' vs.
Proof.
  intros * Hass HC HΔ [Hl HMM] [L1 L2 H].
  constructor; [ congruence | exact L2 |].
  intros k M' T' v A HM' HT' Hv HA.
  assert (Hk : k < List.length C) by (rewrite <- L1, Hl; apply List.nth_error_Some; congruence).
  destruct (nth_error_lt_some Ms k ltac:(lia)) as [M HM].
  destruct (nth_error_lt_some (tele_insts C Id Ms) k) as [T HT]; [ rewrite length_tele_insts by exact Hass; lia |].
  destruct (H _ _ _ _ _ HM HT Hv HA) as [i a P El Ha Hglu HP HMg].
  assert (HCe : ⊢ C ++ ⋅) by (rewrite List.app_nil_r; exact HC).
  assert (HId : Δ ⊢ˢ Id ≈ Id : ⋅) by (apply wf_sub_eq_refl, wf_sub_nil'; exact HΔ).
  destruct (tele_insts_cong C Δ ⋅ Id Id Ms Ms' Hass HCe HId L1 ltac:(lia) HMM k T T' HT HT') as [j HTT].
  pose proof (uidx_le_max i j) as Hij.
  destruct (glu_univ_elem_cumu_ge_uidx (i := i) (j := ul (Nat.max (ulvl i) j)) Hij Hglu) as (P' & El' & Hglu').
  assert (HP' : Δ ⊢ T ® P') by (eapply glu_univ_elem_typ_cumu_ge_uidx; [ exact Hij | exact Hglu | exact Hglu' | exact HP ]).
  assert (HTT' : Δ ⊢ T ≈ T' : Typeω@(Nat.max (ulvl i) j)) by (eapply lift_exp_eq_ge; [| exact HTT ]; lia).
  apply (mk_glu_arg _ _ _ _ _ _ (ul (Nat.max (ulvl i) j)) a P' El' Ha Hglu');
    [ eapply glu_univ_elem_typ_resp_exp_eq; eassumption |].
  eapply glu_univ_elem_trm_resp_typ_exp_eq; [ exact Hglu' | | exact HTT' ].
  eapply glu_univ_elem_trm_resp_exp_eq;
    [ exact Hglu' | eapply glu_univ_elem_exp_cumu_ge_uidx; [ exact Hij | exact Hglu | exact Hglu' | exact HMg ] | exact (HMM _ _ _ _ HM HM' HT) ].
Qed.

Lemma firstn_app_ge : forall {X} (l1 l2 : list X) k, List.length l1 <= k ->
    List.firstn k (l1 ++ l2) = l1 ++ List.firstn (k - List.length l1) l2.
Proof. intros; rewrite List.firstn_app, List.firstn_all2 by lia; reflexivity. Qed.

Lemma firstn_app_le : forall {X} (l1 l2 : list X) k, k <= List.length l1 ->
    List.firstn k (l1 ++ l2) = List.firstn k l1.
Proof. intros; rewrite List.firstn_app; replace (k - List.length l1) with 0 by lia; cbn; apply List.app_nil_r. Qed.

Lemma glu_args_app : forall Δ C1 C2 τ ρ Ms1 Ms2 vs1 vs2, tele_ass C1 ->
    List.length Ms1 = List.length C1 -> List.length vs1 = List.length C1 ->
    glu_args Δ (C2 ++ C1) τ ρ (Ms1 ++ Ms2) (vs1 ++ vs2) <->
    glu_args Δ C1 τ ρ Ms1 vs1 /\ glu_args Δ C2 (sb_of_list τ Ms1) (env_args ρ vs1) Ms2 vs2.
Proof.
  intros * Hass HM1 Hv1.
  assert (Ht1 : List.length (tele_insts C1 τ Ms1) = List.length C1) by (rewrite length_tele_insts by exact Hass; lia).
  assert (Hr1 : List.length (List.rev C1) = List.length C1) by apply List.length_rev.
  split.
  - intros [L1 L2 H]; rewrite !List.length_app in L1, L2.
    rewrite tele_insts_app, List.rev_app_distr in H by assumption.
    split; constructor; [ lia | lia | | lia | lia |].
    + intros k M T v A HM HT Hv HA.
      assert (Hk : k < List.length C1) by (rewrite <- HM1; apply List.nth_error_Some; congruence).
      pose proof (H k M T v A) as H'.
      rewrite (firstn_app_le vs1) in H' by lia.
      apply H'; rewrite List.nth_error_app1 by lia; assumption.
    + intros k M T v A HM HT Hv HA.
      pose proof (H (List.length C1 + k) M T v A) as H'.
      rewrite firstn_app_ge, env_args_app in H' by lia.
      replace (List.length C1 + k - List.length vs1) with k in H' by lia.
      apply H'; rewrite List.nth_error_app2 by lia.
      * replace (List.length C1 + k - List.length Ms1) with k by lia; exact HM.
      * replace (List.length C1 + k - List.length (tele_insts C1 τ Ms1)) with k by lia; exact HT.
      * replace (List.length C1 + k - List.length vs1) with k by lia; exact Hv.
      * replace (List.length C1 + k - List.length (List.rev C1)) with k by lia; exact HA.
  - intros [[L1 L2 H1] [L3 L4 H2]]; constructor; [ rewrite !List.length_app; lia | rewrite !List.length_app; lia |].
    rewrite tele_insts_app, List.rev_app_distr by assumption.
    intros k M T v A HM HT Hv HA.
    destruct (Nat.lt_ge_cases k (List.length C1)) as [Hk | Hk].
    + rewrite List.nth_error_app1 in HM, HT, Hv, HA by lia.
      rewrite (firstn_app_le vs1) by lia.
      exact (H1 _ _ _ _ _ HM HT Hv HA).
    + rewrite List.nth_error_app2 in HM, HT, Hv, HA by lia.
      rewrite firstn_app_ge, env_args_app by lia.
      rewrite HM1, Ht1, Hv1, Hr1 in *.
      exact (H2 _ _ _ _ _ HM HT Hv HA).
Qed.

Lemma read_ps_nth : forall s ρ T vs Rs, Rps vs at T in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Rs ->
    List.length (List.map nf_to_exp Rs) = List.length vs /\
    forall k v A, List.nth_error vs k = Some v -> List.nth_error T k = Some (ce_ass A) ->
      exists a (V : nf), ⟦ A ⟧ env_args ρ (List.firstn k vs) ↘ a /\ Rnf ⇓ a v in gc_deps ⍮ gc_stack ⍮ s ↘ V /\
        List.nth_error (List.map nf_to_exp Rs) k = Some (V : exp).
Proof.
  induction 1; [ split; [ reflexivity | intros [] *; discriminate ] |].
  match goal with H : _ /\ _ |- _ => destruct H as [IHl IHn] end.
  split; [ cbn; congruence |].
  intros [| k] v0 A0 Hv HA; cbn in Hv, HA.
  - injection Hv as <-; injection HA as <-; do 2 eexists; split; [ eassumption | split; [ eassumption | reflexivity ] ].
  - destruct (IHn _ _ _ Hv HA) as (a0 & V0 & Ha0 & HV0 & HN0); exists a0, V0; repeat split; assumption.
Qed.

Lemma glu_args_ass_nth : forall C k, tele_ass C -> k < List.length C -> exists A, List.nth_error (List.rev C) k = Some (ce_ass A).
Proof.
  intros * Hass Hk.
  destruct (nth_error_lt_some (List.rev C) k ltac:(rewrite List.length_rev; exact Hk)) as [e He].
  assert (He' := He); apply List.nth_error_In in He'; apply List.in_rev in He'.
  destruct (proj1 (List.Forall_forall _ _) Hass _ He') as [A ->]; eauto.
Qed.

(** Arguments glued along a member's telescope are glued to their values
    by their readback. *)
Lemma glu_args_params_top : forall Dh Mh Δ Ms vs, tele_ass (im_params Dh Mh) -> ctx_scoped 0 (im_params Dh Mh) ->
    glu_args Δ (im_params Dh Mh) Id nil Ms vs -> glu_params_top Dh Mh Δ Ms vs.
Proof.
  intros * Hass Hs Hg; pose proof Hg as [L1 L2 H].
  constructor; [ rewrite L1; apply length_im_params | |].
  - intros k M T HM HT.
    assert (Hk : k < List.length (im_params Dh Mh)) by (rewrite <- L1; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some vs k ltac:(lia)) as [v Hv].
    destruct (glu_args_ass_nth _ _ Hass Hk) as [A He].
    destruct (H _ _ _ _ _ HM HT Hv He) as [i a P El _ Hglu _ HMg].
    eapply glu_univ_elem_trm_escape; eassumption.
  - intros Δ' φ Rs Hφ HRs.
    destruct (read_ps_nth _ _ _ _ _ HRs) as [HRl HRn].
    split; [ rewrite List.length_map, HRl; congruence |].
    intros k X Y T HX HY HT.
    rewrite List.nth_error_map in HX.
    destruct (List.nth_error Ms k) as [M |] eqn:HM; [| discriminate ]; injection HX as <-.
    rewrite <- (tele_insts_closed_wk _ _ _ Hass Hs), List.nth_error_map in HT.
    destruct (List.nth_error (tele_insts (im_params Dh Mh) Id Ms) k) as [T0 |] eqn:HT0; [| discriminate ]; injection HT as <-.
    assert (Hk : k < List.length (im_params Dh Mh)) by (rewrite <- L1; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some vs k ltac:(lia)) as [v Hv].
    destruct (glu_args_ass_nth _ _ Hass Hk) as [A He].
    destruct (HRn _ _ _ Hv He) as (a' & V & Ha' & HV & HY').
    rewrite HY' in HY; injection HY as <-.
    destruct (H _ _ _ _ _ HM HT0 Hv He) as [i a P El Ha Hglu HP HMg].
    assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (realize_glu_elem_top _ _ _ _ Hglu _ _ _ _ HMg) as [? ? _ _ _ _ Hrb].
    exact (Hrb _ _ _ Hφ HV).
Qed.

(** ** The Non-Recursive Arguments, Syntactically *)

(** The terms among [As] at the non-recursive positions of [gs]. *)
Fixpoint nonrec_exps (gs : list carg) (As : list exp) : list exp :=
  match gs, As with
  | ca_arg _ :: gs, A :: As => A :: nonrec_exps gs As
  | ca_rec _ :: gs, _ :: As => nonrec_exps gs As
  | _, _ => nil
  end.

Lemma nonrec_exps_app : forall gs gs' As As', List.length As = List.length gs ->
    nonrec_exps (gs ++ gs') (As ++ As') = nonrec_exps gs As ++ nonrec_exps gs' As'.
Proof.
  induction gs as [| [] gs IH]; intros gs' [| A As] As' Hl; cbn in *; try discriminate; try reflexivity;
    rewrite IH by lia; reflexivity.
Qed.

Lemma length_nonrec_exps : forall gs As, List.length As = List.length gs ->
    List.length (nonrec_exps gs As) = List.length (cargs_nonrec gs).
Proof.
  induction gs as [| [] gs IH]; intros [| A As] Hl; cbn in *; try discriminate; try reflexivity;
    rewrite ?IH by lia; reflexivity.
Qed.

Lemma nonrec_exps_firstn : forall gs gs1 g gs2 As, gs = gs1 ++ g :: gs2 -> List.length As = List.length gs ->
    List.firstn (List.length (cargs_nonrec gs1)) (nonrec_exps gs As) = nonrec_exps gs1 (List.firstn (List.length gs1) As).
Proof.
  intros * Heq Hl.
  rewrite <- (List.firstn_skipn (List.length gs1) As) at 1.
  rewrite Heq at 1.
  rewrite nonrec_exps_app by (rewrite List.length_firstn; subst; rewrite List.length_app in Hl; cbn in Hl; lia).
  rewrite firstn_app_exact by (apply length_nonrec_exps; rewrite List.length_firstn; subst; rewrite List.length_app in Hl; cbn in Hl; lia).
  reflexivity.
Qed.

Lemma nonrec_exps_nth_arg : forall gs gs1 A gs2 As N, gs = gs1 ++ ca_arg A :: gs2 -> List.length As = List.length gs ->
    List.nth_error As (List.length gs1) = Some N ->
    List.nth_error (nonrec_exps gs As) (List.length (cargs_nonrec gs1)) = Some N.
Proof.
  intros * Heq Hl Hv; subst gs.
  rewrite <- (List.firstn_skipn (List.length gs1) As) in Hv |- *.
  assert (Hl1 : List.length (List.firstn (List.length gs1) As) = List.length gs1)
    by (rewrite List.length_firstn; rewrite List.length_app in Hl; cbn in Hl; lia).
  rewrite nonrec_exps_app by exact Hl1.
  rewrite List.nth_error_app2 in Hv by lia; rewrite Hl1 in Hv.
  replace (List.length gs1 - List.length gs1) with 0 in Hv by lia.
  rewrite List.nth_error_app2 by (rewrite length_nonrec_exps by exact Hl1; lia).
  rewrite length_nonrec_exps by exact Hl1.
  replace (List.length (cargs_nonrec gs1) - List.length (cargs_nonrec gs1)) with 0 by lia.
  destruct (List.skipn (List.length gs1) As) as [| v0 ws]; cbn in Hv |- *; [ discriminate | exact Hv ].
Qed.

(** [wk_pat] picks the non-recursive arguments out of an instance of all of
    them. *)
Lemma wk_pat_sb_of_list : forall gs1 σ As, List.length As = List.length gs1 ->
    sb_eq ((ι (wk_pat (cargs_pat gs1))) ⨟ sb_of_list σ As) (sb_of_list σ (nonrec_exps gs1 As)).
Proof.
  induction gs1 as [| g gs1 IH] using List.rev_ind; intros σ As Hl.
  - destruct As; [| discriminate ]; intros x; reflexivity.
  - rewrite List.length_app in Hl; cbn in Hl.
    destruct As as [| A As] using List.rev_ind; [ cbn in Hl; lia |]; clear IHAs.
    rewrite List.length_app in Hl; cbn in Hl.
    rewrite cargs_pat_snoc, nonrec_exps_app by lia.
    rewrite !sb_of_list_app.
    destruct g as [B | Ps]; cbn [wk_pat nonrec_exps sb_of_list].
    + intros [| x]; [ reflexivity |].
      cbn [sb_compose sb_of_wk sentry_sub wk_q sb_extend]; specialize (IH σ As ltac:(lia) x).
      cbn [sb_compose sb_of_wk sentry_sub] in IH; exact IH.
    + intros x; specialize (IH σ As ltac:(lia) x).
      cbn [sb_compose sb_of_wk sentry_sub wk_compose] in IH |- *; exact IH.
Qed.

Corollary exp_wk_pat_sb_of_list : forall B gs1 σ As, List.length As = List.length gs1 ->
    B[wk_pat (cargs_pat gs1)]ʷ[sb_of_list σ As] = B[sb_of_list σ (nonrec_exps gs1 As)].
Proof.
  intros; rewrite <- exp_sub_of_wk, exp_sub_sub; apply exp_sub_sb_eq, wk_pat_sb_of_list; assumption.
Qed.

(** The type of a non-recursive argument. *)
Lemma cargs_arg_type : forall p D Mk gs gs1 A gs2 σ As T, gs = gs1 ++ ca_arg A :: gs2 ->
    List.nth_error (tele_insts (cargs_ctx p D Mk gs) σ As) (List.length gs1) = Some T ->
    T = A[wk_pat (cargs_pat gs1)]ʷ[sb_of_list σ (List.firstn (List.length gs1) As)].
Proof.
  intros * -> HT.
  destruct (tele_insts_nth _ _ _ _ _ HT) as (A0 & HA & ->).
  unfold cargs_ctx in HA; rewrite cargs_ctx_aux_app in HA; cbn [cargs_ctx_aux] in HA.
  rewrite !List.rev_app_distr in HA; cbn [List.rev List.app] in HA.
  rewrite List.nth_error_app2 in HA by (rewrite List.length_rev, length_cargs_ctx_aux; lia).
  rewrite List.length_rev, length_cargs_ctx_aux, Nat.sub_diag in HA; cbn in HA.
  injection HA as <-; rewrite List.app_nil_r; reflexivity.
Qed.

(** A term glued at a type of a value is glued at that type of a value
    related to it, at a larger universe. *)
Lemma glu_transfer_per : forall (j i : nat) a b P El Γ T M m, DG a ∈ glu_univ_elem j ↘ P ↘ El -> Dom a ≈ b ∈ per_univ i ->
    Γ ⊢ T ® P -> Γ ⊢ M : T ® m ∈ El ->
    exists (k : uidx) P' El', DG b ∈ glu_univ_elem k ↘ P' ↘ El' /\ Γ ⊢ T ® P' /\ Γ ⊢ M : T ® m ∈ El'.
Proof.
  intros * Hg [R HR] HT HM.
  destruct (glu_univ_elem_cumu_ge (i := j) (j := Nat.max j i) (Nat.le_max_l _ _) Hg) as (P1 & El1 & Hg1).
  pose proof (per_univ_elem_cumu_ge i (Nat.max j i) _ _ _ (Nat.le_max_r _ _) HR) as HR1.
  pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro _ R HR1) Hg1) as Hg2.
  exists (Nat.max j i), P1, El1; split; [ exact Hg2 | split ].
  - eapply glu_univ_elem_typ_cumu_ge; [ apply Nat.le_max_l | exact Hg | exact Hg1 | exact HT ].
  - eapply glu_univ_elem_exp_cumu_ge; [ apply Nat.le_max_l | exact Hg | exact Hg1 | exact HM ].
Qed.

(** The type of a recursive argument: the shape's type at the uniform
    parameters of the parameters, under the parameters and the
    non-recursive arguments before it. *)
Lemma cargs_rec_type_sh : forall p D Mk gs gs1 t gs2 Ps As T, gs = gs1 ++ ca_rec t :: gs2 ->
    decl_closed D -> List.length Ps = im_np D Mk ->
    List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id Ps) As) (List.length gs1) = Some T ->
    T = ptyp_ty_at p D (List.firstn (ind_nu D) Ps) (sb_of_list Id (Ps ++ nonrec_exps gs1 (List.firstn (List.length gs1) As))) t.
Proof.
  intros * Heq Hc HPl HT.
  assert (HAl : List.length gs1 < List.length As).
  { destruct (Nat.lt_ge_cases (List.length gs1) (List.length As)) as [| Hge]; [ assumption |].
    rewrite (proj2 (List.nth_error_None _ _)) in HT; [ discriminate |].
    rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; subst gs; rewrite List.length_app; cbn; lia. }
  rewrite (cargs_rec_type_at _ _ _ _ _ _ _ _ _ _ Heq Hc HPl HT).
  apply ptyp_ty_at_sb_eq.
  rewrite !sb_of_list_app; apply wk_pat_sb_of_list; rewrite List.length_firstn; lia.
Qed.

(** The types of the non-uniform parameters of a recursive argument ending
    in the member [Mj], at an instance [Us ++ Ys] of the context it is
    declared in. *)
Lemma rec_tele_inst : forall D j Mj Pr L τ Us Ys m T, decl_closed D -> ind_member D j = Some Mj ->
    List.length Us = ind_nu D -> List.length Ys = L ->
    List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn L)) Pr) m = Some T ->
    List.nth_error (tele_insts (im_nparams Mj) (sb_of_list Id Us) (List.map (fun P => P[sb_of_list τ (Us ++ Ys)]) Pr)) m
      = Some T[sb_of_list τ (Us ++ Ys)].
Proof.
  intros * Hc HMj HUl HYl HT.
  rewrite <- (tele_insts_sub _ (ind_nu D) (sb_of_wk (wk_shiftn L)));
    [ rewrite List.nth_error_map, HT; reflexivity
    | eapply decl_closed_nparams_ass; eassumption | eapply decl_closed_nparams_scoped; eassumption |].
  intros x Hx; cbn [sb_of_wk sentry_sub wk_shiftn].
  rewrite (sb_of_list_app Us Ys).
  replace (x + L) with (List.length Ys + x) by lia.
  rewrite sb_of_list_ge, (sb_of_list_nth Us τ x (a_var 0)), (sb_of_list_nth Us Id x (a_var 0)) by lia; reflexivity.
Qed.

Lemma eval_exps_firstn : forall Ms ρ ms k, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms ->
    ⟦ List.firstn k Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ List.firstn k ms.
Proof.
  induction Ms as [| M Ms IH]; intros * H; inversion H; subst; destruct k; cbn;
    solve [ constructor | econstructor; [ eassumption | apply IH; assumption ] ].
Qed.

(** A weakened list instance is the list of the weakened terms, over the
    weakened base. *)
Lemma sb_wk_sb_of_list : forall Xs τ φ,
    sb_eq (sb_wk (sb_of_list τ Xs) φ) (sb_of_list (sb_wk τ φ) (List.map (fun X => X[φ]ʷ) Xs)).
Proof.
  induction Xs as [| X Xs IH]; intros τ φ; cbn [sb_of_list List.map]; [ reflexivity |].
  intros x; rewrite (IH (τ,,X) φ x); apply sb_of_list_cong, sb_wk_extend.
Qed.

(** The substitution of the codomain of a shape's [Π], instantiated at an
    argument [b] after a weakening: the list instance extended by [b]. *)
Lemma sb_q_shape_step : forall τ Xs φ b,
    sb_eq ((q (sb_of_list τ Xs)) ⨟ ((ι φ),,b)) (sb_of_list (sb_wk τ φ) (List.map (fun X => X[φ]ʷ) Xs ++ b :: nil)).
Proof.
  intros; rewrite sb_of_list_app; cbn [sb_of_list].
  intros [| x]; [ reflexivity |].
  unfold sb_q, sb_extend, sb_wk; cbn.
  rewrite sentry_sub_wk, (sentry_sub_sb_eq _ _ (ι φ)) by (intros y; reflexivity).
  rewrite sentry_sub_of_wk; exact (sb_wk_sb_of_list Xs τ φ x).
Qed.

(** The type of a shape's rest after a [Π], instantiated at an argument
    [b] after a weakening. *)
Lemma ptyp_ty_at_shape_step : forall p D t τ Us Ys φ b, decl_closed D -> List.length Us = ind_nu D ->
    (ptyp_ty_at p D (List.map (fun U => U[↑]ʷ) Us) (q (sb_of_list τ (Us ++ Ys))) t)[(ι φ),,b]
    = ptyp_ty_at p D (List.map (fun U => U[φ]ʷ) Us)
        (sb_of_list (sb_wk τ φ) (List.map (fun U => U[φ]ʷ) Us ++ (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil))) t.
Proof.
  intros * Hc HUl; rewrite ptyp_ty_at_sub by (try exact Hc; rewrite List.length_map; exact HUl).
  rewrite List.map_map.
  rewrite (List.map_ext _ (fun U => U[φ]ʷ) (fun U => exp_shift_extend_wk U φ b)).
  apply ptyp_ty_at_sb_eq.
  rewrite List.app_assoc, <- List.map_app; apply sb_q_shape_step.
Qed.

(** A glued instance of a context extended by a term glued at the new
    entry's type. *)
Lemma glu_sub_snoc : forall Γ B Sb Sb' Δ σ ρ b c',
    EG Γ ∈ glu_ctx_env ↘ Sb -> EG ce_ass B :: Γ ∈ glu_ctx_env ↘ Sb' -> Δ ⊢ˢ σ ® ρ ∈ Sb ->
    glu_arg Δ ρ B B[σ] b c' ->
    Δ ⊢ˢ σ,,b ® ρ ↦ c' ∈ Sb'.
Proof.
  intros * HSb HSb' Hσ Hb.
  apply (glu_sub_of_list (⋅ ▹ B) Γ Sb' Sb Δ σ ρ (b :: nil) (c' :: nil)); [ repeat constructor; eauto | exact HSb' | exact HSb | exact Hσ |].
  apply (glu_args_snoc Δ nil B σ ρ b nil c' nil); split; [ exact Hb | apply glu_args_nil ].
Qed.

(** An element glued at a type of a value is glued at another type of it,
    at another gluing of it. *)
Lemma glu_elem_retype : forall (i j : uidx) a P El P' El' Γ A A' M m,
    DG a ∈ glu_univ_elem i ↘ P ↘ El -> DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ A ® P -> Γ ⊢ M : A ® m ∈ El -> Γ ⊢ A' ® P' -> Γ ⊢ M : A' ® m ∈ El'.
Proof.
  intros * Hi Hj HA HM HA'.
  set (n := Nat.max (ulvl i) (ulvl j)).
  assert (Hin : uidx_le i (ul n)) by (apply uidx_le_ul_max; unfold n; lia).
  assert (Hjn : uidx_le j (ul n)) by (apply uidx_le_ul_max; unfold n; lia).
  destruct (glu_univ_elem_cumu_ge_uidx Hin Hi) as (Pn & Eln & Hn).
  pose proof (glu_univ_elem_typ_cumu_ge_uidx Hin Hi Hn HA) as HAn.
  pose proof (glu_univ_elem_exp_cumu_ge_uidx Hin Hi Hn HM) as HMn.
  pose proof (glu_univ_elem_typ_cumu_ge_uidx Hjn Hj Hn HA') as HA'n.
  pose proof (glu_univ_elem_typ_unique_upto_exp_eq' Hn HAn HA'n) as HE.
  pose proof (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hn _ _ _ _ _ HMn HE) as HMn'.
  exact (glu_univ_elem_exp_lower_uidx Hjn Hj Hn HA' HMn').
Qed.

(** A type glued at a value of a lower index is glued at a related value
    of a higher one. *)
Lemma glu_typ_transfer : forall (i j k : uidx) a a' P El P' El' Γ A,
    uidx_le i j -> uidx_le k j -> Dom a ≈ a' ∈ per_univ k ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El -> DG a' ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ A ® P -> Γ ⊢ A ® P'.
Proof.
  intros * Hij Hkj [R HR] Hi Hj HA.
  destruct (glu_univ_elem_cumu_ge_uidx Hij Hi) as (Pj & Elj & Hgj).
  pose proof (glu_univ_elem_typ_cumu_ge_uidx Hij Hi Hgj HA) as HAj.
  pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro _ R (per_univ_elem_cumu_uidx _ _ _ _ HR _ Hkj)) Hgj) as Hgj'.
  destruct (functional_glu_univ_elem _ _ _ _ _ _ Hgj' Hj) as [EP _].
  apply EP; exact HAj.
Qed.

(** An element of the relation of a domain's type, read at a related value. *)
Lemma dr_to_rel : forall B ρ b a1 c (i : uidx) R (jd : uidx), ⟦ B ⟧ ρ ↘ b -> Dom a1 ≈ b ∈ per_univ jd ->
    DF a1 ≈ a1 ∈ per_univ_elem i ↘ R -> per_head B B ρ ρ c c -> R c c.
Proof.
  intros * Eb [Rab HRab] HR Hc.
  pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRab) HRab) as Hbb.
  pose proof (Hc _ _ _ _ Eb Eb Hbb) as H.
  apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR HRab); exact H.
Qed.

Lemma sb_q_extend_wk : forall σ φ b, sb_eq ((q σ) ⨟ ((ι φ),,b)) ((sb_wk σ φ),,b).
Proof.
  intros σ φ b [| x]; [ reflexivity |].
  unfold sb_q, sb_extend, sb_wk; cbn.
  rewrite sentry_sub_wk, (sentry_sub_sb_eq _ _ (ι φ)) by (intros y; reflexivity).
  apply sentry_sub_of_wk.
Qed.

(** ** Closed Gluing at [⋅] Weakens to Every Glued Context

    Simpler than [closed_weaken_sem]: [nil_glu_sub_pred] does not constrain
    the environment, and the terms are the same, so no closedness is needed. *)

Lemma glu_rel_exp_nil_weaken : forall Γ N T, ⊩ Γ -> ⋅ ⊩ N : T -> Γ ⊩ N : T.
Proof.
  intros * [SbΓ HΓ] [Sb0 H0 i Hi].
  eapply mk_glu_rel_exp with (gre_lvl := i); [ exact HΓ |]; intros Δ σ ρ Hσ.
  apply Hi.
  inversion H0 as [Sb' Heq Hg | | | |]; subst.
  apply (Heq Δ σ ρ); cbn.
  apply wf_sub_nil', (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape HΓ _ _ _ Hσ)).
Qed.

(** A type a glued context ends with is glued. *)
Lemma glu_rel_typ_of_ctx_ext : forall Γ A, ⊩ Γ ▹ A -> exists i : nat, Γ ⊩ A : Typeω@i.
Proof.
  intros * [Sb HS].
  assert (HΓ : exists TSb, EG Γ ∈ glu_ctx_env ↘ TSb) by (inversion HS; subst; eexists; eassumption).
  destruct HΓ as [TSb HΓ].
  destruct (glu_ctx_env_cons_clean_inversion HΓ HS) as (i & _ & HAs & _).
  exists i; eapply mk_glu_rel_exp with (gre_lvl := S i); [ exact HΓ |]; intros Δ σ ρ Hσ.
  exact (glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub (glu_ctx_env_sub_escape HΓ _ _ _ Hσ) (HAs _ _ _ Hσ)).
Qed.

End Fixed_GCtx.
