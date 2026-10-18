(** * Telescopes over a Context in the PER Model

    The eliminator's motive and branches live under telescopes over the
    context of the elimination, whose types are those of a closed
    declaration instantiated by terms of the context.  This file gives the
    generic tools the eliminator's case of the fundamental theorem uses:

    - a closed context is a context over any other: its relation is weaker
      than that of the extension ([closed_app_sem]), so its judgments hold
      there ([closed_app_valid]);
    - its instance at terms of a context is a substitution built from valid
      parts ([gsub_closed_inst]);
    - the [q^n] of a semantic substitution into a context extended by a
      telescope ([rel_sub_qn]), and its value ([eval_sub_qn_args]);
    - related arguments of a telescope at the value of a substitution are
      related arguments of its instance ([tele_stage_rel]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members Inductives.
From Mctt.Core.Syntactic.System Require Import IndSyntax.
From Mctt.Core.Semantic.PER Require Import Tele.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases UniverseCases SubstitutionCases LetCases UnitCases InstanceCases GlobalArgs MemberReps
  FunctionCases IndSem.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** A Closed Context over Another *)

Lemma closed_app_sem : forall C Γ, tele_ass C -> ⊨ C -> ⊨ Γ ->
    ⊨ C ++ Γ /\
    (forall RC RCΓ, EF C ≈ C ∈ per_ctx_env ↘ RC -> EF C ++ Γ ≈ C ++ Γ ∈ per_ctx_env ↘ RCΓ ->
       forall ρ ρ', RCΓ ρ ρ' -> RC ρ ρ').
Proof.
  induction C as [| e C IH]; intros Γ HCa HC HΓ; cbn [List.app].
  - split; [ exact HΓ |].
    intros * HR _ ρ ρ' _.
    assert (E : RC <~> (fun _ _ => True)) by (eapply per_ctx_env_right_irrel; [ exact HR | exact per_ctx_env_nil_true ]).
    apply E; exact I.
  - assert (He : exists A, e = ce_ass A) by (inversion HCa as [| ? ? He _]; exact He).
    destruct He as [A ->].
    assert (HCa' : tele_ass C) by (inversion HCa; assumption).
    destruct (sem_ctx_ass_inv HC) as [i HA].
    pose proof (sem_ctx_tail HC) as HC'.
    destruct (IH Γ HCa' HC' HΓ) as [HCΓ Hres].
    destruct (sem_ctx_per_ctx_env HC') as [RC' HRC'].
    destruct (sem_ctx_per_ctx_env HCΓ) as [RCΓ' HRCΓ'].
    assert (HA' : C ++ Γ ⊨ A ≈ A : Typeω@i)
      by (eapply rel_exp_under_ctx_restrict; [ exact HRCΓ' | exact HRC' | apply Hres; assumption | exact HA ]).
    pose proof (per_ctx_env_of_typ HRC' HA) as HRCA.
    pose proof (per_ctx_env_of_typ HRCΓ' HA') as HRCΓA.
    split; [ econstructor; [ exact HCΓ | exact HRCΓA | exact HA' ] |].
    intros * HR HRΓ ρ ρ' Hρ.
    assert (E1 : RC <~> per_env_extend A A RC') by (eapply per_ctx_env_right_irrel; eassumption).
    assert (E2 : RCΓ <~> per_env_extend A A RCΓ') by (eapply per_ctx_env_right_irrel; eassumption).
    apply E1; apply E2 in Hρ; destruct Hρ as [Ht Hh].
    split; [ exact (Hres _ _ HRC' HRCΓ' _ _ Ht) | exact Hh ].
Qed.

Lemma closed_app_valid : forall C Γ T M M', tele_ass C -> ⊨ C -> ⊨ Γ ->
    C ⊨ M ≈ M' : T -> C ++ Γ ⊨ M ≈ M' : T.
Proof.
  intros * HCa HC HΓ HM.
  destruct (closed_app_sem C Γ HCa HC HΓ) as [HCΓ Hres].
  destruct (sem_ctx_per_ctx_env HC) as [RC HRC].
  destruct (sem_ctx_per_ctx_env HCΓ) as [RCΓ HRCΓ].
  eapply rel_exp_under_ctx_restrict; [ exact HRCΓ | exact HRC | apply Hres; assumption | exact HM ].
Qed.

(** ** The Instance of a Closed Context *)

Lemma gsub_closed_inst : forall C Γ Ms, tele_ass C -> ⊨ C -> ⊨ Γ ->
    List.length Ms = List.length C ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    gsub Γ (sb_of_list Id Ms) (C ++ Γ).
Proof.
  induction C as [| e C IH]; intros Γ Ms HCa HC HΓ Hl HMs.
  - destruct Ms; cbn in Hl; [| discriminate ]; cbn; constructor; exact HΓ.
  - assert (He : exists A, e = ce_ass A) by (inversion HCa as [| ? ? He _]; exact He).
    destruct He as [A ->].
    assert (HCa' : tele_ass C) by (inversion HCa; assumption).
    destruct (sem_ctx_ass_inv HC) as [i HA].
    pose proof (sem_ctx_tail HC) as HC'.
    destruct (List.exists_last (l := Ms) ltac:(intros ->; cbn in Hl; discriminate)) as (Ms' & M & ->).
    rewrite List.length_app in Hl; cbn in Hl.
    assert (Hl' : List.length Ms' = List.length C) by lia; clear Hl.
    assert (Hti : tele_insts (ce_ass A :: C) Id (Ms' ++ M :: nil) = tele_insts C Id Ms' ++ A[sb_of_list Id Ms'] :: nil).
    { change (ce_ass A :: C) with ((ce_ass A :: nil) ++ C).
      rewrite tele_insts_app by (try exact HCa'; lia); reflexivity. }
    assert (HlT : List.length (tele_insts C Id Ms') = List.length C) by (rewrite length_tele_insts by exact HCa'; lia).
    pose proof (IH Γ Ms' HCa' HC' HΓ ltac:(lia)) as Hg.
    rewrite sb_of_list_app; cbn [sb_of_list List.app].
    eapply gsub_ass; [ apply Hg | exact (closed_app_valid _ _ _ _ _ HCa' HC' HΓ HA) | ].
    + intros k N T HN HT.
      assert (Hk : k < List.length C) by (rewrite <- HlT; apply List.nth_error_Some; congruence).
      apply (HMs k); [ rewrite List.nth_error_app1 by lia; exact HN | rewrite Hti, List.nth_error_app1 by lia; exact HT ].
    + apply (HMs (List.length C)); [ rewrite List.nth_error_app2, Hl', Nat.sub_diag by lia; reflexivity |].
      rewrite Hti, List.nth_error_app2, HlT, Nat.sub_diag by lia; reflexivity.
Qed.

(** ** Relations along a Chain of Types *)

Lemma per_univ_elem_chain_iff : forall i j R S a b c,
    DF a ≈ b ∈ per_univ_elem i ↘ R -> DF b ≈ c ∈ per_univ_elem j ↘ S -> (R <~> S).
Proof.
  intros * H1 H2.
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ H1 H2) as (R' & H3 & E).
  etransitivity; [ exact E | eapply per_univ_elem_left_irrel; [ exact H3 | exact H2 ] ].
Qed.

(** ** Environments of a Context Extended by a Telescope *)

Lemma gargs_env_rel_gen : forall Δ Γ RΓ R ρ ρ' xs xs',
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> EF Δ ++ Γ ≈ Δ ++ Γ ∈ per_ctx_env ↘ R -> ⊨ Δ ++ Γ ->
    RΓ ρ ρ' -> List.length xs = List.length Δ ->
    per_gargs (List.rev Δ) ρ ρ' xs xs' -> R (env_args ρ xs) (env_args ρ' xs').
Proof.
  intros * HΓ HR HC Hρ Hl Hg.
  assert (HC' : ⊨ List.rev (List.rev Δ) ++ Γ) by (rewrite List.rev_involutive; exact HC).
  destruct (gargs_rel _ _ _ _ _ Hg _ _ HΓ Hρ HC') as (R' & HR' & Hρ').
  rewrite List.firstn_all2 in HR' by (rewrite List.length_rev; lia).
  rewrite List.rev_involutive in HR'.
  assert (E : R' <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
  apply E; exact Hρ'.
Qed.

(** ** [q^n] of a Semantic Substitution *)

Lemma rel_sub_qn : forall Δ Γ Γ' σ σ', tele_ass Δ -> ⊨ Δ ++ Γ -> Γ' ⊨ˢ σ ≈ σ' : Γ ->
    tele_sub Δ σ ++ Γ' ⊨ˢ sb_qn (List.length Δ) σ ≈ sb_qn (List.length Δ) σ' : Δ ++ Γ.
Proof.
  induction Δ as [| e Δ IH]; intros * HΔa HΔ Hσ; cbn [List.app tele_sub List.length sb_qn]; [ exact Hσ |].
  assert (He : exists A, e = ce_ass A) by (inversion HΔa as [| ? ? He _]; exact He).
  destruct He as [A ->].
  assert (HΔa' : tele_ass Δ) by (inversion HΔa; assumption).
  destruct (sem_ctx_ass_inv HΔ) as [i HA].
  cbn [centry_sub].
  exact (rel_sub_under_ctx_q (IH _ _ _ _ HΔa' (sem_ctx_tail HΔ) Hσ) HA).
Qed.

Lemma env_entry_args_lt : forall ρ ρ' xs x, x < List.length xs -> env_entry (env_args ρ xs) x = env_entry (env_args ρ' xs) x.
Proof.
  intros; rewrite !env_args_rev, !env_entry_nth, !List.app_nth1 by (rewrite List.length_rev, List.length_map; lia).
  reflexivity.
Qed.

Lemma eval_sub_qn_args : forall n σ ρ xs Y, List.length xs = n ->
    ⟦ sb_wk σ (wk_shiftn n) ⟧s env_args ρ xs ↘ Y -> ⟦ sb_qn n σ ⟧s env_args ρ xs ↘ env_args Y xs.
Proof.
  intros * Hl H x.
  destruct (Nat.lt_ge_cases x n) as [Hx | Hx].
  - rewrite sb_qn_lt by exact Hx; cbn; apply env_entry_args_lt; lia.
  - rewrite sb_qn_ge by exact Hx.
    replace x with (List.length xs + (x - n)) at 2 by lia.
    rewrite env_entry_args_app; exact (H (x - n)).
Qed.

(** The tail of [q^n] at a stage: the value of the substitution past the
    telescope's values, related to its value at the stage's own tail. *)
Lemma stage_base : forall Ψ Γ' Γ σ RΓ RS ρ ρσ xs,
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> EF Ψ ++ Γ' ≈ Ψ ++ Γ' ∈ per_ctx_env ↘ RS ->
    Γ' ⊨ˢ σ ≈ σ : Γ -> RS (env_args ρ xs) (env_args ρ xs) -> List.length xs = List.length Ψ -> ⟦ σ ⟧s ρ ↘ ρσ ->
    exists Y, ⟦ sb_wk σ (wk_shiftn (List.length Ψ)) ⟧s env_args ρ xs ↘ Y /\ RΓ Y ρσ.
Proof.
  intros * HΓ HS Hσ HE Hl Hev.
  destruct Hσ as [R1 H1 R2 H2 Hσ].
  pose proof (rel_wk_shiftn _ _ _ _ HS H1) as Hwk.
  destruct (Hσ _ _ HS _ Hwk _ _ HE) as [y1 y2 y3 y4 Hy1 Hy2 Hy3 Hy4 Hc].
  rewrite <- Hl, eval_wk_shiftn_args in Hy2.
  assert (Heq : env_eq y2 ρσ) by (eapply functional_eval_sub; eassumption).
  assert (E : R2 <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  exists y1; split; [ exact Hy1 |].
  apply E; eapply (per_ctx_env_resp_env_eq H2); [ reflexivity | exact Heq |].
  destruct Hc as (Hc & _); exact Hc.
Qed.

(** ** Instances along a Semantic Substitution *)

Lemma typ_inst_link : forall Δ0 Γ0 A A' (i : nat) τ RΓ0 E Eτ,
    Δ0 ⊨ A ≈ A' : Typeω@i -> EF Γ0 ≈ Γ0 ∈ per_ctx_env ↘ RΓ0 -> Γ0 ⊨ˢ τ ≈ τ : Δ0 ->
    RΓ0 E E -> ⟦ τ ⟧s E ↘ Eτ ->
    exists a b, ⟦ A[τ] ⟧ E ↘ a /\ ⟦ A ⟧ Eτ ↘ b /\ Dom a ≈ b ∈ per_univ i.
Proof.
  intros * HA HΓ0 Hτ HE Hev.
  destruct (rel_exp_of_typ_inversion HA) as (R & HR & Hgen).
  destruct (Hgen _ _ HΓ0 _ _ Hτ _ _ _ _ HE Hev Hev) as [a b c d Ha Hb Hc Hd Hch].
  exists a, b; split; [ exact Ha | split; [ exact Hb | destruct Hch as (H & _); exact H ] ].
Qed.

Lemma exp_inst_link : forall Δ0 Γ0 T M M' τ RΓ0 E Eτ,
    Δ0 ⊨ M ≈ M' : T -> EF Γ0 ≈ Γ0 ∈ per_ctx_env ↘ RΓ0 -> Γ0 ⊨ˢ τ ≈ τ : Δ0 ->
    RΓ0 E E -> ⟦ τ ⟧s E ↘ Eτ ->
    exists m n, ⟦ M[τ] ⟧ E ↘ m /\ ⟦ M ⟧ Eτ ↘ n /\ Dom m ≈ n ∈ per_head T T Eτ Eτ.
Proof.
  intros * HM HΓ0 Hτ HE Hev.
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  destruct HMl as [R HR i Hgen].
  destruct (Hgen _ _ HΓ0 _ _ Hτ _ _ _ _ HE Hev Hev) as (R0 & [a b c d Ha Hb Hc Hd Hch] & [m n n' m' Hm Hn Hn' Hm' Hmc]).
  exists m, n; split; [ exact Hm | split; [ exact Hn |] ].
  destruct Hch as (_ & Hbc & _); destruct Hmc as (Hmn & _).
  eapply per_head_of; [ exact Hb | exact Hc | exact Hbc | exact Hmn ].
Qed.

(** ** The Instance of a Telescope at the Value of a Substitution

    Arguments related at a telescope over the value of [σ] at [ρ] are, over
    [ρ], related at its instance by [σ]. *)
Lemma tele_stage_rel : forall Δ Γ Γ' σ RΓ' ρ ρσ, tele_ass Δ -> ⊨ Δ ++ Γ ->
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ ≈ σ : Γ -> RΓ' ρ ρ -> ⟦ σ ⟧s ρ ↘ ρσ ->
    forall xs, per_gargs (List.rev Δ) ρσ ρσ xs xs -> List.length xs = List.length Δ ->
    forall RS, EF tele_sub Δ σ ++ Γ' ≈ tele_sub Δ σ ++ Γ' ∈ per_ctx_env ↘ RS -> RS (env_args ρ xs) (env_args ρ xs).
Proof.
  induction Δ as [| e Δ IH]; intros * HΔa HΔ HΓ' Hσ Hρ Hev xs Hg Hl RS HS.
  - destruct xs; cbn in Hl; [| discriminate ].
    cbn in HS; assert (E : RS <~> RΓ') by (eapply per_ctx_env_right_irrel; eassumption).
    apply E; exact Hρ.
  - assert (He : exists A, e = ce_ass A) by (inversion HΔa as [| ? ? He _]; exact He).
    destruct He as [B ->].
    assert (HΔa' : tele_ass Δ) by (inversion HΔa; assumption).
    destruct (sem_ctx_ass_inv HΔ) as [i HB].
    pose proof (sem_ctx_tail HΔ) as HΔ'.
    destruct (List.exists_last (l := xs) ltac:(intros ->; cbn in Hl; discriminate)) as (xs' & x & ->).
    rewrite List.length_app in Hl; cbn in Hl.
    assert (Hl' : List.length xs' = List.length Δ) by lia; clear Hl.
    cbn [List.rev] in Hg.
    assert (Hlr : List.length xs' = List.length (List.rev Δ)) by (rewrite List.length_rev; exact Hl').
    destruct (per_gargs_app (List.rev Δ) (ce_ass B :: nil) ρσ ρσ xs' xs' (x :: nil) (x :: nil) Hlr Hg Hlr)
      as [Hg' Hgx].
    inversion Hgx as [| ? ? ? ? ? ? ? ? ? R0 HB0 Hx _]; subst.
    pose proof (sem_ctx_app_r _ _ HΔ') as HΓ.
    destruct (sem_ctx_per_ctx_env HΓ) as [RΓ HRΓ].
    destruct (sem_ctx_per_ctx_env HΔ') as [RΔ HRΔ].
    pose proof (rel_sub_qn _ _ _ _ _ HΔa' HΔ' Hσ) as Hq.
    destruct (rel_sub_under_ctx_simple Hq) as (RS' & HS' & _).
    pose proof (IH _ _ _ _ _ _ HΔa' HΔ' HΓ' Hσ Hρ Hev xs' Hg' Hl' RS' HS') as IHx.
    cbn [tele_sub List.app centry_sub] in HS.
    pose proof (per_ctx_env_of_typ_sub HS' Hq HB) as HS2.
    assert (E : RS <~> per_env_extend B[sb_qn (List.length Δ) σ] B[sb_qn (List.length Δ) σ] RS')
      by (eapply per_ctx_env_right_irrel; eassumption).
    apply E; rewrite env_args_snoc.
    split; [ exact IHx |].
    (** The head: the instance's value at the stage, against the type's at
        the value of [q^n σ] and then at [ρσ]. *)
    destruct (stage_base (tele_sub Δ σ) Γ' Γ σ RΓ RS' ρ ρσ xs' HRΓ HS' Hσ IHx ltac:(rewrite length_tele_sub; exact Hl') Hev)
      as (Y & HY & HYρ).
    rewrite length_tele_sub in HY.
    pose proof (eval_sub_qn_args _ _ _ _ _ Hl' HY) as Hqev.
    destruct (typ_inst_link _ _ _ _ _ _ _ _ _ HB HS' (rel_sub_under_ctx_refl_left Hq) IHx Hqev) as (a & b & Ea & Eb & Hab).
    assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
    assert (Hρσ : RΓ ρσ ρσ) by (etransitivity; [ symmetry; exact HYρ | exact HYρ ]).
    assert (HgY : per_gargs (List.rev Δ) Y ρσ xs' xs').
    { eapply (per_gargs_base _ _ _ HRΓ ltac:(rewrite List.rev_involutive; exact HΔ') ltac:(apply List.Forall_rev; exact HΔa')
                ρσ ρσ); [ exact Hρσ | symmetry; exact HYρ | exact Hρσ | exact Hg' ]. }
    pose proof (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRΔ HΔ' HYρ Hl' HgY) as HYE.
    destruct (rel_exp_of_typ_inversion_simple_at HRΔ HB _ _ HYE) as (b' & c & Eb' & Ec & Hbc).
    assert (b' = b) as -> by (eapply functional_eval_exp; eassumption).
    destruct HB0 as [c0 c1 Ec0 Ec1 HR0].
    assert (c0 = c) as -> by (eapply functional_eval_exp; eassumption).
    intros j R a1 a2 Ea1 Ea2 HR.
    assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (a2 = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct Hab as [R1 HR1]; destruct Hbc as [R2 HR2].
    assert (E1 : R <~> R1) by (eapply per_univ_elem_right_irrel; [ exact HR | exact HR1 ]).
    assert (E2 : R1 <~> R2) by (eapply per_univ_elem_chain_iff; [ exact HR1 | exact HR2 ]).
    assert (E3 : R2 <~> R0) by (eapply per_univ_elem_chain_iff; [ exact HR2 | exact HR0 ]).
    apply E1, E2, E3; exact Hx.
Qed.

(** ** Base Change for a Closed Context *)

Lemma closed_env_base : forall C RC zs zs' B1 B2 B3 B4, tele_ass C -> ⊨ C ->
    EF C ≈ C ∈ per_ctx_env ↘ RC -> List.length zs = List.length C -> List.length zs' = List.length C ->
    RC (env_args B1 zs) (env_args B2 zs') -> RC (env_args B3 zs) (env_args B4 zs').
Proof.
  intros * HCa HC HRC Hl Hl' H.
  assert (HC' : ⊨ List.rev (List.rev C) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HC).
  assert (HRC' : EF List.rev (List.rev C) ++ ⋅ ≈ List.rev (List.rev C) ++ ⋅ ∈ per_ctx_env ↘ RC)
    by (rewrite List.rev_involutive, List.app_nil_r; exact HRC).
  assert (HCr : tele_ass (List.rev C)) by (apply List.Forall_rev; exact HCa).
  destruct (rel_gargs _ _ _ _ per_ctx_env_nil_true HC' HCr HRC' B1 B2 zs zs'
              ltac:(rewrite List.length_rev; exact Hl) ltac:(rewrite List.length_rev; exact Hl') H) as [_ Hg].
  pose proof (per_gargs_base _ _ _ per_ctx_env_nil_true HC' HCr B1 B2 B3 B4 zs zs' I I I Hg) as Hg'.
  assert (HC0 : ⊨ C ++ ⋅) by (rewrite List.app_nil_r; exact HC).
  assert (HRC0 : EF C ++ ⋅ ≈ C ++ ⋅ ∈ per_ctx_env ↘ RC) by (rewrite List.app_nil_r; exact HRC).
  exact (gargs_env_rel_gen C ⋅ _ _ _ _ _ _ per_ctx_env_nil_true HRC0 HC0 I Hl Hg').
Qed.

(** ** Instances of a Closed Type

    A type [X] of a closed context [Pre ++ C0], instantiated past [Pre] by a
    substitution [τ] of [C0], is related at an environment of the instance of
    [Pre] to [X] at any environment related to the values there. *)
Lemma closed_typ_inst : forall Pre C0 Γ X (j : nat) τ RΓ RK RS B zs Bτ F,
    tele_ass (Pre ++ C0) -> ⊨ Pre ++ C0 -> tele_ass C0 -> ⊨ C0 -> ⊨ Γ ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> EF Pre ++ C0 ≈ Pre ++ C0 ∈ per_ctx_env ↘ RK ->
    EF tele_sub Pre τ ++ Γ ≈ tele_sub Pre τ ++ Γ ∈ per_ctx_env ↘ RS ->
    Pre ++ C0 ⊨ X : Typeω@j -> Γ ⊨ˢ τ ≈ τ : C0 ++ Γ ->
    RS (env_args B zs) (env_args B zs) -> List.length zs = List.length Pre ->
    ⟦ τ ⟧s B ↘ Bτ -> RK (env_args Bτ zs) F ->
    exists a b, ⟦ X[sb_qn (List.length Pre) τ] ⟧ env_args B zs ↘ a /\ ⟦ X ⟧ F ↘ b /\ Dom a ≈ b ∈ per_univ j.
Proof.
  intros * HKa HK HC0a HC0 HΓ HRΓ HRK HRS HX Hτ HE Hl Hev HF.
  destruct (closed_app_sem _ _ HKa HK HΓ) as [HKΓ HresK].
  destruct (closed_app_sem _ _ HC0a HC0 HΓ) as [HC0Γ Hres0].
  destruct (sem_ctx_per_ctx_env HC0Γ) as [R0Γ HR0Γ].
  destruct (sem_ctx_per_ctx_env HC0) as [R0 HR0].
  assert (HPK : PER RK) by (eapply per_env_PER; exact HRK).
  assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
  assert (HPa : tele_ass Pre) by (apply List.Forall_app in HKa as [H _]; exact H).
  (** The value of [q^n τ]. *)
  destruct (stage_base (tele_sub Pre τ) Γ (C0 ++ Γ) τ R0Γ RS B Bτ zs HR0Γ HRS Hτ HE
              ltac:(rewrite length_tele_sub; exact Hl) Hev) as (Y & HY & HYτ).
  rewrite length_tele_sub in HY.
  pose proof (eval_sub_qn_args _ _ _ _ _ Hl HY) as Hqev.
  pose proof (rel_sub_qn Pre (C0 ++ Γ) Γ τ τ HPa ltac:(rewrite List.app_assoc; exact HKΓ) Hτ) as Hq.
  assert (HXΓ : Pre ++ C0 ++ Γ ⊨ X : Typeω@j) by (rewrite List.app_assoc; exact (closed_app_valid _ _ _ _ _ HKa HK HΓ HX)).
  destruct (typ_inst_link _ _ _ _ _ _ _ _ _ HXΓ HRS (rel_sub_under_ctx_refl_left Hq) HE Hqev) as (a & b0 & Ea & Eb0 & Hab).
  (** The value at the instance's tail, against the given one. *)
  assert (HYτ0 : R0 Y Bτ) by (exact (Hres0 _ _ HR0 HR0Γ _ _ HYτ)).
  assert (HPre : ⊨ List.rev (List.rev Pre) ++ C0) by (rewrite List.rev_involutive; exact HK).
  assert (HRK' : EF List.rev (List.rev Pre) ++ C0 ≈ List.rev (List.rev Pre) ++ C0 ∈ per_ctx_env ↘ RK)
    by (rewrite List.rev_involutive; exact HRK).
  assert (HBB : RK (env_args Bτ zs) (env_args Bτ zs)) by (etransitivity; [ exact HF | symmetry; exact HF ]).
  destruct (rel_gargs _ _ _ _ HR0 HPre (List.Forall_rev HPa) HRK' Bτ Bτ zs zs
              ltac:(rewrite List.length_rev; exact Hl) ltac:(rewrite List.length_rev; exact Hl) HBB) as [HBτ Hg].
  pose proof (per_gargs_base _ _ _ HR0 HPre (List.Forall_rev HPa) Bτ Bτ Y Bτ zs zs HBτ (symmetry HYτ0) HBτ Hg) as Hg'.
  pose proof (gargs_env_rel_gen Pre C0 _ _ _ _ _ _ HR0 HRK HK HYτ0 Hl Hg') as HYB.
  assert (HYF : RK (env_args Y zs) F) by (etransitivity; [ exact HYB | exact HF ]).
  destruct (rel_exp_of_typ_inversion_simple_at HRK HX _ _ HYF) as (b1 & b & Eb1 & Eb & Hbb).
  assert (b1 = b0) as -> by (eapply functional_eval_exp; eassumption).
  exists a, b; split; [ exact Ea | split; [ exact Eb | etransitivity; [ exact Hab | exact Hbb ] ] ].
Qed.

(** ** Substitutions Built from Valid Parts, over Telescopes *)

Lemma gsub_of_list : forall Δ Γ Γ1 σ0 Ms, gsub Γ σ0 Γ1 -> tele_ass Δ -> ⊨ Δ ++ Γ1 ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ σ0 Ms) k = Some T -> Γ ⊨ N : T) ->
    gsub Γ (sb_of_list σ0 Ms) (Δ ++ Γ1).
Proof.
  induction Δ as [| e Δ IH]; intros Γ Γ1 σ0 Ms Hg0 HCa HC Hl HMs.
  - destruct Ms; cbn in Hl; [| discriminate ]; cbn; exact Hg0.
  - assert (He : exists A, e = ce_ass A) by (inversion HCa as [| ? ? He _]; exact He).
    destruct He as [A ->].
    assert (HCa' : tele_ass Δ) by (inversion HCa; assumption).
    destruct (sem_ctx_ass_inv HC) as [i HA].
    pose proof (sem_ctx_tail HC) as HC'.
    destruct (List.exists_last (l := Ms) ltac:(intros ->; cbn in Hl; discriminate)) as (Ms' & M & ->).
    rewrite List.length_app in Hl; cbn in Hl.
    assert (Hl' : List.length Ms' = List.length Δ) by lia; clear Hl.
    assert (Hti : tele_insts (ce_ass A :: Δ) σ0 (Ms' ++ M :: nil) = tele_insts Δ σ0 Ms' ++ A[sb_of_list σ0 Ms'] :: nil).
    { change (ce_ass A :: Δ) with ((ce_ass A :: nil) ++ Δ).
      rewrite tele_insts_app by (try exact HCa'; lia); reflexivity. }
    assert (HlT : List.length (tele_insts Δ σ0 Ms') = List.length Δ) by (rewrite length_tele_insts by exact HCa'; lia).
    rewrite sb_of_list_app; cbn [sb_of_list List.app].
    eapply gsub_ass; [ apply (IH _ _ _ _ Hg0 HCa' HC' Hl') | exact HA | ].
    + intros k N T HN HT.
      assert (Hk : k < List.length Δ) by (rewrite <- HlT; apply List.nth_error_Some; congruence).
      apply (HMs k); [ rewrite List.nth_error_app1 by lia; exact HN | rewrite Hti, List.nth_error_app1 by lia; exact HT ].
    + apply (HMs (List.length Δ)); [ rewrite List.nth_error_app2, Hl', Nat.sub_diag by lia; reflexivity |].
      rewrite Hti, List.nth_error_app2, HlT, Nat.sub_diag by lia; reflexivity.
Qed.

Lemma sem_ctx_ext_typ : forall Γ A (i : nat), ⊨ Γ -> Γ ⊨ A : Typeω@i -> ⊨ Γ ▹ A.
Proof.
  intros * HΓ HA; destruct (sem_ctx_per_ctx_env HΓ) as [R HR].
  econstructor; [ exact HΓ | exact (per_ctx_env_of_typ HR HA) | exact HA ].
Qed.

Lemma gsub_sem_ctx : forall Γ τ Δ, gsub Γ τ Δ -> ⊨ Γ.
Proof. intros * Hg; exact (proj1 (gsub_sem Hg)). Qed.

Lemma gsub_qn : forall Pre Γ0 τ Δ0, gsub Γ0 τ Δ0 -> tele_ass Pre -> ⊨ Pre ++ Δ0 ->
    gsub (tele_sub Pre τ ++ Γ0) (sb_qn (List.length Pre) τ) (Pre ++ Δ0).
Proof.
  induction Pre as [| e Pre IH]; intros * Hg HPa HP; cbn [tele_sub List.app List.length sb_qn]; [ exact Hg |].
  assert (He : exists A, e = ce_ass A) by (inversion HPa as [| ? ? He _]; exact He).
  destruct He as [B ->].
  assert (HPa' : tele_ass Pre) by (inversion HPa; assumption).
  destruct (sem_ctx_ass_inv HP) as [i HB].
  cbn [centry_sub].
  exact (gsub_q _ _ _ _ _ (IH _ _ _ Hg HPa' (sem_ctx_tail HP)) HB).
Qed.

Lemma gsub_wk : forall Γ φ Δ, Γ ⊨ʷ φ : Δ -> ⊨ Γ -> ⊨ Δ -> gsub Γ (sb_of_wk φ) Δ.
Proof.
  intros * Hφ HΓ HΔ.
  eapply gsub_eq; [ eapply gsub_comp; [ constructor; exact HΔ | exact HΓ | exact (rel_sub_of_wk Hφ) | exact (sub_link_wk Hφ) ] |].
  intros x; reflexivity.
Qed.

(** ** Telescopes of [Π] *)

Lemma rel_exp_ctx_pi : forall Δ Γ B (i : nat), tele_ass Δ -> ⊨ Δ ++ Γ -> Δ ++ Γ ⊨ B : Typeω@i ->
    exists j : nat, Γ ⊨ ctx_pi Δ B : Typeω@j.
Proof.
  induction Δ as [| e Δ IH]; intros * HΔa HΔ HB; [ exists i; exact HB |].
  assert (He : exists A, e = ce_ass A) by (inversion HΔa as [| ? ? He _]; exact He).
  destruct He as [A ->].
  assert (HΔa' : tele_ass Δ) by (inversion HΔa; assumption).
  destruct (sem_ctx_ass_inv HΔ) as [k HA].
  cbn [ctx_pi].
  apply (IH _ _ (max k i) HΔa' (sem_ctx_tail HΔ)).
  apply rel_exp_pi_cong; [ eapply rel_exp_cumu_ge; [| exact HA ]; lia | eapply rel_exp_cumu_ge; [| exact HB ]; lia ].
Qed.

Lemma rel_exp_apps_ctx_pi_n : forall n Δ Γ B (i : nat) M Ms,
    List.length Δ = n -> tele_ass Δ -> ⊨ Δ ++ Γ -> Δ ++ Γ ⊨ B : Typeω@i ->
    Γ ⊨ M : ctx_pi Δ B ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T -> Γ ⊨ N : T) ->
    Γ ⊨ apps M Ms : B[sb_of_list Id Ms].
Proof.
  induction n as [| n IH]; intros * Hn Hass HΔ HB HM Hl HMs.
  - destruct Δ; [| discriminate ]; destruct Ms; [| discriminate ]; cbn; rewrite exp_sub_id; exact HM.
  - destruct (List.exists_last (l := Δ)) as (Δ0 & e & ->); [ intros ->; discriminate |].
    rename Δ0 into Δ.
    rewrite List.length_app in Hn; cbn in Hn.
    unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A0 ->] _].
    rewrite List.length_app in Hl; cbn in Hl.
    destruct Ms as [| M0 Ms]; [ cbn in Hl; lia |]; cbn in Hl.
    rewrite ctx_pi_snoc in HM; rewrite <- List.app_assoc in HΔ, HB; cbn [List.app] in HΔ, HB.
    pose proof (sem_ctx_app_r _ _ HΔ) as HΓA.
    destruct (sem_ctx_ass_inv HΓA) as [k HA0].
    pose proof (sem_ctx_tail HΓA) as HΓ.
    destruct (rel_exp_ctx_pi _ _ _ _ Hass HΔ HB) as [j HPi].
    assert (HM0 : Γ ⊨ M0 : A0)
      by (rewrite <- (exp_sub_id A0); apply (HMs 0); [ reflexivity | rewrite tele_insts_snoc; reflexivity ]).
    assert (Happ : Γ ⊨ M $ M0 : (ctx_pi Δ B)[Id,,M0]).
    { eapply (rel_exp_app_cong (i := max k j)); [ eapply rel_exp_cumu_ge; [| exact HA0 ]; lia
                                                | eapply rel_exp_cumu_ge; [| exact HPi ]; lia | exact HM | exact HM0 ]. }
    rewrite ctx_pi_sub in Happ.
    assert (Hg0 : gsub Γ (Id,,M0) (Γ ▹ A0)).
    { eapply gsub_ass; [ constructor; exact HΓ | exact HA0 | rewrite exp_sub_id; exact HM0 ]. }
    pose proof (gsub_qn _ _ _ _ Hg0 Hass HΔ) as Hgq.
    pose proof (gsub_sem_ctx _ _ _ Hgq) as HΔ'.
    pose proof (rel_exp_under_ctx_gsub Hgq HB) as HB'; cbn [exp_sub] in HB'.
    cbn [apps_exp sb_of_list].
    replace (B[sb_of_list (Id,,M0) Ms]) with (B[sb_qn (List.length Δ) (Id,,M0)][sb_of_list Id Ms])
      by (replace (List.length Δ) with (List.length Ms) by lia; apply exp_sub_qn_of_list).
    eapply (IH (tele_sub Δ (Id,,M0)) Γ (B[sb_qn (List.length Δ) (Id,,M0)]) i (M $ M0) Ms); [ rewrite length_tele_sub; lia | apply tele_ass_sub; exact Hass | exact HΔ' | exact HB' | exact Happ
               | rewrite length_tele_sub; lia |].
    intros k' N T HN HT; apply (HMs (S k')); [ exact HN |].
    rewrite tele_insts_snoc; cbn [List.nth_error].
    rewrite tele_insts_tele_sub in HT; rewrite <- HT; f_equal.
    apply tele_insts_sb_eq; symmetry; apply sb_compose_id_right.
Qed.


(** A judgment about closed terms at [⋅] holds in every context. *)
Lemma closed_weaken_valid : forall Γ T N N', ⊨ Γ -> ⋅ ⊨ N ≈ N' : T -> Γ ⊨ N ≈ N' : T.
Proof.
  intros * HΓ H.
  rewrite <- (exp_wk_id_ext T wk_id), <- (exp_wk_id_ext N wk_id), <- (exp_wk_id_ext N' wk_id) by (intros x; reflexivity).
  eapply rel_exp_under_ctx_wk; [| exact H ].
  destruct (sem_ctx_per_ctx_env HΓ) as [R HR].
  eapply (rel_wk_under_ctx_intro (R' := fun _ _ => True)); [ exact HR | |].
  - apply per_ctx_env_nil; reflexivity.
  - constructor; [ apply wk_mono_id | intros; exact I ].
Qed.

(** ** The Outer Links of a Judgment over a Telescope

    The instance of a judgment over [Δ ++ Γ] along [q^n σ], at an
    environment of the instance of [Δ] over [ρ], against the judgment at
    the value of [σ] at [ρ] extended by the same arguments. *)
Lemma outer_base : forall Δ Γ Γ' RΓ' σ ρ ρσ, tele_ass Δ -> ⊨ Δ ++ Γ ->
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ ≈ σ : Γ -> RΓ' ρ ρ -> ⟦ σ ⟧s ρ ↘ ρσ ->
    forall xs, per_gargs (List.rev Δ) ρσ ρσ xs xs -> List.length xs = List.length Δ ->
    exists RS RΔ Y, EF tele_sub Δ σ ++ Γ' ≈ tele_sub Δ σ ++ Γ' ∈ per_ctx_env ↘ RS /\ RS (env_args ρ xs) (env_args ρ xs) /\
      EF Δ ++ Γ ≈ Δ ++ Γ ∈ per_ctx_env ↘ RΔ /\
      ⟦ sb_qn (List.length Δ) σ ⟧s env_args ρ xs ↘ env_args Y xs /\
      RΔ (env_args Y xs) (env_args ρσ xs) /\
      tele_sub Δ σ ++ Γ' ⊨ˢ sb_qn (List.length Δ) σ ≈ sb_qn (List.length Δ) σ : Δ ++ Γ.
Proof.
  intros * HΔa HΔ HΓ' Hσ Hρ Hev xs Hg Hl.
  pose proof (rel_sub_qn _ _ _ _ _ HΔa HΔ Hσ) as Hq.
  destruct (rel_sub_under_ctx_simple Hq) as (RS & HRS & _).
  pose proof (tele_stage_rel _ _ _ _ _ _ _ HΔa HΔ HΓ' Hσ Hρ Hev _ Hg Hl _ HRS) as HE.
  pose proof (sem_ctx_app_r _ _ HΔ) as HΓ.
  destruct (sem_ctx_per_ctx_env HΓ) as [RΓ HRΓ].
  destruct (sem_ctx_per_ctx_env HΔ) as [RΔ HRΔ].
  destruct (stage_base (tele_sub Δ σ) Γ' Γ σ RΓ RS ρ ρσ xs HRΓ HRS Hσ HE ltac:(rewrite length_tele_sub; exact Hl) Hev)
    as (Y & HY & HYρ).
  rewrite length_tele_sub in HY.
  pose proof (eval_sub_qn_args _ _ _ _ _ Hl HY) as Hqev.
  assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
  assert (Hρσ : RΓ ρσ ρσ) by (etransitivity; [ symmetry; exact HYρ | exact HYρ ]).
  assert (HgY : per_gargs (List.rev Δ) Y ρσ xs xs).
  { eapply (per_gargs_base _ _ _ HRΓ ltac:(rewrite List.rev_involutive; exact HΔ) ltac:(apply List.Forall_rev; exact HΔa)
              ρσ ρσ); [ exact Hρσ | symmetry; exact HYρ | exact Hρσ | exact Hg ]. }
  pose proof (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRΔ HΔ HYρ Hl HgY) as HYE.
  exists RS, RΔ, Y; repeat split; assumption.
Qed.

Lemma outer_typ_link : forall Δ Γ Γ' RΓ' σ ρ ρσ A A' (i : nat), tele_ass Δ -> ⊨ Δ ++ Γ ->
    Δ ++ Γ ⊨ A ≈ A' : Typeω@i ->
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ ≈ σ : Γ -> RΓ' ρ ρ -> ⟦ σ ⟧s ρ ↘ ρσ ->
    forall xs, per_gargs (List.rev Δ) ρσ ρσ xs xs -> List.length xs = List.length Δ ->
    exists a b, ⟦ A[sb_qn (List.length Δ) σ] ⟧ env_args ρ xs ↘ a /\ ⟦ A ⟧ env_args ρσ xs ↘ b /\ Dom a ≈ b ∈ per_univ i.
Proof.
  intros * HΔa HΔ HA HΓ' Hσ Hρ Hev xs Hg Hl.
  destruct (outer_base _ _ _ _ _ _ _ HΔa HΔ HΓ' Hσ Hρ Hev _ Hg Hl) as (RS & RΔ & Y & HRS & HE & HRΔ & Hqev & HYE & Hq).
  pose proof (rel_exp_under_ctx_refl_left HA) as HAl.
  destruct (typ_inst_link _ _ _ _ _ _ _ _ _ HAl HRS Hq HE Hqev) as (a & b0 & Ea & Eb0 & Hab).
  destruct (rel_exp_of_typ_inversion_simple_at HRΔ HAl _ _ HYE) as (b1 & b & Eb1 & Eb & Hbb).
  assert (b1 = b0) as -> by (eapply functional_eval_exp; eassumption).
  exists a, b; split; [ exact Ea | split; [ exact Eb | etransitivity; [ exact Hab | exact Hbb ] ] ].
Qed.

Lemma outer_exp_link : forall Δ Γ Γ' RΓ' σ ρ ρσ T M M', tele_ass Δ -> ⊨ Δ ++ Γ ->
    Δ ++ Γ ⊨ M ≈ M' : T ->
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ ≈ σ : Γ -> RΓ' ρ ρ -> ⟦ σ ⟧s ρ ↘ ρσ ->
    forall xs, per_gargs (List.rev Δ) ρσ ρσ xs xs -> List.length xs = List.length Δ ->
    exists RΔ F m n, EF Δ ++ Γ ≈ Δ ++ Γ ∈ per_ctx_env ↘ RΔ /\ RΔ F (env_args ρσ xs) /\
      ⟦ M[sb_qn (List.length Δ) σ] ⟧ env_args ρ xs ↘ m /\ ⟦ M ⟧ env_args ρσ xs ↘ n /\
      Dom m ≈ n ∈ per_head T T F (env_args ρσ xs).
Proof.
  intros * HΔa HΔ HM HΓ' Hσ Hρ Hev xs Hg Hl.
  destruct (outer_base _ _ _ _ _ _ _ HΔa HΔ HΓ' Hσ Hρ Hev _ Hg Hl) as (RS & RΔ & Y & HRS & HE & HRΔ & Hqev & HYE & Hq).
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  destruct (exp_inst_link _ _ _ _ _ _ _ _ _ HMl HRS Hq HE Hqev) as (m & n0 & Em & En0 & Hmn).
  destruct (rel_exp_under_ctx_simple_full_at HRΔ HMl) as [k Hs].
  destruct (Hs _ _ HYE) as (t1 & t2 & Rt & Et1 & Et2 & HRt & n1 & n & En1 & En & Hnn).
  assert (n1 = n0) as -> by (eapply functional_eval_exp; eassumption).
  exists RΔ, (env_args Y xs), m, n; repeat split; try assumption.
  (** Both relations are those of the type at the left environment. *)
  pose proof (per_univ_elem_sym _ _ _ _ HRt) as [HRts _].
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HRt HRts) as (R11 & HR11 & E11).
  assert (HPt : PER Rt) by (eapply per_elem_PER; exact HRt).
  apply (per_head_iff Et1 Et1 HR11) in Hmn.
  eapply per_head_of; [ exact Et1 | exact Et2 | exact HRt |].
  etransitivity; [ apply E11; exact Hmn | exact Hnn ].
Qed.

End Fixed_GCtx.
