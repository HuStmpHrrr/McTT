(** * Representations of Member Types

    The canonical type of a member is built from the unit's parameters, the
    body before the member and the member's own type, then instantiated with
    the arguments a module expression supplies.  A representation records this
    shape: a telescope of parameters (outermost) and of local definitions and
    modules, generalized over a type valid in the extended context, under a
    substitution built from valid parts.  It is what makes every instance
    [C[Id,,N]] that [mt_app] forms a valid type, without inverting [Π]. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases FunctionCases UniverseCases SubstitutionCases SubtypingCases
  VariableCases LetCases TrueFalseCases UnitCases InstanceCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Semantic Contexts *)

Lemma rel_ctx_extend_mod' : forall {Γ U}, ⊨ Γ -> Γ ⊨ᵘ U ≈ U -> ⊨ Γ ▹ₘ U.
Proof.
  intros * HΓ (HU & HsU & _).
  destruct (sem_ctx_per_ctx_env HΓ) as [R HR].
  econstructor; [ exact HΓ | exact (per_ctx_env_of_mod HR HU) | exact HU | exact HsU ].
Qed.

Lemma sem_ctx_ass_inv : forall {Γ A}, ⊨ Γ ▹ A -> exists i, Γ ⊨ A : Typeω@i.
Proof. intros * H; inversion H; subst; eauto. Qed.

Lemma sem_ctx_def_inv : forall {Γ A M}, ⊨ Γ ▸ A ≔ M -> (exists i, Γ ⊨ A : Typeω@i) /\ Γ ⊨ M : A.
Proof. intros * H; inversion H; subst; eauto. Qed.

Lemma sem_ctx_mod_inv : forall {Γ U}, ⊨ Γ ▹ₘ U -> Γ ⊨ᵘ U ≈ U.
Proof. intros * H; inversion H; subst; split; [ assumption | split; assumption ]. Qed.

Lemma gsub_sem : forall {Γ τ Δ}, gsub Γ τ Δ -> ⊨ Γ /\ ⊨ Δ.
Proof.
  induction 1 as [? HΓ | ? ? ? ? ? ? ? [IH1 IH2] HB HN | ? ? ? ? ? ? ? [IH1 IH2] HB HM
                 | ? ? ? ? ? [IH1 IH2] HU | ? ? ? ? ? [IH1 IH2] Eq | ? ? ? ? ? HG [IH1 IH2] HB
                 | ? ? ? ? ? ? [IH1 IH2] HΓ Hσ Hl ];
    try (split; assumption).
  - split; [ assumption | eapply rel_ctx_extend'; eassumption ].
  - split; [ assumption | eapply rel_ctx_extend_def'; eassumption ].
  - split; [ assumption | eapply rel_ctx_extend_mod'; eassumption ].
  - pose proof (rel_exp_under_ctx_gsub HG HB) as H; cbn in H.
    split; eapply rel_ctx_extend'; eassumption.
Qed.

(** ** Generalizing over a Telescope *)

Definition lets_only (Ψ : ctx) : Prop := List.Forall (fun e => forall B, e <> ce_ass B) Ψ.

Lemma valid_ctx_pi : forall Ψ D X i, ⊨ Ψ ++ D -> Ψ ++ D ⊨ X : Typeω@i -> exists j, D ⊨ ctx_pi Ψ X : Typeω@j.
Proof.
  induction Ψ as [| e Ψ IH]; intros * HΨ HX; cbn in *; [ eauto |].
  destruct e as [B | B M | U].
  - destruct (sem_ctx_ass_inv HΨ) as [k HB].
    eapply IH; [ exact (sem_ctx_tail HΨ) |].
    apply (rel_exp_pi_cong (i := max i k)); eapply rel_exp_cumu_ge; [| exact HB | | exact HX ]; lia.
  - destruct (sem_ctx_def_inv HΨ) as [[k HB] HM].
    eapply IH; [ exact (sem_ctx_tail HΨ) |].
    pose proof (valid_exp_let (oA := Some B) HB HM HX) as H; cbn in H; exact H.
  - pose proof (sem_ctx_mod_inv HΨ) as HU.
    eapply IH; [ exact (sem_ctx_tail HΨ) |].
    pose proof (valid_exp_let_mod HU HX) as H; cbn in H; exact H.
Qed.

(** ** Representations *)

Inductive rep : ctx -> typ -> nat -> bool -> Prop :=
| rep_leaf : forall Γ X i b,
    ⊨ Γ -> Γ ⊨ X : Typeω@i -> (b = true -> X = a_True) -> rep Γ X 0 b
| rep_nest : forall Γ τ D Ψ Δp X m b,
    gsub Γ τ D -> tele_ass Δp -> lets_only Ψ -> ⊨ Ψ ++ Δp ++ D ->
    rep (Ψ ++ Δp ++ D) X m b ->
    rep Γ (ctx_pi (Ψ ++ Δp) X)[τ] (List.length Δp + m) b.

Lemma rep_ctx : forall Γ A n b, rep Γ A n b -> ⊨ Γ.
Proof. intros * H; destruct H; [ assumption | exact (proj1 (gsub_sem ltac:(eassumption))) ]. Qed.

Lemma rep_valid : forall Γ A n b, rep Γ A n b -> exists i, Γ ⊨ A : Typeω@i.
Proof.
  induction 1 as [Γ X i b HΓ HX Hb | Γ τ D Ψ Δp X m b Hg HΔ HΨ HC Hr (i & IH)]; [ eauto |].
  rewrite app_assoc in IH, HC.
  destruct (valid_ctx_pi _ _ _ _ HC IH) as [j Hj].
  pose proof (rel_exp_under_ctx_gsub Hg Hj) as H; cbn in H; eauto.
Qed.

Lemma rep_sub : forall D A n b, rep D A n b -> forall Γ σ, gsub Γ σ D -> rep Γ A[σ] n b.
Proof.
  intros * H Γ σ Hg.
  pose proof (gsub_props Hg) as [Hσ Hl].
  pose proof (gsub_sem Hg) as [HΓ HD].
  destruct H as [D X i b HD' HX Hb | D τ D0 Ψ Δp X m b Hg0 HΔ HΨ HC Hr].
  - replace 0 with (List.length (@nil centry) + 0) by reflexivity.
    replace X[σ] with (ctx_pi (nil ++ nil) X)[σ] by reflexivity.
    eapply rep_nest; [ exact Hg | constructor | constructor | exact HD |].
    eapply rep_leaf; eassumption.
  - rewrite exp_sub_sub.
    eapply rep_nest; [ eapply gsub_comp; eassumption | eassumption .. ].
Qed.

(** ** Local Definitions and Modules before a Type *)

Lemma let_step_def : forall {Γ τ G D1 k M1 X} {i : nat},
    gsub Γ τ G -> G ⊨ D1 : Typeω@k -> G ⊨ M1 : D1 -> G ▸ D1 ≔ M1 ⊨ X : Typeω@i ->
    Γ ⊨ (ℓ D1 ≔ M1 in X)[τ] ≈ X[τ ,, M1[τ]] : Typeω@i /\
    (forall B C, pi_view (ℓ D1 ≔ M1 in X)[τ] = Some (B, C) -> pi_view X[τ ,, M1[τ]] = Some (B, C)).
Proof.
  intros * Hg HD HM HX; split.
  - pose proof (rel_exp_let_zeta (oA := Some D1) HD HM HX) as H.
    pose proof (rel_exp_under_ctx_gsub Hg H) as H'.
    rewrite !exp_sub_extend_sub in H'.
    change (Typeω@i[τ ,, M1[τ]]) with (Typeω@i : typ) in H'; exact H'.
  - intros B C Hp; cbn in Hp.
    destruct (pi_view X[q τ]) as [[B' C'] |] eqn:E; [| discriminate ].
    injection Hp as <- <-.
    rewrite <- exp_sub_q_extend, (pi_view_sub _ _ _ _ E); reflexivity.
Qed.

Lemma let_step_mod : forall {Γ τ G U X} {i : nat},
    gsub Γ τ G -> G ⊨ᵘ U ≈ U -> G ▹ₘ U ⊨ X : Typeω@i ->
    Γ ⊨ (ℓₘ U in X)[τ] ≈ X[τ ,,ₘ me_lit U[τ]ᵘ] : Typeω@i /\
    (forall B C, pi_view (ℓₘ U in X)[τ] = Some (B, C) -> pi_view X[τ ,,ₘ me_lit U[τ]ᵘ] = Some (B, C)).
Proof.
  intros * Hg HU HX; split.
  - pose proof (rel_exp_let_mod_zeta HU HX) as H.
    pose proof (rel_exp_under_ctx_gsub Hg H) as H'.
    rewrite !exp_sub_extend_mod_sub in H'.
    change (Typeω@i[τ ,,ₘ (me_lit U)[τ]ᵐ]) with (Typeω@i : typ) in H'; exact H'.
  - intros B C Hp; cbn in Hp.
    destruct (pi_view X[q τ]) as [[B' C'] |] eqn:E; [| discriminate ].
    injection Hp as <- <-.
    rewrite <- exp_sub_q_extend_mod, (pi_view_sub _ _ _ _ E); reflexivity.
Qed.

Lemma lets_peel : forall Ψ D X i Γ τ,
    lets_only Ψ -> ⊨ Ψ ++ D -> Ψ ++ D ⊨ X : Typeω@i -> gsub Γ τ D ->
    exists τ' j, gsub Γ τ' (Ψ ++ D) /\ Γ ⊨ (ctx_pi Ψ X)[τ] ≈ X[τ'] : Typeω@j /\
      (forall B C, pi_view (ctx_pi Ψ X)[τ] = Some (B, C) -> pi_view X[τ'] = Some (B, C)).
Proof.
  induction Ψ as [| e Ψ IH]; intros * HL HC HX Hg; cbn [ctx_pi app] in *.
  - exists τ, i; split; [ exact Hg |]; split; [ exact (rel_exp_under_ctx_gsub Hg HX) | auto ].
  - inversion HL as [| ? ? He HL']; subst.
    pose proof (sem_ctx_tail HC) as HC'.
    destruct e as [B0 | B0 M0 | U0]; [ exfalso; exact (He _ eq_refl) | |].
    + destruct (sem_ctx_def_inv HC) as [[k HB0] HM0].
      pose proof (valid_exp_let (oA := Some B0) HB0 HM0 HX) as HX'.
      destruct (IH _ _ _ _ _ HL' HC' HX' Hg) as (τ1 & j1 & Hg1 & HJ1 & Hp1).
      destruct (let_step_def Hg1 HB0 HM0 HX) as [HJ2 Hp2].
      exists (τ1 ,, M0[τ1]), (max j1 i); split; [ eapply gsub_def; eassumption |]; split.
      * eapply rel_exp_under_ctx_trans; eapply rel_exp_cumu_ge; [| exact HJ1 | | exact HJ2 ]; lia.
      * intros; apply Hp2, Hp1; assumption.
    + pose proof (sem_ctx_mod_inv HC) as HU0.
      pose proof (valid_exp_let_mod HU0 HX) as HX'.
      destruct (IH _ _ _ _ _ HL' HC' HX' Hg) as (τ1 & j1 & Hg1 & HJ1 & Hp1).
      destruct (let_step_mod Hg1 HU0 HX) as [HJ2 Hp2].
      exists (τ1 ,,ₘ me_lit U0[τ1]ᵘ), (max j1 i); split; [ eapply gsub_mod; eassumption |]; split.
      * eapply rel_exp_under_ctx_trans; eapply rel_exp_cumu_ge; [| exact HJ1 | | exact HJ2 ]; lia.
      * intros; apply Hp2, Hp1; assumption.
Qed.

(** ** Instantiating the Next Parameter *)

Lemma tele_ass_app_inv : forall Δ1 Δ2, tele_ass (Δ1 ++ Δ2) -> tele_ass Δ1 /\ tele_ass Δ2.
Proof. intros * H; apply Forall_app in H; exact H. Qed.

Lemma rep_shift : forall D A k b, rep D A k b -> forall n, k = S n ->
    forall Γ σ, gsub Γ σ D ->
    forall B C, pi_view A[σ] = Some (B, C) ->
    (exists i, Γ ⊨ B : Typeω@i) /\ (exists i, Γ ▹ B ⊨ C : Typeω@i) /\
    (exists i, Γ ⊨ A[σ] ≈ Π B C : Typeω@i) /\ (forall N, Γ ⊨ N : B -> rep Γ C[Id,,N] n b).
Proof.
  induction 1 as [D X i b HD HX Hb | D τ D0 Ψ Δp X m b Hg0 HΔ HΨ HC Hr IH];
    intros n Hk Γ σ Hg B C Hp; [ discriminate |].
  pose proof (gsub_props Hg) as [Hσ Hl].
  pose proof (gsub_sem Hg) as [HΓ _].
  assert (Hg2 : gsub Γ (τ ⨟ σ) D0) by (eapply gsub_comp; eassumption).
  rewrite exp_sub_sub in Hp |- *.
  destruct Δp as [| e0 Δ0] eqn:EΔ.
  - (* only local definitions and modules before the type: look through them *)
    cbn [List.length plus] in Hk; subst m.
    rewrite app_nil_r in Hp |- *; cbn [app] in HC, Hr.
    destruct (rep_valid _ _ _ _ Hr) as [i Hi].
    destruct (lets_peel _ _ _ _ _ _ HΨ HC Hi Hg2) as (τ' & j & Hg' & HJ & Hpt).
    destruct (IH n eq_refl _ _ Hg' _ _ (Hpt _ _ Hp)) as (HB & HCv & (l & HJ') & HN).
    split; [ exact HB |]; split; [ exact HCv |]; split; [| exact HN ].
    exists (max j l); eapply rel_exp_under_ctx_trans; eapply rel_exp_cumu_ge; [| exact HJ | | exact HJ' ]; lia.
  - (* the outermost parameter *)
    assert (Hne : e0 :: Δ0 <> nil) by discriminate.
    destruct (exists_last Hne) as (l & e & El).
    rewrite <- EΔ in *; rewrite El in *; clear El EΔ e0 Δ0 Hne.
    destruct (tele_ass_app_inv _ _ HΔ) as [Hl0 He].
    inversion He as [| ? ? [B0 ->] _]; subst.
    assert (EC : Ψ ++ (l ++ [ce_ass B0]) ++ D0 = (Ψ ++ l) ++ ce_ass B0 :: D0)
      by (rewrite <- !app_assoc; reflexivity).
    rewrite EC in HC, Hr.
    assert (EA : (ctx_pi (Ψ ++ l ++ [ce_ass B0]) X)[τ ⨟ σ] = Π B0[τ ⨟ σ] (ctx_pi (Ψ ++ l) X)[q (τ ⨟ σ)])
      by (rewrite app_assoc, ctx_pi_app; reflexivity).
    rewrite EA in Hp |- *; cbn in Hp; injection Hp as <- <-.
    destruct (sem_ctx_ass_inv (sem_ctx_app_r _ _ HC)) as [k HB0].
    destruct (rep_valid _ _ _ _ Hr) as [i Hi].
    destruct (valid_ctx_pi _ _ _ _ HC Hi) as [j Hj].
    pose proof (rel_exp_under_ctx_gsub Hg2 HB0) as HB1; cbn in HB1.
    pose proof (rel_exp_under_ctx_gsub (gsub_q _ _ _ _ _ Hg2 HB0) Hj) as HC1; cbn in HC1.
    split; [ eauto |]; split; [ eauto |]; split.
    + exists (max k j); apply rel_exp_pi_cong; eapply rel_exp_cumu_ge; [| exact HB1 | | exact HC1 ]; lia.
    + intros N HN.
      rewrite exp_sub_q_extend.
      replace n with (List.length l + m) by (rewrite length_app in Hk; cbn in Hk; lia).
      eapply rep_nest; [ eapply gsub_ass; eassumption | exact Hl0 | exact HΨ | |].
      * rewrite app_assoc; exact HC.
      * rewrite app_assoc; exact Hr.
Qed.

Lemma pi_view_lets_none : forall Ψ X, lets_only Ψ -> (forall σ, pi_view X[σ] = None) ->
    forall σ, pi_view (ctx_pi Ψ X)[σ] = None.
Proof.
  induction Ψ as [| e Ψ IH]; intros X HL HX σ; cbn [ctx_pi]; [ apply HX |].
  inversion HL as [| ? ? He HL']; subst.
  destruct e as [B0 | B0 M0 | U0]; [ exfalso; exact (He _ eq_refl) | |];
    (apply IH; [ exact HL' |]; intros σ'; cbn; rewrite HX; reflexivity).
Qed.

(** An arity with no parameter left is no [Π]. *)
Lemma rep_top_none : forall D A k b, rep D A k b -> k = 0 -> b = true -> forall σ, pi_view A[σ] = None.
Proof.
  induction 1 as [D X i b HD HX Hb | D τ D0 Ψ Δp X m b Hg0 HΔ HΨ HC Hr IH]; intros Hk Hb' σ.
  - rewrite (Hb Hb'); reflexivity.
  - destruct Δp; [| discriminate ]; cbn in Hk; subst m.
    rewrite exp_sub_sub, app_nil_r.
    apply pi_view_lets_none; [ exact HΨ |]; intros; apply IH; auto.
Qed.

Lemma rep_top_zero_gen : forall D A k b, rep D A k b -> k = 0 -> b = true ->
    forall Γ σ, gsub Γ σ D -> exists i, Γ ⊨ A[σ] ≈ ⊤ : Typeω@i.
Proof.
  induction 1 as [D X i b HD HX Hb | D τ D0 Ψ Δp X m b Hg0 HΔ HΨ HC Hr IH]; intros Hk Hb' Γ σ Hg.
  - rewrite (Hb Hb'); cbn.
    exists 0; apply valid_exp_True; exact (proj1 (gsub_sem Hg)).
  - destruct Δp; [| discriminate ]; cbn in Hk; subst m.
    pose proof (gsub_props Hg) as [Hσ Hl].
    pose proof (gsub_sem Hg) as [HΓ _].
    assert (Hg2 : gsub Γ (τ ⨟ σ) D0) by (eapply gsub_comp; eassumption).
    rewrite exp_sub_sub, app_nil_r; cbn [app] in HC, Hr.
    destruct (rep_valid _ _ _ _ Hr) as [i Hi].
    destruct (lets_peel _ _ _ _ _ _ HΨ HC Hi Hg2) as (τ' & j & Hg' & HJ & _).
    destruct (IH eq_refl Hb' _ _ Hg') as [l HJ'].
    exists (max j l); eapply rel_exp_under_ctx_trans; eapply rel_exp_cumu_ge; [| exact HJ | | exact HJ' ]; lia.
Qed.

Corollary rep_top_zero : forall Γ A, rep Γ A 0 true -> exists i, Γ ⊨ A ≈ ⊤ : Typeω@i.
Proof.
  intros * H.
  pose proof (rep_top_zero_gen _ _ _ _ H eq_refl eq_refl _ _ (gsub_id _ (rep_ctx _ _ _ _ H))) as HA.
  rewrite exp_sub_id in HA; exact HA.
Qed.


End Fixed_GCtx.
