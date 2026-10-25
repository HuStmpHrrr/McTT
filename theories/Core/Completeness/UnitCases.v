(** * Units: Slots, Module Expressions and Module Lets

    The context PER of an extension by a slot ties the slot's value to the
    value of its unit, as a literal, over the tail ([env_ext_mod]).  This
    file builds such PERs, the semantic substitutions into slots, the
    symmetry and transitivity of the module judgment, the extensions of a
    context, and the module [let]s.  The closures of related units are
    related in [Modules/Body.v]. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.
#[local] Generalizable All Variables.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Context PERs of Extended Contexts *)

Lemma per_ctx_env_app_tail : forall Ψ Ψ' Γ Γ' R,
    List.length Ψ = List.length Ψ' ->
    EF Ψ ++ Γ ≈ Ψ' ++ Γ' ∈ per_ctx_env ↘ R ->
    exists RΓ, EF Γ ≈ Γ' ∈ per_ctx_env ↘ RΓ.
Proof.
  induction Ψ as [| e Ψ IH]; intros [| e' Ψ'] * Hl H; cbn in *; try discriminate; eauto.
  inversion H; subst; eauto.
Qed.

Lemma rel_ctx_wf_app_r : forall Ψ Γ, ⊨ Ψ ++ Γ -> ⊨ Γ.
Proof. induction Ψ; intros * H; cbn in *; [ exact H | apply IHΨ; eapply rel_ctx_wf_tail; exact H ]. Qed.

(** ** Slots *)

(** The relation of an extension by a slot over the tail relation [R]: the
    heads are tied to the values of both units over their own tails. *)
Record env_ext_mod (U U' : gunit) (R : relation env) (ρ ρ' : env) : Prop := mk_env_ext_mod
  { env_ext_mod_tail : R ρ↯ ρ'↯
  ; env_ext_mod_left_l : tie_mod (env_mod ρ 0) (me_lit U) ρ↯
  ; env_ext_mod_left_r : tie_mod (env_mod ρ 0) (me_lit U') ρ↯
  ; env_ext_mod_right_l : tie_mod (env_mod ρ' 0) (me_lit U) ρ'↯
  ; env_ext_mod_right_r : tie_mod (env_mod ρ' 0) (me_lit U') ρ'↯ }.

(** The same relation, as the slot clause of [per_ctx_env] states it. *)
Lemma env_ext_mod_inline : forall U U' R,
    env_ext_mod U U' R <~> fun ρ ρ' =>
      R ρ↯ ρ'↯ /\
      tie_mod (env_mod ρ 0) (me_lit U) ρ↯ /\
      tie_mod (env_mod ρ 0) (me_lit U') ρ↯ /\
      tie_mod (env_mod ρ' 0) (me_lit U) ρ'↯ /\
      tie_mod (env_mod ρ' 0) (me_lit U') ρ'↯.
Proof.
  intros U U' R ρ ρ'; split; [ intros []; repeat split; assumption | intros (? & ? & ? & ? & ?); constructor; assumption ].
Qed.

(** The relation of an extension by a slot, with its tail relation fixed. *)
Lemma per_ctx_env_cons_mod_inversion : forall {Γ Γ' U U' RΓ R},
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ RΓ ->
    EF Γ ▹ₘ U ≈ Γ' ▹ₘ U' ∈ per_ctx_env ↘ R ->
    (forall ρ ρ', RΓ ρ ρ' -> rel_mexp (me_lit U) ρ (me_lit U') ρ') /\ (R <~> env_ext_mod U U' RΓ).
Proof.
  intros * HΓ H; inversion H; subst.
  match goal with Ht : per_ctx_env ?T Γ Γ' |- _ =>
    assert (HT : T <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption) end.
  split.
  - intros ρ ρ' Hρ; apply H6, HT, Hρ.
  - intros ρ ρ'; split; intros Hρ;
      [ apply H7 in Hρ as (Ht & ? & ? & ? & ?); constructor; [ apply HT; assumption | assumption .. ]
      | apply H7; destruct Hρ as [Ht ? ? ? ?]; repeat split; [ apply HT; assumption | assumption .. ] ].
Qed.

(** A valid module expression, at environments a context PER relates. *)
Lemma rel_modexp_at : forall Γ Γ' H H' R,
    Γ ⊨ᵐ H ≈ H' -> EF Γ ≈ Γ' ∈ per_ctx_env ↘ R ->
    forall ρ ρ', R ρ ρ' ->
      exists h h', ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h /\ ⟦ H' ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ' ↘ h' /\ per_dmod h h'.
Proof.
  intros * [RE HΓE HEg] HR ρ ρ' Hρ.
  assert (Ex : R <~> RE) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (HEg _ _ HΓE _ _ (rel_sub_id (ex_intro _ _ HΓE)) _ _ _ _ (proj1 (Ex _ _) Hρ) (eval_sub_id _) (eval_sub_id _))
    as [h1 h2 h3 h4 _ Hh2 Hh3 _ [_ [Hh _]]].
  exists h2, h3; repeat split; assumption.
Qed.

Corollary rel_mexp_at : forall Γ Γ' H H' R,
    Γ ⊨ᵐ H ≈ H' -> EF Γ ≈ Γ' ∈ per_ctx_env ↘ R -> forall ρ ρ', R ρ ρ' -> rel_mexp H ρ H' ρ'.
Proof.
  intros * HH HR ρ ρ' Hρ; destruct (rel_modexp_at _ _ _ _ _ HH HR _ _ Hρ) as (h & h' & ? & ? & ?).
  exists h h'; assumption.
Qed.

(** The values of a valid literal over related tails. *)
Lemma unit_chain_at : forall {Γ U U' R},
    Γ ⊨ᵐ me_lit U ≈ me_lit U' ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    forall ρ ρ', R ρ ρ' -> rel_mexp (me_lit U) ρ (me_lit U') ρ'.
Proof. intros * HU HΓ ρ ρ' Hρ; exact (rel_mexp_at _ _ _ _ _ HU HΓ _ _ Hρ). Qed.

Lemma per_ctx_env_of_mod : forall {Γ U U' R},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U' ->
    EF Γ ▹ₘ U ≈ Γ ▹ₘ U' ∈ per_ctx_env ↘ env_ext_mod U U' R.
Proof.
  intros * HΓ HU.
  eapply per_ctx_env_cons_mod; [ exact HΓ | eapply per_env_PER; exact HΓ | | apply env_ext_mod_inline ].
  intros; eapply unit_chain_at; eassumption.
Qed.

(** The values of a valid literal moved along a substitution, against those
    of the literal over the substituted tails. *)
Lemma unit_sub_chain : forall {Γ' Γ σ σ' U U' R'},
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' ->
    Γ' ⊨ˢ σ ≈ σ' : Γ ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U' ->
    forall ρ ρ' ρσ ρ'σ', R' ρ ρ' -> ⟦ σ ⟧s ρ ↘ ρσ -> ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
      rel_mexp (me_lit U[σ]ᵘ) ρ (me_lit U) ρσ /\ rel_mexp (me_lit U) ρσ (me_lit U') ρ'σ' /\
      rel_mexp (me_lit U') ρ'σ' (me_lit U'[σ']ᵘ) ρ'.
Proof.
  intros * HΓ' Hσ [R HΓ HU] * Hρ Hev Hev'.
  destruct (HU _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [h1 h2 h3 h4 H1 H2 H3 H4 (C12 & C23 & C34)].
  cbn [modexp_sub] in H1, H4.
  split; [| split ]; econstructor; eassumption.
Qed.

Lemma per_ctx_env_of_mod_sub : forall {Γ' Γ σ σ' U R'},
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' ->
    Γ' ⊨ˢ σ ≈ σ' : Γ ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    EF Γ' ▹ₘ U[σ]ᵘ ≈ Γ' ▹ₘ U[σ]ᵘ ∈ per_ctx_env ↘ env_ext_mod U[σ]ᵘ U[σ]ᵘ R'.
Proof.
  intros * HΓ' Hσ HU.
  eapply per_ctx_env_cons_mod; [ exact HΓ' | eapply per_env_PER; exact HΓ' | | apply env_ext_mod_inline ].
  intros ρ ρ' Hρ.
  pose proof (rel_sub_under_ctx_refl_left Hσ) as Hσσ.
  destruct (rel_sub_under_ctx_simple Hσσ) as [R1 [HΓ1 [RΓ [HΓ0 Hs]]]].
  assert (E : R' <~> R1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E _ _) Hρ)) as (ρσ & ρ'σ & Hev & Hev' & _).
  destruct (unit_sub_chain HΓ' Hσσ HU _ _ _ _ Hρ Hev Hev') as (C1 & C2 & C3).
  eapply rel_mexp_trans; [ exact C1 | eapply rel_mexp_trans; [ exact C2 | exact C3 ] ].
Qed.

(** [q τ] at an environment of an extension: the head is kept, and the
    tail is related to the value of [τ] at the environment's tail. *)
Lemma rel_sub_q_entry : forall {Γ'' Δ τ τ' e Re RΔ},
    EF (e :: Γ'') ≈ (e :: Γ'') ∈ per_ctx_env ↘ Re ->
    EF Δ ≈ Δ ∈ per_ctx_env ↘ RΔ ->
    Γ'' ⊨ˢ τ ≈ τ' : Δ ->
    forall x u, Re x x -> ⟦ τ ⟧s x↯ ↘ u ->
      exists t, ⟦ q τ ⟧s x ↘ env_entry x 0 :: t /\ RΔ t u.
Proof.
  intros * He HΔ [R1 H1 R2 H2 Hσ] x u Hx Hu.
  pose proof (rel_wk_shift H1 He) as Hsh.
  destruct (Hσ _ _ He _ Hsh _ _ Hx) as [t v v' t' Ht Hv Hv' Ht' Hc].
  rewrite eval_wk_shift in Hv, Hv'.
  assert (Heq : env_eq v u) by (eapply functional_eval_sub; eassumption).
  exists t; split; [ apply eval_sub_q; exact Ht |].
  assert (E : R2 <~> RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  apply E; rewrite <- Heq; destruct Hc as [Hc _]; exact Hc.
Qed.

(** A head tied to the value of [U[σ]] over a tail is tied to the value of
    [U] over any environment related to [σ] at the tail. *)
Lemma tie_mod_sub : forall {Γ' Γ σ U R' R},
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' -> EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Γ' ⊨ˢ σ ≈ σ : Γ -> Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    forall m ρ ρσ t, R' ρ ρ -> ⟦ σ ⟧s ρ ↘ ρσ -> R ρσ t ->
      tie_mod m (me_lit U[σ]ᵘ) ρ -> tie_mod m (me_lit U) t.
Proof.
  intros * HΓ' HΓ Hσ HU * Hρ Hev Ht Hm.
  destruct (unit_sub_chain HΓ' Hσ HU _ _ _ _ Hρ Hev Hev) as (C1 & _).
  eapply tie_mod_move; [ eapply tie_mod_move; [ exact Hm | exact C1 ] |].
  exact (unit_chain_at HU HΓ _ _ Ht).
Qed.

(** [q σ] into a slot.  The four tails come from [σ] at the Kripke stage, as
    for an assumption; the head is the same module value on each side, tied
    to the value of [U[σ]] over the stage's tails, which the validity of [U]
    relates to the value of [U] over the tails of [q σ]. *)
Lemma rel_sub_under_ctx_q_mod : forall {Γ' Γ σ σ' U},
    Γ' ⊨ˢ σ ≈ σ' : Γ ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    Γ' ▹ₘ U[σ]ᵘ ⊨ˢ q σ ≈ q σ' : Γ ▹ₘ U.
Proof.
  intros * Hσj HU.
  pose proof Hσj as [R' HΓ' R HΓ Hσ].
  pose proof (per_ctx_env_of_mod_sub HΓ' Hσj HU) as HΓ'U.
  pose proof (per_ctx_env_of_mod HΓ HU) as HΓU.
  pose proof (rel_wk_shift HΓ' HΓ'U) as Hshift.
  pose proof (rel_sub_under_ctx_wk Hσj (rel_wk_under_ctx_intro HΓ'U HΓ' Hshift)) as Hσwkj.
  pose proof Hσwkj as [R'U HΓ'U' R2 HΓ2 Hσwk].
  assert (E1 : R'U <~> env_ext_mod U[σ]ᵘ U[σ]ᵘ R') by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E2 : R2 <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (HPR : PER R) by (eapply per_env_PER; exact HΓ).
  assert (HPR' : PER R') by (eapply per_env_PER; exact HΓ').
  refine (mk_rel_sub_under_ctx _ _ _ _ (env_ext_mod U[σ]ᵘ U[σ]ᵘ R') HΓ'U (env_ext_mod U U R) HΓU _).
  intros Γ'' R'' HΓ'' ψ Hψ ρ ρ' Hρ.
  destruct (Hψ _ _ Hρ) as [Htail Tρ _ Tρ' _].
  destruct (Hσwk _ _ HΓ'' _ (proj2 (rel_wk_morphism ψ _ _ (reflexivity R'') _ _ E1) Hψ) _ _ Hρ)
    as [x1 y1 y4 x4 Hx1 Hy1 Hy4 Hx4 Htails].
  apply (rel_chain_mono _ _ (fun a b H => proj1 (E2 a b) H)) in Htails.
  destruct (Hσ _ _ HΓ'U _ Hshift _ _ (Hψ _ _ Hρ)) as [z1 y2 y3 z4 Hz1 Hy2 Hy3 Hz4 Hbtails].
  rewrite ?eval_wk_shift in *.
  assert (Heq1 : env_eq y1 z1) by (eapply functional_eval_sub; eassumption).
  assert (Heq4 : env_eq y4 z4) by (eapply functional_eval_sub; eassumption).
  assert (Hy12 : R y1 y2) by (rewrite Heq1; pairwise).
  assert (Hy43 : R y4 y3) by (rewrite Heq4; pairwise).
  assert (Htl : R' (⟪ψ⟫ ρ)↯ (⟪ψ⟫ ρ)↯) by (etransitivity; [ exact Htail | symmetry; exact Htail ]).
  assert (Htr : R' (⟪ψ⟫ ρ')↯ (⟪ψ⟫ ρ')↯) by (etransitivity; [ symmetry; exact Htail | exact Htail ]).
  pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
  destruct (rel_sub_under_ctx_simple Hσσ) as [R1 [HΓ1 [R3 [HΓ3 Hs]]]].
  assert (E3 : R' <~> R1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E3 _ _) Htr)) as (w & _ & Hw & _ & _).
  assert (Hw3 : R w y3) by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  rewrite (eval_wk_app_mod ψ) in Tρ, Tρ'.
  assert (Hm : forall t, R y2 t -> tie_mod (env_mod ρ (ψ 0)) (me_lit U) t)
    by (intros t Ht; exact (tie_mod_sub HΓ' HΓ Hσσ HU _ _ _ _ Htl Hy2 Ht Tρ)).
  assert (Hm' : forall t, R w t -> tie_mod (env_mod ρ' (ψ 0)) (me_lit U) t)
    by (intros t Ht; exact (tie_mod_sub HΓ' HΓ Hσσ HU _ _ _ _ Htr Hw Ht Tρ')).
  assert (Hl : forall t, In t (x1 :: y1 :: nil) -> R y2 t)
    by (intros t Ht; symmetry; etransitivity; [| exact Hy12 ]; eapply (rel_chain_pairwise R); [ exact Htails | | solve_in ];
        destruct Ht as [<- | [<- | []]]; solve_in).
  assert (Hr : forall t, In t (y4 :: x4 :: nil) -> R w t).
  { intros t Ht; symmetry; etransitivity; [| symmetry; exact Hw3 ]; etransitivity; [| exact Hy43 ].
    eapply (rel_chain_pairwise R); [ exact Htails | | solve_in ].
    destruct Ht as [<- | [<- | []]]; solve_in. }
  apply (mk_rel_sub (env_entry ρ (ψ 0) :: x1) (env_entry ρ (ψ 0) :: y1)
                    (env_entry ρ' (ψ 0) :: y4) (env_entry ρ' (ψ 0) :: x4));
    [ apply eval_sub_wk_q; eassumption
    | rewrite <- (eval_wk_app_entry ψ); apply eval_sub_q; eassumption
    | rewrite <- (eval_wk_app_entry ψ); apply eval_sub_q; eassumption
    | apply eval_sub_wk_q; eassumption
    | ].
  cbn [rel_chain]; cbn [drop_env tl].
  unfold env_mod in Hm, Hm' |- *; cbn [env_entry hd] in Hm, Hm' |- *.
  repeat split.
  all: try solve [ eapply (rel_chain_pairwise R); [ exact Htails | solve_in | solve_in ]
          | apply Hm, Hl; solve_in | apply Hm', Hr; solve_in ].
Qed.

(** ** Module Expressions: Symmetry and Transitivity *)

Lemma rel_modexp_under_ctx_sym : forall {Γ H H'},
    Γ ⊨ᵐ H ≈ H' -> Γ ⊨ᵐ H' ≈ H.
Proof.
  intros * [R HΓ HH]; refine (mk_rel_modexp_under_ctx _ _ _ R HΓ _).
  intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HP : PER R') by (eapply per_env_PER; exact HΓ').
  destruct (HH _ _ HΓ' _ _ (rel_sub_under_ctx_sym Hσ) _ _ _ _ (symmetry Hρ) Hev' Hev) as [? ? ? ? ? ? ? ? Hc].
  econstructor; try eassumption.
  assert (PER per_dmod) by typeclasses eauto.
  now apply rel_chain_4_sym.
Qed.

End Fixed_GCtx.

Lemma sem_me_sym :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H' ≈ H ).
Proof. intros * HH; sem_intro; first [ assumption | exact (rel_modexp_under_ctx_sym HH) ]. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma rel_modexp_under_ctx_trans : forall {Γ H1 H2 H3},
    Γ ⊨ᵐ H1 ≈ H2 -> Γ ⊨ᵐ H2 ≈ H3 -> Γ ⊨ᵐ H1 ≈ H3.
Proof.
  intros * [R HΓ H12] [R2 HΓ2 H23].
  refine (mk_rel_modexp_under_ctx _ _ _ R HΓ _).
  intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HP : PER R') by (eapply per_env_PER; exact HΓ').
  assert (Hρ' : R' ρ' ρ') by (etransitivity; [ symmetry |]; eassumption).
  destruct (H12 _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [v1 v2 v3 v4 ? ? ? ? Hc1].
  destruct (H23 _ _ HΓ' _ _ (rel_sub_under_ctx_refl_right Hσ) _ _ _ _ Hρ' Hev' Hev')
    as [w1 w2 w3 w4 ? ? ? ? Hc2].
  repeat match goal with
         | H : eval_modexp _ _ ?E ?r ?a, H' : eval_modexp _ _ ?E ?r ?b |- _ =>
             pose proof (functional_eval_modexp _ _ _ _ H H'); subst; clear H'
         end.
  econstructor; try eassumption.
  assert (PER per_dmod) by typeclasses eauto.
  match type of Hc1 with rel_chain _ (_ :: _ :: ?c :: _) => merge_rel_chain Hc1 Hc2 c end.
Qed.

End Fixed_GCtx.

Lemma sem_me_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H' ≈ H'' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H'' ).
Proof. intros * H1 H2; sem_intro; first [ assumption | exact (rel_modexp_under_ctx_trans H1 H2) ]. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Corollary rel_modexp_refl_left : forall {Γ H H'}, Γ ⊨ᵐ H ≈ H' -> Γ ⊨ᵐ H ≈ H.
Proof. intros * HH; eapply rel_modexp_under_ctx_trans; [ exact HH | apply rel_modexp_under_ctx_sym, HH ]. Qed.

Corollary rel_modexp_refl_right : forall {Γ H H'}, Γ ⊨ᵐ H ≈ H' -> Γ ⊨ᵐ H' ≈ H'.
Proof. intros * HH; eapply rel_modexp_under_ctx_trans; [ apply rel_modexp_under_ctx_sym, HH | exact HH ]. Qed.

(** ** Extensions *)

(** Two definition entries with related types and bodies, over related
    contexts. *)
Lemma per_ctx_env_extend_def_cross : forall {Δ Δ' A A' M M'} {i : nat} {R},
    EF Δ ≈ Δ' ∈ per_ctx_env ↘ R ->
    Δ ⊨ A ≈ A' : Typeω@i ->
    Δ ⊨ M ≈ M' : A ->
    exists R', EF Δ ▸ A ≔ M ≈ Δ' ▸ A' ≔ M' ∈ per_ctx_env ↘ R'.
Proof.
  intros * HR HA HM.
  pose proof (rel_exp_of_typ_inversion_simple HA) as [RΔ [HΔ HAs]].
  assert (E : R <~> RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  pose proof (rel_exp_of_typ_inversion_simple_at HΔ (rel_exp_under_ctx_refl_left HA)) as HAl.
  pose proof (rel_exp_under_ctx_simple_at HΔ HM) as HMs.
  eexists.
  eapply (@per_ctx_env_cons_def _ Δ Δ' i A A' M M' R (fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ R) => per_head A A' ρ ρ')
            (fun ρ ρ' => exists (H : R ρ↯ ρ'↯),
               per_head A A' ρ↯ ρ'↯ (ρ 0) (ρ' 0) /\
               (exists m, ⟦ M ⟧ ρ↯ ↘ m /\ per_head A A' ρ↯ ρ'↯ m (ρ 0)) /\
               (exists m, ⟦ M' ⟧ ρ↯ ↘ m /\ per_head A A' ρ↯ ρ'↯ m (ρ 0)) /\
               (exists m', ⟦ M ⟧ ρ'↯ ↘ m' /\ per_head A A' ρ↯ ρ'↯ m' (ρ' 0)) /\
               (exists m', ⟦ M' ⟧ ρ'↯ ↘ m' /\ per_head A A' ρ↯ ρ'↯ m' (ρ' 0))));
    [ exact HR | eapply per_env_PER; exact HR | | | reflexivity ].
  - intros ρ ρ' Hρ.
    destruct (HAs _ _ (proj1 (E _ _) Hρ)) as [a [a' [Ha [Ha' [R1 HR1]]]]].
    econstructor; try eassumption.
    eapply per_univ_elem_resp_iff; [ eassumption |].
    eapply per_head_iff; eassumption.
  - intros ρ ρ' Hρ.
    destruct (HAs _ _ (proj1 (E _ _) Hρ)) as [a [a' [Ha [Ha' [R1 HR1]]]]].
    destruct (HAl _ _ (proj1 (E _ _) Hρ)) as [a0 [b [Ha0 [Hb [R2 HR2]]]]].
    destruct (HMs _ _ (proj1 (E _ _) Hρ)) as [m [m' [Hm [Hm' Hmm']]]].
    functional_eval_rewrite_clear.
    econstructor; try eassumption.
    apply (per_head_iff Ha Ha' HR1).
    apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR2 HR1).
    apply (per_head_iff Ha Hb HR2); exact Hmm'.
Qed.

(** Two related extensions by definitions with module parts: the term
    parts as definitions, the units as slots. *)
Lemma per_ctx_env_extend_dm_cross : forall {Δ Δ' A A' M M' U U'} {i : nat} {R},
    EF Δ ≈ Δ' ∈ per_ctx_env ↘ R ->
    Δ ⊨ A ≈ A' : Typeω@i ->
    Δ ⊨ M ≈ M' : A ->
    Δ ⊨ᵐ me_lit U ≈ me_lit U' ->
    exists R', EF Δ ▸ₘ A ≔ M ‖ U ≈ Δ' ▸ₘ A' ≔ M' ‖ U' ∈ per_ctx_env ↘ R'.
Proof.
  intros * HR HA HM HU.
  pose proof (rel_exp_of_typ_inversion_simple HA) as [RΔ [HΔ HAs]].
  assert (E : R <~> RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  pose proof (rel_exp_of_typ_inversion_simple_at HΔ (rel_exp_under_ctx_refl_left HA)) as HAl.
  pose proof (rel_exp_under_ctx_simple_at HΔ HM) as HMs.
  eexists.
  eapply (@per_ctx_env_cons_dm _ Δ Δ' i A A' M M' U U' R (fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ R) => per_head A A' ρ ρ')
            (per_ctx_env_dm_rel R (fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ R) => per_head A A' ρ ρ') M M' U U'));
    [ exact HR | eapply per_env_PER; exact HR | | | | reflexivity ].
  - intros ρ ρ' Hρ.
    destruct (HAs _ _ (proj1 (E _ _) Hρ)) as [a [a' [Ha [Ha' [R1 HR1]]]]].
    econstructor; try eassumption.
    eapply per_univ_elem_resp_iff; [ eassumption |].
    eapply per_head_iff; eassumption.
  - intros ρ ρ' Hρ.
    destruct (HAs _ _ (proj1 (E _ _) Hρ)) as [a [a' [Ha [Ha' [R1 HR1]]]]].
    destruct (HAl _ _ (proj1 (E _ _) Hρ)) as [a0 [b [Ha0 [Hb [R2 HR2]]]]].
    destruct (HMs _ _ (proj1 (E _ _) Hρ)) as [m [m' [Hm [Hm' Hmm']]]].
    functional_eval_rewrite_clear.
    econstructor; try eassumption.
    apply (per_head_iff Ha Ha' HR1).
    apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR2 HR1).
    apply (per_head_iff Ha Hb HR2); exact Hmm'.
  - intros ρ ρ' Hρ; eapply unit_chain_at; [ exact HU | exact HΔ | apply E, Hρ ].
Qed.

End Fixed_GCtx.

Lemma sem_ext_eq_nil :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ ⋅ ≈ ⋅ ).
Proof.
  intros * H; sem_intro; [ assumption | | assumption | assumption ].
  constructor; [ exact H | exact H | exact (rel_ctx_wf_per_ctx H) ].
Qed.

Lemma sem_ext_eq_ass :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ▹ A ≈ Ψ' ▹ A' ).
Proof.
  intros * HΨ HA HAA' HA'; sem_intro0.
  assert (Hr : Γ ⊨ˣ Ψ ▹ A ≈ Ψ' ▹ A').
  { destruct HΨ as [H1 H2 H3].
    constructor; cbn [app].
    - exact (rel_ctx_wf_extend H1 HA).
    - exact (rel_ctx_wf_extend H2 HA').
    - exact (per_ctx_extend H3 HAA'). }
  constructor; [ assumption | exact Hr | apply valid_ctx_ass | apply valid_ctx_ass ];
    first [ assumption | exact (rel_ext_under_ctx_left _ _ _ Hr) | exact (rel_ext_under_ctx_right _ _ _ Hr) ].
Qed.

Lemma sem_ext_eq_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ M' : A' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ▸ A ≔ M ≈ Ψ' ▸ A' ≔ M' ).
Proof.
  intros * HΨ HA HAA' HM HMM' HA' HM'; sem_intro0.
  assert (Hr : Γ ⊨ˣ Ψ ▸ A ≔ M ≈ Ψ' ▸ A' ≔ M').
  { destruct HΨ as [H1 H2 [R HR]].
    constructor; cbn [app].
    - exact (rel_ctx_wf_extend_def H1 HA HM).
    - exact (rel_ctx_wf_extend_def H2 HA' HM').
    - exact (per_ctx_env_extend_def_cross HR HAA' HMM'). }
  constructor; [ assumption | exact Hr | apply valid_ctx_def | apply valid_ctx_def ];
    first [ assumption | exact (rel_ext_under_ctx_left _ _ _ Hr) | exact (rel_ext_under_ctx_right _ _ _ Hr) ].
Qed.

Lemma sem_ext_eq_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ᵘ U' ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ▹ₘ U ≈ Ψ' ▹ₘ U' ).
Proof.
  intros * HΨ HUU' HU'U'; sem_intro0.
  assert (Hr : Γ ⊨ˣ Ψ ▹ₘ U ≈ Ψ' ▹ₘ U').
  { destruct HΨ as [H1 H2 [Rx HRx]]; destruct HUU' as [HU HsU _]; destruct HU'U' as [HU' HsU' _].
    destruct (rel_ctx_wf_per_ctx_env H1) as [R HR].
    destruct (rel_ctx_wf_per_ctx_env H2) as [R' HR'].
    pose proof (rel_modexp_refl_left HU) as HUU.
    constructor; cbn [app].
    - econstructor; [ exact H1 | exact (per_ctx_env_of_mod HR HUU) | exact HUU | exact HsU ].
    - econstructor; [ exact H2 | exact (per_ctx_env_of_mod HR' HU') | exact HU' | exact HsU' ].
    - assert (E : Rx <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
      exists (env_ext_mod U U' Rx).
      eapply per_ctx_env_cons_mod; [ exact HRx | eapply per_env_PER; exact HRx | | apply env_ext_mod_inline ].
      intros ρ ρ' Hρ; eapply unit_chain_at; [ exact HU | exact HR | apply E, Hρ ]. }
  constructor; [ assumption | exact Hr | apply valid_ctx_mod | apply valid_ctx_mod ];
    first [ assumption | exact (rel_ext_under_ctx_left _ _ _ Hr) | exact (rel_ext_under_ctx_right _ _ _ Hr) ].
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Module Lets *)

Lemma eval_sub_wk_extend_mod : forall σ H φ ρ ρσ h,
    ⟦ sb_wk σ φ ⟧s ρ ↘ ρσ ->
    ⟦ modexp_wk H φ ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h ->
    ⟦ sb_wk (σ ,,ₘ H) φ ⟧s ρ ↘ ρσ ↦ᵐ h.
Proof. intros * Hσ HH [| x]; [ exists h; split; [ reflexivity | assumption ] | apply Hσ ]. Qed.

(** A literal's value is the value of its closure. *)
Lemma eval_me_lit_iff : forall Δ D ρ h,
    ⟦ me_lit (gu_mk Δ D) ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h <-> ⟦ Δ ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ h.
Proof. intros; split; intros H; [ inversion H; subst; assumption | constructor; exact H ]. Qed.

(** A substitution extended into a slot by the literals of equivalent units. *)
Lemma rel_sub_under_ctx_extend_mod : forall {Γ' Γ σ σ' U U'},
    Γ' ⊨ˢ σ ≈ σ' : Γ ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U' ->
    Γ' ⊨ˢ σ ,,ₘ me_lit U[σ]ᵘ ≈ σ' ,,ₘ me_lit U'[σ']ᵘ : Γ ▹ₘ U.
Proof.
  intros * Hσj HU.
  pose proof Hσj as [R' HΓ' R HΓ Hσ].
  pose proof (rel_modexp_refl_left HU) as HUU.
  pose proof (rel_modexp_refl_right HU) as HU'U'.
  assert (HPd : PER per_dmod) by typeclasses eauto.
  refine (mk_rel_sub_under_ctx _ _ _ _ R' HΓ' (env_ext_mod U U R) (per_ctx_env_of_mod HΓ HUU) _).
  intros Γ'' R'' HΓ'' φ Hφ ρ ρ' Hρ.
  assert (HP'' : PER R'') by (eapply per_env_PER; exact HΓ'').
  assert (HPR : PER R) by (eapply per_env_PER; exact HΓ).
  pose proof (rel_sub_under_ctx_wk Hσj (rel_wk_under_ctx_intro HΓ'' HΓ' Hφ)) as Hσφ.
  destruct (Hσ _ _ HΓ'' _ Hφ _ _ Hρ) as [x1 x2 x3 x4 Hx1 Hx2 Hx3 Hx4 Hc].
  assert (Hρρ : R'' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  assert (Hρ'ρ' : R'' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
  pose proof (rel_wk_app _ _ _ Hφ _ _ Hρρ) as Hφρ.
  pose proof (rel_wk_app _ _ _ Hφ _ _ Hρ'ρ') as Hφρ'.
  destruct (unit_sub_chain HΓ'' (rel_sub_under_ctx_refl_left Hσφ) HUU _ _ _ _ Hρρ Hx1 Hx1) as (C1 & _).
  destruct (unit_sub_chain HΓ' (rel_sub_under_ctx_refl_left Hσj) HUU _ _ _ _ Hφρ Hx2 Hx2) as (C2 & _).
  destruct (unit_sub_chain HΓ' (rel_sub_under_ctx_refl_right Hσj) HU'U' _ _ _ _ Hφρ' Hx3 Hx3) as (_ & _ & C3).
  destruct (unit_sub_chain HΓ'' (rel_sub_under_ctx_refl_right Hσφ) HU'U' _ _ _ _ Hρ'ρ' Hx4 Hx4) as (_ & _ & C4).
  destruct C1 as [h1 g1 Hh1 Hg1 D1]; destruct C2 as [h2 g2 Hh2 Hg2 D2].
  destruct C3 as [g3 h3 Hg3 Hh3 D3]; destruct C4 as [g4 h4 Hg4 Hh4 D4].
  destruct Hc as (H12 & H23 & H34).
  (* the four heads, tied to both units over each tail *)
  assert (T : forall t h0, R t t -> per_dmod h0 h0 ->
            (exists g, ⟦ me_lit U ⟧ᵐ gc_deps ⍮ gc_stack ⍮ t ↘ g /\ per_dmod h0 g) ->
            tie_mod h0 (me_lit U) t /\ tie_mod h0 (me_lit U') t).
  { intros t h0 Ht Hh0 (g & Hg & Hhg); split; [ exists g; split; assumption |].
    exact (tie_mod_move _ _ _ _ _ (ex_intro _ g (conj Hg Hhg)) (unit_chain_at HU HΓ _ _ Ht)). }
  assert (T' : forall t h0, R t t -> per_dmod h0 h0 ->
            (exists g, ⟦ me_lit U' ⟧ᵐ gc_deps ⍮ gc_stack ⍮ t ↘ g /\ per_dmod h0 g) ->
            tie_mod h0 (me_lit U) t /\ tie_mod h0 (me_lit U') t).
  { intros t h0 Ht Hh0 (g & Hg & Hhg); split; [| exists g; split; assumption ].
    exact (tie_mod_move _ _ _ _ _ (ex_intro _ g (conj Hg Hhg)) (rel_mexp_sym _ _ _ _ (unit_chain_at HU HΓ _ _ Ht))). }
  assert (R11 : R x1 x1) by (etransitivity; [ exact H12 | symmetry; exact H12 ]).
  assert (R22 : R x2 x2) by (etransitivity; [ symmetry; exact H12 | exact H12 ]).
  assert (R33 : R x3 x3) by (etransitivity; [ exact H34 | symmetry; exact H34 ]).
  assert (R44 : R x4 x4) by (etransitivity; [ symmetry; exact H34 | exact H34 ]).
  apply (mk_rel_sub (x1 ↦ᵐ h1) (x2 ↦ᵐ h2) (x3 ↦ᵐ h3) (x4 ↦ᵐ h4)).
  - apply eval_sub_wk_extend_mod; [ exact Hx1 |]; cbn [modexp_wk]; rewrite gunit_wk_sub; exact Hh1.
  - apply eval_sub_extend_mod; [ exact Hx2 | exact Hh2 ].
  - apply eval_sub_extend_mod; [ exact Hx3 | exact Hh3 ].
  - apply eval_sub_wk_extend_mod; [ exact Hx4 |]; cbn [modexp_wk]; rewrite gunit_wk_sub; exact Hh4.
  - cbn [drop_env tl env_mod env_entry hd].
    destruct (T _ _ R11 ltac:(etransitivity; [ exact D1 | symmetry; exact D1 ]) (ex_intro _ g1 (conj Hg1 D1))) as [T1 T1'].
    destruct (T _ _ R22 ltac:(etransitivity; [ exact D2 | symmetry; exact D2 ]) (ex_intro _ g2 (conj Hg2 D2))) as [T2 T2'].
    destruct (T' _ _ R33 ltac:(etransitivity; [ symmetry; exact D3 | exact D3 ]) (ex_intro _ g3 (conj Hg3 (symmetry D3)))) as [T3 T3'].
    destruct (T' _ _ R44 ltac:(etransitivity; [ symmetry; exact D4 | exact D4 ]) (ex_intro _ g4 (conj Hg4 (symmetry D4)))) as [T4 T4'].
    repeat split; assumption.
Qed.

(** ** Definitions with a Module Part

    The canonical context PER of [Γ ▸ₘ A ≔ M ‖ U] is [per_env_extend_dm]: a
    definition entry's, with the head tied to the closure of [U] as a slot's
    is.  A substitution into it is one into the definition entry and one into
    the slot, read together: the head of the first, the module of the
    second. *)
Lemma per_ctx_env_of_dm : forall {Γ A} {i : nat} {M U R},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M : A ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    EF Γ ▸ₘ A ≔ M ‖ U ≈ Γ ▸ₘ A ≔ M ‖ U ∈ per_ctx_env ↘ per_env_extend_dm A M U R.
Proof.
  intros * HΓ HA HM HU.
  eapply per_ctx_env_extend_dm; [ exact HΓ | | | ].
  - exact (rel_exp_of_typ_inversion_simple_at HΓ HA).
  - exact (rel_exp_under_ctx_simple_at HΓ HM).
  - intros; eapply unit_chain_at; eassumption.
Qed.

(** An evaluation of a substitution extended by a definition with a module
    part, from those of the same substitution extended by its term and by its
    module expression. *)
Lemma eval_sub_dm_combine : forall σd σm σdm N H ρ ρd ρm,
    ⟦ σd ⟧s ρ ↘ ρd -> ⟦ σm ⟧s ρ ↘ ρm ->
    (forall x, σdm (S x) = σd (S x)) ->
    σd 0 = se_exp N -> σm 0 = se_mod H -> σdm 0 = se_dm N H ->
    ⟦ σdm ⟧s ρ ↘ de_dm (ρd 0) (env_mod ρm 0) :: ρd↯.
Proof.
  intros * Hed Hem Ht Hd Hm Hdm [| x].
  - specialize (Hed 0); specialize (Hem 0); rewrite Hd in Hed; rewrite Hm in Hem; rewrite Hdm.
    destruct Hed as (n & En & Hn); destruct Hem as (h & Eh & Hh).
    exists n, h; unfold env_var, env_mod; rewrite En, Eh; cbn [env_entry hd]; repeat split; assumption.
  - rewrite Ht; exact (Hed (S x)).
Qed.

(** Conversely, an evaluation of a substitution extended by a definition
    with a module part gives those of the substitution extended by its term
    and by its module expression, and the environment is the one their
    parts make. *)
Lemma eval_sub_dm_split : forall σd σm σdm N H ρ e,
    ⟦ σdm ⟧s ρ ↘ e ->
    (forall x, σdm (S x) = σd (S x)) -> (forall x, σm (S x) = σd (S x)) ->
    σd 0 = se_exp N -> σm 0 = se_mod H -> σdm 0 = se_dm N H ->
    ⟦ σd ⟧s ρ ↘ de_term (e 0) :: e↯ /\ ⟦ σm ⟧s ρ ↘ de_mod (env_mod e 0) :: e↯ /\
    env_eq e (de_dm (e 0) (env_mod e 0) :: e↯).
Proof.
  intros * He Ht Htm Hd Hm Hdm.
  pose proof (He 0) as H0; rewrite Hdm in H0; destruct H0 as (n & h & En & Hn & Hh).
  assert (Ev : e 0 = n) by (unfold env_var; rewrite En; reflexivity).
  assert (Emod : env_mod e 0 = h) by (unfold env_mod; rewrite En; reflexivity).
  rewrite Ev, Emod; split; [| split ].
  - intros [| x]; [ rewrite Hd; exists n; split; [ reflexivity | exact Hn ] | rewrite <- Ht; exact (He (S x)) ].
  - intros [| x]; [ rewrite Hm; exists h; split; [ reflexivity | exact Hh ] | rewrite Htm, <- Ht; exact (He (S x)) ].
  - intros [| x]; [ exact En | reflexivity ].
Qed.

(** A head tied to a unit over one tail is tied to it over any tail with the
    same entries. *)
Lemma tie_mod_env_eq : forall {Γ U R m t t'},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    R t' t' -> env_eq t t' ->
    tie_mod m (me_lit U) t -> tie_mod m (me_lit U) t'.
Proof.
  intros * HΓ HU Ht' Heq Hm.
  assert (Htt : R t t') by (eapply (per_ctx_env_resp_env_eq HΓ); [ symmetry; exact Heq | reflexivity | exact Ht' ]).
  exact (tie_mod_move _ _ _ _ _ Hm (unit_chain_at HU HΓ _ _ Htt)).
Qed.

(** Two environments related at a definition entry and two related at a
    slot, with the same tails entry by entry, give two related at the
    definition with a module part: the heads of the first, the modules of
    the second. *)
Lemma per_env_extend_dm_combine : forall {Γ A M U R a b ma mb},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    per_env_extend_def A M R a b ->
    env_ext_mod U U R ma mb ->
    env_eq ma↯ a↯ -> env_eq mb↯ b↯ ->
    per_env_extend_dm A M U R (de_dm (a 0) (env_mod ma 0) :: a↯) (de_dm (b 0) (env_mod mb 0) :: b↯).
Proof.
  intros * HΓ HUU Hab Hm Qa Qb.
  assert (HPR : PER R) by (eapply per_env_PER; exact HΓ).
  destruct Hab as [[Hab1 Hab2] Hta Htb].
  destruct Hm as [_ Ta _ Tb _].
  assert (Raa : R a↯ a↯) by (etransitivity; [ exact Hab1 | symmetry; exact Hab1 ]).
  assert (Rbb : R b↯ b↯) by (etransitivity; [ symmetry; exact Hab1 | exact Hab1 ]).
  constructor; [ constructor; [ split; assumption | exact Hta | exact Htb ]
               | exact (tie_mod_env_eq HΓ HUU Raa Qa Ta) | exact (tie_mod_env_eq HΓ HUU Rbb Qb Tb) ].
Qed.

(** A substitution extended into a definition with a module part by the
    term and the literal of related parts. *)
Lemma rel_sub_under_ctx_extend_dm : forall {Γ' Γ σ σ' A} {i : nat} {M M' U U'},
    Γ' ⊨ˢ σ ≈ σ' : Γ ->
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M ≈ M' : A ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U' ->
    Γ' ⊨ˢ σ ,,ᵈ M[σ] ‖ me_lit U[σ]ᵘ ≈ σ' ,,ᵈ M'[σ'] ‖ me_lit U'[σ']ᵘ : Γ ▸ₘ A ≔ M ‖ U.
Proof.
  intros * Hσj HA HM HU.
  pose proof (rel_sub_under_ctx_extend_sub_def Hσj HA HM) as [Rd1 HΓ'd Rd HΓd Hd].
  pose proof (rel_sub_under_ctx_extend_mod Hσj HU) as [Rm1 HΓ'm Rm HΓm Hm].
  pose proof Hσj as [R' HΓ' R HΓ _].
  pose proof (rel_modexp_refl_left HU) as HUU.
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  assert (HPR : PER R) by (eapply per_env_PER; exact HΓ).
  assert (Ed : Rd <~> per_env_extend_def A M R)
    by (eapply per_ctx_env_right_irrel; [ exact HΓd | exact (per_ctx_env_of_def HΓ HA HMl) ]).
  assert (Em : Rm <~> env_ext_mod U U R)
    by (eapply per_ctx_env_right_irrel; [ exact HΓm | exact (per_ctx_env_of_mod HΓ HUU) ]).
  assert (E1 : Rd1 <~> R') by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E2 : Rm1 <~> R') by (eapply per_ctx_env_right_irrel; eassumption).
  refine (mk_rel_sub_under_ctx _ _ _ _ R' HΓ' (per_env_extend_dm A M U R) (per_ctx_env_of_dm HΓ HA HMl HUU) _).
  intros Γ'' R'' HΓ'' φ Hφ ρ ρ' Hρ.
  destruct (Hd _ _ HΓ'' _ (proj2 (rel_wk_morphism φ _ _ (reflexivity R'') _ _ E1) Hφ) _ _ Hρ)
    as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Cd].
  destruct (Hm _ _ HΓ'' _ (proj2 (rel_wk_morphism φ _ _ (reflexivity R'') _ _ E2) Hφ) _ _ Hρ)
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Cm].
  apply (rel_chain_mono _ _ (fun a b H => proj1 (Ed a b) H)) in Cd.
  apply (rel_chain_mono _ _ (fun a b H => proj1 (Em a b) H)) in Cm.
  (** The tails of the two evaluations of each side have the same entries. *)
  assert (Q1 : env_eq m1↯ d1↯) by (eapply functional_eval_sub; [ intros x; exact (Hm1 (S x)) | intros x; exact (Hd1 (S x)) ]).
  assert (Q2 : env_eq m2↯ d2↯) by (eapply functional_eval_sub; [ intros x; exact (Hm2 (S x)) | intros x; exact (Hd2 (S x)) ]).
  assert (Q3 : env_eq m3↯ d3↯) by (eapply functional_eval_sub; [ intros x; exact (Hm3 (S x)) | intros x; exact (Hd3 (S x)) ]).
  assert (Q4 : env_eq m4↯ d4↯) by (eapply functional_eval_sub; [ intros x; exact (Hm4 (S x)) | intros x; exact (Hd4 (S x)) ]).
  destruct Cd as (D12 & D23 & D34); destruct Cm as (M12 & M23 & M34).
  apply (mk_rel_sub (de_dm (d1 0) (env_mod m1 0) :: d1↯) (de_dm (d2 0) (env_mod m2 0) :: d2↯)
                    (de_dm (d3 0) (env_mod m3 0) :: d3↯) (de_dm (d4 0) (env_mod m4 0) :: d4↯)).
  1-4: eapply eval_sub_dm_combine; [ eassumption | eassumption | intros; reflexivity | reflexivity | reflexivity | reflexivity ].
  apply rel_chain_4; eapply per_env_extend_dm_combine; eassumption.
Qed.

(** Two environments related at a definition entry are related at the
    definition with a module part when environments with the same entries
    are related at its slot. *)
Lemma per_env_extend_dm_of_parts : forall {Γ A M U R a b ma mb},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    per_env_extend_def A M R a b -> env_ext_mod U U R ma mb ->
    env_eq ma a -> env_eq mb b -> per_env_extend_dm A M U R a b.
Proof.
  intros * HΓ HU Hab [_ Ta _ Tb _] Qa Qb.
  assert (HPR : PER R) by (eapply per_env_PER; exact HΓ).
  destruct Hab as [[Hab1 Hab2] Hta Htb].
  assert (Raa : R a↯ a↯) by (etransitivity; [ exact Hab1 | symmetry; exact Hab1 ]).
  assert (Rbb : R b↯ b↯) by (etransitivity; [ symmetry; exact Hab1 | exact Hab1 ]).
  rewrite (env_eq_mod _ _ Qa 0) in Ta; rewrite (env_eq_mod _ _ Qb 0) in Tb.
  constructor; [ constructor; [ split; assumption | exact Hta | exact Htb ]
               | exact (tie_mod_env_eq HΓ HU Raa (fun x => Qa (S x)) Ta)
               | exact (tie_mod_env_eq HΓ HU Rbb (fun x => Qb (S x)) Tb) ].
Qed.

(** One substitution into the definition entry of a term part and into the
    slot of a unit is one into the definition with both as its parts. *)
Lemma rel_sub_under_ctx_dm_of_parts : forall {Γ Δ σ σ' A} {i : nat} {M U},
    Δ ⊨ A : Typeω@i -> Δ ⊨ M : A -> Δ ⊨ᵐ me_lit U ≈ me_lit U ->
    Γ ⊨ˢ σ ≈ σ' : Δ ▸ A ≔ M -> Γ ⊨ˢ σ ≈ σ' : Δ ▹ₘ U ->
    Γ ⊨ˢ σ ≈ σ' : Δ ▸ₘ A ≔ M ‖ U.
Proof.
  intros * HA HM HU [Rd1 HΓd Rd HΔd Hd] [Rm1 HΓm Rm HΔm Hm].
  pose proof (rel_exp_of_typ_inversion_simple HA) as [R [HΔ _]].
  assert (Ed : Rd <~> per_env_extend_def A M R)
    by (eapply per_ctx_env_right_irrel; [ exact HΔd | exact (per_ctx_env_of_def HΔ HA HM) ]).
  assert (Em : Rm <~> env_ext_mod U U R)
    by (eapply per_ctx_env_right_irrel; [ exact HΔm | exact (per_ctx_env_of_mod HΔ HU) ]).
  assert (E : Rm1 <~> Rd1) by (eapply per_ctx_env_right_irrel; eassumption).
  refine (mk_rel_sub_under_ctx _ _ _ _ Rd1 HΓd (per_env_extend_dm A M U R) (per_ctx_env_of_dm HΔ HA HM HU) _).
  intros Γ'' R'' HΓ'' φ Hφ ρ ρ' Hρ.
  destruct (Hd _ _ HΓ'' _ Hφ _ _ Hρ) as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Cd].
  destruct (Hm _ _ HΓ'' _ (proj2 (rel_wk_morphism φ _ _ (reflexivity R'') _ _ E) Hφ) _ _ Hρ)
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Cm].
  apply (rel_chain_mono _ _ (fun a b H => proj1 (Ed a b) H)) in Cd.
  apply (rel_chain_mono _ _ (fun a b H => proj1 (Em a b) H)) in Cm.
  assert (Q1 : env_eq m1 d1) by (eapply functional_eval_sub; eassumption).
  assert (Q2 : env_eq m2 d2) by (eapply functional_eval_sub; eassumption).
  assert (Q3 : env_eq m3 d3) by (eapply functional_eval_sub; eassumption).
  assert (Q4 : env_eq m4 d4) by (eapply functional_eval_sub; eassumption).
  destruct Cd as (D12 & D23 & D34); destruct Cm as (M12 & M23 & M34).
  apply (mk_rel_sub d1 d2 d3 d4); try assumption.
  apply rel_chain_4;
    [ apply (per_env_extend_dm_of_parts HΔ HU (ma := m1) (mb := m2))
    | apply (per_env_extend_dm_of_parts HΔ HU (ma := m2) (mb := m3))
    | apply (per_env_extend_dm_of_parts HΔ HU (ma := m3) (mb := m4)) ]; assumption.
Qed.

(** The canonical context PER of a definition with a module part, along a
    substitution. *)
Lemma per_ctx_env_of_dm_sub : forall {Γ Δ σ σ' A} {i : nat} {M U R},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ A : Typeω@i -> Δ ⊨ M : A -> Δ ⊨ᵐ me_lit U ≈ me_lit U ->
    EF Γ ▸ₘ A[σ] ≔ M[σ] ‖ U[σ]ᵘ ≈ Γ ▸ₘ A[σ] ≔ M[σ] ‖ U[σ]ᵘ ∈ per_ctx_env ↘ per_env_extend_dm A[σ] M[σ] U[σ]ᵘ R.
Proof.
  intros * HΓ Hσj HA HM HU.
  eapply per_ctx_env_extend_dm; [ exact HΓ | exact (rel_exp_of_typ_sub_simple HΓ Hσj HA)
                                | exact (rel_exp_under_ctx_sub_simple HΓ Hσj HM) |].
  intros ρ ρ' Hρ.
  pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
  destruct (rel_sub_under_ctx_simple Hσσ) as [R1 [HΓ1 [R3 [HΓ3 Hs]]]].
  assert (E : R <~> R1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E _ _) Hρ)) as (ρσ & ρ'σ & Hev & Hev' & _).
  destruct (unit_sub_chain HΓ Hσσ HU _ _ _ _ Hρ Hev Hev') as (C1 & C2 & C3).
  eapply rel_mexp_trans; [ exact C1 | eapply rel_mexp_trans; [ exact C2 | exact C3 ] ].
Qed.

(** [q σ] into a definition with a module part: as into a definition entry
    and as into a slot, from the source read as either. *)
Lemma rel_sub_under_ctx_q_dm : forall {Γ' Γ σ σ' A} {i : nat} {M U},
    Γ' ⊨ˢ σ ≈ σ' : Γ ->
    Γ ⊨ A : Typeω@i -> Γ ⊨ M : A -> Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    Γ' ▸ₘ A[σ] ≔ M[σ] ‖ U[σ]ᵘ ⊨ˢ q σ ≈ q σ' : Γ ▸ₘ A ≔ M ‖ U.
Proof.
  intros * Hσj HA HM HU.
  pose proof Hσj as [R' HΓ' R HΓ _].
  pose proof (per_ctx_env_of_dm_sub HΓ' Hσj HA HM HU) as HΓ'dm.
  apply (rel_sub_under_ctx_dm_of_parts HA HM HU).
  - eapply rel_sub_under_ctx_restrict;
      [ exact HΓ'dm | exact (per_ctx_env_of_def_sub HΓ' Hσj HA HM)
      | exact (per_ctx_env_of_def HΓ HA HM) | exact (per_ctx_env_of_def HΓ HA HM)
      | intros ? ? []; assumption | intros; assumption
      | exact (rel_sub_under_ctx_q_def Hσj HA HM) ].
  - eapply rel_sub_under_ctx_restrict;
      [ exact HΓ'dm | exact (per_ctx_env_of_mod_sub HΓ' Hσj HU)
      | exact (per_ctx_env_of_mod HΓ HU) | exact (per_ctx_env_of_mod HΓ HU)
      | intros ? ? [[[Ht _] _ _] T1 T2]; constructor; assumption | intros; assumption
      | exact (rel_sub_under_ctx_q_mod Hσj HU) ].
Qed.

(** The instance [B[Id,,ₘ⌜U⌝]] against a module [let] whose unit [U'] is
    equivalent to [U] and whose body [B'] is related to [B]: the links come
    from [B] along [σ,,ₘ⌜U[σ]⌝] and [Id,,ₘ⌜U⌝], from [B ≈ B'], and from [B']
    along [q σ'], bridged at the heads, which the slot PER ties to the
    values of the units. *)
Lemma rel_exp_let_mod_gen : forall {Γ U U' B B' C},
    Γ ⊨ᵘ U ≈ U' ->
    Γ ▹ₘ U ⊨ B ≈ B' : C ->
    Γ ⊨ B[Id ,,ₘ me_lit U] ≈ ℓₘ U' in B' : C[Id ,,ₘ me_lit U].
Proof.
  intros * [HU _ _] HB.
  pose proof (rel_modexp_refl_left HU) as HUl.
  pose proof (rel_modexp_refl_right HU) as HUr.
  pose proof HU as [R HΓ _].
  assert (HPR : PER R) by (eapply per_env_PER; exact HΓ).
  assert (HPd : PER per_dmod) by typeclasses eauto.
  pose proof (per_ctx_env_of_mod HΓ HUl) as HΓU.
  pose proof (per_ctx_env_of_mod HΓ HUr) as HΓU'.
  pose proof (rel_exp_under_ctx_refl_left HB) as HBl.
  pose proof (rel_exp_under_ctx_refl_right HB) as HBr.
  (** [B'] in the context of the right-hand unit. *)
  assert (HB'r : Γ ▹ₘ U' ⊨ B' ≈ B' : C).
  { eapply rel_exp_under_ctx_restrict; [ exact HΓU' | exact HΓU | | exact HBr ].
    intros ρ ρ' [Ht T1 _ T3 _].
    assert (Htt : R ρ↯ ρ↯) by (etransitivity; [ exact Ht | symmetry; exact Ht ]).
    assert (Ht't' : R ρ'↯ ρ'↯) by (etransitivity; [ symmetry; exact Ht | exact Ht ]).
    pose proof (tie_mod_move _ _ _ _ _ T1 (rel_mexp_sym _ _ _ _ (unit_chain_at HU HΓ _ _ Htt))) as T1'.
    pose proof (tie_mod_move _ _ _ _ _ T3 (rel_mexp_sym _ _ _ _ (unit_chain_at HU HΓ _ _ Ht't'))) as T3'.
    repeat split; assumption. }
  destruct (rel_exp_under_ctx_simple_full_at HΓU HB) as [kX HX].
  destruct (rel_exp_under_ctx_simple_full_at HΓU HBl) as [kY HY].
  destruct (rel_exp_under_ctx_simple_full_at HΓU' HB'r) as [kZ HZ].
  pose proof HBl as [? ? k HBlgen].
  pose proof HB'r as [? ? k3 HB'gen].
  refine (mk_rel_exp_under_ctx _ _ _ _ R HΓ k _).
  intros Γ' R' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HPR' : PER R') by (eapply per_env_PER; exact HΓ').
  assert (Hρσ : R ρσ ρ'σ') by (eapply rel_sub_under_ctx_at'; eassumption).
  pose proof (rel_sub_under_ctx_refl_right Hσj) as Hσ'σ'.
  pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
  assert (Hρρ : R' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  assert (Hρ'ρ' : R' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
  assert (Hσσ' : R ρσ ρσ) by (etransitivity; [ exact Hρσ | symmetry; exact Hρσ ]).
  assert (Hσ'σ'' : R ρ'σ' ρ'σ') by (etransitivity; [ symmetry; exact Hρσ | exact Hρσ ]).
  (** The values of the literals. *)
  destruct (unit_sub_chain HΓ' Hσσ HUl _ _ _ _ Hρρ Hev Hev) as ([u1 u2 Hu1 Hu2 Du12] & _).
  destruct (unit_sub_chain HΓ' Hσ'σ' HUr _ _ _ _ Hρ'ρ' Hev' Hev') as (_ & _ & [v3 v4 Hv3 Hv4 Dv34]).
  destruct (unit_chain_at HU HΓ _ _ Hσ'σ'') as [w2 w3 Hw2 Hw3 Dw].
  (** *** The Instances *)
  pose proof (rel_sub_under_ctx_extend_mod Hσj HUl) as Hτ.
  pose proof (rel_sub_under_ctx_extend_mod (rel_sub_id (ex_intro _ _ HΓ)) HUl) as Hid.
  rewrite gunit_sub_id in Hid.
  destruct (unit_sub_chain HΓ' Hσ'σ' HUl _ _ _ _ Hρ'ρ' Hev' Hev') as ([u4 u3 Hu4 Hu3 Du43] & _).
  pose proof (functional_eval_modexp _ _ _ _ Hw2 Hu3) as ->.
  pose proof (functional_eval_modexp _ _ _ _ Hw3 Hv3) as ->.
  destruct (HBlgen _ _ HΓ' _ _ Hτ _ _ _ _ Hρ
              (eval_sub_extend_mod _ _ _ _ _ Hev Hu1)
              (eval_sub_extend_mod _ _ _ _ _ Hev' Hu4))
    as [R1 [[c1 cA2 cA3 c4 Hc1 HcA2 HcA3 Hc4 Hc1chain] [w1 bA2 bA3 w4x Hw1 HbA2 HbA3 Hw4 Hw1chain]]].
  destruct (HBlgen _ _ HΓ _ _ Hid _ _ _ _ Hρσ
              (eval_sub_single_mod _ _ _ Hu2) (eval_sub_single_mod _ _ _ Hu3))
    as [R2 [[c2 cB2 cB3 c3 Hc2 HcB2 HcB3 Hc3 Hc2chain] [w2' bB2 bB3 w3x Hw2' HbB2 HbB3 Hw3' Hw2chain]]].
  (** *** The Bridges at the Substituted Environments *)
  assert (Tu1 : tie_mod u1 (me_lit U) ρσ) by (exists u2; split; assumption).
  assert (Tu2 : tie_mod u2 (me_lit U) ρσ) by (exists u2; split; [ exact Hu2 | etransitivity; [ symmetry; exact Du12 | exact Du12 ] ]).
  assert (HY1 : env_ext_mod U U R (ρσ ↦ᵐ u1) (ρσ ↦ᵐ u2))
    by (cbn [drop_env tl env_mod env_entry hd]; repeat split; assumption).
  assert (Tv3 : tie_mod v3 (me_lit U') ρ'σ') by (exists v3; split; [ exact Hv3 | etransitivity; [ exact Dv34 | symmetry; exact Dv34 ] ]).
  assert (Tv3U : tie_mod v3 (me_lit U) ρ'σ') by (exists u3; split; [ exact Hu3 | symmetry; exact Dw ]).
  assert (Tu2U' : tie_mod u2 (me_lit U') ρσ)
    by (exact (tie_mod_move _ _ _ _ _ Tu2 (unit_chain_at HU HΓ _ _ Hσσ'))).
  assert (HX1 : env_ext_mod U U R (ρσ ↦ᵐ u2) (ρ'σ' ↦ᵐ v3))
    by (cbn [drop_env tl env_mod env_entry hd]; repeat split; assumption).
  destruct (HY _ _ HY1) as [cy1 [cy2 [RY [Hcy1 [Hcy2 [HRY [by1 [by2 [Hby1 [Hby2 Hby]]]]]]]]]].
  destruct (HX _ _ HX1) as [cx1 [cx2 [RX [Hcx1 [Hcx2 [HRX [bx1 [bx2 [Hbx1 [Hbx2 Hbx]]]]]]]]]].
  (** *** The Right Commutation *)
  pose proof (per_ctx_env_of_mod_sub HΓ' Hσ'σ' HUr) as HΓ'U'.
  assert (Tv4 : tie_mod v4 (me_lit U'[σ']ᵘ) ρ') by (exists v4; split; [ exact Hv4 | etransitivity; [ symmetry; exact Dv34 | exact Dv34 ] ]).
  assert (Hpair : env_ext_mod U'[σ']ᵘ U'[σ']ᵘ R' (ρ' ↦ᵐ v4) (ρ' ↦ᵐ v4))
    by (cbn [drop_env tl env_mod env_entry hd]; repeat split; assumption).
  destruct (rel_sub_q_entry HΓ'U' HΓ Hσ'σ' _ _ Hpair Hev') as [t [Hqt Htr]].
  pose proof (rel_sub_under_ctx_q_mod Hσ'σ' HUr) as Hq.
  destruct (HB'gen _ _ HΓ'U' _ _ Hq _ _ _ _ Hpair Hqt Hqt)
    as [R3 [[e1 e2 e3 e4 He1 He2 He3 He4 He1chain] [f1 f2 f3 f4 Hf1 Hf2 Hf3 Hf4 Hf1chain]]].
  assert (Ttv4 : tie_mod v4 (me_lit U') t)
    by (exact (tie_mod_sub HΓ' HΓ Hσ'σ' HUr _ _ _ _ Hρ'ρ' Hev' (symmetry Htr) Tv4)).
  assert (HZ1 : env_ext_mod U' U' R (ρ'σ' ↦ᵐ v3) (env_entry (ρ' ↦ᵐ v4) 0 :: t))
    by (cbn [drop_env tl env_mod env_entry hd]; repeat split; try assumption; symmetry; exact Htr).
  destruct (HZ _ _ HZ1) as [cz1 [cz2 [RZ [Hcz1 [Hcz2 [HRZ [bz1 [bz2 [Hbz1 [Hbz2 Hbz]]]]]]]]]].
  functional_eval_rewrite_clear.
  (** *** Assembling *)
  assert (Hp1 : DF c1 ≈ cA2 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp1' : DF cA2 ≈ cA3 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp14 : DF c1 ≈ c4 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp2 : DF cB2 ≈ c2 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp2' : DF cB2 ≈ cB3 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp23 : DF c2 ≈ c3 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp3 : DF e1 ≈ e2 ∈ per_univ_elem k3 ↘ R3) by pairwise.
  assert (Ht1 : Dom w1 ≈ bA2 ∈ R1) by pairwise.
  assert (Ht2 : Dom w2' ≈ bB2 ∈ R2) by pairwise.
  assert (Ht3 : Dom f2 ≈ f1 ∈ R3) by pairwise.
  assert (E1 : R1 <~> RY) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hp1' HRY).
  assert (E2 : R2 <~> RY) by exact (per_univ_elem_cross_irrel _ _ _ _ _ _ _ Hp2' HRY).
  assert (E3 : R2 <~> RX) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hp2' HRX).
  assert (E4 : RZ <~> RX) by exact (per_univ_elem_cross_irrel _ _ _ _ _ _ _ HRZ HRX).
  assert (E5 : R3 <~> RZ) by exact (per_univ_elem_left_irrel _ _ _ _ _ _ _ Hp3 HRZ).
  assert (F1 : R1 <~> R2) by (rewrite E1, E2; reflexivity).
  assert (FY : RY <~> R2) by (rewrite E2; reflexivity).
  assert (FX : RX <~> R2) by (rewrite E3; reflexivity).
  assert (FZ : RZ <~> R2) by (rewrite E4, E3; reflexivity).
  assert (F3 : R3 <~> R2) by (rewrite E5, FZ; reflexivity).
  apply (fun H => per_univ_elem_resp_iff H F1) in Hp1, Hp14.
  apply F1 in Ht1.
  apply (fun H => per_univ_elem_resp_iff H FY) in HRY.
  apply FY in Hby.
  apply FX in Hbx.
  apply FZ in Hbz.
  apply F3 in Ht3.
  assert (PER R2) by (eapply per_elem_PER; exact Hp23).
  destruct U' as [Δ' D']; apply eval_me_lit_iff in Hv3; rewrite gunit_sub_mk in Hv4; apply eval_me_lit_iff in Hv4.
  exists R2; split.
  - apply (mk_rel_exp c1 c2 c3 c4); try eassumption.
    + rewrite exp_sub_extend_mod_sub; exact Hc1.
    + rewrite exp_sub_extend_mod_sub; exact Hc4.
    + assert (Hc12 : DF c1 ≈ c2 ∈ per_univ_elem k ↘ R2)
        by (eapply per_univ_trans; [ eapply per_univ_trans; [ exact Hp1 | exact HRY ] | exact Hp2 ]).
      apply rel_chain_4; [ exact Hc12 | exact Hp23 | solve_per ].
  - apply (mk_rel_exp w1 w2' bx2 f1); try eassumption.
    + rewrite exp_sub_extend_mod_sub; exact Hw1.
    + eapply eval_exp_let_mod; [ exact Hv3 | exact Hbx2 ].
    + cbn [exp_sub bnd_sub]; rewrite gunit_sub_mk; eapply eval_exp_let_mod; [ exact Hv4 | exact Hf1 ].
    + apply rel_chain_4; solve_per.
Qed.

(** [ζ] for modules. *)
Corollary rel_exp_under_ctx_let_mod_zeta : forall {Γ U B C},
    Γ ⊨ᵘ U ≈ U ->
    Γ ▹ₘ U ⊨ B : C ->
    Γ ⊨ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : C[Id ,,ₘ me_lit U].
Proof.
  intros * HU HB.
  apply rel_exp_under_ctx_sym.
  exact (rel_exp_let_mod_gen HU HB).
Qed.

End Fixed_GCtx.

Lemma sem_ext_eq_dm :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ M' : A' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ᵘ U' ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ▸ₘ A ≔ M ‖ U ≈ Ψ' ▸ₘ A' ≔ M' ‖ U' ).
Proof.
  intros * HΨ HA HAA' HM HMM' HA' HM' HUU' HU'U'; sem_intro0.
  assert (Hr : Γ ⊨ˣ Ψ ▸ₘ A ≔ M ‖ U ≈ Ψ' ▸ₘ A' ≔ M' ‖ U').
  { destruct HΨ as [H1 H2 [Rx HRx]]; destruct HUU' as [HU HsU _]; destruct HU'U' as [HU' HsU' _].
    destruct (rel_ctx_wf_per_ctx_env H1) as [R HR].
    destruct (rel_ctx_wf_per_ctx_env H2) as [R' HR'].
    pose proof (rel_modexp_refl_left HU) as HUU.
    constructor; cbn [app].
    - econstructor; [ exact H1 | exact (per_ctx_env_of_dm HR HA HM HUU) | exact HA | exact HM | exact HUU | exact HsU ].
    - econstructor; [ exact H2 | exact (per_ctx_env_of_dm HR' HA' HM' HU') | exact HA' | exact HM' | exact HU' | exact HsU' ].
    - exact (per_ctx_env_extend_dm_cross HRx HAA' HMM' HU). }
  constructor; [ assumption | exact Hr | apply valid_ctx_dm | apply valid_ctx_dm ];
    first [ assumption | exact (rel_ext_under_ctx_left _ _ _ Hr) | exact (rel_ext_under_ctx_right _ _ _ Hr) ].
Qed.

Lemma sem_exp_eq_let_mod_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ C : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : C[Id ,,ₘ me_lit U] ).
Proof. intros * HU _ HB; sem_intro; [ assumption | exact (rel_exp_under_ctx_let_mod_zeta HU HB) ]. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** Congruence: both sides are related to the instance [B[Id,,ₘ⌜U⌝]]. *)
Corollary rel_exp_under_ctx_let_mod_cong : forall {Γ U U' B B' C},
    Γ ⊨ᵘ U ≈ U' ->
    Γ ▹ₘ U ⊨ B ≈ B' : C ->
    Γ ⊨ ℓₘ U in B ≈ ℓₘ U' in B' : C[Id ,,ₘ me_lit U].
Proof.
  intros * HU HB.
  pose proof HU as [HU0 HsU _].
  eapply rel_exp_under_ctx_trans; [| exact (rel_exp_let_mod_gen HU HB) ].
  apply rel_exp_under_ctx_sym.
  exact (rel_exp_let_mod_gen (U' := U) (mk_rel_unit_under_ctx _ _ _ (rel_modexp_refl_left HU0) HsU HsU)
           (rel_exp_under_ctx_refl_left HB)).
Qed.

End Fixed_GCtx.

Lemma sem_exp_eq_let_mod_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ B ≈ B' : C ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓₘ U' in B' : C[Id ,,ₘ me_lit U] ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓₘ U in B ≈ ℓₘ U' in B' : C[Id ,,ₘ me_lit U] ).
Proof. intros * HU HB _; sem_intro; [ assumption | exact (rel_exp_under_ctx_let_mod_cong HU HB) ]. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Corollary valid_exp_under_ctx_let_mod : forall {Γ U B C},
    Γ ⊨ᵘ U ≈ U ->
    Γ ▹ₘ U ⊨ B : C ->
    Γ ⊨ ℓₘ U in B : C[Id ,,ₘ me_lit U].
Proof. intros * HU HB; exact (rel_exp_under_ctx_let_mod_cong HU HB). Qed.

End Fixed_GCtx.

Lemma sem_let_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ C : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓₘ U in B : C[Id ,,ₘ me_lit U] ).
Proof. intros * HU _ HB; sem_intro; [ assumption | exact (valid_exp_under_ctx_let_mod HU HB) ]. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** What the gluing model needs of an instance by a literal:
    [⟦B[Id,,ₘ⌜U⌝]⟧ρ] and [⟦B⟧(ρ ↦ᵐ ⟦⌜U⌝⟧ρ)] are related. *)
Lemma per_univ_of_instance_mod : forall {Γ U B k env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ᵘ U ≈ U ->
    Γ ▹ₘ U ⊨ B : Typeω@k ->
    forall ρ h,
      Dom ρ ≈ ρ ∈ env_relΓ ->
      ⟦ me_lit U ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h ->
      exists a b,
        ⟦ B[Id ,,ₘ me_lit U] ⟧ ρ ↘ a /\ ⟦ B ⟧ (ρ ↦ᵐ h) ↘ b /\
          Dom a ≈ a ∈ per_univ k /\ Dom a ≈ b ∈ per_univ k.
Proof.
  intros * HΓ [HU _ _] HB * Hρ Hh.
  pose proof (rel_sub_under_ctx_extend_mod (rel_sub_id (ex_intro _ _ HΓ)) HU) as Hid.
  rewrite gunit_sub_id in Hid.
  pose proof (rel_exp_of_typ_inversion HB) as [env_relΓU [HΓU HBgen]].
  destruct (HBgen _ _ HΓ _ _ Hid _ _ _ _ Hρ (eval_sub_single_mod _ _ _ Hh) (eval_sub_single_mod _ _ _ Hh))
    as [t1 t2 t3 t4 Ht1 Ht2 Ht3 Ht4 Hchain].
  destruct Hchain as [Ht12 _].
  exists t1, t2.
  do 2 (split; [ eassumption |]).
  split; [| eassumption ].
  etransitivity; [ eassumption | symmetry; eassumption ].
Qed.

(** ** Environments of Arguments *)

Lemma env_args_rev : forall ρ xs, env_args ρ xs = List.rev (List.map de_term xs) ++ ρ.
Proof.
  intros ρ xs; revert ρ; induction xs as [| x xs IH]; intros; [ reflexivity |].
  cbn [env_args List.fold_left List.map List.rev]; change (List.fold_left extend_env xs (ρ ↦ x)) with (env_args (ρ ↦ x) xs).
  rewrite IH, <- List.app_assoc; reflexivity.
Qed.

Lemma skipn_env_args : forall ρ xs, List.skipn (List.length xs) (env_args ρ xs) = ρ.
Proof.
  intros; rewrite env_args_rev.
  rewrite List.skipn_app, List.skipn_all2 by (rewrite List.length_rev, List.length_map; lia).
  rewrite List.length_rev, List.length_map, Nat.sub_diag; reflexivity.
Qed.

Lemma eval_wk_shiftn : forall n ρ, ⟪wk_shiftn n⟫ ρ = List.skipn n ρ.
Proof.
  intros n ρ.
  assert (Hm : wk_mono (wk_shiftn n)) by (intros x y Hxy; cbn; lia).
  assert (Hl : wk_len (wk_shiftn n) (List.length ρ) = List.length (List.skipn n ρ)).
  { apply nat_eq_of_lt_iff; intros x; rewrite wk_len_spec by exact Hm; rewrite List.length_skipn; cbn; lia. }
  apply env_ext; [ rewrite eval_wk_length; exact Hl |].
  intros x Hx; rewrite eval_wk_length, Hl in Hx.
  rewrite eval_wk_var by (rewrite Hl; exact Hx).
  rewrite !env_entry_nth, List.nth_skipn; cbn; f_equal; lia.
Qed.

Lemma eval_wk_shiftn_args : forall ρ xs, ⟪wk_shiftn (List.length xs)⟫ (env_args ρ xs) = ρ.
Proof. intros; rewrite eval_wk_shiftn; apply skipn_env_args. Qed.

(** ** The [n]-fold Shift *)

Lemma wk_mono_shiftn : forall n, wk_mono (wk_shiftn n).
Proof. intros n x y H; cbn; lia. Qed.

#[export] Instance WkMono_shiftn (n : nat) : WkMono (wk_shiftn n) := wk_mono_shiftn n.

Lemma rel_wk_shiftn : forall Ψ Γ RΨ RΓ,
    EF Ψ ++ Γ ≈ Ψ ++ Γ ∈ per_ctx_env ↘ RΨ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    rel_wk (wk_shiftn (List.length Ψ)) RΨ RΓ.
Proof.
  intros * HΨ HΓ; split; [ intros x y Hxy; cbn; lia |].
  revert RΨ HΨ; induction Ψ as [| e Ψ IH]; intros RΨ HΨ ρ ρ' Hρ; cbn [List.app List.length] in *.
  - rewrite !eval_wk_shiftn; cbn [List.skipn].
    assert (E : RΨ <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption). apply E; exact Hρ.
  - destruct (rel_wk_shift_tail HΨ) as (R' & HR' & Hsh).
    pose proof (Hsh _ _ Hρ) as Ht; rewrite !eval_wk_shift in Ht.
    rewrite !eval_wk_shiftn; cbn [List.skipn].
    destruct ρ as [| d ρ], ρ' as [| d' ρ']; cbn [drop_env List.tl] in Ht;
      (pose proof (IH _ HR' _ _ Ht) as H; rewrite !eval_wk_shiftn in H; try exact H);
      rewrite List.skipn_nil in *; exact H.
Qed.

Lemma rel_wk_under_ctx_shiftn : forall Ψ Γ, ⊨ Ψ ++ Γ -> Ψ ++ Γ ⊨ʷ (wk_shiftn (List.length Ψ)) : Γ.
Proof.
  intros * H.
  destruct (rel_ctx_wf_per_ctx_env H) as [R HR].
  destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_app_r _ _ H)) as [RΓ HΓ].
  eapply rel_wk_under_ctx_intro; [ exact HR | exact HΓ | exact (rel_wk_shiftn _ _ _ _ HR HΓ) ].
Qed.

End Fixed_GCtx.
