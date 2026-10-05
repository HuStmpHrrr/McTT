(** * Normal Forms of Member Types by Evaluation

    The member type of a definition [x] of a module [H] holds the bodies
    before [x] literally, as [ℓₘ]-binders, and member types of aliases and
    submodules hold them again for every sibling they instantiate.  The
    checker needs only the normal form of the member type, and when [H]
    takes no more argument it gets it without building the member type:
    it evaluates [H] in the initial environment, takes the type value of
    [x] there ([sel_ty], [h ⦂ₜ x Θ ↘ a]) and reads it back.

    This is sound because a well-formed module expression is valid in its
    members ([wf_modexp_sem_mt]): its value types [x] at the value of the
    member type ([mtyped]), and that value is related to the one
    [sel_ty] gives ([mtyped_sel_ty]), so both read back to the same normal
    form ([sel_ty_nbe]). *)

From Stdlib Require Import List.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Semantic Require Import Realizability MemberWf.
From Mctt.Core.Completeness Require Import MemberCases MemberSem.
Import Domain_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The type value [sel_ty] gives is related to the one at which the module
    value types the member. *)
Lemma mtyped_sel_ty : forall h x a,
    h ⦂ₜ x gc_ctx ↘ a ->
    forall a', mtyped h (x :: nil) mk_term a' -> exists i R, per_univ_elem i R a' a.
Proof.
  induction 1 as [| ? ? ? ? ? ? ? Hl He Hs IH]; intros a' Hm;
    inversion Hm; subst;
    (** an unsaturated value has no [sel_ty] *)
    try (match goal with Hx : exists _ _ _, _ = dm_local _ _ _ /\ _ |- _ =>
      destruct Hx as (ρ0 & U0 & args0 & Heq & Hlt);
      destruct U0 as [Δ0 [Φ0 | E0]]; cbn in Heq; inversion Heq; subst; cbn in Hlt; lia end);
    repeat match goal with H1 : ?a = Some _, H2 : ?a = Some _ |- _ => rewrite H1 in H2; inversion H2; subst; clear H2 end;
    functional_eval_rewrite_clear;
    repeat match goal with H1 : eval_modexp _ ?E ?r ?h1, H2 : eval_modexp _ ?E ?r ?h2 |- _ =>
      pose proof (functional_eval_modexp _ _ _ _ H1 H2); subst; clear H2 end;
    eauto.
Qed.

(** The type value [sel_ty] gives reads back to the normal form of the
    member type. *)
Theorem sel_ty_nbe : forall Γ H x A h a B R,
    sem_mt gc_ctx Γ H ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    member_type gc_ctx Γ H (x :: nil) (mr_term A) ->
    forall ρ, initial_env_f Γ ρ ->
    ⟦ H ⟧ᵐ gc_ctx ⍮ ρ ↘ h ->
    h ⦂ₜ x gc_ctx ↘ a ->
    Rtyp a in length Γ ↘ B ->
    nbe_ty_f Γ A B.
Proof.
  intros * [S1 _] HR Hm ρ Hρ Hh Hs HB.
  destruct (per_ctx_then_per_env_initial_env HR) as (ρ1 & ρ2 & Hρ1 & Hρ2 & Hr).
  assert (ρ1 = ρ) as -> by (eapply functional_initial_env; eassumption).
  assert (ρ2 = ρ) as -> by (eapply functional_initial_env; eassumption).
  destruct (proj2 (S1 _ _ Hm ltac:(discriminate)) _ _ HR Hr _ Hh) as (a' & Ha' & Hma'); cbn in Ha', Hma'.
  destruct (mtyped_sel_ty _ _ _ Hs _ Hma') as (i & E & HE).
  destruct (per_univ_then_per_top_typ HE (length Γ)) as (C & HC1 & HC2).
  pose proof (functional_read_typ _ _ _ _ HC2 HB) as ->.
  econstructor; eassumption.
Qed.

(** The form the checker uses: for a well-formed module expression. *)
Corollary sel_ty_nbe_wf : forall Γ H x A h a B ρ,
    ⊢ Γ ->
    gc_ctx ⍮ Γ ⊢ᵐ H ≈ H ->
    member_type gc_ctx Γ H (x :: nil) (mr_term A) ->
    initial_env_f Γ ρ ->
    ⟦ H ⟧ᵐ gc_ctx ⍮ ρ ↘ h ->
    h ⦂ₜ x gc_ctx ↘ a ->
    Rtyp a in length Γ ↘ B ->
    nbe_ty_f Γ A B.
Proof.
  intros * HΓ HH Hm Hρ Hh Hs HB.
  destruct (sem_ctx_per_ctx_env (completeness_fundamental_ctx _ HΓ)) as [R HR].
  eapply sel_ty_nbe; [ exact (proj1 (wf_modexp_sem_mt _ _ HH)) | exact HR | eassumption .. ].
Qed.
End Fixed_GCtx.
