(** * Contexts

    The rules of [wf_ctx] but the module slot's (which is in
    [Modules/MemberTypes.v]), and the two context-subtyping facts that
    [Consequences] needs.  [⊨ Γ] is inductive, so the empty context is
    the constructor [rel_ctx_wf_nil].  The extension step is the one place that
    builds a context PER rather than taking one apart.

    The head relation of the extension is the impredicative [per_head], "whatever
    every [per_univ_elem] relating the values of [A] and [A'] relates", chosen once
    by [per_ctx_env_extend].  This file supplies its premise, which is what
    [rel_exp_of_typ_inversion_simple] delivers. *)

From Stdlib Require Import Morphisms_Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import LogicalRelation UniverseCases.
Import Domain_Notations Fixed_Notations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma per_ctx_extend : forall {Γ Γ' A A'} {i : nat},
    ⊨ Γ ≈ Γ' ->
    Γ ⊨ A ≈ A' : Typeω@i ->
    ⊨ Γ ▹ A ≈ Γ' ▹ A'.
Proof.
  intros * [env_relΓΓ' HΓΓ'] H.
  pose proof (rel_exp_of_typ_inversion_simple H) as [env_relΓ [HΓ HA]].
  (** Both witnesses have [Γ] on the left, so they agree up to [<~>].  Naming
    the equivalence, rather than calling [handle_per_ctx_env_irrel], keeps
    [env_relΓΓ'], the only witness for the tail of the goal, in place. *)
  assert (Hirrel : env_relΓΓ' <~> env_relΓ)
    by (eapply per_ctx_env_right_irrel; [exact HΓΓ' | exact HΓ]).
  eexists.
  eapply per_ctx_env_extend; [ eassumption |].
  intros ρ ρ' Hρ%Hirrel.
  now apply HA.
Qed.

Lemma rel_ctx_wf_extend : forall {Γ A} {i : nat},
    ⊨ Γ ->
    Γ ⊨ A : Typeω@i ->
    ⊨ Γ ▹ A.
Proof.
  intros * HΓ HA.
  pose proof (per_ctx_extend (rel_ctx_wf_per_ctx HΓ) HA) as [env_relΓA HΓA].
  econstructor; eassumption.
Qed.

Hint Resolve per_ctx_extend rel_ctx_wf_extend : mctt.

End Fixed_GCtx.

#[local] Generalizable All Variables.

Lemma sem_ctx_extend :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ▹ A ).
Proof.
  intros * HA; sem_intro.
  apply valid_ctx_ass; [ assumption | eapply rel_ctx_wf_extend; eassumption ].
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Definition Entries

    The canonical context PER of [Γ ▸ A ≔ M] is [per_env_extend_def], fed by
    the [Id] instances of the relations of [A] and [M]. *)
Lemma per_ctx_env_of_def : forall {Γ A} {i : nat} {M env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M : A ->
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ per_env_extend_def A M env_relΓ.
Proof.
  intros * HΓ HA HM.
  eapply per_ctx_env_extend_def; [ eassumption | |].
  - exact (rel_exp_of_typ_inversion_simple_at HΓ HA).
  - exact (rel_exp_under_ctx_simple_at HΓ HM).
Qed.

Lemma rel_ctx_wf_extend_def : forall {Γ A} {i : nat} {M},
    ⊨ Γ ->
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M : A ->
    ⊨ Γ ▸ A ≔ M.
Proof.
  intros * HΓ HA HM.
  destruct (rel_ctx_wf_per_ctx_env HΓ) as [env_relΓ HΓ'].
  econstructor; [ eassumption | eapply per_ctx_env_of_def; eassumption | eassumption | eassumption ].
Qed.

Hint Resolve rel_ctx_wf_extend_def : mctt.

End Fixed_GCtx.

Lemma sem_ctx_extend_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ).
Proof.
  intros * HA HM; sem_intro.
  apply valid_ctx_def; [ assumption | eapply rel_ctx_wf_extend_def; eassumption ].
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** A definition entry refines an assumption entry of the same type. *)
Lemma per_ctx_env_def_forget : forall {Γ A} {i : nat} {M R R'},
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M : A ->
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ R ->
    EF Γ ▹ A ≈ Γ ▹ A ∈ per_ctx_env ↘ R' ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> Dom ρ ≈ ρ' ∈ R'.
Proof.
  intros * HA HM HR HR' ρ ρ' Hρ.
  pose proof (rel_exp_of_typ_inversion_simple HA) as [env_relΓ [HΓ HAs]].
  pose proof (per_ctx_env_of_def HΓ HA HM) as Hd.
  pose proof (per_ctx_env_extend HΓ HAs) as Ha.
  assert (E1 : R <~> per_env_extend_def A M env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E2 : R' <~> per_env_extend A A env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  apply E2; apply E1 in Hρ.
  destruct Hρ as [? _]; assumption.
Qed.

(** A definition with a module part refines an assumption entry of the same
    type: its environments' heads are related at the type's values. *)
Lemma per_ctx_env_dm_forget : forall {Γ A} {i : nat} {M U R R'},
    Γ ⊨ A : Typeω@i ->
    EF Γ ▸ₘ A ≔ M ‖ U ≈ Γ ▸ₘ A ≔ M ‖ U ∈ per_ctx_env ↘ R ->
    EF Γ ▹ A ≈ Γ ▹ A ∈ per_ctx_env ↘ R' ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> Dom ρ ≈ ρ' ∈ R'.
Proof.
  intros * HA HR HR' ρ ρ' Hρ.
  pose proof (rel_exp_of_typ_inversion_simple HA) as [env_relΓ [HΓ HAs]].
  pose proof (per_ctx_env_extend HΓ HAs) as Ha.
  assert (E2 : R' <~> per_env_extend A A env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  apply E2.
  inversion HR; subst.
  match goal with
  | HE : R <~> _, Ht : per_ctx_env ?T Γ Γ,
    HT : forall ρ ρ' (e : ?T ρ ρ'), PER.Definitions.rel_typ _ A ρ A ρ' _ |- _ =>
      let e := fresh "e" in let Hh := fresh "Hh" in let ET := fresh "ET" in
      apply HE in Hρ as [e Hh _ _ _ _ _ _ _ _];
      assert (ET : T <~> env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption);
      destruct (HT _ _ e) as [a a' Ha0 Ha0' HR0];
      split; [ apply ET; exact e |];
      apply (per_head_iff Ha0 Ha0' HR0); exact Hh
  end.
Qed.

(** Definition entries with related bodies relate the same environments. *)
Lemma per_ctx_env_def_conv : forall {Γ A} {i : nat} {M M' R R'},
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M ≈ M' : A ->
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ R ->
    EF Γ ▸ A ≔ M' ≈ Γ ▸ A ≔ M' ∈ per_ctx_env ↘ R' ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> Dom ρ ≈ ρ' ∈ R'.
Proof.
  intros * HA HM HR HR' ρ ρ' Hρ.
  pose proof (rel_exp_of_typ_inversion_simple HA) as [env_relΓ [HΓ HAs]].
  pose proof (per_ctx_env_of_def HΓ HA (rel_exp_under_ctx_refl_left HM)) as Hd.
  pose proof (per_ctx_env_of_def HΓ HA (rel_exp_under_ctx_refl_right HM)) as Hd'.
  pose proof (per_ctx_env_extend HΓ HAs) as Ha.
  assert (E1 : R <~> per_env_extend_def A M env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E2 : R' <~> per_env_extend_def A M' env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (PER env_relΓ) by (eapply per_env_PER; eassumption).
  assert (PER (per_env_extend A A env_relΓ)) by (eapply per_env_PER; eassumption).
  apply E2; apply E1 in Hρ.
  destruct Hρ as [Hρ Ht Ht'].
  assert (Hρρ : Dom ρ ≈ ρ ∈ per_env_extend A A env_relΓ) by solve_per.
  assert (Hρ'ρ' : Dom ρ' ≈ ρ' ∈ per_env_extend A A env_relΓ) by solve_per.
  pose proof (rel_exp_of_typ_inversion_simple_at HΓ HA) as HAat.
  pose proof (rel_exp_under_ctx_simple_at HΓ HM) as HMat.
  constructor; [ exact Hρ | |].
  - exact (def_tie_resp _ HAat HMat Hρρ Ht).
  - exact (def_tie_resp _ HAat HMat Hρ'ρ' Ht').
Qed.

(** A definition with a module part refines the definition entry of its
    term part: its environments' heads are tied to the term's values. *)
Lemma per_ctx_env_dm_forget_def : forall {Γ A} {i : nat} {M U R R'},
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M : A ->
    EF Γ ▸ₘ A ≔ M ‖ U ≈ Γ ▸ₘ A ≔ M ‖ U ∈ per_ctx_env ↘ R ->
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ R' ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> Dom ρ ≈ ρ' ∈ R'.
Proof.
  intros * HA HM HR HR' ρ ρ' Hρ.
  pose proof (rel_exp_of_typ_inversion_simple HA) as [env_relΓ [HΓ HAs]].
  pose proof (per_ctx_env_of_def HΓ HA HM) as Hd.
  assert (E1 : R' <~> per_env_extend_def A M env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (HPER : PER env_relΓ) by (eapply per_env_PER; eassumption).
  pose proof (rel_exp_of_typ_inversion_simple_at HΓ HA) as HAat.
  apply E1.
  inversion HR; subst.
  match goal with
  | HE : R <~> _, Ht : per_ctx_env ?T Γ Γ,
    HT : forall ρ ρ' (e : ?T ρ ρ'), PER.Definitions.rel_typ _ A ρ A ρ' _ |- _ =>
      let e := fresh "e" in let Hh := fresh "Hh" in let ET := fresh "ET" in
      apply HE in Hρ as [e Hh (m1 & Hm1 & Ht1) _ _ (m2 & Hm2 & Ht2) _ _ _ _];
      assert (ET : T <~> env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption);
      destruct (HT _ _ e) as [a a' Ha0 Ha0' HR0];
      pose proof (per_head_iff Ha0 Ha0' HR0) as Eh;
      assert (Hρ0 : Dom ρ↯ ≈ ρ'↯ ∈ env_relΓ) by (apply ET; exact e);
      assert (E3 : per_head A A ρ↯ ρ↯ <~> per_head A A ρ↯ ρ'↯)
        by (eapply (per_head_resp_simple HPER HAat); apply rel_chain_4; solve_per);
      assert (E4 : per_head A A ρ'↯ ρ'↯ <~> per_head A A ρ↯ ρ'↯)
        by (eapply (per_head_resp_simple HPER HAat); apply rel_chain_4; solve_per);
      constructor;
      [ split; [ exact Hρ0 | apply Eh; exact Hh ]
      | exists m1; split; [ exact Hm1 | apply E3, Eh; exact Ht1 ]
      | exists m2; split; [ exact Hm2 | apply E4, Eh; exact Ht2 ] ]
  end.
Qed.

Lemma rel_ctx_sub_empty :
  SubE ⋅ <: ⋅.
Proof. mauto. Qed.

Lemma rel_ctx_sub_extend : forall {Γ Δ} {i : nat} {A A'},
  SubE Γ <: Δ ->
  ⊨ Γ ->
  ⊨ Δ ->
  Γ ⊨ A : Typeω@i ->
  Δ ⊨ A' : Typeω@i ->
  Γ ⊨ A ⊆ A' ->
  SubE Γ ▹ A <: Δ ▹ A'.
Proof.
  intros * Hsub HΓ HΔ HA HA' Hsubtyp.
  pose proof (rel_ctx_wf_extend HΓ HA) as HΓA%rel_ctx_wf_per_ctx_env.
  pose proof (rel_ctx_wf_extend HΔ HA') as HΔA'%rel_ctx_wf_per_ctx_env.
  destruct HΓA as [env_relΓA HΓA], HΔA' as [env_relΔA' HΔA'].
  pose proof (rel_subtyp_under_ctx_simple Hsubtyp) as [env_relΓ [HΓ' [j Hsub2]]].
  econstructor; try eassumption.
  intros ρ ρ' a a' Hρ Ha Ha'.
  destruct (Hsub2 _ _ Hρ) as [a2 [a2' [Ha2 [Ha2' Hsubaa']]]].
  functional_eval_rewrite_clear.
  eassumption.
Qed.

Hint Resolve rel_ctx_sub_empty rel_ctx_sub_extend : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve per_ctx_extend rel_ctx_wf_extend rel_ctx_wf_extend_def : mctt.
#[export]
Hint Resolve rel_ctx_sub_empty rel_ctx_sub_extend : mctt.

(** The empty context, which has no relation of its own: [⊨ ⋅] is a
    constructor. *)
Lemma sem_ctx_empty :
  `( ⊢ᵍ Θ ⍮ Ξ ->
     ⊨ Θ ⍮ Ξ ⍮ ⋅ ).
Proof. intros * H; sem_intro; constructor. Qed.
