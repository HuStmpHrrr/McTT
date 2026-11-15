(** * The Set Model of Local Definitions

    A local definition's body is read at the definition's value; with the
    definition substituted it has the same value ([ζ]). *)

From Stdlib Require Import String List Lia.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Judgments Require Export Variables.
From Mctt.Core.SetModel.Interpretation Require Import Substitution ContextRelation.
From Mctt.Core.Syntactic Require Import Syntax.
From Mctt.Core.Syntactic.System Require Import Definitions Structural.
Import ListNotations.

Section Lets.
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

Section DefinitionDenotations.
  Context {GC : GCtx}.
  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).

(** The environment of a definition at its value. *)
Definition def_env (FM : set_env -> aczel_set) (ρ : set_env) : set_env := set_env_extend ρ (set_entry_term ak_relevant (FM ρ)).

Lemma set_env_in_def : forall Γ A M FM ρ, set_denotes T γ Γ M FM -> set_env_in T γ Γ ρ ->
    set_env_in T γ (ce_def A M :: Γ) (def_env FM ρ).
Proof.
  intros * HM Hρ. split; [exact Hρ |]. exists ak_relevant, (FM ρ), (FM ρ), (FM ρ).
  constructor; [reflexivity | reflexivity | exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) | apply set_eq_refl | apply set_eq_refl].
Qed.

(** A term under a definition denotes, with the definition substituted, its
    value at the definition's. *)
Lemma set_denotes_def_sub : forall Γ A M X FM FX, set_ctx T γ Γ ->
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_def A M :: Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˢ sb_extend sb_id (se_exp M) : ce_def A M :: Γ ->
    set_denotes T γ Γ M FM -> set_denotes T γ (ce_def A M :: Γ) X FX ->
    set_denotes T γ Γ (exp_sub X (sb_extend sb_id (se_exp M))) (fun ρ => FX (def_env FM ρ)).
Proof.
  intros * HΓ Hc Hσ HM HX. apply set_denotes_of_exists; [exact Hfn | exact Hmods | exact HΓ |]. intros ρ Hρ.
  apply (set_interp_single_sub_entry T γ Γ ρ (ce_def A M) ak_relevant M (FM ρ)); [exact Hc | exact Hσ | exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) |].
  apply (set_denotes_exists _ _ _ _ _ HX). apply set_env_in_def; assumption.
Qed.

Lemma set_denotes_let_def : forall Γ A M B FM FB, set_ctx T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ ce_def A M :: Γ ->
    set_denotes T γ Γ M FM -> set_denotes T γ (ce_def A M :: Γ) B FB ->
    set_denotes T γ Γ (a_let (b_def A M) B) (fun ρ => FB (def_env FM ρ)).
Proof.
  intros * HΓ Hc HM HB. destruct (set_env_rel_per _ _ _ HΓ) as [Hsym Htrans]. constructor.
  - intros ρ Hρ. econstructor; [exact Hc | exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) |].
    apply (set_denotes_exists _ _ _ _ _ HB). apply set_env_in_def; assumption.
  - intros ρ ρ' v Hr Hv. inversion Hv; subst.
    assert (Hρ : set_env_in T γ Γ ρ) by (eapply Htrans; [exact Hr | apply Hsym; exact Hr]).
    match goal with HM' : set_interp _ _ _ _ M ?v0, HB' : set_interp _ _ _ _ B _ |- _ =>
      apply (set_denotes_unique _ _ _ _ _ HB (def_env FM ρ) (set_env_extend ρ' (set_entry_term ak_relevant v0)) v); [| exact HB'];
      split; [exact Hr |]; exists ak_relevant, (FM ρ), v0, (FM ρ);
      constructor; [reflexivity | reflexivity | exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) | apply set_eq_refl
                   | exact (set_denotes_unique _ _ _ _ _ HM _ _ _ Hr HM')] end.
Qed.

End DefinitionDenotations.


(** ** Local Modules *)

Section ModuleDenotations.
  Context {GC : GCtx}.
  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).

(** The environment of a local module at its module. *)
Definition mod_env (FU : set_env -> set_module) (ρ : set_env) : set_env := set_env_extend ρ (set_entry_module (FU ρ)).

Lemma set_env_in_mod : forall Γ U FU ρ, set_modexp_denotes T γ Γ (me_lit U) FU -> set_env_in T γ Γ ρ ->
    set_env_in T γ (ce_mod U :: Γ) (mod_env FU ρ).
Proof.
  intros * HU Hρ. split; [exact Hρ |]. exists (FU ρ), (FU ρ), (FU ρ).
  constructor; [reflexivity | reflexivity | apply set_interp_me_lit_iff; exact (set_modexp_denotes_exists _ _ _ _ _ HU _ Hρ)
               | exact (set_modexp_denotes_refl _ _ _ _ _ _ HU Hρ) .. ].
Qed.

(** A term under a local module denotes, with the unit substituted, its
    value at the unit's module. *)
Lemma set_denotes_mod_sub : forall Γ U X FU FX, set_ctx T γ Γ ->
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_mod U :: Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˢ sb_extend sb_id (se_mod (me_lit U)) : ce_mod U :: Γ ->
    set_modexp_denotes T γ Γ (me_lit U) FU -> set_denotes T γ (ce_mod U :: Γ) X FX ->
    set_denotes T γ Γ (exp_sub X (sb_extend sb_id (se_mod (me_lit U)))) (fun ρ => FX (mod_env FU ρ)).
Proof.
  intros * HΓ Hc Hσ HU HX. apply set_denotes_of_exists; [exact Hfn | exact Hmods | exact HΓ |]. intros ρ Hρ.
  apply (set_interp_single_sub_slot T γ Γ ρ (ce_mod U) _ (set_entry_module (FU ρ))); [exact Hc | exact Hσ | |].
  - split; cbn; [constructor | exact (set_modexp_denotes_exists _ _ _ _ _ HU _ Hρ)].
  - apply (set_denotes_exists _ _ _ _ _ HX). apply set_env_in_mod; assumption.
Qed.

Lemma set_denotes_let_mod : forall Γ U B FU FB, set_ctx T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ ce_mod U :: Γ ->
    set_modexp_denotes T γ Γ (me_lit U) FU -> set_denotes T γ (ce_mod U :: Γ) B FB ->
    set_denotes T γ Γ (a_let (b_mod U) B) (fun ρ => FB (mod_env FU ρ)).
Proof.
  intros * HΓ Hc HU HB. apply set_denotes_of_exists; [exact Hfn | exact Hmods | exact HΓ |]. intros ρ Hρ.
  econstructor; [exact Hc | apply set_interp_me_lit_iff; exact (set_modexp_denotes_exists _ _ _ _ _ HU _ Hρ) |].
  apply (set_denotes_exists _ _ _ _ _ HB). apply set_env_in_mod; assumption.
Qed.

End ModuleDenotations.


(** ** Local Definitions with a Module Part *)

Section DefinitionModuleDenotations.
  Context {GC : GCtx}.
  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).

(** The environment of a definition with a module part at its value and
    module. *)
Definition dm_env (FM : set_env -> aczel_set) (FU : set_env -> set_module) (ρ : set_env) : set_env :=
  set_env_extend ρ (set_entry_both (FM ρ) (FU ρ)).

Lemma set_env_in_dm : forall Γ A M U FM FU ρ, set_denotes T γ Γ M FM -> set_modexp_denotes T γ Γ (me_lit U) FU ->
    set_env_in T γ Γ ρ -> set_env_in T γ (ce_dm A M U :: Γ) (dm_env FM FU ρ).
Proof.
  intros * HM HU Hρ. split; [exact Hρ |]. exists (FM ρ), (FM ρ), (FM ρ), (FU ρ), (FU ρ), (FU ρ).
  constructor; [reflexivity | reflexivity | exact (set_denotes_exists _ _ _ _ _ HM _ Hρ)
               | apply set_interp_me_lit_iff; exact (set_modexp_denotes_exists _ _ _ _ _ HU _ Hρ)
               | apply set_eq_refl | apply set_eq_refl | exact (set_modexp_denotes_refl _ _ _ _ _ _ HU Hρ) .. ].
Qed.

(** A term under a definition with a module part denotes, with both parts
    substituted, its value at the definition's value and module. *)
Lemma set_denotes_dm_sub : forall Γ A M U X FM FU FX, set_ctx T γ Γ ->
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_dm A M U :: Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˢ sb_extend sb_id (se_dm M (me_lit U)) : ce_dm A M U :: Γ ->
    set_denotes T γ Γ M FM -> set_modexp_denotes T γ Γ (me_lit U) FU -> set_denotes T γ (ce_dm A M U :: Γ) X FX ->
    set_denotes T γ Γ (exp_sub X (sb_extend sb_id (se_dm M (me_lit U)))) (fun ρ => FX (dm_env FM FU ρ)).
Proof.
  intros * HΓ Hc Hσ HM HU HX. apply set_denotes_of_exists; [exact Hfn | exact Hmods | exact HΓ |]. intros ρ Hρ.
  apply (set_interp_single_sub_slot T γ Γ ρ (ce_dm A M U) _ (set_entry_both (FM ρ) (FU ρ))); [exact Hc | exact Hσ | |].
  - split; cbn; [exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) | exact (set_modexp_denotes_exists _ _ _ _ _ HU _ Hρ)].
  - apply (set_denotes_exists _ _ _ _ _ HX). apply set_env_in_dm; assumption.
Qed.

Lemma set_denotes_let_dm : forall Γ A M U B FM FU FB, set_ctx T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ ce_dm A M U :: Γ ->
    set_denotes T γ Γ M FM -> set_modexp_denotes T γ Γ (me_lit U) FU -> set_denotes T γ (ce_dm A M U :: Γ) B FB ->
    set_denotes T γ Γ (a_let (b_def_mod A M U) B) (fun ρ => FB (dm_env FM FU ρ)).
Proof.
  intros * HΓ Hc HM HU HB. apply set_denotes_of_exists; [exact Hfn | exact Hmods | exact HΓ |]. intros ρ Hρ.
  econstructor; [exact Hc | exact (set_denotes_exists _ _ _ _ _ HM _ Hρ)
                | apply set_interp_me_lit_iff; exact (set_modexp_denotes_exists _ _ _ _ _ HU _ Hρ) |].
  apply (set_denotes_exists _ _ _ _ _ HB). apply set_env_in_dm; assumption.
Qed.

End DefinitionModuleDenotations.


(** ** Congruences

    The right-hand side is read in its own context, which the identity
    converts from the left's. *)


Section BodiesAcross.
  Context {GC : GCtx}.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).

(** The body of the right-hand side, read in its own context, is read as
    in the left's: the two contexts extend one by equal extensions. *)
Lemma set_interp_body_across : forall Γ e e' B ρ d d' v w, fn_kinds_unique_ext ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ e :: nil ≈ e' :: nil -> set_env_in T γ Γ ρ -> set_entry_eq γ d d' ->
    set_interp T γ (e :: Γ) (set_env_extend ρ d) B v -> set_interp T γ (e' :: Γ) (set_env_extend ρ d') B w -> set_eq v w.
Proof.
  intros * Hfnx Hx Hρ Ed Hv Hw.
  assert (Hext : ctx_ext_equal (e :: Γ) (e' :: Γ))
    by (exists Γ, (e :: nil), (e' :: nil); constructor; [reflexivity | reflexivity | exact Hx]).
  assert (Eenv : set_env_eq γ (set_env_extend ρ d) (set_env_extend ρ d'))
    by (pose proof (set_env_rel_eq T γ _ _ _ Hρ) as Eρ; intros [| x]; [exact Ed | exact (Eρ x)]).
  exact (set_interp_functional_ext T γ Hfnx Hmods _ _ _ _ Hv _ _ _ Hext Eenv Hw).
Qed.

End BodiesAcross.



End Lets.
