(** * The Rules of Module Expressions in the PER Model

    The congruence, [δ] and [β] rules of module expressions hold in the
    PER model.  Two module expressions are related once each is valid and
    their values are related at related environments ([rel_modexp_of_at]),
    or once each is moved along substitutions as the PER model asks
    ([modexp_sub_rel]) and their values are related at related environments
    ([rel_modexp_of_links]).  An application is valid when its module's
    values lack a parameter of the argument's type ([rel_modexp_under_ctx_app]); a
    literal given its outermost parameter is the literal with the parameter
    instantiated ([rel_modexp_under_ctx_beta]). *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases FunctionCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Modules Require Import MemberTypes ModuleVal Values.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness Require Import VariableCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Related Values make Related Module Expressions *)

Lemma rel_modexp_of_at : forall Γ H H', Γ ⊨ᵐ H ≈ H -> Γ ⊨ᵐ H' ≈ H' ->
    (forall R, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> forall ρ ρ', R ρ ρ' ->
       exists h h', ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h /\ ⟦ H' ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ' ↘ h' /\ per_dmod h h') ->
    Γ ⊨ᵐ H ≈ H'.
Proof.
  intros * [R HR HH] [R2 HR2 HH'] Hat.
  refine (mk_rel_modexp_under_ctx _ _ _ R HR _); intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  pose proof (rel_sub_under_ctx_at' Hσ HΓ' HR _ _ _ _ Hρ Hev Hev') as Hρσ.
  assert (HP' : PER R') by (eapply per_env_PER; exact HΓ').
  assert (Hρρ : R' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  assert (Hρ'ρ' : R' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
  assert (E : R <~> R2) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (rel_modexp_hub _ _ _ _ _ _ _ _ (HH _ _ HΓ' _ _ (rel_sub_under_ctx_refl_left Hσ) _ _ _ _ Hρρ Hev Hev))
    as (h1 & h2 & h3 & h4 & E1 & E2 & E3 & E4 & D1 & D2 & D3 & D4).
  destruct (rel_modexp_hub _ _ _ _ _ _ _ _ (HH' _ _ HΓ' _ _ (rel_sub_under_ctx_refl_right Hσ) _ _ _ _ Hρ'ρ' Hev' Hev'))
    as (g1 & g2 & g3 & g4 & F1 & F2 & F3 & F4 & G1 & G2 & G3 & G4).
  destruct (Hat _ HR _ _ Hρσ) as (h & g & Eh & Eg & Hhg).
  pose proof (functional_eval_modexp _ _ _ _ Eh E3) as ->.
  pose proof (functional_eval_modexp _ _ _ _ Eg F3) as ->.
  apply (mk_rel_modexp h1 h3 g3 g4); try assumption.
  split; [ exact (per_dmod_trans _ _ _ D1 (per_dmod_sym _ _ D3)) |].
  split; [ exact Hhg | exact (per_dmod_sym _ _ G4) ].
Qed.

(** ** Module Expressions along Substitutions *)

(** [H] moved along a semantic substitution: its value at an environment
    against that of [H] at the substitution's value there. *)
Definition modexp_sub_rel (Γ : ctx) (H : modexp) : Prop :=
  forall Γ' R' σ σ' ρ ρσ, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' -> Γ' ⊨ˢ σ ≈ σ' : Γ -> R' ρ ρ ->
    ⟦ σ ⟧s gc_deps ⍮ gc_stack ⍮ ρ ↘ ρσ -> rel_mexp H[σ]ᵐ ρ H ρσ.

(** A valid module expression is so moved. *)
Lemma modexp_sub_rel_of_valid : forall Γ H H', Γ ⊨ᵐ H ≈ H' -> modexp_sub_rel Γ H.
Proof.
  intros * [R HR HH] Γ' R' σ σ' ρ ρσ HΓ' Hσ Hρ Hev.
  destruct (HH _ _ HΓ' _ _ (rel_sub_under_ctx_refl_left Hσ) _ _ _ _ Hρ Hev Hev) as [h1 h2 h3 h4 E1 E2 _ _ (C12 & _)].
  exists h1 h2; assumption.
Qed.

(** The output of a substitution is determined only pointwise. *)
Lemma eval_sub_env_eq : forall σ ρ ρσ ρσ', ⟦ σ ⟧s gc_deps ⍮ gc_stack ⍮ ρ ↘ ρσ -> env_eq ρσ ρσ' ->
    ⟦ σ ⟧s gc_deps ⍮ gc_stack ⍮ ρ ↘ ρσ'.
Proof. intros * Hσ Heq x; rewrite <- (Heq x); exact (Hσ x). Qed.

Lemma env_eq_head : forall ρ m, env_entry ρ 0 = de_term m -> env_eq ρ (ρ↯ ↦ m).
Proof. intros [| e ρ] m He [| x]; cbn in *; try exact He; try reflexivity; destruct x; reflexivity. Qed.

Lemma rel_modexp_of_links : forall Γ H H', ⊨ Γ -> modexp_sub_rel Γ H -> modexp_sub_rel Γ H' ->
    (forall R, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> forall ρ ρ', R ρ ρ' -> rel_mexp H ρ H' ρ') ->
    Γ ⊨ᵐ H ≈ H'.
Proof.
  intros * HΓ L L' Hat.
  destruct (rel_ctx_wf_per_ctx_env HΓ) as [R HR].
  refine (mk_rel_modexp_under_ctx _ _ _ R HR _); intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  pose proof (rel_sub_under_ctx_at' Hσ HΓ' HR _ _ _ _ Hρ Hev Hev') as Hρσ.
  assert (HP' : PER R') by (eapply per_env_PER; exact HΓ').
  assert (Hρρ : R' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  assert (Hρ'ρ' : R' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
  destruct (L _ _ _ _ _ _ HΓ' Hσ Hρρ Hev) as [h1 h2 E1 E2 D12].
  destruct (L' _ _ _ _ _ _ HΓ' (rel_sub_under_ctx_sym Hσ) Hρ'ρ' Hev') as [h4 h3 E4 E3 D43].
  destruct (Hat _ HR _ _ Hρσ) as [g2 g3 F2 F3 D23].
  pose proof (functional_eval_modexp _ _ _ _ F2 E2) as ->; pose proof (functional_eval_modexp _ _ _ _ F3 E3) as ->.
  apply (mk_rel_modexp h1 h2 h3 h4); try assumption.
  split; [ exact D12 | split; [ exact D23 | exact (per_dmod_sym _ _ D43) ] ].
Qed.

(** ** Slots *)

Lemma env_mod_S : forall ρ n, env_mod ρ (S n) = env_mod ρ↯ n.
Proof. intros [| d ρ] n; reflexivity. Qed.

Lemma per_ctx_env_tail_of : forall e Γ R, EF e :: Γ ≈ e :: Γ ∈ per_ctx_env ↘ R ->
    exists R', EF Γ ≈ Γ ∈ per_ctx_env ↘ R' /\ forall ρ ρ', R ρ ρ' -> R' ρ↯ ρ'↯.
Proof.
  intros * HR.
  destruct (per_ctx_env_app_tail (e :: nil) (e :: nil) Γ Γ R eq_refl HR) as [R' HR'].
  exists R'; split; [ exact HR' |].
  intros ρ ρ' Hρ; pose proof (rel_wk_app _ _ _ (rel_wk_shift HR' HR) _ _ Hρ) as H; rewrite !eval_wk_shift in H; exact H.
Qed.

Lemma slot_rel : forall Γ x U, Γ ∋ #x ≔ₘ U ->
    forall R, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> forall ρ ρ', R ρ ρ' -> per_dmod (env_mod ρ x) (env_mod ρ' x).
Proof.
  induction 1 as [U0 Γ0 | U0 A M Γ0 | n U1 Γ0 e Hl IH]; intros R HR ρ ρ' Hρ.
  - destruct (per_ctx_env_tail_of _ _ _ HR) as (R0 & HR0 & _).
    destruct (per_ctx_env_cons_mod_inversion HR0 HR) as [HU ER].
    destruct (proj1 (ER ρ ρ') Hρ) as [Ht H1 _ H3 _].
    exact (tie_mod_rel _ _ _ _ _ _ H1 H3 (HU _ _ Ht)).
  - (* a definition with a module part: its module part, as a slot's *)
    inversion HR; subst.
    match goal with
    | HE : R <~> _, HU : forall ρ ρ', ?T ρ ρ' -> rel_mexp _ _ _ _ |- _ =>
        apply HE in Hρ as [Ht _ _ _ _ _ H1 _ H3 _];
        exact (tie_mod_rel _ _ _ _ _ _ H1 H3 (HU _ _ Ht))
    end.
  - destruct (per_ctx_env_tail_of _ _ _ HR) as (R0 & HR0 & Ht).
    rewrite !env_mod_S; exact (IH _ HR0 _ _ (Ht _ _ Hρ)).
Qed.

Lemma rel_modexp_under_ctx_var : forall Γ x U, ⊨ Γ -> Γ ∋ #x ≔ₘ U -> Γ ⊨ᵐ me_var x ≈ me_var x.
Proof.
  intros * HΓ Hl.
  destruct (rel_ctx_wf_per_ctx_env HΓ) as [R HR].
  refine (mk_rel_modexp_under_ctx _ _ _ R HR _); intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  pose proof (rel_sub_under_ctx_at' Hσ HΓ' HR _ _ _ _ Hρ Hev Hev') as Hρσ.
  pose proof (slot_rel _ _ _ Hl _ HR _ _ Hρσ) as Hd.
  apply (mk_rel_modexp (env_mod ρσ x) (env_mod ρσ x) (env_mod ρ'σ' x) (env_mod ρ'σ' x));
    [ apply eval_sub_mvar; assumption | constructor | constructor | apply eval_sub_mvar; assumption |].
  split; [ exact (per_dmod_trans _ _ _ Hd (per_dmod_sym _ _ Hd)) |].
  split; [ exact Hd | exact (per_dmod_trans _ _ _ (per_dmod_sym _ _ Hd) Hd) ].
Qed.

(** A slot of a valid context holds the weakening of a unit valid in its
    parts, and its value is tied to the value of that unit. *)
Lemma slot_decomp : forall Γ x U, Γ ∋ #x ≔ₘ U -> ⊨ Γ ->
    exists Γ0 U0 φ, Γ ⊨ʷ φ : Γ0 /\ U = gunit_wk U0 φ /\ ⊨ Γ0 /\ Γ0 ⊨ᵘ U0 ≈ U0 /\
      forall R ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> R ρ ρ -> tie_mod (env_mod ρ x) (me_lit U0) (⟪φ⟫ ρ).
Proof.
  induction 1 as [U0 Γ0 | U0 A M Γ0 | n U1 Γ0 e Hl IH]; intros HC.
  - pose proof (rel_ctx_wf_mod_inv HC) as HU.
    exists Γ0, U0, wk_shift; split; [ exact (rel_wk_under_ctx_shift HC) |]; split; [ reflexivity |].
    split; [ exact (rel_ctx_wf_tail HC) |]; split; [ exact HU |].
    intros R ρ HR Hρ.
    destruct (per_ctx_env_tail_of _ _ _ HR) as (R0 & HR0 & _).
    destruct (per_ctx_env_cons_mod_inversion HR0 HR) as [_ ER].
    destruct (proj1 (ER ρ ρ) Hρ) as [_ Hd _ _ _].
    rewrite eval_wk_shift; exact Hd.
  - (* a definition with a module part: its module part, as a slot's *)
    destruct (rel_ctx_wf_dm_inv HC) as (_ & _ & HU).
    exists Γ0, U0, wk_shift; split; [ exact (rel_wk_under_ctx_shift HC) |]; split; [ reflexivity |].
    split; [ exact (rel_ctx_wf_tail HC) |]; split; [ exact HU |].
    intros R ρ HR Hρ.
    rewrite eval_wk_shift.
    inversion HR; subst.
    match goal with HE : R <~> _ |- _ => apply HE in Hρ as [_ _ _ _ _ _ Hd _ _ _]; exact Hd end.
  - destruct (IH (rel_ctx_wf_tail HC)) as (G0 & U0 & φ & Hφ & -> & HG0 & HsU & Ht).
    exists G0, U0, (φ ⊙ wk_shift); split; [| split; [ apply gunit_wk_wk | split; [ exact HG0 | split; [ exact HsU |] ] ] ].
    + destruct (rel_wk_under_ctx_shift HC) as [R1 HR1 R2 HR2 Hs].
      destruct Hφ as [R3 HR3 R4 HR4 Hw].
      assert (E : R2 <~> R3) by (eapply per_ctx_env_right_irrel; eassumption).
      refine (mk_rel_wk_under_ctx _ _ _ R1 HR1 R4 HR4 _).
      destruct Hs as [Hsm Hs]; destruct Hw as [Hwm Hw].
      split; [ apply wk_mono_compose; assumption |].
      intros ρ ρ' Hρ; rewrite !(@eval_wk_compose φ wk_shift _ Hwm Hsm).
      apply Hw, E, Hs, Hρ.
    + intros R ρ HR Hρ.
      destruct (per_ctx_env_tail_of _ _ _ HR) as (R0 & HR0 & Htl).
      destruct Hφ as [_ _ _ _ [Hwm _]].
      rewrite (@eval_wk_compose φ wk_shift _ Hwm wk_mono_shift), eval_wk_shift, env_mod_S.
      exact (Ht _ _ HR0 (Htl _ _ Hρ)).
Qed.

(** The unit of a slot of a valid context is valid. *)
Lemma slot_unit_valid : forall Γ x U, Γ ∋ #x ≔ₘ U -> ⊨ Γ -> Γ ⊨ᵐ me_lit U ≈ me_lit U.
Proof.
  intros * Hl HC.
  destruct (slot_decomp _ _ _ Hl HC) as (Γ0 & U0 & φ & Hφ & -> & HG0 & [HU _ _] & _).
  pose proof (rel_modexp_under_ctx_gsub (gsub_wk _ _ _ Hφ HC HG0) HU) as H.
  cbn [modexp_sub] in H; rewrite gunit_sub_of_wk in H; exact H.
Qed.

Lemma slot_closure_tie : forall Γ x U, Γ ∋ #x ≔ₘ U -> ⊨ Γ ->
    forall R ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> R ρ ρ -> tie_mod (env_mod ρ x) (me_lit U) ρ.
Proof.
  intros * Hl HC R ρ HR Hρ.
  destruct (slot_decomp _ _ _ Hl HC) as (Γ0 & U0 & φ & Hφ & -> & _ & [HU _ _] & Ht).
  pose proof Hφ as [_ _ _ _ [Hwm _]].
  pose proof (modexp_sub_rel_of_valid _ _ _ HU _ _ _ _ _ _ HR (rel_sub_of_wk Hφ) Hρ (@eval_sub_of_wk _ _ φ ρ Hwm)) as Hd.
  cbn [modexp_sub] in Hd; rewrite gunit_sub_of_wk in Hd.
  exact (tie_mod_move _ _ _ _ _ (Ht _ _ HR Hρ) (rel_mexp_sym _ _ _ _ Hd)).
Qed.

(** [δ] for a slot: the slot is its unit. *)
Lemma rel_modexp_under_ctx_delta_slot : forall Γ x U, ⊨ Γ -> Γ ∋ #x ≔ₘ U -> Γ ⊨ᵐ me_var x ≈ me_lit U.
Proof.
  intros * HC Hl.
  pose proof (slot_unit_valid _ _ _ Hl HC) as HU.
  apply rel_modexp_of_at; [ exact (rel_modexp_under_ctx_var _ _ _ HC Hl) | exact HU |].
  intros R HR ρ ρ' Hρ.
  assert (HP : PER R) by (eapply per_env_PER; exact HR).
  destruct (slot_closure_tie _ _ _ Hl HC _ _ HR ltac:(etransitivity; [ exact Hρ | symmetry; exact Hρ ])) as (h & Hh & Hd).
  destruct (unit_chain_at HU HR _ _ Hρ) as [h1 h' Hh1 Hh' Hd'].
  pose proof (functional_eval_modexp _ _ _ _ Hh Hh1) as <-.
  exists (env_mod ρ x), h'; split; [ constructor |]; split; [ exact Hh' | eapply per_dmod_trans; eassumption ].
Qed.

(** ** Applications *)

(** The values of a module expression lack a parameter of type [B]. *)
#[warnings="-cannot-define-projection"]
Record modexp_next_param_at (H : modexp) (B : typ) (ρ : env) : Prop := mk_modexp_next_param_at
  { modexp_next_param_at_mod : dmod
  ; modexp_next_param_at_param : domain
  ; modexp_next_param_at_typ : domain
  ; modexp_next_param_at_lvl : universe_index
  ; modexp_next_param_at_rel : relation domain
  ; modexp_next_param_at_eval_mod : ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ modexp_next_param_at_mod
  ; modexp_next_param_at_next : nextparam modexp_next_param_at_mod modexp_next_param_at_param
  ; modexp_next_param_at_eval_typ : ⟦ B ⟧ ρ ↘ modexp_next_param_at_typ
  ; modexp_next_param_at_per : per_univ_elem modexp_next_param_at_lvl modexp_next_param_at_rel modexp_next_param_at_param modexp_next_param_at_typ }.

Definition modexp_next_param (Γ : ctx) (H : modexp) (B : typ) : Prop :=
  forall R, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> forall ρ, R ρ ρ -> modexp_next_param_at H B ρ.

Lemma rel_modexp_under_ctx_app : forall Γ H H' B N N', Γ ⊨ᵐ H ≈ H' -> Γ ⊨ N ≈ N' : B ->
    modexp_next_param Γ H B -> Γ ⊨ᵐ me_app H N ≈ me_app H' N'.
Proof.
  intros * [R HR HH] HN Hl.
  pose proof HN as [RN HRN iN HNgen].
  refine (mk_rel_modexp_under_ctx _ _ _ R HR _); intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  pose proof (rel_sub_under_ctx_at' Hσ HΓ' HR _ _ _ _ Hρ Hev Hev') as Hρσ.
  assert (HP : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρσσ : R ρσ ρσ) by (etransitivity; [ exact Hρσ | symmetry; exact Hρσ ]).
  destruct (rel_modexp_hub _ _ _ _ _ _ _ _ (HH _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev'))
    as (h1 & h2 & h3 & h4 & E1 & E2 & E3 & E4 & D1 & D2 & D3 & D4).
  destruct (HNgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [RB [[b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 (B12 & B23 & B34)] [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 (N12 & N23 & N34)]]].
  destruct (Hl _ HR _ Hρσσ) as [h a b i Ra Eh Hp Eb HRa].
  pose proof (functional_eval_modexp _ _ _ _ Eh E2) as ->.
  pose proof (functional_eval_exp _ _ _ _ Eb Hb2) as ->.
  assert (HPB : PER RB) by (eapply per_elem_PER; exact B23).
  assert (HB22 : per_univ_elem iN RB b2 b2) by (etransitivity; [ exact B23 | symmetry; exact B23 ]).
  assert (HPa : PER Ra) by (eapply per_elem_PER; exact HRa).
  assert (Eab : Ra <~> RB) by (eapply per_univ_elem_left_irrel; [ exact HRa | exact HB22 ]).
  hnf in N34, B34.
  assert (Happ : forall g c, per_dmod g h2 -> RB c n2 -> exists r r', $ᵐ| g & c | gc_deps ⍮ gc_stack ↘ r /\
              $ᵐ| h2 & n2 | gc_deps ⍮ gc_stack ↘ r' /\ per_dmod r r').
  { intros g c Hg Hc.
    destruct (per_dmod_appm _ _ _ (per_dmod_sym _ _ Hg) Hp) as (ig & Rg & ag & _ & HRg & Hap).
    assert (E : Rg <~> Ra) by (eapply per_univ_elem_right_irrel; [ exact HRg | exact HRa ]).
    destruct (Hap n2 c ltac:(apply E, Eab; symmetry; exact Hc)) as (r' & r & Hr' & Hr & Hrr).
    exists r, r'; repeat split; [ exact Hr | exact Hr' | exact (per_dmod_sym _ _ Hrr) ]. }
  assert (G1 : per_dmod h1 h2) by (eapply per_dmod_trans; [ exact D1 | apply per_dmod_sym; exact D2 ]).
  assert (G3 : per_dmod h3 h2) by (apply per_dmod_sym; exact D2).
  assert (G4 : per_dmod h4 h2) by (eapply per_dmod_trans; [ exact D4 | apply per_dmod_sym; exact D2 ]).
  destruct (Happ _ _ G1 N12) as (r1 & r2 & R1 & R2 & C1).
  destruct (Happ _ _ G3 ltac:(symmetry; exact N23)) as (r3 & r2' & R3 & R2' & C3).
  destruct (Happ _ _ G4 ltac:(etransitivity; [ symmetry; exact N34 | symmetry; exact N23 ])) as (r4 & r2'' & R4 & R2'' & C4).
  pose proof (functional_eval_appm _ _ _ _ R2' R2) as ->.
  pose proof (functional_eval_appm _ _ _ _ R2'' R2) as ->.
  apply (mk_rel_modexp r1 r2 r3 r4); try (econstructor; eassumption).
  split; [ exact C1 |]; split; [ apply per_dmod_sym; exact C3 |].
  eapply per_dmod_trans; [ exact C3 | apply per_dmod_sym; exact C4 ].
Qed.

(** Lacking a parameter moves along related module expressions. *)
Lemma modexp_next_param_resp : forall Γ H H' B, Γ ⊨ᵐ H ≈ H' -> modexp_next_param Γ H' B -> modexp_next_param Γ H B.
Proof.
  intros * HH Hl R HR ρ Hρ.
  destruct (rel_modexp_at _ _ _ _ _ HH HR _ _ Hρ) as (h & h' & Eh & Eh' & Hhh).
  destruct (Hl _ HR _ Hρ) as [h0 a' b i RB Eh0 Hp' Eb HRB].
  pose proof (functional_eval_modexp _ _ _ _ Eh0 Eh') as ->.
  destruct (per_dmod_appm _ _ _ (per_dmod_sym _ _ Hhh) Hp') as (j & Ra & a & Hp & HRa & _).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ HRa)) HRB) as (R2 & HR2 & _).
  exists h a b j R2; eassumption.
Qed.

(** ** [β] *)

(** A unit valid in its parts, under one parameter fewer. *)
Lemma rel_unit_wf_unabs1 : forall Γ Δ X D, rel_unit_wf Γ (gu_mk (Δ ++ ce_ass X :: nil) D) -> rel_unit_wf (Γ ▹ X) (gu_mk Δ D).
Proof.
  intros * HU; inversion HU as [? Δ0 Φ Φx HΔ Hx Hs Hsx HC Ho | ? Δ0 E HΔ HC HE]; subst.
  - destruct (tele_ass_app_inv _ _ HΔ) as [HΔ' _].
    rewrite <- app_assoc in Hx, HC; cbn [List.app] in Hx, HC.
    apply (rel_unit_wf_body _ _ _ Φx); try assumption.
    intros k Ψ H Hk; pose proof (Ho _ _ _ Hk) as H1; rewrite <- app_assoc in H1; exact H1.
  - destruct (tele_ass_app_inv _ _ HΔ) as [HΔ' _].
    rewrite <- app_assoc in HC, HE; cbn [List.app] in HC, HE.
    apply rel_unit_wf_alias; assumption.
Qed.

Lemma lit_params_val : forall ρ Δ X D,
    ⟦ me_lit (gu_mk (Δ ++ ce_ass X :: nil) D) ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ dm_local (Δ ++ ce_ass X :: nil) D ρ.
Proof. intros; apply eval_me_lit, close_unsat; rewrite length_app; cbn; lia. Qed.

Lemma lit_params_lacks : forall Γ Δ X D i, Γ ⊨ X : Typeω@i -> modexp_next_param Γ (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) X.
Proof.
  intros * HX R HR ρ Hρ.
  destruct (rel_exp_of_typ_inversion_simple_at HR HX _ _ Hρ) as (a & a' & Ha & Ha' & [Ra HRa]).
  pose proof (functional_eval_exp _ _ _ _ Ha Ha') as <-.
  exists (dm_local (Δ ++ ce_ass X :: nil) D ρ) a a i Ra; [ apply lit_params_val | constructor; exact Ha | exact Ha | exact HRa ].
Qed.

(** The closures of related literals with an outermost parameter, given
    related arguments for it. *)
Lemma rel_lit_arg : forall Γ Δ X D Δ' X' D' R,
    Γ ⊨ᵐ me_lit (gu_mk (Δ ++ ce_ass X :: nil) D) ≈ me_lit (gu_mk (Δ' ++ ce_ass X' :: nil) D') ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> forall ρ ρ' a c c', R ρ ρ' -> ⟦ X ⟧ ρ ↘ a -> per_head X X' ρ ρ' c c' ->
    rel_mexp (me_lit (gu_mk Δ D)) (ρ ↦ c) (me_lit (gu_mk Δ' D')) (ρ' ↦ c').
Proof.
  intros * HU HR * Hρ Ha Hc.
  destruct (unit_chain_at HU HR _ _ Hρ) as [h h' Hh Hh' Hd].
  pose proof (functional_eval_modexp _ _ _ _ Hh (lit_params_val _ _ _ _)) as ->.
  pose proof (functional_eval_modexp _ _ _ _ Hh' (lit_params_val _ _ _ _)) as ->.
  destruct (per_dmod_appm _ _ _ Hd (nextparam_local _ _ _ _ _ Ha)) as (i & RX & a' & Hp' & HRX & Hap).
  inversion Hp' as [Δ0 A ? ? ? Ha' Hl | |]; subst.
  apply app_inj_tail in Hl as [-> [= ->]].
  destruct (Hap c c' (Hc _ _ _ _ Ha Ha' HRX)) as (hc & hc' & Hc1 & Hc2 & Hcc).
  inversion Hc1; subst; inversion Hc2; subst.
  repeat match goal with Hl : _ ++ _ = _ ++ _ |- _ => apply app_inj_tail in Hl as [-> [= ->]] end.
  exists hc hc'; [ apply eval_me_lit; assumption | apply eval_me_lit; assumption | exact Hcc ].
Qed.

Section Beta.
  Variables (Γ Δ : ctx) (X : typ) (D : moddef) (N : exp) (i : nat).
  Hypotheses (HΓ : ⊨ Γ)
    (HU : Γ ⊨ᵐ me_lit (gu_mk (Δ ++ ce_ass X :: nil) D) ≈ me_lit (gu_mk (Δ ++ ce_ass X :: nil) D))
    (HL : modexp_sub_rel (Γ ▹ X) (me_lit (gu_mk Δ D))) (HX : Γ ⊨ X : Typeω@i) (HN : Γ ⊨ N : X).

  Let gid : gsub Γ (Id,,N) (Γ ▹ X).
  Proof. eapply gsub_ass; [ constructor; exact HΓ | exact HX | rewrite exp_sub_id; exact HN ]. Qed.

  (** The instance at an environment, against the literal under one
      parameter fewer at the argument's value. *)
  Lemma beta_link : forall R ρ n, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> R ρ ρ -> ⟦ N ⟧ ρ ↘ n ->
      rel_mexp (me_lit (gu_mk Δ D)[Id,,N]ᵘ) ρ (me_lit (gu_mk Δ D)) (ρ ↦ n).
  Proof.
    intros * HR Hρ Hn.
    exact (HL _ _ _ _ _ _ HR (gsub_valid gid) Hρ (eval_sub_extend _ _ _ _ _ (eval_sub_id _) Hn)).
  Qed.

  (** The values of the literal under one parameter fewer, at related
      arguments. *)
  Lemma beta_mid : forall R ρ ρ' n n', EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> R ρ ρ' -> ⟦ N ⟧ ρ ↘ n -> ⟦ N ⟧ ρ' ↘ n' ->
      rel_mexp (me_lit (gu_mk Δ D)) (ρ ↦ n) (me_lit (gu_mk Δ D)) (ρ' ↦ n').
  Proof.
    intros * HR Hρ Hn Hn'.
    destruct (rel_exp_of_typ_inversion_simple_at HR HX _ _ Hρ) as (a & a' & Ha & Ha' & _).
    destruct (rel_exp_under_ctx_simple_at HR HN _ _ Hρ) as (m & m' & Hm & Hm' & Hmm).
    functional_eval_rewrite_clear.
    exact (rel_lit_arg _ _ _ _ _ _ _ _ HU HR _ _ _ _ _ Hρ Ha Hmm).
  Qed.

  Lemma rel_lit_beta : Γ ⊨ᵐ me_lit (gu_mk Δ D)[Id,,N]ᵘ ≈ me_lit (gu_mk Δ D)[Id,,N]ᵘ.
  Proof.
    destruct (gsub_props gid) as [Hτ Hlk].
    destruct (rel_ctx_wf_per_ctx_env HΓ) as [R HR].
    assert (HP : PER R) by (eapply per_env_PER; exact HR).
    assert (Ls : modexp_sub_rel Γ (me_lit (gu_mk Δ D)[Id,,N]ᵘ)).
    { intros Γ' R' σ σ' ρ ρσ HΓ' Hσ Hρ Hev.
      pose proof (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HR _ _ _ _ Hρ Hev Hev) as Hρσ.
      destruct (rel_exp_under_ctx_simple_at HR HN _ _ Hρσ) as (n & _ & Hn & _ & _).
      destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_ext_typ _ _ _ HΓ HX)) as [RX HRX].
      destruct (Hlk _ _ HΓ' _ _ Hσ _ HRX _ _ Hρ Hev) as (e1 & He1 & Le1).
      pose proof (Le1 _ (eval_sub_extend _ _ _ _ _ (eval_sub_id _) Hn)) as He12.
      (* the head of [e1] is a term: read it as an extension *)
      destruct (He1 0) as (m & Hm0 & Hm).
      pose proof (eval_sub_env_eq _ _ _ _ He1 (env_eq_head _ _ Hm0)) as He1'.
      pose proof (HL _ _ _ _ _ _ HΓ' (gsub_compose gid _ _ _ Hσ) Hρ He1') as L1.
      change (me_lit (gu_mk Δ D)[Id,,N]ᵘ) with ((me_lit (gu_mk Δ D))[Id,,N]ᵐ); rewrite modexp_sub_sub.
      destruct (per_ctx_env_cons_clean_inversion HR HRX) as (j & hr & Hhr & EX).
      apply EX in He12 as [Ht Hh]; cbn in Ht.
      assert (Ehd : e1 0 = m) by (unfold env_var; rewrite Hm0; reflexivity).
      rewrite Ehd in Hh.
      destruct (rel_exp_of_typ_inversion_simple_at HR HX _ _ Ht) as (a & a' & Ha & Ha' & _).
      destruct (Hhr _ _ Ht) as [x1 x2 Hx1 Hx2 HRx].
      assert (Hc : per_head X X e1↯ ρσ m n) by (eapply per_head_of; [ exact Hx1 | exact Hx2 | exact HRx | exact Hh ]).
      pose proof (rel_lit_arg _ _ _ _ _ _ _ _ HU HR _ _ _ m n Ht Ha Hc) as Hmid.
      pose proof (beta_link _ _ _ HR Hρσ Hn) as L2.
      exact (rel_mexp_trans _ _ _ _ _ _ L1 (rel_mexp_trans _ _ _ _ _ _ Hmid (rel_mexp_sym _ _ _ _ L2))). }
    apply rel_modexp_of_links; [ exact HΓ | exact Ls | exact Ls |].
    intros R' HR' ρ ρ' Hρ.
    assert (E : R' <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
    apply E in Hρ.
    assert (Hρρ : R ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
    assert (Hρ'ρ' : R ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
    destruct (rel_exp_under_ctx_simple_at HR HN _ _ Hρ) as (n & n' & Hn & Hn' & _).
    exact (rel_mexp_trans _ _ _ _ _ _ (beta_link _ _ _ HR Hρρ Hn)
             (rel_mexp_trans _ _ _ _ _ _ (beta_mid _ _ _ _ _ HR Hρ Hn Hn') (rel_mexp_sym _ _ _ _ (beta_link _ _ _ HR Hρ'ρ' Hn')))).
  Qed.

  (** A literal given its outermost parameter is the literal under the
      other parameters with the argument for it. *)
  Lemma rel_modexp_under_ctx_beta : Γ ⊨ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) N ≈ me_lit (gu_mk Δ D)[Id,,N]ᵘ.
  Proof.
    apply rel_modexp_of_at.
    - eapply rel_modexp_under_ctx_app; [ exact HU | exact HN | eapply lit_params_lacks; exact HX ].
    - exact rel_lit_beta.
    - intros R HR ρ ρ' Hρ.
      assert (HP : PER R) by (eapply per_env_PER; exact HR).
      assert (Hρρ : R ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
      assert (Hρ'ρ' : R ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
      destruct (rel_exp_under_ctx_simple_at HR HN _ _ Hρ) as (n & n' & Hn & Hn' & _).
      destruct (beta_mid _ _ _ _ _ HR Hρ Hn Hn') as [hc hc' Hc Hc' Hcc].
      destruct (beta_link _ _ _ HR Hρ'ρ' Hn') as [g hc'' Hg Hc'' Hgc].
      pose proof (functional_eval_modexp _ _ _ _ Hc'' Hc') as ->.
      exists hc, g; split; [| split; [ exact Hg | exact (per_dmod_trans _ _ _ Hcc (per_dmod_sym _ _ Hgc)) ] ].
      econstructor; [ apply lit_params_val | exact Hn | apply eval_appm_local, eval_me_lit_iff; exact Hc ].
  Qed.
End Beta.

Lemma rel_modexp_under_ctx_beta_alias0 : forall Γ E, Γ ⊨ᵐ E ≈ E -> Γ ⊨ᵐ me_lit (gu_mk nil (md_alias E)) ≈ E.
Proof.
  intros * [R HR HE].
  refine (mk_rel_modexp_under_ctx _ _ _ R HR _); intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HE _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [e1 e2 e3 e4 E1 E2 E3 E4 Ch].
  apply (mk_rel_modexp e1 e2 e3 e4); [ cbn; rewrite gunit_sub_mk; cbn; apply eval_me_lit, eval_close_alias0; exact E1
                                  | apply eval_me_lit, eval_close_alias0; exact E2 | exact E3 | exact E4 | exact Ch ].
Qed.

End Fixed_GCtx.
