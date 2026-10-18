(** * Related Closures of Units

    The closures of two related units are related ([rel_unit_body],
    [rel_unit_alias]), and the closure of a unit moved along a substitution is
    related to the closure of the unit over the substituted environment
    ([unit_sub_link]).  A body is walked entry by entry as written, each entry
    read in the environment the expansion before it makes; a local open is
    read as the entries it generates, whose kinds come from the kinds of its
    target ([kinds_ok]). *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping GlobalPaths MemberLemmas DescTyping.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases FunctionCases UniverseCases SubstitutionCases LetCases UnitCases InstanceCases MemberReps
  ModuleVal ModuleSem ValidUnit.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules Kinds KindsTyping KindsEval KindsPER.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.

(** ** Environments of the Generated Entries *)

Lemma eval_entry_reloc : forall ρ Φ y E ρ',
    ⟦ gm_ext Φ y E ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' <->
    exists ρ1, ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 /\ ⟦ gm_ext gm_nil y E ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ1 ↘ ρ'.
Proof.
  intros; split.
  - intros He; inversion He; subst; eexists; split; try eassumption;
      first [ apply eval_benv_def; [ constructor | eassumption ] | apply eval_benv_mod; [ constructor | eassumption ] ].
  - intros (ρ1 & H1 & H2); inversion H2; subst;
      match goal with Hn : ⟦ gm_nil ⟧ᵇ _ ⍮ _ ⍮ ρ1 ↘ ?r |- _ => inversion Hn; subst end; econstructor; eassumption.
Qed.

Lemma eval_gens_split : forall gs Φ k ρ ρ2,
    ⟦ gens_append Φ k gs ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ2 <->
    exists ρ1, ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 /\ ⟦ gens_append gm_nil k gs ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ1 ↘ ρ2.
Proof.
  induction gs as [| g gs IH]; intros; cbn [gens_append].
  - split; [ intros He; exists ρ2; split; [ exact He | constructor ] | intros (ρ1 & H1 & H2); inversion H2; subst; exact H1 ].
  - destruct (ig_entry g) as [d E]; rewrite IH.
    split.
    + intros (ρ1' & H1 & H2); apply eval_entry_reloc in H1 as (ρ1 & H1a & H1b).
      exists ρ1; split; [ exact H1a |]; apply IH; exists ρ1'; split; assumption.
    + intros (ρ1 & H1 & H2); apply IH in H2 as (ρm & Hm & H2); exists ρm; split; [| exact H2 ].
      apply eval_entry_reloc; exists ρ1; split; assumption.
Qed.

(** A body without opens adds as many entries as it binds. *)
Lemma eval_benv_nopens_app : forall ρ Φ ρ', ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' -> gm_nopens Φ = 0 ->
    exists X, ρ' = X ++ ρ /\ List.length X = gm_binders Φ.
Proof.
  intros * Hev; induction Hev; intros Hn; cbn in Hn |- *; try discriminate.
  - exists nil; split; reflexivity.
  - destruct (IHHev Hn) as (X & -> & HX); exists (de_term m :: X); cbn; split; [ reflexivity | congruence ].
  - destruct (IHHev Hn) as (X & -> & HX); eexists (_ :: X); cbn; split; [ reflexivity | congruence ].
Qed.

(** The first [k] entries an open generates, as a prefix of all of them. *)
Lemma gm_dropn_gens : forall gs Φ k n, n <= List.length gs ->
    gm_dropn n (gens_append Φ k gs) = gens_append Φ k (List.firstn (List.length gs - n) gs).
Proof.
  induction gs as [| g gs IH] using rev_ind; intros * Hn; cbn [List.length] in *.
  - destruct n; [| lia ]; reflexivity.
  - rewrite length_app in Hn |- *; cbn [List.length] in *.
    destruct n as [| n].
    + rewrite Nat.sub_0_r, firstn_all2 by (rewrite length_app; cbn; lia); destruct (gs ++ g :: nil); reflexivity.
    + rewrite gens_append_snoc; cbn [gm_dropn].
      replace (List.length gs + 1 - S n) with (List.length gs - n) by lia.
      rewrite IH by lia; rewrite firstn_app, (proj2 (Nat.sub_0_le (List.length gs - n) (List.length gs)) ltac:(lia)).
      cbn [List.firstn]; rewrite app_nil_r; reflexivity.
Qed.

(** ** Walking along a Substitution

    [sub_walk_inv Γ' Γ σ Ψ ρl ρr]: [ρl] is an environment of [Ψ] moved along [σ]
    ([tele_sub Ψ σ ++ Γ']), and [σ] lifted over [Ψ] evaluates there to an
    environment related to [ρr], one of [Ψ ++ Γ]. *)
#[warnings="-cannot-define-projection"]
Record sub_walk_inv (Γ' Γ : ctx) (σ : sub) (Ψ : ctx) (ρl ρr : env) : Prop := mk_sub_walk_inv
  { swi_left_rel : relation env
  ; swi_right_rel : relation env
  ; swi_left_per : EF tele_sub Ψ σ ++ Γ' ≈ tele_sub Ψ σ ++ Γ' ∈ per_ctx_env ↘ swi_left_rel
  ; swi_right_per : EF Ψ ++ Γ ≈ Ψ ++ Γ ∈ per_ctx_env ↘ swi_right_rel
  ; swi_sub : (tele_sub Ψ σ ++ Γ') ⊨ˢ sb_qn (List.length Ψ) σ ≈ sb_qn (List.length Ψ) σ : Ψ ++ Γ
  ; swi_left : swi_left_rel ρl ρl
  ; swi_link : exists ρm, ⟦ sb_qn (List.length Ψ) σ ⟧s ρl ↘ ρm /\ swi_right_rel ρm ρr }.

Lemma sub_walk_init : forall Γ' Γ σ σ' R' R ρ ρσ,
    Γ' ⊨ˢ σ ≈ σ' : Γ ->
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    R' ρ ρ -> ⟦ σ ⟧s ρ ↘ ρσ ->
    sub_walk_inv Γ' Γ σ nil ρ ρσ.
Proof.
  intros * Hσ HΓ' HΓ Hρ Hev.
  pose proof (rel_sub_under_ctx_refl_left Hσ) as Hσσ.
  econstructor; [ exact HΓ' | exact HΓ | exact Hσσ | exact Hρ |].
  exists ρσ; split; [ exact Hev |].
  eapply (rel_sub_under_ctx_at' Hσσ HΓ' HΓ); eassumption.
Qed.

Lemma sub_walk_right : forall Γ' Γ σ Ψ ρl ρr, sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    exists Rr, EF Ψ ++ Γ ≈ Ψ ++ Γ ∈ per_ctx_env ↘ Rr /\ Rr ρr ρr.
Proof.
  intros * [Rl Rr _ HΓr _ _ [ρm [_ Hmr]]].
  assert (HPr : PER Rr) by (eapply per_env_PER; exact HΓr).
  exists Rr; split; [ exact HΓr | etransitivity; [ symmetry; exact Hmr | exact Hmr ] ].
Qed.

(** The two values of an assumption's type are related, and so are the
    extended environments, at any related pair of values. *)
Lemma sub_walk_ass : forall Γ' Γ σ Ψ A i ρl ρr,
    sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    Ψ ++ Γ ⊨ A : Typeω@i ->
    exists R, PER.Definitions.rel_typ i A[sb_qn (List.length Ψ) σ] ρl A ρr R /\
      forall c c', R c c' -> sub_walk_inv Γ' Γ σ (Ψ ▹ A) (ρl ↦ c) (ρr ↦ c').
Proof.
  intros * [Rl Rr HΓl HΓr Hsub Hl [ρm [Hm Hmr]]] HA.
  set (τ := sb_qn (List.length Ψ) σ) in *.
  pose proof (rel_exp_of_typ_inversion HA) as [R0 [HΓ0 HAgen]].
  assert (HPl : PER Rl) by (eapply per_env_PER; exact HΓl).
  assert (HPr : PER Rr) by (eapply per_env_PER; exact HΓr).
  destruct (HAgen _ _ HΓl _ _ Hsub _ _ _ _ Hl Hm Hm) as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hc1].
  destruct (HAgen _ _ HΓr _ _ (rel_sub_id (ex_intro _ _ HΓr)) _ _ _ _ Hmr (eval_sub_id _) (eval_sub_id _))
    as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hc2].
  rewrite exp_sub_id in Hb1, Hb4.
  functional_eval_rewrite_clear.
  assert (H14 : Dom a1 ≈ b3 ∈ per_univ i)
    by (destruct Hc1 as [H12 _]; destruct Hc2 as [_ [H23 _]]; etransitivity; eassumption).
  destruct H14 as [R HR].
  destruct Hc2 as [_ [[R2 HR2] _]].
  exists R; split; [ econstructor; eassumption |].
  intros c c' Hcc'.
  assert (HRP : PER R) by (eapply per_elem_PER; eassumption).
  assert (Hcc : R c c) by (etransitivity; [ exact Hcc' | symmetry; exact Hcc' ]).
  pose proof (per_ctx_env_of_typ_sub HΓl Hsub HA) as HΓl'.
  pose proof (per_ctx_env_of_typ HΓr HA) as HΓr'.
  assert (Hl' : per_env_extend A[τ] A[τ] Rl (ρl ↦ c) (ρl ↦ c))
    by (eapply (per_env_extend_sub_intro HΓl Hsub HA); eassumption).
  destruct (rel_sub_under_ctx_q_at HΓl HΓr' Hsub HA _ _ _ _ _ _ Hl' Hm Hm) as [s [s' [Hs [_ Hch]]]].
  assert (Hmr' : per_env_extend A A Rr (ρm ↦ c) (ρr ↦ c')).
  { apply per_env_extend_intro'; [ exact Hmr |].
    eapply per_head_of; [ exact Ha2 | exact Hb3 | exact HR2 |].
    eapply (per_univ_elem_left_irrel _ _ _ _ _ _ _ HR HR2); exact Hcc'. }
  econstructor; [ exact HΓl' | exact HΓr' | exact (rel_sub_under_ctx_q Hsub HA) | exact Hl' |].
  exists (s ↦ c); split; [ exact Hs |].
  assert (HPr' : PER (per_env_extend A A Rr)) by (eapply per_env_PER; exact HΓr').
  etransitivity; [| exact Hmr' ].
  destruct Hch as [_ [H1 _]]; exact H1.
Qed.

(** A definition's types and values along the walk, and the extended
    invariant at any values of its two sides. *)
Lemma sub_walk_def : forall Γ' Γ σ Ψ A i M ρl ρr,
    sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    Ψ ++ Γ ⊨ A : Typeω@i ->
    Ψ ++ Γ ⊨ M : A ->
    exists j R, PER.Definitions.rel_typ j A[sb_qn (List.length Ψ) σ] ρl A ρr R /\
      PER.Definitions.rel_elem M[sb_qn (List.length Ψ) σ] ρl M ρr R /\
      forall m m', ⟦ M[sb_qn (List.length Ψ) σ] ⟧ ρl ↘ m -> ⟦ M ⟧ ρr ↘ m' ->
        sub_walk_inv Γ' Γ σ (Ψ ▸ A ≔ M) (ρl ↦ m) (ρr ↦ m').
Proof.
  intros * [Rl Rr HΓl HΓr Hsub Hl [ρm [Hm Hmr]]] HA HM.
  set (τ := sb_qn (List.length Ψ) σ) in *.
  assert (HPl : PER Rl) by (eapply per_env_PER; exact HΓl).
  assert (HPr : PER Rr) by (eapply per_env_PER; exact HΓr).
  pose proof HM as [R0 HΓ0 j HMgen].
  destruct (HMgen _ _ HΓl _ _ Hsub _ _ _ _ Hl Hm Hm)
    as [R1 [[a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hac] [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmc]]].
  destruct (HMgen _ _ HΓr _ _ (rel_sub_id (ex_intro _ _ HΓr)) _ _ _ _ Hmr (eval_sub_id _) (eval_sub_id _))
    as [R2 [[b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbc] [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnc]]].
  rewrite exp_sub_id in Hb1, Hb4, Hn1, Hn4.
  functional_eval_rewrite_clear.
  destruct Hac as [Ha12 _]; destruct Hbc as [_ [Hab3 _]].
  destruct Hmc as [Hm12 _]; destruct Hnc as [_ [Hmn3 _]].
  assert (Hu : Dom a1 ≈ b3 ∈ per_univ j) by (etransitivity; eexists; eassumption).
  destruct Hu as [R HR].
  pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR Ha12) as E1.
  pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ Hab3 HR) as E2.
  assert (HRP : PER R) by (eapply per_elem_PER; eassumption).
  assert (Hmn : R m1 n3) by (etransitivity; [ apply E1; exact Hm12 | apply E2; exact Hmn3 ]).
  exists j, R; split; [ econstructor; eassumption |]; split; [ econstructor; eassumption |].
  intros m m' Hm' Hm''.
  functional_eval_rewrite_clear.
  pose proof (per_ctx_env_of_def_sub HΓl Hsub HA HM) as HΓl'.
  pose proof (per_ctx_env_of_def HΓr HA HM) as HΓr'.
  pose proof (rel_exp_of_typ_sub_simple HΓl Hsub HA) as HSl.
  pose proof (rel_exp_under_ctx_sub_simple HΓl Hsub HM) as HMl.
  pose proof (rel_exp_of_typ_inversion_simple_at HΓr HA) as HSr.
  pose proof (rel_exp_under_ctx_simple_at HΓr HM) as HMr.
  assert (Ha11 : per_univ_elem j R a1 a1) by (etransitivity; [ exact HR | symmetry; exact HR ]).
  assert (Hb33 : per_univ_elem j R b3 b3) by (etransitivity; [ symmetry; exact HR | exact HR ]).
  assert (Hc : per_head A[τ] A[τ] ρl ρl m1 m1)
    by (eapply per_head_of; [ exact Ha1 | exact Ha1 | exact Ha11 | etransitivity; [ exact Hmn | symmetry; exact Hmn ] ]).
  assert (Hl' : per_env_extend_def A[τ] M[τ] Rl (ρl ↦ m1) (ρl ↦ m1))
    by (eapply per_env_extend_def_intro; [ exact HPl | exact HSl | exact HMl | exact Hl | exact Hc | exact Hm1 | exact Hc ]).
  destruct (rel_sub_q_entry HΓl' HΓr Hsub _ _ Hl' Hm) as [t [Hq Htm]].
  assert (Htr : Rr t ρr) by (etransitivity; eassumption).
  assert (Hh : per_head A A ρm ρr m1 n3)
    by (eapply per_head_of; [ exact Ha2 | exact Hb3 | exact Hab3 | apply E2; exact Hmn ]).
  assert (Hh' : per_head A A t ρr m1 n3).
  { eapply (per_head_of_typ_resp HΓr HA); [| exact Hh ].
    apply rel_chain_4; [ exact Htr | symmetry; exact Hmr | exact Hmr ]. }
  assert (Hext : per_env_extend A A Rr (t ↦ m1) (ρr ↦ n3)) by (apply per_env_extend_intro'; assumption).
  assert (Tr : def_tie A M (ρr ↦ n3)).
  { exists n3; split; [ exact Hn3 |].
    eapply per_head_of; [ exact Hb3 | exact Hb3 | exact Hb33 | etransitivity; [ symmetry; exact Hmn | exact Hmn ] ]. }
  assert (HPe : PER (per_env_extend A A Rr)) by (eapply per_env_PER; eapply per_ctx_env_of_typ; eassumption).
  assert (Tl : def_tie A M (t ↦ m1)) by (eapply (def_tie_resp HPr HSr HMr); [ symmetry; exact Hext | exact Tr ]).
  econstructor; [ exact HΓl' | exact HΓr' | exact (rel_sub_under_ctx_q_def Hsub HA HM) | exact Hl' |].
  exists (t ↦ m1); split; [ exact Hq |].
  constructor; [ exact Hext | assumption | assumption ].
Qed.

(** A nested unit along the walk: its two closures are related, and so are
    the environments they extend. *)
Lemma sub_walk_mod : forall Γ' Γ σ Ψ U ρl ρr,
    sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    Ψ ++ Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    exists hl hr, ⟦ me_lit U[sb_qn (List.length Ψ) σ]ᵘ ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρl ↘ hl /\
      ⟦ me_lit U ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρr ↘ hr /\ per_dmod hl hr /\
      sub_walk_inv Γ' Γ σ (Ψ ▹ₘ U) (ρl ↦ᵐ hl) (ρr ↦ᵐ hr).
Proof.
  intros * [Rl Rr HΓl HΓr Hsub Hl [ρm [Hm Hmr]]] HU.
  set (τ := sb_qn (List.length Ψ) σ) in *.
  assert (HPr : PER Rr) by (eapply per_env_PER; exact HΓr).
  assert (HPd : PER per_dmod) by typeclasses eauto.
  destruct (unit_sub_chain HΓl Hsub HU _ _ _ _ Hl Hm Hm) as ([hl hm Hhl Hhm Hlm] & _).
  destruct (unit_chain_at HU HΓr _ _ Hmr) as [hm' hr Hhm' Hhr Hmr'].
  pose proof (functional_eval_modexp _ _ _ _ Hhm Hhm') as <-.
  assert (Hlr : per_dmod hl hr) by (etransitivity; eassumption).
  exists hl, hr; split; [ exact Hhl | split; [ exact Hhr | split; [ exact Hlr |] ] ].
  pose proof (per_ctx_env_of_mod_sub HΓl Hsub HU) as HΓl'.
  pose proof (per_ctx_env_of_mod HΓr HU) as HΓr'.
  assert (Hll : per_dmod hl hl) by (etransitivity; [ exact Hlr | symmetry; exact Hlr ]).
  assert (Hrr : per_dmod hr hr) by (etransitivity; [ symmetry; exact Hlr | exact Hlr ]).
  assert (Hl' : env_ext_mod U[τ]ᵘ U[τ]ᵘ Rl (ρl ↦ᵐ hl) (ρl ↦ᵐ hl))
    by (unfold extend_env_mod, env_mod; cbn [drop_env tl nth_error env_entry hd];
        repeat split; try assumption; exists hl; split; assumption).
  destruct (rel_sub_q_entry HΓl' HΓr Hsub _ _ Hl' Hm) as [t [Hq Htm]].
  assert (Htr : Rr t ρr) by (etransitivity; eassumption).
  destruct (unit_chain_at HU HΓr _ _ Htr) as [ht hr' Hht Hhr' Htr'].
  pose proof (functional_eval_modexp _ _ _ _ Hhr Hhr') as <-.
  econstructor; [ exact HΓl' | exact HΓr' | exact (rel_sub_under_ctx_q_mod Hsub HU) | exact Hl' |].
  exists (env_entry (ρl ↦ᵐ hl) 0 :: t); split; [ exact Hq |].
  unfold extend_env_mod, env_mod; cbn [drop_env tl nth_error env_entry hd].
  repeat split; try assumption;
    solve [ exists hr; split; assumption | exists ht; split; [ exact Hht | etransitivity; [ exact Hlr | symmetry; exact Htr' ] ] ].
Qed.

(** An alias's targets along the walk are related. *)
Lemma sub_walk_alias : forall Γ' Γ σ Ψ E ρl ρr,
    sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    Ψ ++ Γ ⊨ᵐ E ≈ E ->
    exists h h', ⟦ E[sb_qn (List.length Ψ) σ]ᵐ ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρl ↘ h /\
      ⟦ E ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρr ↘ h' /\ per_dmod h h'.
Proof.
  intros * [Rl Rr HΓl HΓr Hsub Hl [ρm [Hm Hmr]]] [R0 HΓ0 HE].
  destruct (HE _ _ HΓl _ _ Hsub _ _ _ _ Hl Hm Hm) as [h1 h2 h3 h4 H1 H2 H3 H4 [Hc _]].
  destruct (HE _ _ HΓr _ _ (rel_sub_id (ex_intro _ _ HΓr)) _ _ _ _ Hmr (eval_sub_id _) (eval_sub_id _))
    as [g1 g2 g3 g4 G1 G2 G3 G4 [_ [Hg _]]].
  pose proof (functional_eval_modexp _ _ _ _ H2 G2) as <-.
  exists h1, g3; split; [ exact H1 | split; [ exact G3 | eapply per_dmod_trans; eassumption ] ].
Qed.

(** The parameters, outermost first: [ts] is the rest of the telescope,
    reversed. *)
Lemma sub_walk_params : forall Γ' Γ σ ts Ψ Dl D ρl ρr,
    tele_ass ts ->
    ⊨ rev ts ++ Ψ ++ Γ ->
    sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    (forall ρl' ρr', sub_walk_inv Γ' Γ σ (rev ts ++ Ψ) ρl' ρr' ->
       exists h h', ⟦ nil ⊢ Dl ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρl' ↘ h /\ ⟦ nil ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρr' ↘ h' /\ per_dmod h h') ->
    exists h h', ⟦ tele_sub (rev ts) (sb_qn (List.length Ψ) σ) ⊢ Dl ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρl ↘ h /\
      ⟦ rev ts ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρr ↘ h' /\ per_dmod h h'.
Proof.
  induction ts as [| e ts IH]; intros * Hts HΨ Hinv HD; cbn [rev tele_sub app] in *.
  - apply HD; exact Hinv.
  - inversion Hts as [| ? ? [A ->] Hts0]; subst.
    rewrite tele_sub_app; cbn [tele_sub length sb_qn centry_sub].
    rewrite <- !app_assoc in HΨ; cbn [app] in HΨ.
    pose proof (rel_ctx_wf_app_r _ _ HΨ) as HΨA.
    destruct (rel_ctx_wf_ass_inv HΨA) as [i HA].
    destruct (sub_walk_ass _ _ _ _ _ _ _ _ Hinv HA) as [R [[a a' Ha Ha' HRa] Hc]].
    exists (dm_local (tele_sub (rev ts) (sb_qn (S (List.length Ψ)) σ) ++ ce_ass A[sb_qn (List.length Ψ) σ] :: nil) Dl ρl),
           (dm_local (rev ts ++ ce_ass A :: nil) D ρr).
    split; [ apply close_unsat; rewrite length_app; cbn; lia |].
    split; [ apply close_unsat; rewrite length_app; cbn; lia |].
    eapply per_dmod_closure_step; [ exact Ha | exact Ha' | exact HRa |].
    intros c c' Hcc.
    pose proof (IH (Ψ ▹ A) Dl D (ρl ↦ c) (ρr ↦ c') Hts0 HΨ (Hc _ _ Hcc)) as HI.
    cbn [length] in HI; apply HI.
    intros ρl' ρr' Hi; apply HD; rewrite <- app_assoc; exact Hi.
Qed.

Lemma body_eq_upto_types_binders : forall Φe Φt, body_eq_upto_types Φe Φt -> gm_binders Φe = gm_binders Φt.
Proof.
  induction Φe as [| Φe IH y Ee | ]; intros [| Φt y' Et | ] Hk; cbn [body_eq_upto_types] in Hk; try contradiction; [ reflexivity |].
  destruct Hk as (Hk & _ & _); cbn; f_equal; auto.
Qed.

(** Entries without opens, read by kinds as [Φe] and by the context as
    [Φt], along the walk. *)
Lemma sub_walk_eval : forall Γ' Γ σ Φt Φe Ψ ρl ρr,
    body_eq_upto_types Φe Φt -> body_shape Φt Φt ->
    ⊨ body_ctx Φt ++ Ψ ++ Γ ->
    sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    exists ρl1 ρr1, ⟦ gmod_sub Φe (sb_qn (List.length Ψ) σ) ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρl ↘ ρl1 /\
      ⟦ Φe ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρr ↘ ρr1 /\ sub_walk_inv Γ' Γ σ (body_ctx Φt ++ Ψ) ρl1 ρr1.
Proof.
  induction Φt as [| Φt IH y Et | Φt IH H its]; intros [| Φe0 ye Ee | ] * Hm Hs HΦ Hinv; cbn [body_eq_upto_types] in Hm; try contradiction.
  - exists ρl, ρr; repeat split; try constructor; exact Hinv.
  - destruct Hm as (Hm & <- & HEe); cbn [body_shape] in Hs; destruct Hs as (Hs & _ & HsE).
    assert (Hq : sb_eq (sb_qn (gm_binders Φe0) (sb_qn (List.length Ψ) σ)) (sb_qn (List.length (body_ctx Φt ++ Ψ)) σ))
      by (rewrite sb_qn_add, length_app, length_body_ctx, (body_eq_upto_types_binders _ _ Hm); reflexivity).
    destruct Et as [bt pvt At [Mt |] | pmt Ut | ? ? ? ? | ? ? ? ?]; cbn in HsE; try contradiction;
      destruct HEe as [-> | (b' & pv' & A' & A'' & M' & -> & [= <- <- <- <-])];
      cbn [gmod_sub gentry_sub body_ctx app] in *.
    1,2: (* a definition *)
      destruct (rel_ctx_wf_def_inv HΦ) as [[i HA] HM];
      destruct (IH _ _ _ _ Hm Hs (rel_ctx_wf_tail HΦ) Hinv) as (ρl1 & ρr1 & Hb1 & Hb1' & Hi1);
      rewrite app_assoc in HA, HM;
      destruct (sub_walk_def _ _ _ _ _ _ _ _ _ Hi1 HA HM) as (j & R & HR & HMr & Hstep);
      rewrite (exp_sub_sb_eq Mt _ _ Hq);
      destruct HMr as [m m' Hm1 Hm1' Hmm'];
      exists (ρl1 ↦ m), (ρr1 ↦ m');
      (split; [ apply eval_benv_def; assumption | split; [ apply eval_benv_def; assumption |] ]);
      apply Hstep; assumption.
    + (* a module *)
      pose proof (rel_ctx_wf_mod_inv HΦ) as [HU _ _].
      destruct (IH _ _ _ _ Hm Hs (rel_ctx_wf_tail HΦ) Hinv) as (ρl1 & ρr1 & Hb1 & Hb1' & Hi1).
      rewrite app_assoc in HU.
      destruct (sub_walk_mod _ _ _ _ _ _ _ Hi1 HU) as (hl & hr & Hhl & Hhr & _ & Hstep).
      destruct Ut as [Δy Dy].
      rewrite (gunit_sub_sb_eq (gu_mk Δy Dy) _ _ Hq), gunit_sub_mk.
      rewrite gunit_sub_mk in Hhl; apply eval_me_lit_iff in Hhl, Hhr.
      exists (ρl1 ↦ᵐ hl), (ρr1 ↦ᵐ hr).
      split; [ apply eval_benv_mod; assumption | split; [ apply eval_benv_mod; assumption |] ].
      exact Hstep.
Qed.

(** ** Opens

    The target of a local open, read again after the first entries it
    generates, against its value before them. *)
Lemma wk_coh : forall C1 H X R ρk ρ1 h hk,
    C1 ⊨ᵐ H ≈ H -> ⊨ X ++ C1 -> EF X ++ C1 ≈ X ++ C1 ∈ per_ctx_env ↘ R -> R ρk ρk ->
    List.skipn (List.length X) ρk = ρ1 ->
    ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ1 ↘ h -> ⟦ modexp_wk H (wk_shiftn (List.length X)) ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρk ↘ hk ->
    per_dmod hk h.
Proof.
  intros * [R0 HC0 HH] HX HR Hρ Hsk Hh Hhk.
  pose proof (rel_sub_of_wk (rel_wk_under_ctx_shiftn _ _ HX)) as Hs.
  pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn (List.length X)) ρk (wk_mono_shiftn _)) as Hev.
  rewrite eval_wk_shiftn, Hsk in Hev.
  destruct (HH _ _ HR _ _ Hs _ _ _ _ Hρ Hev Hev) as [h1 h2 h3 h4 H1 H2 H3 H4 (C12 & _)].
  rewrite modexp_sub_of_wk in H1.
  rewrite (functional_eval_modexp _ _ _ _ Hhk H1), (functional_eval_modexp _ _ _ _ Hh H2); exact C12.
Qed.

Lemma wk_coh_ex : forall C1 H X R ρk ρ1,
    C1 ⊨ᵐ H ≈ H -> ⊨ X ++ C1 -> EF X ++ C1 ≈ X ++ C1 ∈ per_ctx_env ↘ R -> R ρk ρk ->
    List.skipn (List.length X) ρk = ρ1 ->
    exists hk, ⟦ modexp_wk H (wk_shiftn (List.length X)) ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρk ↘ hk.
Proof.
  intros * [R0 HC0 HH] HX HR Hρ Hsk.
  pose proof (rel_sub_of_wk (rel_wk_under_ctx_shiftn _ _ HX)) as Hs.
  pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn (List.length X)) ρk (wk_mono_shiftn _)) as Hev.
  destruct (HH _ _ HR _ _ Hs _ _ _ _ Hρ Hev Hev) as [h1 h2 h3 h4 H1 H2 H3 H4 _].
  rewrite modexp_sub_of_wk in H1; exists h1; exact H1.
Qed.

Lemma kbody_binders : forall ρ Φ Φk, kbody gc_deps gc_stack ρ Φ Φk -> gm_binders Φk = gm_binders Φ.
Proof.
  induction 1; cbn; auto.
  rewrite gens_append_binders; erewrite kgens_length by eassumption; lia.
Qed.

(** What the kinds read off an open of a target, read off an open of a
    module expression with the same kinds. *)
Lemma kgens_transfer : forall ρl ρr H τ its gs,
    kgens gc_deps gc_stack ρr H its gs ->
    (forall n k, skind gc_deps gc_stack ρr H (n :: nil) k -> skind gc_deps gc_stack ρl H[τ]ᵐ (n :: nil) k) ->
    kgens gc_deps gc_stack ρl H[τ]ᵐ its (List.map (fun g => igen_sub g τ) gs).
Proof. intros * Hg Hs; induction Hg; cbn [List.map igen_sub exp_sub modexp_sub]; constructor; auto. Qed.

Lemma body_shape_gens_any : forall gs Φ Φ' k, body_shape (gens_append Φ k gs) (gens_append Φ k gs) ->
    body_shape Φ' Φ' -> body_shape (gens_append Φ' k gs) (gens_append Φ' k gs).
Proof.
  induction gs as [| g gs IH]; intros * Hs Hs'; cbn [gens_append] in *; [ exact Hs' |].
  destruct (ig_entry g) as [d E]; eapply IH; [ exact Hs |].
  pose proof (body_shape_gens_l _ _ _ Hs) as Hs0; cbn in Hs0 |- *; tauto.
Qed.

Lemma body_ctx_gens_firstn : forall gs Φ k n, exists X,
    body_ctx (gens_append Φ k gs) = X ++ body_ctx (gens_append Φ k (List.firstn n gs)).
Proof.
  intros gs Φ k n.
  replace (gens_append Φ k gs) with (gens_append Φ k (List.firstn n gs ++ List.skipn n gs)) by (rewrite firstn_skipn; reflexivity).
  rewrite gens_append_app, gens_body_ctx_base; eauto.
Qed.

Lemma skipn_benv_gens : forall gs ρ ρ', ⟦ gens_append gm_nil 0 gs ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' ->
    List.skipn (List.length gs) ρ' = ρ.
Proof.
  intros * He.
  destruct (eval_benv_nopens_app _ _ _ He ltac:(rewrite gens_append_nopens; reflexivity)) as (X & -> & HX).
  rewrite gens_append_binders in HX; cbn in HX.
  rewrite <- (Nat.add_0_r (List.length gs)), <- HX, skipn_app, Nat.sub_diag; cbn; rewrite skipn_all; reflexivity.
Qed.

Variables (Θm : gdeps) (Ξm : gstack).

(** A body, entry by entry as written, along a substitution; a local open,
    as the entries it generates. *)
Lemma sub_walk_body : forall Γ' Γ σ Φ Φx Ψ ρl ρr,
    body_xp Θm Ξm (Ψ ++ Γ) Φ Φx ->
    body_shape Φ Φ -> body_shape Φx Φx ->
    ⊨ body_ctx Φx ++ Ψ ++ Γ ->
    (forall k Ψo H, nth_error (body_opens Φ Φx) k = Some (Ψo, H) ->
       Ψo ++ Ψ ++ Γ ⊨ᵐ H ≈ H /\ kinds_ok Θm Ξm (Ψo ++ Ψ ++ Γ) H) ->
    sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    per_body ρl (gmod_sub Φ (sb_qn (List.length Ψ) σ)) ρr Φ /\
    exists Φr ρl1 ρr1, kbody gc_deps gc_stack ρl (gmod_sub Φ (sb_qn (List.length Ψ) σ)) (gmod_sub Φr (sb_qn (List.length Ψ) σ)) /\
      kbody gc_deps gc_stack ρr Φ Φr /\ body_eq_upto_types Φr Φx /\
      ⟦ gmod_sub Φr (sb_qn (List.length Ψ) σ) ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρl ↘ ρl1 /\ ⟦ Φr ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρr ↘ ρr1 /\
      sub_walk_inv Γ' Γ σ (body_ctx Φx ++ Ψ) ρl1 ρr1.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros * Hx Hs Hsx HΦ Ho Hinv; cbn in Hs.
  - inversion Hx; subst; split; [ constructor |].
    exists gm_nil, ρl, ρr; repeat split; try constructor; exact Hinv.
  - destruct Hs as (Hs & _ & HE).
    inversion Hx as [| ? ? Φx0 ? ? Hx0 |]; subst.
    cbn [body_opens gm_dropn] in Ho; cbn [body_shape] in Hsx; destruct Hsx as (Hsx & _ & _).
    assert (Hq : sb_eq (sb_qn (gm_binders Φ) (sb_qn (List.length Ψ) σ)) (sb_qn (List.length (body_ctx Φx0 ++ Ψ)) σ))
      by (rewrite sb_qn_add, length_app, length_body_ctx, (body_xp_binders _ _ _ _ _ Hx0); reflexivity).
    destruct E as [b pv A [M |] | pm Uy | pv D Φd | ? ? ? ?]; cbn in HE; try contradiction; cbn [gmod_sub gentry_sub body_ctx app] in *.
    + destruct (rel_ctx_wf_def_inv HΦ) as [[i HA] HM].
      destruct (IH _ _ _ _ Hx0 Hs Hsx (rel_ctx_wf_tail HΦ) Ho Hinv) as (Hb & Φr & ρl1 & ρr1 & Hkl & Hkr & Hkx & Hb1 & Hb1' & Hi1).
      rewrite app_assoc in HA, HM.
      destruct (sub_walk_def _ _ _ _ _ _ _ _ _ Hi1 HA HM) as (j & R & HR & HMr & Hstep).
      assert (Hbr : gm_binders Φr = gm_binders Φ) by exact (kbody_binders _ _ _ Hkr).
      rewrite (exp_sub_sb_eq A _ _ Hq), (exp_sub_sb_eq M _ _ Hq).
      split; [ eapply per_body_def; [ exact Hb | exact Hkl | exact Hkr | exact Hb1 | exact Hb1' | exact HR | exact HMr ] |].
      destruct HMr as [m m' Hm Hm' Hmm'].
      exists (gm_ext Φr y (ge_def b pv A (Some M))), (ρl1 ↦ m), (ρr1 ↦ m').
      cbn [gmod_sub gentry_sub]; rewrite Hbr, (exp_sub_sb_eq A _ _ Hq), (exp_sub_sb_eq M _ _ Hq).
      split; [ constructor; exact Hkl |]; split; [ constructor; exact Hkr |].
      split; [ split; [ exact Hkx | split; [ reflexivity | left; reflexivity ] ] |].
      split; [ apply eval_benv_def; assumption |]; split; [ apply eval_benv_def; assumption |].
      apply Hstep; assumption.
    + pose proof (rel_ctx_wf_mod_inv HΦ) as [HU _ _].
      destruct (IH _ _ _ _ Hx0 Hs Hsx (rel_ctx_wf_tail HΦ) Ho Hinv) as (Hb & Φr & ρl1 & ρr1 & Hkl & Hkr & Hkx & Hb1 & Hb1' & Hi1).
      rewrite app_assoc in HU.
      destruct (sub_walk_mod _ _ _ _ _ _ _ Hi1 HU) as (hl & hr & Hhl & Hhr & Hlr & Hstep).
      assert (Hbr : gm_binders Φr = gm_binders Φ) by exact (kbody_binders _ _ _ Hkr).
      destruct Uy as [Δy Dy].
      rewrite (gunit_sub_sb_eq (gu_mk Δy Dy) _ _ Hq), gunit_sub_mk.
      rewrite gunit_sub_mk in Hhl; apply eval_me_lit_iff in Hhl, Hhr.
      split; [ eapply per_body_mod; [ exact Hb | exact Hkl | exact Hkr | exact Hb1 | exact Hb1' | exact Hhl | exact Hhr | exact Hlr ] |].
      exists (gm_ext Φr y (ge_mod pm (gu_mk Δy Dy))), (ρl1 ↦ᵐ hl), (ρr1 ↦ᵐ hr).
      cbn [gmod_sub gentry_sub]; rewrite Hbr, (gunit_sub_sb_eq (gu_mk Δy Dy) _ _ Hq), gunit_sub_mk.
      split; [ constructor; exact Hkl |]; split; [ constructor; exact Hkr |].
      split; [ split; [ exact Hkx | split; [ reflexivity | left; reflexivity ] ] |].
      split; [ apply eval_benv_mod; assumption |]; split; [ apply eval_benv_mod; assumption |].
      exact Hstep.
  - destruct Hs as [Hs _].
    inversion Hx as [| | ? ? Φx0 ? ? Rm T gs Hx0 HRm HT Hgs Hok ]; subst.
    pose proof (items_gen_length _ _ _ _ _ _ _ Hgs) as Hl.
    assert (Eo : body_opens (gm_open Φ H its) (gens_append Φx0 0 gs) = (body_ctx Φx0, H) :: body_opens Φ Φx0).
    { cbn [body_opens]; rewrite <- Hl, gm_dropn_gens_append; reflexivity. }
    rewrite Eo in Ho.
    pose proof (body_shape_gens_l _ _ _ Hsx) as Hsx0.
    rewrite gens_body_ctx_base, <- app_assoc in HΦ.
    pose proof (rel_ctx_wf_app_r _ _ HΦ) as HΦ0.
    destruct (IH _ _ _ _ Hx0 Hs Hsx0 HΦ0 (fun k => Ho (S k)) Hinv) as (Hb & Φr & ρl1 & ρr1 & Hkl & Hkr & Hkx & Hb1 & Hb1' & Hi1).
    destruct (Ho 0 _ _ eq_refl) as [HH Hko]; rewrite app_assoc in HH, Hko.
    destruct (sub_walk_alias _ _ _ _ _ _ _ Hi1 HH) as (hl & hr & Hhl & Hhr & Hhh).
    assert (Hbr : gm_binders Φr = gm_binders Φ) by exact (kbody_binders _ _ _ Hkr).
    set (τ1 := sb_qn (List.length (body_ctx Φx0 ++ Ψ)) σ) in *.
    assert (Hq : sb_eq (sb_qn (gm_binders Φ) (sb_qn (List.length Ψ) σ)) τ1)
      by (subst τ1; rewrite sb_qn_add, length_app, length_body_ctx, (body_xp_binders _ _ _ _ _ Hx0); reflexivity).
    cbn [gmod_sub]; rewrite (modexp_sub_sb_eq H _ _ Hq).
    set (gse := List.map ig_erase gs).
    destruct (sub_walk_right _ _ _ _ _ _ Hi1) as (Rr1 & HRr1 & Hρr1).
    destruct (body_eq_upto_types_kenv_exists _ _ Hkx ρr) as (σr1 & Hσr1).
    destruct (kind_eval_benv _ _ _ _ _ Hb1' _ (kshape_refl _ _ ρr)) as (σ' & Hk' & Hs').
    pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack)))) _ _ _ Hσr1 _ Hk') as <-.
    clear Hk'.
    rewrite <- app_assoc in HRr1, Hko.
    pose proof (items_kgens _ _ _ _ _ _ Hgs Hko _ _ _ HRr1 Hρr1 Hs') as Hkgr.
    destruct (kind_eval_benv _ _ _ _ _ Hb1 _ (kshape_refl _ _ ρl)) as (σl1 & Hσl1 & Hsl).
    assert (Hkgl : kgens gc_deps gc_stack σl1 H[τ1]ᵐ its (List.map (fun g => igen_sub g τ1) gse)).
    { apply (kgens_transfer σl1 σr1); [ exact Hkgr |].
      intros n k Hk.
      apply (skind_id _ _ _ _ (proj1 Hsl)), (kind_eval_modexp _ _ _ _ _ Hhl), (per_dmod_kequiv _ _ Hhh),
            (kind_eval_modexp _ _ _ _ _ Hhr), (skind_id _ _ _ _ (proj1 (kshape_sym _ _ Hs'))); exact Hk. }
    set (gsl := List.map (fun g => igen_sub g τ1) gse) in *.
    assert (Eg : forall g, igen_sub g (sb_qn (gm_binders Φr) (sb_qn (List.length Ψ) σ)) = igen_sub g τ1).
    { rewrite Hbr; intros [d pv A0 M0 | d pv E0 | ? ? ? ? ?]; cbn [igen_sub]; try reflexivity.
      - rewrite (exp_sub_sb_eq A0 _ _ Hq), (exp_sub_sb_eq M0 _ _ Hq); reflexivity.
      - rewrite (modexp_sub_sb_eq E0 _ _ Hq); reflexivity. }
    assert (Ex : gmod_sub (gens_append Φr 0 gse) (sb_qn (List.length Ψ) σ) = gens_append (gmod_sub Φr (sb_qn (List.length Ψ) σ)) 0 gsl).
    { rewrite gens_append_sub by lia; rewrite Nat.sub_0_r; subst gsl; f_equal; apply map_ext; exact Eg. }
    assert (Hlse : List.length gse = List.length its) by (subst gse; rewrite length_map; exact Hl).
    assert (Hlsl : List.length gsl = List.length its) by (subst gsl; rewrite length_map; exact Hlse).
    assert (HshT : body_shape (gens_append gm_nil 0 gs) (gens_append gm_nil 0 gs)) by exact (body_shape_gens_any gs Φx0 gm_nil 0 Hsx I).
    assert (HΦ' : ⊨ body_ctx (gens_append gm_nil 0 gs) ++ (body_ctx Φx0 ++ Ψ) ++ Γ) by (rewrite <- app_assoc; exact HΦ).
    (* the environments the first [k] generated entries make, along the walk *)
    assert (Hpre : forall k, exists ρlk ρrk,
               ⟦ gens_append gm_nil 0 (List.firstn k gsl) ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρl1 ↘ ρlk /\
               ⟦ gens_append gm_nil 0 (List.firstn k gse) ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρr1 ↘ ρrk /\
               sub_walk_inv Γ' Γ σ (body_ctx (gens_append gm_nil 0 (List.firstn k gs)) ++ body_ctx Φx0 ++ Ψ) ρlk ρrk /\
               ⊨ body_ctx (gens_append gm_nil 0 (List.firstn k gs)) ++ (body_ctx Φx0 ++ Ψ) ++ Γ).
    { intros k.
      assert (HshK : body_shape (gens_append gm_nil 0 (List.firstn k gs)) (gens_append gm_nil 0 (List.firstn k gs))).
      { apply (body_shape_gens_l (List.skipn k gs) _ (0 + List.length (List.firstn k gs))).
        rewrite <- gens_append_app, firstn_skipn; exact HshT. }
      assert (HΦK : ⊨ body_ctx (gens_append gm_nil 0 (List.firstn k gs)) ++ (body_ctx Φx0 ++ Ψ) ++ Γ).
      { destruct (body_ctx_gens_firstn gs gm_nil 0 k) as (X & HX).
        rewrite HX, <- app_assoc in HΦ'; exact (rel_ctx_wf_app_r _ _ HΦ'). }
      destruct (sub_walk_eval _ _ _ (gens_append gm_nil 0 (List.firstn k gs)) (gens_append gm_nil 0 (List.firstn k gse)) _ _ _
                  ltac:(subst gse; rewrite firstn_map; exact (body_eq_upto_types_gens _ gm_nil gm_nil 0 I)) HshK HΦK Hi1)
        as (ρlk & ρrk & Hlk & Hrk & Hik).
      rewrite (gens_append_sub _ gm_nil 0 _ (le_n 0)) in Hlk; cbn [gmod_sub gm_binders Nat.sub sb_qn] in Hlk.
      exists ρlk, ρrk; split; [ subst gsl; rewrite firstn_map; exact Hlk |].
      split; [ exact Hrk | split; [ exact Hik | exact HΦK ] ]. }
    destruct (Hpre (List.length its)) as (ρl2 & ρr2 & Hb2 & Hb2' & Hi2 & _).
    rewrite firstn_all2 in Hb2 by lia; rewrite firstn_all2 in Hb2' by lia; rewrite firstn_all2 in Hi2 by lia.
    assert (Hbo : ⟦ gens_append (gmod_sub Φr (sb_qn (List.length Ψ) σ)) 0 gsl ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρl ↘ ρl2)
      by (apply eval_gens_split; exists ρl1; split; [ exact Hb1 | exact Hb2 ]).
    assert (Hbo' : ⟦ gens_append Φr 0 gse ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρr ↘ ρr2)
      by (apply eval_gens_split; exists ρr1; split; [ exact Hb1' | exact Hb2' ]).
    assert (Hko' : kbody gc_deps gc_stack ρl (gm_open (gmod_sub Φ (sb_qn (List.length Ψ) σ)) H[τ1]ᵐ its)
                     (gens_append (gmod_sub Φr (sb_qn (List.length Ψ) σ)) 0 gsl))
      by (econstructor; [ exact Hkl | exact Hσl1 | exact Hkgl ]).
    assert (Hkor : kbody gc_deps gc_stack ρr (gm_open Φ H its) (gens_append Φr 0 gse))
      by (econstructor; [ exact Hkr | exact Hσr1 | exact Hkgr ]).
    split; [| exists (gens_append Φr 0 gse), ρl2, ρr2; rewrite Ex;
              split; [ exact Hko' |]; split; [ exact Hkor |]; split; [ exact (body_eq_upto_types_gens _ _ _ _ Hkx) |];
              split; [ exact Hbo |]; split; [ exact Hbo' |];
              rewrite gens_body_ctx_base, <- app_assoc; exact Hi2 ].
    assert (Cl : forall k ρk, k < List.length its ->
               ⟦ gm_dropn (List.length its - k) (gens_append (gmod_sub Φr (sb_qn (List.length Ψ) σ)) 0 gsl) ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρl ↘ ρk ->
               exists hk, ⟦ modexp_wk H[τ1]ᵐ (wk_shiftn k) ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρk ↘ hk /\ per_dmod hk hl).
    { intros k ρk Hk Hbk.
      rewrite gm_dropn_gens in Hbk by lia.
      (* the substituted side, against the original's *)
      replace (List.length gsl - (List.length its - k)) with k in Hbk by lia.
      apply eval_gens_split in Hbk as (ρl1' & Hb1x & Hbk').
      pose proof (functional_eval_benv _ _ _ _ Hb1x Hb1) as ->.
      destruct (Hpre k) as (ρlk & ρrk & Hlk & Hrk & Hik & HΦK).
      pose proof (functional_eval_benv _ _ _ _ Hbk' Hlk) as <-.
      assert (Hlk' : List.length (List.firstn k gsl) = k) by (rewrite length_firstn; lia).
      pose proof (skipn_benv_gens _ _ _ Hbk') as Hskip; rewrite Hlk' in Hskip.
      rewrite modexp_wk_sub.
      destruct Hi1 as [Rl1 RrI HΓl1 HΓr1 Hsub1 Hl1 [ρm [Hm Hmr]]].
      destruct Hik as [Rlk Rrk HΓlk HΓrk _ Hlkk _].
      set (Xk := tele_sub (body_ctx (gens_append gm_nil 0 (List.firstn k gs))) (sb_qn (List.length (body_ctx Φx0 ++ Ψ)) σ)).
      assert (HXk : List.length Xk = k)
        by (subst Xk; rewrite length_tele_sub, gens_body_ctx_length, length_firstn; lia).
      assert (HΓlk' : EF Xk ++ (tele_sub (body_ctx Φx0 ++ Ψ) σ ++ Γ') ≈ Xk ++ (tele_sub (body_ctx Φx0 ++ Ψ) σ ++ Γ') ∈ per_ctx_env ↘ Rlk)
        by (subst Xk; rewrite app_assoc, <- tele_sub_app; exact HΓlk).
      pose proof (rel_wk_shiftn _ _ _ _ HΓlk' HΓl1) as Hwk; rewrite HXk in Hwk.
      pose proof (rel_sub_under_ctx_wk Hsub1 (rel_wk_under_ctx_intro HΓlk' HΓl1 Hwk)) as Hsw.
      pose proof Hsub1 as [Ra HRa Ro HRo Hs1].
      assert (Ea : Rl1 <~> Ra) by (eapply per_ctx_env_right_irrel; eassumption).
      assert (Eo' : RrI <~> Ro) by (eapply per_ctx_env_right_irrel; eassumption).
      assert (Hwk' : rel_wk (wk_shiftn k) Rlk Ra) by (destruct Hwk as [Hmono Happ]; split; [ exact Hmono | intros ? ? Hr; apply Ea, Happ, Hr ]).
      destruct (Hs1 _ _ HΓlk' _ Hwk' _ _ Hlkk) as [ρσφ ρσ ρ'σ' ρ'σ'φ Eσφ Eσ _ _ (C1 & _)].
      rewrite eval_wk_shiftn, Hskip in Eσ.
      assert (HPr : PER RrI) by (eapply per_env_PER; exact HΓr1).
      assert (Hσm : RrI ρσ ρm) by (eapply (rel_sub_under_ctx_at' Hsub1 HΓl1 HΓr1); eassumption).
      assert (Hφr : RrI ρσφ ρr1) by (apply Eo' in C1; etransitivity; [ exact C1 | etransitivity; eassumption ]).
      destruct HH as [RH HRH HHg].
      destruct (HHg _ _ HΓlk' _ _ Hsw _ _ _ _ Hlkk Eσφ Eσφ) as [h1 h2 h3 h4 E1 E2 E3 E4 (C12 & _)].
      exists h1; split; [ exact E1 |].
      destruct (rel_modexp_at _ _ _ _ _ (mk_rel_modexp_under_ctx _ _ _ RH HRH HHg) HΓr1 _ _ Hφr) as (g & g' & Hg & Hg' & Hgg).
      pose proof (functional_eval_modexp _ _ _ _ Hg E2) as ->; pose proof (functional_eval_modexp _ _ _ _ Hg' Hhr) as ->.
      eapply per_dmod_trans; [ exact C12 | eapply per_dmod_trans; [ exact Hgg | apply per_dmod_sym; exact Hhh ] ]. }
    assert (Cr : forall k ρk, k < List.length its ->
               ⟦ gm_dropn (List.length its - k) (gens_append Φr 0 gse) ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρr ↘ ρk ->
               exists hk, ⟦ modexp_wk H (wk_shiftn k) ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρk ↘ hk /\ per_dmod hk hr).
    { intros k ρk Hk Hbk.
      rewrite gm_dropn_gens in Hbk by lia.
      (* the original side *)
      replace (List.length gse - (List.length its - k)) with k in Hbk by lia.
      apply eval_gens_split in Hbk as (ρr1' & Hb1x & Hbk').
      pose proof (functional_eval_benv _ _ _ _ Hb1x Hb1') as ->.
      destruct (Hpre k) as (ρlk & ρrk & Hlk & Hrk & Hik & HΦK).
      pose proof (functional_eval_benv _ _ _ _ Hbk' Hrk) as <-.
      destruct (sub_walk_right _ _ _ _ _ _ Hik) as (Rrk & HRrk & Hρk).
      rewrite <- app_assoc in HRrk.
      assert (HlX : List.length (body_ctx (gens_append gm_nil 0 (List.firstn k gs))) = k)
        by (rewrite gens_body_ctx_length, length_firstn; lia).
      pose proof (skipn_benv_gens _ _ _ Hbk') as Hskip; rewrite length_firstn in Hskip.
      replace (Init.Nat.min k (List.length gse)) with k in Hskip by lia.
      rewrite <- HlX in Hskip |- *.
      destruct (wk_coh_ex _ _ _ _ _ _ HH HΦK HRrk Hρk Hskip) as (hk & Hhk).
      exists hk; split; [ exact Hhk | exact (wk_coh _ _ _ _ _ _ _ _ HH HΦK HRrk Hρk Hskip Hhr Hhk) ]. }
    eapply per_body_open; [ exact Hb | exact Hkl | exact Hkr | exact Hb1 | exact Hb1' | exact Hhl | exact Hhr | exact Hhh
                          | exact Hko' | exact Hkor | exact Hbo | exact Hbo' | | | | ].
    + intros k ρk Hk Hbk; destruct (Cl _ _ Hk Hbk) as (hk & Hhk & _); exists hk; exact Hhk.
    + intros k ρk Hk Hbk; destruct (Cr _ _ Hk Hbk) as (hk & Hhk & _); exists hk; exact Hhk.
    + intros k ρk hk Hk Hbk Hhk; destruct (Cl _ _ Hk Hbk) as (hk' & Hhk' & Hd).
      rewrite (functional_eval_modexp _ _ _ _ Hhk Hhk'); exact Hd.
    + intros k ρk hk Hk Hbk Hhk; destruct (Cr _ _ Hk Hbk) as (hk' & Hhk' & Hd).
      rewrite (functional_eval_modexp _ _ _ _ Hhk Hhk'); exact Hd.
Qed.

(** ** Closures Commute with Substitution

    The closure of [U[σ]] over [ρ] is related to that of [U] over [⟦σ⟧ρ],
    for a unit valid in its parts. *)

Lemma unit_sub_link_body : forall Γ' Γ σ σ' Δ Φ Φx R' ρ ρσ,
    tele_ass Δ -> body_xp Θm Ξm (Δ ++ Γ) Φ Φx -> body_shape Φ Φ -> body_shape Φx Φx ->
    ⊨ body_ctx Φx ++ Δ ++ Γ ->
    (forall k Ψo H, nth_error (body_opens Φ Φx) k = Some (Ψo, H) ->
       Ψo ++ Δ ++ Γ ⊨ᵐ H ≈ H /\ kinds_ok Θm Ξm (Ψo ++ Δ ++ Γ) H) ->
    Γ' ⊨ˢ σ ≈ σ' : Γ -> EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' -> R' ρ ρ -> ⟦ σ ⟧s ρ ↘ ρσ ->
    rel_mexp (me_lit (gu_open Δ Φ)[σ]ᵘ) ρ (me_lit (gu_open Δ Φ)) ρσ.
Proof.
  intros * HΔ Hx Hs Hsx HΦ Ho Hσ HΓ' Hρ Hev.
  pose proof (rel_ctx_wf_app_r _ _ HΦ) as HΔΓ.
  destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_app_r _ _ HΔΓ)) as [R HΓ].
  pose proof (sub_walk_init _ _ _ _ _ _ _ _ Hσ HΓ' HΓ Hρ Hev) as Hi.
  destruct (sub_walk_params Γ' Γ σ (rev Δ) nil (md_body sm_open (gmod_sub Φ (sb_qn (List.length Δ) σ))) (md_body sm_open Φ) ρ ρσ
              ltac:(apply Forall_rev; exact HΔ) ltac:(rewrite rev_involutive, app_nil_l; exact HΔΓ) Hi)
    as (h & h' & Hh & Hh' & Hhh).
  - intros ρl' ρr' Hi'; rewrite rev_involutive, app_nil_r in Hi'.
    destruct (sub_walk_body _ _ _ _ _ _ _ _ Hx Hs Hsx HΦ Ho Hi') as (Hb & _).
    eexists _, _; split; [ apply eval_close_body | split; [ apply eval_close_body | apply per_dmod_body; exact Hb ] ].
  - rewrite rev_involutive in Hh, Hh'; cbn [List.length] in Hh.
    rewrite gunit_sub_mk; cbn [moddef_sub].
    exists h h'; [ apply eval_me_lit; exact Hh | apply eval_me_lit; exact Hh' | exact Hhh ].
Qed.

Lemma unit_sub_link_alias : forall Γ' Γ σ σ' Δ E R' ρ ρσ,
    tele_ass Δ -> ⊨ Δ ++ Γ -> Δ ++ Γ ⊨ᵐ E ≈ E ->
    Γ' ⊨ˢ σ ≈ σ' : Γ -> EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' -> R' ρ ρ -> ⟦ σ ⟧s ρ ↘ ρσ ->
    rel_mexp (me_lit (gu_mk Δ (md_alias E))[σ]ᵘ) ρ (me_lit (gu_mk Δ (md_alias E))) ρσ.
Proof.
  intros * HΔ HΔΓ HE Hσ HΓ' Hρ Hev.
  destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_app_r _ _ HΔΓ)) as [R HΓ].
  pose proof (sub_walk_init _ _ _ _ _ _ _ _ Hσ HΓ' HΓ Hρ Hev) as Hi.
  destruct (sub_walk_params Γ' Γ σ (rev Δ) nil (md_alias E[sb_qn (List.length Δ) σ]ᵐ) (md_alias E) ρ ρσ
              ltac:(apply Forall_rev; exact HΔ) ltac:(rewrite rev_involutive, app_nil_l; exact HΔΓ) Hi)
    as (h & h' & Hh & Hh' & Hhh).
  - intros ρl' ρr' Hi'; rewrite rev_involutive, app_nil_r in Hi'.
    destruct (sub_walk_alias _ _ _ _ _ _ _ Hi' HE) as (g & g' & Hg & Hg' & Hgg).
    exists g, g'; split; [ apply eval_close_alias0; exact Hg | split; [ apply eval_close_alias0; exact Hg' | exact Hgg ] ].
  - rewrite rev_involutive in Hh, Hh'; cbn [List.length] in Hh.
    rewrite gunit_sub_mk; cbn [moddef_sub].
    exists h h'; [ apply eval_me_lit; exact Hh | apply eval_me_lit; exact Hh' | exact Hhh ].
Qed.

(** ** Entries of Two Related Bodies

    An entry of each of two bodies, read in the environments their
    expansions make, is related to the other through their filled-in forms,
    which are related at the parameters. *)

Lemma typ_bridge : forall C C1 C' C1' A A' σ σ' i i' j RC R1 RC' R1' ρa ρa' ρσ ρσ' ρ1 ρ1',
    C1 ⊨ A : Typeω@i -> C ⊨ˢ σ ≈ σ : C1 -> EF C ≈ C ∈ per_ctx_env ↘ RC -> RC ρa ρa' ->
    EF C1 ≈ C1 ∈ per_ctx_env ↘ R1 -> ⟦ σ ⟧s ρa ↘ ρσ -> R1 ρσ ρ1 ->
    C ⊨ A[σ] ≈ A'[σ'] : Typeω@j ->
    C1' ⊨ A' : Typeω@i' -> C' ⊨ˢ σ' ≈ σ' : C1' -> EF C' ≈ C' ∈ per_ctx_env ↘ RC' -> RC' ρa' ρa' ->
    EF C1' ≈ C1' ∈ per_ctx_env ↘ R1' -> ⟦ σ' ⟧s ρa' ↘ ρσ' -> R1' ρσ' ρ1' ->
    exists a a', ⟦ A ⟧ ρ1 ↘ a /\ ⟦ A' ⟧ ρ1' ↘ a' /\ Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * HA Hσ HRC Hρ HR1 Hev H1 HAA' HA' Hσ' HRC' Hρ' HR1' Hev' H1'.
  assert (HP : PER RC) by (eapply per_env_PER; exact HRC).
  assert (Hρρ : RC ρa ρa) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  destruct (valid_typ_inst _ _ _ _ _ _ HA Hσ HRC _ _ Hρρ Hev) as (a1 & a2 & Ha1 & Ha2 & U12).
  destruct (rel_exp_of_typ_inversion_simple_at HR1 HA _ _ H1) as (b2 & b3 & Hb2 & Hb3 & U23).
  destruct (rel_exp_of_typ_inversion_simple_at HRC HAA' _ _ Hρ) as (c1 & c4 & Hc1 & Hc4 & U14).
  destruct (valid_typ_inst _ _ _ _ _ _ HA' Hσ' HRC' _ _ Hρ' Hev') as (d4 & d5 & Hd4 & Hd5 & U45).
  destruct (rel_exp_of_typ_inversion_simple_at HR1' HA' _ _ H1') as (e5 & e6 & He5 & He6 & U56).
  functional_eval_rewrite_clear.
  exists b3, e6; split; [ exact Hb3 | split; [ exact He6 |] ].
  eapply per_univ_trans'; [ apply per_univ_sym'; exact U23 |].
  eapply per_univ_trans'; [ apply per_univ_sym'; exact U12 |].
  eapply per_univ_trans'; [ exact U14 |].
  eapply per_univ_trans'; [ exact U45 | exact U56 ].
Qed.

(** An element PER of a type related to [a] is the element PER [a] has. *)
Lemma per_univ_irrel_rel : forall i R a a' j t k Q t',
    per_univ_elem i R a a' -> Dom a ≈ t ∈ per_univ j -> per_univ_elem k Q t t' -> (R <~> Q).
Proof.
  intros * HR [S HS] HQ.
  destruct (per_univ_elem_sym _ _ _ _ HS) as [HS' _].
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HS' HR) as (T & HT & _).
  pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HT HQ) as E1.
  pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ HR HT) as E2.
  rewrite E2; exact E1.
Qed.

Lemma elem_bridge : forall C C1 C' C1' A A' M M' σ σ' i i' j RC R1 RC' R1' ρa ρa' ρσ ρσ' ρ1 ρ1' k R a a',
    C1 ⊨ A : Typeω@i -> C1 ⊨ M : A -> C ⊨ˢ σ ≈ σ : C1 -> EF C ≈ C ∈ per_ctx_env ↘ RC -> RC ρa ρa' ->
    EF C1 ≈ C1 ∈ per_ctx_env ↘ R1 -> ⟦ σ ⟧s ρa ↘ ρσ -> R1 ρσ ρ1 ->
    C ⊨ A[σ] ≈ A'[σ'] : Typeω@j -> C ⊨ M[σ] ≈ M'[σ'] : A[σ] ->
    C1' ⊨ A' : Typeω@i' -> C1' ⊨ M' : A' -> C' ⊨ˢ σ' ≈ σ' : C1' -> EF C' ≈ C' ∈ per_ctx_env ↘ RC' -> RC' ρa' ρa' ->
    EF C1' ≈ C1' ∈ per_ctx_env ↘ R1' -> ⟦ σ' ⟧s ρa' ↘ ρσ' -> R1' ρσ' ρ1' ->
    ⟦ A ⟧ ρ1 ↘ a -> ⟦ A' ⟧ ρ1' ↘ a' -> per_univ_elem k R a a' ->
    exists m m', ⟦ M ⟧ ρ1 ↘ m /\ ⟦ M' ⟧ ρ1' ↘ m' /\ R m m'.
Proof.
  intros * HA HM Hσ HRC Hρ HR1 Hev H1 HAA' HMM' HA' HM' Hσ' HRC' Hρ' HR1' Hev' H1' Ha Ha' HR.
  assert (HP : PER RC) by (eapply per_env_PER; exact HRC).
  assert (Hρρ : RC ρa ρa) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  assert (Hρρ' : RC ρa' ρa') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
  assert (HPR : PER R) by (eapply per_elem_PER; exact HR).
  destruct (valid_inst _ _ _ _ _ _ HM Hσ HRC _ _ Hρρ Hev) as (m1 & m2 & x2 & j2 & X2 & Hm1 & Hm2 & Hx2 & HX2 & M12).
  destruct (rel_exp_under_ctx_simple_full_at HR1 HM) as [j3 HMs].
  destruct (HMs _ _ H1) as (y2 & y3 & Y & Hy2 & Hy3 & HY & m2' & m3 & Hm2' & Hm3 & M23).
  destruct (rel_exp_under_ctx_simple_full_at HRC HMM') as [j4 HMMs].
  destruct (HMMs _ _ Hρ) as (z1 & z4 & Z & Hz1 & Hz4 & HZ & m1' & m4 & Hm1' & Hm4 & M14).
  destruct (valid_inst _ _ _ _ _ _ HM' Hσ' HRC' _ _ Hρ' Hev') as (m4' & m5 & x5 & j5 & X5 & Hm4' & Hm5 & Hx5 & HX5 & M45).
  destruct (rel_exp_under_ctx_simple_full_at HR1' HM') as [j6 HMs'].
  destruct (HMs' _ _ H1') as (w5 & w6 & W & Hw5 & Hw6 & HW & m5' & m6 & Hm5' & Hm6 & M56).
  (* the types along the chain *)
  destruct (valid_typ_inst _ _ _ _ _ _ HA Hσ HRC _ _ Hρρ Hev) as (t1 & t2 & Ht1 & Ht2 & T12).
  destruct (rel_exp_of_typ_inversion_simple_at HRC HAA' _ _ Hρρ') as (u4 & u4' & Hu4 & Hu4' & U44).
  destruct (valid_typ_inst _ _ _ _ _ _ HA' Hσ' HRC' _ _ Hρ' Hev') as (v4 & v5 & Hv4 & Hv5 & V45).
  functional_eval_rewrite_clear.
  exists m3, m6; split; [ exact Hm3 | split; [ exact Hm6 |] ].
  assert (Ha_x2 : Dom a ≈ x2 ∈ per_univ j3) by (apply per_univ_sym'; eexists; exact HY).
  assert (Ha_z1 : Dom a ≈ z1 ∈ per_univ j3) by (eapply per_univ_trans'; [ exact Ha_x2 | apply per_univ_sym'; exact T12 ]).
  assert (Ha_z4 : Dom a ≈ z4 ∈ per_univ j3) by (eapply per_univ_trans'; [ exact Ha_z1 | eexists; exact HZ ]).
  assert (Ha_v4 : Dom a ≈ u4' ∈ per_univ j3) by (eapply per_univ_trans'; [ exact Ha_z4 | exact U44 ]).
  assert (Ha_x5 : Dom a ≈ x5 ∈ per_univ j3) by (eapply per_univ_trans'; [ exact Ha_v4 | exact V45 ]).
  assert (EY : R <~> Y) by (eapply per_univ_irrel_rel; [ exact HR | exact Ha_x2 | exact HY ]).
  assert (EX2 : R <~> X2) by (eapply per_univ_irrel_rel; [ exact HR | exact Ha_x2 | exact HX2 ]).
  assert (EZ : R <~> Z) by (eapply per_univ_irrel_rel; [ exact HR | exact Ha_z1 | exact HZ ]).
  assert (EX5 : R <~> X5) by (eapply per_univ_irrel_rel; [ exact HR | exact Ha_x5 | exact HX5 ]).
  assert (EW : R <~> W) by (eapply per_univ_irrel_rel; [ exact HR | exact Ha_x5 | exact HW ]).
  apply EY in M23; apply EX2 in M12; apply EZ in M14; apply EX5 in M45; apply EW in M56.
  etransitivity; [ symmetry; exact M23 |].
  etransitivity; [ symmetry; exact M12 |].
  etransitivity; [ exact M14 |].
  etransitivity; [ exact M45 | exact M56 ].
Qed.

Lemma mod_bridge : forall C C1 C' C1' H H' σ σ' RC R1 RC' R1' ρa ρa' ρσ ρσ' ρ1 ρ1',
    C1 ⊨ᵐ H ≈ H -> C ⊨ˢ σ ≈ σ : C1 -> EF C ≈ C ∈ per_ctx_env ↘ RC -> RC ρa ρa' ->
    EF C1 ≈ C1 ∈ per_ctx_env ↘ R1 -> ⟦ σ ⟧s ρa ↘ ρσ -> R1 ρσ ρ1 ->
    C ⊨ᵐ H[σ]ᵐ ≈ H'[σ']ᵐ ->
    C1' ⊨ᵐ H' ≈ H' -> C' ⊨ˢ σ' ≈ σ' : C1' -> EF C' ≈ C' ∈ per_ctx_env ↘ RC' -> RC' ρa' ρa' ->
    EF C1' ≈ C1' ∈ per_ctx_env ↘ R1' -> ⟦ σ' ⟧s ρa' ↘ ρσ' -> R1' ρσ' ρ1' ->
    rel_mexp H ρ1 H' ρ1'.
Proof.
  intros * HH Hσ HRC Hρ HR1 Hev H1 HHH' HH' Hσ' HRC' Hρ' HR1' Hev' H1'.
  assert (HP : PER RC) by (eapply per_env_PER; exact HRC).
  assert (Hρρ : RC ρa ρa) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  destruct (valid_mod_inst _ _ _ _ _ HH Hσ HRC _ _ Hρρ Hev) as (h1 & h2 & Hh1 & Hh2 & D12).
  destruct (rel_modexp_at _ _ _ _ _ HH HR1 _ _ H1) as (g2 & g3 & Hg2 & Hg3 & D23).
  destruct (rel_modexp_at _ _ _ _ _ HHH' HRC _ _ Hρ) as (k1 & k4 & Hk1 & Hk4 & D14).
  destruct (valid_mod_inst _ _ _ _ _ HH' Hσ' HRC' _ _ Hρ' Hev') as (l4 & l5 & Hl4 & Hl5 & D45).
  destruct (rel_modexp_at _ _ _ _ _ HH' HR1' _ _ H1') as (n5 & n6 & Hn5 & Hn6 & D56).
  repeat match goal with
         | E1 : eval_modexp _ _ ?E ?r ?a, E2 : eval_modexp _ _ ?E ?r ?b |- _ =>
             assert_fails (constr_eq a b); pose proof (functional_eval_modexp _ _ _ _ E1 E2); subst b
         end.
  exists g3 n6; [ exact Hg3 | exact Hn6 |].
  eapply per_dmod_trans; [ apply per_dmod_sym; exact D23 |].
  eapply per_dmod_trans; [ apply per_dmod_sym; exact D12 |].
  eapply per_dmod_trans; [ exact D14 |].
  eapply per_dmod_trans; [ exact D45 | exact D56 ].
Qed.

(** ** Walking Two Related Bodies *)

Lemma prefix_in_names : forall Φ y P, gm_prefix_upto Φ y = Some P -> List.In y (gm_names Φ).
Proof.
  induction Φ as [| Φ IH z E | Φ IH H its]; intros * Hp; cbn in Hp |- *; try discriminate.
  - destruct (String.eqb_spec y z) as [-> | Hne]; [ left; reflexivity | right; eauto ].
  - destruct (existsb _ _); [ discriminate | apply in_or_app; right; eauto ].
Qed.

Lemma prefix_ext_keep : forall Φ z E y P, List.NoDup (gm_names (gm_ext Φ z E)) ->
    gm_prefix_upto Φ y = Some P -> gm_prefix_upto (gm_ext Φ z E) y = Some P.
Proof.
  intros * Hn Hp; cbn [gm_names] in Hn; inversion Hn as [| ? ? Hz _]; subst.
  cbn [gm_prefix_upto]; destruct (String.eqb_spec y z) as [-> | _]; [| exact Hp ].
  exfalso; exact (Hz (prefix_in_names _ _ _ Hp)).
Qed.

Lemma prefix_gens_keep : forall gs Φ k y P, List.NoDup (gm_names (gens_append Φ k gs)) ->
    gm_prefix_upto Φ y = Some P -> gm_prefix_upto (gens_append Φ k gs) y = Some P.
Proof.
  intros * Hn Hp; rewrite gens_append_names in Hn.
  rewrite gens_prefix_none; [ exact Hp |].
  destruct (existsb (String.eqb y) (map ig_name gs)) eqn:E; [| reflexivity ].
  exfalso; apply existsb_exists in E as (z & Hz & Hyz); apply String.eqb_eq in Hyz; subst z.
  pose proof (prefix_in_names _ _ _ Hp) as Hy.
  destruct (in_split _ _ Hy) as (l1 & l2 & El); rewrite El, app_assoc in Hn.
  apply NoDup_remove_2 in Hn; apply Hn, in_or_app; left; apply in_or_app; left; apply (proj1 (in_rev _ _)); exact Hz.
Qed.

Lemma body_opens_at_open : forall Φ Φx0 H its gs, List.length gs = List.length its ->
    body_opens_at (gm_open Φ H its) (gens_append Φx0 0 gs) = (Φx0, H) :: body_opens_at Φ Φx0.
Proof. intros * Hl; cbn [body_opens_at]; rewrite <- Hl, gm_dropn_gens_append; reflexivity. Qed.

Lemma body_opens_open : forall Φ Φx0 H its gs, List.length gs = List.length its ->
    body_opens (gm_open Φ H its) (gens_append Φx0 0 gs) = (body_ctx Φx0, H) :: body_opens Φ Φx0.
Proof. intros * Hl; cbn [body_opens]; rewrite <- Hl, gm_dropn_gens_append; reflexivity. Qed.

(** The prefix of a valid body's expansion is valid, and evaluates. *)
Lemma body_prefix_rel_ctx_wf : forall Φx0 y E C, ⊨ body_ctx (gm_ext Φx0 y E) ++ C -> ⊨ body_ctx Φx0 ++ C.
Proof. intros * H; destruct E as [? ? ? [] | | |]; exact (rel_ctx_wf_tail H). Qed.

(** The original's generated block against itself: the target read again
    after the first [k] entries the open generates. *)
Lemma open_coh : forall C Φx0 gs H ρa ρ1 h k ρk hk RC,
    gm_nopens Φx0 = 0 ->
    ⊨ body_ctx (gens_append Φx0 0 gs) ++ C -> body_shape (gens_append Φx0 0 gs) (gens_append Φx0 0 gs) ->
    body_ctx Φx0 ++ C ⊨ᵐ H ≈ H ->
    EF C ≈ C ∈ per_ctx_env ↘ RC -> RC ρa ρa ->
    ⟦ Φx0 ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρa ↘ ρ1 -> ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ1 ↘ h ->
    k <= List.length gs ->
    ⟦ gens_append Φx0 0 (List.firstn k gs) ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρa ↘ ρk ->
    ⟦ modexp_wk H (wk_shiftn k) ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρk ↘ hk -> per_dmod hk h.
Proof.
  intros * Hn0 HC Hsx HH HRC Hρ Hb1 Hh Hk Hbk Hhk.
  set (Φp := gens_append Φx0 0 (List.firstn k gs)) in *.
  assert (HshP : body_shape Φp Φp).
  { apply (body_shape_gens_l (List.skipn k gs) _ (0 + List.length (List.firstn k gs))).
    subst Φp; rewrite <- gens_append_app, firstn_skipn; exact Hsx. }
  assert (HCP : ⊨ body_ctx Φp ++ C).
  { destruct (body_ctx_gens_firstn gs Φx0 0 k) as (X & HX).
    rewrite HX, <- app_assoc in HC; exact (rel_ctx_wf_app_r _ _ HC). }
  assert (HnP : gm_nopens Φp = 0) by (subst Φp; rewrite gens_append_nopens; exact Hn0).
  destruct (rel_ctx_wf_per_ctx_env HCP) as [RP HRP].
  destruct (benv_exists _ _ HnP (proj1 (body_shape_fill _ _ HnP HshP)) HCP _ _ HRC HRP _ Hρ) as (ρk' & Hbk2 & Hρk).
  pose proof (functional_eval_benv _ _ _ _ Hbk2 Hbk) as <-.
  apply eval_gens_split in Hbk as (ρ1' & Hb1x & Hbk').
  pose proof (functional_eval_benv _ _ _ _ Hb1x Hb1) as ->.
  pose proof (skipn_benv_gens _ _ _ Hbk') as Hskip.
  assert (HlX : List.length (body_ctx (gens_append gm_nil 0 (List.firstn k gs))) = List.length (List.firstn k gs))
    by apply gens_body_ctx_length.
  rewrite <- HlX in Hskip.
  rewrite length_firstn in HlX; replace (Init.Nat.min k (List.length gs)) with k in HlX by lia.
  rewrite <- HlX in Hhk.
  subst Φp; rewrite gens_body_ctx_base, <- app_assoc in HRP, HCP.
  exact (wk_coh _ _ _ _ _ _ _ _ HH HCP HRP Hρk Hskip Hh Hhk).
Qed.

Lemma open_coh_ex : forall C Φx0 gs H ρa ρ1 k ρk RC,
    gm_nopens Φx0 = 0 ->
    ⊨ body_ctx (gens_append Φx0 0 gs) ++ C -> body_shape (gens_append Φx0 0 gs) (gens_append Φx0 0 gs) ->
    body_ctx Φx0 ++ C ⊨ᵐ H ≈ H ->
    EF C ≈ C ∈ per_ctx_env ↘ RC -> RC ρa ρa ->
    ⟦ Φx0 ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρa ↘ ρ1 ->
    k <= List.length gs ->
    ⟦ gens_append Φx0 0 (List.firstn k gs) ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρa ↘ ρk ->
    exists hk, ⟦ modexp_wk H (wk_shiftn k) ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρk ↘ hk.
Proof.
  intros * Hn0 HC Hsx HH HRC Hρ Hb1 Hk Hbk.
  set (Φp := gens_append Φx0 0 (List.firstn k gs)) in *.
  assert (HshP : body_shape Φp Φp).
  { apply (body_shape_gens_l (List.skipn k gs) _ (0 + List.length (List.firstn k gs))).
    subst Φp; rewrite <- gens_append_app, firstn_skipn; exact Hsx. }
  assert (HCP : ⊨ body_ctx Φp ++ C).
  { destruct (body_ctx_gens_firstn gs Φx0 0 k) as (X & HX).
    rewrite HX, <- app_assoc in HC; exact (rel_ctx_wf_app_r _ _ HC). }
  assert (HnP : gm_nopens Φp = 0) by (subst Φp; rewrite gens_append_nopens; exact Hn0).
  destruct (rel_ctx_wf_per_ctx_env HCP) as [RP HRP].
  destruct (benv_exists _ _ HnP (proj1 (body_shape_fill _ _ HnP HshP)) HCP _ _ HRC HRP _ Hρ) as (ρk' & Hbk2 & Hρk).
  pose proof (functional_eval_benv _ _ _ _ Hbk2 Hbk) as <-.
  apply eval_gens_split in Hbk as (ρ1' & Hb1x & Hbk').
  pose proof (functional_eval_benv _ _ _ _ Hb1x Hb1) as ->.
  pose proof (skipn_benv_gens _ _ _ Hbk') as Hskip.
  assert (HlX : List.length (body_ctx (gens_append gm_nil 0 (List.firstn k gs))) = List.length (List.firstn k gs))
    by apply gens_body_ctx_length.
  rewrite <- HlX in Hskip.
  rewrite length_firstn in HlX; replace (Init.Nat.min k (List.length gs)) with k in HlX by lia.
  rewrite <- HlX.
  subst Φp; rewrite gens_body_ctx_base, <- app_assoc in HRP, HCP.
  exact (wk_coh_ex _ _ _ _ _ _ HH HCP HRP Hρk Hskip).
Qed.

(** Two bodies of one shape, each read in its parameters' context, related
    entry by entry through their filled-in entries. *)
Lemma fw_body : forall Φ Φ' Φx Φx' C C' RC RC',
    body_xp Θm Ξm C Φ Φx -> body_xp Θm Ξm C' Φ' Φx' ->
    body_shape Φ Φ' -> body_shape Φx Φx -> body_shape Φx' Φx' ->
    List.NoDup (gm_names Φx) -> List.NoDup (gm_names Φx') ->
    ⊨ body_ctx Φx ++ C -> ⊨ body_ctx Φx' ++ C' ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       (exists i, C ⊨ A[σ] ≈ A'[σ'] : Typeω@i) /\ C ⊨ M[σ] ≈ M'[σ'] : A[σ]) ->
    (forall y Φ0 pv U Φ0' pv' U' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_mod pv' U')) ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       C ⊨ᵐ me_lit U[σ]ᵘ ≈ me_lit U'[σ']ᵘ) ->
    (forall k Φ0 H Φ0' H' σ σ',
       nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> C ⊨ᵐ H[σ]ᵐ ≈ H'[σ']ᵐ) ->
    (forall k Ψo H, nth_error (body_opens Φ Φx) k = Some (Ψo, H) ->
       Ψo ++ C ⊨ᵐ H ≈ H /\ kinds_ok Θm Ξm (Ψo ++ C) H) ->
    (forall k Ψo H, nth_error (body_opens Φ' Φx') k = Some (Ψo, H) ->
       Ψo ++ C' ⊨ᵐ H ≈ H /\ kinds_ok Θm Ξm (Ψo ++ C') H) ->
    EF C ≈ C ∈ per_ctx_env ↘ RC -> EF C' ≈ C' ∈ per_ctx_env ↘ RC' ->
    forall ρa ρa', RC ρa ρa' -> RC' ρa' ρa' ->
    per_body ρa Φ ρa' Φ' /\
    exists Φk Φk', kbody gc_deps gc_stack ρa Φ Φk /\ body_eq_upto_types Φk Φx /\ kbody gc_deps gc_stack ρa' Φ' Φk' /\ body_eq_upto_types Φk' Φx'.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros [| Φ' y' E' | Φ' H' its'] * Hx Hx' Hs Hsx Hsx' Hnd Hnd' HC HC'
    HD HU HO Ho Ho' HRC HRC' ρa ρa' Hρ Hρ'; cbn [body_shape] in Hs; try contradiction.
  - inversion Hx; inversion Hx'; subst; split; [ constructor |].
    exists gm_nil, gm_nil; repeat split; constructor.
  - destruct Hs as (Hs & <- & HE).
    inversion Hx as [| ? ? Φx0 ? ? Hx0 |]; subst; inversion Hx' as [| ? ? Φx0' ? ? Hx0' |]; subst.
    cbn [body_opens body_opens_at gm_dropn] in HO, Ho, Ho'.
    cbn [body_shape] in Hsx, Hsx'; destruct Hsx as (Hsx & _ & HsE); destruct Hsx' as (Hsx' & _ & HsE').
    pose proof Hnd as Hnd0; cbn [gm_names] in Hnd0; inversion Hnd0 as [| ? ? _ Hnd00]; subst.
    pose proof Hnd' as Hnd0'; cbn [gm_names] in Hnd0'; inversion Hnd0' as [| ? ? _ Hnd00']; subst.
    pose proof (body_prefix_rel_ctx_wf _ _ _ _ HC) as HC0; pose proof (body_prefix_rel_ctx_wf _ _ _ _ HC') as HC0'.
    destruct (IH _ _ _ _ _ _ _ Hx0 Hx0' Hs Hsx Hsx' Hnd00 Hnd00' HC0 HC0'
                ltac:(intros * H1 H2 H3 H4; eapply HD; [ | | exact H3 | exact H4 ]; [ exact (prefix_ext_keep _ _ _ _ _ Hnd H1) | exact (prefix_ext_keep _ _ _ _ _ Hnd' H2) ])
                ltac:(intros * H1 H2 H3 H4; eapply HU; [ | | exact H3 | exact H4 ]; [ exact (prefix_ext_keep _ _ _ _ _ Hnd H1) | exact (prefix_ext_keep _ _ _ _ _ Hnd' H2) ])
                HO Ho Ho' HRC HRC' _ _ Hρ Hρ')
      as (Hb & Φk & Φk' & Hk & Hkx & Hk' & Hkx').
    (* the entries before, filled in, against their environments *)
    pose proof (body_xp_nopens _ _ _ _ _ Hx0) as Hn0; pose proof (body_xp_nopens _ _ _ _ _ Hx0') as Hn0'.
    destruct (gm_fill Φx0) as [σ0 |] eqn:Hf0; [| exfalso; exact (proj1 (body_shape_fill _ _ Hn0 Hsx) Hf0) ].
    destruct (gm_fill Φx0') as [σ0' |] eqn:Hf0'; [| exfalso; exact (proj1 (body_shape_fill _ _ Hn0' Hsx') Hf0') ].
    destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0]; destruct (rel_ctx_wf_per_ctx_env HC0') as [R0' HR0'].
    assert (HP : PER RC) by (eapply per_env_PER; exact HRC).
    assert (Hρρ : RC ρa ρa) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
    destruct (fill_rel _ _ _ Hn0 Hf0 HC0 _ _ HRC HR0 _ Hρρ) as (ρσ & ρ1 & Hev & Hb1 & H1).
    destruct (fill_rel _ _ _ Hn0' Hf0' HC0' _ _ HRC' HR0' _ Hρ') as (ρσ' & ρ1' & Hev' & Hb1' & H1').
    pose proof (gsub_valid (fill_gsub _ _ _ Hn0 Hf0 HC0)) as Hσ.
    pose proof (gsub_valid (fill_gsub _ _ _ Hn0' Hf0' HC0')) as Hσ'.
    assert (Hp : gm_prefix_upto (gm_ext Φx0 y E) y = Some (gm_ext Φx0 y E)) by (cbn; rewrite String.eqb_refl; reflexivity).
    assert (Hp' : gm_prefix_upto (gm_ext Φx0' y E') y = Some (gm_ext Φx0' y E')) by (cbn; rewrite String.eqb_refl; reflexivity).
    pose proof (proj2 (body_eq_upto_types_benv _ _ Hkx _ _) Hb1) as Hb1k; pose proof (proj2 (body_eq_upto_types_benv _ _ Hkx' _ _) Hb1') as Hb1k'.
    destruct E as [b pv A [M |] | pm U | | ], E' as [b' pv' A' [M' |] | pm' U' | | ]; cbn in HE, HsE, HsE'; try contradiction.
    + (* a definition each *)
      destruct (HD _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0') as [[j HAA'] HMM'].
      destruct (rel_ctx_wf_def_inv HC) as [[i HA] HM]; destruct (rel_ctx_wf_def_inv HC') as [[i' HA'] HM'].
      edestruct typ_bridge as (a & a' & Ha & Ha' & [R HR]);
        [ exact HA | exact Hσ | exact HRC | exact Hρ | exact HR0 | exact Hev | exact H1 | exact HAA'
        | exact HA' | exact Hσ' | exact HRC' | exact Hρ' | exact HR0' | exact Hev' | exact H1' |].
      edestruct elem_bridge as (m & m' & Hm & Hm' & Hmm');
        [ exact HA | exact HM | exact Hσ | exact HRC | exact Hρ | exact HR0 | exact Hev | exact H1 | exact HAA' | exact HMM'
        | exact HA' | exact HM' | exact Hσ' | exact HRC' | exact Hρ' | exact HR0' | exact Hev' | exact H1'
        | exact Ha | exact Ha' | exact HR |].
      split; [ eapply per_body_def; [ exact Hb | exact Hk | exact Hk' | exact Hb1k | exact Hb1k' | econstructor; eassumption
                                    | econstructor; eassumption ] |].
      exists (gm_ext Φk y (ge_def b pv A (Some M))), (gm_ext Φk' y (ge_def b' pv' A' (Some M'))).
      split; [ constructor; exact Hk |]; split; [ split; [ exact Hkx | split; [ reflexivity | left; reflexivity ] ] |].
      split; [ constructor; exact Hk' | split; [ exact Hkx' | split; [ reflexivity | left; reflexivity ] ] ].
    + (* a submodule each *)
      pose proof (HU _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0') as HUU'.
      pose proof (ruu_lit _ _ _ (rel_ctx_wf_mod_inv HC)) as HUv; pose proof (ruu_lit _ _ _ (rel_ctx_wf_mod_inv HC')) as HUv'.
      destruct (mod_bridge _ _ _ _ (me_lit U) (me_lit U') _ _ _ _ _ _ _ _ _ _ _ _
                  HUv Hσ HRC Hρ HR0 Hev H1 HUU' HUv' Hσ' HRC' Hρ' HR0' Hev' H1')
        as [h h' Hh Hh' Hhh].
      destruct U as [Δy Dy], U' as [Δy' Dy']; apply eval_me_lit_iff in Hh, Hh'.
      split; [ eapply per_body_mod; [ exact Hb | exact Hk | exact Hk' | exact Hb1k | exact Hb1k' | exact Hh | exact Hh' | exact Hhh ] |].
      exists (gm_ext Φk y (ge_mod pm (gu_mk Δy Dy))), (gm_ext Φk' y (ge_mod pm' (gu_mk Δy' Dy'))).
      split; [ constructor; exact Hk |]; split; [ split; [ exact Hkx | split; [ reflexivity | left; reflexivity ] ] |].
      split; [ constructor; exact Hk' | split; [ exact Hkx' | split; [ reflexivity | left; reflexivity ] ] ].
  - (* an open each *)
    destruct Hs as (Hs & <-).
    inversion Hx as [| | ? ? Φx0 ? ? Rm T gs Hx0 HRm HT Hgs Hok ]; subst.
    inversion Hx' as [| | ? ? Φx0' ? ? Rm' T' gs' Hx0' HRm' HT' Hgs' Hok' ]; subst.
    pose proof (items_gen_length _ _ _ _ _ _ _ Hgs) as Hl; pose proof (items_gen_length _ _ _ _ _ _ _ Hgs') as Hl'.
    rewrite (body_opens_at_open _ _ _ _ _ Hl), (body_opens_at_open _ _ _ _ _ Hl') in HO.
    rewrite (body_opens_open _ _ _ _ _ Hl) in Ho; rewrite (body_opens_open _ _ _ _ _ Hl') in Ho'.
    pose proof (body_shape_gens_l _ _ _ Hsx) as Hsx0; pose proof (body_shape_gens_l _ _ _ Hsx') as Hsx0'.
    pose proof Hnd as Hnd0; rewrite gens_append_names in Hnd0; apply NoDup_app_remove_l in Hnd0.
    pose proof Hnd' as Hnd0'; rewrite gens_append_names in Hnd0'; apply NoDup_app_remove_l in Hnd0'.
    pose proof HC as HCf; pose proof HC' as HCf'.
    rewrite gens_body_ctx_base, <- app_assoc in HC, HC'.
    pose proof (rel_ctx_wf_app_r _ _ HC) as HC0; pose proof (rel_ctx_wf_app_r _ _ HC') as HC0'.
    destruct (IH _ _ _ _ _ _ _ Hx0 Hx0' Hs Hsx0 Hsx0' Hnd0 Hnd0' HC0 HC0'
                ltac:(intros * H1 H2 H3 H4; eapply HD; [ | | exact H3 | exact H4 ]; [ exact (prefix_gens_keep _ _ _ _ _ Hnd H1) | exact (prefix_gens_keep _ _ _ _ _ Hnd' H2) ])
                ltac:(intros * H1 H2 H3 H4; eapply HU; [ | | exact H3 | exact H4 ]; [ exact (prefix_gens_keep _ _ _ _ _ Hnd H1) | exact (prefix_gens_keep _ _ _ _ _ Hnd' H2) ])
                (fun k => HO (S k)) (fun k => Ho (S k)) (fun k => Ho' (S k)) HRC HRC' _ _ Hρ Hρ')
      as (Hb & Φk & Φk' & Hk & Hkx & Hk' & Hkx').
    pose proof (body_xp_nopens _ _ _ _ _ Hx0) as Hn0; pose proof (body_xp_nopens _ _ _ _ _ Hx0') as Hn0'.
    destruct (gm_fill Φx0) as [σ0 |] eqn:Hf0; [| exfalso; exact (proj1 (body_shape_fill _ _ Hn0 Hsx0) Hf0) ].
    destruct (gm_fill Φx0') as [σ0' |] eqn:Hf0'; [| exfalso; exact (proj1 (body_shape_fill _ _ Hn0' Hsx0') Hf0') ].
    destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0]; destruct (rel_ctx_wf_per_ctx_env HC0') as [R0' HR0'].
    assert (HP : PER RC) by (eapply per_env_PER; exact HRC).
    assert (Hρρ : RC ρa ρa) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
    destruct (fill_rel _ _ _ Hn0 Hf0 HC0 _ _ HRC HR0 _ Hρρ) as (ρσ & ρ1 & Hev & Hb1 & H1).
    destruct (fill_rel _ _ _ Hn0' Hf0' HC0' _ _ HRC' HR0' _ Hρ') as (ρσ' & ρ1' & Hev' & Hb1' & H1').
    pose proof (gsub_valid (fill_gsub _ _ _ Hn0 Hf0 HC0)) as Hσ.
    pose proof (gsub_valid (fill_gsub _ _ _ Hn0' Hf0' HC0')) as Hσ'.
    destruct (Ho 0 _ _ eq_refl) as [HH Hko]; destruct (Ho' 0 _ _ eq_refl) as [HH' Hko'].
    pose proof (HO 0 _ _ _ _ _ _ eq_refl eq_refl Hf0 Hf0') as HHH'.
    destruct (mod_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH Hσ HRC Hρ HR0 Hev H1 HHH' HH' Hσ' HRC' Hρ' HR0' Hev' H1')
      as [h h' Hh Hh' Hhh].
    pose proof (proj2 (body_eq_upto_types_benv _ _ Hkx _ _) Hb1) as Hb1k; pose proof (proj2 (body_eq_upto_types_benv _ _ Hkx' _ _) Hb1') as Hb1k'.
    (* the kinds of the two opens *)
    assert (H11 : R0 ρ1 ρ1) by (assert (PER R0) by (eapply per_env_PER; exact HR0); etransitivity; [ symmetry; exact H1 | exact H1 ]).
    assert (H11' : R0' ρ1' ρ1') by (assert (PER R0') by (eapply per_env_PER; exact HR0'); etransitivity; [ symmetry; exact H1' | exact H1' ]).
    destruct (kind_eval_benv _ _ _ _ _ Hb1k _ (kshape_refl _ _ ρa)) as (σ1 & Hσ1 & Hs1).
    destruct (kind_eval_benv _ _ _ _ _ Hb1k' _ (kshape_refl _ _ ρa')) as (σ1' & Hσ1' & Hs1').
    pose proof (items_kgens _ _ _ _ _ _ Hgs Hko _ _ _ HR0 H11 Hs1) as Hkg.
    pose proof (items_kgens _ _ _ _ _ _ Hgs' Hko' _ _ _ HR0' H11' Hs1') as Hkg'.
    assert (Hko1 : kbody gc_deps gc_stack ρa (gm_open Φ H its) (gens_append Φk 0 (List.map ig_erase gs)))
      by (econstructor; [ exact Hk | exact Hσ1 | exact Hkg ]).
    assert (Hko1' : kbody gc_deps gc_stack ρa' (gm_open Φ' H' its) (gens_append Φk' 0 (List.map ig_erase gs')))
      by (econstructor; [ exact Hk' | exact Hσ1' | exact Hkg' ]).
    pose proof (body_eq_upto_types_gens gs _ _ 0 Hkx) as Hkxo; pose proof (body_eq_upto_types_gens gs' _ _ 0 Hkx') as Hkxo'.
    (* the whole blocks evaluate *)
    assert (Hnf : gm_nopens (gens_append Φx0 0 gs) = 0) by (rewrite gens_append_nopens; exact Hn0).
    assert (Hnf' : gm_nopens (gens_append Φx0' 0 gs') = 0) by (rewrite gens_append_nopens; exact Hn0').
    destruct (rel_ctx_wf_per_ctx_env HCf) as [Rf HRf]; destruct (rel_ctx_wf_per_ctx_env HCf') as [Rf' HRf'].
    destruct (benv_exists _ _ Hnf (proj1 (body_shape_fill _ _ Hnf Hsx)) HCf _ _ HRC HRf _ Hρρ) as (ρo & Hbo & _).
    destruct (benv_exists _ _ Hnf' (proj1 (body_shape_fill _ _ Hnf' Hsx')) HCf' _ _ HRC' HRf' _ Hρ') as (ρo' & Hbo' & _).
    apply (body_eq_upto_types_benv _ _ Hkxo) in Hbo; apply (body_eq_upto_types_benv _ _ Hkxo') in Hbo'.
    split; [| exists (gens_append Φk 0 (List.map ig_erase gs)), (gens_append Φk' 0 (List.map ig_erase gs'));
              repeat split; assumption ].
    eapply per_body_open; [ exact Hb | exact Hk | exact Hk' | exact Hb1k | exact Hb1k' | exact Hh | exact Hh' | exact Hhh
                          | exact Hko1 | exact Hko1' | exact Hbo | exact Hbo' | | | | ].
    + intros k ρk Hk0 Hbk.
      rewrite gm_dropn_gens in Hbk by (rewrite length_map; lia).
      rewrite length_map in Hbk; replace (List.length gs - (List.length its - k)) with k in Hbk by lia.
      rewrite firstn_map in Hbk.
      apply (body_eq_upto_types_benv _ _ (body_eq_upto_types_gens _ _ _ 0 Hkx)) in Hbk.
      assert (Hkk : k <= List.length gs) by lia.
      exact (open_coh_ex _ _ _ _ _ _ _ _ _ Hn0 HCf Hsx HH HRC Hρρ Hb1 Hkk Hbk).
    + intros k ρk Hk0 Hbk.
      rewrite gm_dropn_gens in Hbk by (rewrite length_map; lia).
      rewrite length_map in Hbk; replace (List.length gs' - (List.length its - k)) with k in Hbk by lia.
      rewrite firstn_map in Hbk.
      apply (body_eq_upto_types_benv _ _ (body_eq_upto_types_gens _ _ _ 0 Hkx')) in Hbk.
      assert (Hkk : k <= List.length gs') by lia.
      exact (open_coh_ex _ _ _ _ _ _ _ _ _ Hn0' HCf' Hsx' HH' HRC' Hρ' Hb1' Hkk Hbk).
    + intros k ρk hk Hk0 Hbk Hhk.
      rewrite gm_dropn_gens in Hbk by (rewrite length_map; lia).
      rewrite length_map in Hbk; replace (List.length gs - (List.length its - k)) with k in Hbk by lia.
      rewrite firstn_map in Hbk.
      apply (body_eq_upto_types_benv _ _ (body_eq_upto_types_gens _ _ _ 0 Hkx)) in Hbk.
      assert (Hkk : k <= List.length gs) by lia.
      exact (open_coh _ _ _ _ _ _ _ _ _ _ _ Hn0 HCf Hsx HH HRC Hρρ Hb1 Hh Hkk Hbk Hhk).
    + intros k ρk hk Hk0 Hbk Hhk.
      rewrite gm_dropn_gens in Hbk by (rewrite length_map; lia).
      rewrite length_map in Hbk; replace (List.length gs' - (List.length its - k)) with k in Hbk by lia.
      rewrite firstn_map in Hbk.
      apply (body_eq_upto_types_benv _ _ (body_eq_upto_types_gens _ _ _ 0 Hkx')) in Hbk.
      assert (Hkk : k <= List.length gs') by lia.
      exact (open_coh _ _ _ _ _ _ _ _ _ _ _ Hn0' HCf' Hsx' HH' HRC' Hρ' Hb1' Hh' Hkk Hbk Hhk).
Qed.

(** ** Related Closures *)

(** The parameters of two units, outermost first: [ts] and [ts'] are the
    telescopes reversed. *)
Lemma walk_params : forall ts ts' Γ Γ' RΓ R D D',
    tele_ass ts -> tele_ass ts' -> List.length ts = List.length ts' ->
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ RΓ ->
    EF rev ts ++ Γ ≈ rev ts' ++ Γ' ∈ per_ctx_env ↘ R ->
    (forall ρ ρ', R ρ ρ' -> exists h h', ⟦ nil ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ h /\
                                     ⟦ nil ⊢ D' ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ' ↘ h' /\ per_dmod h h') ->
    forall ρ ρ', RΓ ρ ρ' -> exists h h', ⟦ rev ts ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ h /\
                                     ⟦ rev ts' ⊢ D' ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ' ↘ h' /\ per_dmod h h'.
Proof.
  induction ts as [| e ts IH]; intros [| e' ts'] * Hts Hts' Hl HΓ HR HD ρ ρ' Hρ; cbn in Hl; try discriminate.
  - apply HD.
    assert (HRR : R <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    apply HRR, Hρ.
  - inversion Hts as [| ? ? [A ->] Hts0]; inversion Hts' as [| ? ? [A' ->] Hts0']; subst.
    cbn [rev] in HR |- *; rewrite <- !app_assoc in HR; cbn [app] in HR.
    destruct (per_ctx_env_app_tail (rev ts) (rev ts') _ _ _ ltac:(rewrite !length_rev; congruence) HR)
      as [R1 HR1].
    destruct (per_ctx_env_cons_clean_inversion HΓ HR1) as (i & head_rel & Hhead & HE).
    destruct (Hhead _ _ Hρ) as [a a' Ha Ha' HRa].
    eexists _, _; split; [ apply close_unsat; rewrite length_app; cbn; lia |].
    split; [ apply close_unsat; rewrite length_app; cbn; lia |].
    eapply per_dmod_closure_step; [ exact Ha | exact Ha' | exact HRa |].
    intros c c' Hc.
    eapply IH; [ eassumption | eassumption | congruence | exact HR1 | exact HR | exact HD |].
    apply HE; exists Hρ; exact Hc.
Qed.

(** The heterogeneous relation of two extensions of one context, at the
    two sides. *)
Lemma ext_rel_sides : forall C C' R RC RC', EF C ≈ C' ∈ per_ctx_env ↘ R ->
    EF C ≈ C ∈ per_ctx_env ↘ RC -> EF C' ≈ C' ∈ per_ctx_env ↘ RC' ->
    forall ρ ρ', R ρ ρ' -> RC ρ ρ' /\ RC' ρ' ρ'.
Proof.
  intros * HR HRC HRC' ρ ρ' Hρ.
  assert (E1 : R <~> RC) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E2 : R <~> RC') by (eapply per_ctx_env_left_irrel; eassumption).
  split; [ apply E1, Hρ |].
  apply E2; eapply per_env_trans; [ exact HR | eapply per_env_sym; [ exact HR | exact Hρ ] | exact Hρ ].
Qed.

Section BodyRel.
  Variables (Γ Δ Δ' : ctx) (Φ Φ' Φx Φx' : gmod).
  Hypotheses (HΔ : Γ ⊨ˣ Δ ≈ Δ') (Ha : tele_ass Δ) (Ha' : tele_ass Δ') (Hl : List.length Δ = List.length Δ')
    (Hx : body_xp Θm Ξm (Δ ++ Γ) Φ Φx) (Hx' : body_xp Θm Ξm (Δ' ++ Γ) Φ' Φx')
    (Hs : body_shape Φ Φ') (Hsx : body_shape Φx Φx) (Hsx' : body_shape Φx' Φx')
    (Hsw : body_shape Φ Φ) (Hsw' : body_shape Φ' Φ')
    (Hnd : List.NoDup (gm_names Φx)) (Hnd' : List.NoDup (gm_names Φx'))
    (HC : ⊨ body_ctx Φx ++ Δ ++ Γ) (HC' : ⊨ body_ctx Φx' ++ Δ' ++ Γ).
  Hypothesis HD : forall y Φ0 b pv A M Φ0' b' pv' A' M' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
      (exists i, Δ ++ Γ ⊨ A[σ] ≈ A'[σ'] : Typeω@i) /\ Δ ++ Γ ⊨ M[σ] ≈ M'[σ'] : A[σ].
  Hypothesis HU : forall y Φ0 pv U Φ0' pv' U' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_mod pv' U')) ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
      Δ ++ Γ ⊨ᵐ me_lit U[σ]ᵘ ≈ me_lit U'[σ']ᵘ.
  Hypothesis HO : forall k Φ0 H Φ0' H' σ σ',
      nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Δ ++ Γ ⊨ᵐ H[σ]ᵐ ≈ H'[σ']ᵐ.
  Hypothesis Ho : forall k Ψo H, nth_error (body_opens Φ Φx) k = Some (Ψo, H) ->
      Ψo ++ Δ ++ Γ ⊨ᵐ H ≈ H /\ kinds_ok Θm Ξm (Ψo ++ Δ ++ Γ) H.
  Hypothesis Ho' : forall k Ψo H, nth_error (body_opens Φ' Φx') k = Some (Ψo, H) ->
      Ψo ++ Δ' ++ Γ ⊨ᵐ H ≈ H /\ kinds_ok Θm Ξm (Ψo ++ Δ' ++ Γ) H.

  Lemma rel_closure_body : forall RΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
      forall ρ ρ', RΓ ρ ρ' -> rel_mexp (me_lit (gu_open Δ Φ)) ρ (me_lit (gu_open Δ' Φ')) ρ'.
  Proof.
    intros RΓ HΓ ρ ρ' Hρ.
    destruct HΔ as [HΔΓ HΔ'Γ [Rh HRh]].
    destruct (rel_ctx_wf_per_ctx_env HΔΓ) as [RC HRC]; destruct (rel_ctx_wf_per_ctx_env HΔ'Γ) as [RC' HRC'].
    rewrite <- (rev_involutive Δ), <- (rev_involutive Δ') in HRh.
    destruct (walk_params (rev Δ) (rev Δ') Γ Γ RΓ Rh (md_body sm_open Φ) (md_body sm_open Φ')
                (Forall_rev Ha) (Forall_rev Ha') ltac:(rewrite !length_rev; exact Hl) HΓ HRh
                ltac:(intros ρa ρa' Hρa; rewrite !rev_involutive in HRh;
                      destruct (ext_rel_sides _ _ _ _ _ HRh HRC HRC' _ _ Hρa) as [H1 H2];
                      destruct (fw_body _ _ _ _ _ _ _ _ Hx Hx' Hs Hsx Hsx' Hnd Hnd' HC HC' HD HU HO Ho Ho' HRC HRC' _ _ H1 H2)
                        as (Hb & _);
                      eexists _, _; split; [ apply eval_close_body | split; [ apply eval_close_body | apply per_dmod_body; exact Hb ] ])
                _ _ Hρ)
      as (h & h' & Hh & Hh' & Hhh).
    rewrite !rev_involutive in Hh, Hh'.
    exists h h'; [ apply eval_me_lit; exact Hh | apply eval_me_lit; exact Hh' | exact Hhh ].
  Qed.

  Lemma rel_lit_body : Γ ⊨ᵐ me_lit (gu_open Δ Φ) ≈ me_lit (gu_open Δ' Φ').
  Proof.
    pose proof (rel_ctx_wf_app_r _ _ (rel_ctx_wf_app_r _ _ HC)) as HΓs.
    destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HΓ].
    refine (mk_rel_modexp_under_ctx _ _ _ RΓ HΓ _); intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
    assert (HP' : PER R') by (eapply per_env_PER; exact HΓ').
    assert (Hρρ : R' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
    assert (Hρ'ρ' : R' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
    pose proof (rel_sub_under_ctx_at' Hσ HΓ' HΓ _ _ _ _ Hρ Hev Hev') as Hρσ.
    destruct (unit_sub_link_body _ _ _ _ _ _ _ _ _ _ Ha Hx Hsw Hsx HC Ho Hσ HΓ' Hρρ Hev) as [v1 v2 Hv1 Hv2 V12].
    destruct (unit_sub_link_body _ _ _ _ _ _ _ _ _ _ Ha' Hx' Hsw' Hsx' HC' Ho' (rel_sub_under_ctx_refl_right Hσ) HΓ' Hρ'ρ' Hev')
      as [v4 v3 Hv4 Hv3 V43].
    destruct (rel_closure_body _ HΓ _ _ Hρσ) as [w2 w3 Hw2 Hw3 W23].
    pose proof (functional_eval_modexp _ _ _ _ Hw2 Hv2) as ->; pose proof (functional_eval_modexp _ _ _ _ Hw3 Hv3) as ->.
    apply (mk_rel_modexp v1 v2 v3 v4); try assumption.
    split; [ exact V12 | split; [ exact W23 | apply per_dmod_sym; exact V43 ] ].
  Qed.
End BodyRel.

Lemma rel_closure_alias : forall Γ Δ Δ' E E' RΓ,
    Γ ⊨ˣ Δ ≈ Δ' -> tele_ass Δ -> tele_ass Δ' -> List.length Δ = List.length Δ' ->
    Δ ++ Γ ⊨ᵐ E ≈ E' -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    forall ρ ρ', RΓ ρ ρ' -> rel_mexp (me_lit (gu_mk Δ (md_alias E))) ρ (me_lit (gu_mk Δ' (md_alias E'))) ρ'.
Proof.
  intros * HΔ Ha Ha' Hl HE HΓ ρ ρ' Hρ.
  destruct HΔ as [HΔΓ HΔ'Γ [Rh HRh]].
  destruct (rel_ctx_wf_per_ctx_env HΔΓ) as [RC HRC]; destruct (rel_ctx_wf_per_ctx_env HΔ'Γ) as [RC' HRC'].
  pose proof HRh as HRh0.
  rewrite <- (rev_involutive Δ), <- (rev_involutive Δ') in HRh.
  destruct (walk_params (rev Δ) (rev Δ') Γ Γ RΓ Rh (md_alias E) (md_alias E')
              (Forall_rev Ha) (Forall_rev Ha') ltac:(rewrite !length_rev; exact Hl) HΓ HRh
              ltac:(intros ρa ρa' Hρa;
                    destruct (ext_rel_sides _ _ _ _ _ HRh0 HRC HRC' _ _ Hρa) as [H1 _];
                    destruct (rel_modexp_at _ _ _ _ _ HE HRC _ _ H1) as (h & h' & Hh & Hh' & Hhh);
                    exists h, h'; split; [ apply eval_close_alias0; exact Hh | split; [ apply eval_close_alias0; exact Hh' | exact Hhh ] ])
              _ _ Hρ)
    as (h & h' & Hh & Hh' & Hhh).
  rewrite !rev_involutive in Hh, Hh'.
  exists h h'; [ apply eval_me_lit; exact Hh | apply eval_me_lit; exact Hh' | exact Hhh ].
Qed.

Lemma rel_lit_alias : forall Γ Δ Δ' E E',
    Γ ⊨ˣ Δ ≈ Δ' -> tele_ass Δ -> tele_ass Δ' -> List.length Δ = List.length Δ' ->
    Δ ++ Γ ⊨ᵐ E ≈ E' -> Δ' ++ Γ ⊨ᵐ E' ≈ E' ->
    Γ ⊨ᵐ me_lit (gu_mk Δ (md_alias E)) ≈ me_lit (gu_mk Δ' (md_alias E')).
Proof.
  intros * HΔ Ha Ha' Hl HE HE'.
  pose proof HΔ as [HΔΓ HΔ'Γ _].
  destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_app_r _ _ HΔΓ)) as [RΓ HΓ].
  refine (mk_rel_modexp_under_ctx _ _ _ RΓ HΓ _); intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HP' : PER R') by (eapply per_env_PER; exact HΓ').
  assert (Hρρ : R' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  assert (Hρ'ρ' : R' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
  pose proof (rel_sub_under_ctx_at' Hσ HΓ' HΓ _ _ _ _ Hρ Hev Hev') as Hρσ.
  destruct (unit_sub_link_alias _ _ _ _ _ _ _ _ _ Ha HΔΓ (rel_modexp_refl_left HE) Hσ HΓ' Hρρ Hev) as [v1 v2 Hv1 Hv2 V12].
  destruct (unit_sub_link_alias _ _ _ _ _ _ _ _ _ Ha' HΔ'Γ HE' (rel_sub_under_ctx_refl_right Hσ) HΓ' Hρ'ρ' Hev')
    as [v4 v3 Hv4 Hv3 V43].
  destruct (rel_closure_alias _ _ _ _ _ _ HΔ Ha Ha' Hl HE HΓ _ _ Hρσ) as [w2 w3 Hw2 Hw3 W23].
  pose proof (functional_eval_modexp _ _ _ _ Hw2 Hv2) as ->; pose proof (functional_eval_modexp _ _ _ _ Hw3 Hv3) as ->.
  apply (mk_rel_modexp v1 v2 v3 v4); try assumption.
  split; [ exact V12 | split; [ exact W23 | apply per_dmod_sym; exact V43 ] ].
Qed.

End Fixed_GCtx.
