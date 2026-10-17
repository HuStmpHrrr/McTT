(** * Semantic Members of Module Expressions

    A term member of a module expression [K] is valid at a type [A] when, at
    every environment of the context, every module value related to [K]'s
    selects it, related at [A] to [K]'s own ([smem]); and a module member,
    when the submodule every related value selects is related to a given
    module expression's value ([smod]).  So the members of a module
    expression related to [K] are related to [K]'s ([rel_mem_of_smem],
    [rel_sel_of_smod]).  Selection from a value lacking a parameter commutes
    with application ([sel_app_comm]), and a member, which is evaluated by
    the root of its module expression and the arguments after it, is the
    member selected from the expression's value ([eval_mem_of_sel]). *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases UniverseCases SubstitutionCases LetCases UnitCases ModuleVal.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Values of Module Expressions *)

Lemma functional_eval_sel : forall h x r1 r2,
    h ·ₜ x gc_deps ⍮ gc_stack ↘ r1 -> h ·ₜ x gc_deps ⍮ gc_stack ↘ r2 -> r1 = r2.
Proof. intros; pose proof (@functional_eval gc_deps gc_stack) as Hf; destruct_all; eauto. Qed.

Lemma functional_eval_selc : forall h ch r1 r2,
    h ·ₜ* ch gc_deps ⍮ gc_stack ↘ r1 -> h ·ₜ* ch gc_deps ⍮ gc_stack ↘ r2 -> r1 = r2.
Proof. intros; pose proof (@functional_eval gc_deps gc_stack) as Hf; destruct_all; eauto. Qed.

Lemma functional_eval_apps : forall f args r1 r2,
    $*| f & args | gc_deps ⍮ gc_stack ↘ r1 -> $*| f & args | gc_deps ⍮ gc_stack ↘ r2 -> r1 = r2.
Proof. intros; pose proof (@functional_eval gc_deps gc_stack) as Hf; destruct_all; eauto. Qed.

Lemma eval_app_apps1 : forall f c r, $| f & c |↘ r <-> $*| f & (c :: nil) | gc_deps ⍮ gc_stack ↘ r.
Proof.
  intros; split; intros H; [ econstructor; [ exact H | constructor ] |].
  inversion H; subst; match goal with Hn : eval_apps _ _ _ nil _ |- _ => inversion Hn; subst end; assumption.
Qed.

(** ** Selection from Values Lacking a Parameter *)

Lemma selc_member_ex : forall h ch0 ch, ch <> nil ->
    dm_member h ch0 ·ₜ* ch gc_deps ⍮ gc_stack ↘ d_member h (ch0 ++ ch).
Proof.
  intros h ch0 ch; revert ch0; induction ch as [| y ch IH]; intros ch0 Hch; [ congruence |].
  destruct ch as [| z ch].
  - constructor; constructor.
  - econstructor; [ constructor |].
    replace (ch0 ++ y :: z :: ch) with ((ch0 ++ y :: nil) ++ z :: ch) by (rewrite <- app_assoc; reflexivity).
    apply IH; discriminate.
Qed.

Lemma selc_unsat_ex : forall Δ D ρ ch, 0 < List.length Δ -> ch <> nil ->
    dm_local Δ D ρ ·ₜ* ch gc_deps ⍮ gc_stack ↘ d_member (dm_local Δ D ρ) ch.
Proof.
  intros * Hl Hch; destruct ch as [| y ch]; [ congruence |].
  destruct ch as [| z ch].
  - constructor; constructor; exact Hl.
  - econstructor; [ apply eval_selm_unsat; exact Hl |].
    apply (selc_member_ex _ (y :: nil) (z :: ch)); discriminate.
Qed.

(** A member of a value given one more argument is the member of the value,
    applied to it. *)
Lemma sel_appm : forall ch, ch <> nil -> forall h0 n h r, $ᵐ| h0 & n | gc_deps ⍮ gc_stack ↘ h ->
    h ·ₜ* ch gc_deps ⍮ gc_stack ↘ r ->
    exists f, h0 ·ₜ* ch gc_deps ⍮ gc_stack ↘ f /\ $| f & n |↘ r.
Proof.
  induction ch as [| y ch IH]; intros Hch h0 n h r Hap Hc; [ congruence |].
  inversion Hap; subst.
  - (* a global module *)
    inversion Hc; subst.
    + match goal with Hs : eval_sel _ _ _ _ _ |- _ => apply eval_sel_global_inv in Hs as (f0 & Hf0 & Ha) end.
      apply eval_apps_app in Ha as (f1 & Hf1 & Ha1).
      exists f1; split; [ constructor; eapply eval_sel_global_apps; eassumption | apply eval_app_apps1; exact Ha1 ].
    + match goal with Hc' : eval_selc _ _ _ ch r |- _ => assert (Hch' : ch <> nil) by (intros ->; inversion Hc') end.
      match goal with Hs : eval_selm _ _ _ _ _ |- _ => inversion Hs; subst end.
      * destruct (IH Hch' (dm_global (qname_app p (y :: nil)) args) n _ r ltac:(constructor) ltac:(eassumption)) as (f & Hf & Ha).
        exists f; split; [ econstructor; [ eapply eval_selm_global; eassumption | exact Hf ] | exact Ha ].
      * match goal with Ha : eval_appms _ _ _ _ _ |- _ => apply appms_snoc in Ha as (h3 & Ha1 & Ha2) end.
        destruct (IH Hch' h3 n _ r Ha2 ltac:(eassumption)) as (f & Hf & Ha).
        exists f; split; [ econstructor; [ eapply eval_selm_global_alias; eassumption | exact Hf ] | exact Ha ].
  - (* a closure lacking a parameter *)
    exists (d_member (dm_local (Δ ++ ce_ass A :: nil) D ρ) (y :: ch)); split.
    + apply selc_unsat_ex; [ rewrite List.length_app; cbn; lia | exact Hch ].
    + econstructor; eassumption.
  - (* a submodule closure *)
    exists (d_member h1 (ch0 ++ y :: ch)); split; [ apply selc_member_ex; exact Hch |].
    econstructor; [ eassumption |].
    apply eval_selc_app; [ exact Hch | eexists; split; eassumption ].
Qed.

(** A chain of members of a module expression's value, read off the root of
    the expression and applied to the expression's arguments. *)
Lemma eval_spine_of_selc : forall H ρ h, ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h ->
    forall R args pre, modexp_spine H = (R, args, pre) ->
    forall ch r, ch <> nil -> h ·ₜ* ch gc_deps ⍮ gc_stack ↘ r ->
    exists hr f ns, ⟦ R ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ hr /\ hr ·ₜ* (pre ++ ch) gc_deps ⍮ gc_stack ↘ f /\
      ⟦ args ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns /\ $*| f & ns | gc_deps ⍮ gc_stack ↘ r.
Proof.
  induction H as [fp | x | H IH y | H IH N | U]; intros ρ h He R args pre Hs ch r Hch Hc; cbn in Hs.
  1,2,5: injection Hs as <- <- <-; exists h, r, nil; repeat split; [ assumption | assumption | constructor | constructor ].
  - destruct (modexp_spine H) as [[R' args'] pre'] eqn:E; injection Hs as <- <- <-.
    inversion He; subst.
    destruct (IH _ _ ltac:(eassumption) _ _ _ eq_refl (y :: ch) r ltac:(discriminate) ltac:(econstructor; eassumption))
      as (hr & f & ns & Hr & Hf & Hns & Ha).
    exists hr, f, ns; repeat split; try assumption; rewrite <- app_assoc; exact Hf.
  - destruct (modexp_spine H) as [[R' args'] pre'] eqn:E; injection Hs as <- <- <-.
    inversion He; subst.
    destruct (sel_appm _ Hch _ _ _ _ ltac:(eassumption) Hc) as (f1 & Hf1 & Ha1).
    destruct (IH _ _ ltac:(eassumption) _ _ _ eq_refl ch f1 Hch Hf1) as (hr & f & ns & Hr & Hf & Hns & Ha).
    exists hr, f, (ns ++ n :: nil); repeat split; try assumption.
    + apply eval_exps_app; [ exact Hns | econstructor; [ eassumption | constructor ] ].
    + apply eval_apps_app; exists f1; split; [ exact Ha | apply eval_app_apps1; exact Ha1 ].
Qed.

Lemma eval_mem_of_sel : forall H ρ h x r,
    ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h -> h ·ₜ x gc_deps ⍮ gc_stack ↘ r -> ⟦ a_mem H x ⟧ ρ ↘ r.
Proof.
  intros * He Hs.
  destruct (modexp_spine H) as [[R args] pre] eqn:E.
  destruct (eval_spine_of_selc _ _ _ He _ _ _ E (x :: nil) r ltac:(discriminate) ltac:(constructor; exact Hs))
    as (hr & f & ns & Hr & Hf & Hns & Ha).
  apply (eval_mem_spine gc_deps gc_stack _ _ _ _ _ _ _ E); do 3 eexists; eauto.
Qed.

(** Selecting a term member from a value lacking a parameter commutes with
    giving it that parameter. *)
Lemma sel_app_comm : forall h a, nextparam h a ->
    forall c hc, $ᵐ| h & c | gc_deps ⍮ gc_stack ↘ hc ->
    forall x f, h ·ₜ x gc_deps ⍮ gc_stack ↘ f ->
    forall r, $| f & c |↘ r <-> hc ·ₜ x gc_deps ⍮ gc_stack ↘ r.
Proof.
  intros * Hn * Hh * Hs r; inversion Hn; subst.
  - (* a closure *)
    inversion Hs; subst; [ | destruct Δ; discriminate ].
    split; intros Hx.
    + inversion Hx; subst.
      match goal with H1 : eval_appm _ _ ?h c ?a, H2 : eval_appm _ _ ?h c ?b |- _ =>
        assert_fails (constr_eq a b); pose proof (functional_eval_appm _ _ _ _ H1 H2) as <- end.
      match goal with Hc : _ ·ₜ* (x :: nil) _ ⍮ _ ↘ r |- _ => inversion Hc; subst end; [ assumption |].
      match goal with Hc : _ ·ₜ* nil _ ⍮ _ ↘ r |- _ => inversion Hc end.
    + econstructor; [ exact Hh | constructor; exact Hx ].
  - (* a global module: its member applied to one more argument *)
    apply eval_sel_global_inv in Hs as (f0 & Hf0 & Ha).
    inversion Hh; subst.
    split; intros Hx.
    + eapply eval_sel_global_apps; [ exact Hf0 |].
      apply eval_apps_app; exists f; split; [ exact Ha | apply eval_app_apps1; exact Hx ].
    + apply eval_sel_global_inv in Hx as (f1 & Hf1 & Ha1).
      pose proof (functional_eval_sel _ _ _ _ Hf1 Hf0) as ->.
      apply eval_apps_app in Ha1 as (f2 & Hf2 & Ha2).
      pose proof (functional_eval_apps _ _ _ _ Hf2 Ha) as ->.
      apply eval_app_apps1; exact Ha2.
  - (* a submodule closure *)
    inversion Hs; subst; inversion Hh; subst.
    split; intros Hx.
    + inversion Hx; subst.
      match goal with H1 : eval_appm _ _ ?h c ?a, H2 : eval_appm _ _ ?h c ?b |- _ =>
        assert_fails (constr_eq a b); pose proof (functional_eval_appm _ _ _ _ H1 H2) as <- end.
      match goal with Hc : _ ·ₜ* (ch ++ x :: nil) _ ⍮ _ ↘ r |- _ =>
        apply eval_selc_app in Hc as (gc & Hgc & Hgy); [| discriminate ] end.
      match goal with H1 : eval_selmc _ _ ?h ch ?a, H2 : eval_selmc _ _ ?h ch ?b |- _ =>
        assert_fails (constr_eq a b); pose proof (functional_eval_selmc _ _ _ _ H1 H2) as <- end.
      inversion Hgy; subst; [ assumption | match goal with Hc : _ ·ₜ* nil _ ⍮ _ ↘ r |- _ => inversion Hc end ].
    + econstructor; [ eassumption |].
      apply eval_selc_app; [ discriminate | eexists; split; [ eassumption | constructor; exact Hx ] ].
Qed.

(** A value lacking a parameter has a term member wherever it has one at an
    argument. *)
Lemma sel_of_appm : forall h a, nextparam h a -> forall c hc x r,
    $ᵐ| h & c | gc_deps ⍮ gc_stack ↘ hc -> hc ·ₜ x gc_deps ⍮ gc_stack ↘ r ->
    exists f, h ·ₜ x gc_deps ⍮ gc_stack ↘ f.
Proof.
  intros * Hn * Hh Hs; inversion Hn; subst.
  - eexists; apply eval_sel_unsat; rewrite List.length_app; cbn; lia.
  - inversion Hh; subst.
    apply eval_sel_global_inv in Hs as (f0 & Hf0 & Ha).
    apply eval_apps_app in Ha as (f1 & Hf1 & _).
    exists f1; eapply eval_sel_global_apps; eassumption.
  - eexists; apply eval_sel_member.
Qed.

(** The four values of a valid module expression are related to the one at
    the substituted environment. *)
Lemma rel_mod_hub : forall H σ ρ ρσ H' σ' ρ' ρ'σ',
    rel_mod H σ ρ ρσ H' σ' ρ' ρ'σ' ->
    exists h1 h2 h3 h4,
      eval_modexp gc_deps gc_stack H[σ]ᵐ ρ h1 /\ ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρσ ↘ h2 /\
      ⟦ H' ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ'σ' ↘ h3 /\ eval_modexp gc_deps gc_stack H'[σ']ᵐ ρ' h4 /\
      per_dmod h1 h3 /\ per_dmod h2 h3 /\ per_dmod h3 h3 /\ per_dmod h4 h3.
Proof.
  intros * [h1 h2 h3 h4 E1 E2 E3 E4 (C12 & C23 & C34)].
  exists h1, h2, h3, h4; repeat split; try assumption.
  - exact (per_dmod_trans _ _ _ C12 C23).
  - exact (per_dmod_trans _ _ _ (per_dmod_sym _ _ C23) C23).
  - exact (per_dmod_sym _ _ C34).
Qed.

(** ** Semantic Members *)

(** The member [x] of the module value [k], related at [R] to that of any
    value related to [k]. *)
Definition mty (k : dmod) (x : String.string) (R : relation domain) : Prop :=
  forall h, per_dmod h k -> exists r r', h ·ₜ x gc_deps ⍮ gc_stack ↘ r /\ k ·ₜ x gc_deps ⍮ gc_stack ↘ r' /\ R r r'.

Definition smem (Γ : ctx) (K : modexp) (x : String.string) (A : typ) (om : option exp) : Prop :=
  (exists i, Γ ⊨ A : Typeω@i) /\ (forall M, om = Some M -> Γ ⊨ M : A) /\
  forall R, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> forall ρ, R ρ ρ ->
    exists k a i RA, ⟦ K ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ k /\ ⟦ A ⟧ ρ ↘ a /\ per_univ_elem i RA a a /\ mty k x RA /\
      forall M, om = Some M -> exists m r, ⟦ M ⟧ ρ ↘ m /\ k ·ₜ x gc_deps ⍮ gc_stack ↘ r /\ RA m r.

(** The submodule [y] of [K] at every environment, from any value related
    to [K]'s, related to the value of [V]. *)
Definition smod (Γ : ctx) (K : modexp) (y : String.string) (V : modexp) : Prop :=
  forall R, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> forall ρ, R ρ ρ ->
    exists k v, ⟦ K ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ k /\ ⟦ V ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ v /\
      forall h, per_dmod h k -> exists r, h ·ₘ y gc_deps ⍮ gc_stack ↘ r /\ per_dmod r v.

(** ** Members of Related Module Expressions *)

Lemma rel_mem_of_smem : forall Γ H K x A om,
    Γ ⊨ᵐ H ≈ K -> smem Γ K x A om -> Γ ⊨ a_mem H x ≈ a_mem K x : A.
Proof.
  intros * [R [HR HH]] [[i HA] [_ HS]].
  pose proof (rel_exp_of_typ_inversion HA) as [RA0 [HRA HAgen]].
  exists R, HR, i; intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  pose proof (rel_sub_under_ctx_at' Hσ HΓ' HR _ _ _ _ Hρ Hev Hev') as Hρσ.
  assert (HP : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρσ' : R ρ'σ' ρ'σ') by (etransitivity; [ symmetry; exact Hρσ | exact Hρσ ]).
  destruct (rel_exp_implies_rel_typ (HAgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')) as [Rel HT].
  exists Rel; split; [ exact HT |].
  destruct HT as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 (T12 & T23 & T34)].
  assert (HPR : PER Rel) by (eapply per_elem_PER; exact T23).
  destruct (rel_mod_hub _ _ _ _ _ _ _ _ (HH _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev'))
    as (h1 & h2 & h3 & h4 & E1 & E2 & E3 & E4 & D1 & D2 & D3 & D4).
  destruct (HS _ HR _ Hρσ') as (k & a & j & RA & Hk & Ha & HRA' & Hm & _).
  pose proof (functional_eval_modexp _ _ _ _ Hk E3) as ->.
  pose proof (functional_eval_exp _ _ _ _ Ha Ha3) as ->.
  assert (E : RA <~> Rel) by (eapply per_univ_elem_right_irrel; [ exact HRA' | etransitivity; [ symmetry; exact T23 | exact T23 ] ]).
  destruct (Hm _ D1) as (v1 & v & S1 & S3 & V1).
  destruct (Hm _ D2) as (v2 & v' & S2 & S3' & V2).
  destruct (Hm _ D4) as (v4 & v'' & S4 & S3'' & V4).
  pose proof (functional_eval_sel _ _ _ _ S3 S3') as <-.
  pose proof (functional_eval_sel _ _ _ _ S3 S3'') as <-.
  apply E in V1, V2, V4.
  apply (mk_rel_exp v1 v2 v v4); try (eapply eval_mem_of_sel; eassumption).
  cbn; split; [ etransitivity; [ exact V1 | symmetry; exact V2 ] |]; split; [ exact V2 | symmetry; exact V4 ].
Qed.

Lemma rel_mem_red_of_smem : forall Γ H K x A M,
    Γ ⊨ᵐ H ≈ K -> smem Γ K x A (Some M) -> Γ ⊨ a_mem H x ≈ M : A.
Proof.
  intros * [R [HR HH]] [[i HA] [HM HS]].
  pose proof (rel_exp_of_typ_inversion HA) as [RA0 [HRA HAgen]].
  pose proof (HM _ eq_refl) as [RM [HRM [iM HMgen]]].
  exists R, HR, i; intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  pose proof (rel_sub_under_ctx_at' Hσ HΓ' HR _ _ _ _ Hρ Hev Hev') as Hρσ.
  assert (HP : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρσ' : R ρ'σ' ρ'σ') by (etransitivity; [ symmetry; exact Hρσ | exact Hρσ ]).
  destruct (rel_exp_implies_rel_typ (HAgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')) as [Rel HT].
  exists Rel; split; [ exact HT |].
  destruct HT as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 (T12 & T23 & T34)].
  assert (HPR : PER Rel) by (eapply per_elem_PER; exact T23).
  destruct (HMgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [RelM [[b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 (B12 & B23 & B34)] [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 (M12 & M23 & M34)]]].
  functional_eval_rewrite_clear.
  assert (EM : RelM <~> Rel) by (eapply per_univ_elem_right_irrel; [ exact B23 | exact T23 ]).
  destruct (rel_mod_hub _ _ _ _ _ _ _ _ (HH _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev'))
    as (h1 & h2 & h3 & h4 & E1 & E2 & E3 & E4 & D1 & D2 & D3 & D4).
  destruct (HS _ HR _ Hρσ') as (k & a & j & RA & Hk & Ha & HRA' & Hm & Hred).
  pose proof (functional_eval_modexp _ _ _ _ Hk E3) as ->.
  pose proof (functional_eval_exp _ _ _ _ Ha Ha3) as ->.
  assert (E : RA <~> Rel) by (eapply per_univ_elem_right_irrel; [ exact HRA' | etransitivity; [ symmetry; exact T23 | exact T23 ] ]).
  destruct (Hred _ eq_refl) as (m & v & Hm0 & Hv & HRv).
  pose proof (functional_eval_exp _ _ _ _ Hm0 Hm3) as ->.
  destruct (Hm _ D1) as (v1 & v' & S1 & S3 & V1).
  destruct (Hm _ D2) as (v2 & v'' & S2 & S3' & V2).
  pose proof (functional_eval_sel _ _ _ _ Hv S3) as <-.
  pose proof (functional_eval_sel _ _ _ _ Hv S3') as <-.
  apply E in V1, V2, HRv. apply EM in M34.
  apply (mk_rel_exp v1 v2 m3 m4); try (eapply eval_mem_of_sel; eassumption); try assumption.
  cbn; split; [ etransitivity; [ exact V1 | symmetry; exact V2 ] |]; split; [ etransitivity; [ exact V2 | symmetry; exact HRv ] | exact M34 ].
Qed.

Lemma rel_sel_of_smod : forall Γ H K y V,
    Γ ⊨ᵐ H ≈ K -> smod Γ K y V -> Γ ⊨ᵐ V ≈ V -> Γ ⊨ᵐ me_mem H y ≈ V.
Proof.
  intros * [R [HR HH]] HS [RV [HRV HV]].
  exists R, HR; intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  pose proof (rel_sub_under_ctx_at' Hσ HΓ' HR _ _ _ _ Hρ Hev Hev') as Hρσ.
  assert (HP : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρσ' : R ρ'σ' ρ'σ') by (etransitivity; [ symmetry; exact Hρσ | exact Hρσ ]).
  assert (EV : R <~> RV) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (rel_mod_hub _ _ _ _ _ _ _ _ (HH _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev'))
    as (h1 & h2 & h3 & h4 & E1 & E2 & E3 & E4 & D1 & D2 & D3 & D4).
  destruct (rel_mod_hub _ _ _ _ _ _ _ _ (HV _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev'))
    as (g1 & g2 & g3 & g4 & F1 & F2 & F3 & F4 & G1 & G2 & G3 & G4).
  destruct (HS _ HR _ Hρσ') as (k & v & Hk & Hv & Hsel).
  pose proof (functional_eval_modexp _ _ _ _ Hk E3) as ->.
  pose proof (functional_eval_modexp _ _ _ _ Hv F3) as ->.
  destruct (Hsel _ D1) as (r1 & S1 & R1).
  destruct (Hsel _ D2) as (r2 & S2 & R2).
  apply (mk_rel_mod r1 r2 g3 g4); [ cbn; econstructor; eassumption | econstructor; eassumption | exact F3 | exact F4 |].
  split; [ exact (per_dmod_trans _ _ _ R1 (per_dmod_sym _ _ R2)) |].
  split; [ exact R2 | exact (per_dmod_sym _ _ G4) ].
Qed.

(** ** Members of Values Lacking a Parameter *)

Lemma per_univ_elem_pi_inv : forall {j E a ρ B a' ρ' B'},
    per_univ_elem j E (Πᵈ a ρ B) (Πᵈ a' ρ' B') ->
    exists in_rel (out_rel : forall c c', in_rel c c' -> relation domain),
      per_univ_elem j in_rel a a' /\
      (forall c c' (H : in_rel c c'), rel_mod_eval (per_univ_elem j) B (ρ ↦ c) B' (ρ' ↦ c') (out_rel c c' H)) /\
      (E <~> fun f f' => forall c c' (H : in_rel c c'), rel_mod_app f c f' c' (out_rel c c' H)).
Proof.
  intros * H.
  basic_invert_per_univ_elem H.
  do 2 eexists; split; [ eassumption | split ]; [| eassumption ].
  intros c c' Hc; destruct_rel_mod_eval; econstructor; eassumption.
Qed.

(** The member of a value lacking a parameter, at a [Π] over a type of
    that parameter: when it is related at the codomain once applied, it is
    related at the [Π]. *)
Lemma mty_fun : forall k a0 x i E a ρB B,
    nextparam k a0 -> per_dmod k k ->
    per_univ_elem i E (Πᵈ a ρB B) (Πᵈ a ρB B) ->
    (exists j R0, per_univ_elem j R0 a0 a) ->
    (forall j Ra c, per_univ_elem j Ra a a -> Ra c c -> forall kc b, $ᵐ| k & c | gc_deps ⍮ gc_stack ↘ kc ->
       ⟦ B ⟧ ρB ↦ c ↘ b -> exists l Rb, per_univ_elem l Rb b b /\ mty kc x Rb) ->
    (exists f, k ·ₜ x gc_deps ⍮ gc_stack ↘ f) ->
    mty k x E.
Proof.
  intros * Hpk Hkk HE (j0 & R0 & H0) Hcod (fk & Hfk) h Hh.
  destruct (per_dmod_appm _ _ _ (per_dmod_sym _ _ Hh) Hpk) as (ih & R & ah & Hph & HRh & Happ0).
  destruct (per_univ_elem_pi_inv HE) as (in_rel & out_rel & Hin & Hout & HEq).
  assert (HPin : PER in_rel) by (eapply per_elem_PER; exact Hin).
  assert (E1 : R <~> R0) by (eapply per_univ_elem_right_irrel; [ exact HRh | exact H0 ]).
  assert (E2 : R0 <~> in_rel) by (eapply per_univ_elem_right_irrel; [ apply per_univ_elem_sym; exact H0 | exact Hin ]).
  assert (Hrel : forall c c', in_rel c c' -> R c' c) by (intros c c' Hc; apply E1, E2; symmetry; exact Hc).
  assert (Happ : forall c c', in_rel c c' -> exists hc kc, $ᵐ| h & c | gc_deps ⍮ gc_stack ↘ hc /\
                   $ᵐ| k & c' | gc_deps ⍮ gc_stack ↘ kc /\ per_dmod hc kc).
  { intros c c' Hc; destruct (Happ0 _ _ (Hrel _ _ Hc)) as (kc & hc & Hkc & Hhc & Hr).
    exists hc, kc; repeat split; [ exact Hhc | exact Hkc | apply per_dmod_sym; exact Hr ]. }
  (* the member of the other value, at a reflected variable *)
  pose proof (var_per_elem 0 Hin) as Hc0.
  destruct (Happ _ _ Hc0) as (hc0 & kc0 & Hhc0 & Hkc0 & Hc00).
  destruct (Hout _ _ Hc0) as [b0 b0' Hb0 Hb0' Hbb0].
  destruct (Hcod _ _ _ Hin Hc0 _ _ Hkc0 Hb0') as (l0 & Rb0 & _ & Hm0).
  destruct (Hm0 _ Hc00) as (y0 & _ & Hy0 & _ & _).
  destruct (sel_of_appm _ _ Hph _ _ _ _ Hhc0 Hy0) as (fh & Hfh).
  exists fh, fk; split; [ exact Hfh | split; [ exact Hfk |] ].
  apply HEq; intros c c' Hc.
  assert (Hc' : in_rel c' c') by (etransitivity; [ symmetry; exact Hc | exact Hc ]).
  destruct (Happ _ _ Hc) as (hc & kc & Hhc & Hkc & Hcc).
  destruct (Hout _ _ Hc) as [b1 b2 Hb1 Hb2 Hbb].
  destruct (Hcod _ _ _ Hin Hc' _ _ Hkc Hb2) as (l & Rb & HRb & Hm).
  destruct (Hm _ Hcc) as (y1 & y2 & Hy1 & Hy2 & Hyy).
  assert (Eo : out_rel c c' Hc <~> Rb) by (eapply per_univ_elem_right_irrel; [ apply per_univ_elem_sym; exact Hbb | exact HRb ]).
  econstructor; [ apply (proj2 (sel_app_comm _ _ Hph _ _ Hhc _ _ Hfh y1)); exact Hy1
                | apply (proj2 (sel_app_comm _ _ Hpk _ _ Hkc _ _ Hfk y2)); exact Hy2 | apply Eo; exact Hyy ].
Qed.

(** Robust member typing is a property of the class in the module PER. *)
Lemma mty_resp : forall k k' x R, PER R -> per_dmod k' k -> mty k x R -> mty k' x R.
Proof.
  intros * HP Hk Hm h Hh.
  destruct (Hm _ (per_dmod_trans _ _ _ Hh Hk)) as (r & r1 & Hr & Hr1 & Hrr).
  destruct (Hm _ Hk) as (r' & r1' & Hr' & Hr1' & Hrr').
  pose proof (functional_eval_sel _ _ _ _ Hr1 Hr1') as <-.
  exists r, r'; repeat split; try assumption; etransitivity; [ exact Hrr | symmetry; exact Hrr' ].
Qed.

Lemma mty_iff : forall k x R R', mty k x R -> (R <~> R') -> mty k x R'.
Proof. intros * Hm E h Hh; destruct (Hm _ Hh) as (r & r' & Hr & Hr' & Hrr); exists r, r'; repeat split; try assumption; apply E, Hrr. Qed.

(** A function related, once applied, to the member of the applied values
    is related to the member at the [Π]. *)
Lemma red_fun : forall k a0 x i E a ρB B f fk,
    nextparam k a0 ->
    per_univ_elem i E (Πᵈ a ρB B) (Πᵈ a ρB B) ->
    (exists j R0, per_univ_elem j R0 a0 a) -> per_dmod k k -> k ·ₜ x gc_deps ⍮ gc_stack ↘ fk ->
    (forall j Ra c, per_univ_elem j Ra a a -> Ra c c -> forall kc b, $ᵐ| k & c | gc_deps ⍮ gc_stack ↘ kc ->
       ⟦ B ⟧ ρB ↦ c ↘ b -> exists l Rb fc r, per_univ_elem l Rb b b /\ mty kc x Rb /\
         $| f & c |↘ fc /\ kc ·ₜ x gc_deps ⍮ gc_stack ↘ r /\ Rb fc r) ->
    E f fk.
Proof.
  intros * Hpk HE (j0 & R0 & H0) Hkk Hfk Hcod.
  destruct (per_dmod_appm _ _ _ Hkk Hpk) as (ih & Rh & ah & Hph & HRh & Happ).
  pose proof (nextparam_functional _ _ Hph _ Hpk) as ->.
  destruct (per_univ_elem_pi_inv HE) as (in_rel & out_rel & Hin & Hout & HEq).
  assert (HPin : PER in_rel) by (eapply per_elem_PER; exact Hin).
  assert (E1 : Rh <~> R0) by (eapply per_univ_elem_right_irrel; [ exact HRh | exact H0 ]).
  assert (E2 : R0 <~> in_rel) by (eapply per_univ_elem_right_irrel; [ apply per_univ_elem_sym; exact H0 | exact Hin ]).
  apply HEq; intros c c' Hc.
  assert (Hcc : in_rel c c) by (etransitivity; [ exact Hc | symmetry; exact Hc ]).
  destruct (Happ c c' (proj2 (E1 _ _) (proj2 (E2 _ _) Hc))) as (kc & kc' & Hkc & Hkc' & Hkk').
  destruct (Hout _ _ Hc) as [b1 b2 Hb1 Hb2 Hbb].
  destruct (Hcod _ _ _ Hin Hcc _ _ Hkc Hb1) as (l & Rb & fc & r & HRb & Hm & Hfc & Hr & Hfr).
  destruct (Hm _ (per_dmod_sym _ _ Hkk')) as (r' & r2 & Hr' & Hr2 & Hrr).
  pose proof (functional_eval_sel _ _ _ _ Hr2 Hr) as ->.
  assert (HPb : PER Rb) by (eapply per_elem_PER; exact HRb).
  assert (Eo : out_rel c c' Hc <~> Rb) by (eapply per_univ_elem_right_irrel; [ exact Hbb | exact HRb ]).
  econstructor; [ exact Hfc | apply (proj2 (sel_app_comm _ _ Hpk _ _ Hkc' _ _ Hfk r')); exact Hr' |].
  apply Eo; etransitivity; [ exact Hfr | symmetry; exact Hrr ].
Qed.

End Fixed_GCtx.
