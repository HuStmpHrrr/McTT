(** * The Rules for Module Expressions and Members

    A member read through the spine of a module expression is the member
    selected from the expression's value ([eval_mem_of_sel]): arguments
    commute with selection.  With this, the module PER relates the values of
    equivalent module expressions, and the members of related values are
    related at their canonical types. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import MemberLemmas.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases FunctionCases UniverseCases SubstitutionCases SubtypingCases
  VariableCases LetCases TrueFalseCases UnitCases InstanceCases MemberCases MemberTyping MemberReps MemberSem.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Arguments Commute with Selection *)

Lemma selc_local_le : forall ρ U args ch r,
    eval_selc gc_deps gc_stack (dm_local ρ U args) ch r -> List.length args <= List.length (gu_params U).
Proof.
  intros * H; inversion H; subst;
    match goal with Hs : eval_sel _ _ _ _ _ |- _ => inversion Hs | Hs : eval_selm _ _ _ _ _ |- _ => inversion Hs end;
    subst; cbn; lia.
Qed.

Lemma sel_app_local : forall ρ U args n ch r,
    List.length args < List.length (gu_params U) -> ch <> nil ->
    eval_selc gc_deps gc_stack (dm_local ρ U (args ++ n :: nil)) ch r ->
    exists f, eval_selc gc_deps gc_stack (dm_local ρ U args) ch f /\ eval_app gc_deps gc_stack f n r.
Proof.
  intros * Hl Hch Hs.
  exists (d_member (dm_local ρ U args) ch); split; [ apply selc_unsat_ex; assumption |].
  econstructor; [| exact Hs ].
  destruct U as [Δ [Φ | E]]; cbn in Hl; [ apply eval_appm_body | apply eval_appm_alias_unsat ]; exact Hl.
Qed.

Lemma sel_app_global : forall ch p args n r, ch <> nil ->
    eval_selc gc_deps gc_stack (dm_global p (args ++ n :: nil)) ch r ->
    exists f, eval_selc gc_deps gc_stack (dm_global p args) ch f /\ eval_app gc_deps gc_stack f n r.
Proof.
  induction ch as [| y ch IH]; intros * Hch Hs; [ congruence |].
  inversion Hs; subst.
  - match goal with Hs1 : eval_sel _ _ _ _ _ |- _ => inversion Hs1; subst end.
    match goal with Ha : eval_apps _ _ _ (args ++ _) r |- _ =>
      apply (eval_apps_app gc_deps gc_stack) in Ha as (g & Hg & Ha2) end.
    inversion Ha2; subst.
    match goal with Hn : eval_apps _ _ _ nil r |- _ => inversion Hn; subst end.
    eexists; split; [ constructor; econstructor; eassumption | eassumption ].
  - match goal with Hc : eval_selc _ _ _ ch r |- _ => assert (Hch' : ch <> nil) by (intros ->; inversion Hc) end.
    match goal with Hs1 : eval_selm _ _ _ _ _ |- _ => inversion Hs1; subst end.
    + destruct (IH _ _ _ _ Hch' ltac:(eassumption)) as (f & Hf & Ha).
      exists f; split; [ econstructor; [ apply eval_selm_global; assumption | exact Hf ] | exact Ha ].
    + match goal with H1 : eval_selmc _ _ (dm_local nil ?U _) ?ch1 ?h1, H2 : eval_selc _ _ ?h1 ch r |- _ =>
        assert (Hc : eval_selc gc_deps gc_stack (dm_local nil U (args ++ n :: nil)) (ch1 ++ ch) r)
          by (apply (eval_selc_app gc_deps gc_stack); [ exact Hch' | eexists; split; eassumption ]);
        pose proof (selc_local_le _ _ _ _ _ Hc) as Hle; rewrite length_app in Hle; cbn in Hle;
        assert (Hlt : List.length args < List.length (gu_params U)) by lia;
        assert (Hne : ch1 ++ ch <> nil) by (destruct ch; [ congruence | intros Hx; apply app_eq_nil in Hx as [_ Hx]; discriminate ]);
        destruct (sel_app_local _ _ _ _ _ _ Hlt Hne Hc) as (f & Hf & Ha);
        apply (eval_selc_app gc_deps gc_stack) in Hf as (h1' & Hh1' & Hf); [| exact Hch' ];
        exists f; split; [ econstructor; [ eapply eval_selm_global_alias; eassumption | exact Hf ] | exact Ha ] end.
Qed.

(** Selecting from an applied module value is applying the selected member. *)
Lemma sel_appm : forall h0 n h, eval_appm gc_deps gc_stack h0 n h ->
    forall ch r, ch <> nil -> eval_selc gc_deps gc_stack h ch r ->
    exists f, eval_selc gc_deps gc_stack h0 ch f /\ eval_app gc_deps gc_stack f n r.
Proof.
  induction 1 as [p args n | ρ Δ Φ args n Hl | ρ Δ E args n Hl | ρ Δ E args n h1 r1 Hl HE Hap IH
                 | hm n hm' ch0 r1 Hap Hs ]; intros ch r Hch Hc.
  - exact (sel_app_global _ _ _ _ _ Hch Hc).
  - eapply sel_app_local; [ cbn; exact Hl | exact Hch | exact Hc ].
  - eapply sel_app_local; [ cbn; exact Hl | exact Hch | exact Hc ].
  - destruct (IH _ _ Hch Hc) as (f & Hf & Ha).
    exists f; split; [ apply (selc_alias _ _ _ _ _ _ _ Hl HE); exact Hf | exact Ha ].
  - exists (d_member hm (ch0 ++ ch)); split; [ apply selc_member_ex; exact Hch |].
    econstructor; [ exact Hap |].
    apply (eval_selc_app gc_deps gc_stack); [ exact Hch | eexists; split; eassumption ].
Qed.

Lemma eval_spine_of_selc : forall H ρ h, eval_modexp gc_deps gc_stack H ρ h ->
    forall R args pre, modexp_spine H = (R, args, pre) ->
    forall ch r, ch <> nil -> eval_selc gc_deps gc_stack h ch r ->
    exists hr f ns, eval_modexp gc_deps gc_stack R ρ hr /\ eval_selc gc_deps gc_stack hr (pre ++ ch) f /\
      eval_exps gc_deps gc_stack args ρ ns /\ eval_apps gc_deps gc_stack f ns r.
Proof.
  induction H as [p | x | H IH y | H IH N | U]; intros ρ h He R args pre Hs ch r Hch Hc;
    cbn in Hs.
  1,2,5: injection Hs as <- <- <-; exists h, r, nil; repeat split; [ exact He | exact Hc | constructor | constructor ].
  - destruct (modexp_spine H) as [[R0 a0] p0] eqn:E; injection Hs as <- <- <-.
    inversion He; subst.
    match goal with H1 : eval_modexp _ _ H ρ ?h0, H2 : eval_selm _ _ ?h0 y h |- _ =>
      destruct (IH _ _ H1 _ _ _ eq_refl (y :: ch) r ltac:(discriminate) ltac:(econstructor; eassumption))
        as (hr & f & ns & Hr & Hf & Hns & Ha) end.
    exists hr, f, ns; repeat split; [ exact Hr | rewrite <- app_assoc; exact Hf | exact Hns | exact Ha ].
  - destruct (modexp_spine H) as [[R0 a0] p0] eqn:E; injection Hs as <- <- <-.
    inversion He; subst.
    match goal with H1 : eval_modexp _ _ H ρ ?h0, H2 : eval_exp _ _ N ρ ?n, H3 : eval_appm _ _ ?h0 ?n h |- _ =>
      destruct (sel_appm _ _ _ H3 _ _ Hch Hc) as (f0 & Hf0 & Ha0);
      destruct (IH _ _ H1 _ _ _ eq_refl _ _ Hch Hf0) as (hr & f & ns & Hr & Hf & Hns & Ha);
      exists hr, f, (ns ++ n :: nil); repeat split; [ exact Hr | exact Hf | |];
        [ apply eval_exps_app; [ exact Hns | econstructor; [ exact H2 | constructor ] ]
        | apply (eval_apps_app gc_deps gc_stack); exists f0; split; [ exact Ha | econstructor; [ exact Ha0 | constructor ] ] ] end.
Qed.

Lemma eval_mem_of_sel : forall H ρ h x r,
    eval_modexp gc_deps gc_stack H ρ h -> eval_sel gc_deps gc_stack h x r -> ⟦ a_mem H x ⟧ ρ ↘ r.
Proof.
  intros * He Hs.
  destruct (modexp_spine H) as [[R args] pre] eqn:E.
  destruct (eval_spine_of_selc _ _ _ He _ _ _ E (x :: nil) r ltac:(discriminate) ltac:(constructor; exact Hs))
    as (hr & f & ns & Hr & Hf & Hns & Ha).
  apply (eval_mem_spine gc_deps gc_stack _ _ _ _ _ _ _ E); do 3 eexists; eauto.
Qed.

(** ** Module Expressions *)

Lemma functional_eval_sel : forall h x r1 r2,
    eval_sel gc_deps gc_stack h x r1 -> eval_sel gc_deps gc_stack h x r2 -> r1 = r2.
Proof. intros; pose proof (@functional_eval gc_deps gc_stack) as Hf; destruct_all; eauto. Qed.

Lemma functional_eval_selm : forall h y r1 r2,
    eval_selm gc_deps gc_stack h y r1 -> eval_selm gc_deps gc_stack h y r2 -> r1 = r2.
Proof. intros; pose proof (@functional_eval gc_deps gc_stack) as Hf; destruct_all; eauto. Qed.


Lemma hub_chain : forall v v1 v3 v4,
    per_dmod v v1 -> per_dmod v v3 -> per_dmod v v4 -> rel_chain per_dmod ([v1; v; v3; v4]).
Proof.
  intros * H1 H3 H4; split; [ exact (per_dmod_sym _ _ H1) |].
  split; [ exact H3 | exact (per_dmod_trans _ _ _ (per_dmod_sym _ _ H3) H4) ].
Qed.

(** The four values of a valid module expression are related to the one at
    the substituted environment. *)
Lemma rel_mod_hub : forall H σ ρ ρσ H' σ' ρ' ρ'σ',
    rel_mod H σ ρ ρσ H' σ' ρ' ρ'σ' ->
    exists h1 h2 h3 h4,
      eval_modexp gc_deps gc_stack H[σ]ᵐ ρ h1 /\ eval_modexp gc_deps gc_stack H ρσ h2 /\
      eval_modexp gc_deps gc_stack H' ρ'σ' h3 /\ eval_modexp gc_deps gc_stack H'[σ']ᵐ ρ' h4 /\
      per_dmod h2 h1 /\ per_dmod h2 h2 /\ per_dmod h2 h3 /\ per_dmod h2 h4.
Proof.
  intros * [h1 h2 h3 h4 E1 E2 E3 E4 (C12 & C23 & C34)].
  exists h1, h2, h3, h4; repeat split; try assumption.
  - exact (per_dmod_sym _ _ C12).
  - exact (per_dmod_trans _ _ _ C23 (per_dmod_sym _ _ C23)).
  - exact (per_dmod_trans _ _ _ C23 C34).
Qed.

Lemma per_ctx_env_tail_of : forall e Γ R, EF e :: Γ ≈ e :: Γ ∈ per_ctx_env ↘ R ->
    exists R', EF Γ ≈ Γ ∈ per_ctx_env ↘ R' /\ forall ρ ρ', R ρ ρ' -> R' ρ↯ ρ'↯.
Proof.
  intros * HR.
  destruct (per_ctx_env_app_tail (e :: nil) (e :: nil) Γ Γ R eq_refl HR) as [R' HR'].
  exists R'; split; [ exact HR' |].
  intros ρ ρ' Hρ; pose proof (rel_wk_app _ _ _ (rel_wk_shift HR' HR) _ _ Hρ) as H; rewrite !eval_wk_shift in H; exact H.
Qed.

Lemma slot_rel : forall Γ x U, Γ ∋ #x ⇒ₘ U ->
    forall R, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> forall ρ ρ', R ρ ρ' -> per_dmod (env_mod ρ x) (env_mod ρ' x).
Proof.
  induction 1 as [U0 Γ0 | n U1 Γ0 e Hl IH]; intros R HR ρ ρ' Hρ.
  - destruct (per_ctx_env_tail_of _ _ _ HR) as (R0 & HR0 & _).
    destruct (per_ctx_env_cons_mod_inversion HR0 HR) as [HU ER].
    destruct (proj1 (ER ρ ρ') Hρ) as (Ht & H1 & _ & H3 & _).
    exact (per_dmod_trans _ _ _ H1 (per_dmod_trans _ _ _ (HU _ _ Ht) (per_dmod_sym _ _ H3))).
  - destruct (per_ctx_env_tail_of _ _ _ HR) as (R0 & HR0 & Ht).
    rewrite !env_mod_S; exact (IH _ HR0 _ _ (Ht _ _ Hρ)).
Qed.

Lemma rel_me_var : forall Γ x U, ⊨ Γ -> Γ ∋ #x ⇒ₘ U -> Γ ⊨ᵐ me_var x ≈ me_var x.
Proof.
  intros * HΓ Hl.
  destruct (sem_ctx_per_ctx_env HΓ) as [R HR].
  exists R, HR; intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  pose proof (rel_sub_under_ctx_at' Hσ HΓ' HR _ _ _ _ Hρ Hev Hev') as Hρσ.
  pose proof (slot_rel _ _ _ Hl _ HR _ _ Hρσ) as Hd.
  apply (mk_rel_mod (env_mod ρσ x) (env_mod ρσ x) (env_mod ρ'σ' x) (env_mod ρ'σ' x));
    [ apply eval_sub_mvar; assumption | constructor | constructor | apply eval_sub_mvar; assumption |].
  split; [ exact (per_dmod_trans _ _ _ Hd (per_dmod_sym _ _ Hd)) |].
  split; [ exact Hd | exact (per_dmod_trans _ _ _ (per_dmod_sym _ _ Hd) Hd) ].
Qed.

Lemma rel_me_mem : gmod_ok -> forall Γ H H' y A,
    Γ ⊨ᵐ H ≈ H' -> sem_mt Γ H -> member_type gc_deps gc_stack Γ H (y :: nil) mk_mod A ->
    Γ ⊨ᵐ me_mem H y ≈ me_mem H' y.
Proof.
  intros Hok * [R [HR HH]] [S1 _] Hm.
  pose proof Hok as (HGc & HGap & Hc).
  destruct (S1 _ _ _ Hm ltac:(discriminate)) as [(n & b & Hr) Hv].
  destruct (rep_valid _ _ _ _ Hr) as [i HA].
  exists R, HR; intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  pose proof (rel_sub_under_ctx_at' Hσ HΓ' HR _ _ _ _ Hρ Hev Hev') as Hρσ.
  assert (HP : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρσ' : R ρσ ρσ) by (etransitivity; [ exact Hρσ | symmetry; exact Hρσ ]).
  destruct (rel_mod_hub _ _ _ _ _ _ _ _ (HH _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev'))
    as (h1 & h2 & h3 & h4 & E1 & E2 & E3 & E4 & D1 & D2 & D3 & D4).
  destruct (Hv _ _ HR Hρσ' _ E2) as (a & Ha & Hma).
  destruct (rel_exp_of_typ_inversion_simple_at HR HA _ _ Hρσ') as (a1 & a2 & Ha1 & Ha2 & [Ra HRa]).
  functional_eval_rewrite_clear.
  assert (HRa' : per_univ_elem i Ra a a) by (etransitivity; [ exact HRa | symmetry; exact HRa ]).
  assert (Sel : forall hk, per_dmod h2 hk -> exists v vk, eval_selm gc_deps gc_stack h2 y v /\
                  eval_selm gc_deps gc_stack hk y vk /\ per_dmod v vk).
  { intros hk Hk.
    destruct (mtyped_rel HGc _ _ _ _ Hma _ _ _ Hk HRa') as (v & vk & Hs & Hsk & Hvv).
    inversion Hs; subst; inversion Hsk; subst.
    repeat match goal with Hn : eval_selmc _ _ _ nil _ |- _ => inversion Hn; subst; clear Hn end.
    eauto. }
  destruct (Sel _ D1) as (v & v1 & S2 & S1' & V1).
  destruct (Sel _ D3) as (v' & v3 & S2' & S3 & V3).
  destruct (Sel _ D4) as (v'' & v4 & S2'' & S4 & V4).
  pose proof (functional_eval_selm _ _ _ _ S2 S2') as <-.
  pose proof (functional_eval_selm _ _ _ _ S2 S2'') as <-.
  apply (mk_rel_mod v1 v v3 v4); [ econstructor; eassumption .. | exact (hub_chain _ _ _ _ V1 V3 V4) ].
Qed.

Lemma rel_me_app : gmod_ok -> forall Γ H H' N N' A0 B C i,
    Γ ⊨ᵐ H ≈ H' -> sem_mt Γ H -> member_type gc_deps gc_stack Γ H nil mk_mod A0 ->
    Γ ⊨ A0 ≈ Π B C : Type@i -> Γ ⊨ N ≈ N' : B ->
    Γ ⊨ᵐ me_app H N ≈ me_app H' N'.
Proof.
  intros Hok * [R [HR HH]] [S1 _] Hm0 HA0 HN.
  pose proof Hok as (HGc & HGap & Hc).
  exists R, HR; intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  pose proof (rel_sub_under_ctx_at' Hσ HΓ' HR _ _ _ _ Hρ Hev Hev') as Hρσ.
  assert (HP : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρσ' : R ρσ ρσ) by (etransitivity; [ exact Hρσ | symmetry; exact Hρσ ]).
  destruct (rel_mod_hub _ _ _ _ _ _ _ _ (HH _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev'))
    as (h1 & h2 & h3 & h4 & E1 & E2 & E3 & E4 & D1 & D2 & D3 & D4).
  destruct HN as [RN [HRN [j HNgen]]].
  destruct (HNgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [Rel [[b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 (T12 & T23 & T34)] [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 (N12 & N23 & N34)]]].
  assert (HPR : PER Rel) by (eapply per_elem_PER; exact T23).
  destruct (proj2 (S1 _ _ _ Hm0 ltac:(discriminate)) _ _ HR Hρσ' _ E2) as (a0 & Ha0 & Hma).
  destruct (rel_exp_of_typ_inversion_simple_at HR HA0 _ _ Hρσ') as (x0 & p0 & Hx0 & Hp0 & [Rp HRp]).
  functional_eval_rewrite_clear.
  inversion Hp0; subst.
  match goal with Hb : ⟦ B ⟧ ρσ ↘ ?bb |- _ => pose proof (functional_eval_exp _ _ _ _ Hb Hb2) as -> end.
  destruct (mtyped_arity_pi HGc HGap _ _ Hma _ _ _ _ _ HRp) as (d & j0 & Rd & Hnd & _).
  pose proof (mtyped_resp _ _ _ _ Hma _ _ _ HRp) as Hm'.
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ HRp)) HRp) as (Rπ & Hπ & _).
  destruct (per_univ_elem_pi_inv Hπ) as (in_rel & out & Hin & Hout & _).
  assert (HB : forall c, in_rel c c -> exists b, ⟦ C ⟧ ρσ ↦ c ↘ b)
    by (intros c Hcc; destruct (Hout _ _ Hcc) as [b ? Hb ?]; eauto).
  pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ T23 Hin) as ER.
  assert (Ap : forall hk nk, per_dmod h2 hk -> Rel n2 nk ->
             exists w wk, eval_appm gc_deps gc_stack h2 n2 w /\ eval_appm gc_deps gc_stack hk nk wk /\ per_dmod w wk)
    by (intros hk nk Hk Hnk; exact (appm_rel_typed HGc HGap _ _ Hnd _ _ _ _ _ Hm' _ _ Hin HB _ Hk _ _ (proj1 (ER _ _) Hnk))).
  destruct (Ap _ _ D1 ltac:(symmetry; exact N12)) as (w & w1 & A2 & A1 & W1).
  destruct (Ap _ _ D3 N23) as (w' & w3 & A2' & A3 & W3).
  destruct (Ap _ _ D4 ltac:(etransitivity; [ exact N23 | exact N34 ])) as (w'' & w4 & A2'' & A4 & W4).
  pose proof (functional_eval_appm _ _ _ _ A2 A2') as <-.
  pose proof (functional_eval_appm _ _ _ _ A2 A2'') as <-.
  apply (mk_rel_mod w1 w w3 w4); [ econstructor; eassumption .. | exact (hub_chain _ _ _ _ W1 W3 W4) ].
Qed.

(** ** Members *)

Lemma selc_one_inv : forall h x v, eval_selc gc_deps gc_stack h (x :: nil) v -> eval_sel gc_deps gc_stack h x v.
Proof. intros * H; inversion H; subst; [ assumption | match goal with Hn : eval_selc _ _ _ nil _ |- _ => inversion Hn end ]. Qed.

(** Members of equivalent module expressions are equal at the canonical type
    of the left one. *)
Lemma rel_exp_mem_gen : gmod_ok -> forall Γ H H' x A i,
    Γ ⊨ᵐ H ≈ H' -> sem_mt Γ H -> member_type gc_deps gc_stack Γ H (x :: nil) mk_term A ->
    Γ ⊨ A : Type@i -> Γ ⊨ a_mem H x ≈ a_mem H' x : A.
Proof.
  intros Hok * [R [HR HH]] [S1 _] Hm HA.
  pose proof Hok as (HGc & HGap & Hc).
  pose proof (rel_exp_of_typ_inversion HA) as [RA [HRA HAgen]].
  exists R, HR, i; intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  pose proof (rel_sub_under_ctx_at' Hσ HΓ' HR _ _ _ _ Hρ Hev Hev') as Hρσ.
  assert (HP : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρσ' : R ρσ ρσ) by (etransitivity; [ exact Hρσ | symmetry; exact Hρσ ]).
  destruct (rel_exp_implies_rel_typ (HAgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')) as [Rel HT].
  exists Rel; split; [ exact HT |].
  destruct HT as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 (T12 & T23 & T34)].
  assert (HPR : PER Rel) by (eapply per_elem_PER; exact T23).
  destruct (rel_mod_hub _ _ _ _ _ _ _ _ (HH _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev'))
    as (h1 & h2 & h3 & h4 & E1 & E2 & E3 & E4 & D1 & D2 & D3 & D4).
  destruct (proj2 (S1 _ _ _ Hm ltac:(discriminate)) _ _ HR Hρσ' _ E2) as (a & Ha & Hma).
  pose proof (functional_eval_exp _ _ _ _ Ha Ha2) as ->.
  assert (Haa : per_univ_elem i Rel a2 a2) by (etransitivity; [ exact T23 | symmetry; exact T23 ]).
  assert (Sel : forall hk, per_dmod h2 hk -> exists v vk, eval_sel gc_deps gc_stack h2 x v /\
                  eval_sel gc_deps gc_stack hk x vk /\ Rel v vk).
  { intros hk Hk.
    destruct (mtyped_rel HGc _ _ _ _ Hma _ _ _ Hk Haa) as (v & vk & Hs & Hsk & Hvv).
    exists v, vk; split; [ exact (selc_one_inv _ _ _ Hs) | split; [ exact (selc_one_inv _ _ _ Hsk) | exact Hvv ] ]. }
  destruct (Sel _ D1) as (v & v1 & S2 & S1' & V1).
  destruct (Sel _ D3) as (v' & v3 & S2' & S3 & V3).
  destruct (Sel _ D4) as (v'' & v4 & S2'' & S4 & V4).
  pose proof (functional_eval_sel _ _ _ _ S2 S2') as <-.
  pose proof (functional_eval_sel _ _ _ _ S2 S2'') as <-.
  apply (mk_rel_exp v1 v v3 v4); [ eapply eval_mem_of_sel; eassumption .. |].
  cbn; split; [ symmetry; exact V1 |]; split; [ exact V3 | etransitivity; [ symmetry; exact V3 | exact V4 ] ].
Qed.

(** ** δ: Members Are Their Expansions *)

(** An element of a [Π]-type and any [f] agreeing with it on the diagonal
    are related. *)
Lemma pi_rel_of_diag : forall i E a ρB B f g,
    per_univ_elem i E (Πᵈ a ρB B) (Πᵈ a ρB B) -> E g g ->
    (forall j Ra c, per_univ_elem j Ra a a -> Ra c c ->
       exists b r r' k Rb, ⟦ B ⟧ ρB ↦ c ↘ b /\ eval_app gc_deps gc_stack f c r /\
         eval_app gc_deps gc_stack g c r' /\ per_univ_elem k Rb b b /\ Rb r r') ->
    E f g.
Proof.
  intros * HE Hg Hd.
  destruct (per_univ_elem_pi_inv HE) as (in' & out' & Hin' & Hout' & HEq).
  assert (HPin : PER in') by (eapply per_elem_PER; exact Hin').
  apply HEq; intros c c' Hcc.
  assert (Hc : in' c c) by (etransitivity; [ exact Hcc | symmetry; exact Hcc ]).
  destruct (Hd _ _ _ Hin' Hc) as (b & r & r' & k & Rb & Hb & Hr & Hr' & HRb & Hrr).
  destruct (proj1 (HEq g g) Hg _ _ Hcc) as [r2 r3 Hr2 Hr3 Hr23].
  destruct (Hout' _ _ Hcc) as [b1 b2 Hb1 Hb2 Hbb].
  functional_eval_rewrite_clear.
  pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRb Hbb) as F.
  assert (HPo : PER (out' c c' Hcc)) by (eapply per_elem_PER; exact Hbb).
  econstructor; [ exact Hr | exact Hr3 |].
  etransitivity; [ apply F; exact Hrr | exact Hr23 ].
Qed.

(** A member of a closure still lacking arguments is related to its
    expansion: both sides take the next argument the same way, and at
    saturation the expansion evaluates to the member. *)
Lemma bridge_walk : forall ρ U ch Y Body,
    tele_ass (gu_params U) -> ch <> nil ->
    (forall args, List.length args = List.length (gu_params U) ->
       forall r, eval_selc gc_deps gc_stack (dm_local ρ U args) ch r -> ⟦ Body ⟧ env_args ρ args ↘ r) ->
    forall Δin Δout args, gu_params U = Δin ++ Δout -> List.length args = List.length Δout ->
      forall a i E d, ⟦ ctx_pi Δin Y ⟧ env_args ρ args ↘ a -> per_univ_elem i E a a ->
        eval_selc gc_deps gc_stack (dm_local ρ U args) ch d -> E d d ->
        exists m, ⟦ ctx_fn Δin Body ⟧ env_args ρ args ↘ m /\ E m d.
Proof.
  intros * HU Hch HS Δin.
  induction Δin as [| e Δin IH] using rev_ind;
    intros Δout args EU Hl a i E d Ha HE Hd Hdd; cbn [app ctx_pi ctx_fn] in *.
  - exists d; split; [ exact (HS _ ltac:(rewrite EU; exact Hl) _ Hd) | exact Hdd ].
  - pose proof EU as EU'.
    rewrite EU in HU; destruct (tele_ass_app_inv _ _ HU) as [HU1 HU2].
    destruct (tele_ass_app_inv _ _ HU1) as [_ He]; inversion He as [| ? ? [A1 ->] _]; subst.
    rewrite ctx_pi_app in Ha; rewrite ctx_fn_app; cbn [ctx_pi ctx_fn] in Ha |- *.
    inversion Ha; subst.
    assert (Hlt : List.length args < List.length (gu_params U))
      by (rewrite EU', !length_app; cbn; lia).
    pose proof (selc_unsat _ _ _ _ _ Hlt Hd) as ->.
    eexists; split; [ constructor |].
    apply (pi_rel_of_diag _ _ _ _ _ _ _ HE Hdd).
    intros j Ra c HRa Hc.
    destruct (per_univ_elem_pi_inv HE) as (in' & out' & Hin' & Hout' & HEq).
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRa Hin') as ER.
    assert (Hc' : in' c c) by (apply ER; exact Hc).
    destruct (Hout' _ _ Hc') as [b b' Hb Hb' Hbb].
    functional_eval_rewrite_clear.
    destruct (proj1 (HEq _ _) Hdd _ _ Hc') as [r' r3 Hr' Hr3 Hrr'].
    pose proof (functional_eval_app _ _ _ _ Hr' Hr3) as <-.
    inversion Hr'; subst.
    match goal with Hap : eval_appm _ _ (dm_local ρ U args) c ?h1 |- _ =>
      assert (Hw : h1 = dm_local ρ U (args ++ c :: nil))
        by (destruct U as [Δ [Φ | E0]]; inversion Hap; subst; cbn in *; try lia; reflexivity); subst h1 end.
    destruct (IH (ce_ass A1 :: Δout) (args ++ c :: nil) ltac:(rewrite EU', <- app_assoc; reflexivity)
                ltac:(rewrite length_app; cbn; lia) b i (out' c c Hc') r'
                ltac:(rewrite env_args_snoc; exact Hb) Hbb ltac:(eassumption) Hrr') as (m & Hm & Hmr).
    rewrite env_args_snoc in Hm.
    exists b, m, r', i, (out' c c Hc'); split; [ exact Hb |]; split; [ constructor; exact Hm |].
    split; [ exact Hr' |]; split; [ exact Hbb | exact Hmr ].
Qed.

Lemma member_ref_of_selc : forall E ρ h ch r, ch <> nil ->
    eval_modexp gc_deps gc_stack E ρ h -> eval_selc gc_deps gc_stack h ch r -> ⟦ member_ref E ch ⟧ ρ ↘ r.
Proof.
  intros * Hch HE Hs.
  apply (eval_member_ref gc_deps gc_stack _ _ _ _ Hch).
  destruct (modexp_spine E) as [[R args] pre] eqn:Es.
  destruct (eval_spine_of_selc _ _ _ HE _ _ _ Es _ _ Hch Hs) as (hr & f & ns & ? & ? & ? & ?).
  do 3 eexists; eauto.
Qed.

Lemma sat_alias : forall ρ Δ E args ch r, List.length args = List.length Δ -> ch <> nil ->
    eval_selc gc_deps gc_stack (dm_local ρ (gu_mk Δ (md_alias E)) args) ch r -> ⟦ member_ref E ch ⟧ env_args ρ args ↘ r.
Proof.
  intros * Hl Hch Hs.
  assert (Hh : exists h, eval_modexp gc_deps gc_stack E (env_args ρ args) h).
  { inversion Hs; subst;
      match goal with Hs1 : eval_sel _ _ _ _ _ |- _ => inversion Hs1 | Hs1 : eval_selm _ _ _ _ _ |- _ => inversion Hs1 end;
      subst; cbn in *; try lia; eauto. }
  destruct Hh as [h HE].
  exact (member_ref_of_selc _ _ _ _ _ Hch HE (proj1 (selc_alias _ _ _ _ _ _ _ Hl HE) Hs)).
Qed.

Lemma unit_delta : forall Γ U ch k A M, unit_member_type gc_deps gc_stack Γ U ch k A -> k = mk_term ->
    member_expansion U ch = Some M -> tele_ass (gu_params U) ->
    forall ρ a i E d, ⟦ A ⟧ ρ ↘ a -> per_univ_elem i E a a ->
      eval_selc gc_deps gc_stack (dm_local ρ U nil) ch d -> E d d -> exists m, ⟦ M ⟧ ρ ↘ m /\ E m d.
Proof.
  intros * Hm Hk HM HU * Ha HE Hd Hdd.
  inversion Hm as [ | ? Δ Φ Φ' x b A0 B Hx | ? Δ Φ Φ' y Uy ch' k' A0 Hk' Hy Hm' | ? Δ E0 ch' k' A0 Hm' ];
    subst; try discriminate; unfold member_expansion in HM.
  - rewrite Hx in HM; injection HM as <-.
    rewrite ctx_pi_app in Ha; rewrite ctx_fn_app.
    refine (bridge_walk ρ _ _ _ _ HU (cons_neq_nil _ _) _ Δ nil nil (eq_sym (app_nil_r _)) eq_refl _ _ _ _ Ha HE Hd Hdd).
    intros args Hl r Hr.
    apply selc_one_inv in Hr; inversion Hr; subst; cbn [gu_params] in *; try lia.
    match goal with Hx' : gm_prefix_upto Φ x = Some _ |- _ =>
      rewrite Hx in Hx'; injection Hx'; intros; subst end.
    cbn [body_ctx ctx_fn].
    eapply eval_ctx_fn_body; [ eassumption |].
    eapply eval_exp_let; [ eassumption | apply eval_exp_var_eq; reflexivity ].
  - destruct ch' as [| z ch'']; [ exfalso; exact (Hk' eq_refl eq_refl) |].
    rewrite Hy in HM; injection HM as <-.
    rewrite ctx_pi_app in Ha; rewrite ctx_fn_app.
    refine (bridge_walk ρ _ _ _ _ HU (cons_neq_nil _ _) _ Δ nil nil (eq_sym (app_nil_r _)) eq_refl _ _ _ _ Ha HE Hd Hdd).
    intros args Hl r Hr.
    inversion Hr; subst.
    match goal with Hs : eval_selm _ _ _ y _ |- _ => inversion Hs; subst end; cbn [gu_params] in *; try lia.
    match goal with Hy' : gm_prefix_upto Φ y = Some _ |- _ =>
      rewrite Hy in Hy'; injection Hy'; intros; subst end.
    cbn [body_ctx ctx_fn].
    eapply eval_ctx_fn_body; [ eassumption |].
    constructor.
    refine (member_ref_of_selc (me_var 0) _ _ (z :: ch'') _ (cons_neq_nil _ _) _ _); [ constructor | eassumption ].
  - assert (Hch : ch <> nil) by (intros ->; inversion Hd).
    destruct ch as [| c0 ch0]; [ congruence |]; injection HM as <-.
    refine (bridge_walk ρ _ _ A0 _ HU Hch _ Δ nil nil (eq_sym (app_nil_r _)) eq_refl _ _ _ _ _ HE Hd Hdd).
    + intros args Hl r Hr; exact (sat_alias _ _ _ _ _ _ Hl Hch Hr).
    + exact Ha.
Qed.

(** ** Module Slots, Weakened Units and their Closures *)

Lemma slot_decomp : forall Γ x U, Γ ∋ #x ⇒ₘ U -> ⊨ Γ ->
    exists Γ0 U0 φ, Γ ⊨w φ : Γ0 /\ U = gunit_wk U0 φ /\ sem_unit Γ0 U0 /\
      forall R ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> R ρ ρ -> per_dmod (env_mod ρ x) (dm_local (⟪φ⟫ ρ) U0 nil).
Proof.
  induction 1 as [U0 Γ0 | n U1 Γ0 e Hl IH]; intros HC.
  - pose proof (sem_ctx_mod_inv HC) as (_ & HsU & _).
    exists Γ0, U0, wk_shift; split; [ exact (rel_wk_under_ctx_shift HC) |]; split; [ reflexivity |]; split; [ exact HsU |].
    intros R ρ HR Hρ.
    destruct (per_ctx_env_tail_of _ _ _ HR) as (R0 & HR0 & _).
    destruct (per_ctx_env_cons_mod_inversion HR0 HR) as [_ ER].
    destruct (proj1 (ER ρ ρ) Hρ) as (_ & Hd & _).
    rewrite eval_wk_shift; exact Hd.
  - destruct (IH (sem_ctx_tail HC)) as (G0 & U0 & φ & Hφ & -> & HsU & Ht).
    exists G0, U0, (φ ⊙ wk_shift); split; [| split; [ apply gunit_wk_wk | split; [ exact HsU |] ] ].
    + destruct (rel_wk_under_ctx_shift HC) as [R1 [HR1 [R2 [HR2 Hs]]]].
      destruct Hφ as [R3 [HR3 [R4 [HR4 Hw]]]].
      assert (E : R2 <~> R3) by (eapply per_ctx_env_right_irrel; eassumption).
      exists R1, HR1, R4, HR4.
      destruct Hs as [Hsm Hs]; destruct Hw as [Hwm Hw].
      split; [ apply wk_mono_compose; assumption |].
      intros ρ ρ' Hρ; rewrite !(@eval_wk_compose φ wk_shift _ Hwm Hsm).
      apply Hw, E, Hs, Hρ.
    + intros R ρ HR Hρ.
      destruct (per_ctx_env_tail_of _ _ _ HR) as (R0 & HR0 & Htl).
      destruct Hφ as [_ [_ [_ [_ [Hwm _]]]]].
      rewrite (@eval_wk_compose φ wk_shift _ Hwm wk_mono_shift), eval_wk_shift, env_mod_S.
      exact (Ht _ _ HR0 (Htl _ _ Hρ)).
Qed.

Lemma slot_closure_tie : forall Γ x U, Γ ∋ #x ⇒ₘ U -> ⊨ Γ ->
    forall R ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> R ρ ρ -> per_dmod (env_mod ρ x) (dm_local ρ U nil).
Proof.
  intros * Hl HC R ρ HR Hρ.
  destruct (slot_decomp _ _ _ Hl HC) as (Γ0 & U0 & φ & Hφ & -> & HsU & Ht).
  pose proof Hφ as [_ [_ [_ [_ [Hwm _]]]]].
  pose proof (unit_sub_link _ _ _ _ _ _ _ _ HsU (rel_sub_of_wk Hφ) HR Hρ (@eval_sub_of_wk _ _ φ ρ Hwm)) as Hd.
  rewrite gunit_sub_of_wk in Hd.
  exact (per_dmod_trans _ _ _ (Ht _ _ HR Hρ) (per_dmod_sym _ _ Hd)).
Qed.

Lemma slot_tele_ass : forall Γ x U, Γ ∋ #x ⇒ₘ U -> ⊨ Γ -> tele_ass (gu_params U).
Proof.
  intros * Hl HC.
  destruct (slot_decomp _ _ _ Hl HC) as (Γ0 & [Δ D] & φ & _ & -> & HsU & _).
  rewrite gunit_wk_mk; cbn [gu_params].
  assert (HΔ : tele_ass Δ) by (inversion HsU; assumption).
  clear -HΔ; induction HΔ as [| e Δ [A ->] HΔ IH]; cbn; constructor; eauto.
Qed.

(** ** Validity in δ-Reducts *)

(** The δ-reducts of a module expression's members are related to the
    members selected from its values. *)
Definition sem_unf (Γ : ctx) (H : modexp) : Prop :=
  forall ch A M, member_type gc_deps gc_stack Γ H ch mk_term A ->
    member_unfold_ch gc_deps gc_stack Γ H ch = Some M ->
    forall R ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> R ρ ρ ->
    forall h, eval_modexp gc_deps gc_stack H ρ h ->
    forall a i E d, ⟦ A ⟧ ρ ↘ a -> per_univ_elem i E a a ->
      eval_selc gc_deps gc_stack h ch d -> E d d -> exists m, ⟦ M ⟧ ρ ↘ m /\ E m d.

Lemma sem_unf_lit : forall Γ U, tele_ass (gu_params U) -> sem_unf Γ (me_lit U).
Proof.
  intros * HU ch A M Hm HM R ρ HR Hρ h Hh * Ha HE Hd Hdd.
  inversion Hm; subst; inversion Hh; subst; cbn in HM.
  eapply unit_delta; eauto.
Qed.

Lemma sem_unf_var : gmod_ok -> forall Γ x U, Γ ∋ #x ⇒ₘ U -> ⊨ Γ -> ctx_mt Γ -> sem_unf Γ (me_var x).
Proof.
  intros Hok * Hl HC Hok' ch A M Hm HM R ρ HR Hρ h Hh * Ha HE Hd Hdd.
  pose proof Hok as (HGc & HGap & Hc).
  inversion Hm; subst; inversion Hh; subst.
  match goal with Hl' : _ ∋ #x ⇒ₘ ?U' |- _ => pose proof (ctx_lookup_mod_functional _ _ _ _ Hl Hl') as <- end.
  cbn in HM; rewrite (ctx_find_mod_complete _ _ _ Hl) in HM.
  pose proof (slot_closure_tie _ _ _ Hl HC _ _ HR Hρ) as Ht.
  destruct (proj1 (sem_mt_var HGc Hc _ _ _ Hl HC Hok') _ _ _ Hm ltac:(destruct ch; [ inversion Hd | discriminate ]))
    as [_ Hv].
  destruct (Hv _ _ HR Hρ _ ltac:(constructor)) as (a' & Ha' & Hma).
  pose proof (functional_eval_exp _ _ _ _ Ha Ha') as <-.
  destruct (mtyped_rel HGc _ _ _ _ Hma _ _ _ Ht HE) as (v & v' & Hv1 & Hv2 & Hvv).
  pose proof (functional_eval_selc _ _ _ _ Hd Hv1) as <-.
  assert (HPE : PER E) by (eapply per_elem_PER; exact HE).
  assert (Hv'v' : E v' v') by (etransitivity; [ symmetry; exact Hvv | exact Hvv ]).
  match goal with Hu : unit_member_type _ _ _ _ _ _ _ |- _ =>
    destruct (unit_delta _ _ _ _ _ _ Hu eq_refl HM (slot_tele_ass _ _ _ Hl HC) _ _ _ _ _ Ha HE Hv2 Hv'v') as (m & Hm' & Hmv) end.
  exists m; split; [ exact Hm' | etransitivity; [ exact Hmv | symmetry; exact Hvv ] ].
Qed.

Lemma sem_unf_mem : forall Γ H y, sem_unf Γ H -> sem_unf Γ (me_mem H y).
Proof.
  intros * HS ch A M Hm HM R ρ HR Hρ h' Hh' * Ha HE Hd Hdd.
  inversion Hm as [| | | | | ? ? ? ? ? ? Hk Hm' | ]; subst; inversion Hh'; subst; cbn in HM.
  match goal with He : eval_modexp _ _ H ρ ?h, Hs : eval_selm _ _ ?h y h' |- _ =>
    exact (HS _ _ _ Hm' HM _ _ HR Hρ _ He _ _ _ _ Ha HE ltac:(econstructor; eassumption) Hdd) end.
Qed.

Lemma sem_unf_app : gmod_ok -> forall Γ H A0 B C N i,
    sem_mt Γ H -> sem_unf Γ H -> Γ ⊨ᵐ H ≈ H ->
    member_type gc_deps gc_stack Γ H nil mk_mod A0 -> Γ ⊨ A0 ≈ Π B C : Type@i -> Γ ⊨ B : Type@i ->
    Γ ⊨ N : B -> sem_unf Γ (me_app H N).
Proof.
  intros Hok * HS HU HH Hm0 HA0 HB HN ch A' M' Hm HM R ρ HR Hρ h' Hh' a i' E d Ha HE Hd Hdd.
  pose proof Hok as (HGc & HGap & Hc).
  pose proof HS as [S1 S2].
  inversion Hm as [| | | | | | ? ? ? ? ? A1 B1 C1 Hm1 Hp ]; subst.
  cbn in HM; destruct (member_unfold_ch gc_deps gc_stack Γ H ch) as [M0 |] eqn:HM0; cbn in HM; [| discriminate ].
  injection HM as <-.
  assert (Hch : ch <> nil) by (intros ->; inversion Hd).
  assert (Hch' : mk_term = mk_term -> ch <> nil) by (intros; exact Hch).
  destruct (S2 nil _ ch mk_term A1 Hm0 Hm1 Hch') as (m & n & Hr0 & Hr1 & Hmn).
  destruct m as [| m'].
  { exfalso; destruct (rep_top_zero _ _ Hr0) as [l Hl]; exact (typ_top_pi_absurd Hl HA0). }
  destruct n as [| n']; [ lia |].
  destruct (app_shift Hok _ _ _ _ _ _ _ HS HH Hm0 HA0 HB HN _ _ _ _ _ _ _ Hm1 Hch' Hp Hr1)
    as (HN1 & (l & HB1 & HC1 & HA1) & _).
  inversion Hh'; subst.
  match goal with He : eval_modexp _ _ _ _ ?h, Hap : eval_appm _ _ ?h ?c h' |- _ => rename He into Hh, Hap into Happ end.
  match goal with Hn : eval_exp _ _ _ _ ?c, Hap : eval_appm _ _ _ ?c h' |- _ => rename Hn into Hnv end.
  destruct (sel_appm _ _ _ Happ _ _ Hch Hd) as (f & Hf & Hfd).
  destruct (proj2 (S1 _ _ _ Hm1 Hch') _ _ HR Hρ _ Hh) as (a1 & Ha1 & Hma1).
  destruct (rel_exp_of_typ_inversion_simple_at HR HA1 _ _ Hρ) as (x1 & p1 & Hx1 & Hp1 & [Rp HRp]).
  functional_eval_rewrite_clear.
  inversion Hp1; subst.
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HRp (proj1 (per_univ_elem_sym _ _ _ _ HRp))) as (E0 & HE0 & _).
  destruct (rel_modexp_simple_at HR HH _ _ Hρ) as (h0 & h0' & Hh0 & Hh0' & Hhh).
  pose proof (functional_eval_modexp _ _ _ _ Hh Hh0) as <-.
  pose proof (functional_eval_modexp _ _ _ _ Hh Hh0') as <-.
  destruct (mtyped_rel HGc _ _ _ _ Hma1 _ _ _ Hhh HE0) as (v & v' & Hv & Hv' & Hvv).
  pose proof (functional_eval_selc _ _ _ _ Hf Hv) as <-.
  pose proof (functional_eval_selc _ _ _ _ Hf Hv') as <-.
  destruct (HU _ _ _ Hm1 HM0 _ _ HR Hρ _ Hh _ _ _ _ Ha1 HE0 Hf Hvv) as (m0 & Hm0' & Hm0f).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ HRp)) HRp) as (Rπ & Hπ & _).
  pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HE0 HRp) as F1.
  pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ HRp Hπ) as F2.
  assert (Hm0fπ : Rπ m0 f) by (apply F2, F1, Hm0f).
  destruct (per_univ_elem_pi_inv Hπ) as (in_rel & out & Hin & Hout & HEq).
  match goal with Hb : ⟦ B1 ⟧ ρ ↘ ?b1 |- _ => rename Hb into Hb1v end.
  destruct (rel_exp_under_ctx_simple_at HR HN1 _ _ Hρ) as (c1 & c2 & Hc1 & Hc2 & Hcc).
  pose proof (functional_eval_exp _ _ _ _ Hc1 Hnv) as ->.
  pose proof (functional_eval_exp _ _ _ _ Hc2 Hnv) as ->.
  match type of Hnv with eval_exp _ _ _ _ ?c => assert (Hcin : in_rel c c) by (eapply Hcc; eassumption) end.
  destruct (proj1 (HEq _ _) Hm0fπ _ _ Hcin) as [r0 r1 Hr0' Hr1' Hrr].
  pose proof (functional_eval_app _ _ _ _ Hr1' Hfd) as ->.
  destruct (Hout _ _ Hcin) as [bC bC' HbC HbC' HbCC].
  functional_eval_rewrite_clear.
  destruct (per_univ_of_instance HR HC1 HN1 _ _ Hρ Hnv) as (t & b & Ht & Hb & _ & [Rab HRab]).
  functional_eval_rewrite_clear.
  pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HE HRab) as G1.
  pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ HRab HbCC) as G2.
  exists r0; split; [ econstructor; eassumption | apply G1, G2, Hrr ].
Qed.

(** δ: a member of a module expression without arguments is its δ-reduct. *)
Lemma rel_exp_mem_delta : gmod_ok -> forall Γ H x A i M,
    Γ ⊨ᵐ H ≈ H -> sem_mt Γ H -> sem_unf Γ H -> member_type gc_deps gc_stack Γ H (x :: nil) mk_term A ->
    Γ ⊨ A : Type@i -> member_unfold gc_deps gc_stack Γ H x = Some M -> Γ ⊨ M : A ->
    Γ ⊨ a_mem H x ≈ M : A.
Proof.
  intros Hok * HH HS HU Hm HA HM HMv.
  pose proof Hok as (HGc & HGap & Hc).
  pose proof (rel_exp_mem_gen Hok _ _ _ _ _ _ HH HS Hm HA) as HV.
  pose proof HH as [R [HR _]].
  assert (HP : PER R) by (eapply per_env_PER; exact HR).
  apply (rel_exp_under_ctx_of_simple HR HV HMv).
  intros ρ ρ' Hρρ'.
  assert (Hρ : R ρ ρ) by (etransitivity; [ exact Hρρ' | symmetry; exact Hρρ' ]).
  destruct (rel_modexp_simple_at HR HH _ _ Hρ) as (h & h0 & Hh & Hh0 & Hhh).
  pose proof (functional_eval_modexp _ _ _ _ Hh Hh0) as <-.
  destruct (rel_exp_of_typ_inversion_simple_at HR HA _ _ Hρρ') as (a & a' & Ha & Ha' & [Raa HRaa]).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HRaa (proj1 (per_univ_elem_sym _ _ _ _ HRaa))) as (E & HE & _).
  destruct (proj2 (proj1 HS _ _ _ Hm ltac:(discriminate)) _ _ HR Hρ _ Hh) as (a1 & Ha1 & Hma).
  pose proof (functional_eval_exp _ _ _ _ Ha Ha1) as <-.
  destruct (mtyped_rel HGc _ _ _ _ Hma _ _ _ Hhh HE) as (v & v' & Hv & Hv' & Hvv).
  pose proof (functional_eval_selc _ _ _ _ Hv Hv') as <-.
  destruct (HU _ _ _ Hm HM _ _ HR Hρ _ Hh _ _ _ _ Ha HE Hv Hvv) as (m & Hm' & Hmv).
  destruct (rel_exp_under_ctx_simple_at HR HMv _ _ Hρρ') as (m1 & m2 & Hm1 & Hm2 & Hmm).
  pose proof (functional_eval_exp _ _ _ _ Hm' Hm1) as <-.
  exists v, m2; split; [ exact (eval_mem_of_sel _ _ _ _ _ Hh (selc_one_inv _ _ _ Hv)) |]; split; [ exact Hm2 |].
  eapply per_head_of; [ exact Ha | exact Ha' | exact HRaa |].
  pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HE HRaa) as F.
  assert (HPa : PER Raa) by (eapply per_elem_PER; exact HRaa).
  etransitivity; [ apply F; symmetry; exact Hmv | exact (Hmm _ _ _ _ Ha Ha' HRaa) ].
Qed.

End Fixed_GCtx.
