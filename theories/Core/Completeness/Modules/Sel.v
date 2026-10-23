(** * Submodules of Valid Units

    A submodule a valid unit, or a module expression valid in what it
    denotes, has by lookup is, in the PER model, the unit its module part
    stands for, which is valid ([valid_unit_sel_all]): the semantic counterpart
    of [δ] for selections.  Selection from values lacking a parameter is
    followed through the arguments ([sel_step]); a body's submodule is its
    closure, or what an open of the body reads ([body_sel_mod]); a filed
    module's, the filed submodule or the alias stored, at the arguments. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas MemberWf DescTyping LookupSound.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases FunctionCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Modules Require Import MemberTypes ModuleVal Values UnitSubst ModexpRel.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.Inductives Require Import Decl.
From Mctt.Core.Completeness.Modules Require Import ValidUnit Body Filed Unit Mem Canon App.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Semantic.Kinds Require Import Kinds KindsTyping KindsEval KindsPER.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.

(** ** Submodules at Every Environment *)

(** [dmod_has_sel y k v]: every value related to [k] has the submodule [y],
    related to [v]. *)
Definition dmod_has_sel (y : String.string) (k v : dmod) : Prop :=
  forall h, per_dmod h k -> exists r, h ·ₘ y gc_deps ⍮ gc_stack ↘ r /\ per_dmod r v.

Lemma valid_sel_resp_l : forall Γ H K y V, Γ ⊨ᵐ H ≈ K -> valid_sel Γ K y V -> valid_sel Γ H y V.
Proof.
  intros * HHK HS R HR ρ Hρ.
  destruct (HS _ HR _ Hρ) as [k v Hk Hv Hs].
  destruct (rel_modexp_at _ _ _ _ _ HHK HR _ _ Hρ) as (h0 & k' & Hh0 & Hk' & Hhk).
  pose proof (functional_eval_modexp _ _ _ _ Hk' Hk) as ->.
  apply (mk_valid_sel_at _ _ _ _ h0 v); [ exact Hh0 | exact Hv |].
  intros h Hh; exact (Hs _ (per_dmod_trans _ _ _ Hh Hhk)).
Qed.

Lemma valid_sel_resp_r : forall Γ K y V V', valid_sel Γ K y V -> Γ ⊨ᵐ V ≈ V' -> valid_sel Γ K y V'.
Proof.
  intros * HS HVV R HR ρ Hρ.
  destruct (HS _ HR _ Hρ) as [k v Hk Hv Hs].
  destruct (rel_modexp_at _ _ _ _ _ HVV HR _ _ Hρ) as (v0 & v' & Hv0 & Hv' & Hvv).
  pose proof (functional_eval_modexp _ _ _ _ Hv0 Hv) as ->.
  apply (mk_valid_sel_at _ _ _ _ k v'); [ exact Hk | exact Hv' |].
  intros h Hh; destruct (Hs _ Hh) as (r & Hr & Hrv); exists r; split; [ exact Hr | exact (per_dmod_trans _ _ _ Hrv Hvv) ].
Qed.

(** ** Selection from Values Lacking a Parameter *)

(** A submodule of a value lacking a parameter is, at every argument, the
    submodule of the value at it. *)
Lemma sel_step : forall y k v a a' i R,
    nextparam k a -> nextparam v a' -> per_univ_elem i R a a' ->
    (forall c c', R c c' -> exists vc, $ᵐ| v & c' | gc_deps ⍮ gc_stack ↘ vc) ->
    (forall c c' kc vc, R c c' -> $ᵐ| k & c | gc_deps ⍮ gc_stack ↘ kc -> $ᵐ| v & c' | gc_deps ⍮ gc_stack ↘ vc -> dmod_has_sel y kc vc) ->
    dmod_has_sel y k v.
Proof.
  intros * Hk Hv HR Ev IH h Hh.
  destruct (per_dmod_appm _ _ _ (per_dmod_sym _ _ Hh) Hk) as (i' & R' & ah & Hph & HR' & Happ).
  assert (E1 : R' <~> R) by (eapply per_univ_elem_right_irrel; [ exact HR' | exact HR ]).
  assert (HP : PER R) by (eapply per_elem_PER; exact HR).
  assert (HP' : PER R') by (eapply per_elem_PER; exact HR').
  assert (Hrefl : forall c c', R' c c' -> R' c c /\ R' c' c' /\ R c c /\ R c' c' /\ R c c').
  { intros c c' Hc.
    assert (Hcc : R' c c) by (etransitivity; [ exact Hc | symmetry; exact Hc ]).
    assert (Hc'c' : R' c' c') by (etransitivity; [ symmetry; exact Hc | exact Hc ]).
    repeat split; try assumption; apply E1; assumption. }
  (* the value has the submodule: at an argument it has *)
  pose proof (var_per_elem 0 HR') as Hc0.
  destruct (Happ _ _ Hc0) as (kc0 & hc0 & Hk0 & Hh0 & Hkh0).
  destruct (Hrefl _ _ Hc0) as (_ & _ & Hc00 & _ & _).
  destruct (Ev _ _ Hc00) as (vc0 & Hv0).
  destruct (IH _ _ _ _ Hc00 Hk0 Hv0 _ (per_dmod_sym _ _ Hkh0)) as (rc0 & Hrc0 & _).
  destruct (selm_of_appm _ _ Hph _ _ _ _ Hh0 Hrc0) as (r & Hr).
  exists r; split; [ exact Hr |].
  (* related to [v] at every pair of related arguments *)
  assert (HRav : per_univ_elem i' R' ah a').
  { eapply per_univ_trans; [ exact (proj1 (per_univ_elem_sym _ _ _ _ HR')) |].
    exact (per_univ_elem_resp_iff HR (fun m m' => conj (proj2 (E1 m m')) (proj1 (E1 m m')))). }
  assert (Hsel : forall c c' hc, R' c c' -> $ᵐ| h & c | gc_deps ⍮ gc_stack ↘ hc ->
             forall vc, $ᵐ| v & c' | gc_deps ⍮ gc_stack ↘ vc -> exists rc, hc ·ₘ y gc_deps ⍮ gc_stack ↘ rc /\ per_dmod rc vc).
  { intros c c' hc Hc Hhc vc Hvc.
    destruct (Hrefl _ _ Hc) as (Hcc & _ & _ & _ & HRcc').
    destruct (Happ _ _ Hcc) as (kc & hc' & Hkc & Hhc' & Hkh).
    pose proof (functional_eval_appm _ _ _ _ Hhc' Hhc) as ->.
    exact (IH _ _ _ _ HRcc' Hkc Hvc _ (per_dmod_sym _ _ Hkh)). }
  eapply (per_dmod_fun R'); [ exact (nextparam_selm Hgw _ _ Hph _ _ Hr) | exact Hv | exact HRav | | |].
  - intros c c' Hc.
    destruct (Hrefl _ _ Hc) as (Hcc & _ & HRcc & _ & _).
    destruct (Happ _ _ Hcc) as (kc & hc & _ & Hhc & _).
    destruct (Ev _ _ HRcc) as (vc & Hvc).
    destruct (Hsel _ _ _ Hcc Hhc _ Hvc) as (rc & Hrc & _).
    exists rc; apply (selm_appm_comm _ _ Hph _ _ _ _ Hr Hhc); exact Hrc.
  - intros c c' Hc; destruct (Hrefl _ _ Hc) as (_ & _ & _ & _ & Hcc'); exact (Ev _ _ Hcc').
  - intros c c' rc vc Hc Hrc Hvc.
    destruct (Hrefl _ _ Hc) as (Hcc & _ & _ & _ & _).
    destruct (Happ _ _ Hcc) as (kc & hc & _ & Hhc & _).
    destruct (Hsel _ _ _ Hc Hhc _ Hvc) as (rc' & Hrc' & Hrr).
    apply (selm_appm_comm _ _ Hph _ _ _ _ Hr Hhc) in Hrc.
    pose proof (functional_eval_selm _ _ _ _ Hrc Hrc') as ->; exact Hrr.
Qed.

(** A submodule of a unit lacking parameters, against the alias over them
    of the submodule with them given. *)
Lemma sel_walk : forall Δ Γ D y V0 RΓ, tele_ass Δ -> ⊨ Δ ++ Γ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    (forall R, EF Δ ++ Γ ≈ Δ ++ Γ ∈ per_ctx_env ↘ R -> forall ρ ρ', R ρ ρ' ->
       exists k0 v0, ⟦ nil ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ k0 /\ ⟦ V0 ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ' ↘ v0 /\ dmod_has_sel y k0 v0) ->
    forall ρ ρ', RΓ ρ ρ' ->
    exists k v, ⟦ Δ ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ k /\ ⟦ Δ ⊢ md_alias V0 ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ' ↘ v /\ dmod_has_sel y k v.
Proof.
  induction Δ as [| e Δ0 IH] using rev_ind; intros * HΔ HC HΓ Hbase ρ ρ' Hρ; cbn [List.app] in *.
  - destruct (Hbase _ HΓ _ _ Hρ) as (k0 & v0 & Hk0 & Hv0 & Hs).
    exists k0, v0; split; [ exact Hk0 | split; [ apply eval_close_alias0; exact Hv0 | exact Hs ] ].
  - destruct (tele_ass_app_inv _ _ HΔ) as [HΔ0 He]; inversion He as [| ? ? [A ->] _]; subst.
    rewrite <- app_assoc in HC, Hbase; cbn [List.app] in HC, Hbase.
    destruct (rel_ctx_wf_ass_inv (rel_ctx_wf_app_r _ _ HC)) as [i HA].
    pose proof (per_ctx_env_of_typ HΓ HA) as HΓA.
    destruct (rel_exp_of_typ_inversion_simple_at HΓ HA _ _ Hρ) as (a & a' & Ha & Ha' & [Ra HRa]).
    assert (Hext : forall c c', Ra c c' -> per_env_extend A A RΓ (ρ ↦ c) (ρ' ↦ c'))
      by (intros c c' Hc; split; [ exact Hρ | eapply per_head_of; [ exact Ha | exact Ha' | exact HRa | exact Hc ] ]).
    assert (Hl : 0 < List.length (Δ0 ++ ce_ass A :: nil)) by (rewrite length_app; cbn; lia).
    exists (dm_local (Δ0 ++ ce_ass A :: nil) D ρ), (dm_local (Δ0 ++ ce_ass A :: nil) (md_alias V0) ρ').
    split; [ apply close_unsat; exact Hl |]; split; [ apply close_unsat; exact Hl |].
    eapply sel_step; [ constructor; exact Ha | constructor; exact Ha' | exact HRa | |].
    + intros c c' Hc.
      destruct (IH (Γ ▹ A) _ _ _ _ HΔ0 HC HΓA Hbase _ _ (Hext _ _ Hc)) as (k1 & v1 & _ & Hv1 & _).
      exists v1; constructor; exact Hv1.
    + intros c c' kc vc Hc Hkc Hvc.
      inversion Hkc as [| ? ? ? ? ? ? Hkc' Hl1 |]; subst; apply app_inj_tail in Hl1 as [<- [= <-]].
      inversion Hvc as [| ? ? ? ? ? ? Hvc' Hl2 |]; subst; apply app_inj_tail in Hl2 as [<- [= <-]].
      destruct (IH (Γ ▹ A) _ _ _ _ HΔ0 HC HΓA Hbase _ _ (Hext _ _ Hc)) as (k1 & v1 & Hk1 & Hv1 & Hs1).
      pose proof (functional_eval_close _ _ _ _ _ Hk1 Hkc') as ->.
      pose proof (functional_eval_close _ _ _ _ _ Hv1 Hvc') as ->.
      exact Hs1.
Qed.

(** A submodule of a global module at arguments related at its telescope,
    against a family of values lacking the same parameters, given at the
    arguments. *)
Lemma global_sel : forall p T Φ y (W : list domain -> dmod -> Prop),
    gc_loc gc_deps gc_stack p = Some (T, Φ) -> tele_ass T -> ⊨ T ->
    (forall ns ns' w, List.length ns = List.length T -> per_gargs (rev T) nil nil ns ns' -> W ns' w ->
       exists r, dm_global p ns ·ₘ y gc_deps ⍮ gc_stack ↘ r /\ per_dmod r w) ->
    (forall ns w a, List.length ns < List.length T -> W ns w -> nextparam (dm_global p ns) a -> nextparam w a) ->
    (forall ns ns' c c' w, List.length ns < List.length T -> per_gargs (rev T) nil nil (ns ++ c :: nil) (ns' ++ c' :: nil) ->
       W ns' w -> exists w', $ᵐ| w & c' | gc_deps ⍮ gc_stack ↘ w' /\ W (ns' ++ c' :: nil) w') ->
    forall ns ns' w, List.length ns <= List.length T -> per_gargs (rev T) nil nil ns ns' -> W ns' w ->
      dmod_has_sel y (dm_global p ns) w.
Proof.
  intros * Hm HTa HT Hsat HFp HFa ns ns' w Hle Hg Hw.
  remember (List.length T - List.length ns) as n eqn:Hn.
  revert ns ns' w Hn Hle Hg Hw; induction n as [| n IH]; intros ns ns' w Hn Hle Hg Hw.
  - intros h Hh.
    inversion Hh as [p0 T0 oD0 ns0 ns1 Hm0 Hl0 Hg0 | | ? ? ? ? ? Rf Hpf Hpf' _ _ _ _]; subst.
    + rewrite Hm in Hm0; injection Hm0 as <- <-.
      assert (Hd : per_dmod (dm_global p ns0) (dm_global p ns')).
      { eapply per_dmod_trans; [ exact Hh |].
        eapply gval_rel; [ exact Hm | exact HTa | exact HT | reflexivity | exact Hle | exact Hg ]. }
      inversion Hd as [p1 T1 oD1 ns2 ns3 Hm1 Hl1 Hg1 | | ? ? ? ? ? Rf Hpf Hpf' _ _ _ _]; subst.
      * rewrite Hm in Hm1; injection Hm1 as <- <-.
        exact (Hsat _ _ _ Hl0 Hg1 Hw).
      * exfalso; destruct (nextparam_global_lt _ _ _ Hpf) as (T2 & oT2 & Hm2 & Hlt).
        rewrite Hm in Hm2; injection Hm2 as <- <-; lia.
    + exfalso; destruct (nextparam_global_lt _ _ _ Hpf') as (T2 & oT2 & Hm2 & Hlt).
      rewrite Hm in Hm2; injection Hm2 as <- <-; lia.
  - (* one more parameter missing *)
    pose proof (per_gargs_len_eq _ _ _ _ _ Hg) as Hl'.
    destruct (nth_error (rev T) (List.length ns)) as [e |] eqn:Hne;
      [| apply nth_error_None in Hne; rewrite length_rev in Hne; lia ].
    destruct (tele_split_rev _ _ _ Hne) as (l1 & l2 & Hrev & Hl1 & HT').
    assert (Ha : tele_ass (rev l2 ++ e :: rev l1)) by (rewrite <- HT'; exact HTa).
    apply Forall_app in Ha as [_ Ha]; inversion Ha as [| ? ? [A ->] _]; subst e.
    pose proof HT as HT0; rewrite HT' in HT0.
    pose proof (rel_ctx_wf_app_r _ _ HT0) as HAT.
    destruct (rel_ctx_wf_ass_inv HAT) as [i HA].
    pose proof (rel_ctx_wf_tail HAT) as HTl.
    destruct (rel_ctx_wf_per_ctx_env HTl) as [R0 HR0].
    assert (Hg0 : per_gargs l1 nil nil ns ns').
    { rewrite Hrev in Hg; rewrite <- (app_nil_r ns), <- (app_nil_r ns') in Hg.
      exact (proj1 (per_gargs_app l1 (ce_ass A :: l2) nil nil ns ns' nil nil ltac:(lia) Hg ltac:(lia))). }
    assert (Hρ : R0 (env_args nil ns) (env_args nil ns')).
    { rewrite <- (app_nil_r (rev l1)) in HTl, HR0.
      eapply (gargs_env_rel_gen _ _ _ _ _ _ _ _ per_ctx_env_nil_true HR0 HTl I);
        [ rewrite length_rev; lia | rewrite rev_involutive; exact Hg0 ]. }
    destruct (rel_exp_of_typ_inversion_simple_at HR0 HA _ _ Hρ) as (a & a' & Ha0 & Ha0' & [RA HRA]).
    assert (Hlt : List.length ns < List.length T) by lia.
    assert (Hne' : nth_error (rev T) (List.length ns') = Some (ce_ass A)) by (rewrite <- Hl'; exact Hne).
    assert (Hgs : forall c c', RA c c' -> per_gargs (rev T) nil nil (ns ++ c :: nil) (ns' ++ c' :: nil)).
    { intros c c' Hc.
      rewrite Hrev; change (l1 ++ ce_ass A :: l2) with (l1 ++ (ce_ass A :: nil) ++ l2); rewrite app_assoc.
      rewrite <- (app_nil_r (ns ++ c :: nil)), <- (app_nil_r (ns' ++ c' :: nil)).
      apply per_gargs_app_intro; [ rewrite !length_app; cbn; lia | | constructor ].
      eapply per_gargs_snoc; [ lia | exact Hg0 | econstructor; eassumption | exact Hc ]. }
    eapply sel_step; [ econstructor; [ exact Hm | exact Hne | exact Ha0 ]
                     | apply (HFp ns'); [ lia | exact Hw | econstructor; [ exact Hm | exact Hne' | exact Ha0' ] ] | exact HRA | |].
    + intros c c' Hc; destruct (HFa _ _ _ _ _ Hlt (Hgs _ _ Hc) Hw) as (w' & Hw' & _); exists w'; exact Hw'.
    + intros c c' kc vc Hc Hkc Hvc.
      inversion Hkc; subst kc.
      destruct (HFa _ _ _ _ _ Hlt (Hgs _ _ Hc) Hw) as (w' & Hw' & HWw').
      pose proof (functional_eval_appm _ _ _ _ Hvc Hw') as ->.
      apply (IH _ (ns' ++ c' :: nil)); [ rewrite length_app; cbn; lia | rewrite length_app; cbn; lia | exact (Hgs _ _ Hc) | exact HWw' ].
Qed.

(** Applying related closures to arguments related at their telescope,
    the left one's environment underneath. *)
Lemma closure_gargs : forall ns Ta D ρ ρ' ρb ns', tele_ass Ta -> List.length ns <= List.length Ta ->
    per_dmod (dm_local Ta D ρ) (dm_local Ta D ρ') -> per_gargs (rev Ta) ρ ρb ns ns' ->
    exists w w', $ᵐ*| dm_local Ta D ρ & ns | gc_deps ⍮ gc_stack ↘ w /\ $ᵐ*| dm_local Ta D ρ' & ns' | gc_deps ⍮ gc_stack ↘ w' /\
      per_dmod w w'.
Proof.
  induction ns as [| c ns IH]; intros * HTa Hl Hd Hg.
  - inversion Hg; subst; exists (dm_local Ta D ρ), (dm_local Ta D ρ'); repeat split; [ constructor | constructor | exact Hd ].
  - destruct (tele_ass_last _ HTa ltac:(destruct Ta; cbn in Hl; [ lia | discriminate ])) as (Ta0 & A & ->).
    rewrite rev_app_distr in Hg; cbn [rev List.app] in Hg.
    inversion Hg as [| ? A' ? ? a a' ts ? ns0' R HA Hc Hg0]; subst.
    destruct HA as [x x' Hx Hx' HRx].
    destruct (per_dmod_appm _ _ _ Hd (np_local _ _ _ _ _ Hx)) as (i' & R' & ah & Hph & HR' & Happ).
    assert (E : R <~> R') by (eapply per_univ_elem_right_irrel; [ exact HRx | exact HR' ]).
    destruct (Happ _ _ (proj1 (E _ _) Hc)) as (hc & hc' & Hhc & Hhc' & Hhh).
    rewrite length_app in Hl; cbn in Hl.
    apply List.Forall_app in HTa as [HTa0 _].
    inversion Hhc as [| Δ1 D1 ρ1 n1 r1 A1 Hcl Heq |]; subst D1 ρ1 n1 r1;
      apply app_inj_tail in Heq as [-> [= ->]].
    inversion Hhc' as [| Δ1 D1 ρ1 n1 r1 A1 Hcl' Heq' |]; subst D1 ρ1 n1 r1;
      apply app_inj_tail in Heq' as [-> [= ->]].
    destruct ns as [| c1 ns1].
    + inversion Hg0; subst.
      exists hc, hc'; split; [ econstructor; [ exact Hhc | constructor ] |]; split; [ econstructor; [ exact Hhc' | constructor ] | exact Hhh ].
    + assert (HTa0l : 0 < List.length Ta0) by (cbn in Hl; lia).
      pose proof (functional_eval_close _ _ _ _ _ Hcl (close_unsat _ _ _ HTa0l)) as ->.
      pose proof (functional_eval_close _ _ _ _ _ Hcl' (close_unsat _ _ _ HTa0l)) as ->.
      destruct (IH _ _ _ _ _ _ HTa0 ltac:(cbn in Hl |- *; lia) Hhh Hg0) as (w & w' & Hw & Hw' & Hww).
      exists w, w'; split; [ econstructor; [ exact Hhc | exact Hw ] |]; split; [ econstructor; [ exact Hhc' | exact Hw' ] | exact Hww ].
Qed.

Lemma eval_me_apps_inv : forall Ns H ρ v, ⟦ me_apps H Ns ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ v ->
    exists h ns, ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h /\ ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns /\
      $ᵐ*| h & ns | gc_deps ⍮ gc_stack ↘ v.
Proof.
  induction Ns as [| N Ns IH]; intros * Hv; cbn [me_apps] in Hv.
  - exists v, nil; split; [ exact Hv | split; constructor ].
  - destruct (IH _ _ _ Hv) as (h1 & ns & Hh1 & Hns & Ha).
    inversion Hh1; subst.
    match goal with HH : eval_modexp _ _ H ρ ?h, Hap : eval_appm _ _ ?h ?n h1 |- _ =>
      exists h, (n :: ns); split; [ exact HH | split; econstructor; eassumption ] end.
Qed.

Lemma tele_insts_app_full : forall Δ1 Δ2 σ Ms, tele_ass Δ2 -> List.length Ms = List.length Δ2 ->
    tele_insts (Δ1 ++ Δ2) σ Ms = tele_insts Δ2 σ Ms.
Proof.
  intros * Ha Hl.
  rewrite <- (app_nil_r Ms) at 1; rewrite tele_insts_app by assumption.
  unfold tele_insts; destruct (rev Δ1) as [| [] ?]; cbn; apply app_nil_r.
Qed.

Lemma per_gargs_app_short : forall ts ρ ρ' xs xs', per_gargs ts ρ ρ' xs xs' -> forall ts2, per_gargs (ts ++ ts2) ρ ρ' xs xs'.
Proof. induction 1; intros; cbn [List.app]; econstructor; eauto. Qed.

Lemma dmod_has_sel_resp_r : forall y k v v', dmod_has_sel y k v -> per_dmod v v' -> dmod_has_sel y k v'.
Proof. intros * Hs Hv h Hh; destruct (Hs _ Hh) as (r & Hr & Hrv); exists r; split; [ exact Hr | exact (per_dmod_trans _ _ _ Hrv Hv) ]. Qed.

Lemma dmod_has_sel_resp_l : forall y k k' v, dmod_has_sel y k v -> per_dmod k' k -> dmod_has_sel y k' v.
Proof. intros * Hs Hk h Hh; exact (Hs _ (per_dmod_trans _ _ _ Hh Hk)). Qed.

Section Desc.
  Variables (Θm : gdeps) (Ξm : gstack).
  Hypothesis Hgm : ⊢ᵍ Θm ⍮ Ξm.

(** ** What the Submodules of Literals Denote *)

(** A module of a body, filled in, over the parameters. *)
Lemma body_mod_desc : forall Γ Δ Φ Φx y R Rm, body_xp Θm Ξm (Δ ++ Γ) Φ Φx ->
    mdenote Θm Ξm Γ (me_mem (me_lit (gu_open Δ Φ)) y) R -> ds_mod Θm Ξm R = Some Rm ->
    exists Φ' pv U σ RU, gm_prefix_upto Φx y = Some (gm_ext Φ' y (ge_mod pv U)) /\ gm_fill Φ' = Some σ /\
      udenote Θm Ξm (body_ctx Φ' ++ Δ ++ Γ) None U RU /\ Rm = ds_up Δ (ds_sub RU σ).
Proof.
  intros * Hx Hm Hmd.
  inversion Hm as [? ? ? ? ? Hq _ | ? ? ? ? ? ? Hq _ | | | |? ? ? R0 R0m Γy E rd R1 ? Hm0 Hmd0 He Hed Hr | ? ? ? ? Hq _]; subst;
    [ cbn in Hq; discriminate | cbn in Hq; discriminate | | cbn in Hq; discriminate ].
  inversion Hm0; subst; try (match goal with Hq : mod_qname (me_lit _) = Some _ |- _ => cbn in Hq; discriminate end).
  match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
  match goal with Hb : ds_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
  match goal with Hx' : body_xp _ _ _ Φ ?Φx1 |- _ =>
    pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hgm)))) _ _ _ Hx _ Hx') as <- end.
  cbn in Hmd0; injection Hmd0 as <-.
  cbn in He; destruct (gm_prefix_upto Φx y) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
  pose proof (gm_prefix_name _ _ _ _ _ Hp) as ->.
  destruct E0 as [[|] pv A0 [M0 |] | pv U | | |]; try discriminate; injection He as <- <- <-.
  - exfalso; inversion Hed; subst; cbn in Hr.
    destruct (gm_fill Φ'); cbn in Hr; [ injection Hr as <- | discriminate ]; cbn in Hmd; discriminate.
  - inversion Hed; subst.
    cbn in Hr; destruct (gm_fill Φ') as [σ |] eqn:Hf; cbn in Hr; [ injection Hr as <- | discriminate ].
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as HmU end.
    rewrite (ds_is_mod_mod _ _ _ (ds_is_mod_up Δ _ (ds_is_mod_sub _ σ HmU))) in Hmd; injection Hmd as <-.
    do 5 eexists; split; [ reflexivity | split; [ exact Hf | split; [ rewrite app_assoc; eassumption | reflexivity ] ] ].
Qed.

(** A submodule of an alias is its target's, over the parameters. *)
Lemma alias_mod_desc : forall Γ Δ E y R Rm, ⊢ Θm ⍮ Ξm ⍮ Δ ++ Γ ->
    mdenote Θm Ξm Γ (me_mem (me_lit (gu_mk Δ (md_alias E))) y) R -> ds_mod Θm Ξm R = Some Rm ->
    exists R', mdenote Θm Ξm (Δ ++ Γ) (me_mem E y) R' /\ R = ds_up Δ R'.
Proof.
  intros * HΔΓ Hm HmR.
  inversion Hm as [? ? ? ? ? Hq _ | ? ? ? ? ? ? Hq _ | | | |? ? ? R0 R0m Γy Ee rd R1 ? Hm0 Hmd He Hed Hr | ? ? ? ? Hq _]; subst;
    [ cbn in Hq; discriminate | cbn in Hq; discriminate | | cbn in Hq; discriminate ].
  inversion Hm0; subst; try (match goal with Hq : mod_qname (me_lit _) = Some _ |- _ => cbn in Hq; discriminate end).
  match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu as [| ? ? ? ? RE REm HmE HmodE]; subst end.
  pose proof (ds_mod_is_mod _ _ _ _ HmodE) as HisE.
  rewrite (ds_is_mod_mod _ _ _ (ds_is_mod_up _ _ HisE)) in Hmd; injection Hmd as <-.
  destruct REm as [| Δe Φ Φx | Θ p T Φ Ns | |] eqn:EREm; cbn in HisE; try contradiction; cbn [ds_up] in He, Hed.
  - (* an open module part *)
    cbn in He; destruct (gm_prefix_upto Φx y) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
    pose proof (gm_prefix_name _ _ _ _ _ Hp) as ->.
    assert (He' : exists Ee', ds_entry (ds_open Δe Φ Φx) y = Some (body_ctx Φ' ++ Δe, Ee', rd_open Δe Φ') /\
                    Ee = Ee' /\ Γy = body_ctx Φ' ++ Δe ++ Δ /\ rd = rd_open (Δe ++ Δ) Φ').
    { cbn; rewrite Hp; destruct E0 as [[|] ? ? [] | | | |]; try discriminate; injection He as <- <- <-; eexists; repeat split. }
    destruct He' as (Ee' & He' & -> & -> & ->).
    cbn [ds_read] in Hr; destruct (gm_fill Φ') as [σ |] eqn:Hf; cbn in Hr; [ injection Hr as <- | discriminate ].
    exists (ds_up Δe (ds_sub R1 σ)); split; [| rewrite ds_up_cat; reflexivity ].
    cbn [ds_epath] in Hed; rewrite <- !app_assoc in Hed.
    eapply dn_mem; [ exact HmE | exact HmodE | exact He' | cbn [ds_epath]; rewrite <- app_assoc; exact Hed | cbn; rewrite Hf; reflexivity ].
  - (* a closed module part: its entries read alike in any context *)
    cbn in He; destruct (gm_prefix_upto Φ y) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
    injection He as <- <- <-.
    cbn [ds_read] in Hr; destruct (ds_ats R1 Ns) as [R2 |] eqn:Ha; cbn in Hr; [ injection Hr as <- | discriminate ].
    pose proof (ds_canon_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hgm HmE) HmodE) as Hc; cbn in Hc.
    pose proof (loc_closed _ _ Hgm _ _ _ Hc) as HU.
    assert (He0 : ds_entry (ds_closed Θ p T Φ Ns) y = Some (nil, ge_read T E0, rd_closed Θ Ns (apps (a_mem (qname_mod p) y) Ns)))
      by (cbn; rewrite Hp; reflexivity).
    destruct (ds_entry_closed _ _ _ _ _ _ _ _ _ HU He0) as (_ & HsE & _).
    pose proof (ctx_app_wf_right _ _ _ _ HΔΓ) as HΓ.
    assert (Hσ : sub_mod_compat (sb_of_wk (wk_shiftn (List.length Δ))) (Δ ++ Γ) Γ)
      by (eapply wf_sub_mod_compat, wf_sub_of_wk, wf_wk_shiftn_app; eassumption).
    cbn [ds_epath] in Hed.
    assert (Hed' : edenote Θm Ξm (nil ++ Δ ++ Γ) (Some (qname_in p y)) (ge_read T E0) R1)
      by exact (edenote_closed_move _ _ _ _ _ _ _ _ (wf_gstack_closed _ _ Hgm) HsE Hed Hσ).
    exists (ds_up Θ (ds_named Θ Ns (apps (a_mem (qname_mod p) y) Ns) R2)); split.
    { eapply dn_mem; [ exact HmE | exact HmodE | exact He0 | exact Hed' | cbn; rewrite Ha; reflexivity ]. }
    (* a module is read alike with any outside parameters *)
    rewrite ds_up_cat; destruct R2 as [A0 om | | | |]; [| rewrite !ds_named_fix by reflexivity; reflexivity .. ].
    exfalso; assert (Ht : exists om', ds_named (Θ ++ Δ) Ns (apps (a_mem (qname_mod p) y) Ns) (ds_term A0 om) = ds_term A0 om')
      by (apply (ds_named_cases (fun R => exists om', R = ds_term A0 om')); [| destruct om ]; eexists; reflexivity).
    destruct Ht as [om' Ht]; rewrite Ht in HmR; cbn in HmR; discriminate.
Qed.

(** A submodule of a filed module at arguments: a filed module, at the
    arguments; or an alias stored, at them. *)
Lemma filed_mod_desc : forall Γ p T Φ Ns y R Rm, gc_loc Θm Ξm p = Some (T, Φ) ->
    mdenote Θm Ξm Γ (me_mem (me_apps (qname_mod p) Ns) y) R -> ds_mod Θm Ξm R = Some Rm ->
    (exists Tq Φq, gc_loc Θm Ξm (qname_in p y) = Some (Tq, Φq) /\ Rm = ds_closed nil (qname_in p y) Tq Φq Ns) \/
    (exists Φ0 E Ua RU, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) /\ entry_alias_unit E = Some Ua /\
       mdenote Θm Ξm Γ (me_apps (me_lit Ua) Ns) RU /\ ds_mod Θm Ξm RU = Some Rm).
Proof.
  intros * Hgl Hm Hmd.
  inversion Hm as [? ? pu Tq Φq Hq Hu | ? ? pu pq k D Hq Hk | | | | ? ? ? R0 R0m Γy E rd R1 ? Hm0 Hmd0 He Hed Hr
                  | ? ? pu Rr Hq Hk]; subst.
  2:{ (* the open frame of a member's module: its frame, at no argument *)
    left.
    destruct Ns as [| N Ns _] using rev_ind; [| rewrite me_apps_snoc in Hq; cbn in Hq; discriminate ].
    cbn [me_apps] in *; rewrite <- qname_mod_in, mod_qname_qname_mod in Hq; injection Hq as <-.
    destruct (ds_mod_ind_frame _ _ Hgm _ _ _ _ nil nil Hk) as (Tq & Φq & Hf & Hmd'); rewrite Hmd' in Hmd; injection Hmd as <-.
    exists Tq, Φq; split; [ unfold gc_loc; rewrite Hf; reflexivity | reflexivity ]. }
  3:{ (* the open frame of a record type's module: its frame, at no argument *)
    left.
    destruct Ns as [| N Ns _] using rev_ind; [| rewrite me_apps_snoc in Hq; cbn in Hq; discriminate ].
    cbn [me_apps] in *; rewrite <- qname_mod_in, mod_qname_qname_mod in Hq; injection Hq as <-.
    destruct (ds_mod_record_frame _ _ Hgm _ _ nil nil Hk) as (Tq & Φq & Hf & Hmd'); rewrite Hmd' in Hmd; injection Hmd as <-.
    exists Tq, Φq; split; [ unfold gc_loc; rewrite Hf; reflexivity | reflexivity ]. }
  - (* a loaded unit or an open frame *)
    left.
    destruct Ns as [| N Ns _] using rev_ind; [| rewrite me_apps_snoc in Hq; cbn in Hq; discriminate ].
    cbn [me_apps] in *; rewrite <- qname_mod_in, mod_qname_qname_mod in Hq; injection Hq as <-.
    destruct (gc_unit_loc _ _ _ _ _ Hu) as (mp & Hq & Hl).
    rewrite <- qname_mod_in, mod_qname_qname_mod in Hq; injection Hq as <-.
    cbn in Hmd; injection Hmd as <-.
    exists Tq, Φq; split; [ exact (gc_loc_of_loc _ _ Hgm _ _ _ Hl) | reflexivity ].
  - destruct (filed_denote _ _ Hgm _ _ _ Γ Ns Hgl) as (R2 & Hm2 & Hmod2).
    pose proof (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm0 _ Hm2) as ->.
    rewrite Hmod2 in Hmd0; injection Hmd0 as <-.
    cbn in He; destruct (gm_prefix_upto Φ y) as [[| Φ0 z E0 | ] |] eqn:Hp; try discriminate.
    pose proof (gm_prefix_name _ _ _ _ _ Hp) as ->.
    injection He as <- <- <-; cbn [ds_epath List.app] in Hed.
    pose proof (gc_loc_loc _ _ _ _ _ Hgl) as Hl.
    destruct (loc_closed _ _ Hgm _ _ _ Hl) as [_ HΦc].
    pose proof (body_closed_prefix _ _ _ _ HΦc Hp) as HΦ0; cbn in HΦ0; destruct HΦ0 as [_ HE0].
    destruct (gm_prefix_entry _ _ _ Hp) as (Φ0' & E0' & [= <- <-] & Hent).
    destruct E0 as [b pv A0 oM | pv [Δy [sm Φy | Ea]] | pv pq k ΦD Φm | pv Δa pm pq k Nsa | pv Rr Φr]; cbn [ge_read] in Hed, HE0.
    + (* a definition is no module *)
      exfalso; inversion Hed; subst; cbn [ds_read] in Hr.
      destruct (ds_ats _ Ns) as [R3 |] eqn:Ha; cbn in Hr; [ injection Hr as <- | discriminate ].
      destruct (ds_ats_term _ _ _ _ Ha) as (A' & om' & ->); rewrite ds_mod_named_term in Hmd; discriminate.
    + (* a body module: filed at its own path *)
      left; destruct HE0 as (-> & _ & HΦy).
      inversion Hed as [| ? ? ? ? R3 Hu | | |]; subst.
      inversion Hu as [? ? ? ? ? Φyx ? Hx Hb |]; subst.
      cbn in Hb; injection Hb as <-.
      rewrite (body_xp_noopen_id _ _ _ _ _ (body_closed_noopen _ _ HΦy) Hx) in Hr.
      cbn [ds_read] in Hr; rewrite ds_ats_closed_nil in Hr; cbn in Hr; injection Hr as <-.
      rewrite ds_named_fix in Hmd by reflexivity; cbn in Hmd; injection Hmd as <-.
      destruct (loc_child_mod _ _ Hgm _ _ _ Hl _ _ _ _ _ Hent) as [Hb _].
      exists (Δy ++ T), Φy; split; [ exact (gc_loc_of_loc _ _ Hgm _ _ _ (or_intror Hb)) | reflexivity ].
    + (* an alias module: the stored unit at the arguments *)
      right.
      inversion Hed as [| ? ? ? ? R3 Hu | | |]; subst.
      inversion Hu as [| ? ? ? ? RE REm HmE HmodE]; subst.
      assert (HmU : mdenote Θm Ξm Γ (me_lit (gu_mk Δy (md_alias Ea))) (ds_up Δy REm))
        by (apply dn_lit; eapply un_alias; eassumption).
      cbn [ds_read] in Hr; destruct (ds_ats (ds_up Δy REm) Ns) as [R3 |] eqn:Ha; cbn in Hr; [ injection Hr as <- | discriminate ].
      pose proof (ds_ats_is_mod _ _ _ (ds_is_mod_up _ _ (ds_mod_is_mod _ _ _ _ HmodE)) Ha) as HmR3.
      assert (Es : ds_self (apps (a_mem (qname_mod p) y) Ns) R3 = R3) by (destruct R3 as [? [] | | | |]; cbn in HmR3 |- *; first [ contradiction | reflexivity ]).
      rewrite (ds_named_fix _ _ _ _ Es), ds_up_nil in Hmd.
      exists Φ0, (ge_mod pv (gu_mk Δy (md_alias Ea))), (gu_mk Δy (md_alias Ea)), R3.
      split; [ reflexivity | split; [ reflexivity | split; [ exact (mdenote_apps _ _ _ _ _ _ _ HmU Ha) | exact Hmd ] ] ].
    + (* a member of a group: its module is filed at the member's path *)
      left.
      inversion Hed; subst.
      cbn [ds_read] in Hr; rewrite ds_ats_ind_nil in Hr; cbn in Hr; injection Hr as <-.
      pose proof (proj2 (loc_entry _ _ Hgm _ _ _ Hl _ _) Hent) as Hge.
      pose proof (isp_path _ _ _ _ (gc_entry_selfpath _ _ Hgm _ _ _ _ _ _ Hge)) as Hsp.
      pose proof (ind_mlookup_group _ _ Hgm _ _ _ _ (proj2 (gc_entry_ind _ _ _ _ _ _ _ _ Hge))) as Hlq.
      rewrite ds_named_fix in Hmd by reflexivity.
      destruct (ds_mod_ind_inv _ _ _ _ _ _ _ Hmd) as (D1 & pm1 & Tb & Φb & Hl1 & Hpm & Hb & ->).
      rewrite Hlq in Hl1; injection Hl1 as <-; rewrite Hsp in Hpm; injection Hpm as <-.
      exists Tb, Φb; split; [ exact Hb | reflexivity ].
    + (* an inductive alias: the alias of the module of the member it names, at the arguments *)
      right.
      inversion Hed; subst.
      cbn [ds_read] in Hr; destruct (ds_ats (ds_ind Δa pq k Nsa) Ns) as [R3 |] eqn:Ha; cbn in Hr; [ injection Hr as <- | discriminate ].
      destruct (ds_ats_ind _ _ _ _ _ _ Ha) as (Θ'' & Ns'' & ->); rewrite ds_named_fix in Hmd by reflexivity.
      cbn [ds_up] in Hmd; rewrite app_nil_r in Hmd.
      pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ (proj2 (loc_valid _ _ _ _ _ (gctx_valid_syn _ _ Hgm) Hl)) Hp)
        as [_ [D1 M1 Hl1 _ _ Hpm1 _ _ _ _]].
      assert (Hb : exists Tb Φb, gc_loc Θm Ξm pm = Some (Tb, Φb))
        by (cbn in Hmd; rewrite Hl1, Hpm1 in Hmd; destruct (gc_loc Θm Ξm pm) as [[Tb Φb] |]; [ eauto | discriminate ]).
      destruct Hb as (Tb & Φb & Hglq).
      destruct (filed_denote _ _ Hgm _ _ _ (Δa ++ Γ) Nsa Hglq) as (RE & HmE & HmodE).
      assert (HmU : mdenote Θm Ξm Γ (me_lit (gu_mk Δa (md_alias (me_apps (qname_mod pm) Nsa)))) (ds_closed Δa pm Tb Φb Nsa))
        by (apply dn_lit; exact (un_alias _ _ _ _ _ _ _ _ HmE HmodE)).
      assert (Hmi : ds_mod Θm Ξm (ds_ind Δa pq k Nsa) = Some (ds_closed Δa pm Tb Φb Nsa))
        by (cbn; rewrite Hl1, Hpm1, Hglq; reflexivity).
      destruct (ds_mod_ats _ _ _ _ _ _ Hmi Ha) as (Rm' & Ha' & Hmd').
      rewrite Hmd in Hmd'; injection Hmd' as <-.
      exists Φ0, (ge_ind_alias pv Δa pm pq k Nsa), (gu_mk Δa (md_alias (me_apps (qname_mod pm) Nsa))), Rm.
      split; [ reflexivity | split; [ reflexivity | split; [ exact (mdenote_apps _ _ _ _ _ _ _ HmU Ha') |] ] ].
      apply ds_is_mod_mod; exact (ds_ats_is_mod _ (ds_closed Δa pm Tb Φb Nsa) _ I Ha').
    + (* a record type: its module is filed at the record's path *)
      left.
      inversion Hed; subst.
      cbn [ds_read] in Hr; rewrite ds_ats_record_nil in Hr; cbn in Hr; injection Hr as <-.
      rewrite ds_named_fix in Hmd by reflexivity.
      destruct (ds_mod_record_inv _ _ _ _ _ _ Hmd) as (Tb & Φb & Hb & ->).
      exists Tb, Φb; split; [ exact Hb | reflexivity ].
Qed.

(** ** Modules of a Body *)

(** A module of a valid body, against the module of the same name of any
    body related to it: a module written in the body by its closure; one
    a local open generates by its target, or its target's submodule, read
    again past the entries before it. *)
Lemma body_sel_mod : forall D Φ Φx, body_xp Θm Ξm D Φ Φx -> body_shape Φx Φx -> ⊨ body_ctx Φx ++ D ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Ψ ++ D ⊨ᵐ H ≈ H /\
       forall n Rn, mdenote Θm Ξm (Ψ ++ D) (me_mem H n) Rn -> ds_is_mod Rn -> exists V, valid_sel (Ψ ++ D) H n V) ->
    forall RD ρ, EF D ≈ D ∈ per_ctx_env ↘ RD -> RD ρ ρ -> forall Φk, kbody gc_deps gc_stack ρ Φ Φk -> body_eq_upto_types Φk Φx ->
    forall y Φx' pv Δy Dy, gm_prefix_upto Φx y = Some (gm_ext Φx' y (ge_mod pv (gu_mk Δy Dy))) ->
    exists ρ' r, ⟦ Φx' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' /\ ⟦ Δy ⊢ Dy ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ' ↘ r /\
      forall ρh Φh Φhk, per_body ρh Φh ρ Φ -> kbody gc_deps gc_stack ρh Φh Φhk ->
        exists Φhk' pvh Δh Dh ρh' rh, gm_prefix_upto Φhk y = Some (gm_ext Φhk' y (ge_mod pvh (gu_mk Δh Dh))) /\
          ⟦ Φhk' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρh ↘ ρh' /\ ⟦ Δh ⊢ Dh ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρh' ↘ rh /\ per_dmod rh r.
Proof.
  intros D Φ Φx Hx; induction Hx as [Γ | Γ Φ Φx y0 E Hx IH | Γ Φ Φx H its R Rm gs Hx IH HR HRm Hg Hok];
    intros Hsx HC Ho RD ρ HRD Hρ Φk Hkb Hkx y Φx' pv Δy Dy Hp.
  - discriminate.
  - inversion Hkb as [| ? ? Φk0 ? ? Hkb0 |]; subst.
    destruct Hkx as (Hkx0 & _ & _).
    cbn [body_shape] in Hsx; destruct Hsx as (Hsx0 & _ & HsE).
    cbn [body_opens gm_dropn] in Ho.
    pose proof (body_xp_nopens _ _ _ _ _ Hx) as Hn.
    cbn [gm_prefix_upto] in Hp; destruct (String.eqb y y0) eqn:Exy.
    + (* the module itself *)
      apply String.eqb_eq in Exy; subst y0; injection Hp as <- ->.
      cbn [body_ctx app] in HC.
      pose proof (rel_ctx_wf_tail HC) as HC0.
      pose proof (rel_ctx_wf_mod_inv HC) as HU.
      destruct (rel_ctx_wf_per_ctx_env HC0) as [R1 HR1].
      destruct (benv_exists _ _ Hn (proj1 (body_shape_fill _ _ Hn Hsx0)) HC0 _ _ HRD HR1 _ Hρ) as (ρ1 & Hb1 & Hρ1).
      destruct (rel_modexp_at _ _ _ _ _ (ruu_lit _ _ _ HU) HR1 _ _ Hρ1) as (r & _ & Hr & _ & _).
      apply eval_me_lit_iff in Hr.
      exists ρ1, r; split; [ exact Hb1 | split; [ exact Hr |] ].
      intros ρh Φh Φhk Hbh Hkh.
      inversion Hbh as [| | ? Φh0 ? ? Φxh Φx2 ρh1 ρ2 Δh Dh hh Δ2 D2 h2 ? pmh ? Hbh0 Hkh0 Hk0 Hbh1 Hb2 Hch Hc2 Hhh |]; subst.
      pose proof (kbody_functional _ _ _ _ Hk0 Hkb0) as ->.
      apply (body_eq_upto_types_benv _ _ Hkx0) in Hb2; pose proof (functional_eval_benv _ _ _ _ Hb2 Hb1) as ->.
      pose proof (functional_eval_close _ _ _ _ _ Hc2 Hr) as ->.
      inversion Hkh as [| ? ? Φhk0 ? ? Hkh1 |]; subst.
      pose proof (kbody_functional _ _ _ _ Hkh1 Hkh0) as ->.
      exists Φxh, pmh, Δh, Dh, ρh1, hh; split; [ cbn; rewrite String.eqb_refl; reflexivity |].
      split; [ exact Hbh1 | split; [ exact Hch | exact Hhh ] ].
    + (* an entry before it *)
      assert (HC0 : ⊨ body_ctx Φx ++ Γ) by (destruct E as [? ? ? [] | | | |]; cbn in HsE; try contradiction; exact (rel_ctx_wf_tail HC)).
      destruct (IH Hsx0 HC0 Ho _ _ HRD Hρ _ Hkb0 Hkx0 _ _ _ _ _ Hp) as (ρ' & r & Hb & Hr & Hh).
      exists ρ', r; split; [ exact Hb | split; [ exact Hr |] ].
      intros ρh Φh Φhk Hbh Hkh.
      assert (Hrest : exists Φh0 Eh, Φh = gm_ext Φh0 y0 Eh /\ per_body ρh Φh0 ρ Φ)
        by (inversion Hbh; subst; eauto).
      destruct Hrest as (Φh0 & Eh & -> & Hbh0).
      inversion Hkh as [| ? ? Φhk0 ? ? Hkh0 |]; subst.
      destruct (Hh _ _ _ Hbh0 Hkh0) as (Φhk' & pvh & Δh & Dh & ρh' & rh & Hph & Hbh' & Hrh & Hrr).
      exists Φhk', pvh, Δh, Dh, ρh', rh; split; [ cbn; rewrite Exy; exact Hph | split; [ exact Hbh' | split; assumption ] ].
  - (* an open *)
    pose proof (items_gen_length _ _ _ _ _ _ _ Hg) as Hl.
    assert (Eo : body_opens (gm_open Φ H its) (gens_append Φx 0 gs) = (body_ctx Φx, H) :: body_opens Φ Φx).
    { cbn [body_opens]; rewrite <- Hl, gm_dropn_gens_append; reflexivity. }
    rewrite Eo in Ho.
    pose proof (body_shape_gens_l _ _ _ Hsx) as Hsx0.
    pose proof HC as HC'.
    rewrite gens_body_ctx_base, <- app_assoc in HC.
    pose proof (rel_ctx_wf_app_r _ _ HC) as HC0.
    pose proof (body_xp_nopens _ _ _ _ _ Hx) as Hn.
    inversion Hkb as [| | ? ? Φk0 σ1 ? ? gsk Hkb0 Hke Hkg]; subst.
    assert (Hlk : List.length gsk = List.length gs).
    { pose proof (f_equal (@List.length _) (kgens_names _ _ _ _ _ _ Hkg)) as E1.
      pose proof (f_equal (@List.length _) (items_gen_names _ _ _ _ _ _ _ Hg)) as E2.
      rewrite !length_map in E1, E2; lia. }
    pose proof (body_eq_upto_types_gens_inv _ _ _ _ _ Hlk Hkx) as Hkx0.
    destruct (items_upto y its) as [[its1 it] |] eqn:Eu.
    + (* generated by this open *)
      destruct (gens_prefix_some _ _ _ _ _ _ _ Hg _ _ _ Eu) as (its0 & gs0 & g & -> & Hg0 & Hg1 & (Rits & Rg & -> & ->) & Hpx).
      rewrite Hpx, gens_append_snoc in Hp; injection Hp as <- Hd HE.
      pose proof (items_gen_length _ _ _ _ _ _ _ Hg0) as Hl0.
      (* the target, before the open's entries *)
      destruct (Ho 0 _ _ eq_refl) as [HH HS].
      destruct (rel_ctx_wf_per_ctx_env HC0) as [Ro HRo].
      destruct (benv_exists _ _ Hn (proj1 (body_shape_fill _ _ Hn Hsx0)) HC0 _ _ HRD HRo _ Hρ) as (ρo & Hbo & Hρo).
      destruct (rel_modexp_at _ _ _ _ _ HH HRo _ _ Hρo) as (t & _ & Ht & _ & _).
      (* the environment after the entries before it *)
      assert (HnP : gm_nopens (gens_append Φx 0 gs0) = 0) by (rewrite gens_append_nopens; exact Hn).
      assert (HshP : body_shape (gens_append Φx 0 gs0) (gens_append Φx 0 gs0)).
      { apply (body_shape_gens_l (g :: Rg) _ (0 + List.length gs0)).
        rewrite <- gens_append_app; exact Hsx. }
      assert (HCP : ⊨ body_ctx (gens_append Φx 0 gs0) ++ Γ).
      { destruct (body_ctx_gens_firstn (gs0 ++ g :: Rg) Φx 0 (List.length gs0)) as (X & HX).
        rewrite firstn_app, Nat.sub_diag, firstn_all in HX; cbn [firstn] in HX; rewrite app_nil_r in HX.
        rewrite HX, <- app_assoc in HC'; exact (rel_ctx_wf_app_r _ _ HC'). }
      destruct (rel_ctx_wf_per_ctx_env HCP) as [RP HRP].
      destruct (benv_exists _ _ HnP (proj1 (body_shape_fill _ _ HnP HshP)) HCP _ _ HRD HRP _ Hρ) as (ρ' & Hb' & Hρ').
      pose proof Hb' as Hb''; apply eval_gens_split in Hb'' as (ρo' & Hbo' & Hbg).
      pose proof (functional_eval_benv _ _ _ _ Hbo' Hbo) as ->.
      pose proof (skipn_benv_gens _ _ _ Hbg) as Hskip.
      assert (HlX : List.length (body_ctx (gens_append gm_nil 0 gs0)) = List.length gs0) by apply gens_body_ctx_length.
      rewrite <- HlX in Hskip.
      rewrite gens_body_ctx_base, <- app_assoc in HRP, HCP.
      destruct (wk_coh_ex _ _ _ _ _ _ HH HCP HRP Hρ' Hskip) as (hj & Hhj).
      pose proof (wk_coh _ _ _ _ _ _ _ _ HH HCP HRP Hρ' Hskip Ht Hhj) as Hhjt.
      rewrite HlX in Hhj.
      (* a related body's open, and the entry of the same name it generates *)
      clear IH Ho HC HC' Eo Hsx HshP HnP HR HRm Hok Hbo' Hsx0 HC0 HRD Hρ Hkb Hx Hn.
      (* a related body's open: its target, related to ours, and the entry it generates of the name, read
         again past the entries before it *)
      assert (Hrel : forall ρh Φh Φhk, per_body ρh Φh ρ (gm_open Φ H ((its0 ++ it :: nil) ++ Rits)) ->
                 kbody gc_deps gc_stack ρh Φh Φhk ->
        exists H' σh1 Φxh ρh1 hh gsh0 gh Rgh ρq hhj,
          Φhk = gens_append Φxh 0 (gsh0 ++ gh :: Rgh) /\
          gm_prefix_upto Φhk y = Some (gens_append Φxh 0 (gsh0 ++ gh :: nil)) /\
          List.length gsh0 = List.length gs0 /\
          kgens gc_deps gc_stack σh1 H' (it :: nil) (gh :: nil) /\
          ⟦ Φxh ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρh ↘ ρh1 /\ kenv gc_deps gc_stack ρh Φxh σh1 /\
          ⟦ H' ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρh1 ↘ hh /\ per_dmod hh t /\
          ⟦ gens_append Φxh 0 gsh0 ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρh ↘ ρq /\
          ⟦ modexp_wk H' (wk_shiftn (List.length gsh0)) ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρq ↘ hhj /\ per_dmod hhj hh).
      { intros ρh Φh Φhk Hbh Hkh.
        clear Hpx Hg Hg0 Hg1 HS HH HE Hd.
        inversion Hbh; subst.
        pose proof (kbody_functional _ _ _ _ H6 Hkb0) as ->.
        apply (body_eq_upto_types_benv _ _ Hkx0) in H8; pose proof (functional_eval_benv _ _ _ _ H8 Hbo) as ->.
        pose proof (functional_eval_modexp _ _ _ _ H10 Ht) as ->.
        pose proof (kbody_functional _ _ _ _ H12 Hkh) as ->.
        inversion Hkh as [| | ? ? Φhk0 σh1 ? ? gshk Hkh1 Hkhe Hkhg]; subst.
        pose proof (kbody_functional _ _ _ _ Hkh1 H5) as ->.
        destruct (kgens_prefix_at _ _ _ _ _ _ Hkhg _ _ _ Eu) as (gsh0 & gh & Rgh & -> & Hlh & Hkg1 & Hph).
        apply eval_gens_split in H14 as (ρh1' & Hbh1' & Hbhg).
        pose proof (functional_eval_benv _ _ _ _ Hbh1' H7) as ->.
        rewrite gens_append_app in Hbhg; apply eval_gens_split in Hbhg as (ρq & Hbq & _).
        assert (Hbq' : ⟦ gens_append Φx0 0 gsh0 ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρh ↘ ρq) by (apply eval_gens_split; exists ρ1; split; assumption).
        assert (Hlh2 : List.length (gsh0 ++ gh :: Rgh) = List.length ((its0 ++ it :: nil) ++ Rits))
          by (pose proof (f_equal (@List.length _) (kgens_names _ _ _ _ _ _ Hkhg)) as E; rewrite !length_map in E; exact E).
        rewrite length_app in Hlh; cbn in Hlh.
        assert (Hj : List.length gsh0 < List.length ((its0 ++ it :: nil) ++ Rits)) by (rewrite !length_app; cbn; lia).
        assert (Hdq : ⟦ gm_dropn (List.length ((its0 ++ it :: nil) ++ Rits) - List.length gsh0)
                         (gens_append Φx0 0 (gsh0 ++ gh :: Rgh)) ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρh ↘ ρq).
        { rewrite gm_dropn_gens by lia.
          replace (List.length (gsh0 ++ gh :: Rgh) - _) with (List.length gsh0) by lia.
          rewrite firstn_app, Nat.sub_diag, firstn_all; cbn [firstn]; rewrite app_nil_r; exact Hbq'. }
        destruct (H16 _ _ Hj Hdq) as (hhj & Hhhj).
        pose proof (H21 _ _ _ Hj Hdq Hhhj) as Hhth.
        exists H0, σh1, Φx0, ρ1, h, gsh0, gh, Rgh, ρq, hhj.
        repeat split; try assumption; [ apply Hph | lia ]. }
      clear Hg Hg0.
      inversion Hg1 as [| ? ? ? d pv0 ? ? Hg2 | ? ? ? n d pv0 A_n om ? ? HmH Hg2 | ? ? ? n d pv0 Rn ? ? HmH HRn Hg2 |]; subst;
        cbn [ig_entry snd gentry_wk ig_name fst] in HE, Eu, Hpx |- *; try discriminate;
        injection HE as <- <- <-.
      * (* the target itself *)
        exists ρ', hj; split; [ exact Hb' |]; split; [ apply eval_close_alias0; exact Hhj |].
        intros ρh Φh Φhk Hbh Hkh.
        destruct (Hrel _ _ _ Hbh Hkh)
          as (H' & σh1 & Φxh & ρh1 & hh & gsh0 & gh & Rgh & ρq & hhj & -> & Hph & Hlg & Hkg1 & Hbh1 & Hkhe & Hhh & Hht & Hbq & Hhhj & Hhjh).
        inversion Hkg1 as [| ? ? ? ? ? ? Hk2 | |]; subst.
        rewrite gens_append_snoc in Hph; cbn [ig_entry ig_name snd gentry_wk] in Hph.
        exists (gens_append Φxh 0 gsh0), pv0, nil, (md_alias (modexp_wk H' (wk_shiftn (List.length gsh0)))), ρq, hhj.
        split; [ exact Hph |]; split; [ exact Hbq |]; split; [ apply eval_close_alias0; exact Hhhj |].
        eapply per_dmod_trans; [ exact Hhjh |]; eapply per_dmod_trans; [ exact Hht | apply per_dmod_sym; exact Hhjt ].
      * (* the target's submodule *)
        destruct (HS _ _ HmH HRn) as (V & Hsm).
        destruct (Hsm _ HRo _ Hρo) as [k0 v Hk0 Hv Hsel].
        pose proof (functional_eval_modexp _ _ _ _ Hk0 Ht) as ->.
        destruct (Hsel _ Hhjt) as (r2 & Hr2 & Hr2v).
        exists ρ', r2; split; [ exact Hb' |]; split; [ apply eval_close_alias0; econstructor; [ exact Hhj | exact Hr2 ] |].
        (* the member is a module on our side *)
        destruct (kgens_prefix_at _ _ _ _ _ _ Hkg _ _ _ Eu) as (gsk0 & gk & Rgk & -> & Hlk0 & Hkgk & Hpk).
        destruct (body_eq_upto_types_prefix _ _ Hkx d _ _ ltac:(rewrite Hpx, gens_append_snoc; reflexivity)) as (Φk' & Ek & Hpk' & _ & HEx).
        rewrite Hpk, gens_append_snoc in Hpk'; injection Hpk' as _ _ HEk.
        assert (Hsk : skind gc_deps gc_stack σ1 H (n :: nil) mk_mod).
        { subst Ek.
          inversion Hkgk as [| | ? ? ? ? ? ? ? Hsk Hk2 | ? ? ? ? ? ? ? Hsk Hk2]; subst; [| exact Hsk ].
          exfalso; cbn [ig_entry snd gentry_wk] in HEx.
          destruct HEx as [HEx | (? & ? & ? & ? & ? & _ & HEx)]; discriminate. }
        assert (Hkt : dkind gc_deps gc_stack t (n :: nil) mk_mod)
          by exact (open_kind _ _ _ _ _ _ _ _ (proj2 (body_eq_upto_types_benv _ _ Hkx0 _ _) Hbo) Hke Ht Hsk).
        intros ρh Φh Φhk Hbh Hkh.
        destruct (Hrel _ _ _ Hbh Hkh)
          as (H' & σh1 & Φxh & ρh1 & hh & gsh0 & gh & Rgh & ρq & hhj & -> & Hph & Hlg & Hkg1 & Hbh1 & Hkhe & Hhh & Hht & Hbq & Hhhj & Hhjh).
        inversion Hkg1 as [| | ? ? ? ? ? ? ? Hsk' Hk2 | ? ? ? ? ? ? ? Hsk' Hk2]; subst.
        { exfalso.
          pose proof (open_kind _ _ _ _ _ _ _ _ Hbh1 Hkhe Hhh Hsk') as Hkm.
          pose proof (per_dmod_kequiv _ _ Hht) as Hkq.
          assert (Hkm' : dkind gc_deps gc_stack hh (n :: nil) mk_mod) by (apply Hkq; exact Hkt).
          pose proof (proj1 (@functional_kind gc_deps gc_stack) _ _ _ Hkm _ Hkm') as Hc; discriminate. }
        destruct (Hsel _ (per_dmod_trans _ _ _ Hhjh Hht)) as (r1 & Hr1 & Hr1v).
        rewrite gens_append_snoc in Hph; cbn [ig_entry ig_name snd gentry_wk] in Hph.
        eexists (gens_append Φxh 0 gsh0), pv0, nil, _, ρq, r1.
        split; [ exact Hph |]; split; [ exact Hbq |]; split; [ apply eval_close_alias0; econstructor; [ exact Hhhj | exact Hr1 ] |].
        eapply per_dmod_trans; [ exact Hr1v | apply per_dmod_sym; exact Hr2v ].
    + (* an entry before the open *)
      rewrite (gens_prefix_none_items _ _ _ _ _ _ _ _ _ _ Hg Eu) in Hp.
      destruct (IH Hsx0 HC0 (fun k => Ho (S k)) _ _ HRD Hρ _ Hkb0 Hkx0 _ _ _ _ _ Hp) as (ρ' & r & Hb & Hr & Hh).
      exists ρ', r; split; [ exact Hb | split; [ exact Hr |] ].
      intros ρh Φh Φhk Hbh Hkh.
      inversion Hbh; subst.
      inversion Hkh as [| | ? ? Φhk0 σh1 ? ? gshk Hkh1 Hkhe Hkhg]; subst.
      match goal with Hb0 : per_body ρh ?Φh0 ρ Φ |- _ =>
        destruct (Hh _ _ _ Hb0 Hkh1) as (Φhk' & pvh & Δh & Dh & ρh' & rh & Hph & Hbh' & Hrh & Hrr) end.
      exists Φhk', pvh, Δh, Dh, ρh', rh.
      split; [ rewrite (kgens_prefix_none_items _ _ _ _ _ _ _ _ _ Hkhg Eu); exact Hph | split; [ exact Hbh' | split; assumption ] ].
Qed.

End Desc.

Section Valid.
  Variables (Θm : gdeps) (Ξm : gstack).
  Hypothesis Hgm : ⊢ᵍ Θm ⍮ Ξm.
  Hypothesis Hsub : gc_sub Θm Ξm gc_deps gc_stack.
  Hypothesis Hgf : valid_filed_mods Θm Ξm.

  #[local] Abbreviation valid_unit := (valid_unit Θm Ξm).
  #[local] Abbreviation valid_modexp := (valid_modexp Θm Ξm).

(** A submodule of a well-formed module expression is well formed, and the
    unit of its module part well formed and denoting it. *)
Lemma mem_unit_wf : forall Γ H y R Rm, Θm ⍮ Ξm ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θm Ξm Γ (me_mem H y) R -> ds_mod Θm Ξm R = Some Rm ->
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_mem H y ≈ me_mem H y /\ Θm ⍮ Ξm ⍮ Γ ⊢ᵐ ds_unit Rm ≈ ds_unit Rm /\
    exists RK, mdenote Θm Ξm Γ (ds_unit Rm) RK /\ ds_mod Θm Ξm RK = Some Rm.
Proof.
  intros * HwH Hm Hmd.
  pose proof (mem_desc_ok _ _ _ _ _ _ _ (gctx_valid_syn _ _ Hgm) HwH Hm) as Hdok.
  pose proof (desc_ok_mod _ _ Hgm _ _ _ Hdok Hmd) as Hdokm.
  pose proof (ds_mod_is_mod _ _ _ _ Hmd) as Him.
  destruct (desc_ok_tele _ _ _ _ Hdokm Him) as (T' & HT').
  assert (Hmt : ds_mtele Θm Ξm R = Some T') by (unfold ds_mtele; rewrite Hmd; exact HT').
  assert (HwHy : Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_mem H y ≈ me_mem H y)
    by (eapply wf_me_mem; [ exact HwH | exact Hm | exact Hmt | exact Hm | exact Hmt ]).
  pose proof (ds_canon_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hgm Hm) Hmd) as Hc.
  split; [ exact HwHy |]; split; [ exact (proj1 (ds_unit_wf _ _ _ _ (presup_modexp_eq_ctx HwH) Hdokm Hc Him)) |].
  exact (ds_unit_denote _ _ _ Hgm Hc Him Γ (wf_mdenote_mod_xp _ _ _ _ _ _ _ HwHy Hm Hmd)).
Qed.

(** A submodule of a unit lacking parameters, given one of the unit with
    them, valid. *)
Lemma sel_finish : forall Γ Δ D y X, tele_ass Δ -> ⊨ Δ ++ Γ -> ⊨ Γ -> ds_is_mod X -> valid_unit (Δ ++ Γ) (ds_unit X) ->
    (forall R, EF Δ ++ Γ ≈ Δ ++ Γ ∈ per_ctx_env ↘ R -> forall ρ ρ', R ρ ρ' ->
       exists k0 v0, ⟦ nil ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ k0 /\ ⟦ ds_unit X ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ' ↘ v0 /\ dmod_has_sel y k0 v0) ->
    valid_sel Γ (me_lit (gu_mk Δ D)) y (ds_unit (ds_up Δ X)) /\ valid_unit Γ (ds_unit (ds_up Δ X)).
Proof.
  intros * HΔ HC HΓ Hm HK Hbase.
  destruct (rel_ctx_wf_per_ctx_env HΓ) as [RΓ HRΓ].
  assert (HS : valid_sel Γ (me_lit (gu_mk Δ D)) y (me_lit (gu_mk Δ (md_alias (ds_unit X))))).
  { intros R HR ρ Hρ.
    assert (E : R <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    destruct (sel_walk _ _ _ _ _ _ HΔ HC HRΓ Hbase _ _ (proj1 (E _ _) Hρ)) as (k & v & Hk & Hv & Hs).
    apply (mk_valid_sel_at _ _ _ _ k v); [ apply eval_me_lit_iff; exact Hk | apply eval_me_lit_iff; exact Hv | exact Hs ]. }
  destruct Δ as [| e Δ0].
  - rewrite ds_up_nil; cbn [List.app] in *.
    split; [| exact HK ].
    exact (valid_sel_resp_r _ _ _ _ _ HS (rel_modexp_under_ctx_beta_alias0 _ _ (valid_unit_rel _ _ Hgf _ _ HK))).
  - destruct (rel_alias_unit_up _ _ Hgm Hgf Γ (e :: Δ0) X ltac:(discriminate) HΔ Hm HK) as [Hup HKup].
    split; [ exact (valid_sel_resp_r _ _ _ _ _ HS Hup) | exact HKup ].
Qed.

(** A module of a valid body with no parameters, at an environment, against
    the unit of its module part, filled in, at a related one. *)
Lemma body_sel_base : forall D Φ Φx y Φ' pv U σ RU, body_xp Θm Ξm D Φ Φx -> body_shape Φx Φx -> ⊨ body_ctx Φx ++ D ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> kinds_ok Θm Ξm (Ψ ++ D) H) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Ψ ++ D ⊨ᵐ H ≈ H /\
       forall n Rn, mdenote Θm Ξm (Ψ ++ D) (me_mem H n) Rn -> ds_is_mod Rn -> exists V, valid_sel (Ψ ++ D) H n V) ->
    gm_prefix_upto Φx y = Some (gm_ext Φ' y (ge_mod pv U)) -> gm_fill Φ' = Some σ ->
    udenote Θm Ξm (body_ctx Φ' ++ D) None U RU -> valid_unit (body_ctx Φ' ++ D) (me_lit U) ->
    valid_unit D (ds_unit (ds_sub RU σ)) /\
    forall R, EF D ≈ D ∈ per_ctx_env ↘ R -> forall ρ ρ', R ρ ρ' ->
      exists k0 v0, ⟦ nil ⊢ md_body sm_open Φ ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ k0 /\
        ⟦ ds_unit (ds_sub RU σ) ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ' ↘ v0 /\ dmod_has_sel y k0 v0.
Proof.
  intros * Hx Hsx HC Hopk Hopm Hp Hf Hu HK.
  pose proof (body_xp_nopens _ _ _ _ _ Hx) as Hn.
  pose proof (prefix_nopens _ _ _ Hn Hp) as Hn'; cbn in Hn'.
  destruct (prefix_body_ctx _ _ _ Hn Hp) as [Ψ HΨ]; cbn [body_ctx] in HΨ.
  pose proof HC as HC1; rewrite HΨ, <- app_assoc in HC1; cbn [List.app] in HC1.
  pose proof (rel_ctx_wf_tail (rel_ctx_wf_app_r _ _ HC1)) as HC0.
  destruct (proj1 (valid_unit_canon_all _ _ Hgm Hgf) _ _ HK _ _ (dn_lit _ _ _ _ _ Hu) (ds_is_mod_mod _ _ _ (udenote_is_mod _ _ _ _ _ _ Hu)))
    as [HKu HKK].
  pose proof (fill_gsub _ _ _ Hn' Hf HC0) as Hg.
  pose proof (wf_gm_fill _ _ _ _ _ (presup_modexp_eq_ctx (valid_unit_wf _ _ _ _ HK)) Hf) as Hwσ.
  pose proof (valid_unit_gsub Hgw _ _ Hgm Hsub _ _ _ _ HKK Hg Hwσ) as HKX; rewrite <- ds_unit_sub in HKX.
  split; [ exact HKX |].
  intros R HR ρ ρ' Hρ.
  assert (HP : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρρ : R ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  destruct (kbody_exists _ _ _ _ _ Hx Hsx HC Hopk _ _ _ HR Hρρ (kshape_refl _ _ ρ)) as (Φk & Hkb & Hkx).
  destruct U as [Δy Dy].
  destruct (body_sel_mod _ _ _ _ _ Hx Hsx HC Hopm _ _ HR Hρρ _ Hkb Hkx _ _ _ _ _ Hp) as (ρ1 & r & Hb1 & Hr & Hh).
  destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0].
  assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
  destruct (fill_rel _ _ _ Hn' Hf HC0 _ _ HR HR0 _ Hρρ) as (ρσ & ρ1' & Hσ & Hb1' & H01).
  pose proof (functional_eval_benv _ _ _ _ Hb1' Hb1) as ->.
  destruct (rel_modexp_at _ _ _ _ _ HKu HR0 _ _ (symmetry H01)) as (a & b & Ha & Hb & Hab).
  apply eval_me_lit_iff in Ha; pose proof (functional_eval_close _ _ _ _ _ Ha Hr) as ->.
  destruct (valid_mod_inst _ _ _ _ _ (valid_unit_rel _ _ Hgf _ _ HKK) (gsub_valid Hg) HR _ _ Hρρ Hσ) as (h1 & h2 & Hh1 & Hh2 & H12).
  pose proof (functional_eval_modexp _ _ _ _ Hh2 Hb) as ->.
  destruct (rel_modexp_at _ _ _ _ _ (valid_unit_rel _ _ Hgf _ _ HKX) HR _ _ Hρ) as (c & v0 & Hc & Hv0 & Hcv).
  rewrite <- ds_unit_sub in Hh1; pose proof (functional_eval_modexp _ _ _ _ Hh1 Hc) as ->.
  exists (dm_local nil (md_body sm_open Φ) ρ), v0; split; [ apply eval_close_body | split; [ exact Hv0 |] ].
  intros h Hhk.
  inversion Hhk as [| ? ? ? ? ? ? Hbh | ? ? ? ? ? Rf Hpf Hpf' _ _ _ _]; subst;
    [| exfalso; exact (nextparam_body_nil _ _ _ _ Hpf') ].
  destruct (per_body_kbody_l _ _ _ _ Hbh) as (Φhk & Hkh).
  destruct (Hh _ _ _ Hbh Hkh) as (Φhk' & pvh & Δh & Dh & ρh' & rh & Hph & Hbh' & Hrh & Hrr).
  exists rh; split; [ eapply eval_selm_body; eassumption |].
  eapply per_dmod_trans; [ exact Hrr |]; eapply per_dmod_trans; [ exact Hab |].
  eapply per_dmod_trans; [ apply per_dmod_sym; exact H12 | exact Hcv ].
Qed.

(** ** Submodules of Filed Modules *)

Lemma gc_loc_sub : forall pq T Φ, gc_loc Θm Ξm pq = Some (T, Φ) -> exists TΦ, gc_loc gc_deps gc_stack pq = Some TΦ.
Proof.
  intros * Hl; apply gc_loc_loc in Hl as [Hf | Hb].
  - destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hsub Hf) as (Φ' & [[Hf' _] | [Hb' _]]);
      eexists; apply (gc_loc_of_loc _ _ Hgw); [ left; exact Hf' | right; exact Hb' ].
  - destruct (gc_sub_body _ _ _ _ _ _ _ Hsub Hb) as (Φ' & Hb' & _).
    eexists; apply (gc_loc_of_loc _ _ Hgw); right; exact Hb'.
Qed.

(** A body submodule of a filed module at arguments: filed at its path, at
    the arguments. *)
Lemma filed_body_sel : forall Γ p T Φ Ns y Tq Φq, gc_loc Θm Ξm p = Some (T, Φ) ->
    gc_loc Θm Ξm (qname_in p y) = Some (Tq, Φq) -> ⊨ Γ -> valid_args Γ T Ns ->
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_apps (qname_mod (qname_in p y)) Ns ≈ me_apps (qname_mod (qname_in p y)) Ns ->
    valid_sel Γ (me_apps (qname_mod p) Ns) y (me_apps (qname_mod (qname_in p y)) Ns) /\
    valid_unit Γ (me_apps (qname_mod (qname_in p y)) Ns).
Proof.
  intros * Hgl Hglq HΓ Hs Hw.
  destruct (Hgf _ _ _ Hgl) as [(Φd & Hm) _ HT HTa _ _ _ _ _ _ _].
  destruct (Hgf _ _ _ Hglq) as [(Φdq & Hmq) _ HTq HTaq _ _ _ _ _ _ _].
  destruct (loc_child_tele _ _ Hgw _ _ _ _ _ _ Hm Hmq) as (Δ' & -> & _).
  destruct (gc_loc_sub _ _ _ Hglq) as (TΦ & Hglt).
  pose proof Hs as [T1 T2 HT12 Hlen HTa2 HTs2 HNs].
  assert (Hs' : valid_args Γ (Δ' ++ T) Ns)
    by (apply (mk_valid_args _ _ _ (Δ' ++ T1) T2); [ rewrite HT12, app_assoc; reflexivity | assumption .. ]).
  split; [| eapply valid_unit_filed; [ exact Hw | exact Hglq | exact HΓ | exact Hs' ] ].
  intros R HR ρ Hρ.
  destruct (valid_args_gargs _ _ _ _ HT HΓ Hs HR _ _ Hρ) as (ns & ns' & Hns & Hns' & Hgs).
  apply (mk_valid_sel_at _ _ _ _ (dm_global p ns) (dm_global (qname_in p y) ns'));
    [ exact (eval_apps_filed _ _ Hgf _ _ _ _ _ _ Hgl Hns) | exact (eval_apps_filed _ _ Hgf _ _ _ _ _ _ Hglq Hns') |].
  assert (Hle : List.length ns <= List.length T)
    by (rewrite (eval_exps_length _ _ _ Hns), HT12, length_app; lia).
  refine (global_sel p T Φd y (fun ns w => w = dm_global (qname_in p y) ns) Hm HTa HT _ _ _ ns ns' _ Hle Hgs eq_refl).
  - intros ns0 ns1 w Hl0 Hg0 ->.
    exists (dm_global (qname_in p y) ns0); split; [ rewrite qname_in_app in Hglt |- *; eapply eval_selm_global; exact Hglt |].
    eapply gval_rel; [ exact Hmq | exact HTaq | exact HTq | reflexivity | rewrite length_app; lia | ].
    exact (per_gargs_rev_app _ _ _ _ Hg0 Hl0).
  - intros ns0 w a Hlt -> Hnp.
    inversion Hnp; subst.
    match goal with Hm0 : gc_loc _ _ p = Some _ |- _ => rewrite Hm in Hm0; injection Hm0 as <- <- end.
    econstructor; [ exact Hmq | rewrite nth_rev_app_lt by exact Hlt; eassumption | eassumption ].
  - intros ns0 ns1 c c' w _ _ ->.
    exists (dm_global (qname_in p y) (ns1 ++ c' :: nil)); split; [ constructor | reflexivity ].
Qed.

(** A closed alias valid in the empty context, closed at the empty
    environment and at any, given arguments related at its telescope. *)
Lemma alias_apps_rel : forall Ta Ea ρ0 ns ns', tele_ass Ta ->
    ⋅ ⊨ᵐ me_lit (gu_mk Ta (md_alias Ea)) ≈ me_lit (gu_mk Ta (md_alias Ea)) ->
    List.length ns <= List.length Ta -> per_gargs (rev Ta) nil nil ns ns' ->
    exists h0 h1 w w', ⟦ Ta ⊢ md_alias Ea ⟧ᶜ gc_deps ⍮ gc_stack ⍮ nil ↘ h0 /\ ⟦ Ta ⊢ md_alias Ea ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ0 ↘ h1 /\
      $ᵐ*| h0 & ns | gc_deps ⍮ gc_stack ↘ w /\ $ᵐ*| h1 & ns' | gc_deps ⍮ gc_stack ↘ w' /\ per_dmod w w'.
Proof.
  intros * HTa HV Hl Hg.
  destruct (rel_modexp_at _ _ _ _ _ HV per_ctx_env_nil_true nil ρ0 I) as (h0 & h1 & Hh0 & Hh1 & H01).
  apply eval_me_lit_iff in Hh0, Hh1.
  destruct Ta as [| e Ta0].
  - destruct ns; [| cbn in Hl; lia ].
    pose proof (per_gargs_len_eq _ _ _ _ _ Hg) as Hl'; destruct ns'; [| discriminate ].
    exists h0, h1, h0, h1; repeat split; try assumption; constructor.
  - assert (Hlt : 0 < List.length (e :: Ta0)) by (cbn; lia).
    pose proof (functional_eval_close _ _ _ _ _ Hh0 (close_unsat _ _ _ Hlt)) as ->.
    pose proof (functional_eval_close _ _ _ _ _ Hh1 (close_unsat _ _ _ Hlt)) as ->.
    destruct (closure_gargs _ _ _ _ _ _ _ HTa Hl H01 Hg) as (w & w' & Hw & Hw' & Hww).
    exists (dm_local (e :: Ta0) (md_alias Ea) nil), (dm_local (e :: Ta0) (md_alias Ea) ρ0), w, w'.
    repeat split; try assumption; apply close_unsat; exact Hlt.
Qed.

(** An alias submodule of a filed module at arguments: the stored unit at
    the arguments. *)
Lemma filed_alias_sel : forall Γ p T Φ Ns y Φ0 E Ua, gc_loc Θm Ξm p = Some (T, Φ) ->
    gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_alias_unit E = Some Ua -> ⊨ Γ -> valid_args Γ T Ns ->
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns ->
    valid_sel Γ (me_apps (qname_mod p) Ns) y (me_apps (me_lit Ua) Ns) /\ valid_modexp Γ (me_apps (me_lit Ua) Ns).
Proof.
  intros * Hgl Hp HUa HΓ Hs Hw.
  destruct (Hgf _ _ _ Hgl) as [(Φd & Hm) _ HT HTa HTs _ _ _ _ _ Hals].
  destruct (Hals _ _ _ _ Hp HUa) as (HmUa & HsUa).
  assert (HUa' : exists Ta Ea, Ua = gu_mk Ta (md_alias Ea))
    by (destruct E as [| pv [Ta [| Ea]] | | pv Δa pq Nsa |]; cbn in HUa; try discriminate; injection HUa as <-; eauto).
  destruct HUa' as (Ta & Ea & ->).
  destruct (loc_alias_params _ _ Hgw _ _ _ _ _ Hm HmUa) as (Δ0 & HTa' & HaΔ0); cbn [gu_params] in HTa'; subst Ta.
  pose proof (presup_modexp_eq_ctx Hw) as HwΓ.
  pose proof (HsUa _ HΓ HwΓ) as HKUa.
  pose proof (HsUa _ rel_ctx_wf_nil (wf_ctx_empty _ _ Hgm)) as HKUa0.
  pose proof (valid_unit_rel _ _ Hgf _ _ HKUa0) as HV0.
  pose proof Hs as [T1 T2 HT12 Hlen HTa2 HTs2 HNs].
  assert (HaT : tele_ass (Δ0 ++ T)) by (apply List.Forall_app; split; assumption).
  (* the unit at the arguments is valid in what it denotes *)
  pose proof (valid_unit_wf _ _ _ _ HKUa) as HwUa.
  pose proof (proj1 (modexp_gen _ _ _ _ _ HwUa)) as HfUa; cbn [gen_m unit_full] in HfUa.
  destruct HfUa as (HΔΓ & HaTa & HE'w).
  revert HT12.
  inversion HKUa as [| | ? ? ? Hw0 HΔ HΓ0 HΔΓs HU HE Hsm]; subst;
    [ exfalso; match goal with Hq : me_apps _ _ = me_lit _ |- _ => exact (me_apps_qname_not_lit _ _ _ Hq) end |].
  inversion Hsm as [? ? RE RmE ? ? _ HmE HmodE _ _ _ _]; subst.
  intros HT12.
  assert (Hu : udenote Θm Ξm Γ None (gu_mk (Δ0 ++ T) (md_alias Ea)) (ds_up (Δ0 ++ T) RmE)) by (eapply un_alias; eassumption).
  pose proof (desc_ok_mod _ _ Hgm _ _ _ (me_desc_ok _ _ _ _ _ _ HE'w HmE) HmodE) as HokR.
  assert (Hargs : args_ok Θm Ξm Γ T Ns).
  { destruct (filed_denote _ _ Hgm _ _ _ Γ Ns Hgl) as (RF & HmF & HmodF).
    pose proof (desc_ok_mod _ _ Hgm _ _ _ (me_desc_ok _ _ _ _ _ _ Hw HmF) HmodF) as HdK.
    inversion HdK; subst; cbn [List.app] in *; assumption. }
  pose proof (args_ok_ext _ _ _ _ _ Δ0 Hargs) as Hargs'.
  assert (HNv : forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts (Δ0 ++ T) Id Ns) k = Some A -> Γ ⊨ N : A).
  { intros k N A HN HA; rewrite HT12, app_assoc in HA.
    rewrite tele_insts_app_full in HA by (try exact HTa2; lia).
    exact (HNs _ _ _ HN HA). }
  assert (HsV : valid_modexp Γ (me_apps (me_lit (gu_mk (Δ0 ++ T) (md_alias Ea))) Ns)).
  { eapply (valid_modexp_apps_up Hgw _ _ Hgm Hsub Hgf); [ exact (valid_modexp_of_valid_unit _ _ Hgf _ _ HKUa) | exact HwUa | apply dn_lit; exact Hu
                                                | exact (ds_mod_is_mod _ _ _ _ HmodE) | exact HΔΓ | exact HaTa
                                                | exact (args_ok_length _ _ _ _ _ Hargs') | exact (args_ok_insts _ _ _ _ _ Hargs')
                                                | exact HNv | exact HokR ]. }
  split; [| exact HsV ].
  (* at every environment: the global's stored unit, given the arguments *)
  intros R HR ρ Hρ.
  destruct (valid_args_gargs _ _ _ _ HT HΓ Hs HR _ _ Hρ) as (ns & ns' & Hns & Hns' & Hgs).
  pose proof (functional_eval_exps _ _ _ _ Hns' Hns) as ->.
  assert (Hle : List.length ns <= List.length T)
    by (rewrite (eval_exps_length _ _ _ Hns), HT12, length_app; lia).
  assert (HgsA : forall xs xs', List.length xs <= List.length T -> per_gargs (rev T) nil nil xs xs' ->
            per_gargs (rev (Δ0 ++ T)) nil nil xs xs')
    by (intros xs xs' _ Hx; rewrite rev_app_distr; exact (per_gargs_app_short _ _ _ _ _ Hx _)).
  destruct (rel_modexp_at _ _ _ _ _ (valid_modexp_rel _ _ _ _ HsV) HR _ _ Hρ) as (v & _ & Hv & _ & _).
  destruct (eval_me_apps_inv _ _ _ _ Hv) as (u & ns0 & Hu0 & Hns0 & Hav).
  pose proof (functional_eval_exps _ _ _ _ Hns0 Hns) as ->.
  apply eval_me_lit_iff in Hu0.
  destruct (alias_apps_rel (Δ0 ++ T) Ea ρ ns ns HaT HV0 ltac:(rewrite length_app; lia) (HgsA _ _ Hle Hgs))
    as (h0 & h1 & ws & v' & Hh0 & Hh1 & Hws & Hv' & Hwv).
  pose proof (functional_eval_close _ _ _ _ _ Hh1 Hu0) as ->.
  pose proof (functional_eval_appms _ _ _ _ Hv' Hav) as ->.
  apply (mk_valid_sel_at _ _ _ _ (dm_global p ns) v); [ exact (eval_apps_filed _ _ Hgf _ _ _ _ _ _ Hgl Hns) | exact Hv |].
  apply (dmod_has_sel_resp_r _ _ ws); [| exact Hwv ].
  refine (global_sel p T Φd y (fun ns w => $ᵐ*| h0 & ns | gc_deps ⍮ gc_stack ↘ w) Hm HTa HT _ _ _ ns ns _ Hle Hgs Hws).
  - intros ns1 ns2 w Hl1 Hg1 Hw2.
    destruct (alias_apps_rel (Δ0 ++ T) Ea nil ns1 ns2 HaT HV0 ltac:(rewrite length_app; lia) (HgsA ns1 ns2 ltac:(lia) Hg1))
      as (h0' & h0'' & w1 & w2 & Hh0' & Hh0'' & Hw1 & Hw2' & Hww).
    pose proof (functional_eval_close _ _ _ _ _ Hh0' Hh0) as ->.
    pose proof (functional_eval_close _ _ _ _ _ Hh0'' Hh0) as ->.
    pose proof (functional_eval_appms _ _ _ _ Hw2' Hw2) as ->.
    exists w1; split; [| exact Hww ].
    eapply eval_selm_global_alias; [ rewrite <- qname_in_app; exact HmUa | exact Hh0 | exact Hw1 ].
  - intros ns1 w a Hlt Hw1 Hnp.
    assert (Hlt' : 0 < List.length (Δ0 ++ T)) by (rewrite length_app; lia).
    pose proof (functional_eval_close _ _ _ _ _ Hh0 (close_unsat _ _ _ Hlt')) as ->.
    pose proof (functional_eval_appms _ _ _ _ Hw1 (appms_local ns1 (Δ0 ++ T) (md_alias Ea) nil HaT ltac:(rewrite length_app; lia))) as ->.
    inversion Hnp; subst.
    match goal with Hm0 : gc_loc _ _ p = Some _ |- _ => rewrite Hm in Hm0; injection Hm0 as <- <- end.
    match goal with Hx : nth_error (rev ?T0) _ = Some ?e |- _ =>
      rewrite <- (nth_rev_app_lt Δ0 T0) in Hx by exact Hlt;
      destruct (firstn_rev_nth _ _ _ Hx) as (L0 & HL0) end.
    rewrite HL0; constructor; assumption.
  - intros ns1 ns2 c c' w Hlt Hg1 Hw1.
    pose proof (per_gargs_len_eq _ _ _ _ _ Hg1) as Hl12; rewrite !length_app in Hl12; cbn in Hl12.
    destruct (alias_apps_rel (Δ0 ++ T) Ea nil (ns1 ++ c :: nil) (ns2 ++ c' :: nil) HaT HV0 ltac:(rewrite !length_app; cbn; lia)
                (HgsA (ns1 ++ c :: nil) (ns2 ++ c' :: nil) ltac:(rewrite length_app; cbn; lia) Hg1))
      as (h0' & h0'' & w1 & w2 & Hh0' & Hh0'' & _ & Hw2 & _).
    pose proof (functional_eval_close _ _ _ _ _ Hh0'' Hh0) as ->.
    apply appms_snoc in Hw2 as Hw2'; destruct Hw2' as (w0 & Hw00 & Hc).
    pose proof (functional_eval_appms _ _ _ _ Hw00 Hw1) as ->.
    exists w2; split; assumption.
Qed.

(** ** The Submodules of Valid Units *)

Lemma valid_unit_sel_all :
  (forall Γ K, valid_unit Γ K -> forall y R Rm, mdenote Θm Ξm Γ (me_mem K y) R -> ds_mod Θm Ξm R = Some Rm ->
     valid_sel Γ K y (ds_unit Rm) /\ valid_unit Γ (ds_unit Rm)) /\
  (forall Γ H, valid_modexp Γ H -> forall y R Rm, mdenote Θm Ξm Γ (me_mem H y) R -> ds_mod Θm Ξm R = Some Rm ->
     valid_sel Γ H y (ds_unit Rm) /\ valid_unit Γ (ds_unit Rm)).
Proof.
  apply valid_unit_modexp_ind.
  - (* a filed module at arguments *)
    intros Γ p T Φ Ns Hw Hgl HΓ Hs y R Rm Hm Hmd.
    destruct (mem_unit_wf _ _ _ _ _ Hw Hm Hmd) as (_ & HwU & _).
    destruct (filed_mod_desc _ _ Hgm _ _ _ _ _ _ _ _ Hgl Hm Hmd) as [(Tq & Φq & Hglq & ->) | (Φ0 & E & Ua & RU & Hp & HUa & HmU & HmdU)].
    + cbn [ds_unit] in HwU |- *; exact (filed_body_sel _ _ _ _ _ _ _ _ Hgl Hglq HΓ Hs HwU).
    + destruct (filed_alias_sel _ _ _ _ _ _ _ _ _ Hgl Hp HUa HΓ Hs Hw) as [HS HsV].
      destruct (valid_modexp_canon _ _ Hgm Hgf _ _ _ _ HsV HmU HmdU) as [HVu HKu].
      split; [ exact (valid_sel_resp_r _ _ _ _ _ HS HVu) | exact HKu ].
  - (* a body: its module, filled in, over the parameters *)
    intros Γ Δ Φ Φx Hw Hx HΔ HΓ HC Hsl IHsl Hs Hsx HU Hopv Hops IHops y R Rm Hm Hmd.
    destruct (body_mod_desc _ _ Hgm _ _ _ _ _ _ _ Hx Hm Hmd) as (Φ' & pv & U & σ & RU & Hp & Hf & Hu & ->).
    assert (Hopm : forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Ψ ++ Δ ++ Γ ⊨ᵐ H ≈ H /\
               forall n Rn, mdenote Θm Ξm (Ψ ++ Δ ++ Γ) (me_mem H n) Rn -> ds_is_mod Rn -> exists V, valid_sel (Ψ ++ Δ ++ Γ) H n V).
    { intros k Ψ H Hk; split; [ exact (Hopv _ _ _ Hk) |].
      intros n Rn Hmn HRn; eexists; exact (proj1 (IHops _ _ _ Hk _ _ _ Hmn (ds_is_mod_mod _ _ _ HRn))). }
    destruct (body_sel_base _ _ _ _ _ _ _ _ _ Hx Hsx HC (fun k Ψ H Hk => valid_modexp_kinds _ _ Hgm Hgf _ _ (Hops _ _ _ Hk)) Hopm
                Hp Hf Hu (Hsl _ _ _ _ Hp)) as [HKX Hbase].
    exact (sel_finish _ _ _ _ _ HΔ (rel_ctx_wf_app_r _ _ HC) HΓ (ds_is_mod_sub _ σ (udenote_is_mod _ _ _ _ _ _ Hu)) HKX Hbase).
  - (* an alias: its target's, over the parameters *)
    intros Γ Δ E Hw HΔ HΓ HΔΓ HU HE Hsmt IHE y R Rm Hm Hmd.
    pose proof (proj1 (modexp_gen _ _ _ _ _ Hw)) as Hf; cbn [gen_m unit_full] in Hf; destruct Hf as (HwΔΓ & _ & _).
    destruct (alias_mod_desc _ _ Hgm _ _ _ _ _ _ HwΔΓ Hm Hmd) as (R' & Hm' & ->).
    rewrite ds_mod_up in Hmd; destruct (ds_mod Θm Ξm R') as [Rm' |] eqn:Hmd'; cbn in Hmd; [ injection Hmd as <- | discriminate ].
    destruct (IHE _ _ _ Hm' Hmd') as [HSE HKE].
    apply (sel_finish _ _ _ _ _ HΔ HΔΓ HΓ (ds_mod_is_mod _ _ _ _ Hmd') HKE).
    intros R HR ρ ρ' Hρ.
    assert (HP : PER R) by (eapply per_env_PER; exact HR).
    destruct (HSE _ HR ρ ltac:(etransitivity; [ exact Hρ | symmetry; exact Hρ ])) as [k v Hk Hv Hsel].
    destruct (rel_modexp_at _ _ _ _ _ (valid_unit_rel _ _ Hgf _ _ HKE) HR _ _ Hρ) as (v1 & v0 & Hv1 & Hv0 & Hvv).
    pose proof (functional_eval_modexp _ _ _ _ Hv1 Hv) as ->.
    exists k, v0; split; [ apply eval_close_alias0; exact Hk | split; [ exact Hv0 | exact (dmod_has_sel_resp_r _ _ _ _ Hsel Hvv) ] ].
  - (* a module expression equal to a valid unit *)
    intros Γ H R0 Rm0 K RK HwH HmH HmodH HHK HK IHK HmK HmodK y R Rm Hm Hmd.
    (* a path naming an open frame, of either kind: filed at it *)
    assert (Hframe : forall p Tq Φq, mod_qname (me_mem H y) = Some p -> gc_frame Ξm p = Some (Tq, Φq) ->
              Rm = ds_closed nil p Tq Φq nil -> valid_sel Γ H y (ds_unit Rm) /\ valid_unit Γ (ds_unit Rm)).
    { intros p Tq Φq Hq Hf ->.
      destruct (mem_unit_wf _ _ _ _ _ HwH Hm Hmd) as (_ & HwU & _).
      cbn in Hq; destruct (mod_qname H) as [p0 |] eqn:Hq0; [| discriminate ]; injection Hq as <-.
      change (q_abs (q_unit p0) (q_chain p0 ++ y :: nil)) with (qname_in p0 y) in *.
      assert (Ht : exists U T0, gs_find_tele Ξm (qname_in p0 y) = Some (U, nil, T0)).
      { unfold gc_frame in Hf; destruct (gs_find_tele Ξm (qname_in p0 y)) as [[[U [| ? ?]] T0] |];
          try (destruct U as [? [[|] ? | ?]]); try discriminate; eauto. }
      destruct Ht as (U & T1 & Ht).
      destruct (frame_parent _ _ Hgm _ _ _ _ Ht) as (T0 & Φ0 & Hf0 & _).
      pose proof (mod_qname_inv _ _ Hq0) as ->.
      cbn [ds_unit] in HwU |- *.
      assert (Hs0 : valid_args Γ T0 nil).
      { apply (mk_valid_args _ _ _ T0 nil); [ rewrite app_nil_r; reflexivity | reflexivity | constructor | cbn; auto
                                       | intros [|k] ? ? Hk; discriminate ]. }
      exact (filed_body_sel _ _ _ _ nil _ _ _ ltac:(unfold gc_loc; rewrite Hf0; reflexivity) ltac:(unfold gc_loc; rewrite Hf; reflexivity)
               (valid_unit_ctx_wf _ _ _ _ HK) Hs0 HwU). }
    inversion Hm as [? ? pu Tq Φq Hq Hu | ? ? pu pq k D Hq Hk | | | | ? ? ? R1 R1m Γy E rd R2 ? Hm1 Hmd1 He Hed Hr
                    | ? ? pu Rr Hq Hk]; subst.
    + (* a unit: an open frame *)
      cbn in Hmd; injection Hmd as <-.
      destruct (gc_unit_cases _ _ _ _ _ Hu) as (p & Hq' & [Hf | (_ & Hc & _)]); rewrite Hq in Hq'; injection Hq' as <-.
      * exact (Hframe _ _ _ Hq Hf eq_refl).
      * exfalso; cbn in Hq; destruct (mod_qname H) as [p0 |]; [| discriminate ]; injection Hq as <-.
        cbn in Hc; destruct (q_chain p0); discriminate.
    + (* the open frame of a member's module *)
      destruct (ds_mod_ind_frame _ _ Hgm _ _ _ _ nil nil Hk) as (Tq & Φq & Hf & Hmd'); rewrite Hmd' in Hmd; injection Hmd as <-.
      exact (Hframe _ _ _ Hq Hf eq_refl).
    + pose proof (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm1 _ HmH) as ->.
      rewrite HmodH in Hmd1; injection Hmd1 as <-.
      assert (HmKy : mdenote Θm Ξm Γ (me_mem K y) R) by (eapply dn_mem; [ exact HmK | exact HmodK | exact He | exact Hed | exact Hr ]).
      destruct (IHK _ _ _ HmKy Hmd) as [HS HKu].
      split; [ exact (valid_sel_resp_l _ _ _ _ _ HHK HS) | exact HKu ].
    + (* the open frame of a record type's module *)
      destruct (ds_mod_record_frame _ _ Hgm _ _ nil nil Hk) as (Tq & Φq & Hf & Hmd'); rewrite Hmd' in Hmd; injection Hmd as <-.
      exact (Hframe _ _ _ Hq Hf eq_refl).
Qed.

(** A submodule of a module expression valid in what it denotes is the
    unit of its module part, and valid in what it denotes. *)
Corollary valid_modexp_sel : forall Γ H y R Rm, valid_modexp Γ H -> mdenote Θm Ξm Γ (me_mem H y) R -> ds_mod Θm Ξm R = Some Rm ->
    Γ ⊨ᵐ me_mem H y ≈ ds_unit Rm /\ valid_modexp Γ (me_mem H y) /\ valid_unit Γ (ds_unit Rm).
Proof.
  intros * HH Hm Hmd.
  destruct (proj2 valid_unit_sel_all _ _ HH _ _ _ Hm Hmd) as [HS HK].
  destruct (mem_unit_wf _ _ _ _ _ (valid_modexp_wf _ _ _ _ HH) Hm Hmd) as (HwHy & _ & RK & HmK & HmdK).
  pose proof (rel_sel_of_valid_sel _ _ _ _ _ (valid_modexp_rel _ _ _ _ HH) HS (valid_unit_rel _ _ Hgf _ _ HK)) as Hsel.
  split; [ exact Hsel |]; split; [| exact HK ].
  exact (valid_modexp_intro _ _ _ _ _ _ _ _ HwHy Hm Hmd Hsel HK HmK HmdK).
Qed.

End Valid.

End Fixed_GCtx.
