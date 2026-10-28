(** * Filed Modules in the PER Model

    A global body module at arguments related at its telescope is related
    to itself in the module PER ([gval_rel]).  A filed module at arguments
    valid against its telescope is valid ([filed_valid]), lacks the next
    parameter of the telescope ([filed_lacks]), and its term members are
    valid at the types they are looked up at ([filed_mem]). *)

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
From Mctt.Core.Completeness.Modules Require Import MemberTypes ModuleVal Values ModexpRel.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.Inductives Require Import Decl.
From Mctt.Core.Completeness.Modules Require Import ValidUnit.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Semantic.Kinds Require Import Kinds KindsTyping KindsEval KindsPER.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.

(** ** Global Module Values *)

(** A telescope split at the [n]-th parameter from the inside. *)
Lemma tele_split_rev : forall (T : ctx) n e, nth_error (rev T) n = Some e ->
    exists l1 l2, rev T = l1 ++ e :: l2 /\ List.length l1 = n /\ T = rev l2 ++ e :: rev l1.
Proof.
  intros * Hn.
  destruct (nth_error_split _ _ Hn) as (l1 & l2 & Hl & Hlen).
  exists l1, l2; split; [ exact Hl | split; [ exact Hlen |] ].
  rewrite <- (rev_involutive T), Hl, rev_app_distr; cbn; rewrite <- app_assoc; reflexivity.
Qed.

Lemma gval_rel : forall p T Φ, gc_loc gc_deps gc_stack p = Some (T, Φ) -> tele_ass T -> ⊨ T ->
    forall n args args', n = List.length T - List.length args -> List.length args <= List.length T ->
    per_gargs (rev T) nil nil args args' -> per_dmod (dm_global p args) (dm_global p args').
Proof.
  intros * Hm HTa HT n; induction n as [| n IH]; intros args args' Hn Hle Hg.
  - econstructor; [ exact Hm | lia | exact Hg ].
  - pose proof (per_gargs_len_eq _ _ _ _ _ Hg) as Hl'.
    destruct (nth_error (rev T) (List.length args)) as [e |] eqn:Hne;
      [| apply nth_error_None in Hne; rewrite length_rev in Hne; lia ].
    destruct (tele_split_rev _ _ _ Hne) as (l1 & l2 & Hrev & Hl1 & HT').
    assert (Ha : tele_ass (rev l2 ++ e :: rev l1)) by (rewrite <- HT'; exact HTa).
    apply Forall_app in Ha as [_ Ha]; inversion Ha as [| ? ? [A ->] _]; subst e.
    rewrite HT' in HT.
    pose proof (rel_ctx_wf_app_r _ _ HT) as HAT.
    destruct (rel_ctx_wf_ass_inv HAT) as [i HA].
    pose proof (rel_ctx_wf_tail HAT) as HT0.
    destruct (rel_ctx_wf_per_ctx_env HT0) as [R0 HR0].
    assert (Hg0 : per_gargs l1 nil nil args args').
    { rewrite Hrev in Hg; rewrite <- (app_nil_r args), <- (app_nil_r args') in Hg.
      exact (proj1 (per_gargs_app l1 (ce_ass A :: l2) nil nil args args' nil nil ltac:(lia) Hg ltac:(lia))). }
    assert (Hρ : R0 (env_args nil args) (env_args nil args')).
    { rewrite <- (app_nil_r (rev l1)) in HT0, HR0.
      eapply (gargs_env_rel_gen _ _ _ _ _ _ _ _ per_ctx_env_nil_true HR0 HT0 I);
        [ rewrite length_rev; lia | rewrite rev_involutive; exact Hg0 ]. }
    destruct (rel_exp_of_typ_inversion_simple_at HR0 HA _ _ Hρ) as (a & a' & Ha0 & Ha0' & [RA HRA]).
    assert (Hne' : nth_error (rev T) (List.length args') = Some (ce_ass A)) by (rewrite <- Hl'; exact Hne).
    eapply (per_dmod_fun RA); [ econstructor; [ exact Hm | exact Hne | exact Ha0 ]
                              | econstructor; [ exact Hm | exact Hne' | exact Ha0' ] | exact HRA
                              | intros; eexists; constructor | intros; eexists; constructor |].
    intros c c' hc hc' Hc Hhc Hhc'; inversion Hhc; subst; inversion Hhc'; subst.
    apply IH; [ rewrite !length_app in *; cbn in *; lia | rewrite !length_app in *; cbn in *; rewrite !length_rev in *; lia |].
    rewrite Hrev; change (l1 ++ ce_ass A :: l2) with (l1 ++ (ce_ass A :: nil) ++ l2); rewrite app_assoc.
    rewrite <- (app_nil_r (args ++ c :: nil)), <- (app_nil_r (args' ++ c' :: nil)).
    apply per_gargs_app_intro; [ rewrite !length_app; cbn; lia | | constructor ].
    eapply per_gargs_snoc; [ lia | exact Hg0 | econstructor; eassumption | exact Hc ].
Qed.

Lemma eval_apps_global : forall Ns H p ms ρ ns, ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ dm_global p ms ->
    ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns -> ⟦ me_apps H Ns ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ dm_global p (ms ++ ns).
Proof.
  induction Ns as [| N Ns IH]; intros * HH Hns; inversion Hns; subst; cbn [me_apps]; [ rewrite app_nil_r; exact HH |].
  replace (ms ++ m :: ms0) with ((ms ++ m :: nil) ++ ms0) by (rewrite <- app_assoc; reflexivity).
  apply IH; [ econstructor; [ exact HH | eassumption | constructor ] | assumption ].
Qed.

(** ** Instances of Closed Telescopes *)

Lemma eval_args_valid : forall Γ Ms Ts R, EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    (forall k N T, nth_error Ms k = Some N -> nth_error Ts k = Some T -> Γ ⊨ N : T) -> List.length Ts = List.length Ms ->
    forall ρ, R ρ ρ -> exists ms, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms.
Proof.
  induction Ms as [| M Ms IH]; intros * HR HMs Hl ρ Hρ; [ exists nil; constructor |].
  destruct Ts as [| T Ts]; cbn in Hl; [ discriminate |].
  destruct (rel_exp_under_ctx_simple_at HR (HMs 0 _ _ eq_refl eq_refl) _ _ Hρ) as (m & _ & Hm & _ & _).
  destruct (IH Ts R HR (fun k => HMs (S k)) ltac:(lia) _ Hρ) as (ms & Hms).
  exists (m :: ms); constructor; assumption.
Qed.

Lemma eval_exps_length : forall Ms ρ ms, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms -> List.length ms = List.length Ms.
Proof. induction 1; cbn; congruence. Qed.

(** Arguments valid at a closed telescope make environments of it, at
    related environments, over any bases. *)
Lemma closed_inst_env : forall C Γ Ms RΓ, tele_ass C -> ⊨ C -> ⊨ Γ -> List.length Ms = List.length C ->
    (forall k N T, nth_error Ms k = Some N -> nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> forall ρ ρ', RΓ ρ ρ' ->
    exists ms ms' RC RCΓ, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\ ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ' ↘ ms' /\
      EF C ≈ C ∈ per_ctx_env ↘ RC /\ EF C ++ Γ ≈ C ++ Γ ∈ per_ctx_env ↘ RCΓ /\
      RCΓ (env_args ρ ms) (env_args ρ' ms') /\ (forall B1 B2, RC (env_args B1 ms) (env_args B2 ms')) /\
      List.length ms = List.length C /\ List.length ms' = List.length C.
Proof.
  intros * HCa HC HΓ Hl HMs HRΓ ρ ρ' Hρ.
  assert (HP : PER RΓ) by (eapply per_env_PER; exact HRΓ).
  pose proof (gsub_closed_inst _ _ _ HCa HC HΓ Hl HMs) as Hg.
  pose proof (gsub_valid Hg) as Hσ.
  destruct (closed_app_sem C Γ HCa HC HΓ) as [HCΓ Hres].
  destruct (rel_ctx_wf_per_ctx_env HC) as [RC HRC].
  destruct (rel_ctx_wf_per_ctx_env HCΓ) as [RCΓ HRCΓ].
  assert (HlT : List.length (tele_insts C Id Ms) = List.length Ms) by (rewrite length_tele_insts by exact HCa; lia).
  destruct (eval_args_valid _ _ _ _ HRΓ HMs HlT ρ ltac:(etransitivity; [ exact Hρ | symmetry; exact Hρ ])) as (ms & Hms).
  destruct (eval_args_valid _ _ _ _ HRΓ HMs HlT ρ' ltac:(etransitivity; [ symmetry; exact Hρ | exact Hρ ])) as (ms' & Hms').
  pose proof (eval_sb_of_list _ _ _ _ _ (eval_sub_id ρ) Hms) as Hev.
  pose proof (eval_sb_of_list _ _ _ _ _ (eval_sub_id ρ') Hms') as Hev'.
  pose proof (rel_sub_under_ctx_at' Hσ HRΓ HRCΓ _ _ _ _ Hρ Hev Hev') as Hρσ.
  assert (Hlm : List.length ms = List.length C) by (rewrite (eval_exps_length _ _ _ Hms); exact Hl).
  assert (Hlm' : List.length ms' = List.length C) by (rewrite (eval_exps_length _ _ _ Hms'); exact Hl).
  exists ms, ms', RC, RCΓ; repeat split; try assumption.
  intros B1 B2; eapply closed_env_base; [ exact HCa | exact HC | exact HRC | exact Hlm | exact Hlm' |].
  exact (Hres _ _ HRC HRCΓ _ _ Hρσ).
Qed.

Lemma closed_inst_typ : forall C Γ Ms X i RΓ, tele_ass C -> ⊨ C -> ⊨ Γ -> List.length Ms = List.length C ->
    (forall k N T, nth_error Ms k = Some N -> nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    C ⊨ X : Typeω@i -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> forall ρ, RΓ ρ ρ ->
    exists ms a b R, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\ ⟦ X[sb_of_list Id Ms] ⟧ ρ ↘ a /\
      ⟦ X ⟧ env_args nil ms ↘ b /\ per_univ_elem i R a b.
Proof.
  intros * HCa HC HΓ Hl HMs HX HRΓ ρ Hρ.
  destruct (closed_inst_env _ _ _ _ HCa HC HΓ Hl HMs HRΓ _ _ Hρ) as (ms & ms' & RC & RCΓ & Hms & Hms' & HRC & HRCΓ & Hρσ & Hbase & _).
  pose proof (@functional_eval gc_deps gc_stack) as Hfe; destruct Hfe as (_ & _ & Hfs & _).
  pose proof (Hfs _ _ _ Hms _ Hms') as <-.
  pose proof (gsub_valid (gsub_closed_inst _ _ _ HCa HC HΓ Hl HMs)) as Hσ.
  pose proof (closed_app_valid _ _ _ _ _ HCa HC HΓ HX) as HXΓ.
  destruct (valid_typ_inst _ _ _ _ _ _ HXΓ Hσ HRΓ _ _ Hρ (eval_sb_of_list _ _ _ _ _ (eval_sub_id ρ) Hms))
    as (a & a2 & Ha & Ha2 & [R1 HR1]).
  destruct (rel_exp_of_typ_inversion_simple_at HRC HX _ _ (Hbase ρ nil)) as (a3 & b & Ha3 & Hb & [R2 HR2]).
  functional_eval_rewrite_clear.
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR1 HR2) as (R & HR & _).
  exists ms, a, b, R; repeat split; assumption.
Qed.

Lemma closed_inst_exp : forall C Γ Ms M X RΓ, tele_ass C -> ⊨ C -> ⊨ Γ -> List.length Ms = List.length C ->
    (forall k N T, nth_error Ms k = Some N -> nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    C ⊨ M : X -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> forall ρ, RΓ ρ ρ ->
    exists ms m n a i R, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\ ⟦ M[sb_of_list Id Ms] ⟧ ρ ↘ m /\
      ⟦ M ⟧ env_args nil ms ↘ n /\ ⟦ X[sb_of_list Id Ms] ⟧ ρ ↘ a /\ per_univ_elem i R a a /\ R m n.
Proof.
  intros * HCa HC HΓ Hl HMs HM HRΓ ρ Hρ.
  destruct (closed_inst_env _ _ _ _ HCa HC HΓ Hl HMs HRΓ _ _ Hρ) as (ms & ms' & RC & RCΓ & Hms & Hms' & HRC & HRCΓ & Hρσ & Hbase & _).
  pose proof (@functional_eval gc_deps gc_stack) as Hfe; destruct Hfe as (_ & _ & Hfs & _).
  pose proof (Hfs _ _ _ Hms _ Hms') as <-.
  pose proof (gsub_valid (gsub_closed_inst _ _ _ HCa HC HΓ Hl HMs)) as Hσ.
  pose proof (closed_app_valid _ _ _ _ _ HCa HC HΓ HM) as HMΓ.
  destruct (valid_inst _ _ _ _ _ _ HMΓ Hσ HRΓ _ _ Hρ (eval_sb_of_list _ _ _ _ _ (eval_sub_id ρ) Hms))
    as (m & m2 & a2 & i & R1 & Hm & Hm2 & Ha2 & HR1 & Hmm).
  destruct (valid_at _ _ _ _ HM HRC _ _ (Hbase ρ nil)) as (m2' & n & a2' & i' & R2 & Hm2' & Hn & Ha2' & HR2 & Hmn).
  functional_eval_rewrite_clear.
  destruct (presup_rel_exp_under_ctx HMΓ) as [j HXΓ].
  destruct (valid_typ_inst _ _ _ _ _ _ HXΓ Hσ HRΓ _ _ Hρ (eval_sb_of_list _ _ _ _ _ (eval_sub_id ρ) Hms))
    as (a & b2 & Ha & Hb2 & [R0 HR0]).
  functional_eval_rewrite_clear.
  assert (HP1 : PER R1) by (eapply per_elem_PER; exact HR1).
  assert (HP0 : PER R0) by (eapply per_elem_PER; exact HR0).
  assert (E1 : R0 <~> R1) by (eapply per_univ_elem_left_irrel; [ exact HR0 | exact HR1 ]).
  assert (E2 : R2 <~> R1) by (eapply per_univ_elem_right_irrel; [ exact HR2 | exact HR1 ]).
  exists ms, m, n, a, j, R0; repeat split; try assumption.
  - etransitivity; [ exact HR0 | symmetry; exact HR0 ].
  - apply E1; etransitivity; [ exact Hmm | apply E2; exact Hmn ].
Qed.

(** ** Members of Global Modules *)

(** A function at a telescope's [Π]-type, applied to arguments related at
    the telescope. *)
Lemma apps_rel_gargs : forall ts ρ ρ' args args' A0 g g' j E a a',
    per_gargs ts ρ ρ' args args' ->
    ⟦ ctx_pi (rev ts) A0 ⟧ ρ ↘ a -> ⟦ ctx_pi (rev ts) A0 ⟧ ρ' ↘ a' -> per_univ_elem j E a a' -> E g g' ->
    exists v v' b b' R,
      $*| g & args | gc_deps ⍮ gc_stack ↘ v /\ $*| g' & args' | gc_deps ⍮ gc_stack ↘ v' /\
      ⟦ ctx_pi (rev (skipn (List.length args) ts)) A0 ⟧ env_args ρ args ↘ b /\
      ⟦ ctx_pi (rev (skipn (List.length args) ts)) A0 ⟧ env_args ρ' args' ↘ b' /\
      per_univ_elem j R b b' /\ R v v'.
Proof.
  intros * H; revert A0 g g' j E a a'; induction H; intros * Ha Ha' HE Hg.
  - do 5 eexists; repeat split; [ constructor | constructor | exact Ha | exact Ha' | exact HE | exact Hg ].
  - cbn [rev] in Ha, Ha'; rewrite ctx_pi_app in Ha, Ha'; cbn in Ha, Ha'.
    inversion Ha; subst; inversion Ha'; subst.
    functional_eval_rewrite_clear.
    destruct (per_univ_elem_pi_inv HE) as (in_rel & out_rel & Hin & Hout & HEq).
    match goal with Ht : PER.Definitions.rel_typ _ _ _ _ _ _ |- _ => destruct Ht as [x1 x2 Hx1 Hx2 HRx] end.
    functional_eval_rewrite_clear.
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRx Hin) as ER.
    assert (Hcc : in_rel a a') by (apply ER; assumption).
    destruct (Hout _ _ Hcc) as [b1 b1' Hb1 Hb1' Hb].
    destruct (proj1 (HEq g g') Hg _ _ Hcc) as [g1 g1' Hg1 Hg1' Hgg].
    destruct (IHper_gargs _ _ _ _ _ _ _ Hb1 Hb1' Hb Hgg) as (v & v' & b & b' & R1 & Hv & Hv' & Hb2 & Hb2' & HR1 & Hvv).
    exists v, v', b, b', R1; repeat split; try assumption; econstructor; eassumption.
Qed.

Lemma per_gargs_prefix : forall ts1 ts2 ρ ρ' xs xs', per_gargs (ts1 ++ ts2) ρ ρ' xs xs' -> List.length xs <= List.length ts1 ->
    per_gargs ts1 ρ ρ' xs xs'.
Proof.
  induction ts1 as [| e ts1 IH]; intros * H Hl; [ destruct xs; [ inversion H; subst; constructor | cbn in Hl; lia ] |].
  inversion H; subst; [ constructor |].
  econstructor; [ eassumption | eassumption | eapply IH; [ eassumption | cbn in Hl; lia ] ].
Qed.

Lemma per_gargs_rev_app : forall T1 T2 args args',
    per_gargs (rev T2) nil nil args args' -> List.length args = List.length T2 ->
    per_gargs (rev (T1 ++ T2)) nil nil args args'.
Proof.
  intros * H Hl; rewrite rev_app_distr, <- (app_nil_r args), <- (app_nil_r args').
  apply per_gargs_app_intro; [ rewrite length_rev; lia | exact H | constructor ].
Qed.

(** The member [x] of a global module at arguments related to themselves at
    its telescope, typed at the [Π] over the parameters still missing. *)
Lemma glob_dmod_has_mem : forall p T Φ x A0 g j E e,
    gc_loc gc_deps gc_stack p = Some (T, Φ) -> tele_ass T -> ⊨ T -> (exists i, T ⊨ A0 : Typeω@i) ->
    ⟦ ctx_pi T A0 ⟧ nil ↘ e -> per_univ_elem j E e e -> E g g -> dm_global p nil ·ₜ x gc_deps ⍮ gc_stack ↘ g ->
    forall Tin Tout args, T = Tin ++ Tout -> List.length args = List.length Tout ->
      per_gargs (rev T) nil nil args args ->
      exists a i R, ⟦ ctx_pi Tin A0 ⟧ env_args nil args ↘ a /\ per_univ_elem i R a a /\ dmod_has_mem (dm_global p args) x R.
Proof.
  intros * Hm HT HTs [iA HA0] He HE Hgg Hg Tin.
  assert (HeT : ⟦ ctx_pi (rev (rev T)) A0 ⟧ nil ↘ e) by (rewrite rev_involutive; exact He).
  induction Tin as [| e1 Tin0 IH] using rev_ind; intros Tout args ET Hl Hargs; cbn [List.app] in ET.
  - subst Tout.
    destruct (apps_rel_gargs _ _ _ _ _ _ _ _ _ _ _ _ Hargs HeT HeT HE Hgg) as (v & v' & b & b' & R & Hv & Hv' & Hb & Hb' & HR & Hvv).
    rewrite List.skipn_all2 in Hb, Hb' by (rewrite length_rev; lia); cbn [rev ctx_pi] in Hb, Hb'.
    functional_eval_rewrite_clear.
    pose proof (functional_eval_apps _ _ _ _ Hv Hv') as <-.
    exists b, j, R; cbn [ctx_pi]; split; [ exact Hb | split; [ exact HR |] ].
    intros h Hh.
    inversion Hh as [p0 T0 oD0 args0 args0' Hm0 Hl0 Hg0 | | ? ? ? ? ? Rf Hpf Hpf' _ _ _ _]; subst.
    + rewrite Hm in Hm0; injection Hm0 as <- <-.
      destruct (apps_rel_gargs _ _ _ _ _ _ _ _ _ _ _ _ Hg0 HeT HeT HE Hgg) as (u & u' & c & c' & R1 & Hu & Hu' & Hc & Hc' & HR1 & Huu).
      rewrite List.skipn_all2 in Hc, Hc' by (rewrite length_rev; lia); cbn [rev ctx_pi] in Hc, Hc'.
      functional_eval_rewrite_clear.
      pose proof (functional_eval_apps _ _ _ _ Hu' Hv) as ->.
      assert (E1 : R1 <~> R) by (eapply per_univ_elem_left_irrel; [ exact HR1 | exact HR ]).
      exists u v; [ eapply eval_sel_global_apps; eassumption | eapply eval_sel_global_apps; eassumption
                  | apply E1; exact Huu ].
    + exfalso; destruct (nextparam_global_lt _ _ _ Hpf') as (T1 & oT1 & Hm1 & Hlt).
      rewrite Hm in Hm1; injection Hm1 as <- <-; lia.
  - (* one more parameter missing *)
    pose proof HT as HT0; rewrite ET in HT0.
    destruct (tele_ass_app_inv _ _ HT0) as [HT1 _].
    destruct (tele_ass_app_inv _ _ HT1) as [_ He1]; inversion He1 as [| ? ? [A1 HA1e] _]; subst e1; subst T.
    rewrite <- app_assoc in Hm, HTs, HA0, HeT, Hargs, IH, HT; cbn [List.app] in Hm, HTs, HA0, HeT, Hargs, IH, HT.
    pose proof (rel_ctx_wf_app_r _ _ HTs) as HA1T.
    destruct (rel_ctx_wf_ass_inv HA1T) as [i1 HA1].
    pose proof (rel_ctx_wf_tail HA1T) as HTo.
    destruct (rel_ctx_wf_per_ctx_env HTo) as [Ro HRo].
    assert (HTo' : ⊨ Tout ++ ⋅) by (rewrite app_nil_r; exact HTo).
    assert (HRo' : EF Tout ++ ⋅ ≈ Tout ++ ⋅ ∈ per_ctx_env ↘ Ro) by (rewrite app_nil_r; exact HRo).
    assert (Hargs0 : per_gargs (rev Tout) nil nil args args).
    { rewrite rev_app_distr in Hargs; cbn [rev List.app] in Hargs.
      rewrite <- app_assoc in Hargs; eapply per_gargs_prefix; [ exact Hargs | rewrite length_rev; lia ]. }
    pose proof (gargs_env_rel_gen Tout ⋅ _ _ nil nil args args per_ctx_env_nil_true HRo' HTo' I Hl Hargs0) as Hρ.
    destruct (rel_exp_of_typ_inversion_simple_at HRo HA1 _ _ Hρ) as (a1 & a1' & Ha1 & Ha1' & [Ra HRa]).
    functional_eval_rewrite_clear.
    destruct (rel_exp_ctx_pi (Tin0 ++ ce_ass A1 :: nil) Tout A0 iA ltac:(apply List.Forall_app; split; [ exact (proj1 (tele_ass_app_inv _ _ HT)) | repeat constructor; eauto ])
                ltac:(rewrite <- app_assoc; exact HTs) ltac:(rewrite <- app_assoc; exact HA0)) as [ip HP].
    destruct (rel_exp_of_typ_inversion_simple_at HRo HP _ _ Hρ) as (pa & pa' & Hpa & Hpa' & [RP HRP]).
    functional_eval_rewrite_clear.
    rewrite ctx_pi_app in Hpa |- *; cbn [ctx_pi] in Hpa |- *.
    inversion Hpa; subst.
    match goal with H0 : ⟦ A1 ⟧ _ ↘ ?a0 |- _ => pose proof (functional_eval_exp _ _ _ _ H0 Ha1) as -> end.
    exists (Πᵈ a1 (env_args nil args) (ctx_pi Tin0 A0)), ip, RP; split; [ exact Hpa | split; [ exact HRP |] ].
    assert (Hn : nth_error (rev (Tin0 ++ ce_ass A1 :: Tout)) (List.length args) = Some (ce_ass A1)).
    { rewrite rev_app_distr; cbn [rev List.app].
      rewrite nth_error_app1 by (rewrite length_app, length_rev; cbn; lia).
      rewrite nth_error_app2 by (rewrite length_rev; lia).
      rewrite length_rev, Hl, Nat.sub_diag; reflexivity. }
    assert (Hnp : nextparam (dm_global p args) a1) by (econstructor; [ exact Hm | exact Hn | exact Ha1 ]).
    destruct (apps_rel_gargs _ _ _ _ _ _ _ _ _ _ _ _ Hargs HeT HeT HE Hgg) as (v & _ & _ & _ & _ & Hv & _).
    assert (Hkk : per_dmod (dm_global p args) (dm_global p args))
      by (eapply gval_rel; [ exact Hm | exact HT | exact HTs | reflexivity | rewrite length_app; cbn; lia | exact Hargs ]).
    eapply dmod_has_mem_fun; [ exact Hnp | exact Hkk | exact HRP | eexists; eexists; exact HRa | |
                      eexists; eapply eval_sel_global_apps; eassumption ].
    intros j1 Rc c HRc Hc kc b Hkc Hb.
    inversion Hkc; subst.
    assert (HRa' : Rc <~> Ra) by (eapply per_univ_elem_right_irrel; [ exact HRc | exact HRa ]).
    destruct (IH (ce_ass A1 :: Tout) (args ++ c :: nil) eq_refl ltac:(rewrite length_app; cbn; lia)) as (b' & i' & Rb & Hb' & HRb & Hmt).
    { rewrite rev_app_distr; cbn [rev List.app].
      rewrite <- (app_nil_r (args ++ c :: nil)).
      apply per_gargs_app_intro; [ rewrite !length_app, length_rev; cbn; lia | | constructor ].
      eapply (per_gargs_snoc _ _ _ _ _ _ _ _ _ Ra); [ rewrite length_rev; exact Hl | exact Hargs0 | econstructor; eassumption |].
      apply HRa'; exact Hc. }
    rewrite env_args_snoc in Hb'.
    pose proof (functional_eval_exp _ _ _ _ Hb Hb') as <-.
    exists i', Rb; split; [ exact HRb | exact Hmt ].
Qed.

Lemma eval_ctx_fn_apps : forall T ρ M ns r, tele_ass T -> List.length ns = List.length T ->
    ⟦ M ⟧ env_args ρ ns ↘ r -> exists f, ⟦ ctx_fn T M ⟧ ρ ↘ f /\ $*| f & ns | gc_deps ⍮ gc_stack ↘ r.
Proof.
  induction T as [| e T0 IH] using rev_ind; intros * HT Hl HM.
  - destruct ns; cbn in Hl; [| discriminate ]; exists r; split; [ exact HM | constructor ].
  - destruct (tele_ass_app_inv _ _ HT) as [HT0 He]; inversion He as [| ? ? [A ->] _]; subst.
    destruct ns as [| n ns0]; [ rewrite length_app in Hl; cbn in Hl; lia |].
    rewrite length_app in Hl; cbn in Hl.
    change (env_args ρ (n :: ns0)) with (env_args (ρ ↦ n) ns0) in HM.
    destruct (IH _ _ ns0 _ HT0 ltac:(lia) HM) as (f0 & Hf0 & Ha0).
    rewrite ctx_fn_app; cbn [ctx_fn].
    exists (λᵈ ρ (ctx_fn T0 M)); split; [ constructor | econstructor; [ constructor; exact Hf0 | exact Ha0 ] ].
Qed.

(** The arguments of a filed module valid against its telescope are related
    to themselves at it, at any environment. *)
Lemma valid_args_gargs : forall Γ T Ns RΓ, ⊨ T -> ⊨ Γ -> valid_args Γ T Ns -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    forall ρ ρ', RΓ ρ ρ' -> exists ns ns', ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns /\ ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ' ↘ ns' /\
      per_gargs (rev T) nil nil ns ns'.
Proof.
  intros * HT HΓ [T1 T2 -> Hlen HTa2 HTs2 HNs] HR ρ ρ' Hρ.
  pose proof (rel_ctx_wf_app_r _ _ HT) as HT2.
  destruct (closed_inst_env _ _ _ _ HTa2 HT2 HΓ (eq_sym Hlen) HNs HR _ _ Hρ)
    as (ns & ns' & RC & RCΓ & Hns & Hns' & HRC & _ & _ & Hbase & Hl1 & Hl2).
  exists ns, ns'; split; [ exact Hns |]; split; [ exact Hns' |].
  apply per_gargs_rev_app; [| exact Hl1 ].
  assert (HT2' : ⊨ rev (rev T2) ++ ⋅) by (rewrite rev_involutive, app_nil_r; exact HT2).
  assert (HRC' : EF rev (rev T2) ++ ⋅ ≈ rev (rev T2) ++ ⋅ ∈ per_ctx_env ↘ RC) by (rewrite rev_involutive, app_nil_r; exact HRC).
  destruct (rel_gargs _ _ _ _ per_ctx_env_nil_true HT2' (List.Forall_rev HTa2) HRC' nil nil ns ns'
              ltac:(rewrite length_rev; exact Hl1) ltac:(rewrite length_rev; exact Hl2) (Hbase nil nil)) as [_ Hg].
  exact Hg.
Qed.

(** ** Terms Evaluating Alike *)

Lemma valid_exp_eval_iff : forall Γ A M M', Γ ⊨ M : A ->
    (forall σ ρ r, ⟦ M[σ] ⟧ ρ ↘ r <-> ⟦ M'[σ] ⟧ ρ ↘ r) -> Γ ⊨ M' : A.
Proof.
  intros * [R HR i HM] Hiff.
  assert (Hid : forall ρ r, ⟦ M ⟧ ρ ↘ r <-> ⟦ M' ⟧ ρ ↘ r) by (intros ρ r; rewrite <- (exp_sub_id M), <- (exp_sub_id M'); apply Hiff).
  refine (mk_rel_exp_under_ctx _ _ _ _ R HR i _); intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HM _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [Rel [HT [m1 m2 m3 m4 H1 H2 H3 H4 Hc]]].
  exists Rel; split; [ exact HT |].
  apply (mk_rel_exp m1 m2 m3 m4); [ apply Hiff | apply Hid | apply Hid | apply Hiff | ]; assumption.
Qed.

Lemma spine_mems : forall pre H R pre0, modexp_spine H = (R, nil, pre0) -> modexp_spine (me_mems H pre) = (R, nil, pre0 ++ pre).
Proof.
  induction pre as [| y pre IH]; intros * Hs; cbn [me_mems]; [ rewrite app_nil_r; exact Hs |].
  rewrite (IH (me_mem H y) R (pre0 ++ y :: nil)); [ rewrite <- app_assoc; reflexivity | cbn; rewrite Hs; reflexivity ].
Qed.

Lemma spine_apps : forall Ns H R args pre, modexp_spine H = (R, args, pre) -> modexp_spine (me_apps H Ns) = (R, args ++ Ns, pre).
Proof.
  induction Ns as [| N Ns IH]; intros * Hs; cbn [me_apps]; [ rewrite app_nil_r; exact Hs |].
  rewrite (IH (me_app H N) R (args ++ N :: nil) pre); [ rewrite <- app_assoc; reflexivity | cbn; rewrite Hs; reflexivity ].
Qed.

Lemma member_ref_snoc : forall pre R x, member_ref R (pre ++ x :: nil) = a_mem (me_mems R pre) x.
Proof. induction pre as [| y pre IH]; intros; [ reflexivity | cbn [app me_mems]; rewrite <- IH; destruct pre; reflexivity ]. Qed.

(** A member of a filed module at arguments is the member of the module
    applied to the arguments. *)
Lemma eval_mem_filed : forall p Ns x ρ r,
    ⟦ a_mem (me_apps (qname_mod p) Ns) x ⟧ ρ ↘ r <-> ⟦ apps (a_mem (qname_mod p) x) Ns ⟧ ρ ↘ r.
Proof.
  intros.
  assert (Hs : modexp_spine (me_apps (qname_mod p) Ns) = (me_unit (q_unit p), Ns, q_chain p)).
  { pose proof (spine_apps Ns (qname_mod p) (me_unit (q_unit p)) nil (q_chain p)) as H; cbn [app] in H; apply H.
    unfold qname_mod; exact (spine_mems (q_chain p) (me_unit (q_unit p)) (me_unit (q_unit p)) nil eq_refl). }
  rewrite (eval_mem_apps _ _ _ _ _ _ _ _ _ Hs), member_ref_snoc; reflexivity.
Qed.

(** ** Filed Modules *)

Section Filed.
  Variables (Θm : gdeps) (Ξm : gstack).
  Hypothesis Hgm : ⊢ᵍ Θm ⍮ Ξm.
  Hypothesis Hgf : valid_filed_mods Θm Ξm.

Lemma eval_apps_filed : forall p T Φ Ns ρ ns, gc_loc Θm Ξm p = Some (T, Φ) ->
    ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns -> ⟦ me_apps (qname_mod p) Ns ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ dm_global p ns.
Proof.
  intros * Hl Hns; destruct (Hgf _ _ _ Hl) as [_ Hp _ _ _ _ _ _ _ _ _].
  exact (eval_apps_global _ _ _ nil _ _ (Hp ρ) Hns).
Qed.

Lemma filed_gval : forall p T Φ, gc_loc Θm Ξm p = Some (T, Φ) ->
    forall args args', List.length args <= List.length T -> per_gargs (rev T) nil nil args args' ->
    per_dmod (dm_global p args) (dm_global p args').
Proof.
  intros * Hl * Hle Hg; destruct (Hgf _ _ _ Hl) as [(Φ' & Hm) _ HT HTa _ _ _ _ _ _ _].
  exact (gval_rel _ _ _ Hm HTa HT _ _ _ eq_refl Hle Hg).
Qed.

(** The arguments of a filed module lack the next parameter of its
    telescope. *)
Lemma filed_lacks : forall Γ p T Φ L A T2 Ns, gc_loc Θm Ξm p = Some (T, Φ) -> ⊨ Γ ->
    T = L ++ ce_ass A :: T2 -> List.length Ns = List.length T2 ->
    (forall k N B, nth_error Ns k = Some N -> nth_error (tele_insts T2 Id Ns) k = Some B -> Γ ⊨ N : B) ->
    modexp_next_param Γ (me_apps (qname_mod p) Ns) A[sb_of_list Id Ns].
Proof.
  intros * Hl HΓ -> Hlen HNs R HR ρ Hρ.
  destruct (Hgf _ _ _ Hl) as [(oD & Hm) Hp HT HTa HTs _ _ _ _ _ _].
  pose proof (rel_ctx_wf_app_r _ _ HT) as HAT2.
  destruct (rel_ctx_wf_ass_inv HAT2) as [i HA].
  pose proof (rel_ctx_wf_tail HAT2) as HT2.
  destruct (tele_ass_app_inv _ _ HTa) as [_ HTa2]; inversion HTa2 as [| ? ? _ HTa2']; subst.
  destruct (closed_inst_typ _ _ _ _ _ _ HTa2' HT2 HΓ Hlen HNs HA HR _ Hρ) as (ns & a & b & RA & Hns & Ha & Hb & HRA).
  exists (dm_global p ns) b a i RA;
    [ exact (eval_apps_filed _ _ _ _ _ _ Hl Hns) | econstructor; [ exact Hm | | exact Hb ] | exact Ha
    | exact (proj1 (per_univ_elem_sym _ _ _ _ HRA)) ].
  pose proof (eval_exps_length _ _ _ Hns) as Hlns.
  rewrite rev_app_distr; cbn [rev List.app]; rewrite <- app_assoc; cbn [List.app].
  rewrite nth_error_app2 by (rewrite length_rev; lia).
  rewrite length_rev, Hlns, Hlen, Nat.sub_diag; reflexivity.
Qed.

(** A filed module at arguments valid against its telescope is valid. *)
Lemma filed_valid : forall Γ p T Φ Ns, gc_loc Θm Ξm p = Some (T, Φ) -> ⊨ Γ -> valid_args Γ T Ns ->
    Γ ⊨ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns.
Proof.
  intros * Hl HΓ [T1 T2 -> Hlen HTa2 HTs2 HNs].
  revert T1 T2 Hl Hlen HTa2 HTs2 HNs.
  induction Ns as [| N Ns IH] using rev_ind; intros * Hl Hlen HTa2 HTs2 HNs.
  - destruct (Hgf _ _ _ Hl) as [_ Hp _ _ _ _ _ _ _ _ _].
    destruct (rel_ctx_wf_per_ctx_env HΓ) as [R HR].
    pose proof (filed_gval _ _ _ Hl nil nil ltac:(cbn; lia) ltac:(constructor)) as Hd.
    cbn [me_apps]; refine (mk_rel_modexp_under_ctx _ _ _ R HR _); intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
    apply (mk_rel_modexp (dm_global p nil) (dm_global p nil) (dm_global p nil) (dm_global p nil));
      [ rewrite qname_mod_sub; apply Hp | apply Hp | apply Hp | rewrite qname_mod_sub; apply Hp |].
    repeat split; exact Hd.
  - (* the last argument, against the next parameter *)
    destruct T2 as [| e T2']; [ rewrite length_app in Hlen; cbn in Hlen; lia |].
    inversion HTa2 as [| ? ? [A ->] HTa2']; subst.
    rewrite length_app in Hlen; cbn in Hlen.
    assert (Hti : tele_insts (ce_ass A :: T2') Id (Ns ++ N :: nil) = tele_insts T2' Id Ns ++ A[sb_of_list Id Ns] :: nil).
    { change (ce_ass A :: T2') with ((ce_ass A :: nil) ++ T2').
      rewrite tele_insts_app by (try exact HTa2'; lia); reflexivity. }
    assert (HlT : List.length (tele_insts T2' Id Ns) = List.length Ns) by (rewrite length_tele_insts by exact HTa2'; lia).
    assert (HNs' : forall k N0 B, nth_error Ns k = Some N0 -> nth_error (tele_insts T2' Id Ns) k = Some B -> Γ ⊨ N0 : B).
    { intros k N0 B HN0 HB.
      assert (Hk : k < List.length Ns) by (apply List.nth_error_Some; congruence).
      apply (HNs k); [ rewrite nth_error_app1 by lia; exact HN0 | rewrite Hti, nth_error_app1 by lia; exact HB ]. }
    assert (HN : Γ ⊨ N : A[sb_of_list Id Ns])
      by (apply (HNs (List.length Ns)); [ rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity
                                        | rewrite Hti, nth_error_app2, HlT, Nat.sub_diag by lia; reflexivity ]).
    assert (Ex : T1 ++ ce_ass A :: T2' = (T1 ++ ce_ass A :: nil) ++ T2') by (rewrite <- app_assoc; reflexivity).
    pose proof (IH (T1 ++ ce_ass A :: nil) T2' ltac:(rewrite <- Ex; exact Hl)
                  ltac:(lia) HTa2' ltac:(cbn in HTs2; tauto) HNs') as HH.
    rewrite me_apps_snoc.
    eapply rel_modexp_under_ctx_app; [ exact HH | exact HN |].
    eapply filed_lacks; [ exact Hl | exact HΓ | reflexivity | lia | exact HNs' ].
Qed.

Lemma mdesc_type_named_m : forall Θ' Ns M R, mdesc_type (mdesc_named Θ' Ns M R) = mdesc_type R.
Proof. intros; apply (mdesc_named_cases (fun R' => mdesc_type R' = mdesc_type R)); [| destruct R as [A [?|] | | | ] ]; reflexivity. Qed.

Lemma mdesc_reduct_named_some : forall Θ' Ns M R N, mdesc_reduct R = Some N -> mdesc_reduct (mdesc_named Θ' Ns M R) = Some N.
Proof. intros * H; apply (mdesc_named_cases (fun R' => mdesc_reduct R' = Some N)); [ exact H | destruct R as [A [?|] | | | ]; cbn in *; congruence ]. Qed.

(** A stored term part with a module part, read at arguments: its term
    part, as a transparent definition is. *)
#[local] Ltac filed_dm_read :=
  match goal with
  | Hed : edenote _ _ _ _ _ _, Ha : mdesc_ats_read _ ?Ns = Some _ |- _ =>
      inversion Hed; subst; unfold ind_former_desc, record_former_desc in Ha; cbn [mdesc_ats_read] in Ha;
      match type of Ha with
      | context [mdesc_term_part_ats (mdesc_term ?A1 (Some ?M1)) Ns] =>
          destruct (mdesc_term_part_ats (mdesc_term A1 (Some M1)) Ns) as [[B [M' |] | | |] |] eqn:Et; try discriminate;
          exists (mdesc_term A1 (Some M1)), (mdesc_term B (Some M'))
      end;
      match type of Ha with
      | context [mdesc_ats ?Rx Ns] => destruct (mdesc_ats Rx Ns) as [Rm' |]; [ injection Ha as <- | discriminate ]
      end;
      (split; [ left; do 2 eexists; split; [ reflexivity | cbn [entry_term];
                                         try (match goal with HMk : ind_member _ _ = Some _ |- _ => rewrite HMk end);
                                         reflexivity ] | split; [ eassumption |] ]);
      [ .. | rewrite !mdesc_named_fix by reflexivity; split; reflexivity ]
  end.

(** A term member of a filed module at arguments, read off its stored
    entry, or the open frame of a member's module or of a record type's
    module under it, read as its type former. *)
Lemma filed_mem_desc : forall Γ p T Φ Ns x R A, gc_loc Θm Ξm p = Some (T, Φ) ->
    mdenote Θm Ξm Γ (me_mem (me_apps (qname_mod p) Ns) x) R -> mdesc_type R = Some A ->
    exists R0 R1,
      ((exists Φ0 E0, gm_prefix_upto Φ x = Some (gm_ext Φ0 x E0) /\ entry_term (Some (qname_in p x)) E0 = Some R0) \/
       (exists pq k D Mk, gs_find_ind Ξm (qname_in p x) = Some (pq, k, D) /\ ind_member D k = Some Mk /\
          R0 = mdesc_term (ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ) (Some (a_ind pq k))) \/
       (exists Rr, gs_find_record Ξm (qname_in p x) = Some Rr /\
          R0 = mdesc_term (ctx_pi (record_params Rr) (record_sort Rr)) (Some (a_record (qname_in p x))))) /\
      mdesc_term_part_ats R0 Ns = Some R1 /\
      mdesc_type R = mdesc_type (mdesc_named nil Ns (apps (a_mem (qname_mod p) x) Ns) R1) /\
      mdesc_reduct R = mdesc_reduct (mdesc_named nil Ns (apps (a_mem (qname_mod p) x) Ns) R1).
Proof.
  intros * Hgl Hm Hty.
  inversion Hm as [? ? ? ? ? Hq Hu | ? ? ? pq k D Mk Tm Φm Hq Hk HMk Hlm | | | | ? ? ? R0 R0m Γy E rd R1 ? Hm0 Hmd He Hed Hr
                  | ? ? ? Rr Tm Φm Hq Hk Hlm]; subst;
    [ cbn in Hty; discriminate | | |].
  { (* the open frame of a member's module: no argument; its type former *)
    destruct Ns as [| N Ns'] using List.rev_ind; [| rewrite me_apps_snoc in Hq; discriminate ].
    cbn [me_apps] in Hq; rewrite <- qname_mod_in, mod_qname_qname_mod in Hq; injection Hq as <-.
    eexists; eexists;
      split; [ right; left; exists pq, k, D, Mk; split; [ exact Hk | split; [ exact HMk | reflexivity ] ] |].
    split; [ reflexivity | rewrite mdesc_named_nil; split; reflexivity ]. }
  2:{ (* the open frame of a record type's module: likewise *)
    destruct Ns as [| N Ns'] using List.rev_ind; [| rewrite me_apps_snoc in Hq; discriminate ].
    cbn [me_apps] in Hq; rewrite <- qname_mod_in, mod_qname_qname_mod in Hq; injection Hq as <-.
    eexists; eexists;
      split; [ right; right; exists Rr; split; [ exact Hk | reflexivity ] |].
    split; [ reflexivity | rewrite mdesc_named_nil; split; reflexivity ]. }
  destruct (filed_denote _ _ Hgm _ _ _ Γ Ns Hgl) as (R2 & Hm2 & Hmod2).
  rewrite (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm0 _ Hm2), Hmod2 in Hmd; injection Hmd as <-.
  cbn in He; destruct (gm_prefix_upto Φ x) as [[| Φ0 z E0 | ] |] eqn:Hp; try discriminate.
  pose proof (gm_prefix_name _ _ _ _ _ Hp) as ->.
  injection He as <- <- <-; cbn [app] in Hed.
  cbn [mdesc_read] in Hr; destruct (mdesc_ats_read R1 Ns) as [R3 |] eqn:Ha; cbn in Hr; [ injection Hr as <- | discriminate ].
  rewrite mdesc_up_nil in Hty |- *.
  destruct E0 as [b pv A0 oM | pv U | pv pq D Φd | pv Ad Md Ud | pv Rr Φr].
  - inversion Hed; subst; cbn [mdesc_ats_read] in Ha.
    do 2 eexists; split; [ left; do 2 eexists; split; reflexivity | split; [ exact (mdesc_term_part_ats_of_ats _ _ _ Ha) | split; reflexivity ] ].
  - exfalso.
    assert (HU : exists U', ge_read T (ge_mod pv U) = ge_mod pv U') by (destruct U as [? [[] ?|?]]; eexists; reflexivity).
    destruct HU as [U' HU]; rewrite HU in Hed; inversion Hed; subst.
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hmm end.
    rewrite mdesc_ats_read_mod in Ha by exact Hmm.
    pose proof (mdesc_ats_is_mod _ _ _ Hmm Ha) as Hmod.
    destruct R3; cbn in Hmod; try contradiction; rewrite mdesc_named_fix in Hty by reflexivity; cbn in Hty; discriminate.
  (* a type former, or a definition with a module part: its term part, as
     a transparent definition *)
  - filed_dm_read.
  - filed_dm_read.
  - filed_dm_read.
Qed.

(** The term members of a filed module at arguments valid against its
    telescope are valid at the types they are looked up at, their reducts
    at them too. *)
Lemma filed_mem : forall Γ p T Φ Ns x R A, gc_loc Θm Ξm p = Some (T, Φ) -> ⊨ Γ -> valid_args Γ T Ns ->
    mdenote Θm Ξm Γ (me_mem (me_apps (qname_mod p) Ns) x) R -> mdesc_type R = Some A ->
    valid_mem Γ (me_apps (qname_mod p) Ns) x A (mdesc_reduct R).
Proof.
  intros * Hl HΓ Hs Hm Ht.
  destruct (filed_mem_desc _ _ _ _ _ _ _ _ Hl Hm Ht) as (R0 & R1 & HR0 & Ha & HtR & HrR).
  rewrite HtR in Ht; rewrite HrR.
  rewrite mdesc_type_named_m in Ht.
  destruct (Hgf _ _ _ Hl) as [(oD & Hmo) Hpe HT HTa HTs _ _ Hents Hfrs Hrfrs _].
  pose proof Hs as [T1 T2 -> Hlen HTa2 HTs2 HNs].
  assert (Hvt : valid_filed_term p (T1 ++ T2) x R0)
    by (destruct HR0 as [(Φ0 & E & Hp & He) | [(pq & k & D & Mk & Hk & HMk & ->) | (Rr & Hk & ->)]];
          [ exact (Hents _ _ _ _ Hp He) | exact (Hfrs _ _ _ _ _ Hk HMk) | exact (Hrfrs _ _ Hk) ]).
  destruct Hvt as [A0 i g HA0 Hats Hsel [j E0 e He0 HE0 Hgg]].
  destruct (Hats _ _ _ _ eq_refl Hlen Ha) as [HtyR1 HredR1].
  rewrite HtyR1 in Ht; injection Ht as <-.
  set (K := me_apps (qname_mod p) Ns).
  set (Mn := apps (a_mem (qname_mod p) x) Ns).
  destruct (tele_ass_app_inv _ _ HTa) as [HTa1 _].
  pose proof (rel_ctx_wf_app_r _ _ HT) as HT2.
  destruct (rel_exp_ctx_pi _ _ _ _ HTa1 HT HA0) as [iX HX].
  pose proof (gsub_closed_inst _ _ _ HTa2 HT2 HΓ (eq_sym Hlen) HNs) as Hg.
  assert (HXΓ : Γ ⊨ (ctx_pi T1 A0)[sb_of_list Id Ns] : Typeω@iX)
    by (pose proof (rel_exp_under_ctx_gsub Hg (closed_app_valid _ _ _ _ _ HTa2 HT2 HΓ HX)) as H0; cbn in H0; exact H0).
  (* the member, pointwise *)
  assert (Hpt : forall RΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> forall ρ, RΓ ρ ρ ->
             exists ns a RX, ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns /\ ⟦ (ctx_pi T1 A0)[sb_of_list Id Ns] ⟧ ρ ↘ a /\
               per_univ_elem iX RX a a /\ dmod_has_mem (dm_global p ns) x RX /\ per_dmod (dm_global p ns) (dm_global p ns)).
  { intros RΓ HR ρ Hρ.
    destruct (closed_inst_typ _ _ _ _ _ _ HTa2 HT2 HΓ (eq_sym Hlen) HNs HX HR _ Hρ) as (ns & a & b & RX & Hns & Ha1 & Hbb & HRX).
    destruct (valid_args_gargs _ _ _ _ HT HΓ Hs HR _ _ Hρ) as (ns1 & ns2 & Hns1 & Hns2 & Hgs).
    pose proof (@functional_eval gc_deps gc_stack) as Hfe; destruct Hfe as (_ & _ & Hfs & _).
    pose proof (Hfs _ _ _ Hns1 _ Hns) as ->; pose proof (Hfs _ _ _ Hns2 _ Hns) as ->.
    assert (Hlns : List.length ns = List.length T2) by (rewrite (eval_exps_length _ _ _ Hns); lia).
    destruct (glob_dmod_has_mem _ _ _ _ _ _ _ _ _ Hmo HTa HT (ex_intro (fun i0 : nat => _ ⊨ _ : Typeω@i0) i HA0) He0 HE0 Hgg Hsel T1 T2 ns eq_refl Hlns Hgs)
      as (a' & i' & R' & Ha' & HR' & Hmt).
    functional_eval_rewrite_clear.
    assert (HPX : PER RX) by (eapply per_elem_PER; exact HRX).
    assert (ER : RX <~> R') by (eapply per_univ_elem_left_irrel; [ exact HRX | exact HR' ]).
    assert (Haa : per_univ_elem iX RX a a) by (eapply per_univ_trans; [ exact HRX | apply per_univ_elem_sym; exact HRX ]).
    exists ns, a, RX; repeat split; [ exact Hns | exact Ha1 | exact Haa | apply (dmod_has_mem_iff _ _ R'); [ exact Hmt | symmetry; exact ER ] |].
    apply (filed_gval _ _ _ Hl); [ rewrite length_app; lia | exact Hgs ]. }
  assert (HS0 : valid_mem Γ K x (ctx_pi T1 A0)[sb_of_list Id Ns] None).
  { constructor; [ exists iX; exact HXΓ | discriminate |].
    intros RΓ HR ρ Hρ.
    destruct (Hpt _ HR _ Hρ) as (ns & a & RX & Hns & Ha1 & Haa & Hmt & _).
    apply mk_valid_mem_at with (valid_mem_at_mod := dm_global p ns) (valid_mem_at_typ := a) (valid_mem_at_lvl := iX) (valid_mem_at_rel := RX); try assumption;
      [ exact (eval_apps_filed _ _ _ _ _ _ Hl Hns) | discriminate ]. }
  destruct HredR1 as [HredR1 | (M1 & HredR1 & HM1 & HevM1)].
  2:{ (* a reduct: a term over the outer parameters, instantiated *)
    rewrite (mdesc_reduct_named_some _ _ _ _ _ HredR1).
    constructor; [ exists iX; exact HXΓ | |].
    + intros M HM; injection HM as <-.
      exact (rel_exp_under_ctx_gsub Hg (closed_app_valid _ _ _ _ _ HTa2 HT2 HΓ HM1)).
    + intros RΓ HR ρ Hρ.
      destruct (Hpt _ HR _ Hρ) as (ns & a & RX & Hns & Ha1 & Haa & Hmt & _).
      apply mk_valid_mem_at with (valid_mem_at_mod := dm_global p ns) (valid_mem_at_typ := a) (valid_mem_at_lvl := iX) (valid_mem_at_rel := RX);
        [ exact (eval_apps_filed _ _ _ _ _ _ Hl Hns) | exact Ha1 | exact Haa | exact Hmt |].
      intros M HM; injection HM as <-.
      destruct (closed_inst_exp _ _ _ _ _ _ HTa2 HT2 HΓ (eq_sym Hlen) HNs HM1 HR _ Hρ)
        as (ns' & m & n & a2 & i2 & R2 & Hns' & Hm' & Hn & Ha2 & HR2 & Hmn).
      pose proof (@functional_eval gc_deps gc_stack) as Hfe; destruct Hfe as (_ & _ & Hfs & _).
      pose proof (Hfs _ _ _ Hns' _ Hns) as ->.
      functional_eval_rewrite_clear.
      assert (Hlns : List.length ns = List.length T2) by (rewrite (eval_exps_length _ _ _ Hns); lia).
      apply (mk_rel_mem_reduct _ _ _ _ _ m n); [ exact Hm' | eapply eval_sel_global_apps; [ exact Hsel | exact (HevM1 _ _ Hlns Hn) ] |].
      assert (E2 : R2 <~> RX) by (eapply per_univ_elem_right_irrel; [ exact HR2 | exact Haa ]).
      apply E2; exact Hmn. }
  - (* an axiom or an abstract definition: its name at the arguments, or,
       read bare, none *)
    destruct R1 as [A1 [?|] | | |]; cbn in HredR1, HtyR1; try discriminate.
    destruct (mdesc_named_term_none nil Ns Mn A1) as [(Hn & _ & HN) | Hn]; rewrite Hn; cbn [mdesc_reduct];
      [ exact HS0 |].
    assert (Hiff : forall σ ρ r, ⟦ (a_mem K x)[σ] ⟧ ρ ↘ r <-> ⟦ Mn[σ] ⟧ ρ ↘ r).
    { intros σ ρ r; subst K Mn; cbn [exp_sub]; rewrite me_apps_sub, qname_mod_sub, apps_sub; cbn [exp_sub].
      rewrite qname_mod_sub; apply eval_mem_filed. }
    pose proof (filed_valid _ _ _ _ _ Hl HΓ Hs) as HK.
    pose proof (rel_mem_of_valid_mem _ _ _ _ _ _ HK HS0) as HKx.
    constructor; [ exists iX; exact HXΓ | |].
    + intros M HM; injection HM as <-; exact (valid_exp_eval_iff _ _ _ _ HKx Hiff).
    + intros RΓ HR ρ Hρ.
      destruct (Hpt _ HR _ Hρ) as (ns & a & RX & Hns & Ha1 & Haa & Hmt & Hkk).
      apply mk_valid_mem_at with (valid_mem_at_mod := dm_global p ns) (valid_mem_at_typ := a) (valid_mem_at_lvl := iX) (valid_mem_at_rel := RX);
        [ exact (eval_apps_filed _ _ _ _ _ _ Hl Hns) | exact Ha1 | exact Haa | exact Hmt |].
      intros M HM; injection HM as <-.
      destruct (Hmt _ Hkk) as [r r' Hr Hr' Hrr].
      pose proof (functional_eval_sel _ _ _ _ Hr Hr') as <-.
      apply (mk_rel_mem_reduct _ _ _ _ _ r r); [| exact Hr | exact Hrr ].
      rewrite <- (exp_sub_id Mn); apply Hiff; rewrite exp_sub_id.
      eapply eval_mem_of_sel; [ exact (eval_apps_filed _ _ _ _ _ _ Hl Hns) | exact Hr ].
Qed.

End Filed.

End Fixed_GCtx.
