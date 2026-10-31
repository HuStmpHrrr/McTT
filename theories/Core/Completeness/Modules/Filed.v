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
From Mctt.Core.Completeness Require Import LetCases UnitCases PropCases.
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
    destruct (rel_ctx_wf_ass_inv HAT) as [Srt [HS HAs]].
    destruct (rel_type_of_sort HS HAs) as [i HA].
    pose proof (rel_ctx_wf_tail HAT) as HT0.
    destruct (rel_ctx_wf_per_ctx_env HT0) as [R0 HR0].
    assert (Hg0 : per_gargs l1 nil nil args args').
    { rewrite Hrev in Hg; rewrite <- (app_nil_r args), <- (app_nil_r args') in Hg.
      exact (proj1 (per_gargs_app l1 (ce_ass A :: l2) nil nil args args' nil nil ltac:(lia) Hg ltac:(lia))). }
    assert (Hρ : R0 (env_args nil args) (env_args nil args')).
    { rewrite <- (app_nil_r (rev l1)) in HT0, HR0.
      eapply (gargs_env_rel_gen _ _ _ _ _ _ _ _ per_ctx_env_nil_true HR0 HT0 I);
        [ rewrite length_rev; lia | rewrite rev_involutive; exact Hg0 ]. }
    destruct (rel_type_inversion_simple_at HR0 HA _ _ Hρ) as (a & a' & Ha0 & Ha0' & [RA HRA]).
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

Lemma eval_exps_length : forall Ms ρ ms, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms -> List.length ms = List.length Ms.
Proof. induction 1; cbn; congruence. Qed.

(** Arguments valid at a closed telescope, at relevant instantiated types,
    evaluate, and the substitution they make evaluates at the telescope
    over [Γ] to the environment of their values: no parameter is a
    proposition there, its type being relevant as its instance is
    ([rel_type_sub_relevance]). *)
Lemma closed_inst_eval : forall C Γ Ms RΓ, tele_ass C -> ⊨ C -> ⊨ Γ -> List.length Ms = List.length C ->
    (forall k N T, nth_error Ms k = Some N -> nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    (forall k T, nth_error (tele_insts C Id Ms) k = Some T -> exists i : nat, Γ ⊨ T : Typeω@i) ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> forall ρ, RΓ ρ ρ ->
    exists ms, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\ ⟦ sb_of_list Id Ms : C ++ Γ ⟧s ρ ↘ env_args ρ ms.
Proof.
  induction C as [| e C IH]; intros Γ Ms RΓ HCa HC HΓ Hl HMs HTs HRΓ ρ Hρ.
  - destruct Ms; cbn in Hl; [| discriminate ].
    exists nil; split; [ constructor | exact (proj1 (eval_sub_id_rel HRΓ Hρ)) ].
  - assert (He : exists A, e = ce_ass A) by (inversion HCa as [| ? ? He _]; exact He).
    destruct He as [A ->].
    assert (HCa' : tele_ass C) by (inversion HCa; assumption).
    destruct (rel_ctx_wf_ass_inv HC) as (Srt & HS & HA).
    pose proof (rel_ctx_wf_tail HC) as HC'.
    destruct (List.exists_last (l := Ms) ltac:(intros ->; cbn in Hl; discriminate)) as (Ms' & M & ->).
    rewrite List.length_app in Hl; cbn in Hl.
    assert (Hl' : List.length Ms' = List.length C) by lia; clear Hl.
    assert (Hti : tele_insts (ce_ass A :: C) Id (Ms' ++ M :: nil) = tele_insts C Id Ms' ++ A[sb_of_list Id Ms'] :: nil).
    { change (ce_ass A :: C) with ((ce_ass A :: nil) ++ C).
      rewrite tele_insts_app by (try exact HCa'; lia); reflexivity. }
    assert (HlT : List.length (tele_insts C Id Ms') = List.length C) by (rewrite length_tele_insts by exact HCa'; lia).
    assert (HMs' : forall k N T, nth_error Ms' k = Some N -> nth_error (tele_insts C Id Ms') k = Some T -> Γ ⊨ N : T).
    { intros k N T HN HT.
      assert (Hk : k < List.length C) by (rewrite <- HlT; apply List.nth_error_Some; congruence).
      apply (HMs k); [ rewrite List.nth_error_app1 by lia; exact HN | rewrite Hti, List.nth_error_app1 by lia; exact HT ]. }
    assert (HTs' : forall k T, nth_error (tele_insts C Id Ms') k = Some T -> exists i : nat, Γ ⊨ T : Typeω@i).
    { intros k T HT.
      assert (Hk : k < List.length C) by (rewrite <- HlT; apply List.nth_error_Some; congruence).
      apply (HTs k); rewrite Hti, List.nth_error_app1 by lia; exact HT. }
    destruct (IH Γ Ms' RΓ HCa' HC' HΓ ltac:(lia) HMs' HTs' HRΓ _ Hρ) as (ms' & Hms' & Hev').
    (** The last argument, at its relevant instantiated type *)
    assert (HM : Γ ⊨ M : A[sb_of_list Id Ms']).
    { apply (HMs (List.length C)); [ rewrite List.nth_error_app2, Hl', Nat.sub_diag by lia; reflexivity |].
      rewrite Hti, List.nth_error_app2, HlT, Nat.sub_diag by lia; reflexivity. }
    destruct (HTs (List.length C) (A[sb_of_list Id Ms']) ltac:(rewrite Hti, List.nth_error_app2, HlT, Nat.sub_diag by lia; reflexivity))
      as [i HAi].
    pose proof (rel_exp_of_typ_relevant_at HRΓ HAi _ _ Hρ) as (a & Ea & Hra).
    destruct (rel_exp_under_ctx_simple_at_relevant HRΓ HM _ _ Hρ (ex_intro _ a (conj Ea Hra))) as (m & _ & Hm & _ & _).
    (** The parameter's type at the arguments before is relevant too *)
    destruct (closed_app_sem C Γ HCa' HC' HΓ) as [HCΓ _].
    destruct (rel_ctx_wf_per_ctx_env HCΓ) as [RCΓ HRCΓ].
    pose proof (gsub_valid (gsub_closed_inst _ _ _ HCa' HC' HΓ Hl' HMs')) as Hσ.
    pose proof (closed_app_valid _ _ _ _ _ HCa' HC' HΓ HA) as HAΓ.
    destruct (rel_type_of_sort HS HAΓ) as [j HAt].
    pose proof (rel_sub_under_ctx_at' Hσ HRΓ HRCΓ _ _ _ _ Hρ Hev' Hev') as Hρσ.
    destruct (rel_type_inversion_simple_at HRCΓ HAt _ _ Hρσ) as (a' & _ & Ea' & _ & _).
    pose proof (rel_type_sub_relevance HS HAΓ Hσ HRΓ Hρ Hev' Ea Ea') as Hrel.
    exists (ms' ++ m :: nil); split; [ eapply eval_exps_app; [ exact Hms' | econstructor; [ exact Hm | constructor ] ] |].
    rewrite sb_of_list_app, env_args_snoc; cbn [sb_of_list List.app].
    apply eval_sub_extend; [ exact Hev' | | exact Hm ].
    intros Hp.
    apply (head_propositional_iff (e := ce_ass A) HRCΓ eq_refl (rel_type_inversion_simple_at HRCΓ HAt) Hρσ Ea') in Hp.
    congruence.
Qed.

(** Arguments valid at a closed telescope make environments of it, at
    related environments, over any bases. *)
Lemma closed_inst_env : forall C Γ Ms RΓ, tele_ass C -> ⊨ C -> ⊨ Γ -> List.length Ms = List.length C ->
    (forall k N T, nth_error Ms k = Some N -> nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    (forall k T, nth_error (tele_insts C Id Ms) k = Some T -> exists i : nat, Γ ⊨ T : Typeω@i) ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> forall ρ ρ', RΓ ρ ρ' ->
    exists ms ms' RC RCΓ, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\ ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ' ↘ ms' /\
      EF C ≈ C ∈ per_ctx_env ↘ RC /\ EF C ++ Γ ≈ C ++ Γ ∈ per_ctx_env ↘ RCΓ /\
      RCΓ (env_args ρ ms) (env_args ρ' ms') /\ (forall B1 B2, RC (env_args B1 ms) (env_args B2 ms')) /\
      List.length ms = List.length C /\ List.length ms' = List.length C.
Proof.
  intros * HCa HC HΓ Hl HMs HTs HRΓ ρ ρ' Hρ.
  assert (HP : PER RΓ) by (eapply per_env_PER; exact HRΓ).
  pose proof (gsub_closed_inst _ _ _ HCa HC HΓ Hl HMs) as Hg.
  pose proof (gsub_valid Hg) as Hσ.
  destruct (closed_app_sem C Γ HCa HC HΓ) as [HCΓ Hres].
  destruct (rel_ctx_wf_per_ctx_env HC) as [RC HRC].
  destruct (rel_ctx_wf_per_ctx_env HCΓ) as [RCΓ HRCΓ].
  destruct (closed_inst_eval _ _ _ _ HCa HC HΓ Hl HMs HTs HRΓ ρ ltac:(etransitivity; [ exact Hρ | symmetry; exact Hρ ]))
    as (ms & Hms & Hev).
  destruct (closed_inst_eval _ _ _ _ HCa HC HΓ Hl HMs HTs HRΓ ρ' ltac:(etransitivity; [ symmetry; exact Hρ | exact Hρ ]))
    as (ms' & Hms' & Hev').
  pose proof (rel_sub_under_ctx_at' Hσ HRΓ HRCΓ _ _ _ _ Hρ Hev Hev') as Hρσ.
  assert (Hlm : List.length ms = List.length C) by (rewrite (eval_exps_length _ _ _ Hms); exact Hl).
  assert (Hlm' : List.length ms' = List.length C) by (rewrite (eval_exps_length _ _ _ Hms'); exact Hl).
  exists ms, ms', RC, RCΓ; repeat split; try assumption.
  intros B1 B2; eapply closed_env_base; [ exact HCa | exact HC | exact HRC | exact Hlm | exact Hlm' |].
  exact (Hres _ _ HRC HRCΓ _ _ Hρσ).
Qed.

(** A type of either sort over a closed telescope, at valid arguments of
    relevant instantiated types. *)
Lemma closed_inst_typ : forall C Γ Ms X S RΓ, tele_ass C -> ⊨ C -> ⊨ Γ -> List.length Ms = List.length C ->
    (forall k N T, nth_error Ms k = Some N -> nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    (forall k T, nth_error (tele_insts C Id Ms) k = Some T -> exists i : nat, Γ ⊨ T : Typeω@i) ->
    type_sort S -> C ⊨ X : S -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> forall ρ, RΓ ρ ρ ->
    exists ms a b i R, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\ ⟦ X[sb_of_list Id Ms] ⟧ ρ ↘ a /\
      ⟦ X ⟧ env_args nil ms ↘ b /\ per_univ_elem i R a b.
Proof.
  intros * HCa HC HΓ Hl HMs HTs HS HX HRΓ ρ Hρ.
  destruct (closed_inst_env _ _ _ _ HCa HC HΓ Hl HMs HTs HRΓ _ _ Hρ) as (ms & ms' & RC & RCΓ & Hms & Hms' & HRC & HRCΓ & Hρσ & Hbase & _).
  pose proof (@functional_eval gc_deps gc_stack) as Hfe; destruct Hfe as (_ & _ & Hfs & _).
  pose proof (Hfs _ _ _ Hms _ Hms') as <-.
  pose proof (gsub_valid (gsub_closed_inst _ _ _ HCa HC HΓ Hl HMs)) as Hσ.
  destruct (closed_inst_eval _ _ _ _ HCa HC HΓ Hl HMs HTs HRΓ _ Hρ) as (ms0 & Hms0 & Hev).
  pose proof (Hfs _ _ _ Hms0 _ Hms) as ->.
  destruct (rel_type_of_sort HS (closed_app_valid _ _ _ _ _ HCa HC HΓ HX)) as [i HXΓ].
  pose proof (rel_type_inversion HXΓ) as [R0 [HΔ0 HXgen]].
  destruct (HXgen _ _ HRΓ _ _ (rel_sub_under_ctx_refl_left Hσ) _ _ _ _ Hρ Hev Hev) as [a a2 a3 a4 Ha Ha2 _ _ ([R1 HR1] & _)].
  destruct (rel_type_of_sort HS HX) as [i' HXt].
  destruct (rel_type_inversion_simple_at HRC HXt _ _ (Hbase ρ nil)) as (a3' & b & Ha3 & Hb & [R2 HR2]).
  functional_eval_rewrite_clear.
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR1 HR2) as (R & HR & _).
  exists ms, a, b; eexists; exists R; repeat split; eassumption.
Qed.

(** A term of a relevant type over a closed telescope, at valid arguments
    of relevant instantiated types. *)
Lemma closed_inst_exp : forall C Γ Ms M X k RΓ, tele_ass C -> ⊨ C -> ⊨ Γ -> List.length Ms = List.length C ->
    (forall k N T, nth_error Ms k = Some N -> nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    (forall k T, nth_error (tele_insts C Id Ms) k = Some T -> exists i : nat, Γ ⊨ T : Typeω@i) ->
    C ⊨ X : Typeω@k -> C ⊨ M : X -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> forall ρ, RΓ ρ ρ ->
    exists ms m n a i R, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\ ⟦ M[sb_of_list Id Ms] ⟧ ρ ↘ m /\
      ⟦ M ⟧ env_args nil ms ↘ n /\ ⟦ X[sb_of_list Id Ms] ⟧ ρ ↘ a /\ per_univ_elem i R a a /\ R m n.
Proof.
  intros * HCa HC HΓ Hl HMs HTs HX HM HRΓ ρ Hρ.
  destruct (closed_inst_env _ _ _ _ HCa HC HΓ Hl HMs HTs HRΓ _ _ Hρ) as (ms & ms' & RC & RCΓ & Hms & Hms' & HRC & HRCΓ & Hρσ & Hbase & _).
  pose proof (@functional_eval gc_deps gc_stack) as Hfe; destruct Hfe as (_ & _ & Hfs & _).
  pose proof (Hfs _ _ _ Hms _ Hms') as <-.
  pose proof (gsub_valid (gsub_closed_inst _ _ _ HCa HC HΓ Hl HMs)) as Hσ.
  destruct (closed_inst_eval _ _ _ _ HCa HC HΓ Hl HMs HTs HRΓ _ Hρ) as (ms0 & Hms0 & Hev).
  pose proof (Hfs _ _ _ Hms0 _ Hms) as ->.
  pose proof (closed_app_valid _ _ _ _ _ HCa HC HΓ HM) as HMΓ.
  pose proof (closed_app_valid _ _ _ _ _ HCa HC HΓ HX) as HXΓ.
  destruct (valid_inst _ _ _ _ _ _ _ HMΓ HXΓ Hσ HRΓ _ _ Hρ Hev)
    as (m & m2 & a2 & i & R1 & Hm & Hm2 & Ha2 & HR1 & Hmm).
  destruct (valid_at _ _ _ _ _ HM HX HRC _ _ (Hbase ρ nil)) as (m2' & n & a2' & i' & R2 & Hm2' & Hn & Ha2' & HR2 & Hmn).
  functional_eval_rewrite_clear.
  destruct (valid_typ_inst _ _ _ _ _ _ HXΓ Hσ HRΓ _ _ Hρ Hev)
    as (a & b2 & Ha & Hb2 & [R0 HR0]).
  set (j := k).
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
    destruct (pi_elements_app _ _ _ _ _ _ (proj1 (HEq g g') Hg) _ _ Hcc) as [g1 g1' Hg1 Hg1' Hgg].
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
    (exists l, rel_params_relevant nil T l) ->
    ⟦ ctx_pi T A0 ⟧ nil ↘ e -> per_univ_elem j E e e -> E g g -> global_member_value gc_deps gc_stack p x g ->
    forall Tin Tout args, T = Tin ++ Tout -> List.length args = List.length Tout ->
      per_gargs (rev T) nil nil args args ->
      exists a i R, ⟦ ctx_pi Tin A0 ⟧ env_args nil args ↘ a /\ per_univ_elem i R a a /\ dmod_has_mem (dm_global p args) x R /\
        (** the stored value applied to the arguments is related to the member *)
        forall v, $*| g & args | gc_deps ⍮ gc_stack ↘ v -> exists r, dm_global p args ·ₜ x gc_deps ⍮ gc_stack ↘ r /\ R v r.
Proof.
  intros * Hm HT HTs [iA HA0] [lT HTrel] He HE Hgg Hg Tin.
  assert (HeT : ⟦ ctx_pi (rev (rev T)) A0 ⟧ nil ↘ e) by (rewrite rev_involutive; exact He).
  induction Tin as [| e1 Tin0 IH] using rev_ind; intros Tout args ET Hl Hargs; cbn [List.app] in ET.
  - subst Tout.
    destruct (apps_rel_gargs _ _ _ _ _ _ _ _ _ _ _ _ Hargs HeT HeT HE Hgg) as (v & v' & b & b' & R & Hv & Hv' & Hb & Hb' & HR & Hvv).
    rewrite List.skipn_all2 in Hb, Hb' by (rewrite length_rev; lia); cbn [rev ctx_pi] in Hb, Hb'.
    functional_eval_rewrite_clear.
    pose proof (functional_eval_apps _ _ _ _ Hv Hv') as <-.
    exists b, j, R; cbn [ctx_pi]; split; [ exact Hb | split; [ exact HR |] ].
    (** the arguments fill the telescope *)
    assert (Hs1 : module_saturated gc_deps gc_stack p args)
      by (intros T' Φ' Hm'; rewrite Hm in Hm'; injection Hm' as <- <-; lia).
    split.
    2:{ intros v0 Hv0; pose proof (functional_eval_apps _ _ _ _ Hv0 Hv) as ->.
        exists v; split; [ eapply eval_sel_global_apps; [ exact Hs1 | exact Hg | exact Hv ] | exact Hvv ]. }
    intros h Hh.
    inversion Hh as [p0 T0 oD0 args0 args0' Hm0 Hl0 Hg0 | | ? ? ? ? ? Rf Hpf Hpf' _ _ _ _]; subst.
    + rewrite Hm in Hm0; injection Hm0 as <- <-.
      destruct (apps_rel_gargs _ _ _ _ _ _ _ _ _ _ _ _ Hg0 HeT HeT HE Hgg) as (u & u' & c & c' & R1 & Hu & Hu' & Hc & Hc' & HR1 & Huu).
      rewrite List.skipn_all2 in Hc, Hc' by (rewrite length_rev; lia); cbn [rev ctx_pi] in Hc, Hc'.
      functional_eval_rewrite_clear.
      pose proof (functional_eval_apps _ _ _ _ Hu' Hv) as ->.
      assert (E1 : R1 <~> R) by (eapply per_univ_elem_left_irrel; [ exact HR1 | exact HR ]).
      assert (Hs0 : module_saturated gc_deps gc_stack p args0)
        by (intros T' Φ' Hm'; rewrite Hm in Hm'; injection Hm' as <- <-; lia).
      exists u v; [ eapply eval_sel_global_apps; [ exact Hs0 | exact Hg | exact Hu ]
                  | eapply eval_sel_global_apps; [ exact Hs1 | exact Hg | exact Hv ]
                  | apply E1; exact Huu ].
    + exfalso; destruct (next_param_global_lt _ _ _ Hpf') as (T1 & oT1 & Hm1 & Hlt).
      rewrite Hm in Hm1; injection Hm1 as <- <-; lia.
  - (* one more parameter missing *)
    pose proof HT as HT0; rewrite ET in HT0.
    destruct (tele_ass_app_inv _ _ HT0) as [HT1 _].
    destruct (tele_ass_app_inv _ _ HT1) as [_ He1]; inversion He1 as [| ? ? [A1 HA1e] _]; subst e1; subst T.
    rewrite <- app_assoc in Hm, HTs, HA0, HeT, Hargs, IH, HT; cbn [List.app] in Hm, HTs, HA0, HeT, Hargs, IH, HT.
    pose proof (rel_ctx_wf_app_r _ _ HTs) as HA1T.
    (** the missing parameter is relevant *)
    pose proof (HTrel Tin0 A1 Tout ltac:(rewrite <- app_assoc; reflexivity)) as HA1; rewrite app_nil_r in HA1.
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
    assert (Hnp : next_param (dm_global p args) a1) by (econstructor; [ exact Hm | exact Hn | exact Ha1 ]).
    destruct (apps_rel_gargs _ _ _ _ _ _ _ _ _ _ _ _ Hargs HeT HeT HE Hgg) as (v & v' & b0 & b0' & R0 & Hv & Hv' & Hb0 & Hb0' & HR0 & Hvv).
    assert (Hsk : rev (skipn (List.length args) (rev (Tin0 ++ ce_ass A1 :: Tout))) = Tin0 ++ ce_ass A1 :: nil).
    { rewrite rev_app_distr; cbn [rev List.app]; rewrite <- app_assoc.
      rewrite skipn_app, skipn_all2 by (rewrite length_rev; lia).
      rewrite length_rev, Hl, Nat.sub_diag; cbn [skipn List.app].
      cbn [rev]; rewrite rev_involutive; reflexivity. }
    rewrite Hsk, ctx_pi_app in Hb0, Hb0'; cbn [ctx_pi] in Hb0, Hb0'.
    functional_eval_rewrite_clear.
    pose proof (functional_eval_apps _ _ _ _ Hv Hv') as <-.
    assert (Hkk : per_dmod (dm_global p args) (dm_global p args))
      by (eapply gval_rel; [ exact Hm | exact HT | exact HTs | reflexivity | rewrite length_app; cbn; lia | exact Hargs ]).
    assert (Hra1 : domain_relevance a1 = relevant).
    { destruct (rel_exp_of_typ_relevant_at HRo HA1 _ _ Hρ) as (a'' & Ea'' & Hr'').
      assert (a'' = a1) as -> by (eapply functional_eval_exp; eassumption); exact Hr''. }
    (** the step to one more argument *)
    assert (Hcodh : forall j1 Rc c, per_univ_elem j1 Rc a1 a1 -> Rc c c -> forall kc b,
               $ᵐ| dm_global p args & c | gc_deps ⍮ gc_stack ↘ kc -> ⟦ ctx_pi Tin0 A0 ⟧ env_args nil args ↦ c ↘ b ->
               exists i' Rb, per_univ_elem i' Rb b b /\ dmod_has_mem kc x Rb /\
                 forall v0, $*| g & args ++ c :: nil | gc_deps ⍮ gc_stack ↘ v0 ->
                   exists r, kc ·ₜ x gc_deps ⍮ gc_stack ↘ r /\ Rb v0 r).
    { intros j1 Rc c HRc Hc kc b Hkc Hb.
      inversion Hkc; subst.
      assert (HRa' : Rc <~> Ra) by (eapply per_univ_elem_right_irrel; [ exact HRc | exact HRa ]).
      destruct (IH (ce_ass A1 :: Tout) (args ++ c :: nil) eq_refl ltac:(rewrite length_app; cbn; lia))
        as (b' & i' & Rb & Hb' & HRb & Hmt & Hred).
      { rewrite rev_app_distr; cbn [rev List.app].
        rewrite <- (app_nil_r (args ++ c :: nil)).
        apply per_gargs_app_intro; [ rewrite !length_app, length_rev; cbn; lia | | constructor ].
        eapply (per_gargs_snoc _ _ _ _ _ _ _ _ _ Ra); [ rewrite length_rev; exact Hl | exact Hargs0 | econstructor; eassumption |].
        apply HRa'; exact Hc. }
      rewrite env_args_snoc in Hb'.
      pose proof (functional_eval_exp _ _ _ _ Hb Hb') as <-.
      exists i', Rb; split; [ exact HRb | split; [ exact Hmt | exact Hred ] ]. }
    assert (Hsel : dm_global p args ·ₜ x gc_deps ⍮ gc_stack ↘ d_member (dm_global p args) (x :: nil))
      by (eapply eval_sel_global_unsat; [ exact Hm | rewrite length_app; cbn; lia ]).
    split.
    + eapply dmod_has_mem_fun; [ exact Hnp | exact Hkk | exact HRP | eexists; eexists; exact HRa | exact Hra1 | | eexists; exact Hsel ].
      intros j1 Rc c HRc Hc kc b Hkc Hb.
      destruct (Hcodh _ _ _ HRc Hc _ _ Hkc Hb) as (i' & Rb & HRb & Hmt & _).
      exists i', Rb; split; assumption.
    + (** the stored value at the arguments, against the member closure *)
      intros v0 Hv0; pose proof (functional_eval_apps _ _ _ _ Hv0 Hv) as ->.
      exists (d_member (dm_global p args) (x :: nil)); split; [ exact Hsel |].
      assert (ER : R0 <~> RP) by (eapply per_univ_elem_left_irrel; [ exact HR0 | exact HRP ]).
      destruct (per_univ_elem_pi_inv HRP) as (in_rel & out_rel & Hin & Hout & HEq).
      assert (Hvv' : RP v v) by (apply ER; exact Hvv).
      pose proof (proj1 (HEq v v) Hvv') as Hpe.
      eapply red_fun; [ exact Hnp | exact HRP | eexists; eexists; exact HRa | exact Hkk | exact Hsel | exact Hra1
                      | rewrite (pi_elements_left _ _ _ _ _ _ Hpe); exact Hra1 |].
      intros j1 Rc c HRc Hc kc b Hkc Hb.
      destruct (Hcodh _ _ _ HRc Hc _ _ Hkc Hb) as (i' & Rb & HRb & Hmt & Hred).
      assert (HPin : PER in_rel) by (eapply per_elem_PER; exact Hin).
      assert (Ein : Rc <~> in_rel) by (eapply per_univ_elem_right_irrel; [ exact HRc | exact Hin ]).
      destruct (pi_elements_app _ _ _ _ _ _ Hpe c c (proj1 (Ein _ _) Hc)) as [fc fc' Hfc Hfc' _].
      assert (Hapc : $*| g & args ++ c :: nil | gc_deps ⍮ gc_stack ↘ fc)
        by (apply eval_apps_app; exists v; split; [ exact Hv | econstructor; [ exact Hfc | constructor ] ]).
      destruct (Hred _ Hapc) as (r & Hr & Hfr).
      exists i', Rb, fc, r; repeat split; assumption.
Qed.

(** A term over a telescope, abstracted, applied to arguments related at
    the telescope: the term at them.  The domains of the [λ]s are the
    telescope's types, which evaluate there. *)
Lemma eval_ctx_fn_apps : forall T ρ ρ' M ns ns' r, tele_ass T -> per_gargs (rev T) ρ ρ' ns ns' ->
    List.length ns = List.length T ->
    ⟦ M ⟧ env_args ρ ns ↘ r -> exists f, ⟦ ctx_fn T M ⟧ ρ ↘ f /\ $*| f & ns | gc_deps ⍮ gc_stack ↘ r.
Proof.
  induction T as [| e T0 IH] using rev_ind; intros * HT Hg Hl HM.
  - destruct ns; cbn in Hl; [| discriminate ]; exists r; split; [ exact HM | constructor ].
  - destruct (tele_ass_app_inv _ _ HT) as [HT0 He]; inversion He as [| ? ? [A ->] _]; subst.
    destruct ns as [| n ns0]; [ rewrite length_app in Hl; cbn in Hl; lia |].
    rewrite length_app in Hl; cbn in Hl.
    rewrite rev_app_distr in Hg; cbn [rev List.app] in Hg.
    inversion Hg; subst.
    lazymatch goal with H : per_gargs (rev T0) _ _ _ _ |- _ => rename H into Hg0 end.
    lazymatch goal with H : PER.Definitions.rel_typ _ _ _ _ _ _ |- _ => destruct H as [a a2 Ea _ _] end.
    change (env_args ρ (n :: ns0)) with (env_args (ρ ↦ n) ns0) in HM.
    destruct (IH _ _ _ ns0 _ _ HT0 Hg0 ltac:(lia) HM) as (f0 & Hf0 & Ha0).
    rewrite ctx_fn_app; cbn [ctx_fn].
    exists (λᵈ a ρ (ctx_fn T0 M)); split; [ constructor; exact Ea | econstructor; [ constructor; exact Hf0 | exact Ha0 ] ].
Qed.

(** The arguments of a filed module valid against its telescope are related
    to themselves at it, at any environment. *)
Lemma valid_args_gargs : forall Γ T Ns RΓ, ⊨ T -> ⊨ Γ -> valid_args Γ T Ns -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    forall ρ ρ', RΓ ρ ρ' -> exists ns ns', ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns /\ ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ' ↘ ns' /\
      per_gargs (rev T) nil nil ns ns'.
Proof.
  intros * HT HΓ [T1 T2 -> Hlen HTa2 HTs2 HNs HNr] HR ρ ρ' Hρ.
  pose proof (rel_ctx_wf_app_r _ _ HT) as HT2.
  destruct (closed_inst_env _ _ _ _ HTa2 HT2 HΓ (eq_sym Hlen) HNs HNr HR _ _ Hρ)
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
  destruct (HM _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [Rel [HT [Hp | [m1 m2 m3 m4 H1 H2 H3 H4 Hc]]]].
  { exists Rel; split; [ exact HT | left; exact Hp ]. }
  exists Rel; split; [ exact HT | right ].
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

Lemma me_noargs_mems : forall pre H, me_noargs H -> me_noargs (me_mems H pre).
Proof. induction pre as [| y pre IH]; intros H Hn; cbn [me_mems]; [ exact Hn | apply IH; exact Hn ]. Qed.

(** The member closure of a global module lacking parameters, applied to
    arguments for at most the parameters it lacks: it takes relevant
    arguments at every step, a member closure until the module is
    saturated, so the arguments are all evaluated. *)
Lemma eval_app_args_member_iff : forall p T Φ x, gc_loc gc_deps gc_stack p = Some (T, Φ) ->
    forall Ns args ρ r, List.length args < List.length T -> List.length args + List.length Ns <= List.length T ->
    eval_app_args gc_deps gc_stack (d_member (dm_global p args) (x :: nil)) Ns ρ r <->
    exists ns, ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns /\ $*| d_member (dm_global p args) (x :: nil) & ns | gc_deps ⍮ gc_stack ↘ r.
Proof.
  intros * Hl.
  (** applying the closure to one more argument selects from the module given it *)
  assert (Hstep : forall args n g, $| d_member (dm_global p args) (x :: nil) & n | gc_deps ⍮ gc_stack ↘ g ->
            dm_global p (args ++ n :: nil) ·ₜ x gc_deps ⍮ gc_stack ↘ g).
  { intros * Ha; inversion Ha; subst.
    lazymatch goal with H : $ᵐ| _ & _ | _ ⍮ _ ↘ _ |- _ => inversion H; subst end.
    lazymatch goal with H : _ ·ₜ* _ _ ⍮ _ ↘ _ |- _ => inversion H; subst end; [ assumption |].
    lazymatch goal with H : _ ·ₜ* nil _ ⍮ _ ↘ _ |- _ => inversion H end. }
  induction Ns as [| N Ns IH]; intros * Hlt Hle; split.
  - intros H; inversion H; subst; exists nil; split; constructor.
  - intros (ns & Hns & Ha); inversion Hns; subst; inversion Ha; subst; constructor.
  - intros H; inversion H; subst; [| cbn in *; discriminate ].
    lazymatch goal with Ha : $| _ & ?n | _ ⍮ _ ↘ ?g, Hn : ⟦ N ⟧ _ ⍮ _ ⍮ _ ↘ ?n, Hrest : eval_app_args _ _ ?g Ns _ _ |- _ =>
      pose proof (Hstep _ _ _ Ha) as Hs1;
      destruct (Nat.lt_ge_cases (List.length (args ++ n :: nil)) (List.length T)) as [Hlt' | Hge];
      [ pose proof (eval_sel_global_unsat_inv _ _ _ _ _ _ _ _ Hl Hlt' Hs1) as ->;
        apply IH in Hrest as (ns & Hns & Hap); [| exact Hlt' | rewrite length_app; cbn in *; lia ];
        exists (n :: ns); split; [ econstructor; eassumption | econstructor; eassumption ]
      | destruct Ns as [| N1 Ns1]; [| rewrite length_app in Hge; cbn in *; lia ];
        inversion Hrest; subst;
        exists (n :: nil); split; [ econstructor; [ exact Hn | constructor ] | econstructor; [ exact Ha | constructor ] ] ]
    end.
  - intros (ns & Hns & Hap); inversion Hns as [| ? ? n ? ns0 Hn Hns0]; subst.
    inversion Hap as [| ? ? g ? ? Ha Hrest]; subst.
    eapply eval_app_args_relevant; [ reflexivity | exact Hn | exact Ha |].
    pose proof (Hstep _ _ _ Ha) as Hs1.
    destruct (Nat.lt_ge_cases (List.length (args ++ n :: nil)) (List.length T)) as [Hlt' | Hge].
    + pose proof (eval_sel_global_unsat_inv _ _ _ _ _ _ _ _ Hl Hlt' Hs1) as ->.
      apply IH; [ exact Hlt' | rewrite length_app; cbn in *; lia | exists ns0; split; assumption ].
    + destruct Ns as [| N1 Ns1]; [| rewrite length_app in Hge; cbn in *; lia ].
      inversion Hns0; subst; inversion Hrest; subst; constructor.
Qed.

(** A member of a filed module at arguments for at most its telescope is
    the member of the module applied to the arguments. *)
Lemma eval_mem_filed : forall p T Φ Ns x ρ r, gc_loc gc_deps gc_stack p = Some (T, Φ) ->
    (forall ρ, ⟦ qname_mod p ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ dm_global p nil) -> List.length Ns <= List.length T ->
    ⟦ a_mem (me_apps (qname_mod p) Ns) x ⟧ ρ ↘ r <-> ⟦ apps (a_mem (qname_mod p) x) Ns ⟧ ρ ↘ r.
Proof.
  intros * Hl Hp HlN.
  destruct Ns as [| N0 Ns0] eqn:EN; [ cbn [me_apps apps]; reflexivity |].
  rewrite <- EN in *.
  assert (HT0 : 0 < List.length T) by (subst Ns; cbn in HlN; lia).
  assert (Hna : me_noargs (qname_mod p)) by (unfold qname_mod; apply me_noargs_mems; exact I).
  (** The member without arguments is its member closure *)
  assert (Hf : forall f, ⟦ a_mem (qname_mod p) x ⟧ ρ ↘ f <-> f = d_member (dm_global p nil) (x :: nil)).
  { intros f; rewrite (eval_mem_noargs _ _ _ _ _ _ Hna); split.
    - intros (h & Hh & Hs1).
      pose proof (functional_eval_modexp _ _ _ _ Hh (Hp ρ)) as ->.
      exact (eval_sel_global_unsat_inv gc_deps gc_stack p T Φ x nil f Hl HT0 Hs1).
    - intros ->; exists (dm_global p nil); split; [ apply Hp | eapply eval_sel_global_unsat; [ exact Hl | exact HT0 ] ]. }
  assert (Hs : modexp_spine (me_apps (qname_mod p) Ns) = (me_unit (q_unit p), Ns, q_chain p)).
  { pose proof (spine_apps Ns (qname_mod p) (me_unit (q_unit p)) nil (q_chain p)) as H; cbn [app] in H; apply H.
    unfold qname_mod; exact (spine_mems (q_chain p) (me_unit (q_unit p)) (me_unit (q_unit p)) nil eq_refl). }
  assert (Hs0 : modexp_spine (qname_mod p) = (me_unit (q_unit p), nil, q_chain p))
    by (unfold qname_mod; exact (spine_mems (q_chain p) (me_unit (q_unit p)) (me_unit (q_unit p)) nil eq_refl)).
  rewrite (eval_mem_spine _ _ _ _ _ _ _ _ _ Hs), eval_apps_exp.
  setoid_rewrite Hf.
  split.
  - intros (h & f & ns & Hh & Hc & Hns & Ha).
    assert (Hf0 : ⟦ a_mem (qname_mod p) x ⟧ ρ ↘ f)
      by (apply (eval_mem_spine _ _ _ _ _ _ _ _ _ Hs0); exists h, f, nil; repeat split; [ exact Hh | exact Hc | constructor | constructor ]).
    apply Hf in Hf0; subst f.
    exists (d_member (dm_global p nil) (x :: nil)); split; [ reflexivity |].
    apply (eval_app_args_member_iff _ _ _ _ Hl); [ exact HT0 | cbn; lia | exists ns; split; assumption ].
  - intros (f & -> & Ha).
    apply (eval_app_args_member_iff _ _ _ _ Hl) in Ha as (ns & Hns & Hap); [| exact HT0 | cbn; lia ].
    assert (Hf0 : ⟦ a_mem (qname_mod p) x ⟧ ρ ↘ d_member (dm_global p nil) (x :: nil)) by (apply Hf; reflexivity).
    apply (eval_mem_spine _ _ _ _ _ _ _ _ _ Hs0) in Hf0 as (h & f & ns0 & Hh & Hc & Hns0 & Ha0).
    inversion Hns0; subst; inversion Ha0; subst.
    exists h, (d_member (dm_global p nil) (x :: nil)), ns; repeat split; assumption.
Qed.

(** ** Filed Modules *)

Section Filed.
  Variables (Θm : gdeps) (Ξm : gstack).
  Hypothesis Hgm : ⊢ᵍ Θm ⍮ Ξm.
  Hypothesis Hgf : valid_filed_mods Θm Ξm.

Lemma eval_apps_filed : forall p T Φ Ns ρ ns, gc_loc Θm Ξm p = Some (T, Φ) ->
    ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns -> ⟦ me_apps (qname_mod p) Ns ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ dm_global p ns.
Proof.
  intros * Hl Hns; destruct (Hgf _ _ _ Hl) as [_ Hp _ _ _ _ _ _ _ _ _ _].
  exact (eval_apps_global _ _ _ nil _ _ (Hp ρ) Hns).
Qed.

Lemma filed_gval : forall p T Φ, gc_loc Θm Ξm p = Some (T, Φ) ->
    forall args args', List.length args <= List.length T -> per_gargs (rev T) nil nil args args' ->
    per_dmod (dm_global p args) (dm_global p args').
Proof.
  intros * Hl * Hle Hg; destruct (Hgf _ _ _ Hl) as [(Φ' & Hm) _ HT HTa _ _ _ _ _ _ _ _].
  exact (gval_rel _ _ _ Hm HTa HT _ _ _ eq_refl Hle Hg).
Qed.

(** The arguments of a filed module lack the next parameter of its
    telescope. *)
Lemma filed_lacks : forall Γ p T Φ L A T2 Ns, gc_loc Θm Ξm p = Some (T, Φ) -> ⊨ Γ ->
    T = L ++ ce_ass A :: T2 -> List.length Ns = List.length T2 ->
    (forall k N B, nth_error Ns k = Some N -> nth_error (tele_insts T2 Id Ns) k = Some B -> Γ ⊨ N : B) ->
    (forall k B, nth_error (tele_insts T2 Id Ns) k = Some B -> exists i : nat, Γ ⊨ B : Typeω@i) ->
    modexp_next_param Γ (me_apps (qname_mod p) Ns) A[sb_of_list Id Ns].
Proof.
  intros * Hl HΓ -> Hlen HNs HNr R HR ρ Hρ.
  destruct (Hgf _ _ _ Hl) as [(oD & Hm) Hp HT HTa HTs _ _ _ _ _ _ HTrel].
  pose proof (rel_ctx_wf_app_r _ _ HT) as HAT2.
  destruct (rel_ctx_wf_ass_inv HAT2) as (Srt & HS & HA).
  pose proof (rel_ctx_wf_tail HAT2) as HT2.
  destruct (tele_ass_app_inv _ _ HTa) as [_ HTa2]; inversion HTa2 as [| ? ? _ HTa2']; subst.
  destruct (closed_inst_typ _ _ _ _ _ _ HTa2' HT2 HΓ Hlen HNs HNr HS HA HR _ Hρ) as (ns & a & b & i & RA & Hns & Ha & Hb & HRA).
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
  intros * Hl HΓ [T1 T2 -> Hlen HTa2 HTs2 HNs HNr].
  revert T1 T2 Hl Hlen HTa2 HTs2 HNs HNr.
  induction Ns as [| N Ns IH] using rev_ind; intros * Hl Hlen HTa2 HTs2 HNs HNr.
  - destruct (Hgf _ _ _ Hl) as [_ Hp _ _ _ _ _ _ _ _ _ _].
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
    assert (HNr' : forall k B, nth_error (tele_insts T2' Id Ns) k = Some B -> exists i : nat, Γ ⊨ B : Typeω@i).
    { intros k B HB.
      assert (Hk : k < List.length Ns) by (rewrite <- HlT; apply List.nth_error_Some; congruence).
      apply (HNr k); rewrite Hti, nth_error_app1 by lia; exact HB. }
    assert (HN : Γ ⊨ N : A[sb_of_list Id Ns])
      by (apply (HNs (List.length Ns)); [ rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity
                                        | rewrite Hti, nth_error_app2, HlT, Nat.sub_diag by lia; reflexivity ]).
    destruct (HNr (List.length Ns) (A[sb_of_list Id Ns]) ltac:(rewrite Hti, nth_error_app2, HlT, Nat.sub_diag by lia; reflexivity))
      as [iA HAr].
    assert (Ex : T1 ++ ce_ass A :: T2' = (T1 ++ ce_ass A :: nil) ++ T2') by (rewrite <- app_assoc; reflexivity).
    pose proof (IH (T1 ++ ce_ass A :: nil) T2' ltac:(rewrite <- Ex; exact Hl)
                  ltac:(lia) HTa2' ltac:(cbn in HTs2; tauto) HNs' HNr') as HH.
    rewrite me_apps_snoc.
    eapply rel_modexp_under_ctx_app; [ exact HH | exact HAr | exact HN |].
    eapply filed_lacks; [ exact Hl | exact HΓ | reflexivity | lia | exact HNs' | exact HNr' ].
Qed.

Lemma mdesc_type_named_m : forall Θ' Ns M R, mdesc_type (mdesc_named Θ' Ns M R) = mdesc_type R.
Proof. intros; apply (mdesc_named_cases (fun R' => mdesc_type R' = mdesc_type R)); [| destruct R as [r A [?|] | | | ] ]; reflexivity. Qed.

Lemma mdesc_reduct_named_some : forall Θ' Ns M R N, mdesc_reduct R = Some N -> mdesc_reduct (mdesc_named Θ' Ns M R) = Some N.
Proof. intros * H; apply (mdesc_named_cases (fun R' => mdesc_reduct R' = Some N)); [ exact H | destruct R as [r A [?|] | | | ]; cbn in *; congruence ]. Qed.

(** A description read as a name keeps its tag. *)
Lemma mdesc_relevance_named : forall Θ' Ns M R, mdesc_relevance (mdesc_named Θ' Ns M R) = mdesc_relevance R.
Proof. intros; apply (mdesc_named_cases (fun R' => mdesc_relevance R' = mdesc_relevance R)); [| destruct R as [r A [?|] | | | ] ]; reflexivity. Qed.

(** The term part of a term at an argument is a term of the same tag. *)
Lemma mdesc_term_part_at_term : forall N r A om R', mdesc_term_part_at (mdesc_term r A om) N = Some R' ->
    exists A' om', R' = mdesc_term r A' om'.
Proof.
  intros * H; destruct om as [M |]; cbn [mdesc_term_part_at mdesc_at] in H;
    repeat (match type of H with context [match ?e with _ => _ end] => destruct e end); try discriminate;
    injection H as <-; eauto.
Qed.

(** So is the term part of a term at arguments. *)
Lemma mdesc_term_part_ats_term : forall Ns r A om R', mdesc_term_part_ats (mdesc_term r A om) Ns = Some R' ->
    exists A' om', R' = mdesc_term r A' om'.
Proof.
  induction Ns as [| N Ns IH]; intros * H; cbn [mdesc_term_part_ats] in H; [ injection H as <-; eauto |].
  destruct (mdesc_term_part_at (mdesc_term r A om) N) as [R0 |] eqn:E; [| discriminate ].
  destruct (mdesc_term_part_at_term _ _ _ _ _ E) as (A0 & om0 & ->); exact (IH _ _ _ _ H).
Qed.

(** A stored term part with a module part, read at arguments: its term
    part, as a transparent definition is. *)
#[local] Ltac filed_dm_read :=
  match goal with
  | Hed : edenote _ _ _ _ _ _, Ha : mdesc_ats_read _ ?Ns = Some _ |- _ =>
      inversion Hed; subst; unfold ind_former_desc, record_former_desc in Ha; cbn [mdesc_ats_read] in Ha;
      match type of Ha with
      | context [mdesc_term_part_ats (mdesc_term ?r1 ?A1 (Some ?M1)) Ns] =>
          destruct (mdesc_term_part_ats (mdesc_term r1 A1 (Some M1)) Ns) as [[r2 B [M' |] | | |] |] eqn:Et; try discriminate;
          let Er := fresh "Er" in
          destruct (mdesc_term_part_ats_term _ _ _ _ _ Et) as (? & ? & Er); injection Er as -> _ _;
          exists (mdesc_term r1 A1 (Some M1)), (mdesc_term r1 B (Some M'))
      end;
      match type of Ha with
      | context [mdesc_ats ?Rx Ns] => destruct (mdesc_ats Rx Ns) as [Rm' |]; [ injection Ha as <- | discriminate ]
      end;
      (split; [ left; do 2 eexists; split; [ reflexivity | cbn [entry_term];
                                         try (match goal with HMk : ind_member _ _ = Some _ |- _ => rewrite HMk end);
                                         reflexivity ] | split; [ eassumption |] ]);
      [ .. | rewrite !mdesc_named_fix by reflexivity; split; [ reflexivity | split; reflexivity ] ]
  end.

(** A term member of a filed module at arguments, read off its stored
    entry, or the open frame of a member's module or of a record type's
    module under it, read as its type former. *)
Lemma filed_mem_desc : forall Γ p T Φ Ns x R A, gc_loc Θm Ξm p = Some (T, Φ) ->
    mdenote Θm Ξm Γ (me_mem (me_apps (qname_mod p) Ns) x) R -> mdesc_type R = Some A ->
    exists R0 R1,
      ((exists Φ0 E0, gm_prefix_upto Φ x = Some (gm_ext Φ0 x E0) /\ entry_term (Some (qname_in p x)) E0 = Some R0) \/
       (exists pq k D Mk, gs_find_ind Ξm (qname_in p x) = Some (pq, k, D) /\ ind_member D k = Some Mk /\
          R0 = mdesc_term relevant (ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ) (Some (a_ind pq k))) \/
       (exists Rr, gs_find_record Ξm (qname_in p x) = Some Rr /\
          R0 = mdesc_term relevant (ctx_pi (record_params Rr) (record_sort Rr)) (Some (a_record (qname_in p x))))) /\
      mdesc_term_part_ats R0 Ns = Some R1 /\
      mdesc_relevance R = mdesc_relevance R1 /\
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
    split; [ reflexivity | rewrite mdesc_named_nil; split; [ reflexivity | split; reflexivity ] ]. }
  2:{ (* the open frame of a record type's module: likewise *)
    destruct Ns as [| N Ns'] using List.rev_ind; [| rewrite me_apps_snoc in Hq; discriminate ].
    cbn [me_apps] in Hq; rewrite <- qname_mod_in, mod_qname_qname_mod in Hq; injection Hq as <-.
    eexists; eexists;
      split; [ right; right; exists Rr; split; [ exact Hk | reflexivity ] |].
    split; [ reflexivity | rewrite mdesc_named_nil; split; [ reflexivity | split; reflexivity ] ]. }
  destruct (filed_denote _ _ Hgm _ _ _ Γ Ns Hgl) as (R2 & Hm2 & Hmod2).
  rewrite (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm0 _ Hm2), Hmod2 in Hmd; injection Hmd as <-.
  cbn in He; destruct (gm_prefix_upto Φ x) as [[| Φ0 z E0 | ] |] eqn:Hp; try discriminate.
  pose proof (gm_prefix_name _ _ _ _ _ Hp) as ->.
  injection He as <- <- <-; cbn [app] in Hed.
  cbn [mdesc_read] in Hr; destruct (mdesc_ats_read R1 Ns) as [R3 |] eqn:Ha; cbn in Hr; [ injection Hr as <- | discriminate ].
  rewrite mdesc_up_nil in Hty |- *.
  destruct E0 as [b pv r A0 oM | pv U | pv pq D Φd | pv Ad Md Ud | pv Rr Φr].
  - inversion Hed; subst; cbn [mdesc_ats_read] in Ha.
    do 2 eexists; split; [ left; do 2 eexists; split; reflexivity | split; [ exact (mdesc_term_part_ats_of_ats _ _ _ Ha) |] ].
    split; [ apply mdesc_relevance_named | split; reflexivity ].
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
    valid_mem Γ (me_apps (qname_mod p) Ns) x A (mdesc_reduct R) /\
    exists i : nat, Γ ⊨ A : relevance_sort (mdesc_relevance R) Typeω@i.
Proof.
  intros * Hl HΓ Hs Hm Ht.
  destruct (filed_mem_desc _ _ _ _ _ _ _ _ Hl Hm Ht) as (R0 & R1 & HR0 & Ha & HrelR & HtR & HrR).
  rewrite HtR in Ht; rewrite HrR, HrelR.
  rewrite mdesc_type_named_m in Ht.
  (* the read description is tagged as the stored one *)
  assert (HrR1 : mdesc_relevance R1 = mdesc_relevance R0).
  { assert (HR0t : exists r A om, R0 = mdesc_term r A om).
    { destruct HR0 as [(Φ0 & E & Hp & He) | [(pq & k & D & Mk & Hk & HMk & ->) | (Rr & Hk & ->)]]; [| eauto | eauto ].
      destruct E; cbn [entry_term] in He;
        repeat (match type of He with context [option_map _ ?o] => destruct o; cbn [option_map] in He end);
        try discriminate; injection He as <-; eauto. }
    destruct HR0t as (r & A1 & om & ->).
    destruct (mdesc_term_part_ats_term _ _ _ _ _ Ha) as (A2 & om2 & ->); reflexivity. }
  rewrite HrR1.
  destruct (Hgf _ _ _ Hl) as [(oD & Hmo) Hpe HT HTa HTs _ _ Hents Hfrs Hrfrs _ HTrel].
  pose proof Hs as [T1 T2 -> Hlen HTa2 HTs2 HNs HNr].
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
  pose proof (gsub_closed_inst _ _ _ HTa2 HT2 HΓ (eq_sym Hlen) HNs) as Hg.
  (** the arguments evaluate *)
  assert (HK : forall RΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> forall ρ, RΓ ρ ρ -> exists h, ⟦ K ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h).
  { intros RΓ HR ρ Hρ.
    destruct (closed_inst_eval _ _ _ _ HTa2 HT2 HΓ (eq_sym Hlen) HNs HNr HR _ Hρ) as (ns & Hns & _).
    exists (dm_global p ns); exact (eval_apps_filed _ _ _ _ _ _ Hl Hns). }
  remember (mdesc_relevance R0) as r0 eqn:Er; destruct r0.
  2:{ (* a proof member: only its type and its module's value are asked for *)
    destruct (valid_exp_under_ctx_ctx_pi_at propositional T1 T2 A0 i HT HA0) as [iX HX]; cbn [relevance_sort] in HX.
    assert (HXΓ : Γ ⊨ (ctx_pi_at propositional T1 A0)[sb_of_list Id Ns] : Propₘ)
      by (pose proof (rel_exp_under_ctx_gsub Hg (closed_app_valid _ _ _ _ _ HTa2 HT2 HΓ HX)) as H0; cbn in H0; exact H0).
    split; [| exists 0; exact HXΓ ].
    apply valid_mem_of_prop; [ exact HXΓ | intros M _; exact (rel_exp_under_ctx_proof HXΓ) | exact HK ]. }
  cbn [relevance_sort] in HA0.
  destruct (rel_exp_ctx_pi _ _ _ _ HTa1 HT HA0) as [iX HX].
  assert (HXΓ : Γ ⊨ (ctx_pi T1 A0)[sb_of_list Id Ns] : Typeω@iX)
    by (pose proof (rel_exp_under_ctx_gsub Hg (closed_app_valid _ _ _ _ _ HTa2 HT2 HΓ HX)) as H0; cbn in H0; exact H0).
  split; [| exists iX; exact HXΓ ].
  (* the member, pointwise *)
  assert (Hpt : forall RΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> forall ρ, RΓ ρ ρ ->
             exists ns a k RX, ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns /\ ⟦ (ctx_pi T1 A0)[sb_of_list Id Ns] ⟧ ρ ↘ a /\
               per_univ_elem k RX a a /\ dmod_has_mem (dm_global p ns) x RX /\ per_dmod (dm_global p ns) (dm_global p ns) /\
               per_gargs (rev T2) nil nil ns ns /\
               forall v, $*| g & ns | gc_deps ⍮ gc_stack ↘ v -> exists r, dm_global p ns ·ₜ x gc_deps ⍮ gc_stack ↘ r /\ RX v r).
  { intros RΓ HR ρ Hρ.
    destruct (closed_inst_typ _ _ _ _ _ _ HTa2 HT2 HΓ (eq_sym Hlen) HNs HNr (type_sort_universe iX) HX HR _ Hρ)
      as (ns & a & b & k & RX & Hns & Ha1 & Hbb & HRX).
    destruct (valid_args_gargs _ _ _ _ HT HΓ Hs HR _ _ Hρ) as (ns1 & ns2 & Hns1 & Hns2 & Hgs).
    pose proof (@functional_eval gc_deps gc_stack) as Hfe; destruct Hfe as (_ & _ & Hfs & _).
    pose proof (Hfs _ _ _ Hns1 _ Hns) as ->; pose proof (Hfs _ _ _ Hns2 _ Hns) as ->.
    assert (Hlns : List.length ns = List.length T2) by (rewrite (eval_exps_length _ _ _ Hns); lia).
    destruct (glob_dmod_has_mem _ _ _ _ _ _ _ _ _ Hmo HTa HT (ex_intro (fun i0 : nat => _ ⊨ _ : Typeω@i0) i HA0) HTrel
                He0 HE0 Hgg Hsel T1 T2 ns eq_refl Hlns Hgs)
      as (a' & i' & R' & Ha' & HR' & Hmt & Hred).
    functional_eval_rewrite_clear.
    assert (HPX : PER RX) by (eapply per_elem_PER; exact HRX).
    assert (ER : RX <~> R') by (eapply per_univ_elem_left_irrel; [ exact HRX | exact HR' ]).
    assert (Haa : per_univ_elem k RX a a) by (eapply per_univ_trans; [ exact HRX | apply per_univ_elem_sym; exact HRX ]).
    assert (Hgs2 : per_gargs (rev T2) nil nil ns ns)
      by (rewrite rev_app_distr in Hgs; eapply per_gargs_prefix; [ exact Hgs | rewrite length_rev; lia ]).
    exists ns, a, k, RX; repeat split; [ exact Hns | exact Ha1 | exact Haa | apply (dmod_has_mem_iff _ _ R'); [ exact Hmt | symmetry; exact ER ]
                                    | apply (filed_gval _ _ _ Hl); [ rewrite length_app; lia | exact Hgs ] | exact Hgs2 |].
    intros v Hv; destruct (Hred _ Hv) as (r & Hr & Hvr); exists r; split; [ exact Hr | apply ER; exact Hvr ]. }
  assert (HS0 : valid_mem Γ K x (ctx_pi T1 A0)[sb_of_list Id Ns] None).
  { constructor; [ exists iX; exact (rel_type_of_typ HXΓ) | discriminate |].
    intros RΓ HR ρ Hρ.
    destruct (Hpt _ HR _ Hρ) as (ns & a & k & RX & Hns & Ha1 & Haa & Hmt & _).
    apply mk_valid_mem_at with (valid_mem_at_mod := dm_global p ns) (valid_mem_at_typ := a) (valid_mem_at_lvl := k) (valid_mem_at_rel := RX); try assumption;
      [ exact (eval_apps_filed _ _ _ _ _ _ Hl Hns) | intros _; exact Hmt | intros _ ? ?; discriminate ]. }
  destruct HredR1 as [HredR1 | (M1 & HredR1 & HM1 & HevM1)].
  2:{ (* a reduct: a term over the outer parameters, instantiated *)
    rewrite (mdesc_reduct_named_some _ _ _ _ _ HredR1).
    constructor; [ exists iX; exact (rel_type_of_typ HXΓ) | |].
    + intros M HM; injection HM as <-.
      exact (rel_exp_under_ctx_gsub Hg (closed_app_valid _ _ _ _ _ HTa2 HT2 HΓ HM1)).
    + intros RΓ HR ρ Hρ.
      destruct (Hpt _ HR _ Hρ) as (ns & a & k & RX & Hns & Ha1 & Haa & Hmt & _ & Hgs2 & Hred).
      apply mk_valid_mem_at with (valid_mem_at_mod := dm_global p ns) (valid_mem_at_typ := a) (valid_mem_at_lvl := k) (valid_mem_at_rel := RX);
        [ exact (eval_apps_filed _ _ _ _ _ _ Hl Hns) | exact Ha1 | exact Haa | intros _; exact Hmt |].
      intros _ M HM; injection HM as <-.
      destruct (closed_inst_exp _ _ _ _ _ _ _ HTa2 HT2 HΓ (eq_sym Hlen) HNs HNr HX HM1 HR _ Hρ)
        as (ns' & m & n & a2 & i2 & R2 & Hns' & Hm' & Hn & Ha2 & HR2 & Hmn).
      pose proof (@functional_eval gc_deps gc_stack) as Hfe; destruct Hfe as (_ & _ & Hfs & _).
      pose proof (Hfs _ _ _ Hns' _ Hns) as ->.
      functional_eval_rewrite_clear.
      assert (Hlns : List.length ns = List.length T2) by (rewrite (eval_exps_length _ _ _ Hns); lia).
      destruct (Hred _ (HevM1 _ _ Hlns Hgs2 Hn)) as (r & Hr & Hnr).
      apply (mk_rel_mem_reduct _ _ _ _ _ m r); [ exact Hm' | exact Hr |].
      assert (E2 : R2 <~> RX) by (eapply per_univ_elem_right_irrel; [ exact HR2 | exact Haa ]).
      assert (HPX : PER RX) by (eapply per_elem_PER; exact Haa).
      etransitivity; [ apply E2; exact Hmn | exact Hnr ]. }
  - (* an axiom or an abstract definition: its name at the arguments, or,
       read bare, none *)
    destruct R1 as [r1 A1 [?|] | | |]; cbn in HredR1, HtyR1; try discriminate.
    destruct (mdesc_named_term_none nil Ns Mn r1 A1) as [(Hn & _ & HN) | Hn]; rewrite Hn; cbn [mdesc_reduct];
      [ exact HS0 |].
    assert (HlNs : List.length Ns <= List.length (T1 ++ T2)) by (rewrite length_app; lia).
    assert (Hiff : forall σ ρ r, ⟦ (a_mem K x)[σ] ⟧ ρ ↘ r <-> ⟦ Mn[σ] ⟧ ρ ↘ r).
    { intros σ ρ r; subst K Mn; cbn [exp_sub]; rewrite me_apps_sub, qname_mod_sub, apps_sub; cbn [exp_sub].
      rewrite qname_mod_sub; apply (eval_mem_filed _ _ _ _ _ _ _ Hmo Hpe); rewrite length_map; exact HlNs. }
    pose proof (filed_valid _ _ _ _ _ Hl HΓ Hs) as HKv.
    pose proof (rel_mem_of_valid_mem _ _ _ _ _ _ HKv HS0) as HKx.
    constructor; [ exists iX; exact (rel_type_of_typ HXΓ) | |].
    + intros M HM; injection HM as <-; exact (valid_exp_eval_iff _ _ _ _ HKx Hiff).
    + intros RΓ HR ρ Hρ.
      destruct (Hpt _ HR _ Hρ) as (ns & a & k & RX & Hns & Ha1 & Haa & Hmt & Hkk & _).
      apply mk_valid_mem_at with (valid_mem_at_mod := dm_global p ns) (valid_mem_at_typ := a) (valid_mem_at_lvl := k) (valid_mem_at_rel := RX);
        [ exact (eval_apps_filed _ _ _ _ _ _ Hl Hns) | exact Ha1 | exact Haa | intros _; exact Hmt |].
      intros _ M HM; injection HM as <-.
      destruct (Hmt _ Hkk) as [r r' Hr Hr' Hrr].
      pose proof (functional_eval_sel _ _ _ _ Hr Hr') as <-.
      apply (mk_rel_mem_reduct _ _ _ _ _ r r); [| exact Hr | exact Hrr ].
      rewrite <- (exp_sub_id Mn); apply Hiff; rewrite exp_sub_id.
      eapply eval_mem_of_sel; [ exact (eval_apps_filed _ _ _ _ _ _ Hl Hns) | exact Hr ].
Qed.

End Filed.

End Fixed_GCtx.
