(** * The Set Rules of the Eliminator

    At an environment of its context, the eliminator of a group at an
    element of a member's carrier has a result in the motive there: by
    induction on the group's least fixed point ([member_carrier_ind]), the
    element is built by a constructor from arguments whose recursive ones
    have results, which the branch takes, in its context, to a result in
    the motive at the constructor.

    The recursive results are functions of the arguments: along a leaf
    path, the eliminator's result at the end ([elim_result], described
    among the elements of the universe of the motives, without choice),
    under a domain the graph of the results at the argument's values, at a
    projection the results at the field ([leaf_result]). *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Weakening Substitution JudgmentSubstitution.
From Mctt.Core.SetModel.Interpretation.Global Require Import Model.
From Mctt.Core.SetModel.Cases Require Import UniverseCases PropCases ValidUnit MemberTypes Sel IndCases RecordCases.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths DescTyping MemberLemmas.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing.
Import ListNotations.

Section Eliminator.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.
  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).
  (** The global context is well formed *)
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  (** The valuation models the global context *)
  Hypothesis Hok : set_gctx_ok T γ.

(** ** Closed Contexts Read Only Their Own Entries *)

Lemma set_env_above_lt' : forall n ρ ρb x, x < n -> set_env_above n ρ ρb x = ρ x.
Proof.
  induction n as [| n IH]; intros ρ ρb x Hx; [lia |]. destruct x as [| x]; [reflexivity |]. cbn [set_env_above].
  change (set_env_extend (set_env_above n (set_env_tail ρ) ρb) (ρ 0) (S x)) with (set_env_above n (set_env_tail ρ) ρb x).
  rewrite IH by lia. reflexivity.
Qed.

Lemma set_env_above_ge' : forall n ρ ρb y, set_env_above n ρ ρb (n + y) = ρb y.
Proof. induction n as [| n IH]; intros ρ ρb y; [reflexivity |]. cbn [set_env_above Nat.add]. apply IH. Qed.

(** The values of a telescope read only its own entries. *)
Lemma set_env_values_agree : forall Δ ρ ρ', (forall x, x < List.length Δ -> ρ x = ρ' x) -> set_env_values Δ ρ = set_env_values Δ ρ'.
Proof.
  induction Δ as [| e Δ IH]; intros ρ ρ' E; [reflexivity |]. cbn [set_env_values List.length] in *.
  rewrite (IH (set_env_tail ρ) (set_env_tail ρ')); [| intros x Hx; unfold set_env_tail; apply E; lia].
  rewrite (E 0) by lia. reflexivity.
Qed.

(** A term of a closed context has one value at two environments whose
    entries in the context are equal, whatever they hold below it: both
    are read at environments holding both below the context. *)
Lemma set_interp_closed_ctx_functional : forall Δ ρ1 ρ2 M v1 v2, ctx_scoped 0 Δ -> exp_scoped (List.length Δ) M ->
    (forall x, x < List.length Δ -> set_entry_eq γ (ρ1 x) (ρ2 x)) ->
    set_env_eq γ (set_env_drop (List.length Δ) ρ1) (set_env_drop (List.length Δ) ρ1) ->
    set_env_eq γ (set_env_drop (List.length Δ) ρ2) (set_env_drop (List.length Δ) ρ2) ->
    set_interp T γ Δ ρ1 M v1 -> set_interp T γ Δ ρ2 M v2 -> set_eq v1 v2.
Proof.
  intros * HΔ HM E Ed1 Ed2 H1 H2. set (n := List.length Δ) in *.
  pose proof (wf_ctx_empty _ _ Hgw) as Hc.
  assert (Hwk : forall φ, gc_deps ⍮ gc_stack ⍮ nil ⊢ʷ φ : nil)
    by (intros φ; constructor; [exact Hc | exact Hc | intros ? ? Hl; inversion Hl | intros ? ? ? Hl; inversion Hl
                               | intros ? ? Hl; inversion Hl]).
  set (ρb := set_env_merge (set_env_drop n ρ1) (set_env_drop n ρ2)).
  assert (Hmv : forall ρ ρ' φ v, set_interp T γ Δ ρ M v -> (forall x, x < n -> ρ x = ρ' x) ->
            (forall y, ρ (n + y) = ρ' (n + φ y)) -> set_interp T γ Δ ρ' M v).
  { intros ρ ρ' φ v H Hlt Hge. rewrite <- (List.app_nil_r Δ) in H.
    pose proof (set_interp_wk T γ _ _ _ _ H Δ nil nil φ ρ' eq_refl (Hwk φ)) as H'.
    rewrite tele_closed_wk, List.app_nil_r in H' by exact HΔ. fold n in H'.
    rewrite (proj1 syn_scoped_wk_id M n (wk_qn n φ) HM (fun x Hx => wk_qn_lt n φ x Hx)) in H'.
    apply H'. intros x. destruct (Nat.lt_ge_cases x n) as [Hx | Hx].
    - rewrite wk_qn_lt by exact Hx. apply Hlt. exact Hx.
    - rewrite wk_qn_ge by exact Hx. replace x with (n + (x - n)) at 1 by lia. rewrite Hge. f_equal. lia. }
  set (ρ3 := set_env_above n ρ1 ρb). set (ρ3' := set_env_above n ρ2 ρb).
  assert (H1' : set_interp T γ Δ ρ3 M v1).
  { apply (Hmv ρ1 ρ3 (fun y => y + y) v1 H1); intros; unfold ρ3;
      [rewrite set_env_above_lt' by assumption; reflexivity | rewrite set_env_above_ge'; unfold ρb; rewrite set_env_merge_even; reflexivity]. }
  assert (H2' : set_interp T γ Δ ρ3' M v2).
  { apply (Hmv ρ2 ρ3' (fun y => S (y + y)) v2 H2); intros; unfold ρ3';
      [rewrite set_env_above_lt' by assumption; reflexivity | rewrite set_env_above_ge'; unfold ρb; rewrite set_env_merge_odd; reflexivity]. }
  apply (set_interp_functional T γ Hfn Hmods _ _ _ _ H1' ρ3' v2); [| exact H2'].
  intros x. unfold ρ3, ρ3'. destruct (Nat.lt_ge_cases x n) as [Hx | Hx].
  - rewrite !set_env_above_lt' by exact Hx. apply E. exact Hx.
  - replace x with (n + (x - n)) by lia. rewrite !set_env_above_ge'. unfold ρb, set_env_merge.
    destruct (Nat.even (x - n)); [apply Ed1 | apply Ed2].
Qed.

(** Two environments of a telescope of assumptions with equal values
    have equal entries in it. *)
Lemma set_env_in_entries_eq : forall Δ Γ0 θ1 θ2, all_assumptions Δ -> set_env_in T γ (Δ ++ Γ0) θ1 -> set_env_in T γ (Δ ++ Γ0) θ2 ->
    list_set_eq (set_env_values Δ θ1) (set_env_values Δ θ2) -> forall x, x < List.length Δ -> set_entry_eq γ (θ1 x) (θ2 x).
Proof.
  induction Δ as [| e Δ IH]; intros Γ0 θ1 θ2 Hass H1 H2 E x Hx; [cbn in Hx; lia |].
  inversion Hass as [| ? ? (κ & A & ->) Hass']; subst.
  cbn [set_env_values] in E.
  assert (Hl : List.length (set_env_values Δ (set_env_tail θ1)) = List.length (set_env_values Δ (set_env_tail θ2)))
    by (rewrite !length_set_env_values; reflexivity).
  destruct (list_set_eq_app_inv _ _ _ _ Hl E) as [E1 E2].
  destruct H1 as [Ht1 He1]. destruct H2 as [Ht2 He2].
  destruct x as [| x].
  - cbn [set_entry_rel] in He1, He2. destruct He1 as (a1 & a1' & b1 & [L1 _ _ _ _]). destruct He2 as (a2 & a2' & b2 & [L2 _ _ _ _]).
    rewrite L1, L2. rewrite L1, L2 in E2. inversion E2 as [| ? ? ? ? Ex _]; subst. constructor. exact Ex.
  - exact (IH _ _ _ Hass' Ht1 Ht2 E1 x ltac:(cbn in Hx; lia)).
Qed.

(** A term of a closed telescope of assumptions has one value at two of
    its environments with equal values. *)
Lemma closed_values_interp : forall Δ θ1 θ2 M v1 v2, ctx_scoped 0 Δ -> all_assumptions Δ -> exp_scoped (List.length Δ) M ->
    set_env_in T γ Δ θ1 -> set_env_in T γ Δ θ2 -> list_set_eq (set_env_values Δ θ1) (set_env_values Δ θ2) ->
    set_interp T γ Δ θ1 M v1 -> set_interp T γ Δ θ2 M v2 -> set_eq v1 v2.
Proof.
  intros * Hs Hass HM H1 H2 E I1 I2.
  rewrite <- (List.app_nil_r Δ) in H1, H2.
  apply (set_interp_closed_ctx_functional Δ θ1 θ2 M v1 v2 Hs HM); [exact (set_env_in_entries_eq _ _ _ _ Hass H1 H2 E) | | | exact I1 | exact I2].
  - exact (set_env_rel_drop T γ _ _ _ _ H1).
  - exact (set_env_rel_drop T γ _ _ _ _ H2).
Qed.

(** ** Pointwise Equal Environments *)

Lemma set_interp_env_ext : forall Ξ ρ ρ' M v, ⊢ gc_deps ⍮ gc_stack ⍮ Ξ -> (forall x, ρ x = ρ' x) ->
    set_interp T γ Ξ ρ M v -> set_interp T γ Ξ ρ' M v.
Proof.
  intros * Hc E H. pose proof (set_interp_wk T γ _ _ _ _ H nil Ξ Ξ wk_id ρ' eq_refl (wf_wk_id _ _ _ Hc) ltac:(intros; apply E)) as H'.
  cbn [tele_wk List.app wk_qn List.length] in H'. rewrite exp_wk_id in H'. exact H'.
Qed.

Lemma set_interp_gunit_env_ext : forall Ξ ρ ρ' U m, ⊢ gc_deps ⍮ gc_stack ⍮ Ξ -> (forall x, ρ x = ρ' x) ->
    set_interp_gunit T γ Ξ ρ U m -> set_interp_gunit T γ Ξ ρ' U m.
Proof.
  intros * Hc E H.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (set_interp_wk_all T γ))))) _ _ _ _ H nil Ξ Ξ wk_id ρ'
                (Build_wk_setting Ξ ρ nil Ξ Ξ wk_id ρ' eq_refl (wf_wk_id _ _ _ Hc) (fun x => E x))) as H'.
  cbn [tele_wk List.app wk_qn List.length] in H'. rewrite gunit_wk_id in H'. exact H'.
Qed.

Lemma set_entry_rel_ext : forall Ξ ρ ρ' ce e e', ⊢ gc_deps ⍮ gc_stack ⍮ ce :: Ξ -> (forall x, ρ x = ρ' x) ->
    set_entry_rel T γ Ξ ρ ce e e' -> set_entry_rel T γ Ξ ρ' ce e e'.
Proof.
  intros * Hc E He. pose proof (ctx_decomp_tail Hc) as Hc'.
  destruct ce as [κ A | A M | U | A M U]; cbn [set_entry_rel] in He |- *.
  - destruct He as (x & x' & a & [E1 E2 Ha Hx Ex]). exists x, x', a. constructor; try assumption.
    exact (set_interp_env_ext _ _ _ _ _ Hc' E Ha).
  - destruct He as (r0 & v & v' & w & [E1 E2 Hw Ev Ev']). exists r0, v, v', w. constructor; try assumption.
    exact (set_interp_env_ext _ _ _ _ _ Hc' E Hw).
  - destruct He as (m & m' & n & [E1 E2 Hn Em Em']). exists m, m', n. constructor; try assumption.
    exact (set_interp_gunit_env_ext _ _ _ _ _ Hc' E Hn).
  - destruct He as (v & v' & w & m & m' & n & [E1 E2 Hw Hn Ev Ev' Em Em']). exists v, v', w, m, m', n.
    constructor; try assumption; [exact (set_interp_env_ext _ _ _ _ _ Hc' E Hw) | exact (set_interp_gunit_env_ext _ _ _ _ _ Hc' E Hn)].
Qed.

(** Related environments of a well-formed context stay related at
    environments equal to them at every variable. *)
Lemma set_env_rel_ext : forall Ξ ρ1 ρ2 ρ1' ρ2', ⊢ gc_deps ⍮ gc_stack ⍮ Ξ -> (forall x, ρ1 x = ρ1' x) -> (forall x, ρ2 x = ρ2' x) ->
    set_env_rel T γ Ξ ρ1 ρ2 -> set_env_rel T γ Ξ ρ1' ρ2'.
Proof.
  induction Ξ as [| ce Ξ IH]; intros * Hc E1 E2 H.
  - intros x. rewrite <- E1, <- E2. apply H.
  - destruct H as [Ht He]. split.
    + apply (IH (set_env_tail ρ1) (set_env_tail ρ2)); [exact (ctx_decomp_tail Hc) | intros; apply E1 | intros; apply E2 | exact Ht].
    + rewrite <- E1, <- E2. eapply set_entry_rel_ext; [exact Hc | | exact He]. intros x. apply E1.
Qed.

Lemma set_env_values_resp : forall Δ ρ ρ', set_env_eq γ ρ ρ' -> list_set_eq (set_env_values Δ ρ) (set_env_values Δ ρ').
Proof.
  induction Δ as [| e Δ IH]; intros ρ ρ' E; cbn [set_env_values]; [constructor |].
  apply list_set_eq_app; [apply IH; intros x; apply E | constructor; [apply (set_entry_value_resp (γ := γ)); apply E | constructor]].
Qed.

(** ** Instances of Closed Telescopes

    A closed telescope [Ψ] over a closed base [B], instantiated in [Γ] by
    a substitution [σ] of the base: an environment of the instance reads
    one of [Ψ ++ B] ([inst_closed_env]), and grows by an element of the
    next type's reading there. *)

(** An environment with the same entries in a closed telescope of
    assumptions as one of its environments, and equal to itself below,
    is one too. *)
Lemma env_in_closed_agree : forall Δ θ1 θ2, ctx_scoped 0 Δ -> all_assumptions Δ -> set_ctx T γ Δ -> set_env_in T γ Δ θ1 ->
    (forall x, x < List.length Δ -> θ1 x = θ2 x) -> set_env_eq γ (set_env_drop (List.length Δ) θ2) (set_env_drop (List.length Δ) θ2) ->
    set_env_in T γ Δ θ2.
Proof.
  induction Δ as [| e Δ IH]; intros θ1 θ2 Hs Hass HC H1 E Ed; [exact Ed |].
  inversion Hass as [| ? ? (κ & A & ->) Hass']; subst.
  destruct Hs as [HsA Hs']. cbn [ce_scoped] in HsA. rewrite Nat.add_0_r in HsA.
  destruct HC as [HC' [FA HFA]]. destruct H1 as [Ht He].
  assert (Et : forall x, x < List.length Δ -> set_env_tail θ1 x = set_env_tail θ2 x) by (intros x Hx; apply E; cbn; lia).
  pose proof (IH _ _ Hs' Hass' HC' Ht Et Ed) as Ht2.
  split; [exact Ht2 |].
  cbn [set_entry_rel] in He |- *. destruct He as (x & x' & a & [L R Ha Hx Ex]).
  rewrite <- (E 0) by (cbn; lia). rewrite L in R. injection R as <-.
  pose proof (set_denotes_exists _ _ _ _ _ HFA _ Ht2) as Ha2.
  exists x, x, (FA (set_env_tail θ2)). constructor; [exact L | exact L | exact Ha2 | | apply set_eq_refl].
  eapply set_mem_eq_r; [apply code_carrier_resp | exact Hx].
  apply (set_interp_closed_ctx_functional Δ (set_env_tail θ1) (set_env_tail θ2) A); try assumption.
  - intros y Hy. rewrite (Et y Hy). rewrite <- (List.app_nil_r Δ) in Ht2.
    exact (set_env_rel_eq T γ _ _ _ Ht2 y).
  - rewrite <- (List.app_nil_r Δ) in Ht. exact (set_env_rel_drop T γ _ _ _ _ Ht).
Qed.

(** Extending by two lists in turn. *)
Lemma set_env_extend_kinded_app : forall vs1 vs2 κs1 κs2 ρ, List.length κs1 = List.length vs1 ->
    set_env_extend_kinded ρ (κs1 ++ κs2) (vs1 ++ vs2) = set_env_extend_kinded (set_env_extend_kinded ρ κs1 vs1) κs2 vs2.
Proof.
  induction vs1 as [| v vs1 IH]; intros vs2 [| κ κs1] κs2 ρ Hl; cbn in Hl; try discriminate; [reflexivity |].
  cbn [List.app set_env_extend_kinded List.hd List.tl]. apply IH. lia.
Qed.

Section ClosedInstances.
  Variables (Γ B : ctx) (σ : sub) (Fσ : set_env -> set_env).
  Hypotheses (Hσ : set_gsub_with T γ Γ σ (B ++ Γ) Fσ) (HΓ : set_ctx T γ Γ) (HcΓ : ⊢ gc_deps ⍮ gc_stack ⍮ Γ).

(** The environment of [Ψ ++ B] an environment of [tele_sub Ψ σ ++ Γ]
    reads. *)
Definition inst_closed_env (Ψ : ctx) (ρo : set_env) : set_env :=
  set_env_moved (List.length (Ψ ++ B)) (set_env_drop (List.length Γ)) (set_env_moved (List.length Ψ) Fσ ρo).

Lemma inst_closed_env_in : forall Ψ ρo, ctx_scoped 0 (Ψ ++ B) -> set_ctx T γ (Ψ ++ B) -> set_ctx T γ ((Ψ ++ B) ++ Γ) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Ψ ++ B -> ⊢ gc_deps ⍮ gc_stack ⍮ (Ψ ++ B) ++ Γ ->
    set_env_in T γ (tele_sub Ψ σ ++ Γ) ρo ->
    set_env_in T γ (Ψ ++ B ++ Γ) (set_env_moved (List.length Ψ) Fσ ρo) /\ set_env_in T γ (Ψ ++ B) (inst_closed_env Ψ ρo).
Proof.
  intros * Hs HC HCΓ Hc HcΓ' Hρo. rewrite <- List.app_assoc in HCΓ, HcΓ'.
  pose proof (set_env_in_moved T γ Hfn Hmods _ _ _ _ _ _ Hσ HΓ HCΓ HcΓ' Hρo) as H1. split; [exact H1 |].
  pose proof (set_gsub_drop T γ _ HcΓ) as Hd.
  rewrite List.app_assoc in H1. rewrite <- (tele_sub_closed _ (sb_of_wk (wk_shiftn (List.length Γ))) Hs) in H1.
  pose proof (set_env_in_moved T γ Hfn Hmods _ _ _ _ _ _ Hd HΓ ltac:(rewrite List.app_nil_r; exact HC)
                ltac:(rewrite List.app_nil_r; exact Hc) H1) as H2.
  rewrite List.app_nil_r in H2. exact H2.
Qed.

(** Its values: the base's at [Fσ], then the telescope's. *)
Lemma inst_closed_env_values : forall Ψ ρo,
    set_env_values (Ψ ++ B) (inst_closed_env Ψ ρo) = set_env_values B (Fσ (set_env_drop (List.length Ψ) ρo)) ++ set_env_values Ψ ρo.
Proof.
  intros Ψ ρo. rewrite set_env_values_app. f_equal.
  - apply set_env_values_agree. intros x Hx. unfold inst_closed_env, set_env_drop, set_env_moved.
    rewrite set_env_above_lt' by (rewrite List.length_app; lia). replace (List.length Ψ + x) with (List.length Ψ + x) by reflexivity.
    rewrite set_env_above_ge'. reflexivity.
  - apply set_env_values_agree. intros x Hx. unfold inst_closed_env, set_env_moved.
    rewrite set_env_above_lt' by (rewrite List.length_app; lia). rewrite set_env_above_lt' by exact Hx. reflexivity.
Qed.

(** One more assumption of the telescope, at an element of its type's
    reading at the closed environment. *)
Lemma set_env_in_inst_extend : forall Ψ κ A F ρo x,
    ctx_scoped 0 (Ψ ++ B) -> exp_scoped (List.length (Ψ ++ B)) A -> set_ctx T γ (Ψ ++ B) -> set_ctx T γ ((Ψ ++ B) ++ Γ) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Ψ ++ B -> ⊢ gc_deps ⍮ gc_stack ⍮ (Ψ ++ B) ++ Γ ->
    set_reads T γ (Ψ ++ B) A F -> set_env_in T γ (tele_sub Ψ σ ++ Γ) ρo ->
    set_mem x (code_carrier (F (set_env_values (Ψ ++ B) (inst_closed_env Ψ ρo)))) ->
    set_env_in T γ (tele_sub (ce_ass κ A :: Ψ) σ ++ Γ) (set_env_extend ρo (set_entry_term κ x)).
Proof.
  intros * Hs HA HC HCΓ Hc HcΓ' HF Hρo Hx.
  destruct (inst_closed_env_in _ _ Hs HC HCΓ Hc HcΓ' Hρo) as [H1 H2].
  set (a := F (set_env_values (Ψ ++ B) (inst_closed_env Ψ ρo))) in *.
  pose proof (HF _ H2) as Ha. fold a in Ha.
  pose proof (set_gsub_drop T γ _ HcΓ) as Hd.
  assert (Hb1 : set_env_in T γ Γ (set_env_drop (List.length (Ψ ++ B)) (set_env_moved (List.length Ψ) Fσ ρo))).
  { rewrite List.app_assoc in H1. exact (set_env_rel_drop T γ _ _ _ _ H1). }
  pose proof (set_interp_moved T γ _ _ _ _ _ _ _ _ Hd ltac:(rewrite List.app_nil_r; exact Hc) Hb1 ltac:(rewrite List.app_nil_r; exact Ha))
    as Ha1.
  rewrite (tele_sub_closed _ _ Hs), (exp_scoped_sub_id _ _ _ HA (fun x Hx => sb_qn_lt _ _ _ Hx)), <- List.app_assoc in Ha1.
  assert (Hb2 : set_env_in T γ Γ (set_env_drop (List.length Ψ) ρo)) by exact (set_env_in_drop T γ _ _ _ _ Hρo).
  pose proof (set_interp_moved T γ _ _ _ _ _ _ _ _ Hσ ltac:(rewrite <- List.app_assoc in HcΓ'; exact HcΓ') Hb2 Ha1) as Ha2.
  split; [exact Hρo |]. cbn [set_entry_rel centry_sub tele_sub]. exists x, x, a.
  constructor; [reflexivity | reflexivity | exact Ha2 | exact Hx | apply set_eq_refl].
Qed.

(** The same at a reading of the type at the closed environment. *)
Lemma set_env_in_inst_extend_at : forall Ψ κ A a ρo x,
    ctx_scoped 0 (Ψ ++ B) -> exp_scoped (List.length (Ψ ++ B)) A -> set_ctx T γ (Ψ ++ B) -> set_ctx T γ ((Ψ ++ B) ++ Γ) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Ψ ++ B -> ⊢ gc_deps ⍮ gc_stack ⍮ (Ψ ++ B) ++ Γ ->
    set_env_in T γ (tele_sub Ψ σ ++ Γ) ρo -> set_interp T γ (Ψ ++ B) (inst_closed_env Ψ ρo) A a -> set_mem x (code_carrier a) ->
    set_env_in T γ (tele_sub (ce_ass κ A :: Ψ) σ ++ Γ) (set_env_extend ρo (set_entry_term κ x)).
Proof.
  intros * Hs HA HC HCΓ Hc HcΓ' Hρo Ha Hx.
  destruct (inst_closed_env_in _ _ Hs HC HCΓ Hc HcΓ' Hρo) as [H1 H2].
  pose proof (set_gsub_drop T γ _ HcΓ) as Hd.
  assert (Hb1 : set_env_in T γ Γ (set_env_drop (List.length (Ψ ++ B)) (set_env_moved (List.length Ψ) Fσ ρo))).
  { rewrite List.app_assoc in H1. exact (set_env_rel_drop T γ _ _ _ _ H1). }
  pose proof (set_interp_moved T γ _ _ _ _ _ _ _ _ Hd ltac:(rewrite List.app_nil_r; exact Hc) Hb1 ltac:(rewrite List.app_nil_r; exact Ha))
    as Ha1.
  rewrite (tele_sub_closed _ _ Hs), (exp_scoped_sub_id _ _ _ HA (fun x Hx => sb_qn_lt _ _ _ Hx)), <- List.app_assoc in Ha1.
  assert (Hb2 : set_env_in T γ Γ (set_env_drop (List.length Ψ) ρo)) by exact (set_env_in_drop T γ _ _ _ _ Hρo).
  pose proof (set_interp_moved T γ _ _ _ _ _ _ _ _ Hσ ltac:(rewrite <- List.app_assoc in HcΓ'; exact HcΓ') Hb2 Ha1) as Ha2.
  split; [exact Hρo |]. cbn [set_entry_rel centry_sub tele_sub]. exists x, x, a.
  constructor; [reflexivity | reflexivity | exact Ha2 | exact Hx | apply set_eq_refl].
Qed.

(** An environment of the closed telescope [Ψ ++ B] whose part in [B]
    has the values [Fσ] gives at [ρ0] gives the instance's environment at
    the same values. *)
Lemma inst_env_of_closed : forall Ψ θc, ctx_scoped 0 (Ψ ++ B) -> all_assumptions Ψ -> set_ctx T γ (Ψ ++ B) ->
    set_ctx T γ ((Ψ ++ B) ++ Γ) -> ⊢ gc_deps ⍮ gc_stack ⍮ Ψ ++ B -> ⊢ gc_deps ⍮ gc_stack ⍮ (Ψ ++ B) ++ Γ ->
    set_env_in T γ (Ψ ++ B) θc -> all_assumptions B ->
    forall ρ0, set_env_in T γ Γ ρ0 -> list_set_eq (set_env_values B (Fσ ρ0)) (set_env_values B (set_env_drop (List.length Ψ) θc)) ->
    set_env_in T γ (tele_sub Ψ σ ++ Γ) (set_env_extend_kinded ρ0 (ctx_kinds Ψ) (set_env_values Ψ θc)).
Proof.
  induction Ψ as [| e Ψ IH]; intros θc Hs Hass HC HCΓ Hc HcΓ' Hθc HassB ρ0 Hρ0 Hu; [exact Hρ0 |].
  inversion Hass as [| ? ? (κ & A & ->) Hass']; subst.
  cbn [List.app] in Hs, HC, HCΓ, Hc, HcΓ', Hθc.
  destruct Hs as [HsA Hs']. cbn [ce_scoped] in HsA. rewrite Nat.add_0_r in HsA.
  destruct HC as [HC' [FA HFA]]. destruct HCΓ as [HCΓ' _].
  pose proof (ctx_decomp_tail Hc) as Hc'. pose proof (ctx_decomp_tail HcΓ') as HcΓ''.
  destruct Hθc as [Ht He].
  pose proof (IH _ Hs' Hass' HC' HCΓ' Hc' HcΓ'' Ht HassB ρ0 Hρ0 Hu) as Hρo.
  set (ρo := set_env_extend_kinded ρ0 (ctx_kinds Ψ) (set_env_values Ψ (set_env_tail θc))) in *.
  cbn [set_entry_rel] in He. destruct He as (x0 & x0' & a0 & [L0 _ Ha0 Hx0 _]).
  assert (Hlk : List.length (ctx_kinds Ψ) = List.length (set_env_values Ψ (set_env_tail θc)))
    by (rewrite length_ctx_kinds, length_set_env_values; reflexivity).
  cbn [set_env_values]. rewrite ctx_kinds_cons, set_env_extend_kinded_snoc by exact Hlk. fold ρo. cbn [centry_kind].
  rewrite L0. cbn [set_entry_value].
  destruct (inst_closed_env_in _ _ Hs' HC' HCΓ' Hc' HcΓ'' Hρo) as [_ Hin].
  pose proof (set_denotes_exists _ _ _ _ _ HFA _ Hin) as Ha.
  apply (set_env_in_inst_extend_at Ψ κ A (FA (inst_closed_env Ψ ρo)) ρo x0 Hs' HsA HC' HCΓ' Hc' HcΓ'' Hρo Ha).
  eapply set_mem_eq_r; [apply code_carrier_resp | exact Hx0].
  apply (closed_values_interp (Ψ ++ B) (set_env_tail θc) (inst_closed_env Ψ ρo) A); try assumption.
  - apply List.Forall_app. split; assumption.
  - rewrite inst_closed_env_values, set_env_values_app. apply list_set_eq_app.
    + eapply list_set_eq_trans; [apply list_set_eq_sym; exact Hu |].
      apply set_env_values_resp.
      assert (Hr : set_env_rel T γ Γ ρ0 (set_env_drop (List.length Ψ) ρo)).
      { eapply set_env_rel_ext; [exact HcΓ | intros y; reflexivity | | exact Hρ0].
        intros y. unfold set_env_drop, ρo.
        replace (List.length Ψ) with (List.length (set_env_values Ψ (set_env_tail θc))) by (rewrite length_set_env_values; reflexivity).
        rewrite set_env_extend_kinded_ge. reflexivity. }
      exact (set_env_rel_eq T γ _ _ _ (set_gsub_rel _ _ _ _ _ _ Hσ _ _ Hr)).
    + unfold ρo. rewrite set_env_values_extend_kinded by (rewrite length_set_env_values; reflexivity).
      apply list_set_eq_refl.
Qed.

End ClosedInstances.

(** ** Erasing Recursive Arguments

    The carriers read each argument after the arguments before it with the
    recursive ones erased ([arguments_fit]); the environments hold them.
    The types ignore each erasure ([set_constructor_ok_ignores]), at any
    values, so they ignore all of them. *)

(** [l] with the positions [P] erased. *)
Fixpoint erase_all (P : list nat) (l : list aczel_set) : list aczel_set :=
  match P with
  | nil => l
  | n :: P' => erase_at n (erase_all P' l)
  end.

Lemma length_erase_at : forall n l, n < List.length l -> List.length (erase_at n l) = List.length l.
Proof.
  intros n l Hn. unfold erase_at. rewrite List.length_app, List.length_firstn. cbn [List.length]. rewrite List.length_skipn. lia.
Qed.

Lemma length_erase_all : forall P l, (forall n, In n P -> n < List.length l) -> List.length (erase_all P l) = List.length l.
Proof.
  induction P as [| n P IH]; intros l HP; [reflexivity |]. cbn [erase_all].
  rewrite length_erase_at; [apply IH; intros; apply HP; right; assumption |].
  rewrite IH by (intros; apply HP; right; assumption). apply HP. left. reflexivity.
Qed.

(** A function that ignores each erasure at every list of a length
    ignores all of them. *)
Lemma erase_all_ignored : forall (F : list aczel_set -> aczel_set) N P l,
    (forall n l', In n P -> List.length l' = N -> set_eq (F l') (F (erase_at n l'))) ->
    (forall n, In n P -> n < N) -> List.length l = N -> set_eq (F l) (F (erase_all P l)).
Proof.
  intros F N P. induction P as [| n P IH]; intros l HF HP Hl; cbn [erase_all]; [apply set_eq_refl |].
  eapply set_eq_trans; [apply IH; [intros; apply HF; [right |]; assumption | intros; apply HP; right; assumption | exact Hl] |].
  apply HF; [left; reflexivity |]. rewrite length_erase_all; [exact Hl |]. intros m Hm. rewrite Hl. apply HP. right. exact Hm.
Qed.

Lemma erase_all_ignored_list : forall (F : list aczel_set -> list aczel_set) N P l,
    (forall n l', In n P -> List.length l' = N -> list_set_eq (F l') (F (erase_at n l'))) ->
    (forall n, In n P -> n < N) -> List.length l = N -> list_set_eq (F l) (F (erase_all P l)).
Proof.
  intros F N P. induction P as [| n P IH]; intros l HF HP Hl; cbn [erase_all]; [apply list_set_eq_refl |].
  eapply list_set_eq_trans; [apply IH; [intros; apply HF; [right |]; assumption | intros; apply HP; right; assumption | exact Hl] |].
  apply HF; [left; reflexivity |]. rewrite length_erase_all; [exact Hl |]. intros m Hm. rewrite Hl. apply HP. right. exact Hm.
Qed.

Lemma nth_error_erase_at : forall n l i, n < List.length l ->
    List.nth_error (erase_at n l) i = if Nat.eqb i n then Some empty_set else List.nth_error l i.
Proof.
  intros n l i Hn. unfold erase_at. destruct (Nat.lt_trichotomy i n) as [Hi | [-> | Hi]].
  - rewrite List.nth_error_app1 by (rewrite List.length_firstn; lia). rewrite List.nth_error_firstn.
    destruct (Nat.ltb_spec i n); [| lia]. destruct (Nat.eqb_spec i n); [lia | reflexivity].
  - rewrite List.nth_error_app2 by (rewrite List.length_firstn; lia). rewrite List.length_firstn, Nat.min_l by lia.
    rewrite Nat.sub_diag, Nat.eqb_refl. reflexivity.
  - rewrite List.nth_error_app2 by (rewrite List.length_firstn; lia). rewrite List.length_firstn, Nat.min_l by lia.
    destruct (i - n) as [| k] eqn:E; [lia |]. cbn [List.nth_error]. rewrite List.nth_error_skipn.
    destruct (Nat.eqb_spec i n); [lia |]. f_equal. lia.
Qed.

(** The values of arguments as the carriers read them: the recursive
    ones erased. *)
Fixpoint erase_args (sgs : list set_argument) (vals : list aczel_set) : list aczel_set :=
  match sgs, vals with
  | set_argument_plain _ _ :: sgs', v :: vals' => v :: erase_args sgs' vals'
  | set_argument_recursive _ _ _ _ :: sgs', _ :: vals' => empty_set :: erase_args sgs' vals'
  | _, _ => nil
  end.

Lemma length_erase_args : forall sgs vals, List.length sgs = List.length vals -> List.length (erase_args sgs vals) = List.length vals.
Proof. induction sgs as [| [] sgs IH]; intros [| v vals] Hl; cbn in *; try lia; rewrite IH by lia; reflexivity. Qed.

(** The [k]-th argument erased, if recursive, after the first [k]. *)
Lemma erase_args_firstn_S : forall k sgs vals g v, List.nth_error sgs k = Some g -> List.nth_error vals k = Some v ->
    erase_args (List.firstn (S k) sgs) (List.firstn (S k) vals) =
    erase_args (List.firstn k sgs) (List.firstn k vals) ++
      [match g with set_argument_plain _ _ => v | set_argument_recursive _ _ _ _ => empty_set end].
Proof.
  induction k as [| k IH]; intros [| g0 sgs] [| v0 vals] g v Hg Hv; cbn in Hg, Hv; try discriminate.
  - injection Hg as <-. injection Hv as <-. destruct g0; reflexivity.
  - change (List.firstn (S (S k)) (g0 :: sgs)) with (g0 :: List.firstn (S k) sgs).
    change (List.firstn (S (S k)) (v0 :: vals)) with (v0 :: List.firstn (S k) vals).
    change (List.firstn (S k) (g0 :: sgs)) with (g0 :: List.firstn k sgs).
    change (List.firstn (S k) (v0 :: vals)) with (v0 :: List.firstn k vals).
    destruct g0; cbn [erase_args List.app]; rewrite (IH sgs vals g v Hg Hv); reflexivity.
Qed.

Lemma erase_at_app : forall A x B, erase_at (List.length A) (A ++ x :: B) = A ++ empty_set :: B.
Proof.
  intros. unfold erase_at. rewrite List.firstn_app, Nat.sub_diag, List.firstn_all; cbn [List.firstn]. rewrite List.app_nil_r.
  rewrite List.skipn_app, List.skipn_all2 by lia. replace (S (List.length A) - List.length A) with 1 by lia. reflexivity.
Qed.

(** A reading that ignores each recursive argument before the [j]-th, at
    every list of its length, reads the values with them erased alike. *)
Lemma erase_args_ignored_gen : forall {X : Type} (R : X -> X -> Prop), (forall x, R x x) -> (forall x y z, R x y -> R y z -> R x z) ->
    forall (F : list aczel_set -> X) L0 sgs vals j,
    (forall n L' ty ds tg tp, n < j -> List.nth_error sgs n = Some (set_argument_recursive ty ds tg tp) ->
       List.length L' = List.length L0 + j -> R (F L') (F (erase_at (List.length L0 + n) L'))) ->
    j <= List.length sgs -> j <= List.length vals ->
    R (F (L0 ++ List.firstn j vals)) (F (L0 ++ erase_args (List.firstn j sgs) (List.firstn j vals))).
Proof.
  intros X R Rrefl Rtrans F L0 sgs vals j HF Hjs Hjv.
  assert (C : forall k, k <= j ->
            R (F (L0 ++ List.firstn j vals))
                   (F (L0 ++ erase_args (List.firstn k sgs) (List.firstn k vals) ++ List.skipn k (List.firstn j vals)))).
  { induction k as [| k IH]; intros Hk; [cbn; apply Rrefl |].
    eapply Rtrans; [apply IH; lia |].
    destruct (List.nth_error sgs k) as [g |] eqn:Hg; [| apply List.nth_error_None in Hg; lia].
    destruct (List.nth_error vals k) as [v |] eqn:Hv; [| apply List.nth_error_None in Hv; lia].
    assert (Hs : List.skipn k (List.firstn j vals) = v :: List.skipn (S k) (List.firstn j vals)).
    { apply skipn_nth_cons. rewrite List.nth_error_firstn. destruct (Nat.ltb_spec k j); [exact Hv | lia]. }
    rewrite Hs, (erase_args_firstn_S k sgs vals g v Hg Hv), <- List.app_assoc. cbn [List.app].
    assert (Hlk : List.length (erase_args (List.firstn k sgs) (List.firstn k vals)) = k)
      by (rewrite length_erase_args; rewrite !List.length_firstn; lia).
    destruct g as [κ ty | ty ds tg tp]; [apply Rrefl |].
    rewrite !List.app_assoc.
    set (A := L0 ++ erase_args (List.firstn k sgs) (List.firstn k vals)).
    set (Bl := List.skipn (S k) (List.firstn j vals)).
    assert (HA : List.length A = List.length L0 + k) by (unfold A; rewrite List.length_app, Hlk; reflexivity).
    rewrite <- (erase_at_app A v Bl), HA. apply (HF k _ ty ds tg tp); [lia | exact Hg |].
    rewrite List.length_app, HA. cbn [List.length]. unfold Bl. rewrite List.length_skipn, List.length_firstn. lia. }
  eapply Rtrans; [apply (C j (le_n _)) |]. rewrite List.skipn_all2 by (rewrite List.length_firstn; lia).
  rewrite List.app_nil_r. apply Rrefl.
Qed.

Lemma erase_args_ignored : forall (F : list aczel_set -> aczel_set) L0 sgs vals j,
    (forall n L' ty ds tg tp, n < j -> List.nth_error sgs n = Some (set_argument_recursive ty ds tg tp) ->
       List.length L' = List.length L0 + j -> set_eq (F L') (F (erase_at (List.length L0 + n) L'))) ->
    j <= List.length sgs -> j <= List.length vals ->
    set_eq (F (L0 ++ List.firstn j vals)) (F (L0 ++ erase_args (List.firstn j sgs) (List.firstn j vals))).
Proof. intros. apply (erase_args_ignored_gen set_eq set_eq_refl set_eq_trans); assumption. Qed.

Lemma erase_args_ignored_list : forall (F : list aczel_set -> list aczel_set) L0 sgs vals j,
    (forall n L' ty ds tg tp, n < j -> List.nth_error sgs n = Some (set_argument_recursive ty ds tg tp) ->
       List.length L' = List.length L0 + j -> list_set_eq (F L') (F (erase_at (List.length L0 + n) L'))) ->
    j <= List.length sgs -> j <= List.length vals ->
    list_set_eq (F (L0 ++ List.firstn j vals)) (F (L0 ++ erase_args (List.firstn j sgs) (List.firstn j vals))).
Proof. intros. apply (erase_args_ignored_gen list_set_eq list_set_eq_refl list_set_eq_trans); assumption. Qed.

(** [arguments_fit]'s reading of each argument. *)
Lemma arguments_fit_nth : forall G bound S pre sgs vals, arguments_fit G bound S pre sgs vals ->
    forall j g v, List.nth_error sgs j = Some g -> List.nth_error vals j = Some v ->
    match g with
    | set_argument_plain _ type => set_mem v (code_carrier (type (pre ++ erase_args (List.firstn j sgs) (List.firstn j vals))))
    | set_argument_recursive _ ds target tparams =>
        set_mem v (shape_set G bound S (pre ++ erase_args (List.firstn j sgs) (List.firstn j vals)) ds target tparams nil)
    end.
Proof.
  induction 1 as [pre | pre κ type gs a vals Ha H IH | pre type ds target tparams gs a vals Ha H IH];
    intros [| j] g v Hg Hv; cbn in Hg, Hv; try discriminate.
  - injection Hg as <-. injection Hv as <-. rewrite List.app_nil_r. exact Ha.
  - specialize (IH j g v Hg Hv). cbn [List.firstn erase_args]. rewrite <- List.app_assoc in IH. exact IH.
  - injection Hg as <-. injection Hv as <-. rewrite List.app_nil_r. exact Ha.
  - specialize (IH j g v Hg Hv). cbn [List.firstn erase_args]. rewrite <- List.app_assoc in IH. exact IH.
Qed.

(** ** The Codes of Recursive Arguments *)

Lemma list_set_eq_firstn : forall n xs ys, list_set_eq xs ys -> list_set_eq (List.firstn n xs) (List.firstn n ys).
Proof.
  induction n as [| n IH]; intros xs ys E; [constructor |]. destruct E as [| x y xs ys Exy E]; cbn; constructor; [exact Exy | apply IH; exact E].
Qed.

Lemma pi_codomain_resp : forall C C' x x', set_eq C C' -> set_eq x x' -> set_eq (pi_codomain C x) (pi_codomain C' x').
Proof.
  intros * E Ex. unfold pi_codomain, code_datum. apply set_apply_resp; [| exact Ex].
  apply pair_second_resp. apply pair_first_resp. apply pair_second_resp. exact E.
Qed.

Lemma pi_codomain_pi_code_on : forall dom F x, respects_on (code_carrier dom) F -> set_mem x (code_carrier dom) ->
    set_eq (pi_codomain (pi_code dom F) x) (F x).
Proof.
  intros dom F x HF Hx. unfold pi_codomain, pi_code.
  eapply set_eq_trans; [apply set_apply_resp; [| apply set_eq_refl] |].
  - eapply set_eq_trans; [apply pair_second_resp; apply code_datum_type_code | apply pair_second_ordered_pair].
  - apply set_apply_graph_on; assumption.
Qed.

(** Equal [Π] codes have equal domains and codomains. *)
Lemma pi_code_inj : forall a F a' F', set_eq (pi_code a F) (pi_code a' F') -> respects_on (code_carrier a) F ->
    respects_on (code_carrier a') F' -> set_eq a a' /\ forall x, set_mem x (code_carrier a) -> set_eq (F x) (F' x).
Proof.
  intros * E HF HF'. assert (Ea : set_eq a a').
  { eapply set_eq_trans; [apply set_eq_sym; apply pi_domain_pi_code |]. eapply set_eq_trans; [| apply pi_domain_pi_code].
    unfold pi_domain, code_datum. apply pair_first_resp. apply pair_first_resp. apply pair_second_resp. exact E. }
  split; [exact Ea |]. intros x Hx.
  apply (set_eq_trans _ (pi_codomain (pi_code a F) x)); [apply set_eq_sym; apply pi_codomain_pi_code_on; assumption |].
  apply (set_eq_trans _ (pi_codomain (pi_code a' F') x)); [apply pi_codomain_resp; [exact E | apply set_eq_refl] |].
  apply pi_codomain_pi_code_on; [exact HF' |]. eapply set_mem_eq_r; [apply code_carrier_resp; exact Ea | exact Hx].
Qed.

(** A function's domain is the set it is a function on. *)
Lemma function_set_domain : forall g S F, respects_set_eq_fun F -> set_mem g (function_set S F) -> set_eq (relation_domain g) S.
Proof.
  intros g S F HF Hg. apply (set_mem_function _ _ _ HF) in Hg as [Hp [Ht _]].
  apply set_eq_intro; intros z Hz.
  - unfold relation_domain in Hz. apply set_mem_family in Hz as [a E].
    destruct (Hp (aczel_element g a) (ex_intro _ a (set_eq_refl _))) as (x & y & Hx & _ & Ep).
    eapply set_mem_eq_l; [| exact Hx]. eapply set_eq_trans; [| apply set_eq_sym; exact E].
    eapply set_eq_trans; [apply set_eq_sym; apply pair_first_ordered_pair |]. apply pair_first_resp. apply set_eq_sym. exact Ep.
  - destruct (Ht z Hz) as (y & [a Ea] & _). unfold relation_domain. apply set_mem_family. exists a.
    eapply set_eq_trans; [apply set_eq_sym; apply (pair_first_ordered_pair z y) |]. apply pair_first_resp. exact Ea.
Qed.

(** Domains moved past [k] more binders, under a pattern. *)
Lemma wk_pat_repeat_false : forall k pat, wk_pat (List.repeat false k ++ pat) = wk_qn k (wk_pat pat).
Proof. induction k as [| k IH]; intros pat; cbn [List.repeat List.app wk_pat wk_qn]; [reflexivity | rewrite IH; reflexivity]. Qed.

(** The domains of a shape over the arguments before it: its domains
    moved by the pattern's renaming. *)
Lemma shape_domains_ctx_wk : forall Bs pat, shape_domains_ctx pat Bs = tele_wk (doms_ctx Bs) (wk_pat pat).
Proof.
  induction Bs as [| B Bs IH]; intros pat; cbn [shape_domains_ctx]; [reflexivity |].
  unfold doms_ctx. cbn [List.map List.rev]. fold (doms_ctx Bs). rewrite tele_wk_app, IH. cbn [tele_wk List.length wk_qn centry_wk wk_pat].
  reflexivity.
Qed.

Section ShapeCodes.
  Variable G : set_group.
  (** The carriers respect equal parameters *)
  Hypothesis HGresp : forall k ps ps', list_set_eq ps ps' -> set_eq (set_group_carrier G k ps) (set_group_carrier G k ps').

Lemma shape_code_resp : forall ds target tparams, Forall list_function_respects ds -> list_list_function_respects tparams ->
    forall pre pre' pts pts', list_set_eq pre pre' -> list_set_eq pts pts' ->
    set_eq (shape_code G ds target tparams pre pts) (shape_code G ds target tparams pre' pts').
Proof.
  intros ds target tparams Hds Htp. induction Hds as [| d ds Hd Hds IH]; intros pre pre' pts pts' Epre Epts; cbn [shape_code].
  - apply type_code_resp; [apply set_eq_refl |]. apply HGresp. apply list_set_eq_app;
      [apply list_set_eq_firstn; exact Epre | apply list_set_eq_skipn; apply Htp; apply list_set_eq_app; assumption].
  - apply pi_code_resp_on; [apply Hd; apply list_set_eq_app; assumption |].
    intros x x' _ Ex. apply IH; [exact Epre | apply list_set_eq_app; [exact Epts | constructor; [exact Ex | constructor]]].
Qed.

(** The elements of a recursive argument's set of shapes, at the
    candidate carriers [S], are of its code, when [S]'s elements at the
    shape's ends are the carriers'. *)
Lemma shape_set_sub_code : forall bound S pre target tparams ds pts1,
    Forall list_function_respects ds -> list_list_function_respects tparams ->
    (forall pts, points_fit ds pre pts1 pts ->
       let ps := tparams (pre ++ pts1 ++ pts) in
       set_sub (candidate_carrier bound S target (List.skipn (List.length (set_group_uniform_types G)) ps))
               (set_group_carrier G target (List.firstn (List.length (set_group_uniform_types G)) pre ++
                                            List.skipn (List.length (set_group_uniform_types G)) ps))) ->
    set_sub (shape_set G bound S pre ds target tparams pts1) (code_carrier (shape_code G ds target tparams pre pts1)).
Proof.
  intros bound S pre target tparams ds. induction ds as [| d ds IH]; intros pts1 Hds Htp Hl; cbn [shape_set shape_code].
  - intros z Hz. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
    specialize (Hl nil (points_fit_nil _ _)). cbv zeta in Hl. rewrite List.app_nil_r in Hl. exact (Hl z Hz).
  - inversion Hds as [| ? ? Hd Hds']; subst.
    intros z Hz. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |]. revert z Hz.
    apply function_set_mono_on.
    + intros x y _ E. apply shape_set_resp; [exact Hds' | exact Htp | apply list_set_eq_refl |
        apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact E | constructor]]].
    + intros x y _ E. apply code_carrier_resp. apply shape_code_resp; [exact Hds' | exact Htp | apply list_set_eq_refl |
        apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact E | constructor]]].
    + intros x Hx. apply IH; [exact Hds' | exact Htp |]. intros pts Hpts. cbv zeta.
      pose proof (Hl (x :: pts) (points_fit_cons _ _ _ _ _ _ Hx Hpts)) as H. cbv zeta in H.
      rewrite <- !List.app_assoc. cbn [List.app]. exact H.
Qed.

Lemma firstn_erase_at_ge : forall m n l, m <= n -> n < List.length l -> List.firstn m (erase_at n l) = List.firstn m l.
Proof.
  intros m n l Hmn Hl. unfold erase_at. rewrite List.firstn_app, List.firstn_firstn, Nat.min_l by exact Hmn.
  rewrite List.length_firstn, Nat.min_l by lia. replace (m - n) with 0 by lia. cbn. rewrite List.app_nil_r. reflexivity.
Qed.

(** A recursive argument's code ignores an erasure that its domains and
    target parameters ignore. *)
Lemma shape_code_erase : forall ds target tparams pre n, Forall list_function_respects ds -> list_list_function_respects tparams ->
    List.length (set_group_uniform_types G) <= n -> n < List.length pre ->
    forall pts1,
    (forall k d pts, List.nth_error ds k = Some d -> List.length pts = k ->
       set_eq (d (pre ++ pts1 ++ pts)) (d (erase_at n pre ++ pts1 ++ pts))) ->
    (forall pts, List.length pts = List.length ds ->
       list_set_eq (tparams (pre ++ pts1 ++ pts)) (tparams (erase_at n pre ++ pts1 ++ pts))) ->
    set_eq (shape_code G ds target tparams pre pts1) (shape_code G ds target tparams (erase_at n pre) pts1).
Proof.
  intros ds target tparams pre n Hds Htp Hn Hnl. induction Hds as [| d ds Hd Hds IH]; intros pts1 H1 H2; cbn [shape_code].
  - apply type_code_resp; [apply set_eq_refl |]. apply HGresp. rewrite firstn_erase_at_ge by assumption.
    apply list_set_eq_app; [apply list_set_eq_refl |]. apply list_set_eq_skipn.
    specialize (H2 nil eq_refl). rewrite !List.app_nil_r in H2. exact H2.
  - apply pi_code_resp_on.
    + specialize (H1 0 d nil eq_refl eq_refl). rewrite !List.app_nil_r in H1. exact H1.
    + intros x x' _ Ex. eapply set_eq_trans; [apply (IH (pts1 ++ [x])) |].
      * intros k d' pts Hk Hl. rewrite <- !List.app_assoc. cbn [List.app]. apply (H1 (S k) d' (x :: pts) Hk). cbn. lia.
      * intros pts Hl. rewrite <- !List.app_assoc. cbn [List.app]. apply (H2 (x :: pts)). cbn. lia.
      * apply shape_code_resp; [exact Hds | exact Htp | apply list_set_eq_refl |].
        apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact Ex | constructor]].
Qed.

Lemma repeat_false_snoc : forall n (pat : list bool), List.repeat false (S n) ++ pat = List.repeat false n ++ false :: pat.
Proof. induction n as [| n IH]; intros pat; [reflexivity |]. cbn [List.repeat List.app] in *. rewrite <- IH. reflexivity. Qed.

(** A recursive argument's type, read as its code: along points of the
    code's domains, an environment of the shape's domains, where the
    type's end reads the code's end. *)
Lemma shape_env_of_points : forall p D nn ds target tparams pre0 t pat Ψ θ C pts1,
    Forall list_function_respects ds -> list_list_function_respects tparams ->
    set_env_in T γ Ψ θ -> set_interp T γ Ψ θ (ptyp_ty p D nn pat t) C ->
    set_eq C (shape_code G ds target tparams pre0 pts1) -> List.length ds = ptyp_depth t ->
    forall pts, points_fit ds pre0 pts1 pts ->
    set_env_in T γ (shape_domains_ctx pat (ptyp_doms t) ++ Ψ) (set_env_extend_kinded θ (List.repeat ak_relevant (List.length pts)) pts) /\
    exists C', set_interp T γ (shape_domains_ctx pat (ptyp_doms t) ++ Ψ)
                 (set_env_extend_kinded θ (List.repeat ak_relevant (List.length pts)) pts)
                 (ptyp_ty p D nn (List.repeat false (ptyp_depth t) ++ pat) (pt_self (ptyp_mem t) (ptyp_ps t))) C' /\
               set_eq C' (shape_code G nil target tparams pre0 (pts1 ++ pts)).
Proof.
  intros p D nn ds target tparams pre0 t. revert ds.
  induction t as [j Ps | A t IH]; intros ds pat Ψ θ C pts1 Hds Htp Hθ HC EC Hl pts Hpts.
  - destruct ds; [| discriminate]. inversion Hpts; subst. cbn [List.length List.repeat set_env_extend_kinded shape_domains_ctx ptyp_doms
      List.app ptyp_depth ptyp_mem ptyp_ps] in *. rewrite List.app_nil_r. split; [exact Hθ |]. exists C. split; [exact HC | exact EC].
  - destruct ds as [| d ds]; [discriminate |]. cbn [List.length ptyp_depth ptyp_doms] in Hl. injection Hl as Hl.
    inversion Hds as [| ? ? Hd Hds']; subst.
    inversion Hpts as [| ? ? ? ? b pts' Hb Hpts']; subst.
    cbn [ptyp_ty] in HC. destruct (set_interp_pi_inv T γ _ _ _ _ _ _ _ HC) as (a1 & F & HA & HB & [[Hk _] | [_ ->]]);
      [discriminate |].
    cbn [shape_code] in EC.
    assert (Eθ : set_env_eq γ θ θ) by exact (set_env_rel_eq T γ _ _ _ Hθ).
    destruct (pi_code_inj _ _ _ _ EC (set_interp_family_respects T γ Hfn Hmods _ _ _ _ _ _ _ Eθ HB)) as [Ea EF].
    { intros x y _ E. apply shape_code_resp; [exact Hds' | exact Htp | apply list_set_eq_refl |].
      apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact E | constructor]]. }
    assert (Hb1 : set_mem b (code_carrier a1)) by (eapply set_mem_eq_r; [apply code_carrier_resp; apply set_eq_sym; exact Ea | exact Hb]).
    set (θ1 := set_env_extend θ (set_entry_term ak_relevant b)).
    assert (Hθ1 : set_env_in T γ (ce_ass ak_relevant (exp_wk A (wk_pat pat)) :: Ψ) θ1).
    { split; [exact Hθ |]. cbn [set_entry_rel]. exists b, b, a1. constructor; [reflexivity | reflexivity | exact HA | exact Hb1 | apply set_eq_refl]. }
    destruct (IH ds (false :: pat) _ θ1 (F b) (pts1 ++ [b]) Hds' Htp Hθ1 (HB b Hb1) (EF b Hb1) Hl pts' Hpts') as [Henv (C' & HC' & EC')].
    cbn [List.length List.repeat set_env_extend_kinded List.hd List.tl shape_domains_ctx ptyp_doms ptyp_depth ptyp_mem ptyp_ps].
    rewrite <- List.app_assoc. cbn [List.app].
    change (false :: List.repeat false (List.length (ptyp_doms t)) ++ pat) with (List.repeat false (S (List.length (ptyp_doms t))) ++ pat).
    rewrite repeat_false_snoc. unfold ptyp_depth in HC'. rewrite <- List.app_assoc in EC'. cbn [List.app] in EC'.
    split; [exact Henv |]. exists C'. split; [exact HC' | exact EC'].
Qed.

End ShapeCodes.

(** ** Arguments as Environments *)

Lemma set_tele_types_suffix : forall Γ0 X Δ Fs, set_tele_types T γ Γ0 (X ++ Δ) Fs ->
    set_tele_types T γ Γ0 Δ (List.firstn (List.length Δ) Fs).
Proof.
  induction X as [| e X IH]; intros Δ Fs H; cbn [List.app] in H.
  - rewrite <- (length_set_tele_types T γ _ _ _ H), List.firstn_all. exact H.
  - inversion H as [| κ A Δ0 Fs0 F H0 HA]; subst. pose proof (IH _ _ H0) as H1.
    rewrite List.firstn_app. rewrite (length_set_tele_types T γ _ _ _ H0), List.length_app.
    replace (List.length Δ - (List.length X + List.length Δ)) with 0 by lia. cbn. rewrite List.app_nil_r. exact H1.
Qed.

(** The kinds and the shapes of the semantic arguments, position by
    position. *)
Lemma set_arguments_shape_nth : forall gs sgs, set_arguments_shape gs sgs -> forall i g, List.nth_error gs i = Some g ->
    exists sg, List.nth_error sgs i = Some sg /\
      match g with
      | ca_arg κ _ => exists F, sg = set_argument_plain κ F
      | ca_rec t => exists F ds tparams, sg = set_argument_recursive F ds (ptyp_mem t) tparams /\ List.length ds = ptyp_depth t
      end.
Proof.
  induction 1 as [| κ A F gs sgs H IH | t F ds tparams gs sgs Hl H IH]; intros [| i] g Hg; cbn in Hg; try discriminate.
  - injection Hg as <-. eexists; split; [reflexivity | eauto].
  - exact (IH _ _ Hg).
  - injection Hg as <-. eexists; split; [reflexivity | eauto].
  - exact (IH _ _ Hg).
Qed.

Lemma set_arguments_shape_length : forall gs sgs, set_arguments_shape gs sgs -> List.length sgs = List.length gs.
Proof. induction 1; cbn; congruence. Qed.

(** The arguments' prefix of a constructor's telescope. *)
Lemma cargs_ctx_prefix : forall p D Mk gs1 rest,
    List.skipn (List.length (gs1 ++ rest) - List.length gs1) (cargs_ctx p D Mk (gs1 ++ rest)) = cargs_ctx p D Mk gs1.
Proof.
  intros. rewrite cargs_ctx_app, List.length_app.
  replace (List.length gs1 + List.length rest - List.length gs1) with (List.length rest) by lia.
  rewrite List.skipn_app, List.skipn_all2 by (rewrite length_cargs_ctx_aux; lia).
  rewrite length_cargs_ctx_aux, Nat.sub_diag. reflexivity.
Qed.

Lemma points_fit_length : forall ds pre pts1 pts, points_fit ds pre pts1 pts -> List.length pts = List.length ds.
Proof. induction 1; cbn; congruence. Qed.

Lemma length_shape_domains_ctx : forall Bs pat, List.length (shape_domains_ctx pat Bs) = List.length Bs.
Proof. induction Bs as [| B Bs IH]; intros pat; cbn [shape_domains_ctx]; [reflexivity |]. rewrite List.length_app, IH. cbn. lia. Qed.

Lemma set_env_extend_kinded_snoc_any : forall vs ρ κs x,
    set_env_extend_kinded ρ κs (vs ++ [x]) =
    set_env_extend (set_env_extend_kinded ρ κs vs) (set_entry_term (List.nth (List.length vs) κs ak_relevant) x).
Proof.
  induction vs as [| v vs IH]; intros ρ κs x; cbn [List.app set_env_extend_kinded List.length].
  - destruct κs; reflexivity.
  - rewrite IH. destruct κs; cbn [List.tl List.nth]; [destruct (List.length vs); reflexivity | reflexivity].
Qed.

(** The values of an environment extended by values, of any kinds. *)
Lemma set_env_values_extend_kinded_any : forall Δ ρ κs vs, List.length Δ = List.length vs ->
    set_env_values Δ (set_env_extend_kinded ρ κs vs) = vs.
Proof.
  induction Δ as [| e Δ IH]; intros ρ κs vs Hl.
  - destruct vs; [reflexivity | discriminate].
  - destruct (List.exists_last (l := vs) ltac:(intros ->; discriminate)) as (vs1 & x & ->).
    rewrite List.length_app in Hl; cbn in Hl. rewrite set_env_extend_kinded_snoc_any. cbn [set_env_values].
    change (set_env_tail (set_env_extend ?r ?e)) with r. rewrite IH by lia. reflexivity.
Qed.

(** Points of domains equal at every list are points of both. *)
Lemma points_fit_transfer : forall ds pre pre' pts1 pts, points_fit ds pre pts1 pts ->
    (forall k d pts0, List.nth_error ds k = Some d -> List.length pts0 = List.length pts1 + k ->
       set_eq (d (pre ++ pts0)) (d (pre' ++ pts0))) ->
    points_fit ds pre' pts1 pts.
Proof.
  induction 1 as [pre0 points | d ds pre0 points b pts Hb H IH]; intros Hd; constructor.
  - eapply set_mem_eq_r; [apply code_carrier_resp; apply (Hd 0 d points eq_refl); lia | exact Hb].
  - apply IH. intros k d' pts0 Hk Hl. apply (Hd (S k) d' pts0 Hk). rewrite List.length_app in Hl. cbn in Hl. lia.
Qed.

Section Arguments.
  (** The eliminator's context, an environment of it, the group, and the
      uniform parameters' instance *)
  Variables (Γ : ctx) (ρ : set_env) (p : qname) (D : ind_decl) (Us : list exp) (Fσ : set_env -> set_env).
  Hypotheses (HΓ : set_ctx T γ Γ) (HcΓ : ⊢ gc_deps ⍮ gc_stack ⍮ Γ) (Hρ : set_env_in T γ Γ ρ)
    (HD : ind_lookup gc_deps gc_stack p = Some D)
    (Hσ : set_gsub_with T γ Γ (sb_of_list sb_id Us) (ind_uparams D ++ Γ) Fσ).

  (** The uniform parameters' values *)
  Definition elim_uniform_values : list aczel_set := set_env_values (ind_uparams D) (Fσ ρ).

(** An environment of an instance whose part below it is [ρ] at every
    variable has the uniform parameters' values. *)
Lemma inst_uniform_values : forall ρ', (forall x, ρ' x = ρ x) ->
    list_set_eq (set_env_values (ind_uparams D) (Fσ ρ')) elim_uniform_values.
Proof.
  intros ρ' E. unfold elim_uniform_values. apply set_env_values_resp.
  assert (Hr : set_env_rel T γ Γ ρ' ρ) by (eapply set_env_rel_ext; [exact HcΓ | intros x; symmetry; apply E | intros x; reflexivity | exact Hρ]).
  pose proof (set_env_rel_eq T γ _ _ _ (set_gsub_rel _ _ _ _ _ _ Hσ _ _ Hr)) as E'. intros x. apply E'.
Qed.

  (** The group's carriers: the least fixed point in [U], at instances of
      the members' parameters over the uniform values *)
  Variable U : aczel_set.
  Hypothesis Hcar : forall k Mk ρk, ind_member D k = Some Mk -> set_env_in T γ (im_params D Mk) ρk ->
    list_set_eq (uniform_values D Mk ρk) elim_uniform_values ->
    set_eq (set_group_carrier (global_group γ p) k (set_env_values (im_params D Mk) ρk))
           (member_carrier (global_group γ p) elim_uniform_values U U k (set_env_values (im_nparams Mk) ρk)).
  (** The candidate carriers at hand, among the fixed point's points *)
  Variable S : aczel_set.
  Hypothesis HS : set_sub S (carrier_fixed_point (global_group γ p) elim_uniform_values U U).

Lemma group_uniform_count : List.length (set_group_uniform_types (global_group γ p)) = ind_nu D.
Proof.
  pose proof (set_group_ok_uniform _ _ _ _ _ (set_gctx_ok_groups _ _ Hok _ _ HD)) as H.
  rewrite (length_set_tele_types T γ _ _ _ H). reflexivity.
Qed.

(** At the end of a recursive argument's shape, the candidate carriers'
    elements are the carriers': the argument's points are an instance of
    its target's parameters ([set_constructor_ok_target_instance]). *)
Lemma recursive_leaf_sub : forall k Mk gs sgs gs1 t gs2 F ds target tparams θo C pre_e,
    ind_member D k = Some Mk -> set_constructor_ok T γ p D (global_group γ p) Mk gs sgs ->
    gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error sgs (List.length gs1) = Some (set_argument_recursive F ds target tparams) ->
    Forall list_function_respects ds -> list_list_function_respects tparams ->
    List.length ds = ptyp_depth t ->
    set_env_in T γ (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo ->
    set_interp T γ (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo (ptyp_ty p D (im_nn Mk) (cargs_pat gs1) t) C ->
    set_eq C (shape_code (global_group γ p) ds target tparams (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo) nil) ->
    list_set_eq (List.firstn (ind_nu D) (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo)) elim_uniform_values ->
    list_set_eq (List.firstn (ind_nu D) pre_e) elim_uniform_values ->
    (forall k' d pts0, List.nth_error ds k' = Some d -> List.length pts0 = k' ->
       set_eq (d (pre_e ++ pts0)) (d (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo ++ pts0))) ->
    (forall pts, List.length pts = List.length ds ->
       list_set_eq (tparams (pre_e ++ pts)) (tparams (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo ++ pts))) ->
    forall pts, points_fit ds pre_e nil pts ->
    let ps := tparams (pre_e ++ nil ++ pts) in
    set_sub (candidate_carrier U S target (List.skipn (List.length (set_group_uniform_types (global_group γ p))) ps))
            (set_group_carrier (global_group γ p) target
               (List.firstn (List.length (set_group_uniform_types (global_group γ p))) pre_e ++
                List.skipn (List.length (set_group_uniform_types (global_group γ p))) ps)).
Proof.
  intros * Hk Hcok Egs Hsg Hds Htp Hlds Hθo HC EC Hus Hpre Hdom Htps pts Hpts ps.
  unfold ps. rewrite group_uniform_count. cbn [List.app].
  set (G := global_group γ p) in *. set (Lv := set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo) in *.
  (* the points are points of the code read at the environment's values *)
  assert (Hpts' : points_fit ds Lv nil pts)
    by (apply (points_fit_transfer _ _ _ _ _ Hpts); intros k' d pts0 Hk' Hl; cbn in Hl; exact (Hdom k' d pts0 Hk' Hl)).
  (* the environment of the shape's end *)
  destruct (shape_env_of_points (global_group γ p) (set_group_ok_carrier_resp _ _ _ _ _ (set_gctx_ok_groups _ _ Hok _ _ HD))
              p D (im_nn Mk) ds target tparams Lv t (cargs_pat gs1) _ θo C nil Hds Htp Hθo HC EC Hlds pts Hpts') as [Hθ' _].
  set (θ' := set_env_extend_kinded θo (List.repeat ak_relevant (List.length pts)) pts) in *.
  pose proof (points_fit_length _ _ _ _ Hpts) as Hlpts.
  assert (Hlds' : List.length (shape_domains_ctx (cargs_pat gs1) (ptyp_doms t)) = List.length pts)
    by (rewrite length_shape_domains_ctx, Hlpts, Hlds; reflexivity).
  assert (Hθ'v : set_env_values (recursive_end_ctx p D Mk gs1 t) θ' = Lv ++ pts).
  { unfold recursive_end_ctx, θ'. rewrite set_env_values_app. f_equal.
    - unfold Lv. apply set_env_values_agree. intros x _. unfold set_env_drop. rewrite Hlds', set_env_extend_kinded_ge. reflexivity.
    - apply set_env_values_extend_kinded_any. exact Hlds'. }
  destruct (set_constructor_ok_target_instance _ _ _ _ _ _ _ _ Hcok gs1 t gs2 F ds target tparams Egs Hsg θ' Hθ')
    as (Mt & ρt & [HMt Hρt Evals]).
  rewrite Hθ'v in Evals.
  assert (HlLv : ind_nu D <= List.length Lv)
    by (unfold Lv; rewrite length_set_env_values, List.length_app, length_im_params; unfold im_np; lia).
  rewrite List.firstn_app, (proj2 (Nat.sub_0_le (ind_nu D) (List.length Lv)) HlLv), List.app_nil_r in Evals.
  unfold im_params in Evals. rewrite set_env_values_app in Evals.
  assert (Hlen : List.length (List.firstn (ind_nu D) Lv) =
                 List.length (set_env_values (ind_uparams D) (set_env_drop (List.length (im_nparams Mt)) ρt)))
    by (rewrite List.length_firstn, length_set_env_values, Nat.min_l by exact HlLv; reflexivity).
  destruct (list_set_eq_app_inv _ _ _ _ Hlen Evals) as [Eu En].
  assert (Hun : list_set_eq (uniform_values D Mt ρt) elim_uniform_values).
  { unfold uniform_values. rewrite <- (length_im_nparams Mt). eapply list_set_eq_trans; [apply list_set_eq_sym; exact Eu | exact Hus]. }
  pose proof (Hcar _ _ _ HMt Hρt Hun) as Ecar.
  intros z Hz.
  assert (Hz1 : set_mem z (member_carrier G elim_uniform_values U U target (set_env_values (im_nparams Mt) ρt))).
  { unfold member_carrier. eapply set_mem_eq_r; [apply candidate_carrier_resp |].
    - eapply list_set_eq_trans; [| exact En]. apply list_set_eq_skipn. apply Htps. rewrite Hlpts. reflexivity.
    - exact (candidate_carrier_mono _ _ _ _ _ HS _ Hz). }
  eapply set_mem_eq_r; [| eapply set_mem_eq_r; [apply set_eq_sym; exact Ecar | exact Hz1]].
  apply (set_group_ok_carrier_resp _ _ _ _ _ (set_gctx_ok_groups _ _ Hok _ _ HD)).
  unfold im_params. rewrite set_env_values_app. apply list_set_eq_app.
  - rewrite (length_im_nparams Mt). eapply list_set_eq_trans; [apply list_set_eq_sym; exact Eu |].
    eapply list_set_eq_trans; [exact Hus | apply list_set_eq_sym; exact Hpre].
  - eapply list_set_eq_trans; [apply list_set_eq_sym; exact En |]. apply list_set_eq_skipn. apply list_set_eq_sym. apply Htps.
    rewrite Hlpts. reflexivity.
Qed.

(** A member's parameters, and its constructors' arguments over them,
    denote, closed. *)
Lemma member_params_ctx : forall k Mk SMk, ind_member D k = Some Mk -> List.nth_error (set_group_members (global_group γ p)) k = Some SMk ->
    set_ctx T γ (im_params D Mk).
Proof.
  intros * Hk HSk. pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG.
  pose proof (set_ctx_of_tele_types T γ Hfn Hmods _ _ _ (set_group_ok_uniform _ _ _ _ _ HG) I) as HU. rewrite List.app_nil_r in HU.
  exact (set_ctx_of_tele_types T γ Hfn Hmods _ _ _ (set_member_ok_nparams _ _ _ _ _ _ _ (set_group_ok_members _ _ _ _ _ HG _ _ _ Hk HSk)) HU).
Qed.

Lemma cargs_prefix_ctx : forall k Mk SMk gs sgs gs1 rest, ind_member D k = Some Mk ->
    List.nth_error (set_group_members (global_group γ p)) k = Some SMk ->
    set_constructor_ok T γ p D (global_group γ p) Mk gs sgs -> gs = gs1 ++ rest ->
    set_ctx T γ (cargs_ctx p D Mk gs1 ++ im_params D Mk).
Proof.
  intros * Hk HSk Hcok ->. pose proof (set_constructor_ok_types _ _ _ _ _ _ _ _ Hcok) as Ht.
  rewrite cargs_ctx_app in Ht. pose proof (set_tele_types_suffix _ _ _ _ Ht) as Ht'.
  exact (set_ctx_of_tele_types T γ Hfn Hmods _ _ _ Ht' (member_params_ctx _ _ _ Hk HSk)).
Qed.

(** The arguments of a constructor, built from arguments fitting the
    candidate carriers at the parameters of an environment of the member's
    non-uniform parameters, are an environment of the instance of their
    telescope. *)
Lemma args_env : forall k Mk SMk cs gs ρn vals,
    ind_member D k = Some Mk -> List.nth_error (set_group_members (global_group γ p)) k = Some SMk ->
    In cs (set_member_constructors SMk) -> ind_con Mk (set_constructor_name cs) = Some gs ->
    set_constructor_ok T γ p D (global_group γ p) Mk gs (set_constructor_arguments cs) ->
    set_env_in T γ (tele_sub (im_nparams Mk) (sb_of_list sb_id Us) ++ Γ) ρn -> (forall x, set_env_drop (im_nn Mk) ρn x = ρ x) ->
    arguments_fit (global_group γ p) U S (elim_uniform_values ++ set_env_values (im_nparams Mk) ρn) (set_constructor_arguments cs) vals ->
    forall gs1 rest, gs = gs1 ++ rest ->
    set_env_in T γ (tele_sub (cargs_ctx p D Mk gs1 ++ im_nparams Mk) (sb_of_list sb_id Us) ++ Γ)
      (set_env_extend_kinded ρn (ctx_kinds (cargs_ctx p D Mk gs1)) (List.firstn (List.length gs1) vals)).
Proof.
  intros k Mk SMk cs gs ρn vals Hk HSk Hcs Hgs Hcok Hρn Hdrop Hfit.
  set (G := global_group γ p) in *. set (sgs := set_constructor_arguments cs) in *.
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG. fold G in HG.
  pose proof (set_constructor_ok_shape _ _ _ _ _ _ _ _ Hcok) as Hsh.
  pose proof (set_arguments_shape_length _ _ Hsh) as Hlsh.
  pose proof (arguments_fit_length _ _ _ _ _ _ Hfit) as Hlv.
  pose proof (set_group_ok_respects _ _ _ _ _ HG _ _ _ HSk Hcs) as Hrs. fold sgs in Hrs.
  pose proof (gctx_closed_ind _ _ _ _ (wf_gctx_closed _ _ _ HcΓ) HD) as Hcl.
  pose proof (decls_of_ctx _ _ _ HcΓ) as HDs.
  pose proof (cons_lookup_in _ _ _ Hgs) as Hin.
  induction gs1 as [| g gs1 IH] using List.rev_ind; intros rest Egs.
  - cbn [cargs_ctx cargs_ctx_aux List.app List.length List.firstn ctx_kinds List.map List.rev set_env_extend_kinded]. exact Hρn.
  - specialize (IH (g :: rest) ltac:(rewrite Egs, <- List.app_assoc; reflexivity)).
    set (i := List.length gs1) in *.
    assert (Hgi : List.nth_error gs i = Some g) by (rewrite Egs, <- List.app_assoc, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
    destruct (set_arguments_shape_nth _ _ Hsh _ _ Hgi) as (sg & Hsg & Hsgk).
    assert (Hi : i < List.length vals) by (rewrite Hlv; apply List.nth_error_Some; congruence).
    destruct (List.nth_error vals i) as [v |] eqn:Hv; [| apply List.nth_error_None in Hv; lia].
    assert (Hfirst : List.firstn (List.length (gs1 ++ [g])) vals = List.firstn i vals ++ [v])
      by (rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r; apply firstn_S_nth; exact Hv).
    rewrite Hfirst, cargs_ctx_snoc.
    assert (Hlk : List.length (ctx_kinds (cargs_ctx p D Mk gs1)) = List.length (List.firstn i vals))
      by (rewrite length_ctx_kinds, length_cargs_ctx, List.length_firstn; lia).
    (* the closed context of the arguments before, and its instance *)
    assert (EΨ : (cargs_ctx p D Mk gs1 ++ im_nparams Mk) ++ ind_uparams D = cargs_ctx p D Mk gs1 ++ im_params D Mk)
      by (rewrite <- List.app_assoc; reflexivity).
    assert (Egs1 : gs = gs1 ++ (g :: rest)) by (rewrite Egs, <- List.app_assoc; reflexivity).
    pose proof (cargs_ctx_closed p D k Mk _ gs gs1 (g :: rest) Hcl Hk Hin Egs1) as Hs0.
    pose proof (cargs_ctx_closed p D k Mk _ gs (gs1 ++ [g]) rest Hcl Hk Hin Egs) as Hs1.
    destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hgw HDs HD Hk Hin gs1 (g :: rest) Egs1) as (Hw0 & _ & _).
    pose proof (cargs_prefix_ctx _ _ _ _ _ gs1 (g :: rest) Hk HSk Hcok Egs1) as Hc0.
    assert (Hass0 : all_assumptions (cargs_ctx p D Mk gs1 ++ im_params D Mk))
      by (apply List.Forall_app; split; [apply cargs_ctx_aux_ass | exact (decl_closed_params_ass _ _ _ Hcl Hk)]).
    pose proof (wf_ctx_closed_app _ _ _ _ Hass0 Hs0 Hw0 HcΓ) as HwΓ0.
    assert (HcΓ0 : set_ctx T γ ((cargs_ctx p D Mk gs1 ++ im_params D Mk) ++ Γ)).
    { pose proof (set_ctx_moved T γ Hfn Hmods _ nil Γ _ _ (set_gsub_drop T γ _ HcΓ) HΓ ltac:(rewrite List.app_nil_r; exact Hc0)
                    ltac:(rewrite List.app_nil_r; exact Hw0)) as H.
      rewrite tele_sub_closed in H by exact Hs0. exact H. }
    pose proof (set_constructor_ok_types _ _ _ _ _ _ _ _ Hcok) as Htys.
    set (ρo := set_env_extend_kinded ρn (ctx_kinds (cargs_ctx p D Mk gs1)) (List.firstn i vals)) in *.
    set (Ψ := cargs_ctx p D Mk gs1 ++ im_nparams Mk) in *.
    (* one more entry, of a type read off the closed context *)
    assert (Gen : forall κ A F, cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [g] = [ce_ass κ A] ->
              ctx_scoped 0 (ce_ass κ A :: cargs_ctx p D Mk gs1 ++ im_params D Mk) ->
              set_reads T γ (cargs_ctx p D Mk gs1 ++ im_params D Mk) A F ->
              set_mem v (code_carrier (F (set_env_values (Ψ ++ ind_uparams D) (inst_closed_env Γ (ind_uparams D) Fσ Ψ ρo)))) ->
              set_env_in T γ (tele_sub ((cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [g] ++ cargs_ctx p D Mk gs1) ++ im_nparams Mk)
                                       (sb_of_list sb_id Us) ++ Γ)
                (set_env_extend_kinded ρn (ctx_kinds (cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [g] ++ cargs_ctx p D Mk gs1))
                   (List.firstn i vals ++ [v]))).
    { intros κ A F E Hsc HF Hx. rewrite E. cbn [List.app]. rewrite ctx_kinds_cons, set_env_extend_kinded_snoc by exact Hlk.
      fold ρo. cbn [centry_kind].
      change (ce_ass κ A :: cargs_ctx p D Mk gs1 ++ im_nparams Mk) with (ce_ass κ A :: Ψ).
      destruct Hsc as [HsA _]. cbn [ce_scoped] in HsA.
      rewrite Nat.add_0_r, <- EΨ in HsA.
      rewrite <- EΨ in HF, Hs0, Hc0, Hw0, HwΓ0, HcΓ0.
      exact (set_env_in_inst_extend Γ (ind_uparams D) _ Fσ Hσ HΓ HcΓ Ψ κ A F ρo v Hs0 HsA Hc0 HcΓ0 Hw0 HwΓ0 HF IH Hx). }
    assert (Hlc : List.length (cargs_ctx p D Mk gs1) = List.length (List.firstn i vals))
      by (rewrite length_cargs_ctx, List.length_firstn; lia).
    (* the closed environment's values *)
    assert (Hvals : list_set_eq (set_env_values (Ψ ++ ind_uparams D) (inst_closed_env Γ (ind_uparams D) Fσ Ψ ρo))
                                (elim_uniform_values ++ set_env_values (im_nparams Mk) ρn ++ List.firstn i vals)).
    { rewrite inst_closed_env_values. apply list_set_eq_app.
      - apply inst_uniform_values. intros x. unfold Ψ, set_env_drop, ρo.
        rewrite List.length_app, <- Nat.add_assoc, Hlc, set_env_extend_kinded_ge. apply Hdrop.
      - unfold Ψ. rewrite set_env_values_app. replace (set_env_values (cargs_ctx p D Mk gs1) ρo) with (List.firstn i vals)
          by (unfold ρo; symmetry; apply set_env_values_extend_kinded_any; exact Hlc).
        apply list_set_eq_app; [| apply list_set_eq_refl].
        rewrite (set_env_values_agree (im_nparams Mk) (set_env_drop (List.length (cargs_ctx p D Mk gs1)) ρo) ρn);
          [apply list_set_eq_refl |].
        intros x _. unfold set_env_drop, ρo. rewrite Hlc, set_env_extend_kinded_ge. reflexivity. }
    assert (HL0 : List.length (elim_uniform_values ++ set_env_values (im_nparams Mk) ρn) = im_np D Mk)
      by (unfold elim_uniform_values; rewrite List.length_app, !length_set_env_values; unfold im_np, im_nn, ind_nu; lia).
    assert (Hrec : forall n ty ds tg tp, List.nth_error sgs n = Some (set_argument_recursive ty ds tg tp) ->
              exists t, List.nth_error gs n = Some (ca_rec t)).
    { intros n ty ds tg tp Hn. assert (Hn' : n < List.length gs) by (rewrite <- Hlsh; apply List.nth_error_Some; congruence).
      destruct (List.nth_error gs n) as [g' |] eqn:Hg'; [| apply List.nth_error_None in Hg'; lia].
      destruct (set_arguments_shape_nth _ _ Hsh _ _ Hg') as (sg' & Hsg' & Hk'). rewrite Hn in Hsg'. injection Hsg' as <-.
      destruct g' as [κ' A' | t']; [destruct Hk' as [F' Hk']; discriminate | eauto]. }
    assert (Hgs_eq : cargs_ctx p D Mk gs =
              cargs_ctx_aux p D (im_nn Mk) (cargs_pat (gs1 ++ [g])) rest ++ (cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [g] ++ cargs_ctx p D Mk gs1))
      by (rewrite Egs, cargs_ctx_app, cargs_ctx_snoc; reflexivity).
    assert (Hs1' : ctx_scoped 0 ((cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [g] ++ cargs_ctx p D Mk gs1) ++ im_params D Mk))
      by (rewrite <- cargs_ctx_snoc; exact Hs1).
    destruct g as [κ A0 | t].
    + (* a non-recursive argument: of its type at the values, which ignores the recursive ones before it *)
      destruct Hsgk as [Fp ->].
      set (A := exp_wk A0 (wk_pat (cargs_pat gs1))).
      assert (E : cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [ca_arg κ A0] = [ce_ass κ A]) by reflexivity.
      rewrite E in Hgs_eq, Hs1'. cbn [List.app] in Hgs_eq, Hs1'.
      destruct (set_tele_types_entry T γ _ _ _ Htys _ κ A _ Hgs_eq) as (F & HF & HnF).
      rewrite List.nth_error_map, length_cargs_ctx in HnF. fold i in HnF. rewrite Hsg in HnF. cbn in HnF. injection HnF as <-.
      apply (Gen κ A Fp E Hs1' HF).
      pose proof (arguments_fit_nth _ _ _ _ _ _ Hfit i _ v Hsg Hv) as Hm. cbn beta iota in Hm.
      assert (Hrp : list_function_respects Fp) by (rewrite List.Forall_forall in Hrs; exact (Hrs _ (List.nth_error_In _ _ Hsg))).
      eapply set_mem_eq_r; [| exact Hm]. apply code_carrier_resp.
      eapply set_eq_trans; [| apply Hrp; apply list_set_eq_sym; exact Hvals]. rewrite List.app_assoc. apply set_eq_sym.
      apply erase_args_ignored; [| lia | lia].
      intros n L' ty ds tg tp Hn Hsn HL'. destruct (Hrec _ _ _ _ _ Hsn) as (tn & Htn).
      rewrite HL0 in HL' |- *.
      exact (set_constructor_ok_ignores _ _ _ _ _ _ _ _ Hcok n tn i _ L' Htn Hn Hsg HL').
    + (* a recursive argument: in its set of shapes, within its code *)
      destruct Hsgk as (Fr & ds & tparams & -> & Hlds).
      set (A := ptyp_ty p D (im_nn Mk) (cargs_pat gs1) t).
      assert (E : cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [ca_rec t] = [ce_ass ak_relevant A]) by reflexivity.
      rewrite E in Hgs_eq, Hs1'. cbn [List.app] in Hgs_eq, Hs1'.
      destruct (set_tele_types_entry T γ _ _ _ Htys _ ak_relevant A _ Hgs_eq) as (F & HF & HnF).
      rewrite List.nth_error_map, length_cargs_ctx in HnF. fold i in HnF. rewrite Hsg in HnF. cbn in HnF. injection HnF as <-.
      apply (Gen ak_relevant A Fr E Hs1' HF).
      set (θ := inst_closed_env Γ (ind_uparams D) Fσ Ψ ρo).
      destruct (inst_closed_env_in Γ (ind_uparams D) _ Fσ Hσ HΓ HcΓ Ψ ρo ltac:(rewrite EΨ; exact Hs0) ltac:(rewrite EΨ; exact Hc0)
                  ltac:(rewrite EΨ; exact HcΓ0) ltac:(rewrite EΨ; exact Hw0) ltac:(rewrite EΨ; exact HwΓ0) IH) as [_ Hθ].
      fold θ in Hθ. rewrite EΨ in Hθ, Hvals |- *.
      pose proof (set_constructor_ok_recursive _ _ _ _ _ _ _ _ Hcok i t Fr ds (ptyp_mem t) tparams θ Hgi Hsg) as Hrc.
      rewrite Egs1 in Hrc. unfold i in Hrc. rewrite cargs_ctx_prefix in Hrc. specialize (Hrc Hθ). cbn [set_argument_type] in HF.
      fold θ in Hvals. set (Lθ := set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θ) in *.
      set (L0 := elim_uniform_values ++ set_env_values (im_nparams Mk) ρn) in *.
      set (pre_e := L0 ++ erase_args (List.firstn i sgs) (List.firstn i vals)).
      assert (Hrsg : argument_respects (set_argument_recursive Fr ds (ptyp_mem t) tparams))
        by (rewrite List.Forall_forall in Hrs; exact (Hrs _ (List.nth_error_In _ _ Hsg))).
      destruct Hrsg as [Hds Htp].
      pose proof (arguments_fit_nth _ _ _ _ _ _ Hfit i _ v Hsg Hv) as Hm. cbn beta iota in Hm. fold L0 pre_e in Hm.
      assert (Hign : forall n L', n < i -> (exists ty ds' tg tp, List.nth_error sgs n = Some (set_argument_recursive ty ds' tg tp)) ->
                 List.length L' = List.length L0 + i ->
                 argument_ignores (List.length L0 + n) (set_argument_recursive Fr ds (ptyp_mem t) tparams) L').
      { intros n L' Hn (ty & ds' & tg & tp & Hsn) HL'. destruct (Hrec _ _ _ _ _ Hsn) as (tn & Htn). rewrite HL0 in HL' |- *.
        exact (set_constructor_ok_ignores _ _ _ _ _ _ _ _ Hcok n tn i _ L' Htn Hn Hsg HL'). }
      assert (Hiv : i <= List.length sgs) by lia. assert (Hiv' : i <= List.length vals) by lia.
      assert (HLθ : list_set_eq Lθ (L0 ++ List.firstn i vals)) by (unfold L0; rewrite <- List.app_assoc; exact Hvals).
      assert (Hnu : List.length elim_uniform_values = ind_nu D)
        by (unfold elim_uniform_values; rewrite length_set_env_values; reflexivity).
      assert (Hdom : forall k' d pts0, List.nth_error ds k' = Some d -> List.length pts0 = k' ->
                set_eq (d (pre_e ++ pts0)) (d (Lθ ++ pts0))).
      { intros k' d pts0 Hk' Hl'.
        assert (Hd : list_function_respects d) by (rewrite List.Forall_forall in Hds; exact (Hds _ (List.nth_error_In _ _ Hk'))).
        eapply set_eq_trans; [| apply Hd; apply list_set_eq_app; [apply list_set_eq_sym; exact HLθ | apply list_set_eq_refl]].
        apply set_eq_sym. unfold pre_e.
        apply (erase_args_ignored (fun L => d (L ++ pts0)) L0 sgs vals i); [| exact Hiv | exact Hiv'].
        intros n L' ty ds' tg tp Hn Hsn HL'. exact (proj1 (Hign n L' Hn ltac:(eauto) HL') k' d pts0 Hk' Hl'). }
      assert (Htps : forall pts, List.length pts = List.length ds -> list_set_eq (tparams (pre_e ++ pts)) (tparams (Lθ ++ pts))).
      { intros pts Hl'.
        eapply list_set_eq_trans; [| apply Htp; apply list_set_eq_app; [apply list_set_eq_sym; exact HLθ | apply list_set_eq_refl]].
        apply list_set_eq_sym. unfold pre_e.
        apply (erase_args_ignored_list (fun L => tparams (L ++ pts)) L0 sgs vals i); [| exact Hiv | exact Hiv'].
        intros n L' ty ds' tg tp Hn Hsn HL'. exact (proj2 (Hign n L' Hn ltac:(eauto) HL') pts Hl'). }
      assert (Hus : list_set_eq (List.firstn (ind_nu D) Lθ) elim_uniform_values).
      { eapply list_set_eq_trans; [apply list_set_eq_firstn; exact HLθ |]. unfold L0.
        rewrite <- List.app_assoc, List.firstn_app, Hnu, Nat.sub_diag, List.firstn_all2 by lia.
        cbn [List.firstn]. rewrite List.app_nil_r. apply list_set_eq_refl. }
      assert (Hpre : list_set_eq (List.firstn (ind_nu D) pre_e) elim_uniform_values).
      { unfold pre_e, L0. rewrite <- List.app_assoc, List.firstn_app, Hnu, Nat.sub_diag, List.firstn_all2 by lia.
        cbn [List.firstn]. rewrite List.app_nil_r. apply list_set_eq_refl. }
      pose proof (set_group_ok_carrier_resp _ _ _ _ _ HG) as HGresp.
      pose proof (shape_set_sub_code G HGresp U S pre_e (ptyp_mem t) tparams ds nil Hds Htp
                    (fun pts Hpts => recursive_leaf_sub k Mk gs sgs gs1 t rest Fr ds (ptyp_mem t) tparams θ (Fr Lθ) pre_e Hk Hcok Egs1 Hsg
                                       Hds Htp Hlds Hθ (HF θ Hθ) Hrc Hus Hpre Hdom Htps pts Hpts) v Hm) as Hv1.
      eapply set_mem_eq_r; [| exact Hv1]. apply code_carrier_resp.
      eapply set_eq_trans; [| apply set_eq_sym; exact Hrc].
      eapply set_eq_trans;
        [| apply shape_code_resp; [exact HGresp | exact Hds | exact Htp | apply list_set_eq_sym; exact HLθ | apply list_set_eq_refl]].
      apply set_eq_sym. unfold pre_e.
      apply (erase_args_ignored (fun L => shape_code G ds (ptyp_mem t) tparams L nil) L0 sgs vals i); [| exact Hiv | exact Hiv'].
      intros n L' ty ds' tg tp Hn Hsn HL'. destruct (Hign n L' Hn ltac:(eauto) HL') as [H1 H2].
      apply (shape_code_erase G HGresp); [exact Hds | exact Htp | unfold G; rewrite group_uniform_count, HL0; unfold im_np; lia | lia
                                         | exact H1 | exact H2].
Qed.

(** The same over the closed context of the parameters: the arguments of
    a constructor, fitting the candidate carriers after the values of an
    environment of the member's parameters whose uniform ones are the
    uniform values, extend it to an environment of the closed context of
    the arguments. *)
Lemma args_env_closed : forall k Mk SMk cs gs θp vals,
    ind_member D k = Some Mk -> List.nth_error (set_group_members (global_group γ p)) k = Some SMk ->
    In cs (set_member_constructors SMk) -> ind_con Mk (set_constructor_name cs) = Some gs ->
    set_constructor_ok T γ p D (global_group γ p) Mk gs (set_constructor_arguments cs) ->
    set_env_in T γ (im_params D Mk) θp -> list_set_eq (uniform_values D Mk θp) elim_uniform_values ->
    arguments_fit (global_group γ p) U S (set_env_values (im_params D Mk) θp) (set_constructor_arguments cs) vals ->
    forall gs1 rest, gs = gs1 ++ rest ->
    set_env_in T γ (cargs_ctx p D Mk gs1 ++ im_params D Mk)
      (set_env_extend_kinded θp (ctx_kinds (cargs_ctx p D Mk gs1)) (List.firstn (List.length gs1) vals)).
Proof.
  intros k Mk SMk cs gs θp vals Hk HSk Hcs Hgs Hcok Hθp Huni Hfit.
  set (G := global_group γ p) in *. set (sgs := set_constructor_arguments cs) in *.
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG. fold G in HG.
  pose proof (set_constructor_ok_shape _ _ _ _ _ _ _ _ Hcok) as Hsh.
  pose proof (set_arguments_shape_length _ _ Hsh) as Hlsh.
  pose proof (arguments_fit_length _ _ _ _ _ _ Hfit) as Hlv.
  pose proof (set_group_ok_respects _ _ _ _ _ HG _ _ _ HSk Hcs) as Hrs. fold sgs in Hrs.
  pose proof (set_constructor_ok_types _ _ _ _ _ _ _ _ Hcok) as Htys.
  set (L0 := set_env_values (im_params D Mk) θp) in *.
  assert (HL0 : List.length L0 = im_np D Mk) by (unfold L0; rewrite length_set_env_values, length_im_params; reflexivity).
  assert (Hnu : ind_nu D <= List.length L0) by (rewrite HL0; unfold im_np; lia).
  assert (Hpre0 : list_set_eq (List.firstn (ind_nu D) L0) elim_uniform_values).
  { unfold L0, im_params. rewrite set_env_values_app, List.firstn_app, length_set_env_values.
    replace (ind_nu D - List.length (ind_uparams D)) with 0 by (unfold ind_nu; lia).
    rewrite List.firstn_all2 by (rewrite length_set_env_values; unfold ind_nu; lia).
    cbn [List.firstn]. rewrite List.app_nil_r. exact Huni. }
  assert (Hrec : forall n ty ds tg tp, List.nth_error sgs n = Some (set_argument_recursive ty ds tg tp) ->
            exists t, List.nth_error gs n = Some (ca_rec t)).
  { intros n ty ds tg tp Hn. assert (Hn' : n < List.length gs) by (rewrite <- Hlsh; apply List.nth_error_Some; congruence).
    destruct (List.nth_error gs n) as [g' |] eqn:Hg'; [| apply List.nth_error_None in Hg'; lia].
    destruct (set_arguments_shape_nth _ _ Hsh _ _ Hg') as (sg' & Hsg' & Hk'). rewrite Hn in Hsg'. injection Hsg' as <-.
    destruct g' as [κ' A' | t']; [destruct Hk' as [F' Hk']; discriminate | eauto]. }
  induction gs1 as [| g gs1 IH] using List.rev_ind; intros rest Egs.
  - cbn [cargs_ctx cargs_ctx_aux List.app List.length List.firstn ctx_kinds List.map List.rev set_env_extend_kinded]. exact Hθp.
  - specialize (IH (g :: rest) ltac:(rewrite Egs, <- List.app_assoc; reflexivity)).
    set (i := List.length gs1) in *.
    assert (Hgi : List.nth_error gs i = Some g) by (rewrite Egs, <- List.app_assoc, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
    destruct (set_arguments_shape_nth _ _ Hsh _ _ Hgi) as (sg & Hsg & Hsgk).
    assert (Hi : i < List.length vals) by (rewrite Hlv; apply List.nth_error_Some; congruence).
    destruct (List.nth_error vals i) as [v |] eqn:Hv; [| apply List.nth_error_None in Hv; lia].
    assert (Hfirst : List.firstn (List.length (gs1 ++ [g])) vals = List.firstn i vals ++ [v])
      by (rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r; apply firstn_S_nth; exact Hv).
    rewrite Hfirst, cargs_ctx_snoc.
    assert (Hlk : List.length (ctx_kinds (cargs_ctx p D Mk gs1)) = List.length (List.firstn i vals))
      by (rewrite length_ctx_kinds, length_cargs_ctx, List.length_firstn; lia).
    assert (Hlc : List.length (cargs_ctx p D Mk gs1) = List.length (List.firstn i vals))
      by (rewrite length_cargs_ctx, List.length_firstn; lia).
    assert (Egs1 : gs = gs1 ++ (g :: rest)) by (rewrite Egs, <- List.app_assoc; reflexivity).
    set (θo := set_env_extend_kinded θp (ctx_kinds (cargs_ctx p D Mk gs1)) (List.firstn i vals)) in *.
    set (Lθ := set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo).
    (* the extended environment's values *)
    assert (HLθ : Lθ = L0 ++ List.firstn i vals).
    { unfold Lθ. rewrite set_env_values_app. f_equal.
      - unfold L0. apply set_env_values_agree. intros x _. unfold set_env_drop, θo. rewrite Hlc, set_env_extend_kinded_ge. reflexivity.
      - unfold θo. apply set_env_values_extend_kinded_any. exact Hlc. }
    (* one more entry, of a type read off the context before it *)
    assert (Gen : forall κ A F, cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [g] = [ce_ass κ A] ->
              set_reads T γ (cargs_ctx p D Mk gs1 ++ im_params D Mk) A F -> set_mem v (code_carrier (F Lθ)) ->
              set_env_in T γ ((cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [g] ++ cargs_ctx p D Mk gs1) ++ im_params D Mk)
                (set_env_extend_kinded θp (ctx_kinds (cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [g] ++ cargs_ctx p D Mk gs1))
                   (List.firstn i vals ++ [v]))).
    { intros κ A F E HF Hx. rewrite E. cbn [List.app]. rewrite ctx_kinds_cons, set_env_extend_kinded_snoc by exact Hlk.
      fold θo. cbn [centry_kind]. split; [exact IH |]. cbn [set_entry_rel]. exists v, v, (F Lθ).
      constructor; [reflexivity | reflexivity | exact (HF θo IH) | exact Hx | apply set_eq_refl]. }
    assert (Hgs_eq : cargs_ctx p D Mk gs =
              cargs_ctx_aux p D (im_nn Mk) (cargs_pat (gs1 ++ [g])) rest ++ (cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [g] ++ cargs_ctx p D Mk gs1))
      by (rewrite Egs, cargs_ctx_app, cargs_ctx_snoc; reflexivity).
    set (pre_e := L0 ++ erase_args (List.firstn i sgs) (List.firstn i vals)).
    pose proof (arguments_fit_nth _ _ _ _ _ _ Hfit i _ v Hsg Hv) as Hm. cbn beta iota in Hm. fold pre_e in Hm.
    assert (Hiv : i <= List.length sgs) by lia. assert (Hiv' : i <= List.length vals) by lia.
    destruct g as [κ A0 | t].
    + (* a non-recursive argument: of its type at the values, which ignores the recursive ones before it *)
      destruct Hsgk as [Fp ->].
      set (A := exp_wk A0 (wk_pat (cargs_pat gs1))).
      assert (E : cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [ca_arg κ A0] = [ce_ass κ A]) by reflexivity.
      rewrite E in Hgs_eq. cbn [List.app] in Hgs_eq.
      destruct (set_tele_types_entry T γ _ _ _ Htys _ κ A _ Hgs_eq) as (F & HF & HnF).
      rewrite List.nth_error_map, length_cargs_ctx in HnF. fold i in HnF. rewrite Hsg in HnF. cbn in HnF. injection HnF as <-.
      apply (Gen κ A Fp E HF).
      assert (Hrp : list_function_respects Fp) by (rewrite List.Forall_forall in Hrs; exact (Hrs _ (List.nth_error_In _ _ Hsg))).
      eapply set_mem_eq_r; [| exact Hm]. apply code_carrier_resp. rewrite HLθ. apply set_eq_sym.
      apply erase_args_ignored; [| lia | lia].
      intros n L' ty ds tg tp Hn Hsn HL'. destruct (Hrec _ _ _ _ _ Hsn) as (tn & Htn).
      rewrite HL0 in HL' |- *.
      exact (set_constructor_ok_ignores _ _ _ _ _ _ _ _ Hcok n tn i _ L' Htn Hn Hsg HL').
    + (* a recursive argument: in its set of shapes, within its code *)
      destruct Hsgk as (Fr & ds & tparams & -> & Hlds).
      set (A := ptyp_ty p D (im_nn Mk) (cargs_pat gs1) t).
      assert (E : cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [ca_rec t] = [ce_ass ak_relevant A]) by reflexivity.
      rewrite E in Hgs_eq. cbn [List.app] in Hgs_eq.
      destruct (set_tele_types_entry T γ _ _ _ Htys _ ak_relevant A _ Hgs_eq) as (F & HF & HnF).
      rewrite List.nth_error_map, length_cargs_ctx in HnF. fold i in HnF. rewrite Hsg in HnF. cbn in HnF. injection HnF as <-.
      apply (Gen ak_relevant A Fr E HF).
      pose proof (set_constructor_ok_recursive _ _ _ _ _ _ _ _ Hcok i t Fr ds (ptyp_mem t) tparams θo Hgi Hsg) as Hrc.
      rewrite Egs1 in Hrc. unfold i in Hrc. rewrite cargs_ctx_prefix in Hrc. specialize (Hrc IH). cbn [set_argument_type] in HF.
      fold Lθ in Hrc.
      assert (Hrsg : argument_respects (set_argument_recursive Fr ds (ptyp_mem t) tparams))
        by (rewrite List.Forall_forall in Hrs; exact (Hrs _ (List.nth_error_In _ _ Hsg))).
      destruct Hrsg as [Hds Htp].
      assert (Hign : forall n L', n < i -> (exists ty ds' tg tp, List.nth_error sgs n = Some (set_argument_recursive ty ds' tg tp)) ->
                 List.length L' = List.length L0 + i ->
                 argument_ignores (List.length L0 + n) (set_argument_recursive Fr ds (ptyp_mem t) tparams) L').
      { intros n L' Hn (ty & ds' & tg & tp & Hsn) HL'. destruct (Hrec _ _ _ _ _ Hsn) as (tn & Htn). rewrite HL0 in HL' |- *.
        exact (set_constructor_ok_ignores _ _ _ _ _ _ _ _ Hcok n tn i _ L' Htn Hn Hsg HL'). }
      assert (Hdom : forall k' d pts0, List.nth_error ds k' = Some d -> List.length pts0 = k' ->
                set_eq (d (pre_e ++ pts0)) (d (Lθ ++ pts0))).
      { intros k' d pts0 Hk' Hl'. rewrite HLθ. apply set_eq_sym. unfold pre_e.
        apply (erase_args_ignored (fun L => d (L ++ pts0)) L0 sgs vals i); [| exact Hiv | exact Hiv'].
        intros n L' ty ds' tg tp Hn Hsn HL'. exact (proj1 (Hign n L' Hn ltac:(eauto) HL') k' d pts0 Hk' Hl'). }
      assert (Htps : forall pts, List.length pts = List.length ds -> list_set_eq (tparams (pre_e ++ pts)) (tparams (Lθ ++ pts))).
      { intros pts Hl'. rewrite HLθ. apply list_set_eq_sym. unfold pre_e.
        apply (erase_args_ignored_list (fun L => tparams (L ++ pts)) L0 sgs vals i); [| exact Hiv | exact Hiv'].
        intros n L' ty ds' tg tp Hn Hsn HL'. exact (proj2 (Hign n L' Hn ltac:(eauto) HL') pts Hl'). }
      assert (Hus : list_set_eq (List.firstn (ind_nu D) Lθ) elim_uniform_values)
        by (rewrite HLθ, List.firstn_app, (proj2 (Nat.sub_0_le _ _) Hnu), List.app_nil_r; exact Hpre0).
      assert (Hpre : list_set_eq (List.firstn (ind_nu D) pre_e) elim_uniform_values)
        by (unfold pre_e; rewrite List.firstn_app, (proj2 (Nat.sub_0_le _ _) Hnu), List.app_nil_r; exact Hpre0).
      pose proof (set_group_ok_carrier_resp _ _ _ _ _ HG) as HGresp.
      pose proof (shape_set_sub_code G HGresp U S pre_e (ptyp_mem t) tparams ds nil Hds Htp
                    (fun pts Hpts => recursive_leaf_sub k Mk gs sgs gs1 t rest Fr ds (ptyp_mem t) tparams θo (Fr Lθ) pre_e Hk Hcok Egs1 Hsg
                                       Hds Htp Hlds IH (HF θo IH) Hrc Hus Hpre Hdom Htps pts Hpts) v Hm) as Hv1.
      eapply set_mem_eq_r; [| exact Hv1]. apply code_carrier_resp.
      eapply set_eq_trans; [| apply set_eq_sym; exact Hrc]. rewrite HLθ.
      apply set_eq_sym. unfold pre_e.
      apply (erase_args_ignored (fun L => shape_code G ds (ptyp_mem t) tparams L nil) L0 sgs vals i); [| exact Hiv | exact Hiv'].
      intros n L' ty ds' tg tp Hn Hsn HL'. destruct (Hign n L' Hn ltac:(eauto) HL') as [H1 H2].
      apply (shape_code_erase G HGresp); [exact Hds | exact Htp | unfold G; rewrite group_uniform_count, HL0; unfold im_np; lia | lia
                                         | exact H1 | exact H2].
Qed.

(** An instance of a member's parameters whose uniform ones have the
    uniform values: its non-uniform parameters' values extend [ρ] to an
    environment of the non-uniform parameters instantiated at [Us]. *)
Lemma nparams_env : forall k Mk SMk c gs θk, ind_member D k = Some Mk ->
    List.nth_error (set_group_members (global_group γ p)) k = Some SMk -> In (c, gs) (im_cons Mk) ->
    set_env_in T γ (im_params D Mk) θk -> list_set_eq (uniform_values D Mk θk) elim_uniform_values ->
    set_env_in T γ (tele_sub (im_nparams Mk) (sb_of_list sb_id Us) ++ Γ)
      (set_env_extend_kinded ρ (ctx_kinds (im_nparams Mk)) (set_env_values (im_nparams Mk) θk)).
Proof.
  intros k Mk SMk c gs θk Hk HSk Hin Hθk Huni.
  pose proof (gctx_closed_ind _ _ _ _ (wf_gctx_closed _ _ _ HcΓ) HD) as Hcl.
  pose proof (decls_of_ctx _ _ _ HcΓ) as HDs.
  pose proof (cargs_ctx_closed p D k Mk _ gs nil gs Hcl Hk Hin eq_refl) as Hs0. cbn [cargs_ctx cargs_ctx_aux List.app] in Hs0.
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hgw HDs HD Hk Hin nil gs eq_refl) as (Hw0 & _ & _). cbn [cargs_ctx cargs_ctx_aux List.app] in Hw0.
  pose proof (member_params_ctx _ _ _ Hk HSk) as Hc0.
  pose proof (decl_closed_params_ass _ _ _ Hcl Hk) as Hass0.
  pose proof (wf_ctx_closed_app _ _ _ _ Hass0 Hs0 Hw0 HcΓ) as HwΓ0.
  assert (HcΓ0 : set_ctx T γ (im_params D Mk ++ Γ)).
  { pose proof (set_ctx_moved T γ Hfn Hmods _ nil Γ _ _ (set_gsub_drop T γ _ HcΓ) HΓ ltac:(rewrite List.app_nil_r; exact Hc0)
                  ltac:(rewrite List.app_nil_r; exact Hw0)) as H.
    rewrite tele_sub_closed in H by exact Hs0. exact H. }
  unfold im_params in *. apply List.Forall_app in Hass0 as [HassN HassU].
  apply (inst_env_of_closed Γ (ind_uparams D) (sb_of_list sb_id Us) Fσ Hσ HΓ HcΓ (im_nparams Mk) θk Hs0 HassN Hc0 HcΓ0 Hw0 HwΓ0
           Hθk HassU ρ Hρ).
  apply list_set_eq_sym. exact Huni.
Qed.

(** [recursive_arg_with Mk gs1 t F ds target tparams θo pre_e v]: the
    recursive argument [v] of shape [t], after the arguments [gs1], read
    at the environment [θo] of their closed context: its domains and its
    target's parameters after the values [pre_e] the carriers read are
    those after [θo]'s values, its type is its code there, and it is in
    its set of shapes. *)
Record recursive_arg_with (Mk : imember) (gs1 : list carg) (t : ptyp) (F : list aczel_set -> aczel_set)
    (ds : list (list aczel_set -> aczel_set)) (target : nat) (tparams : list aczel_set -> list aczel_set) (θo : set_env)
    (pre_e : list aczel_set) (v : aczel_set) : Prop :=
  { (** The domains, after either values *)
    recursive_arg_domains : forall k' d pts0, List.nth_error ds k' = Some d -> List.length pts0 = k' ->
      set_eq (d (pre_e ++ pts0)) (d (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo ++ pts0))
    (** The target's parameters, after either values *)
  ; recursive_arg_tparams : forall pts, List.length pts = List.length ds ->
      list_set_eq (tparams (pre_e ++ pts)) (tparams (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo ++ pts))
    (** The argument's type at [θo] *)
  ; recursive_arg_type : set_interp T γ (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo (ptyp_ty p D (im_nn Mk) (cargs_pat gs1) t)
      (F (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo))
    (** is its shape's code *)
  ; recursive_arg_code : set_eq (F (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo))
      (shape_code (global_group γ p) ds target tparams (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo) nil)
    (** The argument is in its set of shapes *)
  ; recursive_arg_set : set_mem v (shape_set (global_group γ p) U S pre_e ds target tparams nil) }.

(** A recursive argument fitting the candidate carriers, at an
    environment of the closed context of the arguments before it whose
    values are those the carriers read, with the recursive ones in place. *)
Lemma recursive_arg_setting : forall k Mk SMk cs gs L0 vals gs1 t gs2 F ds target tparams θo v,
    ind_member D k = Some Mk -> List.nth_error (set_group_members (global_group γ p)) k = Some SMk ->
    In cs (set_member_constructors SMk) -> ind_con Mk (set_constructor_name cs) = Some gs ->
    set_constructor_ok T γ p D (global_group γ p) Mk gs (set_constructor_arguments cs) ->
    arguments_fit (global_group γ p) U S L0 (set_constructor_arguments cs) vals -> List.length L0 = im_np D Mk ->
    gs = gs1 ++ ca_rec t :: gs2 ->
    List.nth_error (set_constructor_arguments cs) (List.length gs1) = Some (set_argument_recursive F ds target tparams) ->
    List.nth_error vals (List.length gs1) = Some v ->
    set_env_in T γ (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo ->
    list_set_eq (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo) (L0 ++ List.firstn (List.length gs1) vals) ->
    recursive_arg_with Mk gs1 t F ds target tparams θo
      (L0 ++ erase_args (List.firstn (List.length gs1) (set_constructor_arguments cs)) (List.firstn (List.length gs1) vals)) v.
Proof.
  intros k Mk SMk cs gs L0 vals gs1 t gs2 Fr ds target tparams θo v Hk HSk Hcs Hgs Hcok Hfit HL0 Egs Hsg Hv Hθo HLθ.
  set (G := global_group γ p) in *. set (sgs := set_constructor_arguments cs) in *.
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG. fold G in HG.
  pose proof (set_constructor_ok_shape _ _ _ _ _ _ _ _ Hcok) as Hsh.
  pose proof (set_arguments_shape_length _ _ Hsh) as Hlsh.
  pose proof (arguments_fit_length _ _ _ _ _ _ Hfit) as Hlv.
  pose proof (set_group_ok_respects _ _ _ _ _ HG _ _ _ HSk Hcs) as Hrs. fold sgs in Hrs.
  pose proof (set_constructor_ok_types _ _ _ _ _ _ _ _ Hcok) as Htys.
  set (i := List.length gs1) in *.
  assert (Hgi : List.nth_error gs i = Some (ca_rec t)) by (rewrite Egs, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
  assert (Hrec : forall n ty ds tg tp, List.nth_error sgs n = Some (set_argument_recursive ty ds tg tp) ->
            exists t, List.nth_error gs n = Some (ca_rec t)).
  { intros n ty ds' tg tp Hn. assert (Hn' : n < List.length gs) by (rewrite <- Hlsh; apply List.nth_error_Some; congruence).
    destruct (List.nth_error gs n) as [g' |] eqn:Hg'; [| apply List.nth_error_None in Hg'; lia].
    destruct (set_arguments_shape_nth _ _ Hsh _ _ Hg') as (sg' & Hsg' & Hk'). rewrite Hn in Hsg'. injection Hsg' as <-.
    destruct g' as [κ' A' | t']; [destruct Hk' as [F' Hk']; discriminate | eauto]. }
  destruct (set_arguments_shape_nth _ _ Hsh _ _ Hgi) as (sg & Hsg' & Hsgk). rewrite Hsg in Hsg'. injection Hsg' as <-.
  destruct Hsgk as (Fr' & ds' & tparams' & E' & Hlds). injection E' as <- <- Htg <-. subst target.
  assert (Hi : i < List.length vals) by (rewrite Hlv; apply List.nth_error_Some; congruence).
  set (A := ptyp_ty p D (im_nn Mk) (cargs_pat gs1) t).
  assert (Hgs_eq : cargs_ctx p D Mk gs =
            cargs_ctx_aux p D (im_nn Mk) (cargs_pat (gs1 ++ [ca_rec t])) gs2 ++ ([ce_ass ak_relevant A] ++ cargs_ctx p D Mk gs1))
    by (rewrite Egs, <- (List.app_nil_l gs2), app_comm_cons, List.app_assoc, cargs_ctx_app, cargs_ctx_snoc; reflexivity).
  destruct (set_tele_types_entry T γ _ _ _ Htys _ ak_relevant A _ Hgs_eq) as (F & HF & HnF).
  rewrite List.nth_error_map, length_cargs_ctx in HnF. fold i in HnF. rewrite Hsg in HnF. cbn in HnF. injection HnF as <-.
  pose proof (set_constructor_ok_recursive _ _ _ _ _ _ _ _ Hcok i t Fr ds (ptyp_mem t) tparams θo Hgi Hsg) as Hrc.
  rewrite Egs in Hrc. unfold i in Hrc. rewrite cargs_ctx_prefix in Hrc. specialize (Hrc Hθo).
  set (Lθ := set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo) in *.
  set (pre_e := L0 ++ erase_args (List.firstn i sgs) (List.firstn i vals)).
  assert (Hrsg : argument_respects (set_argument_recursive Fr ds (ptyp_mem t) tparams))
    by (rewrite List.Forall_forall in Hrs; exact (Hrs _ (List.nth_error_In _ _ Hsg))).
  destruct Hrsg as [Hds Htp].
  pose proof (arguments_fit_nth _ _ _ _ _ _ Hfit i _ v Hsg Hv) as Hm. cbn beta iota in Hm. fold pre_e in Hm.
  assert (Hiv : i <= List.length sgs) by lia. assert (Hiv' : i <= List.length vals) by lia.
  assert (Hign : forall n L', n < i -> (exists ty ds' tg tp, List.nth_error sgs n = Some (set_argument_recursive ty ds' tg tp)) ->
             List.length L' = List.length L0 + i ->
             argument_ignores (List.length L0 + n) (set_argument_recursive Fr ds (ptyp_mem t) tparams) L').
  { intros n L' Hn (ty & ds' & tg & tp & Hsn) HL'. destruct (Hrec _ _ _ _ _ Hsn) as (tn & Htn). rewrite HL0 in HL' |- *.
    exact (set_constructor_ok_ignores _ _ _ _ _ _ _ _ Hcok n tn i _ L' Htn Hn Hsg HL'). }
  assert (Hdom : forall k' d pts0, List.nth_error ds k' = Some d -> List.length pts0 = k' ->
            set_eq (d (pre_e ++ pts0)) (d (Lθ ++ pts0))).
  { intros k' d pts0 Hk' Hl'.
    assert (Hd : list_function_respects d) by (rewrite List.Forall_forall in Hds; exact (Hds _ (List.nth_error_In _ _ Hk'))).
    eapply set_eq_trans; [| apply Hd; apply list_set_eq_app; [apply list_set_eq_sym; exact HLθ | apply list_set_eq_refl]].
    apply set_eq_sym. unfold pre_e.
    apply (erase_args_ignored (fun L => d (L ++ pts0)) L0 sgs vals i); [| exact Hiv | exact Hiv'].
    intros n L' ty ds' tg tp Hn Hsn HL'. exact (proj1 (Hign n L' Hn ltac:(eauto) HL') k' d pts0 Hk' Hl'). }
  assert (Htps : forall pts, List.length pts = List.length ds -> list_set_eq (tparams (pre_e ++ pts)) (tparams (Lθ ++ pts))).
  { intros pts Hl'.
    eapply list_set_eq_trans; [| apply Htp; apply list_set_eq_app; [apply list_set_eq_sym; exact HLθ | apply list_set_eq_refl]].
    apply list_set_eq_sym. unfold pre_e.
    apply (erase_args_ignored_list (fun L => tparams (L ++ pts)) L0 sgs vals i); [| exact Hiv | exact Hiv'].
    intros n L' ty ds' tg tp Hn Hsn HL'. exact (proj2 (Hign n L' Hn ltac:(eauto) HL') pts Hl'). }
  constructor; [exact Hdom | exact Htps | exact (HF θo Hθo) | exact Hrc | exact Hm].
Qed.

End Arguments.

(** ** The Eliminator's Results at One Environment *)

Section Results.
  (** The eliminator's context and environment *)
  Variables (Γ : ctx) (ρ : set_env).
  (** Its sort, group, uniform parameters and blocks *)
  Variables (r : abs_kind) (p : qname) (Us : list exp) (Bks : list eblock).
  (** A set holding every result *)
  Variable V : aczel_set.
  (** The environment is one of the context *)
  Hypothesis Hρ : set_env_in T γ Γ ρ.

Lemma set_elim_functional : forall j v res res', set_elim T γ Γ ρ r p Us Bks j v res -> set_elim T γ Γ ρ r p Us Bks j v res' ->
    set_eq res res'.
Proof.
  intros * H H'. destruct (set_interp_functional_all T γ Hfn Hmods) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hel & _).
  exact (Hel _ _ _ _ _ _ _ _ _ H _ _ _ (set_env_rel_eq T γ _ _ _ Hρ) (set_eq_refl _) H').
Qed.

Lemma set_ih_functional : forall t v ihs ihs', set_ih T γ Γ ρ r p Us Bks t v ihs -> set_ih T γ Γ ρ r p Us Bks t v ihs' ->
    list_set_eq ihs ihs'.
Proof.
  intros * H H'. destruct (set_interp_functional_all T γ Hfn Hmods) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hih).
  exact (Hih _ _ _ _ _ _ _ _ _ H _ _ _ (set_env_rel_eq T γ _ _ _ Hρ) (set_eq_refl _) H').
Qed.

(** A result is one at a value equal to the element. *)
Lemma set_elim_resp_value : forall j v v' res, set_eq v v' -> set_elim T γ Γ ρ r p Us Bks j v res ->
    set_elim T γ Γ ρ r p Us Bks j v' res.
Proof.
  intros * E H. destruct (set_elim_strip T γ _ _ _ _ _ _ _ _ _ H) as (res0 & E0 & H0).
  apply (set_elim_resp T γ _ _ _ _ _ _ _ _ res0); [| apply set_eq_sym; exact E0].
  destruct H0. eapply set_elim_con; try eassumption. eapply set_eq_trans; [apply set_eq_sym; exact E | eassumption].
Qed.

Lemma elim_result_pred_resp : forall j v, respects_set_eq (fun z => exists res, set_elim T γ Γ ρ r p Us Bks j v res /\ set_eq res z).
Proof. intros j v x y E (res & H & Ex). exists res. split; [exact H | eapply set_eq_trans; eassumption]. Qed.

(** The eliminator's result at the member [j] and the element [v]. *)
Definition elim_result (j : nat) (v : aczel_set) : aczel_set :=
  set_describe V (fun z => exists res, set_elim T γ Γ ρ r p Us Bks j v res /\ set_eq res z).

(** A result in [V] is the described one. *)
Lemma elim_result_eq : forall j v res, set_elim T γ Γ ρ r p Us Bks j v res -> set_mem res V ->
    set_eq (elim_result j v) res.
Proof.
  intros * H HV. apply set_describe_eq; [apply elim_result_pred_resp | exact HV | exists res; split; [exact H | apply set_eq_refl] |].
  intros w _ (res' & H' & E'). eapply set_eq_trans; [apply set_eq_sym; exact E' |]. exact (set_elim_functional _ _ _ _ H' H).
Qed.

(** The described result is a result. *)
Lemma elim_result_spec : forall j v res, set_elim T γ Γ ρ r p Us Bks j v res -> set_mem res V ->
    set_elim T γ Γ ρ r p Us Bks j v (elim_result j v).
Proof. intros * H HV. apply (set_elim_resp T γ _ _ _ _ _ _ _ _ res); [exact H | apply set_eq_sym; exact (elim_result_eq _ _ _ H HV)]. Qed.

(** The recursive result of an element [v] along a leaf path. *)
Fixpoint leaf_result (l : leaf_path) (v : aczel_set) : aczel_set :=
  match l with
  | leaf_self j _ => elim_result j v
  | leaf_pi _ l' => graph_set (relation_domain v) (fun b => leaf_result l' (set_apply v b))
  | leaf_proj f _ l' => leaf_result l' (tuple_field v f)
  end.

Lemma elim_result_resp : forall j v v', set_eq v v' -> set_eq (elim_result j v) (elim_result j v').
Proof.
  intros j v v' E. unfold elim_result, set_describe. apply union_set_resp.
  apply separation_set_resp; [apply elim_result_pred_resp | apply elim_result_pred_resp | apply set_eq_refl |].
  intros z; split; intros (res0 & Hr & Ez); exists res0; (split; [| exact Ez]); eapply set_elim_resp_value; try exact Hr;
    [exact E | apply set_eq_sym; exact E].
Qed.

Lemma leaf_result_resp : forall l v v', set_eq v v' -> set_eq (leaf_result l v) (leaf_result l v').
Proof.
  induction l as [j Ps | B l IH | f ns l IH]; intros v v' E; cbn [leaf_result].
  - apply elim_result_resp; exact E.
  - apply graph_set_resp; [intros b b' Eb; apply IH; apply set_apply_resp; [apply set_eq_refl | exact Eb]
                          | intros b b' Eb; apply IH; apply set_apply_resp; [apply set_eq_refl | exact Eb]
                          | apply relation_domain_resp; exact E |].
    intros b _. apply IH. apply set_apply_resp; [exact E | apply set_eq_refl].
  - apply IH. apply tuple_field_resp. exact E.
Qed.

(** A list of values indexed by positions, pointwise equal to a map. *)
Lemma map_seq_set_eq : forall {X : Type} (L : list X) (f : nat -> aczel_set) (g : X -> aczel_set) k,
    (forall i x, List.nth_error L i = Some x -> set_eq (f (k + i)) (g x)) ->
    list_set_eq (List.map f (List.seq k (List.length L))) (List.map g L).
Proof.
  intros X L f g. induction L as [| x L IH]; intros k H; cbn [List.length List.seq List.map]; constructor.
  - specialize (H 0 x eq_refl). rewrite Nat.add_0_r in H. exact H.
  - apply IH. intros i y Hy. replace (S k + i) with (k + S i) by lia. exact (H (S i) y Hy).
Qed.

Lemma map_set_eq : forall {X : Type} (L : list X) (f g : X -> aczel_set), (forall x, In x L -> set_eq (f x) (g x)) ->
    list_set_eq (List.map f L) (List.map g L).
Proof. intros X L f g H. induction L as [| x L IH]; cbn; constructor; [apply H; left; reflexivity | apply IH; intros; apply H; right; assumption]. Qed.

(** A moved path has the same results. *)
Lemma leaf_result_wk : forall l φ v, set_eq (leaf_result (leaf_wk φ l) v) (leaf_result l v).
Proof.
  induction l as [j Ps | B l IH | f ns l IH]; intros φ v; cbn [leaf_wk leaf_result].
  - apply set_eq_refl.
  - apply graph_set_resp; [intros b b' Eb; apply leaf_result_resp; apply set_apply_resp; [apply set_eq_refl | exact Eb]
                          | intros b b' Eb; apply leaf_result_resp; apply set_apply_resp; [apply set_eq_refl | exact Eb]
                          | apply set_eq_refl |].
    intros b _. apply IH.
  - apply IH.
Qed.

(** Arguments have their recursive results up to equality. *)
Lemma set_ihs_resp_results : forall gs vs ihs, set_ihs T γ Γ ρ r p Us Bks gs vs ihs ->
    forall ihs', list_set_eq ihs ihs' -> set_ihs T γ Γ ρ r p Us Bks gs vs ihs'.
Proof.
  intros gs. induction gs as [| g gs IH]; intros vs ihs H ihs' E; inversion H as [| ? ? ? ? ? ? κ T0 ? v vs0 ihs0 H0 | ? ? ? ? ? ? t ? v vs0 ihs1 ihs2 H1 H2];
    subst.
  - inversion E. constructor.
  - constructor. exact (IH _ _ H0 _ E).
  - destruct (List.Forall2_app_inv_l _ _ E) as (ihs1' & ihs2' & E1 & E2 & ->).
    constructor; [exact (set_ih_resp T γ _ _ _ _ _ _ _ _ _ _ H1 E1) | exact (IH _ _ H2 _ E2)].
Qed.

(** ** The Recursive Results Along a Shape *)

Section Shapes.
  (** The group *)
  Variable D : ind_decl.
  Hypothesis HD : ind_lookup gc_deps gc_stack p = Some D.
  (** Its record views' paths are read off their fields *)
  Hypothesis Hco : leaves_coherent D.
  (** It is typed *)
  Hypothesis HDt : decl_typed gc_deps gc_stack D.

(** [end_results j w]: at the end of a shape, the element [w] of the member
    [j] has a result, at a member with a block, and its fields have the
    recursive results along the record view's paths, at a record view. *)
Record end_results (j : nat) (w : aczel_set) (Mj : imember) : Prop :=
  { (** [Mj] is the member *)
    end_results_member : ind_member D j = Some Mj
    (** A member with a block: a result in [V] *)
  ; end_results_block : im_is_rview Mj = false -> exists res, set_elim T γ Γ ρ r p Us Bks j w res /\ set_mem res V
    (** A record view: its fields' results along its paths *)
  ; end_results_rview : forall qr Is fl c gs, im_head Mj = mh_record qr Is fl -> im_cons Mj = [(c, gs)] ->
      set_ihs T γ Γ ρ r p Us Bks gs (List.map (tuple_field w) fl)
        (List.map (fun l => leaf_result l w) (fields_leaves (rview_leaves D) nil (List.combine fl gs))) }.

(** [shape_results t a]: every value of [a] at the domains of [t] has its
    results at the shape's end. *)
Fixpoint shape_results (t : ptyp) (a : aczel_set) : Prop :=
  match t with
  | pt_self j _ => exists Mj, end_results j a Mj
  | pt_pi _ t' => forall b, set_mem b (relation_domain a) -> shape_results t' (set_apply a b)
  end.

(** An argument whose values have their results has its recursive results
    along the shape's paths. *)
Lemma set_ih_of_shape_results : forall t m a, shape_results t a ->
    set_ih T γ Γ ρ r p Us Bks t a (List.map (fun l => leaf_result l a) (shape_leaves (rview_leaves D) m t)).
Proof.
  induction t as [j Ps | B t IH]; intros m a Ha; cbn [shape_results shape_leaves] in *.
  - destruct Ha as (Mj & [HMj Hblk Hrv]).
    destruct (im_is_rview Mj) eqn:Hr.
    + destruct (im_head Mj) as [pm | qc k' Is0 vm | qr Is fl] eqn:Hh; unfold im_is_rview in Hr; rewrite Hh in Hr; try discriminate.
      destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ HDt) _ _ _ _ _ HMj Hh) as (gs & Hcs & _).
      pose proof (Hco _ _ _ _ _ _ _ HMj Hh Hcs) as E. rewrite E.
      eapply (set_ih_resp T γ); [eapply set_ih_rview; [exact HD | exact HMj | exact Hh | exact Hcs | exact (Hrv _ _ _ _ _ eq_refl Hcs)] |].
      rewrite List.map_map. apply map_set_eq. intros l _. apply set_eq_sym. apply leaf_result_wk.
    + rewrite (rview_leaves_not_rview _ _ _ HMj Hr). cbn [List.map].
      destruct (Hblk eq_refl) as (res & Hres & HV).
      eapply set_ih_self; [exact HD | exact HMj | exact Hr |]. exact (elim_result_spec _ _ _ Hres HV).
  - rewrite List.map_map.
    set (Ls := shape_leaves (rview_leaves D) (S m) t).
    eapply (set_ih_resp T γ);
      [eapply (set_ih_pi T γ _ _ _ _ _ _ D B t a (fun b => List.map (fun l => leaf_result l (set_apply a b)) Ls));
         [exact HD |]; intros b Hb; exact (IH (S m) (set_apply a b) (Ha b Hb)) |].
    rewrite (length_shape_leaves (rview_leaves D) t 0 (S m)). fold Ls.
    apply map_seq_set_eq. intros i l Hi. cbn [leaf_result Nat.add].
    apply graph_set_resp; [| | apply set_eq_refl |].
    + intros b b' Eb. apply list_set_eq_nth. apply map_set_eq. intros l0 _. apply leaf_result_resp.
      apply set_apply_resp; [apply set_eq_refl | exact Eb].
    + intros b b' Eb. apply leaf_result_resp. apply set_apply_resp; [apply set_eq_refl | exact Eb].
    + intros b _.
      assert (Hn : List.nth i (List.map (fun l0 => leaf_result l0 (set_apply a b)) Ls) empty_set = leaf_result l (set_apply a b))
        by (apply List.nth_error_nth; rewrite List.nth_error_map, Hi; reflexivity).
      rewrite Hn. apply set_eq_refl.
Qed.

End Shapes.

(** ** The Recursive Results' Types Along Leaf Paths *)

(** A substitution of terms over [β] agrees with the environment extended
    by their values. *)
Lemma sub_agrees_of_list : forall Ψ ρe L vals, set_interp_list T γ Ψ ρe L vals ->
    forall β ρ0 κs, (forall y, sub_entry_agrees T γ Ψ ρe (β y) (ρ0 y)) ->
    forall y, sub_entry_agrees T γ Ψ ρe (sb_of_list β L y) (set_env_extend_kinded ρ0 κs vals y).
Proof.
  intros Ψ ρe L vals H. induction H as [Ξ ρ1 | Ξ ρ1 M Ms v vs HM HMs IH]; intros β ρ0 κs Hβ y; [exact (Hβ y) |].
  cbn [sb_of_list set_env_extend_kinded]. apply IH. intros [| z]; cbn [sb_extend set_env_extend].
  - split; cbn; [exact HM | constructor].
  - exact (Hβ z).
Qed.

(** An entry's agreement survives a renaming, the entry renamed. *)
Lemma sub_agrees_wk : forall Ψ' Ψ ρe ρe' φ s v, gc_deps ⍮ gc_stack ⍮ Ψ' ⊢ʷ φ : Ψ -> env_agrees ρe ρe' φ ->
    sub_entry_agrees T γ Ψ ρe s v -> sub_entry_agrees T γ Ψ' ρe' (sentry_sub s (sb_of_wk φ)) v.
Proof.
  intros * Hw Hag [He Hm]. rewrite sentry_sub_of_wk. unfold sub_entry_agrees. rewrite <- sentry_exp_wk, sentry_modexp_wk.
  assert (Hag' : env_agrees ρe ρe' (wk_qn (List.length (@nil centry)) φ)) by exact Hag.
  split.
  - exact (proj1 (set_interp_wk_all T γ) _ _ _ _ He nil Ψ _ _ _ (Build_wk_setting _ _ _ _ _ _ _ eq_refl Hw Hag')).
  - exact (proj1 (proj2 (proj2 (proj2 (set_interp_wk_all T γ)))) _ _ _ _ Hm nil Ψ _ _ _ (Build_wk_setting _ _ _ _ _ _ _ eq_refl Hw Hag')).
Qed.

(** An entry's agreement survives one more binder, the entry weakened. *)
Lemma sub_agrees_shift : forall Ψ ρe e d s v, ⊢ gc_deps ⍮ gc_stack ⍮ e :: Ψ -> sub_entry_agrees T γ Ψ ρe s v ->
    sub_entry_agrees T γ (e :: Ψ) (set_env_extend ρe d) (sentry_sub s (sb_of_wk wk_shift)) v.
Proof.
  intros * Hc [He Hm]. rewrite sentry_sub_of_wk. unfold sub_entry_agrees. rewrite <- sentry_exp_wk, sentry_modexp_wk.
  assert (Hw : gc_deps ⍮ gc_stack ⍮ e :: Ψ ⊢ʷ wk_shift : Ψ) by (apply wf_wk_shift; exact Hc).
  assert (Hag : env_agrees ρe (set_env_extend ρe d) (wk_qn (List.length (@nil centry)) wk_shift)) by (intros y; reflexivity).
  split.
  - exact (proj1 (set_interp_wk_all T γ) _ _ _ _ He nil Ψ _ _ _ (Build_wk_setting _ _ _ _ _ _ _ eq_refl Hw Hag)).
  - exact (proj1 (proj2 (proj2 (proj2 (set_interp_wk_all T γ)))) _ _ _ _ Hm nil Ψ _ _ _ (Build_wk_setting _ _ _ _ _ _ _ eq_refl Hw Hag)).
Qed.

(** A term read at an environment a substitution realizes keeps its value
    substituted. *)
Lemma interp_realized : forall Tc θ Ψ ρe σ M v, ⊢ gc_deps ⍮ gc_stack ⍮ Tc -> gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ σ : Tc ->
    (forall y, sub_entry_agrees T γ Ψ ρe (σ y) (θ y)) -> set_interp T γ Tc θ M v -> set_interp T γ Ψ ρe (exp_sub M σ) v.
Proof.
  intros * Hc Hσ Hag HM.
  assert (Hs : sub_setting T γ Tc θ nil Tc Ψ σ ρe ρe)
    by (constructor; [reflexivity | exact Hσ | intros y Hy; cbn in Hy; lia | intros y; reflexivity | exact Hag]).
  pose proof (set_interp_sub T γ _ _ _ _ HM Hc _ _ _ _ _ _ Hs) as H. cbn [tele_sub List.app List.length] in H. exact H.
Qed.

Lemma interp_list_realized : forall Tc θ Ψ ρe σ Ms vs, ⊢ gc_deps ⍮ gc_stack ⍮ Tc -> gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ σ : Tc ->
    (forall y, sub_entry_agrees T γ Ψ ρe (σ y) (θ y)) -> set_interp_list T γ Tc θ Ms vs ->
    set_interp_list T γ Ψ ρe (List.map (fun M => exp_sub M σ) Ms) vs.
Proof.
  intros * Hc Hσ Hag HM.
  assert (Hs : sub_setting T γ Tc θ nil Tc Ψ σ ρe ρe)
    by (constructor; [reflexivity | exact Hσ | intros y Hy; cbn in Hy; lia | intros y; reflexivity | exact Hag]).
  pose proof (proj1 (proj2 (set_interp_sub_all T γ)) _ _ _ _ HM _ _ _ _ _ _ Hc Hs) as H.
  cbn [tele_sub List.app List.length] in H. exact H.
Qed.

(** A substitution lifted past one more binder realizes the environment
    extended by the binder's entry. *)
Lemma sub_agrees_q : forall Ψ ρe e d σ θ, ⊢ gc_deps ⍮ gc_stack ⍮ e :: Ψ ->
    (forall y, sub_entry_agrees T γ Ψ ρe (σ y) (θ y)) ->
    forall y, sub_entry_agrees T γ (e :: Ψ) (set_env_extend ρe d) (sb_q σ y) (set_env_extend θ d y).
Proof.
  intros * Hc Hσ [| y].
  - split; cbn; [exact (set_interp_var T γ _ _ 0) | exact (set_interp_me_var T γ _ _ 0)].
  - unfold sb_q. cbn [sb_extend set_env_extend]. unfold sb_wk. rewrite <- sentry_sub_of_wk.
    exact (sub_agrees_shift _ _ _ _ _ _ Hc (Hσ y)).
Qed.

Section LeafFits.
  (** The group, and the level of the motives *)
  Variables (D : ind_decl) (i : nat).
  (** The motives' contexts are well formed *)
  Hypothesis HMwf : forall j Mj, ind_member D j = Some Mj -> ⊢ gc_deps ⍮ gc_stack ⍮ elim_mctx p D j Mj Us ++ Γ.
  (** The blocks' motives denote *)
  Hypothesis HMot : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
    exists FS FM FM', set_exp_eq_with T γ (elim_mctx p D j Mj Us ++ Γ) (abs_kind_sort r (a_typ i)) (eb_motive b) (eb_motive b) FS FM FM'.
  (** The motives' contexts denote *)
  Hypothesis HMctx : forall j Mj, ind_member D j = Some Mj -> set_ctx T γ (elim_mctx p D j Mj Us ++ Γ).

(** The recursive result at the end of a path: the eliminator's result,
    or the empty set, a proof, into propositions. *)
Definition end_value (j : nat) (w : aczel_set) : aczel_set :=
  match r with ak_propositional => empty_set | _ => elim_result j w end.

(** The recursive result of [v] along the path [l]: the empty set, a
    proof, into propositions, otherwise [leaf_result]. *)
Definition leaf_value (l : leaf_path) (v : aczel_set) : aczel_set :=
  match r with ak_propositional => empty_set | _ => leaf_result l v end.

(** [end_fact j Mj ns w]: the element [w] of the member [j] at the
    non-uniform parameters [ns] is an environment of the motive's context
    with [ρ], and the result there is of every reading of the motive. *)
Definition end_fact (j : nat) (Mj : imember) (ns : list aczel_set) (w : aczel_set) : Prop :=
  forall b FS FM FM', List.nth_error Bks j = Some b ->
    set_exp_eq_with T γ (elim_mctx p D j Mj Us ++ Γ) (abs_kind_sort r (a_typ i)) (eb_motive b) (eb_motive b) FS FM FM' ->
    set_env_in T γ (elim_mctx p D j Mj Us ++ Γ) (set_env_extend_kinded ρ (ctx_kinds (elim_mctx p D j Mj Us)) (ns ++ [w])) /\
    set_mem (end_value j w) (code_carrier (FM (set_env_extend_kinded ρ (ctx_kinds (elim_mctx p D j Mj Us)) (ns ++ [w])))).

(** [leaf_fits Ψ ρe β σ x xv l]: the recursive result of [xv] along [l] is
    of every reading of its type. *)
Definition leaf_fits (Ψ : ctx) (ρe : set_env) (β σ : sub) (x : exp) (xv : aczel_set) (l : leaf_path) : Prop :=
  forall A, set_interp T γ Ψ ρe (leaf_ihty r (blocks_motives Bks) β σ x l) A -> set_mem (leaf_value l xv) (code_carrier A).

(** [leaf_self_with Ψ ρe β σ x xv j Ps Mj b ns]: at the end of a path, at
    the member [j], [Mj], of the block [b], the parameters [Ps] moved by
    [σ] have the values [ns], and the end's facts hold there. *)
Record leaf_self_with (Ψ : ctx) (ρe : set_env) (β σ : sub) (x : exp) (xv : aczel_set) (j : nat) (Ps : list exp)
    (Mj : imember) (b : eblock) (ns : list aczel_set) : Prop :=
  { (** [Mj] is the member [j] *)
    leaf_self_member : ind_member D j = Some Mj
    (** [b] is its block *)
  ; leaf_self_block : List.nth_error Bks j = Some b
    (** The parameters' values *)
  ; leaf_self_params : set_interp_list T γ Ψ ρe (List.map (fun P => exp_sub P σ) Ps) ns
    (** The instance of the motive's context is a substitution *)
  ; leaf_self_typed : gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ sb_of_list β (List.map (fun P => exp_sub P σ) Ps ++ x :: nil)
      : elim_mctx p D j Mj Us ++ Γ
    (** The end's facts *)
  ; leaf_self_fact : end_fact j Mj ns xv }.

(** [leaf_pi_with Ψ ρe σ B xv a rest]: under a domain [B] moved by [σ], of
    the value [a], [xv] is a function on [a]'s elements, and [rest] holds
    at each. *)
Record leaf_pi_with (Ψ : ctx) (ρe : set_env) (σ : sub) (B : exp) (xv a : aczel_set) (rest : aczel_set -> Prop) : Prop :=
  { (** [a] is the domain's value *)
    leaf_pi_interp : set_interp T γ Ψ ρe (exp_sub B σ) a
    (** [xv]'s domain is its carrier *)
  ; leaf_pi_domain_eq : set_eq (relation_domain xv) (code_carrier a)
    (** The rest of the path, at each point *)
  ; leaf_pi_rest : forall b, set_mem b (code_carrier a) -> rest b }.

(** [leaf_sem Ψ ρe β σ x xv l]: the result fits along [l], or, along the
    path [l], the value [xv] of [x]
    has its domains' values and its end's facts, its components moved by
    [σ] and the motives' context by [β], read in [Ψ] at [ρe]. *)
Fixpoint leaf_sem (Ψ : ctx) (ρe : set_env) (β σ : sub) (x : exp) (xv : aczel_set) (l : leaf_path) {struct l} : Prop :=
  leaf_fits Ψ ρe β σ x xv l \/
  match l with
  | leaf_self j Ps => exists Mj b ns, leaf_self_with Ψ ρe β σ x xv j Ps Mj b ns
  | leaf_pi B l' =>
      exists a, leaf_pi_with Ψ ρe σ B xv a (fun b =>
        leaf_sem (ce_ass ak_relevant (exp_sub B σ) :: Ψ) (set_env_extend ρe (set_entry_term ak_relevant b)) (sb_compose β (sb_of_wk wk_shift))
          (sb_q σ) (a_app (exp_wk x wk_shift) (a_var 0)) (set_apply xv b) l')
  | leaf_proj f ns l' => leaf_sem Ψ ρe β (sb_of_list σ (projections_of ns x)) (a_proj f x) (tuple_field xv f) l'
  end.

Lemma leaf_sem_of_fits : forall Ψ ρe β σ x xv l, leaf_fits Ψ ρe β σ x xv l -> leaf_sem Ψ ρe β σ x xv l.
Proof. intros * H. destruct l; cbn [leaf_sem]; left; exact H. Qed.

(** The recursive result along a path is of the type the branch's context
    gives it there. *)
Lemma leaf_fit : forall l Ψ ρe β σ x xv A, ⊢ gc_deps ⍮ gc_stack ⍮ Ψ -> set_env_in T γ Ψ ρe ->
    (forall y, sub_entry_agrees T γ Ψ ρe (β y) (ρ y)) -> set_interp T γ Ψ ρe x xv -> leaf_sem Ψ ρe β σ x xv l ->
    set_interp T γ Ψ ρe (leaf_ihty r (blocks_motives Bks) β σ x l) A -> set_mem (leaf_value l xv) (code_carrier A).
Proof.
  induction l as [j Ps | B l IH | f ns l IH]; intros Ψ ρe β σ x xv A HcΨ Hρe Hβ Hx Hl HA;
    (destruct Hl as [Hfit | Hl]; [exact (Hfit A HA) |]); cbn [leaf_sem leaf_ihty] in Hl, HA.
  - (* the end: the motive at the moved environment *)
    destruct Hl as (Mj & b & ns & [HMj Hb Hns Hτ Hfact]).
    rewrite (blocks_motives_nth _ _ _ Hb) in HA.
    destruct (HMot j Mj b HMj Hb) as (FS & FM & FM' & Hw).
    destruct (Hfact b FS FM FM' Hb Hw) as [Henv Hmem].
    destruct Hw as [_ HL _ _ _].
    pose proof (set_denotes_exists _ _ _ _ _ HL _ Henv) as HM0.
    assert (Hset : sub_setting T γ (elim_mctx p D j Mj Us ++ Γ)
                     (set_env_extend_kinded ρ (ctx_kinds (elim_mctx p D j Mj Us)) (ns ++ [xv])) nil (elim_mctx p D j Mj Us ++ Γ) Ψ
                     (sb_of_list β (List.map (fun P => exp_sub P σ) Ps ++ x :: nil)) ρe ρe).
    { constructor; [reflexivity | exact Hτ | intros y Hy; cbn in Hy; lia | intros y; reflexivity |].
      intros y. cbn [List.length Nat.add]. apply (sub_agrees_of_list _ _ _ _ (set_interp_list_app T γ _ _ _ _ _ _ Hns
                    (set_interp_list_cons T γ _ _ _ _ _ _ Hx (set_interp_list_nil T γ _ _))) β ρ _ Hβ). }
    pose proof (set_interp_sub T γ _ _ _ _ HM0 (HMwf _ _ HMj) _ _ _ _ _ _ Hset) as H1.
    cbn [tele_sub List.app List.length] in H1. change (sb_qn 0 ?s) with s in H1.
    pose proof (set_interp_functional T γ Hfn Hmods _ _ _ _ HA ρe _ (set_env_rel_eq T γ _ _ _ Hρe) H1) as E.
    eapply set_mem_eq_r; [apply code_carrier_resp; apply set_eq_sym; exact E |]. exact Hmem.
  - (* a domain: a function of the results there, or their truth *)
    destruct Hl as (a & [Ha Edom Hrest]).
    set (B' := exp_sub B σ) in *.
    assert (Hpi : exists a1 F, ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass ak_relevant B' :: Ψ /\ set_interp T γ Ψ ρe B' a1 /\
                    (forall b, set_mem b (code_carrier a1) ->
                       set_interp T γ (ce_ass ak_relevant B' :: Ψ) (set_env_extend ρe (set_entry_term ak_relevant b))
                         (leaf_ihty r (blocks_motives Bks) (sb_compose β (sb_of_wk wk_shift)) (sb_q σ) (a_app (exp_wk x wk_shift) (a_var 0)) l)
                         (F b)) /\
                    ((r = ak_propositional /\ A = forall_code a1 F) \/ (r <> ak_propositional /\ A = pi_code a1 F)))
      by (inversion HA; subst; do 2 eexists; repeat split; eauto).
    destruct Hpi as (a1 & F & Hc' & Ha1 & HF & Hk).
    pose proof (set_interp_functional T γ Hfn Hmods _ _ _ _ Ha1 ρe _ (set_env_rel_eq T γ _ _ _ Hρe) Ha) as Ea.
    assert (Hb1 : forall b, set_mem b (code_carrier a1) -> set_mem b (code_carrier a))
      by (intros b Hb; eapply set_mem_eq_r; [apply code_carrier_resp; exact Ea | exact Hb]).
    assert (Hin : forall b, set_mem b (code_carrier a1) -> set_mem (leaf_value l (set_apply xv b)) (code_carrier (F b))).
    { intros b Hb. apply (IH (ce_ass ak_relevant B' :: Ψ) (set_env_extend ρe (set_entry_term ak_relevant b))
                              (sb_compose β (sb_of_wk wk_shift)) (sb_q σ) (a_app (exp_wk x wk_shift) (a_var 0)) (set_apply xv b) (F b) Hc').
      - split; [exact Hρe |]. cbn [set_entry_rel]. exists b, b, a1. constructor; [reflexivity | reflexivity | exact Ha1 | exact Hb | apply set_eq_refl].
      - intros y. unfold sb_compose. exact (sub_agrees_shift _ _ _ _ _ _ Hc' (Hβ y)).
      - apply set_interp_app; [| exact (set_interp_var T γ _ _ 0)].
        assert (Hw : gc_deps ⍮ gc_stack ⍮ ce_ass ak_relevant B' :: Ψ ⊢ʷ wk_shift : Ψ) by (apply wf_wk_shift; exact Hc').
        exact (proj1 (set_interp_wk_all T γ) _ _ _ _ Hx nil Ψ _ _ _
                 (Build_wk_setting Ψ ρe nil Ψ _ wk_shift (set_env_extend ρe (set_entry_term ak_relevant b)) eq_refl Hw (fun y => eq_refl))).
      - exact (Hrest b (Hb1 b Hb)).
      - exact (HF b Hb). }
    destruct Hk as [[Hr ->] | [Hr ->]].
    + unfold leaf_value in Hin |- *. rewrite Hr in Hin |- *. unfold forall_code.
      eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |]. apply set_mem_truth. split; [| apply set_eq_refl].
      intros b Hb. exact (Hin b Hb).
    + assert (Hlv : forall v, leaf_value (leaf_pi B l) v = graph_set (relation_domain v) (fun b => leaf_result l (set_apply v b)))
        by (intros v; unfold leaf_value; destruct r; [reflexivity | contradiction | reflexivity]).
      assert (Hlv' : forall v, leaf_value l v = leaf_result l v)
        by (intros v; unfold leaf_value; destruct r; [reflexivity | contradiction | reflexivity]).
      rewrite Hlv. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
      assert (HFr : respects_on (code_carrier a1) F)
        by exact (set_interp_family_respects T γ Hfn Hmods _ _ _ _ _ _ _ (set_env_rel_eq T γ _ _ _ Hρe) HF).
      assert (Hres : respects_set_eq_fun (fun b => leaf_result l (set_apply xv b)))
        by (intros b b' Eb; apply leaf_result_resp; apply set_apply_resp; [apply set_eq_refl | exact Eb]).
      eapply set_mem_eq_l; [apply graph_set_resp_on; [apply set_eq_sym; eapply set_eq_trans; [exact Edom | apply code_carrier_resp; apply set_eq_sym; exact Ea] |] |].
      * intros b b' _ Eb. apply Hres. exact Eb.
      * apply graph_set_function_on.
        -- intros b b' Hb Eb. apply code_carrier_resp. exact (HFr b b' Hb Eb).
        -- intros b b' _ Eb. apply Hres. exact Eb.
        -- intros b Hb. rewrite <- Hlv'. exact (Hin b Hb).
  - exact (IH Ψ ρe β _ (a_proj f x) (tuple_field xv f) A HcΨ Hρe Hβ (set_interp_proj T γ _ _ _ _ _ Hx) Hl HA).
Qed.

(** ** Along a Shape *)

Section Walk.
  (** The group is typed and closed, at its uniform parameters *)
  Hypotheses (HDt : decl_typed gc_deps gc_stack D) (Hcl : decl_closed D) (HUl : List.length Us = ind_nu D).
  Hypothesis HMh : forall j Mj, ind_member D j = Some Mj -> elim_mctx_head_large gc_deps gc_stack Γ p D j Mj Us.
  (** A member that is no record view has a block *)
  Hypothesis HBk : forall j Mj, ind_member D j = Some Mj -> im_is_rview Mj = false -> exists b, List.nth_error Bks j = Some b.
  (** The values of the uniform parameters *)
  Variable us : list aczel_set.
  (** What the end of a shape at a record view gives *)
  Variable RV : nat -> list aczel_set -> aczel_set -> Prop.

(** The context a shape's components are read in: the domains [Bs1]
    passed so far, moved by [φ], over [Ta] and the parameters of [Mk].  The
    shape's components are over the non-recursive arguments before it; the
    carriers read them over all of those arguments, [Ta]. *)
Definition shape_read_ctx (Mk : imember) (Ta : ctx) (φ : wk) (Bs1 : list exp) : ctx :=
  tele_wk (doms_ctx Bs1) φ ++ Ta ++ im_params D Mk.

Lemma shape_read_ctx_snoc : forall Mk Ta φ Bs1 B,
    shape_read_ctx Mk Ta φ (Bs1 ++ B :: nil) = ce_ass ak_relevant (exp_wk B (wk_qn (List.length Bs1) φ)) :: shape_read_ctx Mk Ta φ Bs1.
Proof. intros. unfold shape_read_ctx. rewrite doms_ctx_app_one. cbn [tele_wk List.app centry_wk]. rewrite length_doms_ctx. reflexivity. Qed.

(** A term moved by [ψ], then by [σa], is moved by [σ], if [σ] is [σa]
    after [ψ]. *)
Lemma wk_sub_realized : forall M ψ σ σa, sb_eq σ (sb_compose (sb_of_wk ψ) σa) -> exp_sub (exp_wk M ψ) σa = exp_sub M σ.
Proof. intros * E. rewrite <- exp_sub_of_wk, exp_sub_sub. symmetry. apply exp_sub_sb_eq. exact E. Qed.

Lemma sb_q_realized : forall ψ σ σa, sb_eq σ (sb_compose (sb_of_wk ψ) σa) ->
    sb_eq (sb_q σ) (sb_compose (sb_of_wk (wk_q ψ)) (sb_q σa)).
Proof.
  intros * E x. cbn [sb_compose sb_of_wk]. change (sentry_sub (se_var (wk_q ψ x)) (sb_q σa)) with (sb_q σa (wk_q ψ x)).
  symmetry. apply (sb_q_wk_pre_ext ψ σa σ). intros y. rewrite (E y). reflexivity.
Qed.

(** [shape_realized Mk Tb Ta φ Bs1 Ψ ρe σ σa θ]: the substitution [σ] of
    the shape's components, read at [ρe], is [σa] after the renaming [φ]
    of the components' context [Tb] into [Ta], and [σa] realizes [θ], an
    environment of the read context whose uniform parameters have the
    values [us]. *)
Record shape_realized (Mk : imember) (Tb Ta : ctx) (φ : wk) (Bs1 : list exp) (Ψ : ctx) (ρe : set_env) (σ σa : sub)
    (θ : set_env) : Prop :=
  { (** [φ] renames the components' context into the read one *)
    shape_realized_renaming : gc_deps ⍮ gc_stack ⍮ Ta ++ im_params D Mk ⊢ʷ φ : Tb ++ im_params D Mk
    (** keeping the parameters *)
  ; shape_realized_params : forall y, φ (List.length Tb + y) = List.length Ta + y
    (** [σa] substitutes the read context *)
  ; shape_realized_typed : gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ σa : shape_read_ctx Mk Ta φ Bs1
    (** and reads as [θ] *)
  ; shape_realized_agrees : forall y, sub_entry_agrees T γ Ψ ρe (σa y) (θ y)
    (** [σ] is [σa] after the renaming *)
  ; shape_realized_sub : sb_eq σ (sb_compose (sb_of_wk (wk_qn (List.length Bs1) φ)) σa)
    (** [θ] is an environment of the read context *)
  ; shape_realized_env : set_env_in T γ (shape_read_ctx Mk Ta φ Bs1) θ
    (** Its uniform parameters have the values [us] *)
  ; shape_realized_uniform :
      list_set_eq (set_env_values (ind_uparams D) (set_env_drop (List.length Bs1 + List.length Ta + im_nn Mk) θ)) us }.

(** [shape_end_with Mk Ta φ Bs1 j Ps θ xv Mj ns]: at the end of a shape,
    at the member [j], [Mj], its parameters [Ps] have the values [ns] at
    [θ], and [xv] has the end's facts there. *)
Record shape_end_with (Mk : imember) (Ta : ctx) (φ : wk) (Bs1 : list exp) (j : nat) (Ps : list exp) (θ : set_env)
    (xv : aczel_set) (Mj : imember) (ns : list aczel_set) : Prop :=
  { (** [Mj] is the member [j] *)
    shape_end_member : ind_member D j = Some Mj
    (** The parameters' values *)
  ; shape_end_params :
      set_interp_list T γ (shape_read_ctx Mk Ta φ Bs1) θ (List.map (fun P => exp_wk P (wk_qn (List.length Bs1) φ)) Ps) ns
    (** At a member with a block, the end's facts *)
  ; shape_end_block : im_is_rview Mj = false -> end_fact j Mj ns xv
    (** At a record view, what it gives *)
  ; shape_end_rview : im_is_rview Mj = true -> RV j ns xv
    (** Into a sort of relevant terms, its results *)
  ; shape_end_results : r <> ak_propositional -> end_results D j xv Mj }.

(** [shape_pi_with Mk Ta φ Bs1 B θ xv a rest]: the shape's next domain
    [B] has the value [a] at [θ], [xv] is a function on its elements, and
    [rest] holds at each. *)
Record shape_pi_with (Mk : imember) (Ta : ctx) (φ : wk) (Bs1 : list exp) (B : exp) (θ : set_env) (xv a : aczel_set)
    (rest : aczel_set -> Prop) : Prop :=
  { (** [a] is the domain's value *)
    shape_pi_interp : set_interp T γ (shape_read_ctx Mk Ta φ Bs1) θ (exp_wk B (wk_qn (List.length Bs1) φ)) a
    (** [xv]'s domain is its carrier *)
  ; shape_pi_domain_eq : set_eq (relation_domain xv) (code_carrier a)
    (** The rest of the shape, at each point *)
  ; shape_pi_rest : forall b, set_mem b (code_carrier a) -> rest b }.

(** [shape_closed_ok Mk Ta φ Bs1 t θ xv]: at the environment [θ] of the
    read context, [xv] is a function on each domain's value, and at the
    end its parameters' values give the end's facts. *)
Fixpoint shape_closed_ok (Mk : imember) (Ta : ctx) (φ : wk) (Bs1 : list exp) (t : ptyp) (θ : set_env) (xv : aczel_set)
    {struct t} : Prop :=
  match t with
  | pt_pi B t' =>
      exists a, shape_pi_with Mk Ta φ Bs1 B θ xv a (fun b =>
        shape_closed_ok Mk Ta φ (Bs1 ++ B :: nil) t' (set_env_extend θ (set_entry_term ak_relevant b)) (set_apply xv b))
  | pt_self j Ps => exists Mj ns, shape_end_with Mk Ta φ Bs1 j Ps θ xv Mj ns
  end.

  (** A record view's end fits along its paths, wherever it is read *)
  Hypothesis HRV : forall Mk Tb Ta φ Bs1 Ψ ρe β σ σa x xv θ j Ps Mj ns, ⊢ gc_deps ⍮ gc_stack ⍮ Ψ -> set_env_in T γ Ψ ρe ->
    (forall y, sub_entry_agrees T γ Ψ ρe (β y) (ρ y)) -> gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ β : Γ ->
    gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ σ : doms_ctx Bs1 ++ Tb ++ im_params D Mk ->
    shape_uc D Us (doms_ctx Bs1 ++ Tb ++ im_params D Mk) σ β -> shape_realized Mk Tb Ta φ Bs1 Ψ ρe σ σa θ ->
    set_interp T γ Ψ ρe x xv ->
    gc_deps ⍮ gc_stack ⍮ Ψ ⊢ x : ptyp_ty_at p D (List.map (fun U => exp_sub U β) Us) σ (pt_self j Ps) ->
    ind_member D j = Some Mj -> im_is_rview Mj = true -> List.length Ps = im_nn Mj -> RV j ns xv ->
    forall l, In l (shape_leaves (rview_leaves D) (List.length Bs1 + List.length Tb + im_nn Mk) (pt_self j Ps)) ->
    leaf_fits Ψ ρe β σ x xv l.

Lemma shape_leaf_sem : forall t Mk Bs1 Tb Ta φ Ψ ρe β σ σa x xv θ Mj,
    ⊢ gc_deps ⍮ gc_stack ⍮ Ψ -> set_env_in T γ Ψ ρe -> (forall y, sub_entry_agrees T γ Ψ ρe (β y) (ρ y)) ->
    gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ β : Γ -> gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ σ : doms_ctx Bs1 ++ Tb ++ im_params D Mk ->
    ⊢ gc_deps ⍮ gc_stack ⍮ doms_ctx Bs1 ++ Tb ++ im_params D Mk ->
    shape_uc D Us (doms_ctx Bs1 ++ Tb ++ im_params D Mk) σ β -> shape_realized Mk Tb Ta φ Bs1 Ψ ρe σ σa θ ->
    set_interp T γ Ψ ρe x xv ->
    gc_deps ⍮ gc_stack ⍮ Ψ ⊢ x : ptyp_ty_at p D (List.map (fun U => exp_sub U β) Us) σ t ->
    ind_member D (ptyp_mem t) = Some Mj -> List.length (ptyp_ps t) = im_nn Mj ->
    shape_doms_typed gc_deps gc_stack D Mk Bs1 Tb t -> shape_leaf_typed gc_deps gc_stack D Mk Mj Bs1 Tb t ->
    shape_closed_ok Mk Ta φ Bs1 t θ xv ->
    forall l, In l (shape_leaves (rview_leaves D) (List.length Bs1 + List.length Tb + im_nn Mk) t) -> leaf_sem Ψ ρe β σ x xv l.
Proof.
  induction t as [j0 Ps | B t IH]; intros Mk Bs1 Tb Ta φ Ψ ρe β σ σa x xv θ Mj HcΨ Hρe Hβ Hβt Hσt HcT Huc Hrz Hx Hxt Hj HPl HB HP
    Hcok l Hin; cbn [ptyp_mem ptyp_ps shape_closed_ok shape_leaves] in Hj, HPl, Hcok, Hin.
  all: pose proof Hrz as [Hφ Hφp Hσat Hσa Eσ Hθ Hus].
  all: assert (HcTa : ⊢ gc_deps ⍮ gc_stack ⍮ shape_read_ctx Mk Ta φ Bs1) by exact (ctx_wk _ _ _ _ HcT Hφ).
  - (* the end: a record view's fits, or the end's facts *)
    destruct Hcok as (Mj0 & ns & [HMj0 Hns Hblk Hrv _]). rewrite Hj in HMj0. injection HMj0 as <-.
    destruct (im_is_rview Mj) eqn:Hr.
    + apply leaf_sem_of_fits.
      eapply HRV; [exact HcΨ | exact Hρe | exact Hβ | exact Hβt | exact Hσt | exact Huc | exact Hrz | exact Hx | exact Hxt
                  | exact Hj | exact Hr | exact HPl | exact (Hrv eq_refl) | exact Hin].
    + rewrite (rview_leaves_not_rview _ _ _ Hj Hr) in Hin. destruct Hin as [<- | []].
      cbn [leaf_sem]. right. destruct (HBk _ _ Hj Hr) as [b Hb]. exists Mj, b, ns.
      constructor; [exact Hj | exact Hb | | | exact (Hblk eq_refl)].
      * pose proof (interp_list_realized _ _ _ _ _ _ _ HcTa Hσat Hσa Hns) as H. rewrite List.map_map in H.
        erewrite List.map_ext in H; [exact H |]. intros P. exact (wk_sub_realized P _ _ _ Eσ).
      * exact (ih_leaf_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDt Hcl Hj HUl (HMwf _ _ Hj) Hβt Hσt Huc HPl
                 (shape_leaf_at _ _ _ _ _ _ _ _ HP eq_refl) Hxt).
  - (* a domain: the walk goes on under it *)
    apply List.in_map_iff in Hin as (l' & <- & Hin').
    destruct Hcok as (a & [Ha Edom Hrest]).
    pose proof (interp_realized _ _ _ _ _ _ _ HcTa Hσat Hσa Ha) as Ha'. rewrite (wk_sub_realized B _ _ _ Eσ) in Ha'.
    cbn [leaf_sem]. right. exists a.
    constructor; [exact Ha' | exact Edom |].
    intros b Hb.
    destruct (HB nil B (ptyp_doms t) eq_refl) as [j1 Hj1]. rewrite List.app_nil_r in Hj1.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hj1 Hσt) as Hj1'. cbn [exp_sub] in Hj1'.
    pose proof (typing_wk _ _ _ _ _ _ Hj1 Hφ) as Hj1a. cbn [exp_wk] in Hj1a. rewrite length_doms_ctx in Hj1a.
    fold (shape_read_ctx Mk Ta φ Bs1) in Hj1a.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hj1a Hσat) as Hj1a'. cbn [exp_sub] in Hj1a'.
    pose proof (wf_sub_q _ _ _ _ _ _ _ _ Hσat Hj1a (sort_kind_universe _) Hj1a') as Hσat'.
    rewrite (wk_sub_realized B _ _ _ Eσ), <- shape_read_ctx_snoc in Hσat'.
    assert (HΨ' : ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass ak_relevant (exp_sub B σ) :: Ψ)
      by (eapply wf_ctx_extend; [exact Hj1' | constructor]).
    pose proof (wf_sub_q _ _ _ _ _ _ _ _ Hσt Hj1 (sort_kind_universe _) Hj1') as Hσt'.
    assert (Hβt' : gc_deps ⍮ gc_stack ⍮ ce_ass ak_relevant (exp_sub B σ) :: Ψ ⊢ˢ sb_compose β (sb_of_wk wk_shift) : Γ)
      by (eapply wf_sub_compose; [exact Hβt | apply wf_sub_of_wk, wf_wk_shift; exact HΨ']).
    assert (HcT' : ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass ak_relevant B :: doms_ctx Bs1 ++ Tb ++ im_params D Mk)
      by (eapply wf_ctx_extend; [exact Hj1 | constructor]).
    assert (EC : ce_ass ak_relevant B :: doms_ctx Bs1 ++ Tb ++ im_params D Mk = doms_ctx (Bs1 ++ B :: nil) ++ Tb ++ im_params D Mk)
      by (rewrite doms_ctx_app_one; reflexivity).
    rewrite EC in Hσt', HcT'.
    assert (Huc' : shape_uc D Us (doms_ctx (Bs1 ++ B :: nil) ++ Tb ++ im_params D Mk) (sb_q σ) (sb_compose β (sb_of_wk wk_shift)))
      by (rewrite doms_ctx_app_one; apply shape_uc_pi; [exact (proj2 (length_shape_ctx D Mk Bs1 Tb)) | exact Huc]).
    pose proof (shape_doms_typed_pi _ _ _ _ _ _ _ _ HB) as HB''.
    pose proof (shape_leaf_typed_pi _ _ _ _ _ _ _ _ _ HP) as HP''.
    destruct (ty_at_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDt Hcl HUl HMwf HMh Hβt' Hσt' Huc' Hj HPl HB'' HP'') as [j2 Hj2].
    assert (Hum : List.map (fun U => exp_wk U wk_shift) (List.map (fun U => exp_sub U β) Us)
                  = List.map (fun U => exp_sub U (sb_compose β (sb_of_wk wk_shift))) Us)
      by (rewrite List.map_map; apply List.map_ext; intros; rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity).
    cbn [ptyp_ty_at] in Hxt. rewrite Hum in Hxt.
    pose proof (shape_arg_app _ _ _ _ _ _ _ _ Hj1' Hj2 Hxt) as Hxt'.
    assert (Hrz' : shape_realized Mk Tb Ta φ (Bs1 ++ B :: nil) (ce_ass ak_relevant (exp_sub B σ) :: Ψ)
                     (set_env_extend ρe (set_entry_term ak_relevant b)) (sb_q σ) (sb_q σa)
                     (set_env_extend θ (set_entry_term ak_relevant b))).
    { constructor.
      - exact Hφ.
      - exact Hφp.
      - exact Hσat'.
      - exact (sub_agrees_q _ _ _ _ _ _ HΨ' Hσa).
      - rewrite List.length_app, Nat.add_1_r. cbn [wk_qn]. exact (sb_q_realized _ _ _ Eσ).
      - rewrite shape_read_ctx_snoc. split; [exact Hθ |]. cbn [set_entry_rel]. exists b, b, a.
        constructor; [reflexivity | reflexivity | exact Ha | exact Hb | apply set_eq_refl].
      - rewrite List.length_app. cbn [List.length]. eapply list_set_eq_trans; [| exact Hus].
        rewrite (set_env_values_agree _ _ (set_env_drop (List.length Bs1 + List.length Ta + im_nn Mk) θ)); [apply list_set_eq_refl |].
        intros y _. unfold set_env_drop.
        replace (List.length Bs1 + 1 + List.length Ta + im_nn Mk + y) with (S (List.length Bs1 + List.length Ta + im_nn Mk + y)) by lia.
        reflexivity. }
    apply (IH Mk (Bs1 ++ B :: nil) Tb Ta φ _ _ _ _ (sb_q σa) _ _ (set_env_extend θ (set_entry_term ak_relevant b)) Mj HΨ').
    + split; [exact Hρe |]. cbn [set_entry_rel]. exists b, b, a.
      constructor; [reflexivity | reflexivity | exact Ha' | exact Hb | apply set_eq_refl].
    + intros y. unfold sb_compose. exact (sub_agrees_shift _ _ _ _ _ _ HΨ' (Hβ y)).
    + exact Hβt'.
    + exact Hσt'.
    + exact HcT'.
    + exact Huc'.
    + exact Hrz'.
    + apply set_interp_app; [| exact (set_interp_var T γ _ _ 0)].
      assert (Hw : gc_deps ⍮ gc_stack ⍮ ce_ass ak_relevant (exp_sub B σ) :: Ψ ⊢ʷ wk_shift : Ψ) by (apply wf_wk_shift; exact HΨ').
      exact (proj1 (set_interp_wk_all T γ) _ _ _ _ Hx nil Ψ _ _ _
               (Build_wk_setting Ψ ρe nil Ψ _ wk_shift (set_env_extend ρe (set_entry_term ak_relevant b)) eq_refl Hw (fun y => eq_refl))).
    + exact Hxt'.
    + exact Hj.
    + exact HPl.
    + exact HB''.
    + exact HP''.
    + exact (Hrest b Hb).
    + rewrite List.length_app. cbn [List.length]. replace (List.length Bs1 + 1 + List.length Tb + im_nn Mk)
        with (S (List.length Bs1 + List.length Tb + im_nn Mk)) by lia. exact Hin'.
Qed.

End Walk.

(** A recursive argument whose ends have their results has its results
    along its shape, into a sort of relevant terms. *)
Lemma shape_results_of_closed_ok : r <> ak_propositional ->
    forall RV t Mk Ta φ Bs1 θ a, shape_closed_ok RV Mk Ta φ Bs1 t θ a -> shape_results D t a.
Proof.
  intros Hr RV t. induction t as [j Ps | B t IH]; intros Mk Ta φ Bs1 θ a H; cbn [shape_closed_ok shape_results] in *.
  - destruct H as (Mj & ns & [_ _ _ _ Hres]). exists Mj. exact (Hres Hr).
  - destruct H as (a1 & [_ Edom Hrest]). intros b Hb.
    exact (IH _ _ _ _ _ _ (Hrest b (set_mem_eq_r _ _ _ Edom Hb))).
Qed.

(** ** The Fits of a Record View *)

(** [rview_embedding qr Is θ0 Ψ ρe β σ0 x xv]: [x], of value [xv], is an
    argument of the record [qr] at its instance [Is] moved by [σ0], read in
    [Ψ] at [ρe], where [σ0] sends the uniform parameters to [Us] moved by
    [β] and reads as [θ0]. *)
Record rview_embedding (qr : qname) (Is : list exp) (θ0 : set_env) (Ψ : ctx) (ρe : set_env) (β σ0 : sub) (x : exp)
    (xv : aczel_set) : Prop :=
  { (** The context is well formed *)
    rview_embedding_ctx : ⊢ gc_deps ⍮ gc_stack ⍮ Ψ
    (** [ρe] is an environment of it *)
  ; rview_embedding_env : set_env_in T γ Ψ ρe
    (** [β] reads as [ρ] *)
  ; rview_embedding_base : forall y, sub_entry_agrees T γ Ψ ρe (β y) (ρ y)
    (** and substitutes the eliminator's context *)
  ; rview_embedding_base_typed : gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ β : Γ
    (** [σ0] substitutes the uniform parameters *)
  ; rview_embedding_typed : gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ σ0 : ind_uparams D
    (** and reads as [θ0] *)
  ; rview_embedding_agrees : forall y, sub_entry_agrees T γ Ψ ρe (σ0 y) (θ0 y)
    (** sending them to [Us] moved by [β] *)
  ; rview_embedding_uniform : forall y, y < ind_nu D ->
      sentry_exp (σ0 y) = sentry_exp (sb_compose (sb_of_list sb_id Us) β y)
    (** [xv] is [x]'s value *)
  ; rview_embedding_value : set_interp T γ Ψ ρe x xv
    (** [x] is of the record at its instance *)
  ; rview_embedding_arg : gc_deps ⍮ gc_stack ⍮ Ψ ⊢ x : apps_exp (a_record qr) (List.map (fun I => exp_sub I σ0) Is) }.

(** [rview_fits us j ns xv]: at the record view [j], whose parameters are
    the uniform ones ([ns] is empty), the recursive results of [xv] fit
    along the paths of its fields wherever it is an argument, at every
    environment of the uniform parameters of the values [us], and so do
    those of every element equal to it. *)
Definition rview_fits (us : list aczel_set) (j : nat) (ns : list aczel_set) (xv : aczel_set) : Prop :=
  forall xv' Mj qr Is fl c gs θ0 Ψ ρe β σ0 x, set_eq xv xv' ->
    ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil ->
    set_env_in T γ (ind_uparams D) θ0 -> list_set_eq (set_env_values (ind_uparams D) θ0) us ->
    rview_embedding qr Is θ0 Ψ ρe β σ0 x xv' ->
    forall l, In l (fields_leaves (rview_leaves D) nil (List.combine fl gs)) -> leaf_fits Ψ ρe β σ0 x xv' l.

(** The fits of a record view hold at every element equal to it. *)
Lemma rview_fits_resp : forall us j ns ns' xv xv', set_eq xv xv' -> rview_fits us j ns xv -> rview_fits us j ns' xv'.
Proof. intros * E H xv2 * E2. apply H. eapply set_eq_trans; [exact E | exact E2]. Qed.

(** Extending environments that agree everywhere gives ones that agree. *)
Lemma set_env_extend_kinded_base : forall vs κs ρ1 ρ2, (forall x, ρ1 x = ρ2 x) ->
    forall x, set_env_extend_kinded ρ1 κs vs x = set_env_extend_kinded ρ2 κs vs x.
Proof.
  induction vs as [| v vs IH]; intros κs ρ1 ρ2 E; cbn [set_env_extend_kinded]; [exact E |].
  apply IH. intros [| y]; cbn; [reflexivity | apply E].
Qed.

(** The end's facts at equal parameters and elements. *)
Lemma end_fact_resp : decl_closed D -> forall j Mj ns ns' w w', ind_member D j = Some Mj -> List.length ns = im_nn Mj ->
    list_set_eq ns ns' -> set_eq w w' -> end_fact j Mj ns w -> end_fact j Mj ns' w'.
Proof.
  intros Hcl j Mj ns ns' w w' Hj Hl En Ew H b FS FM FM' Hb Hw.
  destruct (H b FS FM FM' Hb Hw) as [Hin Hmem].
  set (Δ := elim_mctx p D j Mj Us) in *.
  set (ρ1 := set_env_extend_kinded ρ (ctx_kinds Δ) (ns ++ [w])) in *.
  set (ρ2 := set_env_extend_kinded ρ (ctx_kinds Δ) (ns' ++ [w'])).
  assert (HlΔ : List.length (ns ++ [w]) = List.length Δ) by (unfold Δ; rewrite List.length_app, length_elim_mctx; cbn; lia).
  assert (E : list_set_eq (set_env_values Δ ρ1) (ns' ++ [w'])).
  { unfold ρ1. rewrite set_env_values_extend_kinded by exact HlΔ.
    apply list_set_eq_app; [exact En | constructor; [exact Ew | constructor]]. }
  pose proof (set_env_rel_retarget T γ Δ Γ _ _ (elim_mctx_ass _ _ _ _ _ Hcl Hj) Hin E) as Hr.
  assert (Hr' : set_env_rel T γ (Δ ++ Γ) ρ1 ρ2).
  { eapply set_env_rel_ext; [exact (HMwf _ _ Hj) | intros x; reflexivity | | exact Hr].
    apply set_env_extend_kinded_base. intros x. unfold set_env_drop, ρ1. rewrite <- HlΔ, set_env_extend_kinded_ge. reflexivity. }
  destruct (set_env_rel_per T γ _ (HMctx _ _ Hj)) as [Hsym Htr].
  pose proof (Htr _ _ _ (Hsym _ _ Hr') Hr') as Hin2.
  split; [exact Hin2 |].
  destruct Hw as [_ HL _ _ _].
  pose proof (set_denotes_rel T γ _ _ _ _ _ HL Hr' Hin2) as EF.
  eapply set_mem_eq_r; [apply code_carrier_resp; apply set_eq_sym; exact EF |].
  eapply set_mem_eq_l; [| exact Hmem]. unfold end_value. destruct r; [apply elim_result_resp; exact Ew | apply set_eq_refl
                                                                    | apply elim_result_resp; exact Ew].
Qed.

(** The fits of a record view give the fits at the end of a shape ending
    in it: the walk's hypothesis on record views. *)
Lemma rview_fits_at_end : decl_typed gc_deps gc_stack D -> decl_closed D -> List.length Us = ind_nu D ->
    forall us Mk Tb Ta φ Bs1 Ψ ρe β σ σa x xv θ j Ps Mj ns, ⊢ gc_deps ⍮ gc_stack ⍮ Ψ -> set_env_in T γ Ψ ρe ->
    (forall y, sub_entry_agrees T γ Ψ ρe (β y) (ρ y)) -> gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ β : Γ ->
    gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ σ : doms_ctx Bs1 ++ Tb ++ im_params D Mk ->
    shape_uc D Us (doms_ctx Bs1 ++ Tb ++ im_params D Mk) σ β -> shape_realized us Mk Tb Ta φ Bs1 Ψ ρe σ σa θ ->
    set_interp T γ Ψ ρe x xv ->
    gc_deps ⍮ gc_stack ⍮ Ψ ⊢ x : ptyp_ty_at p D (List.map (fun U => exp_sub U β) Us) σ (pt_self j Ps) ->
    ind_member D j = Some Mj -> im_is_rview Mj = true -> List.length Ps = im_nn Mj -> rview_fits us j ns xv ->
    forall l, In l (shape_leaves (rview_leaves D) (List.length Bs1 + List.length Tb + im_nn Mk) (pt_self j Ps)) ->
    leaf_fits Ψ ρe β σ x xv l.
Proof.
  intros HDt Hcl HUl us Mk Tb Ta φ Bs1 Ψ ρe β σ σa x xv θ j Ps Mj ns HcΨ Hρe Hβ Hβt Hσt Huc Hrz Hx Hxt Hj Hr HPl HRVf l Hin.
  destruct Hrz as [Hφ Hφp Hσat Hσa Eσ Hθ Hus].
  unfold im_is_rview in Hr. destruct (im_head Mj) as [pm | qc k' Is0 vm | qr Is fl] eqn:Hh; try discriminate.
  destruct (rview_params _ _ _ _ _ _ _ _ HDt Hj Hh) as [EG Hnn].
  destruct Ps; [| cbn in HPl; lia].
  destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ HDt) _ _ _ _ _ Hj Hh) as (gs & Hcs & Hlen).
  pose proof (leaves_coherent_of_order _ (rview_struct_order _ _ _ (decl_typed_record_struct _ _ _ HDt))) as Hco.
  cbn [shape_leaves] in Hin. rewrite (Hco _ _ _ _ _ _ _ Hj Hh Hcs) in Hin.
  apply List.in_map_iff in Hin as (l0 & <- & Hin).
  set (m := List.length Bs1 + List.length Tb + im_nn Mk) in *.
  set (k := List.length Bs1 + List.length Ta + im_nn Mk) in *.
  set (σ0 := sb_compose (sb_of_wk (wk_shiftn m)) σ).
  destruct (length_shape_ctx D Mk Bs1 Tb) as [Hlm _]. fold m in Hlm.
  assert (Huc0 : forall y, y < ind_nu D -> sentry_exp (σ0 y) = sentry_exp (sb_compose (sb_of_list sb_id Us) β y)).
  { intros y Hy. unfold σ0. cbn [sb_compose sb_of_wk sentry_sub wk_shiftn]. rewrite <- Hlm. exact (Huc y Hy). }
  assert (Hfit : leaf_fits Ψ ρe β σ0 x xv l0).
  { eapply HRVf; [apply set_eq_refl | exact Hj | exact Hh | exact Hcs | | exact Hus | | exact Hin].
    - unfold shape_read_ctx, im_params in Hθ. rewrite !List.app_assoc in Hθ.
      pose proof (set_env_rel_drop T γ _ _ _ _ Hθ) as H.
      rewrite !List.length_app, length_tele_wk, length_doms_ctx in H. exact H.
    - constructor; [exact HcΨ | exact Hρe | exact Hβ | exact Hβt | | | exact Huc0 | exact Hx |].
      + eapply wf_sub_compose; [| exact Hσt]. apply wf_sub_of_wk.
        pose proof (wf_sub_cod _ _ _ _ _ Hσt) as HC.
        replace m with (List.length ((doms_ctx Bs1 ++ Tb) ++ im_nparams Mk))
          by (unfold m; rewrite !List.length_app, length_doms_ctx; unfold im_nn; lia).
        replace (doms_ctx Bs1 ++ Tb ++ im_params D Mk) with (((doms_ctx Bs1 ++ Tb) ++ im_nparams Mk) ++ ind_uparams D)
          in HC |- * by (unfold im_params; rewrite <- !List.app_assoc; reflexivity).
        apply wf_wk_shiftn_app'; exact HC.
      + intros y. unfold σ0. cbn [sb_compose sb_of_wk wk_shiftn].
        change (sentry_sub (se_var (y + m)) σ) with (σ (y + m)). rewrite (Eσ (y + m)). cbn [sb_compose sb_of_wk].
        change (sentry_sub (se_var ?z) σa) with (σa z). rewrite wk_qn_ge by (unfold m; lia).
        replace (y + m - List.length Bs1) with (List.length Tb + (im_nn Mk + y)) by (unfold m; lia).
        rewrite Hφp. replace (List.length Ta + (im_nn Mk + y) + List.length Bs1) with (k + y) by (unfold k; lia).
        exact (Hσa (k + y)).
      + cbn [ptyp_ty_at List.map] in Hxt.
        rewrite <- (rview_mty _ _ p _ _ _ _ _ _ (List.map (fun U => exp_sub U β) Us) σ0 HDt Hcl Hj Hh); [exact Hxt |].
        intros y Hy. rewrite (Huc0 y Hy). cbn [sb_compose]. rewrite sb_of_list_lt_compose by lia. reflexivity. }
  intros A HA. unfold leaf_fits in Hfit. rewrite leaf_ihty_wk in HA.
  eapply set_mem_eq_l; [| exact (Hfit A HA)].
  unfold leaf_value. destruct r; try apply set_eq_refl; apply set_eq_sym, leaf_result_wk.
Qed.

(** ** The Property of the Carriers' Points *)

(** [point_ok us k ns w Mk]: the element [w] of the member [k], [Mk], at
    the non-uniform parameters [ns] has, and every element equal to it
    has, its results, into a sort of relevant terms; at a member with a
    block, the end's facts; at a record view, its fits. *)
Record point_ok (us : list aczel_set) (k : nat) (ns : list aczel_set) (w : aczel_set) (Mk : imember) : Prop :=
  { (** Its results, and those of every element equal to it *)
    point_ok_results : r <> ak_propositional -> forall w', set_eq w w' -> end_results D k w' Mk
    (** At a member with a block, the end's facts *)
  ; point_ok_fact : im_is_rview Mk = false -> end_fact k Mk ns w
    (** At a record view, its fits *)
  ; point_ok_fits : im_is_rview Mk = true -> rview_fits us k ns w }.

(** [elim_point us k ns w]: at every instance of the parameters of the
    member [k] whose uniform ones have the values [us] and the others [ns],
    [w] is as [point_ok] says: the property the induction on the carriers
    proves. *)
Definition elim_point (us : list aczel_set) (k : nat) (ns : list aczel_set) (w : aczel_set) : Prop :=
  forall Mk θk, ind_member D k = Some Mk -> set_env_in T γ (im_params D Mk) θk ->
    list_set_eq (uniform_values D Mk θk) us -> list_set_eq (set_env_values (im_nparams Mk) θk) ns -> point_ok us k ns w Mk.

(** The property respects equality, as the induction on the carriers
    needs. *)
Lemma elim_point_resp : decl_closed D -> forall us k ns ns' w w', list_set_eq ns ns' -> set_eq w w' ->
    elim_point us k ns w -> elim_point us k ns' w'.
Proof.
  intros Hcl us k ns ns' w w' En Ew H Mk θk Hk Hθk Hu Hn.
  assert (Hn' : list_set_eq (set_env_values (im_nparams Mk) θk) ns) by (eapply list_set_eq_trans; [exact Hn | apply list_set_eq_sym; exact En]).
  destruct (H Mk θk Hk Hθk Hu Hn') as [Hres Hfact Hfits]. constructor.
  - intros Hr w'' E. apply Hres; [exact Hr | eapply set_eq_trans; [exact Ew | exact E]].
  - intros Hr. apply (end_fact_resp Hcl k Mk ns ns' w w' Hk); [| exact En | exact Ew | exact (Hfact Hr)].
    rewrite <- (Forall2_length Hn'), length_set_env_values. reflexivity.
  - intros Hr. exact (rview_fits_resp _ _ _ _ _ _ Ew (Hfits Hr)).
Qed.

(** ** Recursive Arguments Drawn From the Points *)

(** A recursive argument drawn from the points having the property, at an
    environment of the arguments before it, is a function on its domains'
    values whose ends have the property: what the walk along its paths
    needs ([shape_leaf_sem]). *)
Lemma shape_closed_ok_of_set : ind_lookup gc_deps gc_stack p = Some D -> decl_closed D ->
    forall us U Mk gs sgs gs1 t0 gs2 F ds0 target tparams pre_e θa C,
    List.length (set_group_uniform_types (global_group γ p)) = ind_nu D ->
    set_constructor_ok T γ p D (global_group γ p) Mk gs sgs -> gs = gs1 ++ ca_rec t0 :: gs2 ->
    List.nth_error sgs (List.length gs1) = Some (set_argument_recursive F ds0 target tparams) ->
    Forall list_function_respects ds0 -> list_list_function_respects tparams -> List.length ds0 = ptyp_depth t0 ->
    forall Mt, ind_member D (ptyp_mem t0) = Some Mt ->
    set_env_in T γ (cargs_ctx p D Mk gs1 ++ im_params D Mk) θa ->
    list_set_eq (List.firstn (ind_nu D) (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θa)) us ->
    (forall k' d pts0, List.nth_error ds0 k' = Some d -> List.length pts0 = k' ->
       set_eq (d (pre_e ++ pts0)) (d (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θa ++ pts0))) ->
    (forall pts, List.length pts = List.length ds0 ->
       list_set_eq (tparams (pre_e ++ pts)) (tparams (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θa ++ pts))) ->
    set_interp T γ (cargs_ctx p D Mk gs1 ++ im_params D Mk) θa (ptyp_ty p D (im_nn Mk) (cargs_pat gs1) t0) C ->
    set_eq C (shape_code (global_group γ p) ds0 target tparams (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θa) nil) ->
    forall a, set_mem a (shape_set (global_group γ p) U (carrier_points_with (global_group γ p) us U U (elim_point us))
                         pre_e ds0 target tparams nil) ->
    shape_closed_ok (rview_fits us) Mk (cargs_ctx p D Mk gs1) (wk_pat (cargs_pat gs1)) nil t0 θa a.
Proof.
  intros HD Hcl us U Mk gs sgs gs1 t0 gs2 F ds0 target tparams pre_e θa C0 Hnu Hcok Egs Hsg Hds0 Htp Hlds Mt HMt Hθa HLv Hdom0 Htps
    HC0 EC0 a0 Ha0.
  pose proof (set_group_ok_carrier_resp _ _ _ _ _ (set_gctx_ok_groups _ _ Hok _ _ HD)) as HGresp.
  set (G := global_group γ p) in *.
  set (S := carrier_points_with G us U U (elim_point us)) in *.
  set (Ta := cargs_ctx p D Mk gs1) in *. set (pat := cargs_pat gs1) in *. set (φ := wk_pat pat).
  set (Lv := set_env_values (Ta ++ im_params D Mk) θa) in *.
  pose proof (set_constructor_ok_target _ _ _ _ _ _ _ _ Hcok gs1 t0 gs2 F ds0 target tparams Egs Hsg) as Htg.
  (* the property at the end of a shape *)
  assert (Hend : forall θ pts, set_env_in T γ (shape_read_ctx Mk Ta φ (ptyp_doms t0)) θ ->
            set_env_values (shape_read_ctx Mk Ta φ (ptyp_doms t0)) θ = Lv ++ pts -> List.length pts = List.length ds0 ->
            forall a, set_mem a (candidate_carrier U S target (List.skipn (ind_nu D) (tparams (pre_e ++ pts)))) ->
            point_ok us target (List.skipn (ind_nu D) (tparams (Lv ++ pts))) a Mt).
  { intros θ pts Hθ Hvals Hlp a Ha.
    assert (Hθ' : set_env_in T γ (recursive_end_ctx p D Mk gs1 t0) θ)
      by (unfold recursive_end_ctx; rewrite shape_domains_ctx_wk; exact Hθ).
    unfold candidate_carrier in Ha. apply (set_mem_separation _ _ _ (member_point_pred_resp _ _ _)) in Ha as [_ Hp].
    unfold S, carrier_points_with in Hp. apply (set_mem_separation _ _ _ (carrier_points_with_pred_resp _)) in Hp as [_ Hp].
    destruct Hp as (k' & ns' & v' & Ept & HQ). apply member_point_inj in Ept as [<- [En Ev]].
    assert (HQ' : elim_point us target (List.skipn (ind_nu D) (tparams (Lv ++ pts))) a).
    { eapply (elim_point_resp Hcl); [| apply set_eq_sym; exact Ev | exact HQ].
      eapply list_set_eq_trans; [apply list_set_eq_sym; exact En |]. apply list_set_eq_skipn. apply Htps. exact Hlp. }
    destruct (set_constructor_ok_target_instance _ _ _ _ _ _ _ _ Hcok gs1 t0 gs2 F ds0 target tparams Egs Hsg θ Hθ')
      as (Mt' & ρt & [HMt' Hρt Evals]).
    rewrite Htg in HMt'. rewrite HMt in HMt'. injection HMt' as <-.
    unfold recursive_end_ctx in Evals. rewrite shape_domains_ctx_wk in Evals.
    change (tele_wk (doms_ctx (ptyp_doms t0)) (wk_pat (cargs_pat gs1)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk)
      with (shape_read_ctx Mk Ta φ (ptyp_doms t0)) in Evals.
    rewrite Hvals in Evals.
    assert (HlLv : ind_nu D <= List.length Lv)
      by (unfold Lv; rewrite length_set_env_values, List.length_app, length_im_params; unfold im_np; lia).
    rewrite List.firstn_app, (proj2 (Nat.sub_0_le (ind_nu D) (List.length Lv)) HlLv), List.app_nil_r in Evals.
    unfold im_params in Evals. rewrite set_env_values_app in Evals.
    assert (Hlen : List.length (List.firstn (ind_nu D) Lv) =
                   List.length (set_env_values (ind_uparams D) (set_env_drop (List.length (im_nparams Mt)) ρt)))
      by (rewrite List.length_firstn, length_set_env_values, Nat.min_l by exact HlLv; reflexivity).
    destruct (list_set_eq_app_inv _ _ _ _ Hlen Evals) as [Eu En'].
    apply (HQ' Mt ρt); [rewrite Htg; exact HMt | exact Hρt | | apply list_set_eq_sym; exact En'].
    unfold uniform_values. rewrite <- (length_im_nparams Mt). eapply list_set_eq_trans; [apply list_set_eq_sym; exact Eu | exact HLv]. }
  (* the walk along the shape's domains *)
  assert (Gen : forall t Bs1 ds θ C pts1 a,
            Bs1 ++ ptyp_doms t = ptyp_doms t0 -> ptyp_mem t = ptyp_mem t0 -> ptyp_ps t = ptyp_ps t0 ->
            List.length pts1 = List.length Bs1 -> List.length ds = ptyp_depth t -> Forall list_function_respects ds ->
            (forall k' d pts0, List.nth_error ds k' = Some d -> List.length pts0 = List.length pts1 + k' ->
               set_eq (d (pre_e ++ pts0)) (d (Lv ++ pts0))) ->
            set_env_in T γ (shape_read_ctx Mk Ta φ Bs1) θ -> set_env_values (shape_read_ctx Mk Ta φ Bs1) θ = Lv ++ pts1 ->
            set_interp T γ (shape_read_ctx Mk Ta φ Bs1) θ (ptyp_ty p D (im_nn Mk) (List.repeat false (List.length Bs1) ++ pat) t) C ->
            set_eq C (shape_code G ds target tparams Lv pts1) ->
            set_mem a (shape_set G U S pre_e ds target tparams pts1) ->
            shape_closed_ok (rview_fits us) Mk Ta φ Bs1 t θ a).
  { induction t as [j Ps | A t IH]; intros Bs1 ds θ C pts1 a EBs Emem Eps Hlp Hld Hds Hdom Hθ Hvals HC EC Ha.
    - (* the end: the parameters' values, and the property there *)
      cbn [ptyp_doms ptyp_mem ptyp_ps ptyp_depth] in EBs, Emem, Eps, Hld. rewrite List.app_nil_r in EBs. subst Bs1.
      destruct ds; [| discriminate].
      assert (Hlp' : List.length pts1 = List.length ds0)
        by (rewrite Hlp, Hlds; reflexivity).
      cbn [shape_closed_ok]. exists Mt, (List.skipn (ind_nu D) (tparams (Lv ++ pts1))).
      assert (Hθ' : set_env_in T γ (recursive_end_ctx p D Mk gs1 t0) θ)
        by (unfold recursive_end_ctx; rewrite shape_domains_ctx_wk; exact Hθ).
      cbn [shape_set] in Ha. rewrite Hnu in Ha.
      pose proof (Hend θ pts1 Hθ Hvals Hlp' a Ha) as [Hres Hfact Hfits].
      rewrite Emem, <- Htg. constructor; [rewrite Htg; exact HMt | | exact Hfact | exact Hfits |].
      2: { intros Hr. exact (Hres Hr a (set_eq_refl a)). }
      pose proof (set_constructor_ok_target_params _ _ _ _ _ _ _ _ Hcok gs1 t0 gs2 F ds0 target tparams Egs Hsg θ Hθ') as Hps.
      unfold recursive_end_ctx in Hps. rewrite shape_domains_ctx_wk in Hps.
      change (tele_wk (doms_ctx (ptyp_doms t0)) (wk_pat (cargs_pat gs1)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk)
        with (shape_read_ctx Mk Ta φ (ptyp_doms t0)) in Hps.
      rewrite Hvals in Hps. unfold ptyp_ps_at, ptyp_depth in Hps. rewrite wk_pat_repeat_false in Hps.
      rewrite Eps. exact Hps.
    - (* a domain: the function's domain, and on under it *)
      cbn [ptyp_doms ptyp_mem ptyp_ps ptyp_depth] in EBs, Emem, Eps, Hld.
      destruct ds as [| d ds]; [discriminate |]. cbn [List.length] in Hld. injection Hld as Hld.
      apply List.Forall_cons_iff in Hds as [Hd Hds'].
      cbn [ptyp_ty] in HC. destruct (set_interp_pi_inv T γ _ _ _ _ _ _ _ HC) as (a1 & Fc & HA & HB & [[Hk _] | [_ ->]]);
        [discriminate |].
      rewrite wk_pat_repeat_false in HA.
      cbn [shape_code] in EC.
      assert (Eθ : set_env_eq γ θ θ) by exact (set_env_rel_eq T γ _ _ _ Hθ).
      destruct (pi_code_inj _ _ _ _ EC (set_interp_family_respects T γ Hfn Hmods _ _ _ _ _ _ _ Eθ HB)) as [Ea EF].
      { intros x y _ E. apply (shape_code_resp G HGresp); [exact Hds' | exact Htp | apply list_set_eq_refl |
          apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact E | constructor]]]. }
      assert (HFr : respects_set_eq_fun (fun b => shape_set G U S pre_e ds target tparams (pts1 ++ [b])))
        by (intros x y E; apply shape_set_resp; [exact Hds' | exact Htp | apply list_set_eq_refl
                                                | apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact E | constructor]]]).
      cbn [shape_set] in Ha.
      assert (Ed : set_eq (d (pre_e ++ pts1)) a1).
      { eapply set_eq_trans; [| apply set_eq_sym; exact Ea]. apply (Hdom 0 d pts1 eq_refl). lia. }
      cbn [shape_closed_ok]. exists a1. constructor; [exact HA | |].
      + eapply set_eq_trans; [exact (function_set_domain _ _ _ HFr Ha) |]. apply code_carrier_resp. exact Ed.
      + intros b Hb.
        assert (Hb' : set_mem b (code_carrier (d (pre_e ++ pts1))))
          by (eapply set_mem_eq_r; [apply code_carrier_resp; apply set_eq_sym; exact Ed | exact Hb]).
        pose proof (HB b Hb) as HBb. rewrite wk_pat_repeat_false in HBb.
        apply (IH (Bs1 ++ [A]) ds (set_env_extend θ (set_entry_term ak_relevant b)) (Fc b) (pts1 ++ [b])).
        * rewrite <- List.app_assoc. exact EBs.
        * exact Emem.
        * exact Eps.
        * rewrite !List.length_app, Hlp. reflexivity.
        * exact Hld.
        * exact Hds'.
        * intros k' d' pts0 Hk' Hl'. apply (Hdom (Datatypes.S k') d' pts0 Hk'). rewrite Hl', List.length_app. cbn [List.length]. lia.
        * rewrite shape_read_ctx_snoc. split; [exact Hθ |]. cbn [set_entry_rel]. exists b, b, a1.
          constructor; [reflexivity | reflexivity | exact HA | exact Hb | apply set_eq_refl].
        * rewrite shape_read_ctx_snoc. cbn [set_env_values]. change (set_env_tail (set_env_extend ?r ?e)) with r.
          rewrite Hvals, <- List.app_assoc. reflexivity.
        * rewrite shape_read_ctx_snoc, List.length_app, Nat.add_1_r. cbn [List.repeat List.app]. exact HBb.
        * exact (EF b Hb).
        * exact (function_set_apply _ _ _ _ HFr Ha Hb'). }
  apply (Gen t0 nil ds0 θa C0 nil a0); [reflexivity | reflexivity | reflexivity | reflexivity | exact Hlds | exact Hds0
                                       | | | | | exact EC0 | exact Ha0].
  - intros k' d pts0 Hk' Hl'. exact (Hdom0 k' d pts0 Hk' Hl').
  - change (shape_read_ctx Mk Ta φ nil) with (Ta ++ im_params D Mk). exact Hθa.
  - change (shape_read_ctx Mk Ta φ nil) with (Ta ++ im_params D Mk). rewrite List.app_nil_r. reflexivity.
  - change (shape_read_ctx Mk Ta φ nil) with (Ta ++ im_params D Mk). exact HC0.
Qed.

End LeafFits.

End Results.

(** ** The Induction on the Carriers *)

(** The fields of a tuple of distinct names are its components. *)
Lemma tuple_fields_combine : forall fl vals, NoDup fl -> List.length fl = List.length vals ->
    list_set_eq (List.map (tuple_field (tuple_code (List.combine fl vals))) fl) vals.
Proof.
  intros fl vals Hnd Hl.
  assert (Hf : List.map fst (List.combine fl vals) = fl).
  { clear Hnd. revert vals Hl; induction fl as [| a fl IH]; intros [| v vals] Hl; cbn in *; try lia; f_equal; auto. }
  assert (Hs : List.map snd (List.combine fl vals) = vals).
  { clear Hnd Hf. revert vals Hl; induction fl as [| a fl IH]; intros [| v vals] Hl; cbn in *; try lia; f_equal; auto. }
  set (fs := List.combine fl vals) in *. rewrite <- Hf, <- Hs. rewrite <- Hf in Hnd.
  assert (H : forall ps, List.incl ps fs -> list_set_eq (List.map (tuple_field (tuple_code fs)) (List.map fst ps)) (List.map snd ps)).
  { induction ps as [| [f v] ps IH]; intros Hi; cbn; constructor.
    - apply tuple_field_at; [exact Hnd | apply Hi; left; reflexivity].
    - apply IH. intros q Hq. apply Hi. right. exact Hq. }
  apply H. intros q Hq. exact Hq.
Qed.

(** The projections of an argument are its fields. *)
Lemma set_interp_list_projections : forall Ψ ρe x xv fs, set_interp T γ Ψ ρe x xv ->
    set_interp_list T γ Ψ ρe (projections_of fs x) (List.map (tuple_field xv) fs).
Proof.
  intros * Hx. induction fs as [| f fs IH]; cbn; constructor; [exact (set_interp_proj T γ _ _ f _ _ Hx) | exact IH].
Qed.

(** The variables past [rest] read the values [vs] an environment is
    extended by before [rest]. *)
Lemma set_interp_list_vars_from : forall Ψ vs rest ρ0 κs,
    set_interp_list T γ Ψ (set_env_extend_kinded ρ0 κs (vs ++ rest)) (vars_from (List.length rest) (List.length vs)) vs.
Proof.
  assert (Hs : forall k n, vars_from k (Datatypes.S n) = a_var (k + n) :: vars_from k n)
    by (intros; unfold vars_from; rewrite List.seq_S, List.rev_app_distr; reflexivity).
  induction vs as [| x vs IH]; intros rest ρ0 κs; [constructor |].
  cbn [List.length]. rewrite Hs. constructor.
  - replace x with (set_entry_value (set_env_extend_kinded ρ0 κs ((x :: vs) ++ rest) (List.length rest + (0 + List.length vs)))) at 2.
    + apply set_interp_var.
    + cbn [List.app set_env_extend_kinded]. replace (List.length rest + (0 + List.length vs)) with (List.length (vs ++ rest) + 0)
        by (rewrite List.length_app; lia).
      rewrite set_env_extend_kinded_ge. reflexivity.
  - cbn [List.app set_env_extend_kinded]. exact (IH rest _ _).
Qed.

(** A substituted telescope has the kinds of the telescope. *)
Lemma ctx_kinds_tele_sub : forall Δ σ, ctx_kinds (tele_sub Δ σ) = ctx_kinds Δ.
Proof.
  induction Δ as [| e Δ IH]; intros σ; [reflexivity |]. unfold ctx_kinds in *. cbn [tele_sub List.map List.rev].
  rewrite IH. destruct e; reflexivity.
Qed.

(** A name among a list's keys has an entry. *)
Lemma cons_lookup_of_names : forall (cs : list (string * list carg)) c, In c (List.map fst cs) -> exists gs, cons_lookup cs c = Some gs.
Proof.
  induction cs as [| [c' gs'] cs IH]; intros c Hin; [destruct Hin |]. cbn [cons_lookup].
  destruct (String.eqb_spec c c') as [-> | Hne]; [eauto |].
  destruct Hin as [E | Hin]; [cbn in E; congruence | exact (IH c Hin)].
Qed.

(** A variable agrees with the entry it reads. *)
Lemma sub_agrees_var : forall Ψ ρe x e, ρe x = e -> sub_entry_agrees T γ Ψ ρe (se_var x) e.
Proof. intros * <-. split; cbn; [exact (set_interp_var T γ _ _ x) | exact (set_interp_me_var T γ _ _ x)]. Qed.

(** The kinds of a context in two parts, outermost first. *)
Lemma ctx_kinds_app : forall Δ1 Δ2, ctx_kinds (Δ1 ++ Δ2) = ctx_kinds Δ2 ++ ctx_kinds Δ1.
Proof. intros. unfold ctx_kinds. rewrite List.map_app, List.rev_app_distr. reflexivity. Qed.

(** The substitution a recursive argument's shape components are moved by
    in a branch's context: past the arguments after it and the results
    before it, the instance of the arguments before it and the
    parameters; the shape's own substitution is it after the pattern's
    renaming. *)
Lemma rec_arg_inst_split : forall Γ p D k Mk Us c gs gs1 t gs2 E,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> ⊢ gc_deps ⍮ gc_stack ⍮ Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˢ sb_of_list sb_id Us : ind_uparams D ++ Γ ->
    In (c, gs) (im_cons Mk) -> gs = gs1 ++ ca_rec t :: gs2 -> ⊢ gc_deps ⍮ gc_stack ⍮ E ++ con_inst_ctx Γ p D Mk Us gs ->
    gc_deps ⍮ gc_stack ⍮ E ++ con_inst_ctx Γ p D Mk Us gs
      ⊢ˢ sb_compose (sb_qn (List.length gs1 + im_nn Mk) (sb_of_list sb_id Us))
           (sb_of_wk (wk_shiftn (List.length gs - List.length gs1 + List.length E))) : cargs_ctx p D Mk gs1 ++ im_params D Mk /\
    sb_eq (ihs_sub (im_nn Mk) Us (List.length gs) (cargs_pat gs1) (List.length E))
      (sb_compose (sb_of_wk (wk_pat (cargs_pat gs1)))
         (sb_compose (sb_qn (List.length gs1 + im_nn Mk) (sb_of_list sb_id Us))
            (sb_of_wk (wk_shiftn (List.length gs - List.length gs1 + List.length E))))).
Proof.
  intros * Hl Hk HΓ Hσ Hin Heq HΨ.
  pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (wf_sub_cinst _ _ _ _ _ _ _ _ Hgw HDs Hl Hk HΓ Hσ c gs gs1 (ca_rec t :: gs2) Hin Heq) as (Hi1 & Hτ2).
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hgw HDs Hl Hk Hin gs1 (ca_rec t :: gs2) Heq) as (HΨ1 & _ & _).
  assert (Hw3 : gc_deps ⍮ gc_stack ⍮ E ++ con_inst_ctx Γ p D Mk Us gs
                  ⊢ʷ wk_shiftn (List.length gs - List.length gs1 + List.length E) : con_inst_ctx Γ p D Mk Us gs1).
  { rewrite Heq in HΨ |- *; rewrite con_inst_ctx_split in HΨ |- *; rewrite List.app_assoc in HΨ |- *.
    replace (List.length (gs1 ++ ca_rec t :: gs2) - List.length gs1 + List.length E)
      with (List.length (E ++ tele_sub (cargs_ctx_aux p D (im_nn Mk) (true :: cargs_pat gs1) gs2)
                                     (sb_qn (S (List.length gs1)) (sb_qn (im_nn Mk) (sb_of_list sb_id Us)))
                                     ++ ce_ass ak_relevant (exp_sub (ptyp_ty p D (im_nn Mk) (cargs_pat gs1) t)
                                          (sb_qn (List.length gs1) (sb_qn (im_nn Mk) (sb_of_list sb_id Us)))) :: nil))
      by (rewrite !List.length_app, length_tele_sub, length_cargs_ctx_aux; cbn; lia).
    apply wf_wk_shiftn_app'; exact HΨ. }
  rewrite List.app_assoc in Hτ2; apply wf_sub_prefix in Hτ2; [| exact HΨ1].
  split.
  - eapply wf_sub_compose; [exact Hτ2 | apply wf_sub_of_wk; exact Hw3].
  - unfold ihs_sub. rewrite length_cargs_pat. apply sb_compose_assoc.
Qed.

(** Terms whose substitution agrees with the entries of an environment of
    a telescope, as many as its entries, read its values. *)
Lemma interp_list_of_sub_agrees : forall Ψ ρe Ms Δ θ, List.length Ms = List.length Δ ->
    (forall y, y < List.length Δ -> sub_entry_agrees T γ Ψ ρe (sb_of_list sb_id Ms y) (θ y)) ->
    set_interp_list T γ Ψ ρe Ms (set_env_values Δ θ).
Proof.
  intros Ψ ρe Ms Δ. revert Ms. induction Δ as [| e Δ IH]; intros Ms θ Hl H.
  - destruct Ms; [constructor | discriminate].
  - destruct (List.exists_last (l := Ms) ltac:(intros ->; discriminate)) as (Ms' & M & ->).
    rewrite List.length_app in Hl; cbn [List.length] in Hl.
    cbn [set_env_values]. apply set_interp_list_app.
    + apply IH; [lia |]. intros y Hy. specialize (H (Datatypes.S y) ltac:(cbn; lia)).
      rewrite sb_of_list_app in H. cbn [sb_of_list sb_extend] in H. exact H.
    + constructor; [| constructor]. specialize (H 0 ltac:(cbn; lia)).
      rewrite sb_of_list_app in H. cbn [sb_of_list sb_extend sentry_exp] in H. exact (proj1 H).
Qed.

Section Induction.
  (** The eliminator's context, environment, sort, group, uniform
      parameters, blocks, the set of its results, and the level of its
      motives *)
  Variables (Γ : ctx) (ρ : set_env) (r : abs_kind) (p : qname) (Us : list exp) (Bks : list eblock) (V : aczel_set).
  Variables (D : ind_decl) (i : nat).
  (** The uniform parameters' instance, and the universe of the carriers *)
  Variables (Fσ : set_env -> set_env) (U : aczel_set).
  Hypotheses (HΓ : set_ctx T γ Γ) (HcΓ : ⊢ gc_deps ⍮ gc_stack ⍮ Γ) (Hρ : set_env_in T γ Γ ρ)
    (HD : ind_lookup gc_deps gc_stack p = Some D)
    (Hσ : set_gsub_with T γ Γ (sb_of_list sb_id Us) (ind_uparams D ++ Γ) Fσ).
  Hypotheses (HDt : decl_typed gc_deps gc_stack D) (Hcl : decl_closed D) (HUl : List.length Us = ind_nu D).
  Hypothesis HMwf : forall j Mj, ind_member D j = Some Mj -> ⊢ gc_deps ⍮ gc_stack ⍮ elim_mctx p D j Mj Us ++ Γ.
  Hypothesis HMot : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
    exists FS FM FM', set_exp_eq_with T γ (elim_mctx p D j Mj Us ++ Γ) (abs_kind_sort r (a_typ i)) (eb_motive b) (eb_motive b) FS FM FM'.
  Hypothesis HMctx : forall j Mj, ind_member D j = Some Mj -> set_ctx T γ (elim_mctx p D j Mj Us ++ Γ).
  Hypothesis HMh : forall j Mj, ind_member D j = Some Mj -> elim_mctx_head_large gc_deps gc_stack Γ p D j Mj Us.
  Hypothesis HBk : forall j Mj, ind_member D j = Some Mj -> im_is_rview Mj = false -> exists b, List.nth_error Bks j = Some b.
  (** The carriers are the least fixed point in [U] *)
  Hypothesis Hcar : forall k Mk ρk, ind_member D k = Some Mk -> set_env_in T γ (im_params D Mk) ρk ->
    list_set_eq (uniform_values D Mk ρk) (elim_uniform_values ρ D Fσ) ->
    set_eq (set_group_carrier (global_group γ p) k (set_env_values (im_params D Mk) ρk))
           (member_carrier (global_group γ p) (elim_uniform_values ρ D Fσ) U U k (set_env_values (im_nparams Mk) ρk)).

  (** The instance of the motives' context in a branch's *)
  Hypothesis Hbτ : forall k Mk c gs, ind_member D k = Some Mk -> im_is_rview Mk = false -> ind_con Mk c = Some gs ->
    gc_deps ⍮ gc_stack ⍮ elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ
      ⊢ˢ sb_of_list (sb_of_wk (wk_shiftn (im_nn Mk + List.length gs + cargs_nrec D gs)))
           (vars_from (cargs_nrec D gs + List.length gs) (im_nn Mk) ++
            apps_exp (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c)
              (im_pre Mk (List.map (fun U => exp_wk U (wk_shiftn (im_nn Mk + List.length gs + cargs_nrec D gs))) Us) ++
               vars_from (cargs_nrec D gs + List.length gs) (im_nn Mk) ++ vars_from (cargs_nrec D gs) (List.length gs))
            :: nil)
      : elim_mctx p D k Mk Us ++ Γ.

  (** The branches' contexts denote and are well formed *)
  Hypothesis Hbctx : forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    set_ctx T γ (elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ) /\
    ⊢ gc_deps ⍮ gc_stack ⍮ elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ.
  (** A block has a branch per constructor *)
  Hypothesis Hbrs : forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b).
  (** The branches are of their types *)
  Hypothesis HBr : forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> ind_con Mk c = Some gs ->
    In (c, n, B) (eb_brs b) ->
    exists FS FB FB', set_exp_eq_with T γ (elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ)
                        (elim_branch_type p D k Mk c gs (eb_motive b) Us) B B FS FB FB'.
  (** Into a sort of relevant terms, the motives' elements are in [V] *)
  Hypothesis HV : r <> ak_propositional -> forall k Mk b FS FM FM' θ, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
    set_exp_eq_with T γ (elim_mctx p D k Mk Us ++ Γ) (abs_kind_sort r (a_typ i)) (eb_motive b) (eb_motive b) FS FM FM' ->
    set_env_in T γ (elim_mctx p D k Mk Us ++ Γ) θ -> set_sub (code_carrier (FM θ)) V.

  Let us := elim_uniform_values ρ D Fσ.
  Let G := global_group γ p.
  Let Q := elim_point Γ ρ r p Us Bks V D i us.
  Let S := carrier_points_with G us U U Q.

(** The uniform parameters read as the uniform values. *)
Lemma uniform_interp_list : set_interp_list T γ Γ ρ Us us.
Proof.
  unfold us, elim_uniform_values.
  assert (Gen : forall Δ θ Ms, List.length Ms = List.length Δ ->
            (forall y, y < List.length Δ -> set_interp T γ Γ ρ (List.nth (List.length Ms - 1 - y) Ms a_prop) (set_entry_value (θ y))) ->
            set_interp_list T γ Γ ρ Ms (set_env_values Δ θ)).
  { induction Δ as [| e Δ IH]; intros θ Ms Hl H.
    - destruct Ms; [constructor | discriminate].
    - destruct (List.exists_last (l := Ms) ltac:(intros ->; discriminate)) as (Ms' & M & ->).
      rewrite List.length_app in Hl; cbn [List.length] in Hl.
      cbn [set_env_values]. apply set_interp_list_app.
      + apply IH; [lia |]. intros y Hy. specialize (H (Datatypes.S y) ltac:(cbn; lia)).
        rewrite List.length_app, List.app_nth1 in H by (cbn; lia). cbn [List.length] in H.
        replace (List.length Ms' + 1 - 1 - Datatypes.S y) with (List.length Ms' - 1 - y) in H by lia. exact H.
      + constructor; [| constructor]. specialize (H 0 ltac:(cbn; lia)).
        rewrite List.length_app, List.app_nth2 in H by (cbn; lia). cbn [List.length] in H.
        replace (List.length Ms' + 1 - 1 - 0 - List.length Ms') with 0 in H by lia. exact H. }
  apply Gen; [rewrite HUl; reflexivity |]. intros y Hy.
  destruct (set_gsub_agrees _ _ _ _ _ _ Hσ ρ y Hρ) as [H _].
  rewrite (sb_of_list_nth Us sb_id y a_prop) in H by (rewrite HUl; exact Hy). cbn [sentry_exp] in H. exact H.
Qed.

Lemma points_in_fixed_point : set_sub S (carrier_fixed_point G us U U).
Proof.
  intros z Hz. unfold S, carrier_points_with in Hz.
  apply (set_mem_separation _ _ _ (carrier_points_with_pred_resp _)) in Hz as [Hz _]. exact Hz.
Qed.

(** A recursive field of a record view's element built from arguments
    drawn from the points having the property, at an environment of the
    uniform parameters of their values, extended by the fields before it:
    an environment of the fields before it, at which the field is a
    function on its domains whose ends have the property. *)
Lemma rview_field_closed_ok : forall k Mk qr Is fl SMk cs gs vals xv θ0 fs1 f t fs2,
    ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
    List.nth_error (set_group_members G) k = Some SMk -> In cs (set_member_constructors SMk) ->
    ind_con Mk (set_constructor_name cs) = Some gs ->
    arguments_fit G U S us (set_constructor_arguments cs) vals -> NoDup fl -> List.length fl = List.length vals ->
    set_eq xv (tuple_code (List.combine fl vals)) ->
    set_env_in T γ (ind_uparams D) θ0 -> list_set_eq (set_env_values (ind_uparams D) θ0) us ->
    List.combine fl gs = fs1 ++ (f, ca_rec t) :: fs2 ->
    set_env_in T γ (cargs_ctx p D Mk (List.map snd fs1) ++ im_params D Mk)
      (set_env_extend_kinded θ0 (ctx_kinds (cargs_ctx p D Mk (List.map snd fs1))) (List.map (tuple_field xv) (List.map fst fs1))) /\
    shape_closed_ok Γ ρ r p Us Bks V D i (rview_fits Γ ρ r p Us Bks V D us) Mk (cargs_ctx p D Mk (List.map snd fs1))
      (wk_pat (cargs_pat (List.map snd fs1))) nil t
      (set_env_extend_kinded θ0 (ctx_kinds (cargs_ctx p D Mk (List.map snd fs1))) (List.map (tuple_field xv) (List.map fst fs1)))
      (tuple_field xv f).
Proof.
  intros k Mk qr Is fl SMk cs gs vals xv' θ0 fs1 f t fs2 Hk Hh HSk Hcs Hgs Hfit Hnd Hlv Exv' Hθ0 Hus0 Ec.
  destruct (rview_params _ _ _ _ _ _ _ _ HDt Hk Hh) as [EG Hnn].
  destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ HDt) _ _ _ _ _ Hk Hh) as (gs0 & Hcs0 & Hlen).
  pose proof (cons_lookup_in _ _ _ Hgs) as Hin0. rewrite Hcs0 in Hin0. destruct Hin0 as [Ec0 | []]. injection Ec0 as Ename ->.
  destruct (combine_split_at _ _ _ _ _ _ (eq_sym Hlen) Ec) as [Efl Egs].
  set (gs1 := List.map snd fs1) in *. set (i0 := List.length gs1).
  (* the semantic constructor *)
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG. fold G in HG.
  pose proof (set_member_ok_constructors _ _ _ _ _ _ _ (set_group_ok_members _ _ _ _ _ HG _ _ _ Hk HSk) cs gs Hcs Hgs) as Hcok.
  set (sgs := set_constructor_arguments cs) in *.
  pose proof (set_group_ok_respects _ _ _ _ _ HG _ _ _ HSk Hcs) as Hrs. fold sgs in Hrs.
  pose proof (set_constructor_ok_shape _ _ _ _ _ _ _ _ Hcok) as Hsh.
  assert (Hgi : List.nth_error gs i0 = Some (ca_rec t))
    by (rewrite Egs, List.nth_error_app2, Nat.sub_diag by (unfold i0, gs1; lia); reflexivity).
  destruct (set_arguments_shape_nth _ _ Hsh _ _ Hgi) as (sg & Hsg & Hsgk).
  destruct Hsgk as (Fr & ds & tparams & -> & Hlds).
  (* the field values of the element at hand *)
  set (vals' := List.map (tuple_field xv') fl).
  assert (Evv : list_set_eq vals vals').
  { apply list_set_eq_sym. unfold vals'. eapply list_set_eq_trans; [| exact (tuple_fields_combine fl vals Hnd Hlv)].
    apply map_set_eq. intros g _. apply tuple_field_resp. exact Exv'. }
  set (L0 := set_env_values (im_params D Mk) θ0).
  assert (EL0 : L0 = set_env_values (ind_uparams D) θ0) by (unfold L0; rewrite EG; reflexivity).
  assert (Hfit' : arguments_fit G U S L0 sgs vals').
  { eapply arguments_fit_resp; [exact Hrs | | exact Evv | exact Hfit]. rewrite EL0. apply list_set_eq_sym. exact Hus0. }
  assert (Hθp : set_env_in T γ (im_params D Mk) θ0) by (rewrite EG; exact Hθ0).
  assert (Huni : list_set_eq (uniform_values D Mk θ0) us) by (unfold uniform_values; rewrite Hnn; exact Hus0).
  assert (Egs' : gs = gs1 ++ ca_rec t :: List.map snd fs2) by exact Egs.
  pose proof (args_env_closed ρ p D Fσ HD U Hcar S points_in_fixed_point k Mk SMk cs gs θ0 vals'
                Hk HSk Hcs Hgs Hcok Hθp Huni Hfit' gs1 _ Egs') as Hθa.
  set (θa := set_env_extend_kinded θ0 (ctx_kinds (cargs_ctx p D Mk gs1)) (List.firstn (List.length gs1) vals')) in *.
  assert (Hfst : List.firstn (List.length gs1) vals' = List.map (tuple_field xv') (List.map fst fs1)).
  { unfold vals'. rewrite Efl, List.map_app. unfold gs1. rewrite List.firstn_app, !List.length_map, Nat.sub_diag.
    rewrite List.firstn_all2 by (rewrite !List.length_map; lia).
    cbn [List.firstn]. rewrite List.app_nil_r. reflexivity. }
  assert (Hlc : List.length (cargs_ctx p D Mk gs1) = List.length (List.firstn (List.length gs1) vals')).
  { rewrite Hfst, length_cargs_ctx, !List.length_map. unfold gs1. rewrite List.length_map. reflexivity. }
  assert (HLθ : set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θa = L0 ++ List.firstn (List.length gs1) vals').
  { rewrite set_env_values_app. f_equal.
    - unfold L0. apply set_env_values_agree. intros y _. unfold set_env_drop, θa. rewrite Hlc, set_env_extend_kinded_ge. reflexivity.
    - unfold θa. apply set_env_values_extend_kinded_any. exact Hlc. }
  assert (Hvi : List.nth_error vals' (List.length gs1) = Some (tuple_field xv' f)).
  { unfold vals'. rewrite List.nth_error_map, Efl, List.nth_error_app2 by (unfold gs1; rewrite !List.length_map; lia).
    unfold gs1. rewrite !List.length_map, Nat.sub_diag. reflexivity. }
  assert (HL0 : List.length L0 = im_np D Mk) by (unfold L0; rewrite length_set_env_values, length_im_params; reflexivity).
  destruct (recursive_arg_setting p D HD U S k Mk SMk cs gs L0 vals' gs1 t (List.map snd fs2) Fr ds (ptyp_mem t) tparams θa
              (tuple_field xv' f) Hk HSk Hcs Hgs Hcok Hfit' HL0 Egs' Hsg Hvi Hθa ltac:(rewrite HLθ; apply list_set_eq_refl))
    as [Hdom Htps HC EC Hm].
  assert (Hin' : In (rview_con, gs) (im_cons Mk)) by (rewrite Hcs0; left; reflexivity).
  destruct (decl_shape_facts _ _ _ _ _ _ _ _ _ _ HDt Hk Hin' Egs') as (Mt & HMt & HPlt & HBt & HPt).
  assert (Hrsg : argument_respects (set_argument_recursive Fr ds (ptyp_mem t) tparams))
    by (rewrite List.Forall_forall in Hrs; exact (Hrs _ (List.nth_error_In _ _ Hsg))).
  destruct Hrsg as [Hds Htp].
  assert (HLv : list_set_eq (List.firstn (ind_nu D) (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θa)) us).
  { rewrite HLθ, List.firstn_app. replace (ind_nu D - List.length L0) with 0 by (rewrite HL0; unfold im_np; lia).
    rewrite List.firstn_all2 by (rewrite HL0; unfold im_np; lia). cbn [List.firstn]. rewrite List.app_nil_r, EL0. exact Hus0. }
  pose proof (shape_closed_ok_of_set Γ ρ r p Us Bks V D i HMwf HMot HMctx HD Hcl us U Mk gs sgs gs1 t
                (List.map snd fs2) Fr ds (ptyp_mem t) tparams _ θa _ (group_uniform_count p D HD) Hcok Egs' Hsg Hds Htp
                Hlds Mt HMt Hθa HLv Hdom Htps HC EC _ Hm) as Hshape.
  unfold θa in Hθa, Hshape. rewrite Hfst in Hθa, Hshape. split; [exact Hθa | exact Hshape].
Qed.

(** At a record view built from arguments drawn from the points having
    the property, its fits: along the paths of each recursive field, by
    the walk along the field's shape. *)
Lemma rview_point_fits : forall k Mk qr Is fl SMk cs gs vals xv,
    ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
    List.nth_error (set_group_members G) k = Some SMk -> In cs (set_member_constructors SMk) ->
    ind_con Mk (set_constructor_name cs) = Some gs ->
    arguments_fit G U S us (set_constructor_arguments cs) vals -> NoDup fl -> List.length fl = List.length vals ->
    set_eq xv (tuple_code (List.combine fl vals)) ->
    rview_fits Γ ρ r p Us Bks V D us k nil xv.
Proof.
  intros k Mk qr Is fl SMk cs gs vals xv Hk Hh HSk Hcs Hgs Hfit Hnd Hlv Exv.
  intros xv' Mj qr' Is' fl' c' gs' θ0 Ψ ρe β σ0 x Exv' Hj Hh' Hcs' Hθ0 Hus0 Hemb l Hin.
  rewrite Hk in Hj. injection Hj as <-. rewrite Hh in Hh'. injection Hh' as <- <- <-.
  destruct (rview_params _ _ _ _ _ _ _ _ HDt Hk Hh) as [EG Hnn].
  destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ HDt) _ _ _ _ _ Hk Hh) as (gs0 & Hcs0 & Hlen).
  rewrite Hcs0 in Hcs'. injection Hcs' as <- <-.
  pose proof (cons_lookup_in _ _ _ Hgs) as Hin0. rewrite Hcs0 in Hin0. destruct Hin0 as [Ec0 | []]. injection Ec0 as Ename ->.
  destruct Hemb as [HcΨ Hρe Hβ Hβt Hσ0 Hσ0a Huc0 Hx Hx0].
  apply fields_leaves_in in Hin as (fs1 & f & t & fs2 & l1 & Ec & -> & Hin1). cbn [List.app] in Hin1 |- *.
  destruct (combine_split_at _ _ _ _ _ _ (eq_sym Hlen) Ec) as [Efl Egs].
  destruct (rview_field_closed_ok k Mk qr Is fl SMk cs gs vals xv' θ0 fs1 f t fs2 Hk Hh HSk Hcs Hgs Hfit Hnd Hlv
              (set_eq_trans _ _ _ (set_eq_sym _ _ Exv') Exv) Hθ0 Hus0 Ec) as [Hθa Hshape].
  set (gs1 := List.map snd fs1) in *. set (pat := cargs_pat gs1) in *.
  set (θa := set_env_extend_kinded θ0 (ctx_kinds (cargs_ctx p D Mk gs1)) (List.map (tuple_field xv') (List.map fst fs1))) in *.
  pose proof (decls_of_ctx _ _ _ HcΓ) as HDs.
  assert (Hσ0' : gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ σ0 : im_params D Mk) by (rewrite EG; exact Hσ0).
  destruct (rview_field_arg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hgw HDs HD Hk Hh Hcs0 Ec Hσ0' Hx0) as [Hτ Hxf].
  set (τ := sb_of_list σ0 (projections_of (List.map fst fs1) x)) in *.
  assert (Egs' : gs = gs1 ++ ca_rec t :: List.map snd fs2) by exact Egs.
  assert (Hin' : In (rview_con, gs) (im_cons Mk)) by (rewrite Hcs0; left; reflexivity).
  destruct (decl_shape_facts _ _ _ _ _ _ _ _ _ _ HDt Hk Hin' Egs') as (Mt & HMt & HPlt & HBt & HPt).
  assert (Hlc : List.length (cargs_ctx p D Mk gs1) = List.length (List.map (tuple_field xv') (List.map fst fs1)))
    by (rewrite length_cargs_ctx, !List.length_map; unfold gs1; rewrite List.length_map; reflexivity).
  (* the walk along the field's shape *)
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hgw HDs HD Hk Hin' gs1 _ Egs') as (_ & HcN & Hφ).
  assert (Hlg : List.length (cargs_pat gs1) = List.length (projections_of (List.map fst fs1) x))
    by (unfold gs1, projections_of; rewrite length_cargs_pat, !List.length_map; reflexivity).
  assert (Huc1 : forall y, y < ind_nu D ->
            sentry_exp (τ (y + (List.length (cargs_pat gs1) + im_nn Mk))) = sentry_exp (sb_compose (sb_of_list sb_id Us) β y)).
  { intros y Hy. rewrite Hnn, Nat.add_0_r, Nat.add_comm, Hlg. unfold τ. rewrite sb_of_list_ge. exact (Huc0 y Hy). }
  assert (Hσt : gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ sb_compose (sb_of_wk (wk_pat pat)) τ : doms_ctx nil ++ cargs_nonrec_ctx gs1 ++ im_params D Mk)
    by (eapply wf_sub_compose; [apply wf_sub_of_wk; exact Hφ | exact Hτ]).
  assert (Huc : shape_uc D Us (doms_ctx nil ++ cargs_nonrec_ctx gs1 ++ im_params D Mk) (sb_compose (sb_of_wk (wk_pat pat)) τ) β).
  { intros y Hy; cbn [doms_ctx List.rev List.map List.app] in *.
    rewrite EG, List.length_app; cbn [sb_compose sb_of_wk sentry_sub].
    replace (y + (List.length (cargs_nonrec_ctx gs1) + List.length (ind_uparams D) - ind_nu D))
      with (pat_nargs (cargs_pat gs1) + y) by (rewrite pat_nargs_cargs_pat; unfold ind_nu; lia).
    fold pat. rewrite wk_pat_ge; cbn [sb_compose] in Huc1.
    rewrite <- (Huc1 y Hy), Hnn, Nat.add_0_r, Nat.add_comm; reflexivity. }
  assert (Hrz : shape_realized D us Mk (cargs_nonrec_ctx gs1) (cargs_ctx p D Mk gs1) (wk_pat pat) nil Ψ ρe
                  (sb_compose (sb_of_wk (wk_pat pat)) τ) τ θa).
  { constructor.
    - exact Hφ.
    - intros y. rewrite <- pat_nargs_cargs_pat. fold pat. rewrite wk_pat_ge. unfold pat. rewrite length_cargs_pat, length_cargs_ctx.
      reflexivity.
    - exact Hτ.
    - intros y. unfold τ, θa.
      exact (sub_agrees_of_list _ _ _ _ (set_interp_list_projections _ _ _ _ _ Hx) σ0 θ0 _ Hσ0a y).
    - intros z. reflexivity.
    - exact Hθa.
    - cbn [List.length]. rewrite Hnn, Nat.add_0_r.
      rewrite (set_env_values_agree _ _ θ0); [exact Hus0 |].
      intros y _. unfold set_env_drop, θa. rewrite Hlc, set_env_extend_kinded_ge. reflexivity. }
  assert (Hxt : gc_deps ⍮ gc_stack ⍮ Ψ ⊢ a_proj f x
                  : ptyp_ty_at p D (List.map (fun U => exp_sub U β) Us) (sb_compose (sb_of_wk (wk_pat pat)) τ) t).
  { rewrite ptyp_ty_eq_at, ptyp_ty_at_sub in Hxf by (try exact Hcl; apply length_ind_uvars).
    fold gs1 in Hxf. rewrite (uvars_inst _ _ _ _ _ _ HUl Huc1) in Hxf. exact Hxf. }
  assert (Hin2 : In l1 (shape_leaves (rview_leaves D) (List.length (@nil exp) + List.length (cargs_nonrec_ctx gs1) + im_nn Mk) t)).
  { cbn [List.length]. rewrite Hnn, Nat.add_0_r.
    replace (List.length (cargs_nonrec_ctx gs1)) with (List.length (fields_args fs1)); [exact Hin1 |].
    unfold gs1; clear; induction fs1 as [| [? []] fs1 IH]; cbn [List.map snd fields_args cargs_nonrec_ctx];
      rewrite ?List.length_app; cbn [List.length]; lia. }
  pose proof (shape_leaf_sem Γ ρ r p Us Bks V D i HMwf HDt Hcl HUl HMh HBk us (rview_fits Γ ρ r p Us Bks V D us)
                (rview_fits_at_end Γ ρ r p Us Bks V D i HMot HDt Hcl HUl us) t Mk nil (cargs_nonrec_ctx gs1)
                (cargs_ctx p D Mk gs1) (wk_pat pat) Ψ ρe β _ τ (a_proj f x) (tuple_field xv' f) θa Mt HcΨ Hρe Hβ Hβt Hσt HcN Huc Hrz
                (set_interp_proj T γ _ _ f _ _ Hx) Hxt HMt HPlt HBt HPt Hshape l1 Hin2) as Hsem.
  (* the fit along the field's path *)
  assert (Hσ1e : sb_eq (sb_compose (sb_of_wk (wk_pat pat)) τ) (sb_of_list σ0 (projections_of (fields_args fs1) x))).
  { pose proof (wk_pat_projections fs1 nil σ0 x) as E; rewrite List.app_nil_r in E.
    etransitivity; [exact E |]. apply sb_of_list_cong; intros z; reflexivity. }
  intros A HA. cbn [leaf_ihty] in HA.
  rewrite <- (leaf_ihty_sb_eq r l1 (blocks_motives Bks) β β (sb_compose (sb_of_wk (wk_pat pat)) τ)
                (sb_of_list σ0 (projections_of (fields_args fs1) x)) (a_proj f x)) in HA; [| reflexivity | exact Hσ1e].
  assert (Hlv' : leaf_value Γ ρ r p Us Bks V (leaf_proj f (fields_args fs1) l1) xv' =
                 leaf_value Γ ρ r p Us Bks V l1 (tuple_field xv' f))
    by (unfold leaf_value; destruct r; reflexivity).
  rewrite Hlv'.
  exact (leaf_fit Γ ρ r p Us Bks V D i HMwf HMot l1 Ψ ρe β _ (a_proj f x) (tuple_field xv' f) A HcΨ Hρe Hβ
           (set_interp_proj T γ _ _ f _ _ Hx) Hsem HA).
Qed.

Lemma fields_args_snoc : forall fs f g, fields_args (fs ++ [(f, g)]) =
    fields_args fs ++ match g with ca_arg _ _ => [f] | ca_rec _ => nil end.
Proof.
  induction fs as [| [f0 [] ] fs IH]; intros f g; cbn [List.app fields_args]; [destruct g; reflexivity | |];
    rewrite IH; [reflexivity | reflexivity].
Qed.

(** At a record view built from arguments drawn from the points having
    the property, into a sort of relevant terms, its fields' results
    along its paths. *)
Lemma rview_point_results : r <> ak_propositional -> forall k Mk qr Is fl SMk cs gs vals xv θ0,
    ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
    List.nth_error (set_group_members G) k = Some SMk -> In cs (set_member_constructors SMk) ->
    ind_con Mk (set_constructor_name cs) = Some gs ->
    arguments_fit G U S us (set_constructor_arguments cs) vals -> NoDup fl -> List.length fl = List.length vals ->
    set_eq xv (tuple_code (List.combine fl vals)) ->
    set_env_in T γ (ind_uparams D) θ0 -> list_set_eq (set_env_values (ind_uparams D) θ0) us ->
    set_ihs T γ Γ ρ r p Us Bks gs (List.map (tuple_field xv) fl)
      (List.map (fun l => leaf_result Γ ρ r p Us Bks V l xv) (fields_leaves (rview_leaves D) nil (List.combine fl gs))).
Proof.
  intros Hr k Mk qr Is fl SMk cs gs vals xv θ0 Hk Hh HSk Hcs Hgs Hfit Hnd Hlv Exv Hθ0 Hus0.
  destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ HDt) _ _ _ _ _ Hk Hh) as (gs0 & Hcs0 & Hlen).
  pose proof (cons_lookup_in _ _ _ Hgs) as Hin0. rewrite Hcs0 in Hin0. destruct Hin0 as [Ec0 | []]. injection Ec0 as _ ->.
  pose proof (leaves_coherent_of_order _ (rview_struct_order _ _ _ (decl_typed_record_struct _ _ _ HDt))) as Hco.
  assert (Hf : List.map fst (List.combine fl gs) = fl).
  { clear -Hlen. revert gs Hlen; induction fl as [| a fl IH]; intros [| g gs] Hl; cbn in *; try lia; f_equal; auto. }
  assert (Hs : List.map snd (List.combine fl gs) = gs).
  { clear -Hlen. revert gs Hlen; induction fl as [| a fl IH]; intros [| g gs] Hl; cbn in *; try lia; f_equal; auto. }
  assert (Gen : forall fs fs1, List.combine fl gs = fs1 ++ fs ->
            set_ihs T γ Γ ρ r p Us Bks (List.map snd fs) (List.map (tuple_field xv) (List.map fst fs))
              (List.map (fun l => leaf_result Γ ρ r p Us Bks V l xv) (fields_leaves (rview_leaves D) (fields_args fs1) fs))).
  { induction fs as [| [f [κ A | t]] fs IH]; intros fs1 Efs; cbn [List.map fst snd fields_leaves].
    - constructor.
    - constructor. replace (fields_args fs1 ++ [f]) with (fields_args (fs1 ++ [(f, ca_arg κ A)])) by apply fields_args_snoc.
      apply IH. rewrite Efs, <- List.app_assoc. reflexivity.
    - rewrite List.map_app, (List.map_map (leaf_proj f (fields_args fs1))). cbn [leaf_result]. constructor.
      + destruct (rview_field_closed_ok k Mk qr Is fl SMk cs gs vals xv θ0 fs1 f t fs Hk Hh HSk Hcs Hgs Hfit Hnd Hlv Exv Hθ0 Hus0 Efs)
          as [_ Hcok].
        apply (set_ih_of_shape_results Γ ρ r p Us Bks V Hρ D HD Hco HDt).
        exact (shape_results_of_closed_ok Γ ρ r p Us Bks V D i Hr _ _ _ _ _ _ _ _ Hcok).
      + replace (fields_args fs1) with (fields_args (fs1 ++ [(f, ca_rec t)])) by (rewrite fields_args_snoc, List.app_nil_r; reflexivity).
        apply IH. rewrite Efs, <- List.app_assoc. reflexivity. }
  pose proof (Gen (List.combine fl gs) nil eq_refl) as H. rewrite Hf, Hs in H. exact H.
Qed.

(** The arguments before [gs1]'s end of a block member's constructor and
    the parameters, read as the open instance reads them: an environment
    of their closed context, of the values the carriers read. *)
Lemma block_args_env_closed : forall k Mk SMk cs gs vals θk gs1 rest,
    ind_member D k = Some Mk -> List.nth_error (set_group_members G) k = Some SMk -> In cs (set_member_constructors SMk) ->
    ind_con Mk (set_constructor_name cs) = Some gs ->
    set_env_in T γ (im_params D Mk) θk -> list_set_eq (uniform_values D Mk θk) us ->
    arguments_fit G U S (us ++ set_env_values (im_nparams Mk) θk) (set_constructor_arguments cs) vals ->
    gs = gs1 ++ rest ->
    set_env_in T γ (cargs_ctx p D Mk gs1 ++ im_params D Mk)
      (set_env_moved (List.length (cargs_ctx p D Mk gs1 ++ im_nparams Mk)) Fσ
         (set_env_extend_kinded (set_env_extend_kinded ρ (ctx_kinds (im_nparams Mk)) (set_env_values (im_nparams Mk) θk))
            (ctx_kinds (cargs_ctx p D Mk gs1)) (List.firstn (List.length gs1) vals))) /\
    list_set_eq
      (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk)
         (set_env_moved (List.length (cargs_ctx p D Mk gs1 ++ im_nparams Mk)) Fσ
            (set_env_extend_kinded (set_env_extend_kinded ρ (ctx_kinds (im_nparams Mk)) (set_env_values (im_nparams Mk) θk))
               (ctx_kinds (cargs_ctx p D Mk gs1)) (List.firstn (List.length gs1) vals))))
      ((us ++ set_env_values (im_nparams Mk) θk) ++ List.firstn (List.length gs1) vals).
Proof.
  intros k Mk SMk cs gs vals θk gs1 rest Hk HSk Hcs Hgs Hθk Huni Hfit Egs.
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG. fold G in HG.
  pose proof (set_member_ok_constructors _ _ _ _ _ _ _ (set_group_ok_members _ _ _ _ _ HG _ _ _ Hk HSk) cs gs Hcs Hgs) as Hcok.
  set (sgs := set_constructor_arguments cs) in *.
  pose proof (cons_lookup_in _ _ _ Hgs) as Hin.
  pose proof (arguments_fit_length _ _ _ _ _ _ Hfit) as Hlv.
  pose proof (set_arguments_shape_length _ _ (set_constructor_ok_shape _ _ _ _ _ _ _ _ Hcok)) as Hlsh.
  set (i0 := List.length gs1). set (nn := im_nn Mk).
  assert (Hi0 : i0 <= List.length vals) by (unfold i0; rewrite Hlv, Hlsh, Egs, List.length_app; lia).
  set (ρn := set_env_extend_kinded ρ (ctx_kinds (im_nparams Mk)) (set_env_values (im_nparams Mk) θk)) in *.
  pose proof (nparams_env Γ ρ p D Us Fσ HΓ HcΓ Hρ HD Hσ k Mk SMk _ _ θk Hk HSk Hin Hθk Huni) as Hρn. fold ρn in Hρn.
  assert (Hlnp : List.length (ctx_kinds (im_nparams Mk)) = List.length (set_env_values (im_nparams Mk) θk))
    by (rewrite length_ctx_kinds, length_set_env_values; reflexivity).
  assert (Hdrop : forall x, set_env_drop (im_nn Mk) ρn x = ρ x).
  { intros x. unfold set_env_drop, ρn. unfold im_nn. rewrite <- length_ctx_kinds, Hlnp, set_env_extend_kinded_ge. reflexivity. }
  assert (Hvn : set_env_values (im_nparams Mk) ρn = set_env_values (im_nparams Mk) θk)
    by (unfold ρn; apply set_env_values_extend_kinded; rewrite length_set_env_values; reflexivity).
  assert (Hfit' : arguments_fit G U S (elim_uniform_values ρ D Fσ ++ set_env_values (im_nparams Mk) ρn) sgs vals)
    by (rewrite Hvn; exact Hfit).
  pose proof (args_env Γ ρ p D Us Fσ HΓ HcΓ Hρ HD Hσ U Hcar S points_in_fixed_point k Mk SMk cs gs ρn vals Hk HSk Hcs Hgs Hcok Hρn Hdrop Hfit'
                gs1 _ Egs) as Hρo.
  set (ρo := set_env_extend_kinded ρn (ctx_kinds (cargs_ctx p D Mk gs1)) (List.firstn i0 vals)) in *.
  fold i0 in Hρo. fold ρo in Hρo.
  assert (Hlf : List.length (List.firstn i0 vals) = i0) by (rewrite List.length_firstn; lia).
  assert (Hρo_drop : forall x, ρo (i0 + nn + x) = ρ x).
  { intros x. unfold ρo. replace (i0 + nn + x) with (List.length (List.firstn i0 vals) + (nn + x)) by lia.
    rewrite set_env_extend_kinded_ge. rewrite <- Hdrop. reflexivity. }
  set (Ψc := cargs_ctx p D Mk gs1 ++ im_nparams Mk) in *.
  assert (HΨc : List.length Ψc = i0 + nn) by (unfold Ψc; rewrite List.length_app, length_cargs_ctx; reflexivity).
  assert (EΨ : Ψc ++ ind_uparams D = cargs_ctx p D Mk gs1 ++ im_params D Mk) by (unfold Ψc, im_params; rewrite <- List.app_assoc; reflexivity).
  pose proof (cargs_ctx_closed p D k Mk _ gs gs1 rest Hcl Hk Hin Egs) as Hs0.
  pose proof (decls_of_ctx _ _ _ HcΓ) as HDs.
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hgw HDs HD Hk Hin gs1 _ Egs) as (Hw0 & _ & _).
  pose proof (cargs_prefix_ctx p D HD k Mk SMk gs sgs gs1 _ Hk HSk Hcok Egs) as Hc0.
  assert (Hass0 : all_assumptions (cargs_ctx p D Mk gs1 ++ im_params D Mk))
    by (apply List.Forall_app; split; [apply cargs_ctx_aux_ass | exact (decl_closed_params_ass _ _ _ Hcl Hk)]).
  pose proof (wf_ctx_closed_app _ _ _ _ Hass0 Hs0 Hw0 HcΓ) as HwΓ0.
  assert (HcΓ0 : set_ctx T γ ((cargs_ctx p D Mk gs1 ++ im_params D Mk) ++ Γ)).
  { pose proof (set_ctx_moved T γ Hfn Hmods _ nil Γ _ _ (set_gsub_drop T γ _ HcΓ) HΓ ltac:(rewrite List.app_nil_r; exact Hc0)
                  ltac:(rewrite List.app_nil_r; exact Hw0)) as H.
    rewrite tele_sub_closed in H by exact Hs0. exact H. }
  rewrite <- EΨ in Hs0, Hw0, Hc0, Hass0, HwΓ0, HcΓ0 |- *.
  destruct (inst_closed_env_in Γ (ind_uparams D) _ Fσ Hσ HΓ HcΓ Ψc ρo Hs0 Hc0 HcΓ0 Hw0 HwΓ0 Hρo) as [Hm Hinst].
  set (θa := set_env_moved (List.length Ψc) Fσ ρo) in *.
  assert (Eθi : forall x, x < List.length (Ψc ++ ind_uparams D) -> inst_closed_env Γ (ind_uparams D) Fσ Ψc ρo x = θa x).
  { intros x Hx. unfold inst_closed_env. fold θa. unfold set_env_moved at 1. rewrite set_env_above_lt' by exact Hx. reflexivity. }
  split.
  - apply (env_in_closed_agree _ _ _ Hs0 Hass0 Hc0 Hinst Eθi).
    rewrite List.app_assoc in Hm. exact (set_env_rel_eq T γ _ _ _ (set_env_rel_drop T γ _ _ _ _ Hm)).
  - rewrite <- (set_env_values_agree _ _ _ Eθi), inst_closed_env_values. rewrite <- List.app_assoc. apply list_set_eq_app.
    + apply (inst_uniform_values Γ ρ D Us Fσ HcΓ Hρ Hσ). intros x. unfold set_env_drop. rewrite HΨc. apply Hρo_drop.
    + unfold Ψc. rewrite set_env_values_app. apply list_set_eq_app.
      * rewrite <- Hvn. rewrite (set_env_values_agree (im_nparams Mk) _ ρn); [apply list_set_eq_refl |].
        intros x _. unfold set_env_drop, ρo. rewrite length_cargs_ctx. fold i0.
        replace (i0 + x) with (List.length (List.firstn i0 vals) + x) by lia. rewrite set_env_extend_kinded_ge. reflexivity.
      * unfold ρo. rewrite set_env_values_extend_kinded_any by (rewrite length_cargs_ctx, Hlf; reflexivity).
        apply list_set_eq_refl.
Qed.

(** A recursive argument of a block member's constructor, drawn from the
    points having the property, at the environment of the arguments
    before it and the parameters the open instance reads: an environment
    of their closed context, at which the argument is a function on its
    domains whose ends have the property. *)
Lemma block_arg_closed : forall k Mk SMk cs gs vals θk gs1 t gs2 v,
    ind_member D k = Some Mk -> List.nth_error (set_group_members G) k = Some SMk -> In cs (set_member_constructors SMk) ->
    ind_con Mk (set_constructor_name cs) = Some gs ->
    set_env_in T γ (im_params D Mk) θk -> list_set_eq (uniform_values D Mk θk) us ->
    arguments_fit G U S (us ++ set_env_values (im_nparams Mk) θk) (set_constructor_arguments cs) vals ->
    gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error vals (List.length gs1) = Some v ->
    set_env_in T γ (cargs_ctx p D Mk gs1 ++ im_params D Mk)
      (set_env_moved (List.length (cargs_ctx p D Mk gs1 ++ im_nparams Mk)) Fσ
         (set_env_extend_kinded (set_env_extend_kinded ρ (ctx_kinds (im_nparams Mk)) (set_env_values (im_nparams Mk) θk))
            (ctx_kinds (cargs_ctx p D Mk gs1)) (List.firstn (List.length gs1) vals))) /\
    shape_closed_ok Γ ρ r p Us Bks V D i (rview_fits Γ ρ r p Us Bks V D us) Mk (cargs_ctx p D Mk gs1) (wk_pat (cargs_pat gs1)) nil t
      (set_env_moved (List.length (cargs_ctx p D Mk gs1 ++ im_nparams Mk)) Fσ
         (set_env_extend_kinded (set_env_extend_kinded ρ (ctx_kinds (im_nparams Mk)) (set_env_values (im_nparams Mk) θk))
            (ctx_kinds (cargs_ctx p D Mk gs1)) (List.firstn (List.length gs1) vals))) v.
Proof.
  intros k Mk SMk cs gs vals θk gs1 t gs2 v Hk HSk Hcs Hgs Hθk Huni Hfit Egs Hv.
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG. fold G in HG.
  pose proof (set_member_ok_constructors _ _ _ _ _ _ _ (set_group_ok_members _ _ _ _ _ HG _ _ _ Hk HSk) cs gs Hcs Hgs) as Hcok.
  set (sgs := set_constructor_arguments cs) in *.
  pose proof (set_group_ok_respects _ _ _ _ _ HG _ _ _ HSk Hcs) as Hrs. fold sgs in Hrs.
  pose proof (set_constructor_ok_shape _ _ _ _ _ _ _ _ Hcok) as Hsh.
  pose proof (cons_lookup_in _ _ _ Hgs) as Hin.
  set (i0 := List.length gs1). set (nn := im_nn Mk).
  assert (Hgi : List.nth_error gs i0 = Some (ca_rec t)) by (rewrite Egs, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
  destruct (set_arguments_shape_nth _ _ Hsh _ _ Hgi) as (sg & Hsg & Hsgk).
  destruct Hsgk as (Fr & ds & tparams & -> & Hlds).
  set (ρn := set_env_extend_kinded ρ (ctx_kinds (im_nparams Mk)) (set_env_values (im_nparams Mk) θk)) in *.
  pose proof (nparams_env Γ ρ p D Us Fσ HΓ HcΓ Hρ HD Hσ k Mk SMk _ _ θk Hk HSk Hin Hθk Huni) as Hρn. fold ρn in Hρn.
  assert (Hlnp : List.length (ctx_kinds (im_nparams Mk)) = List.length (set_env_values (im_nparams Mk) θk))
    by (rewrite length_ctx_kinds, length_set_env_values; reflexivity).
  assert (Hdrop : forall x, set_env_drop (im_nn Mk) ρn x = ρ x).
  { intros x. unfold set_env_drop, ρn. unfold im_nn. rewrite <- length_ctx_kinds, Hlnp, set_env_extend_kinded_ge. reflexivity. }
  assert (Hvn : set_env_values (im_nparams Mk) ρn = set_env_values (im_nparams Mk) θk)
    by (unfold ρn; apply set_env_values_extend_kinded; rewrite length_set_env_values; reflexivity).
  assert (Hfit' : arguments_fit G U S (elim_uniform_values ρ D Fσ ++ set_env_values (im_nparams Mk) ρn) sgs vals)
    by (rewrite Hvn; exact Hfit).
  pose proof (args_env Γ ρ p D Us Fσ HΓ HcΓ Hρ HD Hσ U Hcar S points_in_fixed_point k Mk SMk cs gs ρn vals Hk HSk Hcs Hgs Hcok Hρn Hdrop Hfit'
                gs1 _ Egs) as Hρo.
  set (ρo := set_env_extend_kinded ρn (ctx_kinds (cargs_ctx p D Mk gs1)) (List.firstn i0 vals)) in *.
  destruct (List.nth_error_split vals i0 Hv) as (l1 & l2 & Evals & Hl1).
  fold i0 in Hρo. fold ρo in Hρo.
  assert (Hfst : List.firstn i0 vals = l1) by (rewrite Evals, <- Hl1, List.firstn_app, Nat.sub_diag, List.firstn_all; cbn; apply List.app_nil_r).
  assert (Hρo_drop : forall x, ρo (i0 + nn + x) = ρ x).
  { intros x. unfold ρo. replace (i0 + nn + x) with (List.length (List.firstn i0 vals) + (nn + x))
      by (rewrite Hfst, Hl1; lia). rewrite set_env_extend_kinded_ge. rewrite <- Hdrop. reflexivity. }
  (* the closed environment of the arguments before and the parameters *)
  set (Ψc := cargs_ctx p D Mk gs1 ++ im_nparams Mk) in *.
  assert (HΨc : List.length Ψc = i0 + nn) by (unfold Ψc; rewrite List.length_app, length_cargs_ctx; reflexivity).
  assert (EΨ : Ψc ++ ind_uparams D = cargs_ctx p D Mk gs1 ++ im_params D Mk) by (unfold Ψc, im_params; rewrite <- List.app_assoc; reflexivity).
  destruct (block_args_env_closed k Mk SMk cs gs vals θk gs1 _ Hk HSk Hcs Hgs Hθk Huni Hfit Egs) as [Hθa HLθ].
  fold i0 ρn ρo Ψc in Hθa, HLθ. rewrite <- Hvn in HLθ.
  set (θa := set_env_moved (List.length Ψc) Fσ ρo) in *.
  assert (HL0 : List.length (us ++ set_env_values (im_nparams Mk) ρn) = im_np D Mk)
    by (unfold us, elim_uniform_values; rewrite List.length_app, !length_set_env_values; unfold im_np, im_nn, ind_nu; lia).
  destruct (recursive_arg_setting p D HD U S k Mk SMk cs gs (us ++ set_env_values (im_nparams Mk) ρn) vals gs1 t gs2 Fr ds
              (ptyp_mem t) tparams θa v Hk HSk Hcs Hgs Hcok Hfit' HL0 Egs Hsg Hv Hθa HLθ) as [Hdom Htps HC EC Hmem].
  destruct (decl_shape_facts _ _ _ _ _ _ _ _ _ _ HDt Hk Hin Egs) as (Mt & HMt & _ & _ & _).
  assert (Hrsg : argument_respects (set_argument_recursive Fr ds (ptyp_mem t) tparams))
    by (rewrite List.Forall_forall in Hrs; exact (Hrs _ (List.nth_error_In _ _ Hsg))).
  destruct Hrsg as [Hds Htp].
  assert (HLv : list_set_eq (List.firstn (ind_nu D) (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θa)) us).
  { eapply list_set_eq_trans; [apply list_set_eq_firstn; exact HLθ |].
    assert (Hnu : List.length us = ind_nu D) by (unfold us, elim_uniform_values; rewrite length_set_env_values; reflexivity).
    rewrite <- !List.app_assoc, List.firstn_app, Hnu, Nat.sub_diag, List.firstn_all2 by lia. cbn [List.firstn].
    rewrite List.app_nil_r. apply list_set_eq_refl. }
  split; [exact Hθa |].
  exact (shape_closed_ok_of_set Γ ρ r p Us Bks V D i HMwf HMot HMctx HD Hcl us U Mk gs sgs gs1 t gs2 Fr ds (ptyp_mem t) tparams
           _ θa _ (group_uniform_count p D HD) Hcok Egs Hsg Hds Htp Hlds Mt HMt Hθa HLv Hdom Htps HC EC _ Hmem).
Qed.

(** In a branch's context after the results [E], at an environment
    holding the arguments above [E], a recursive argument drawn from the
    points having the property has its results of their types along its
    paths: the walk along its shape, read over the arguments before it. *)
Lemma block_arg_fits : forall k Mk SMk cs gs vals θk E ρe gs1 t gs2 v,
    ind_member D k = Some Mk -> List.nth_error (set_group_members G) k = Some SMk -> In cs (set_member_constructors SMk) ->
    ind_con Mk (set_constructor_name cs) = Some gs ->
    set_env_in T γ (im_params D Mk) θk -> list_set_eq (uniform_values D Mk θk) us ->
    arguments_fit G U S (us ++ set_env_values (im_nparams Mk) θk) (set_constructor_arguments cs) vals ->
    ⊢ gc_deps ⍮ gc_stack ⍮ E ++ con_inst_ctx Γ p D Mk Us gs -> set_env_in T γ (E ++ con_inst_ctx Γ p D Mk Us gs) ρe ->
    (forall z, ρe (List.length E + z) =
       set_env_extend_kinded (set_env_extend_kinded ρ (ctx_kinds (im_nparams Mk)) (set_env_values (im_nparams Mk) θk))
         (ctx_kinds (cargs_ctx p D Mk gs)) vals z) ->
    gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error vals (List.length gs1) = Some v ->
    forall l, In l (shape_leaves (rview_leaves D) (pat_nargs (cargs_pat gs1) + im_nn Mk) t) ->
    forall A, set_interp T γ (E ++ con_inst_ctx Γ p D Mk Us gs) ρe
      (leaf_ihty r (blocks_motives Bks) (sb_of_wk (wk_shiftn (List.length E + List.length gs + im_nn Mk)))
         (ihs_sub (im_nn Mk) Us (List.length gs) (cargs_pat gs1) (List.length E))
         (a_var (List.length E + List.length gs - 1 - List.length (cargs_pat gs1))) l) A ->
    set_mem (leaf_value Γ ρ r p Us Bks V l v) (code_carrier A).
Proof.
  intros k Mk SMk cs gs vals θk E ρe gs1 t gs2 v Hk HSk Hcs Hgs Hθk Huni Hfit HcΨ Hρe Eρe Egs Hv l Hl A HA.
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG. fold G in HG.
  pose proof (set_member_ok_constructors _ _ _ _ _ _ _ (set_group_ok_members _ _ _ _ _ HG _ _ _ Hk HSk) cs gs Hcs Hgs) as Hcok.
  set (sgs := set_constructor_arguments cs) in *.
  pose proof (set_group_ok_respects _ _ _ _ _ HG _ _ _ HSk Hcs) as Hrs. fold sgs in Hrs.
  pose proof (set_constructor_ok_shape _ _ _ _ _ _ _ _ Hcok) as Hsh.
  pose proof (arguments_fit_length _ _ _ _ _ _ Hfit) as Hlv.
  pose proof (set_arguments_shape_length _ _ Hsh) as Hlsh.
  pose proof (cons_lookup_in _ _ _ Hgs) as Hin.
  pose proof (decls_of_ctx _ _ _ HcΓ) as HDs.
  set (i0 := List.length gs1). set (pat := cargs_pat gs1). set (nn := im_nn Mk). set (na := List.length gs).
  assert (Hgi : List.nth_error gs i0 = Some (ca_rec t)) by (rewrite Egs, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
  destruct (set_arguments_shape_nth _ _ Hsh _ _ Hgi) as (sg & Hsg & Hsgk).
  destruct Hsgk as (Fr & ds & tparams & -> & Hlds).
  assert (Hi0 : i0 < na) by (unfold i0, na; rewrite Egs, List.length_app; cbn; lia).
  (* the environments of the parameters and of the arguments before *)
  set (ρn := set_env_extend_kinded ρ (ctx_kinds (im_nparams Mk)) (set_env_values (im_nparams Mk) θk)) in *.
  pose proof (nparams_env Γ ρ p D Us Fσ HΓ HcΓ Hρ HD Hσ k Mk SMk _ _ θk Hk HSk Hin Hθk Huni) as Hρn. fold ρn in Hρn.
  assert (Hlnp : List.length (ctx_kinds (im_nparams Mk)) = List.length (set_env_values (im_nparams Mk) θk))
    by (rewrite length_ctx_kinds, length_set_env_values; reflexivity).
  assert (Hdrop : forall x, set_env_drop (im_nn Mk) ρn x = ρ x).
  { intros x. unfold set_env_drop, ρn. unfold im_nn. rewrite <- length_ctx_kinds, Hlnp, set_env_extend_kinded_ge. reflexivity. }
  assert (Hvn : set_env_values (im_nparams Mk) ρn = set_env_values (im_nparams Mk) θk)
    by (unfold ρn; apply set_env_values_extend_kinded; rewrite length_set_env_values; reflexivity).
  assert (Hfit' : arguments_fit G U S (elim_uniform_values ρ D Fσ ++ set_env_values (im_nparams Mk) ρn) sgs vals)
    by (rewrite Hvn; exact Hfit).
  pose proof (args_env Γ ρ p D Us Fσ HΓ HcΓ Hρ HD Hσ U Hcar S points_in_fixed_point k Mk SMk cs gs ρn vals Hk HSk Hcs Hgs Hcok Hρn Hdrop Hfit'
                gs1 _ Egs) as Hρo.
  set (ρo := set_env_extend_kinded ρn (ctx_kinds (cargs_ctx p D Mk gs1)) (List.firstn i0 vals)) in *.
  destruct (List.nth_error_split vals i0 Hv) as (l1 & l2 & Evals & Hl1).
  fold i0 in Hρo. fold ρo in Hρo.
  assert (Hfst : List.firstn i0 vals = l1) by (rewrite Evals, <- Hl1, List.firstn_app, Nat.sub_diag, List.firstn_all; cbn; apply List.app_nil_r).
  assert (Hskp : List.skipn i0 vals = v :: l2) by (rewrite Evals, <- Hl1, List.skipn_app, Nat.sub_diag, List.skipn_all; reflexivity).
  assert (Hlk1 : List.length (ctx_kinds (cargs_ctx p D Mk gs1)) = List.length (List.firstn i0 vals))
    by (rewrite length_ctx_kinds, length_cargs_ctx, Hfst, Hl1; reflexivity).
  set (KS := ctx_kinds (cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) (ca_rec t :: gs2))).
  assert (Erest : forall z, set_env_extend_kinded ρn (ctx_kinds (cargs_ctx p D Mk gs)) vals z =
                            set_env_extend_kinded ρo KS (List.skipn i0 vals) z).
  { intros z. rewrite Egs at 1. rewrite cargs_ctx_app, ctx_kinds_app.
    rewrite <- (List.firstn_skipn i0 vals) at 1. rewrite set_env_extend_kinded_app by exact Hlk1. reflexivity. }
  assert (Hls : List.length (List.skipn i0 vals) = na - i0) by (rewrite List.length_skipn, Hlv, Hlsh; reflexivity).
  assert (F1 : forall z, ρe (List.length E + (na - i0 + z)) = ρo z).
  { intros z. rewrite Eρe, Erest, <- Hls, set_env_extend_kinded_ge. reflexivity. }
  assert (Hρo_drop : forall x, ρo (i0 + nn + x) = ρ x).
  { intros x. unfold ρo. replace (i0 + nn + x) with (List.length (List.firstn i0 vals) + (nn + x))
      by (rewrite Hfst, Hl1; lia). rewrite set_env_extend_kinded_ge. rewrite <- Hdrop. reflexivity. }
  (* the closed environment of the arguments before and the parameters *)
  set (Ψc := cargs_ctx p D Mk gs1 ++ im_nparams Mk) in *.
  assert (HΨc : List.length Ψc = i0 + nn) by (unfold Ψc; rewrite List.length_app, length_cargs_ctx; reflexivity).
  assert (EΨ : Ψc ++ ind_uparams D = cargs_ctx p D Mk gs1 ++ im_params D Mk) by (unfold Ψc, im_params; rewrite <- List.app_assoc; reflexivity).
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hgw HDs HD Hk Hin gs1 _ Egs) as (_ & HcN & Hφ).
  destruct (block_arg_closed k Mk SMk cs gs vals θk gs1 t gs2 v Hk HSk Hcs Hgs Hθk Huni Hfit Egs Hv) as [Hθa Hshape].
  fold i0 ρn ρo Ψc in Hθa, Hshape.
  set (θa := set_env_moved (List.length Ψc) Fσ ρo) in *.
  destruct (decl_shape_facts _ _ _ _ _ _ _ _ _ _ HDt Hk Hin Egs) as (Mt & HMt & HPlt & HBt & HPt).
  (* the walk *)
  destruct (rec_arg_inst _ _ _ _ _ _ _ _ _ _ _ _ _ E Hgw HDs HD Hk HcΓ HUl (set_gsub_typed _ _ _ _ _ _ Hσ) Hin Egs HcΨ)
    as (Hβt & Hσt & Huc & Hxt).
  destruct (rec_arg_inst_split Γ p D k Mk Us _ gs gs1 t gs2 E HD Hk HcΓ (set_gsub_typed _ _ _ _ _ _ Hσ) Hin Egs HcΨ) as [Hσat Eσ].
  set (m := List.length E + na + nn) in *.
  set (s := na - i0 + List.length E) in *.
  assert (Hw : gc_deps ⍮ gc_stack ⍮ E ++ con_inst_ctx Γ p D Mk Us gs ⊢ʷ wk_shiftn m : Γ).
  { pose proof HcΨ as HΨ. unfold con_inst_ctx in HΨ |- *. rewrite !List.app_assoc in HΨ |- *.
    replace m with (List.length ((E ++ tele_sub (cargs_ctx p D Mk gs) (sb_qn (im_nn Mk) (sb_of_list sb_id Us)))
                                   ++ tele_sub (im_nparams Mk) (sb_of_list sb_id Us)))
      by (rewrite !List.length_app, !length_tele_sub, length_cargs_ctx; unfold m, nn, na, im_nn; lia).
    apply wf_wk_shiftn_app'; exact HΨ. }
  assert (Hβ : forall y, sub_entry_agrees T γ (E ++ con_inst_ctx Γ p D Mk Us gs) ρe (sb_of_wk (wk_shiftn m) y) (ρ y)).
  { intros y. cbn [sb_of_wk wk_shiftn]. apply sub_agrees_var.
    replace (y + m) with (List.length E + (na - i0 + (i0 + nn + y))) by (unfold m; lia). rewrite F1. apply Hρo_drop. }
  assert (Hrz : shape_realized D us Mk (cargs_nonrec_ctx gs1) (cargs_ctx p D Mk gs1) (wk_pat pat) nil
                  (E ++ con_inst_ctx Γ p D Mk Us gs) ρe (ihs_sub nn Us na pat (List.length E))
                  (sb_compose (sb_qn (i0 + nn) (sb_of_list sb_id Us)) (sb_of_wk (wk_shiftn s))) θa).
  { constructor.
    - exact Hφ.
    - intros y. rewrite <- pat_nargs_cargs_pat. fold pat. rewrite wk_pat_ge. unfold pat. rewrite length_cargs_pat, length_cargs_ctx.
      reflexivity.
    - exact Hσat.
    - intros y. destruct (Nat.lt_ge_cases y (i0 + nn)) as [Hy | Hy].
      + cbn [sb_compose]. rewrite sb_qn_lt by exact Hy. cbn [sentry_sub sb_of_wk wk_shiftn]. apply sub_agrees_var.
        unfold θa, set_env_moved. rewrite set_env_above_lt' by (rewrite HΨc; exact Hy).
        replace (y + s) with (List.length E + (na - i0 + y)) by (unfold s; lia). apply F1.
      + cbn [sb_compose]. rewrite sb_qn_ge by exact Hy. rewrite sentry_sub_of_wk, sentry_wk_wk.
        rewrite (sentry_wk_wk_eq _ _ (wk_shiftn m)) by (intros z; cbn; unfold m, s; lia).
        rewrite <- sentry_sub_of_wk.
        unfold θa, set_env_moved. replace y with (List.length Ψc + (y - (i0 + nn))) at 2 by (rewrite HΨc; lia).
        rewrite set_env_above_ge'.
        apply (sub_agrees_wk _ Γ (set_env_drop (List.length Ψc) ρo) ρe (wk_shiftn m) _ _ Hw).
        * intros x. unfold set_env_drop. cbn. rewrite HΨc.
          replace (x + m) with (List.length E + (na - i0 + (i0 + nn + x))) by (unfold m; lia). rewrite F1. reflexivity.
        * exact (set_gsub_agrees _ _ _ _ _ _ Hσ _ _ (set_env_in_drop T γ _ _ _ _ Hρo)).
    - exact Eσ.
    - change (shape_read_ctx D Mk (cargs_ctx p D Mk gs1) (wk_pat pat) nil) with (cargs_ctx p D Mk gs1 ++ im_params D Mk). exact Hθa.
    - cbn [List.length]. rewrite length_cargs_ctx. fold i0. fold nn.
      rewrite (set_env_values_agree _ _ (Fσ (set_env_drop (List.length Ψc) ρo))).
      + apply (inst_uniform_values Γ ρ D Us Fσ HcΓ Hρ Hσ). intros x. unfold set_env_drop. rewrite HΨc. apply Hρo_drop.
      + intros x _. unfold set_env_drop at 1, θa, set_env_moved.
        match goal with |- set_env_above _ _ _ (?a + x) = _ =>
          replace a with (List.length Ψc) by (rewrite HΨc; unfold i0, nn; lia) end.
        rewrite set_env_above_ge'. reflexivity. }
  assert (Hx : set_interp T γ (E ++ con_inst_ctx Γ p D Mk Us gs) ρe (a_var (List.length E + na - 1 - List.length pat)) v).
  { replace v with (set_entry_value (ρe (List.length E + na - 1 - List.length pat))); [apply set_interp_var |].
    unfold pat. rewrite length_cargs_pat. fold i0.
    replace (List.length E + na - 1 - i0) with (List.length E + (List.length l2 + 0)) by (rewrite Hskp in Hls; cbn in Hls; lia).
    rewrite Eρe, Erest, Hskp. cbn [set_env_extend_kinded]. rewrite set_env_extend_kinded_ge. reflexivity. }
  assert (Hl' : In l (shape_leaves (rview_leaves D) (List.length (@nil exp) + List.length (cargs_nonrec_ctx gs1) + im_nn Mk) t))
    by (cbn [List.length]; rewrite <- pat_nargs_cargs_pat; exact Hl).
  pose proof (shape_leaf_sem Γ ρ r p Us Bks V D i HMwf HDt Hcl HUl HMh HBk us (rview_fits Γ ρ r p Us Bks V D us)
                (rview_fits_at_end Γ ρ r p Us Bks V D i HMot HDt Hcl HUl us) t Mk nil (cargs_nonrec_ctx gs1)
                (cargs_ctx p D Mk gs1) (wk_pat pat) _ ρe _ _ _ _ v θa Mt HcΨ Hρe Hβ Hβt Hσt HcN Huc Hrz Hx Hxt HMt HPlt HBt HPt
                Hshape l Hl') as Hsem.
  exact (leaf_fit Γ ρ r p Us Bks V D i HMwf HMot l _ ρe _ _ _ v A HcΨ Hρe Hβ Hx Hsem HA).
Qed.

(** The recursive results of the arguments [vs] of the kinds [gs], after
    arguments told by [pat]: along each leaf path of each recursive one. *)
Fixpoint ihs_values (nn : nat) (pat : list bool) (gs : list carg) (vs : list aczel_set) : list aczel_set :=
  match gs, vs with
  | ca_arg _ _ :: gs', _ :: vs' => ihs_values nn (false :: pat) gs' vs'
  | ca_rec t :: gs', v :: vs' =>
      List.map (fun l => leaf_value Γ ρ r p Us Bks V l v) (shape_leaves (rview_leaves D) (pat_nargs pat + nn) t) ++
      ihs_values nn (true :: pat) gs' vs'
  | _, _ => nil
  end.

(** The results of one recursive argument along some of its paths extend
    an environment of the branch's context above them. *)
Lemma leaves_env : forall k Mk SMk cs gs vals θk gs1 t gs2 v,
    ind_member D k = Some Mk -> List.nth_error (set_group_members G) k = Some SMk -> In cs (set_member_constructors SMk) ->
    ind_con Mk (set_constructor_name cs) = Some gs ->
    set_env_in T γ (im_params D Mk) θk -> list_set_eq (uniform_values D Mk θk) us ->
    arguments_fit G U S (us ++ set_env_values (im_nparams Mk) θk) (set_constructor_arguments cs) vals ->
    gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error vals (List.length gs1) = Some v ->
    forall ls, List.incl ls (shape_leaves (rview_leaves D) (pat_nargs (cargs_pat gs1) + im_nn Mk) t) ->
    forall E ρe,
    set_ctx T γ (leaves_ctx r (im_nn Mk) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) (List.length E) ls ++
                 E ++ con_inst_ctx Γ p D Mk Us gs) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ leaves_ctx r (im_nn Mk) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) (List.length E) ls ++
                 E ++ con_inst_ctx Γ p D Mk Us gs ->
    set_env_in T γ (E ++ con_inst_ctx Γ p D Mk Us gs) ρe ->
    (forall z, ρe (List.length E + z) =
       set_env_extend_kinded (set_env_extend_kinded ρ (ctx_kinds (im_nparams Mk)) (set_env_values (im_nparams Mk) θk))
         (ctx_kinds (cargs_ctx p D Mk gs)) vals z) ->
    set_env_in T γ (leaves_ctx r (im_nn Mk) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) (List.length E) ls ++
                    E ++ con_inst_ctx Γ p D Mk Us gs)
      (set_env_extend_kinded ρe
         (ctx_kinds (leaves_ctx r (im_nn Mk) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) (List.length E) ls))
         (List.map (fun l => leaf_value Γ ρ r p Us Bks V l v) ls)).
Proof.
  intros k Mk SMk cs gs vals θk gs1 t gs2 v Hk HSk Hcs Hgs Hθk Huni Hfit Egs Hv.
  induction ls as [| l ls IH]; intros Hincl E ρe HC Hc Hρe Eρe; [exact Hρe |].
  cbn [leaves_ctx List.map] in HC, Hc |- *.
  rewrite ctx_kinds_app. cbn [ctx_kinds List.map List.rev List.app centry_kind set_env_extend_kinded List.hd List.tl].
  set (ty := leaf_ihty r (blocks_motives Bks) (sb_of_wk (wk_shiftn (List.length E + List.length gs + im_nn Mk)))
               (ihs_sub (im_nn Mk) Us (List.length gs) (cargs_pat gs1) (List.length E))
               (a_var (List.length E + List.length gs - 1 - List.length (cargs_pat gs1))) l) in *.
  rewrite <- List.app_assoc in HC, Hc |- *. cbn [List.app] in HC, Hc |- *.
  change (ce_ass r ty :: E ++ con_inst_ctx Γ p D Mk Us gs) with ((ce_ass r ty :: E) ++ con_inst_ctx Γ p D Mk Us gs) in HC, Hc |- *.
  assert (HE' : set_env_in T γ ((ce_ass r ty :: E) ++ con_inst_ctx Γ p D Mk Us gs)
                  (set_env_extend ρe (set_entry_term r (leaf_value Γ ρ r p Us Bks V l v)))).
  { pose proof (set_ctx_app_r T γ _ _ HC) as HC1. destruct HC1 as [_ [FA HFA]].
    pose proof (ctx_app_wf_tail _ _ _ _ Hc) as Hc1. pose proof (ctx_decomp_tail Hc1) as Hc2.
    split; [exact Hρe |]. cbn [set_entry_rel]. exists (leaf_value Γ ρ r p Us Bks V l v), (leaf_value Γ ρ r p Us Bks V l v), (FA ρe).
    constructor; [reflexivity | reflexivity | exact (set_denotes_exists _ _ _ _ _ HFA _ Hρe) | | apply set_eq_refl].
    exact (block_arg_fits k Mk SMk cs gs vals θk E ρe gs1 t gs2 v Hk HSk Hcs Hgs Hθk Huni Hfit Hc2 Hρe Eρe Egs Hv l
             (Hincl l (or_introl eq_refl)) _ (set_denotes_exists _ _ _ _ _ HFA _ Hρe)). }
  replace (Datatypes.S (List.length E)) with (List.length (ce_ass r ty :: E)) in HC, Hc |- * by reflexivity.
  apply (IH (fun x Hx => Hincl x (or_intror Hx)) _ _ HC Hc HE').
  intros z. cbn [List.length]. exact (Eρe z).
Qed.

(** The results of the arguments after [gs1] extend an environment of
    the branch's context above them. *)
Lemma ihs_env : forall k Mk SMk cs gs vals θk,
    ind_member D k = Some Mk -> List.nth_error (set_group_members G) k = Some SMk -> In cs (set_member_constructors SMk) ->
    ind_con Mk (set_constructor_name cs) = Some gs ->
    set_env_in T γ (im_params D Mk) θk -> list_set_eq (uniform_values D Mk θk) us ->
    arguments_fit G U S (us ++ set_env_values (im_nparams Mk) θk) (set_constructor_arguments cs) vals ->
    forall gs2 gs1 E ρe, gs = gs1 ++ gs2 ->
    set_ctx T γ (ihs_ctx_aux r (rview_leaves D) (im_nn Mk) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) (List.length E) gs2 ++
                 E ++ con_inst_ctx Γ p D Mk Us gs) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ ihs_ctx_aux r (rview_leaves D) (im_nn Mk) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1)
                 (List.length E) gs2 ++ E ++ con_inst_ctx Γ p D Mk Us gs ->
    set_env_in T γ (E ++ con_inst_ctx Γ p D Mk Us gs) ρe ->
    (forall z, ρe (List.length E + z) =
       set_env_extend_kinded (set_env_extend_kinded ρ (ctx_kinds (im_nparams Mk)) (set_env_values (im_nparams Mk) θk))
         (ctx_kinds (cargs_ctx p D Mk gs)) vals z) ->
    set_env_in T γ (ihs_ctx_aux r (rview_leaves D) (im_nn Mk) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) (List.length E) gs2 ++
                    E ++ con_inst_ctx Γ p D Mk Us gs)
      (set_env_extend_kinded ρe
         (ctx_kinds (ihs_ctx_aux r (rview_leaves D) (im_nn Mk) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) (List.length E) gs2))
         (ihs_values (im_nn Mk) (cargs_pat gs1) gs2 (List.skipn (List.length gs1) vals))).
Proof.
  intros k Mk SMk cs gs vals θk Hk HSk Hcs Hgs Hθk Huni Hfit.
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG.
  pose proof (set_member_ok_constructors _ _ _ _ _ _ _ (set_group_ok_members _ _ _ _ _ HG _ _ _ Hk HSk) cs gs Hcs Hgs) as Hcok.
  pose proof (arguments_fit_length _ _ _ _ _ _ Hfit) as Hlv.
  pose proof (set_arguments_shape_length _ _ (set_constructor_ok_shape _ _ _ _ _ _ _ _ Hcok)) as Hlsh.
  induction gs2 as [| g gs2 IH]; intros gs1 E ρe Egs HC Hc Hρe Eρe.
  - cbn [ihs_ctx_aux]. destruct (List.skipn (List.length gs1) vals); exact Hρe.
  - assert (Hlt : List.length gs1 < List.length vals) by (rewrite Hlv, Hlsh, Egs, List.length_app; cbn; lia).
    destruct (List.nth_error vals (List.length gs1)) as [v |] eqn:Hv; [| apply List.nth_error_None in Hv; lia].
    destruct (List.nth_error_split vals _ Hv) as (l1 & l2 & Evals & Hl1).
    assert (Hskp : List.skipn (List.length gs1) vals = v :: l2)
      by (rewrite Evals, <- Hl1, List.skipn_app, Nat.sub_diag, List.skipn_all; reflexivity).
    assert (Hskp' : List.skipn (List.length (gs1 ++ [g])) vals = l2)
      by (rewrite Evals, List.length_app, <- Hl1, List.skipn_app; cbn [List.length];
          replace (List.length l1 + 1 - List.length l1) with 1 by lia; rewrite List.skipn_all2 by lia; reflexivity).
    assert (Egs' : gs = (gs1 ++ [g]) ++ gs2) by (rewrite Egs, <- List.app_assoc; reflexivity).
    rewrite Hskp. destruct g as [κ A | t].
    + cbn [ihs_ctx_aux ihs_values] in HC, Hc |- *.
      replace (false :: cargs_pat gs1) with (cargs_pat (gs1 ++ [ca_arg κ A])) in HC, Hc |- * by (rewrite cargs_pat_snoc; reflexivity).
      rewrite <- Hskp'. exact (IH _ _ _ Egs' HC Hc Hρe Eρe).
    + cbn [ihs_ctx_aux ihs_values] in HC, Hc |- *.
      set (ls := shape_leaves (rview_leaves D) (pat_nargs (cargs_pat gs1) + im_nn Mk) t) in *.
      set (LC := leaves_ctx r (im_nn Mk) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) (List.length E) ls) in *.
      rewrite <- List.app_assoc in HC, Hc |- *.
      rewrite ctx_kinds_app.
      assert (Hlk : List.length (ctx_kinds LC) = List.length (List.map (fun l => leaf_value Γ ρ r p Us Bks V l v) ls))
        by (unfold LC; rewrite length_ctx_kinds, length_leaves_ctx, List.length_map; reflexivity).
      rewrite set_env_extend_kinded_app by exact Hlk.
      pose proof (leaves_env k Mk SMk cs gs vals θk gs1 t gs2 v Hk HSk Hcs Hgs Hθk Huni Hfit Egs Hv ls (List.incl_refl _) E ρe
                    (set_ctx_app_r T γ _ _ HC) (ctx_app_wf_tail _ _ _ _ Hc) Hρe Eρe) as HL.
      fold LC in HL.
      replace (true :: cargs_pat gs1) with (cargs_pat (gs1 ++ [ca_rec t])) in HC, Hc |- * by (rewrite cargs_pat_snoc; reflexivity).
      replace (List.length ls + List.length E) with (List.length (LC ++ E)) in HC, Hc |- *
        by (unfold LC; rewrite List.length_app, length_leaves_ctx; reflexivity).
      rewrite (List.app_assoc LC E (con_inst_ctx Γ p D Mk Us gs)) in HC, Hc |- *.
      rewrite <- Hskp'.
      apply (IH _ _ _ Egs' HC Hc); [rewrite <- List.app_assoc; exact HL |].
      intros z. rewrite List.length_app, <- Nat.add_assoc.
      replace (List.length LC) with (List.length (List.map (fun l => leaf_value Γ ρ r p Us Bks V l v) ls))
        by (rewrite <- Hlk, length_ctx_kinds; reflexivity).
      rewrite set_env_extend_kinded_ge. exact (Eρe z).
Qed.

(** Into a sort of relevant terms, the arguments after [gs1] have their
    results. *)
Lemma block_ihs : r <> ak_propositional -> forall k Mk SMk cs gs vals θk,
    ind_member D k = Some Mk -> List.nth_error (set_group_members G) k = Some SMk -> In cs (set_member_constructors SMk) ->
    ind_con Mk (set_constructor_name cs) = Some gs ->
    set_env_in T γ (im_params D Mk) θk -> list_set_eq (uniform_values D Mk θk) us ->
    arguments_fit G U S (us ++ set_env_values (im_nparams Mk) θk) (set_constructor_arguments cs) vals ->
    forall gs2 gs1, gs = gs1 ++ gs2 ->
    set_ihs T γ Γ ρ r p Us Bks gs2 (List.skipn (List.length gs1) vals)
      (ihs_values (im_nn Mk) (cargs_pat gs1) gs2 (List.skipn (List.length gs1) vals)).
Proof.
  intros Hr k Mk SMk cs gs vals θk Hk HSk Hcs Hgs Hθk Huni Hfit.
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG.
  pose proof (set_member_ok_constructors _ _ _ _ _ _ _ (set_group_ok_members _ _ _ _ _ HG _ _ _ Hk HSk) cs gs Hcs Hgs) as Hcok.
  pose proof (arguments_fit_length _ _ _ _ _ _ Hfit) as Hlv.
  pose proof (set_arguments_shape_length _ _ (set_constructor_ok_shape _ _ _ _ _ _ _ _ Hcok)) as Hlsh.
  pose proof (leaves_coherent_of_order _ (rview_struct_order _ _ _ (decl_typed_record_struct _ _ _ HDt))) as Hco.
  assert (Hlvr : forall l x, leaf_value Γ ρ r p Us Bks V l x = leaf_result Γ ρ r p Us Bks V l x)
    by (intros; unfold leaf_value; destruct r; [reflexivity | contradiction | reflexivity]).
  induction gs2 as [| g gs2 IH]; intros gs1 Egs.
  - rewrite List.skipn_all2 by (rewrite Hlv, Hlsh, Egs, List.app_nil_r; lia). constructor.
  - assert (Hlt : List.length gs1 < List.length vals) by (rewrite Hlv, Hlsh, Egs, List.length_app; cbn; lia).
    destruct (List.nth_error vals (List.length gs1)) as [v |] eqn:Hv; [| apply List.nth_error_None in Hv; lia].
    destruct (List.nth_error_split vals _ Hv) as (l1 & l2 & Evals & Hl1).
    assert (Hskp : List.skipn (List.length gs1) vals = v :: l2)
      by (rewrite Evals, <- Hl1, List.skipn_app, Nat.sub_diag, List.skipn_all; reflexivity).
    assert (Hskp' : List.skipn (List.length (gs1 ++ [g])) vals = l2)
      by (rewrite Evals, List.length_app, <- Hl1, List.skipn_app; cbn [List.length];
          replace (List.length l1 + 1 - List.length l1) with 1 by lia; rewrite List.skipn_all2 by lia; reflexivity).
    assert (Egs' : gs = (gs1 ++ [g]) ++ gs2) by (rewrite Egs, <- List.app_assoc; reflexivity).
    rewrite Hskp. destruct g as [κ A | t]; cbn [ihs_values].
    + constructor. replace (false :: cargs_pat gs1) with (cargs_pat (gs1 ++ [ca_arg κ A])) by (rewrite cargs_pat_snoc; reflexivity).
      rewrite <- Hskp'. exact (IH _ Egs').
    + constructor.
      * erewrite List.map_ext by (intros l; apply Hlvr).
        destruct (block_arg_closed k Mk SMk cs gs vals θk gs1 t gs2 v Hk HSk Hcs Hgs Hθk Huni Hfit Egs Hv) as [_ Hcok'].
        apply (set_ih_of_shape_results Γ ρ r p Us Bks V Hρ D HD Hco HDt).
        exact (shape_results_of_closed_ok Γ ρ r p Us Bks V D i Hr _ _ _ _ _ _ _ _ Hcok').
      * replace (true :: cargs_pat gs1) with (cargs_pat (gs1 ++ [ca_rec t])) by (rewrite cargs_pat_snoc; reflexivity).
        rewrite <- Hskp'. exact (IH _ Egs').
Qed.

(** One recursive result per leaf path of each recursive argument. *)
Lemma length_ihs_values : forall nn pat gs vs, List.length vs = List.length gs -> List.length (ihs_values nn pat gs vs) = cargs_nrec D gs.
Proof.
  intros nn pat gs. revert pat. induction gs as [| [κ A | t] gs IH]; intros pat [| v vs] Hl; cbn in Hl |- *; try lia.
  - apply IH. lia.
  - rewrite List.length_app, List.length_map, IH by lia. rewrite (length_shape_leaves _ _ _ 0). reflexivity.
Qed.

(** [view_instance_with Mk Is ρu is]: the instance [Is] of the view [Mk]
    reads [is] in the declaration at [ρu], an environment of the uniform
    parameters holding the uniform values, and at the uniform parameters
    [Us] at [ρ]. *)
Record view_instance_with (Mk : imember) (Is : list exp) (ρu : set_env) (is : list aczel_set) : Prop :=
  { (** [ρu] is an environment of the uniform parameters *)
    view_instance_env : set_env_in T γ (ind_uparams D) ρu
    (** holding the uniform values *)
  ; view_instance_uniform : set_env_values (ind_uparams D) ρu = us
    (** The instance reads [is] there *)
  ; view_instance_closed : set_interp_list T γ (ind_uparams D) ρu Is is
    (** The instance at [Us] reads [is] at [ρ] *)
  ; view_instance_open : set_interp_list T γ Γ ρ (im_pre Mk Us) is }.

(** A view's instance at the uniform parameters [Us] reads, at [ρ], the
    values the instance has in the declaration at an environment of the
    uniform parameters holding the uniform values. *)
Lemma view_instance_values : forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
    exists ρu is, view_instance_with Mk Is ρu is.
Proof.
  intros k Mk qc k' Is vm Hk Hh.
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG.
  pose proof (set_ctx_of_tele_types T γ Hfn Hmods _ _ _ (set_group_ok_uniform _ _ _ _ _ HG) I) as HU. rewrite List.app_nil_r in HU.
  pose proof (decl_closed_uparams _ Hcl) as Hs. pose proof (decl_closed_ass _ Hcl) as Hass.
  destruct (decl_typed_uparams _ _ _ HDt) as [Hw _].
  pose proof (wf_ctx_closed_app _ _ _ _ Hass Hs Hw HcΓ) as HwΓ.
  assert (HUΓ : set_ctx T γ (ind_uparams D ++ Γ)).
  { pose proof (set_ctx_moved T γ Hfn Hmods _ nil Γ _ _ (set_gsub_drop T γ _ HcΓ) HΓ ltac:(rewrite List.app_nil_r; exact HU)
                  ltac:(rewrite List.app_nil_r; exact Hw)) as H.
    rewrite tele_sub_closed in H by exact Hs. exact H. }
  destruct (inst_closed_env_in Γ (ind_uparams D) _ Fσ Hσ HΓ HcΓ nil ρ Hs HU HUΓ Hw HwΓ Hρ) as [Hm Hinst].
  set (ρu := inst_closed_env Γ (ind_uparams D) Fσ nil ρ) in *.
  destruct (set_group_ok_view_instances _ _ _ _ _ HG k Mk qc k' Is vm ρu Hk Hh Hinst) as [is His].
  exists ρu, is. constructor; [exact Hinst | | exact His |].
  { unfold ρu. pose proof (inst_closed_env_values Γ (ind_uparams D) Fσ nil ρ) as E. cbn [List.app] in E.
    rewrite E, List.app_nil_r. reflexivity. }
  (* the instance read below [Γ], then substituted by [Us] *)
  pose proof (decl_closed_head_scoped _ Hcl _ _ _ _ _ _ Hk Hh) as HIs.
  set (ρm := set_env_moved 0 Fσ ρ) in *. cbn [List.app List.length] in Hm. fold ρm in Hm.
  assert (Hw0 : gc_deps ⍮ gc_stack ⍮ Γ ⊢ʷ wk_shiftn (List.length Γ) : nil).
  { pose proof (wf_wk_shiftn_app' _ _ Γ nil ltac:(rewrite List.app_nil_r; exact HcΓ)) as H. rewrite List.app_nil_r in H. exact H. }
  assert (Hag : env_agrees ρu ρm (wk_qn (List.length (ind_uparams D)) (wk_shiftn (List.length Γ)))).
  { intros x. destruct (Nat.lt_ge_cases x (List.length (ind_uparams D))) as [Hx | Hx].
    - rewrite wk_qn_lt by exact Hx. unfold ρu, inst_closed_env. unfold set_env_moved at 1.
      rewrite set_env_above_lt' by (cbn; exact Hx). reflexivity.
    - rewrite wk_qn_ge by exact Hx. unfold ρu, inst_closed_env. unfold set_env_moved at 1. cbn [List.app].
      replace x with (List.length (ind_uparams D) + (x - List.length (ind_uparams D))) at 1 by lia.
      rewrite set_env_above_ge'. unfold set_env_drop. cbn [wk_shiftn].
      change (set_env_moved (List.length (@nil centry)) Fσ ρ) with ρm. f_equal. lia. }
  assert (HI0 : set_interp_list T γ (ind_uparams D ++ nil) ρu Is is) by (rewrite List.app_nil_r; exact His).
  pose proof (proj1 (proj2 (set_interp_wk_all T γ)) _ _ _ _ HI0 (ind_uparams D) nil Γ _ ρm
                (Build_wk_setting _ _ _ _ _ _ _ eq_refl Hw0 Hag)) as H1.
  rewrite tele_closed_wk in H1 by exact Hs.
  rewrite (List.map_ext_in _ (fun M => M)) in H1.
  2:{ intros I HI. apply (proj1 syn_scoped_wk_id I (ind_nu D)); [exact (proj1 (List.Forall_forall _ _) HIs I HI) |].
      intros y Hy. apply wk_qn_lt. exact Hy. }
  rewrite List.map_id in H1.
  pose proof (set_sub_setting_moved T γ nil (ind_uparams D ++ Γ) Γ _ Fσ ρ Hσ Hρ) as Hset.
  pose proof (proj1 (proj2 (set_interp_sub_all T γ)) _ _ _ _ H1 _ _ _ _ _ _ HwΓ Hset) as H2.
  cbn [tele_sub List.app] in H2. unfold im_pre. rewrite Hh. exact H2.
Qed.

(** Applying to two lists in turn. *)
Lemma apply_values_app : forall f vs1 vs2, apply_values f (vs1 ++ vs2) = apply_values (apply_values f vs1) vs2.
Proof. intros. unfold apply_values. apply List.fold_left_app. Qed.

(** The uniform arguments of a member that is not a record view, at the
    uniform parameters [Us]: their values, at which its reference's type
    former and constructors are the member's own at the uniform values. *)
Record member_pre_with (k : nat) (Mk : imember) (pre : list aczel_set) : Prop :=
  { (** The uniform arguments read [pre] *)
    member_pre_interp : set_interp_list T γ Γ ρ (im_pre Mk Us) pre
    (** The reference's type former at them is the member's *)
  ; member_pre_former : set_eq (apply_values (global_former γ (fst (im_ref p k Mk)) (snd (im_ref p k Mk))) pre)
                               (apply_values (global_former γ p k) us)
    (** So are its constructors *)
  ; member_pre_constructors : forall c gs, ind_con Mk c = Some gs ->
      set_eq (apply_values (global_constructor γ (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c) pre)
             (apply_values (global_constructor γ p k c) us) }.

(** Every member that is not a record view has its uniform arguments'
    values: the uniform values at a declared member, the instance's
    reading at a view. *)
Lemma member_pre_values : forall k Mk, ind_member D k = Some Mk -> im_is_rview Mk = false -> exists pre, member_pre_with k Mk pre.
Proof.
  intros k Mk Hk Hr. pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG.
  unfold im_is_rview in Hr. destruct (im_head Mk) as [pm | qc k' Is vm | qr Is fl] eqn:Hh; try discriminate.
  - exists us. constructor; unfold im_pre, im_ref; rewrite Hh; cbn [fst snd].
    + exact uniform_interp_list.
    + apply set_eq_refl.
    + intros; apply set_eq_refl.
  - destruct (view_instance_values k Mk qc k' Is vm Hk Hh) as (ρu & is & [Hρu Eu HIs Hpre]).
    exists is. constructor; unfold im_ref; rewrite ?Hh; cbn [fst snd].
    + exact Hpre.
    + rewrite <- Eu. apply set_eq_sym. exact (set_group_ok_view_formers _ _ _ _ _ HG k Mk qc k' Is vm ρu is Hk Hh Hρu HIs).
    + intros c gs Hgs. rewrite <- Eu. apply set_eq_sym.
      exact (set_group_ok_view_constructors _ _ _ _ _ HG k Mk qc k' Is vm c gs ρu is Hk Hh Hgs Hρu HIs).
Qed.

(** The uniform arguments moved below an extension [Ψ] of [Γ] read the
    same values at an environment holding [ρ] below [Ψ]. *)
Lemma member_pre_wk : forall k Mk pre Ψ ρ', ind_member D k = Some Mk -> set_interp_list T γ Γ ρ (im_pre Mk Us) pre ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ -> (forall x, ρ' (List.length Ψ + x) = ρ x) ->
    set_interp_list T γ (Ψ ++ Γ) ρ' (im_pre Mk (List.map (fun U => exp_wk U (wk_shiftn (List.length Ψ))) Us)) pre.
Proof.
  intros k Mk pre Ψ ρ' Hk H Hc Hag.
  assert (Hw : gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ ⊢ʷ wk_shiftn (List.length Ψ) : Γ) by (apply wf_wk_shiftn_app'; exact Hc).
  assert (Hag' : env_agrees ρ ρ' (wk_qn (List.length (@nil centry)) (wk_shiftn (List.length Ψ)))).
  { intros x. cbn [List.length wk_qn wk_shiftn]. rewrite Nat.add_comm, Hag. reflexivity. }
  pose proof (proj1 (proj2 (set_interp_wk_all T γ)) _ _ _ _ H nil Γ _ _ _ (Build_wk_setting _ _ _ _ _ _ _ eq_refl Hw Hag')) as H'.
  cbn [tele_wk List.app List.length wk_qn] in H'. rewrite (im_pre_wk D k Mk Us _ Hcl Hk HUl) in H'. exact H'.
Qed.

(** A member that is not a record view has the inductive type of its
    reference for type. *)
Lemma im_ty_at_not_rview : forall pq k M Us0 Ns, im_is_rview M = false ->
    im_ty_at pq k M Us0 Ns = apps_exp (a_ind (fst (im_ref pq k M)) (snd (im_ref pq k M))) (im_pre M Us0 ++ Ns).
Proof. intros * Hr. unfold im_is_rview in Hr. unfold im_ty_at. destruct (im_head M); [reflexivity | reflexivity | discriminate]. Qed.

(** At a member that is not a record view, the member's type at the
    instance read at its parameters' values is a code of the member's
    carrier there. *)
Lemma block_mty_value : forall k Mk θk, ind_member D k = Some Mk -> im_is_rview Mk = false ->
    set_env_in T γ (im_params D Mk) θk -> list_set_eq (uniform_values D Mk θk) us ->
    exists a, set_interp T γ (tele_sub (im_nparams Mk) (sb_of_list sb_id Us) ++ Γ)
                (set_env_extend_kinded ρ (ctx_kinds (im_nparams Mk)) (set_env_values (im_nparams Mk) θk))
                (ind_mty p D k (List.map (fun U => exp_wk U (wk_shiftn (im_nn Mk))) Us) (vars_from 0 (im_nn Mk))) a /\
              set_eq (code_carrier a) (member_carrier G us U U k (set_env_values (im_nparams Mk) θk)).
Proof.
  intros k Mk θk Hk Hr Hθk Huni.
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG. fold G in HG.
  destruct (member_pre_values k Mk Hk Hr) as [pre Hpre].
  set (ns0 := set_env_values (im_nparams Mk) θk).
  set (ρn := set_env_extend_kinded ρ (ctx_kinds (im_nparams Mk)) ns0).
  assert (Hlns : List.length ns0 = im_nn Mk) by (unfold ns0, im_nn; rewrite length_set_env_values; reflexivity).
  exists (apply_values (global_former γ (fst (im_ref p k Mk)) (snd (im_ref p k Mk))) (pre ++ ns0)). split.
  - unfold ind_mty. rewrite Hk, (im_ty_at_not_rview _ _ _ _ _ Hr).
    apply set_interp_apps; [apply set_interp_indty |]. apply set_interp_list_app.
    + pose proof (HMwf _ _ Hk) as Hwm. unfold elim_mctx in Hwm. pose proof (ctx_decomp_tail Hwm) as Hwn.
      pose proof (member_pre_wk k Mk pre _ ρn Hk (member_pre_interp _ _ _ Hpre) Hwn) as H.
      rewrite length_tele_sub in H. change (List.length (im_nparams Mk)) with (im_nn Mk) in H. apply H.
      intros x. unfold ρn. rewrite <- Hlns. apply set_env_extend_kinded_ge.
    + rewrite <- Hlns. unfold ρn. rewrite <- (List.app_nil_r ns0) at 1. exact (set_interp_list_vars_from _ ns0 nil ρ _).
  - pose proof (set_group_ok_formers_value _ _ _ _ _ HG k Mk θk Hk Hθk) as Ef.
    eapply set_eq_trans; [apply code_carrier_resp; apply (set_eq_trans _ (apply_values (global_former γ p k) (us ++ ns0)));
                          [| eapply set_eq_trans; [| exact Ef]] |].
    + rewrite !apply_values_app. apply apply_values_resp; [exact (member_pre_former _ _ _ Hpre) | apply list_set_eq_refl].
    + apply apply_values_resp; [apply set_eq_refl |]. unfold im_params. rewrite set_env_values_app. apply list_set_eq_app.
      * apply list_set_eq_sym. exact Huni.
      * apply list_set_eq_refl.
    + unfold inductive_code. eapply set_eq_trans; [apply code_carrier_type_code |].
      unfold us in Huni |- *. exact (Hcar k Mk θk Hk Hθk Huni).
Qed.

(** At a member that is not a record view, its constructor at the
    uniform values, the parameters' values and arguments fitting the
    carriers is the element of its name. *)
Lemma block_con_value : forall k Mk SMk cs gs vals θk, ind_member D k = Some Mk -> im_is_rview Mk = false ->
    List.nth_error (set_group_members G) k = Some SMk -> In cs (set_member_constructors SMk) ->
    ind_con Mk (set_constructor_name cs) = Some gs ->
    set_env_in T γ (im_params D Mk) θk -> list_set_eq (uniform_values D Mk θk) us ->
    arguments_fit G U S (us ++ set_env_values (im_nparams Mk) θk) (set_constructor_arguments cs) vals ->
    set_eq (apply_values (global_constructor γ p k (set_constructor_name cs)) (us ++ set_env_values (im_nparams Mk) θk ++ vals))
           (con_val (set_constructor_name cs) (set_env_values (im_nparams Mk) θk ++ vals)).
Proof.
  intros k Mk SMk cs gs vals θk Hk Hr HSk Hcs Hgs Hθk Huni Hfit.
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG. fold G in HG.
  pose proof (set_member_ok_constructors _ _ _ _ _ _ _ (set_group_ok_members _ _ _ _ _ HG _ _ _ Hk HSk) cs gs Hcs Hgs) as Hcok.
  pose proof (arguments_fit_length _ _ _ _ _ _ Hfit) as Hlv.
  pose proof (set_arguments_shape_length _ _ (set_constructor_ok_shape _ _ _ _ _ _ _ _ Hcok)) as Hlsh.
  destruct (block_args_env_closed k Mk SMk cs gs vals θk gs nil Hk HSk Hcs Hgs Hθk Huni Hfit (eq_sym (List.app_nil_r gs)))
    as [Hθc HLθ].
  set (θc := set_env_moved _ Fσ _) in *.
  rewrite List.firstn_all2 in HLθ by lia.
  pose proof (set_group_ok_constructors_value _ _ _ _ _ HG k Mk _ gs θc Hk Hgs Hθc) as Ec.
  assert (Hce : forall c0 vs, member_constructor_element Mk c0 vs = con_val c0 vs)
    by (intros; unfold im_is_rview in Hr; unfold member_constructor_element; destruct (im_head Mk); [reflexivity | reflexivity | discriminate]).
  rewrite Hce in Ec.
  assert (Hnu : List.length us = ind_nu D) by (unfold us, elim_uniform_values; rewrite length_set_env_values; reflexivity).
  eapply set_eq_trans; [| eapply set_eq_trans; [exact Ec |]].
  - apply apply_values_resp; [apply set_eq_refl |]. rewrite List.app_assoc. apply list_set_eq_sym. exact HLθ.
  - unfold con_val. apply ordered_pair_resp; [apply set_eq_refl |]. apply list_code_resp.
    eapply list_set_eq_trans; [apply list_set_eq_skipn; exact HLθ |].
    rewrite <- List.app_assoc, List.skipn_app, Hnu, Nat.sub_diag, List.skipn_all2 by lia. apply list_set_eq_refl.
Qed.

(** A branch's type, at an environment of the branch's context, is the
    motive at the parameters' values and the constructor's value. *)
Lemma block_branch_motive : forall k Mk c gs b FSm FM FM' ns0 vals ihv cv,
    ind_member D k = Some Mk -> im_is_rview Mk = false -> ind_con Mk c = Some gs -> List.nth_error Bks k = Some b ->
    set_exp_eq_with T γ (elim_mctx p D k Mk Us ++ Γ) (abs_kind_sort r (a_typ i)) (eb_motive b) (eb_motive b) FSm FM FM' ->
    List.length ns0 = im_nn Mk -> List.length vals = List.length gs -> List.length ihv = cargs_nrec D gs ->
    set_env_in T γ (elim_mctx p D k Mk Us ++ Γ) (set_env_extend_kinded ρ (ctx_kinds (elim_mctx p D k Mk Us)) (ns0 ++ [cv])) ->
    set_interp T γ (elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ)
      (set_env_extend_kinded ρ (ctx_kinds (elim_bctx r p D Mk gs (blocks_motives Bks) Us)) (ns0 ++ vals ++ ihv))
      (apps_exp (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c)
         (im_pre Mk (List.map (fun U => exp_wk U (wk_shiftn (im_nn Mk + List.length gs + cargs_nrec D gs))) Us) ++
          vars_from (cargs_nrec D gs + List.length gs) (im_nn Mk) ++ vars_from (cargs_nrec D gs) (List.length gs))) cv ->
    set_interp T γ (elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ)
      (set_env_extend_kinded ρ (ctx_kinds (elim_bctx r p D Mk gs (blocks_motives Bks) Us)) (ns0 ++ vals ++ ihv))
      (elim_branch_type p D k Mk c gs (eb_motive b) Us)
      (FM (set_env_extend_kinded ρ (ctx_kinds (elim_mctx p D k Mk Us)) (ns0 ++ [cv]))).
Proof.
  intros k Mk c gs b FSm FM FM' ns0 vals ihv cv Hk Hr Hgs Hb HM Hln Hlv Hli Hθm Hcv.
  set (n := im_nn Mk + List.length gs + cargs_nrec D gs).
  set (ρb := set_env_extend_kinded ρ (ctx_kinds (elim_bctx r p D Mk gs (blocks_motives Bks) Us)) (ns0 ++ vals ++ ihv)) in *.
  set (θm := set_env_extend_kinded ρ (ctx_kinds (elim_mctx p D k Mk Us)) (ns0 ++ [cv])) in *.
  destruct HM as [_ HL _ _ _].
  pose proof (set_denotes_exists _ _ _ _ _ HL _ Hθm) as HM0.
  assert (Hlist : set_interp_list T γ (elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ) ρb
                    (vars_from (cargs_nrec D gs + List.length gs) (im_nn Mk) ++
                     apps_exp (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c)
                       (im_pre Mk (List.map (fun U => exp_wk U (wk_shiftn n)) Us) ++
                        vars_from (cargs_nrec D gs + List.length gs) (im_nn Mk) ++ vars_from (cargs_nrec D gs) (List.length gs)) :: nil)
                    (ns0 ++ [cv])).
  { apply set_interp_list_app; [| constructor; [exact Hcv | constructor]].
    replace (cargs_nrec D gs + List.length gs) with (List.length (vals ++ ihv)) by (rewrite List.length_app; lia).
    rewrite <- Hln. exact (set_interp_list_vars_from _ ns0 (vals ++ ihv) ρ _). }
  assert (Hβ : forall y, sub_entry_agrees T γ (elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ) ρb (sb_of_wk (wk_shiftn n) y) (ρ y)).
  { intros y. cbn [sb_of_wk wk_shiftn]. apply sub_agrees_var. unfold ρb.
    replace (y + n) with (List.length (ns0 ++ vals ++ ihv) + y) by (rewrite !List.length_app; unfold n; lia).
    apply set_env_extend_kinded_ge. }
  assert (Hset : sub_setting T γ (elim_mctx p D k Mk Us ++ Γ) θm nil (elim_mctx p D k Mk Us ++ Γ)
                   (elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ)
                   (sb_of_list (sb_of_wk (wk_shiftn n))
                      (vars_from (cargs_nrec D gs + List.length gs) (im_nn Mk) ++
                       apps_exp (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c)
                         (im_pre Mk (List.map (fun U => exp_wk U (wk_shiftn n)) Us) ++
                          vars_from (cargs_nrec D gs + List.length gs) (im_nn Mk) ++ vars_from (cargs_nrec D gs) (List.length gs)) :: nil))
                   ρb ρb).
  { constructor; [reflexivity | exact (Hbτ _ _ _ _ Hk Hr Hgs) | intros y Hy; cbn in Hy; lia | intros y; reflexivity |].
    intros y. exact (sub_agrees_of_list _ _ _ _ Hlist _ ρ _ Hβ y). }
  pose proof (set_interp_sub T γ _ _ _ _ HM0 (HMwf _ _ Hk) _ _ _ _ _ _ Hset) as H1.
  cbn [tele_sub List.app] in H1. unfold elim_branch_type. cbv zeta. exact H1.
Qed.

(** [member_reference_with k Mk Dq Mq]: the member [Mk], not a record
    view, refers to the member [Mq] of the group [Dq], with as many
    non-uniform parameters: itself at a declared member, the viewed
    member at a view. *)
Record member_reference_with (k : nat) (Mk : imember) (Dq : ind_decl) (Mq : imember) : Prop :=
  { (** [Dq] is the referred group *)
    member_reference_group : ind_lookup gc_deps gc_stack (fst (im_ref p k Mk)) = Some Dq
    (** [Mq] is the referred member *)
  ; member_reference_member : ind_member Dq (snd (im_ref p k Mk)) = Some Mq
    (** with as many non-uniform parameters *)
  ; member_reference_nn : im_nn Mq = im_nn Mk }.

(** Every member that is not a record view has its reference. *)
Lemma member_reference : forall k Mk, ind_member D k = Some Mk -> im_is_rview Mk = false ->
    exists Dq Mq, member_reference_with k Mk Dq Mq.
Proof.
  intros k Mk Hk Hr. unfold im_is_rview in Hr.
  destruct (im_head Mk) as [pm | qc k' Is vm | qr Is fl] eqn:Hh; try discriminate.
  - exists D, Mk. constructor; unfold im_ref; rewrite ?Hh; cbn [fst snd]; auto.
  - destruct (decl_typed_view _ _ _ HDt _ _ _ _ _ _ Hk Hh) as (D' & Mk' & Hl' & Hk' & _ & _ & _ & Hv & _).
    exists D', Mk'. constructor; unfold im_ref; rewrite ?Hh; cbn [fst snd]; [exact Hl' | exact Hk' |].
    destruct (decl_typed_view_wrap _ _ _ HDt _ _ _ _ _ _ Hk Hh) as (D2 & Hl2 & Hw).
    rewrite Hl' in Hl2. injection Hl2 as <-.
    destruct (view_wrap_ok_members _ _ _ Hw _ _ _ Hk' Hv) as (Mv & HMv & Hnn & _).
    rewrite Hk in HMv. injection HMv as <-. symmetry. exact Hnn.
Qed.

(** At a member that is not a record view, an element built from
    arguments drawn from the points having the property has the property:
    the branch at the constructor, at the arguments and their results, is
    its result, of the motive at the element. *)
Lemma block_point : forall k ns v SMk cs vals Mk θk,
    ind_member D k = Some Mk -> im_is_rview Mk = false ->
    List.nth_error (set_group_members G) k = Some SMk -> In cs (set_member_constructors SMk) ->
    arguments_fit G U S (us ++ ns) (set_constructor_arguments cs) vals -> set_eq v (constructed_element SMk cs ns vals) ->
    set_mem v (member_carrier G us U U k ns) ->
    set_env_in T γ (im_params D Mk) θk -> list_set_eq (uniform_values D Mk θk) us ->
    list_set_eq (set_env_values (im_nparams Mk) θk) ns ->
    point_ok Γ ρ r p Us Bks V D i us k ns v Mk.
Proof.
  intros k ns v SMk cs vals Mk θk Hk Hrv HSk Hcs Hfit Ev Hvmem Hθk Huni Hns.
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG. fold G in HG.
  pose proof (set_group_ok_members _ _ _ _ _ HG _ _ _ Hk HSk) as Hmok.
  set (c := set_constructor_name cs).
  assert (Hcn : In c (List.map fst (im_cons Mk)))
    by (rewrite <- (set_member_ok_names _ _ _ _ _ _ _ Hmok); apply List.in_map; exact Hcs).
  destruct (cons_lookup_of_names _ _ Hcn) as [gs Hgs]. change (ind_con Mk c = Some gs) in Hgs.
  pose proof (set_member_ok_constructors _ _ _ _ _ _ _ Hmok cs gs Hcs Hgs) as Hcok.
  set (sgs := set_constructor_arguments cs) in *.
  pose proof (set_group_ok_respects _ _ _ _ _ HG _ _ _ HSk Hcs) as Hrs. fold sgs in Hrs.
  pose proof (arguments_fit_length _ _ _ _ _ _ Hfit) as Hlv.
  pose proof (set_arguments_shape_length _ _ (set_constructor_ok_shape _ _ _ _ _ _ _ _ Hcok)) as Hlsh.
  assert (Hlvg : List.length vals = List.length gs) by lia.
  pose proof (cons_lookup_in _ _ _ Hgs) as Hin.
  destruct (member_pre_values k Mk Hk Hrv) as [pre Hpre].
  set (ns0 := set_env_values (im_nparams Mk) θk) in *.
  assert (Hln : List.length ns0 = im_nn Mk) by (unfold ns0, im_nn; rewrite length_set_env_values; reflexivity).
  assert (Hfit0 : arguments_fit G U S (us ++ ns0) sgs vals)
    by (eapply arguments_fit_resp; [exact Hrs | apply list_set_eq_app; [apply list_set_eq_refl | apply list_set_eq_sym; exact Hns]
                                   | apply list_set_eq_refl | exact Hfit]).
  (* the environments of the branch's context *)
  set (ρn := set_env_extend_kinded ρ (ctx_kinds (im_nparams Mk)) ns0).
  pose proof (nparams_env Γ ρ p D Us Fσ HΓ HcΓ Hρ HD Hσ k Mk SMk _ _ θk Hk HSk Hin Hθk Huni) as Hρn. fold ns0 ρn in Hρn.
  assert (Hdrop : forall x, set_env_drop (im_nn Mk) ρn x = ρ x)
    by (intros x; unfold set_env_drop, ρn; rewrite <- Hln, set_env_extend_kinded_ge; reflexivity).
  assert (Hvn : set_env_values (im_nparams Mk) ρn = ns0)
    by (unfold ρn; apply set_env_values_extend_kinded; exact Hln).
  pose proof (args_env Γ ρ p D Us Fσ HΓ HcΓ Hρ HD Hσ U Hcar S points_in_fixed_point k Mk SMk cs gs ρn vals Hk HSk Hcs Hgs Hcok Hρn Hdrop
                ltac:(rewrite Hvn; exact Hfit0) gs nil (eq_sym (List.app_nil_r gs))) as Hρa.
  rewrite List.firstn_all2 in Hρa by lia.
  set (ρa := set_env_extend_kinded ρn (ctx_kinds (cargs_ctx p D Mk gs)) vals) in *.
  assert (Econ : con_inst_ctx Γ p D Mk Us gs = tele_sub (cargs_ctx p D Mk gs ++ im_nparams Mk) (sb_of_list sb_id Us) ++ Γ)
    by (unfold con_inst_ctx; rewrite tele_sub_app, length_im_nparams, List.app_assoc; reflexivity).
  rewrite <- Econ in Hρa.
  destruct (Hbctx k Mk c gs Hk Hgs) as [Hbc Hbw].
  assert (Ebc : elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ =
                ihs_ctx_aux r (rview_leaves D) (im_nn Mk) (blocks_motives Bks) Us (List.length gs) (cargs_pat nil)
                  (List.length (@nil centry)) gs ++ nil ++ con_inst_ctx Γ p D Mk Us gs)
    by (unfold elim_bctx, con_inst_ctx; rewrite <- !List.app_assoc; reflexivity).
  rewrite Ebc in Hbc, Hbw.
  pose proof (ihs_env k Mk SMk cs gs vals θk Hk HSk Hcs Hgs Hθk Huni Hfit0 gs nil nil ρa eq_refl Hbc Hbw Hρa (fun z => eq_refl))
    as Hρb.
  rewrite <- Ebc in Hρb. change (List.skipn (List.length (@nil carg)) vals) with vals in Hρb.
  set (ihv := ihs_values (im_nn Mk) (cargs_pat nil) gs vals) in *.
  assert (Hli : List.length ihv = cargs_nrec D gs) by (apply length_ihs_values; exact Hlvg).
  assert (Eρb : set_env_extend_kinded ρa (ctx_kinds (ihs_ctx_aux r (rview_leaves D) (im_nn Mk) (blocks_motives Bks) Us (List.length gs)
                                                       (cargs_pat nil) (List.length (@nil centry)) gs)) ihv
                = set_env_extend_kinded ρ (ctx_kinds (elim_bctx r p D Mk gs (blocks_motives Bks) Us)) (ns0 ++ vals ++ ihv)).
  { unfold elim_bctx. rewrite !ctx_kinds_app, !ctx_kinds_tele_sub, <- (List.app_assoc (ctx_kinds (im_nparams Mk))).
    rewrite set_env_extend_kinded_app by (rewrite length_ctx_kinds; unfold im_nn in Hln; lia).
    rewrite set_env_extend_kinded_app by (rewrite length_ctx_kinds, length_cargs_ctx; lia). reflexivity. }
  rewrite Eρb in Hρb.
  set (ρb := set_env_extend_kinded ρ (ctx_kinds (elim_bctx r p D Mk gs (blocks_motives Bks) Us)) (ns0 ++ vals ++ ihv)) in *.
  (* the branch *)
  destruct (HBk k Mk Hk Hrv) as [b Hb].
  destruct (brs_names_lookup _ _ _ _ (Hbrs k Mk b Hk Hb) Hgs) as (n & B & Hlook & HinB).
  destruct (HBr k Mk b c gs n B Hk Hb Hgs HinB) as (FS & FB & FB' & HBt).
  pose proof HBt as [HFS HFB _ _ HFBm].
  pose proof (set_denotes_exists _ _ _ _ _ HFB _ Hρb) as Hres.
  pose proof (HFBm _ Hρb) as Hresm.
  set (res := FB ρb) in *.
  (* the constructor's value *)
  set (nb := im_nn Mk + List.length gs + cargs_nrec D gs).
  assert (Hlb : List.length (ns0 ++ vals ++ ihv) = nb) by (rewrite !List.length_app; unfold nb; lia).
  set (cv := apply_values (global_constructor γ (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c) (pre ++ ns0 ++ vals)).
  assert (Hcv : set_interp T γ (elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ) ρb
                  (apps_exp (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c)
                     (im_pre Mk (List.map (fun U => exp_wk U (wk_shiftn nb)) Us) ++
                      vars_from (cargs_nrec D gs + List.length gs) (im_nn Mk) ++ vars_from (cargs_nrec D gs) (List.length gs))) cv).
  { apply set_interp_apps; [apply set_interp_con |].
    apply set_interp_list_app; [| apply set_interp_list_app].
    - rewrite <- Ebc in Hbw. pose proof (member_pre_wk k Mk pre _ ρb Hk (member_pre_interp _ _ _ Hpre) Hbw) as H.
      rewrite length_elim_bctx in H. replace nb with (cargs_nrec D gs + List.length gs + im_nn Mk) by (unfold nb; lia). apply H.
      intros x. unfold ρb.
      replace (cargs_nrec D gs + List.length gs + im_nn Mk + x) with (List.length (ns0 ++ vals ++ ihv) + x) by (rewrite Hlb; unfold nb; lia).
      apply set_env_extend_kinded_ge.
    - replace (cargs_nrec D gs + List.length gs) with (List.length (vals ++ ihv)) by (rewrite List.length_app; lia).
      rewrite <- Hln. exact (set_interp_list_vars_from _ ns0 (vals ++ ihv) ρ _).
    - unfold ρb. unfold elim_bctx. rewrite !ctx_kinds_app, !ctx_kinds_tele_sub, <- (List.app_assoc (ctx_kinds (im_nparams Mk))).
      rewrite set_env_extend_kinded_app by (rewrite length_ctx_kinds; unfold im_nn in Hln; lia).
      rewrite <- Hli, <- Hlvg. exact (set_interp_list_vars_from _ vals ihv _ _). }
  assert (Ecv' : set_eq cv (con_val c (ns0 ++ vals))).
  { eapply set_eq_trans; [| exact (block_con_value k Mk SMk cs gs vals θk Hk Hrv HSk Hcs Hgs Hθk Huni Hfit0)].
    unfold cv. rewrite (apply_values_app _ pre), (apply_values_app _ us).
    apply apply_values_resp; [exact (member_pre_constructors _ _ _ Hpre c gs Hgs) | apply list_set_eq_refl]. }
  assert (Ecv : set_eq cv v).
  { eapply set_eq_trans; [exact Ecv' |].
    apply set_eq_sym. eapply set_eq_trans; [exact Ev |].
    unfold constructed_element. destruct (set_member_record_fields SMk) as [fl |] eqn:Hfl.
    - exfalso. destruct (proj1 (set_member_ok_record_fields _ _ _ _ _ _ _ Hmok fl) Hfl) as (qr & Is & Hh').
      unfold im_is_rview in Hrv. rewrite Hh' in Hrv. discriminate.
    - unfold con_val. apply ordered_pair_resp; [apply set_eq_refl |]. apply list_code_resp.
      apply list_set_eq_app; [apply list_set_eq_sym; exact Hns | apply list_set_eq_refl]. }
  (* the member type's value, and the motive's environment *)
  destruct (block_mty_value k Mk θk Hk Hrv Hθk Huni) as (amty & Hamty & Eamty). fold ns0 ρn in Hamty.
  set (θm := set_env_extend_kinded ρ (ctx_kinds (elim_mctx p D k Mk Us)) (ns0 ++ [cv])).
  assert (Eθm : θm = set_env_extend ρn (set_entry_term ak_relevant cv)).
  { unfold θm, elim_mctx. rewrite ctx_kinds_cons, ctx_kinds_tele_sub. cbn [centry_kind].
    apply set_env_extend_kinded_snoc. rewrite length_ctx_kinds. unfold im_nn in Hln. lia. }
  assert (Hθm : set_env_in T γ (elim_mctx p D k Mk Us ++ Γ) θm).
  { rewrite Eθm. unfold elim_mctx. cbn [List.app]. split; [exact Hρn |]. cbn [set_entry_rel]. exists cv, cv, amty.
    constructor; [reflexivity | reflexivity | exact Hamty | | apply set_eq_refl].
    eapply set_mem_eq_r; [apply set_eq_sym; exact Eamty |]. eapply set_mem_eq_l; [apply set_eq_sym; exact Ecv |].
    eapply set_mem_eq_r; [| exact Hvmem]. unfold member_carrier. apply candidate_carrier_resp. apply list_set_eq_sym. exact Hns. }
  (* the branch's value at every reading of the motive *)
  assert (Hbm : forall FSm FM FM', set_exp_eq_with T γ (elim_mctx p D k Mk Us ++ Γ) (abs_kind_sort r (a_typ i)) (eb_motive b) (eb_motive b)
                  FSm FM FM' -> set_mem res (code_carrier (FM θm))).
  { intros FSm FM FM' Hm.
    pose proof (block_branch_motive k Mk c gs b FSm FM FM' ns0 vals ihv cv Hk Hrv Hgs Hb Hm Hln Hlvg Hli Hθm Hcv) as H1.
    pose proof (set_denotes_exists _ _ _ _ _ HFS _ Hρb) as H2.
    pose proof (set_interp_functional T γ Hfn Hmods _ _ _ _ H2 ρb _ (set_env_rel_eq T γ _ _ _ Hρb) H1) as E.
    eapply set_mem_eq_r; [apply code_carrier_resp; exact E | exact Hresm]. }
  assert (Helim : r <> ak_propositional -> forall w, set_eq w (con_val c (ns0 ++ vals)) -> set_elim T γ Γ ρ r p Us Bks k w res).
  { intros Hr w Ew. destruct b as [nm Z A Bs].
    destruct (member_reference k Mk Hk Hrv) as (Dq & Mq & [HDq HMq Hnnq]).
    apply (set_elim_con T γ Γ ρ r p Us Bks k w res D Mk (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) Dq Mq c gs ns0 vals nm Z A Bs n B ihv
             HD Hk (surjective_pairing _) HDq HMq Hgs Ew ltac:(rewrite Hnnq; exact Hln) Hlvg Hb Hlook).
    - exact (block_ihs Hr k Mk SMk cs gs vals θk Hk HSk Hcs Hgs Hθk Huni Hfit0 gs nil eq_refl).
    - rewrite length_elim_bctx. lia.
    - rewrite <- Ebc in Hbw. exact Hbw.
    - exact Hres. }
  constructor.
  - intros Hr w' Ew'. constructor; [exact Hk | |].
    + intros _. exists res. split.
      * apply (Helim Hr). eapply set_eq_trans; [apply set_eq_sym; exact Ew' |]. eapply set_eq_trans; [apply set_eq_sym; exact Ecv | exact Ecv'].
      * destruct (HMot k Mk b Hk Hb) as (FSm & FM & FM' & Hm).
        exact (HV Hr k Mk b FSm FM FM' θm Hk Hb Hm Hθm res (Hbm _ _ _ Hm)).
    + intros qr Is fl c' gs' Hh'. unfold im_is_rview in Hrv. rewrite Hh' in Hrv. discriminate.
  - intros _. apply (end_fact_resp Γ ρ r p Us Bks V D i HMwf HMot HMctx Hcl k Mk ns0 ns cv v Hk Hln Hns Ecv).
    intros b' FSm FM FM' Hb' Hm. rewrite Hb in Hb'. injection Hb' as <-. split; [exact Hθm |].
    fold θm. pose proof (Hbm _ _ _ Hm) as Hr0.
    unfold end_value. destruct r eqn:Er.
    + eapply set_mem_eq_l; [| exact Hr0]. apply set_eq_sym.
      apply (elim_result_eq Γ ρ _ p Us Bks V Hρ k cv res); [apply Helim; [discriminate | exact Ecv'] |].
      destruct (HMot k Mk b Hk Hb) as (FSm' & FM0 & FM0' & Hm').
      exact (HV ltac:(discriminate) k Mk b FSm' FM0 FM0' θm Hk Hb Hm' Hθm res (Hbm _ _ _ Hm')).
    + cbn [abs_kind_sort] in Hm.
      pose proof (set_prop_is_prop_code T γ _ _ _ _ _ _ Hm Hθm) as Hpc.
      eapply set_mem_eq_l; [exact (prop_code_carrier_empty _ _ Hpc Hr0) | exact Hr0].
    + eapply set_mem_eq_l; [| exact Hr0]. apply set_eq_sym.
      apply (elim_result_eq Γ ρ _ p Us Bks V Hρ k cv res); [apply Helim; [discriminate | exact Ecv'] |].
      destruct (HMot k Mk b Hk Hb) as (FSm' & FM0 & FM0' & Hm').
      exact (HV ltac:(discriminate) k Mk b FSm' FM0 FM0' θm Hk Hb Hm' Hθm res (Hbm _ _ _ Hm')).
  - intros Hr. rewrite Hrv in Hr. discriminate.
Qed.

(** The induction's step: an element built from arguments drawn from the
    points having the property has the property, at every member. *)
Lemma elim_point_step : forall k ns v, set_mem (list_code ns) U -> set_mem v U ->
    constructed_from G us U S k ns v -> Q k ns v.
Proof.
  intros k ns v HnsU HvU (SMk & cs & vals & [HSk Hcs Hfit Ev]).
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG. fold G in HG.
  pose proof (set_group_ok_respects _ _ _ _ _ HG _ _ _ HSk Hcs) as Hrs.
  unfold Q, elim_point. intros Mk θk Hk Hθk Huni Hns.
  pose proof (set_group_ok_members _ _ _ _ _ HG _ _ _ Hk HSk) as Hmok.
  destruct (im_is_rview Mk) eqn:Hrv.
  2:{ (* a member with a block *)
      apply (block_point k ns v SMk cs vals Mk θk Hk Hrv HSk Hcs Hfit Ev); [| exact Hθk | exact Huni | exact Hns].
      apply member_carrier_intro; [exact (set_group_ok_respects _ _ _ _ _ HG) | exact HnsU | exact HvU |].
      exists SMk, cs, vals. constructor; [exact HSk | exact Hcs | | exact Ev].
      eapply arguments_fit_mono; [exact points_in_fixed_point | exact Hrs | exact Hfit]. }
  (* a record view: no non-uniform parameter, and its fields *)
  unfold im_is_rview in Hrv. destruct (im_head Mk) as [pm | qc k' Is vm | qr Is fl] eqn:Hh; try discriminate.
  pose proof (member_closed_rview_nn _ _ (decl_closed_members _ Hcl _ _ Hk) _ _ _ Hh) as Hnp.
  assert (Ens : ns = nil) by (rewrite Hnp in Hns; cbn [set_env_values] in Hns; inversion Hns; reflexivity).
  subst ns. rewrite List.app_nil_r in Hfit.
  pose proof (proj2 (set_member_ok_record_fields _ _ _ _ _ _ _ Hmok fl) (ex_intro _ qr (ex_intro _ Is Hh))) as Hfl.
  destruct (set_group_ok_record_views _ _ _ _ _ HG _ _ _ HSk Hfl) as (Hnd & _ & Hargs).
  pose proof (arguments_fit_length _ _ _ _ _ _ Hfit) as Hlv.
  assert (Hlfv : List.length fl = List.length vals) by (rewrite Hlv; symmetry; exact (Hargs cs Hcs)).
  assert (Exv : set_eq v (tuple_code (List.combine fl vals))) by (unfold constructed_element in Ev; rewrite Hfl in Ev; exact Ev).
  assert (Hcn : In (set_constructor_name cs) (List.map fst (im_cons Mk)))
    by (rewrite <- (set_member_ok_names _ _ _ _ _ _ _ Hmok); apply List.in_map; exact Hcs).
  destruct (cons_lookup_of_names _ _ Hcn) as [gs Hgs]. change (ind_con Mk (set_constructor_name cs) = Some gs) in Hgs.
  set (θ0 := set_env_drop (im_nn Mk) θk).
  assert (Hθ0 : set_env_in T γ (ind_uparams D) θ0) by exact (set_env_rel_drop T γ _ _ _ _ Hθk).
  constructor.
  - intros Hr w' Ew'. constructor; [exact Hk | unfold im_is_rview; rewrite Hh; discriminate |].
    intros qr' Is' fl' c gs' Hh' Hcs1. rewrite Hh in Hh'. injection Hh' as <- <- <-.
    pose proof (cons_lookup_in _ _ _ Hgs) as Hin. rewrite Hcs1 in Hin. destruct Hin as [E | []]. injection E as _ ->.
    exact (rview_point_results Hr k Mk qr Is fl SMk cs gs vals w' θ0 Hk Hh HSk Hcs Hgs Hfit Hnd Hlfv
             (set_eq_trans _ _ _ (set_eq_sym _ _ Ew') Exv) Hθ0 Huni).
  - unfold im_is_rview. rewrite Hh. discriminate.
  - intros _. exact (rview_point_fits k Mk qr Is fl SMk cs gs vals v Hk Hh HSk Hcs Hgs Hfit Hnd Hlfv Exv).
Qed.

(** The induction on the carriers: every element of a member's carrier
    has the property. *)
Lemma elim_point_of_carrier : forall k ns v, set_mem v (member_carrier G us U U k ns) -> Q k ns v.
Proof.
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG. fold G in HG.
  apply (member_carrier_ind G us U U (set_group_ok_respects _ _ _ _ _ HG) Q).
  - intros k ns ns' v v' En Ev HQ. unfold Q in *. exact (elim_point_resp Γ ρ r p Us Bks V D i HMwf HMot HMctx Hcl us k ns ns' v v' En Ev HQ).
  - exact elim_point_step.
Qed.

(** A member type, not a record view's, at [Us] and arguments reading the
    non-uniform parameters' values of an environment of its parameters
    whose uniform ones hold the uniform values: a code of the member's
    carrier there. *)
Lemma elim_mty_reading : forall m Mm Ns θ, ind_member D m = Some Mm -> im_is_rview Mm = false ->
    set_env_in T γ (im_params D Mm) θ -> list_set_eq (uniform_values D Mm θ) us ->
    set_interp_list T γ Γ ρ Ns (set_env_values (im_nparams Mm) θ) ->
    exists a, set_interp T γ Γ ρ (ind_mty p D m Us Ns) a /\
      set_eq (code_carrier a) (set_group_carrier G m (set_env_values (im_params D Mm) θ)).
Proof.
  intros m Mm Ns θ Hm Hr Hθ Huni HNs.
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG. fold G in HG.
  destruct (member_pre_values m Mm Hm Hr) as [pre Hpre].
  set (ns := set_env_values (im_nparams Mm) θ) in *.
  exists (apply_values (global_former γ (fst (im_ref p m Mm)) (snd (im_ref p m Mm))) (pre ++ ns)). split.
  - unfold ind_mty. rewrite Hm, (im_ty_at_not_rview _ _ _ _ _ Hr).
    apply set_interp_apps; [apply set_interp_indty |]. apply set_interp_list_app; [exact (member_pre_interp _ _ _ Hpre) | exact HNs].
  - pose proof (set_group_ok_formers_value _ _ _ _ _ HG m Mm θ Hm Hθ) as Ef.
    eapply set_eq_trans; [apply code_carrier_resp |].
    + apply (set_eq_trans _ (apply_values (global_former γ p m) (us ++ ns))).
      * rewrite !apply_values_app. apply apply_values_resp; [exact (member_pre_former _ _ _ Hpre) | apply list_set_eq_refl].
      * eapply set_eq_trans; [| exact Ef]. apply apply_values_resp; [apply set_eq_refl |].
        unfold im_params. rewrite set_env_values_app. apply list_set_eq_app; [apply list_set_eq_sym; exact Huni | apply list_set_eq_refl].
    + unfold inductive_code. apply code_carrier_type_code.
Qed.

(** An element of a member's carrier, not a record view's, at an
    environment of its parameters whose uniform ones hold the uniform
    values: into a sort of relevant terms its result is in [V], and the
    end's facts hold. *)
Lemma elim_at_scrutinee : forall m Mm θ w, ind_member D m = Some Mm -> im_is_rview Mm = false ->
    set_env_in T γ (im_params D Mm) θ -> list_set_eq (uniform_values D Mm θ) us ->
    set_mem w (set_group_carrier G m (set_env_values (im_params D Mm) θ)) ->
    (r <> ak_propositional -> exists res, set_elim T γ Γ ρ r p Us Bks m w res /\ set_mem res V) /\
    end_fact Γ ρ r p Us Bks V D i m Mm (set_env_values (im_nparams Mm) θ) w.
Proof.
  intros m Mm θ w Hm Hr Hθ Huni Hw.
  assert (Hw' : set_mem w (member_carrier G us U U m (set_env_values (im_nparams Mm) θ)))
    by (eapply set_mem_eq_r; [exact (Hcar m Mm θ Hm Hθ Huni) | exact Hw]).
  pose proof (elim_point_of_carrier _ _ _ Hw' Mm θ Hm Hθ Huni (list_set_eq_refl _)) as Hpt.
  split.
  - intros Hr0. destruct (point_ok_results _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpt Hr0 w (set_eq_refl _)) as [_ Hblk _]. exact (Hblk Hr).
  - exact (point_ok_fact _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpt Hr).
Qed.

End Induction.

(** ** The Rule of the Eliminator *)

(** The union of the carriers of the codes of the large universe at [i]:
    the set the results of an elimination into it are drawn from. *)
Definition large_results (i : nat) : aczel_set :=
  union_set (replacement_set (code_carrier (large_universe_code T i)) code_carrier).

(** An elimination, typed by its premises, of which the parameters, the
    scrutinee, the motives and the branches hold in the model and the
    motives' and branches' contexts denote, holds in the model: at every
    environment the scrutinee's value is in its member's carrier, the
    least fixed point, and the induction on it gives the eliminator's
    result, of the motive at the non-uniform parameters and the
    scrutinee. *)
Lemma set_rule_elim : forall Γ r p Us m Bks M D Mm bm Ps i,
    set_ctx T γ Γ ->
    ind_lookup gc_deps gc_stack p = Some D ->
    ind_member D m = Some Mm ->
    List.nth_error Bks m = Some bm ->
    List.length Bks = ind_nblk D ->
    List.length Ps = im_np D Mm ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) sb_id Ps) k = Some A ->
       gc_deps ⍮ gc_stack ⍮ Γ ⊢ P : A) ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) sb_id Ps) k = Some A ->
       set_exp_eq T γ Γ A P P) ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    set_exp_eq T γ Γ (ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps)) M M ->
    Us = List.firstn (ind_nu D) Ps ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ ce_ass ak_relevant (eb_scrutinee_type b) :: tele_sub (im_nparams Mk) (sb_of_list sb_id (List.firstn (ind_nu D) Ps))
                    ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       gc_deps ⍮ gc_stack ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : abs_kind_sort r (a_typ i)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       set_exp_eq T γ (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ) (abs_kind_sort r (a_typ i)) (eb_motive b) (eb_motive b)) ->
    (forall k Mk, ind_member D k = Some Mk ->
       gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk, ind_member D k = Some Mk -> set_ctx T γ (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                    ≈ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       set_ctx T γ (elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ)) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       gc_deps ⍮ gc_stack ⍮ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
         : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       set_exp_eq T γ (elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ)
         (elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) B B) ->
    motive_kind r ->
    set_exp_eq T γ Γ (exp_sub (eb_motive bm) (sb_of_list sb_id (List.skipn (ind_nu D) Ps ++ M :: nil)))
      (a_elim r p Us m Bks M) (a_elim r p Us m Bks M).
Proof.
  intros Γ r p Us m Bks M D Mm bm Ps i HΓ HD Hm Hbm HlB HPl HPs HPsem HMt HMsem HUs Hcnt Hsc HMty HMotsem HMx HMxsem Hbrs
    HBx HBxsem Hn HBty HBsem Hmk.
  pose proof (wf_elim _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD Hm Hbm HlB HPl HPs HMt HUs Hcnt Hsc HMty HMx Hbrs HBx Hn HBty Hmk) as Hel.
  subst Us. set (Us := List.firstn (ind_nu D) Ps) in *. set (Ns := List.skipn (ind_nu D) Ps) in *.
  pose proof (presup_exp_ctx HMt) as HcΓ.
  destruct (decl_of_lookup _ _ _ _ _ HcΓ HD) as [HDt Hcl].
  pose proof (decls_of_ctx _ _ _ HcΓ) as HDs.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.firstn_length_le; [reflexivity |]; rewrite HPl; unfold im_np; lia).
  assert (HNl : List.length Ns = im_nn Mm) by (unfold Ns; rewrite List.length_skipn, HPl; unfold im_np; lia).
  destruct (params_typed_split _ _ D Hcl _ _ Γ Ps Hm HPl HPs) as [HUt _].
  pose proof (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ HDt)) as Hsuf.
  pose proof (block_not_rview _ _ _ _ _ Hsuf HlB Hm Hbm) as Hrv.
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG.
  (* the parameters' instance *)
  destruct (List.nth_error (set_group_members (global_group γ p)) m) as [SMm |] eqn:HSm.
  2:{ exfalso. apply List.nth_error_None in HSm. rewrite (set_group_ok_member_count _ _ _ _ _ HG) in HSm.
      assert (Hlt : m < List.length (ind_members D)) by (apply List.nth_error_Some; unfold ind_member in Hm; congruence). lia. }
  pose proof (member_params_ctx p D HD m Mm SMm Hm HSm) as HPctx.
  pose proof (decl_closed_params _ _ _ Hcl Hm) as HPs0.
  pose proof (decl_closed_params_ass _ _ _ Hcl Hm) as HPass.
  pose proof (member_params_wf _ _ _ _ _ HDt Hm) as HPw.
  pose proof (wf_ctx_closed_app _ _ _ _ HPass HPs0 HPw HcΓ) as HPwΓ.
  assert (HPΓ : set_ctx T γ (im_params D Mm ++ Γ)).
  { pose proof (set_ctx_moved T γ Hfn Hmods _ nil Γ _ _ (set_gsub_drop T γ _ HcΓ) HΓ ltac:(rewrite List.app_nil_r; exact HPctx)
                  ltac:(rewrite List.app_nil_r; exact HPw)) as H.
    rewrite tele_sub_closed in H by exact HPs0. exact H. }
  destruct (set_gsub_closed_inst T γ Hfn Hmods (im_params D Mm) Γ Ps HΓ HPass HPΓ HPwΓ ltac:(rewrite length_im_params; exact HPl)
              HPs HPsem) as (Fι & HFι & _).
  (* the uniform parameters' instance *)
  set (Fσ := fun ρ => set_env_drop (im_nn Mm) (Fι ρ)).
  assert (EPs : forall x, sb_of_list sb_id Ps (im_nn Mm + x) = sb_of_list sb_id Us x).
  { intros x. rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1. fold Us Ns. rewrite sb_of_list_app, <- HNl, sb_of_list_ge. reflexivity. }
  assert (EPn : forall x, x < im_nn Mm -> sb_of_list sb_id Ps x = sb_of_list sb_id Ns x).
  { intros x Hx. rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1. fold Us Ns. rewrite sb_of_list_app.
    apply sb_of_list_lt_base. lia. }
  assert (Hσ : set_gsub_with T γ Γ (sb_of_list sb_id Us) (ind_uparams D ++ Γ) Fσ).
  { constructor.
    - exact (wf_sub_uparams _ _ _ HDt Hcl _ _ HcΓ HUl HUt).
    - intros ρ x Hρ. pose proof (set_gsub_agrees _ _ _ _ _ _ HFι ρ (im_nn Mm + x) Hρ) as H. rewrite EPs in H. exact H.
    - intros ρ ρ' Hr. pose proof (set_gsub_rel _ _ _ _ _ _ HFι _ _ Hr) as H. unfold im_params in H. rewrite <- List.app_assoc in H.
      exact (set_env_rel_drop T γ _ _ _ _ H). }
  (* the hypotheses of the induction that hold at every environment *)
  set (V := large_results i).
  assert (HMwf : forall j Mj, ind_member D j = Some Mj -> ⊢ gc_deps ⍮ gc_stack ⍮ elim_mctx p D j Mj Us ++ Γ)
    by (intros j Mj Hj; exact (ext_eq_ctx_left _ _ _ _ _ (HMx j Mj Hj))).
  assert (HMh : forall j Mj, ind_member D j = Some Mj -> elim_mctx_head_large gc_deps gc_stack Γ p D j Mj Us)
    by (intros j Mj Hj; exact (elim_mctx_head_wf _ _ _ _ _ _ _ _ Hgw HDs HD Hj HcΓ HUl HUt)).
  assert (HBk : forall j Mj, ind_member D j = Some Mj -> im_is_rview Mj = false -> exists b, List.nth_error Bks j = Some b)
    by (intros j Mj Hj Hr; exact (blocks_nth _ _ _ _ Hsuf HlB Hj Hr)).
  assert (Hmots : motives_typed gc_deps gc_stack Γ p D Us (blocks_motives Bks) r i).
  { intros j Mj Hj Hr. destruct (HBk j Mj Hj Hr) as [b Hb]. rewrite (blocks_motives_nth _ _ _ Hb). exact (HMty j Mj b Hj Hb). }
  assert (Hbτ : forall k Mk c gs, ind_member D k = Some Mk -> im_is_rview Mk = false -> ind_con Mk c = Some gs ->
    gc_deps ⍮ gc_stack ⍮ elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ
      ⊢ˢ sb_of_list (sb_of_wk (wk_shiftn (im_nn Mk + List.length gs + cargs_nrec D gs)))
           (vars_from (cargs_nrec D gs + List.length gs) (im_nn Mk) ++
            apps_exp (a_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c)
              (im_pre Mk (List.map (fun U => exp_wk U (wk_shiftn (im_nn Mk + List.length gs + cargs_nrec D gs))) Us) ++
               vars_from (cargs_nrec D gs + List.length gs) (im_nn Mk) ++ vars_from (cargs_nrec D gs) (List.length gs))
            :: nil)
      : elim_mctx p D k Mk Us ++ Γ)
    by (intros k Mk c gs Hk Hr Hc; exact (wf_branch_type_sub _ _ _ _ _ _ _ _ _ _ _ _ _ Hgw HDs HD Hk Hr HcΓ HUl HUt HMwf Hmots Hmk Hc)).
  assert (Hbctx : forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    set_ctx T γ (elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ) /\
    ⊢ gc_deps ⍮ gc_stack ⍮ elim_bctx r p D Mk gs (blocks_motives Bks) Us ++ Γ)
    by (intros k Mk c gs Hk Hc; exact (conj (HBxsem k Mk c gs Hk Hc) (ext_eq_ctx_left _ _ _ _ _ (HBx k Mk c gs Hk Hc)))).
  assert (HV : r <> ak_propositional -> forall k Mk b FS FMk FMk' θ, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
    set_exp_eq_with T γ (elim_mctx p D k Mk Us ++ Γ) (abs_kind_sort r (a_typ i)) (eb_motive b) (eb_motive b) FS FMk FMk' ->
    set_env_in T γ (elim_mctx p D k Mk Us ++ Γ) θ -> set_sub (code_carrier (FMk θ)) V).
  { intros Hr k Mk b FS FMk FMk' θ Hk Hb Hw Hθ z Hz.
    destruct Hmk; [| contradiction]. cbn [abs_kind_sort] in Hw. destruct Hw as [HFS _ _ _ HFm].
    pose proof (set_denotes_agree T γ _ _ _ _ _ HFS (set_denotes_typ T γ _ i) Hθ) as E.
    unfold V, large_results. apply set_mem_union. exists (code_carrier (FMk θ)). split; [| exact Hz].
    apply set_mem_replacement; [intros a b0 Eab; exact (code_carrier_resp _ _ Eab) |].
    exists (FMk θ). split; [eapply set_mem_eq_r; [apply code_carrier_resp; exact E | exact (HFm θ Hθ)] | apply set_eq_refl]. }
  (* the scrutinee and the motive at its member *)
  destruct HMsem as (FA0 & FM & FM' & HMw).
  destruct (HMotsem m Mm bm Hm Hbm) as (FSm & FMot & FMot' & HMotw).
  (* at every environment, the induction *)
  assert (Hkey : forall ρ, set_env_in T γ Γ ρ ->
    (r <> ak_propositional -> exists res, set_elim T γ Γ ρ r p Us Bks m (FM ρ) res /\ set_mem res V) /\
    end_fact Γ ρ r p Us Bks V D i m Mm (set_env_values (im_nparams Mm) (Fι ρ)) (FM ρ)).
  { intros ρ Hρ.
    (* the uniform parameters' environment, and the carriers' universe there *)
    pose proof (set_ctx_of_tele_types T γ Hfn Hmods _ _ _ (set_group_ok_uniform _ _ _ _ _ HG) I) as HU. rewrite List.app_nil_r in HU.
    pose proof (decl_closed_uparams _ Hcl) as Hs. pose proof (decl_closed_ass _ Hcl) as Hass.
    destruct (decl_typed_uparams _ _ _ HDt) as [Hw _].
    pose proof (wf_ctx_closed_app _ _ _ _ Hass Hs Hw HcΓ) as HwΓ.
    assert (HUΓ : set_ctx T γ (ind_uparams D ++ Γ)).
    { pose proof (set_ctx_moved T γ Hfn Hmods _ nil Γ _ _ (set_gsub_drop T γ _ HcΓ) HΓ ltac:(rewrite List.app_nil_r; exact HU)
                    ltac:(rewrite List.app_nil_r; exact Hw)) as H.
      rewrite tele_sub_closed in H by exact Hs. exact H. }
    destruct (inst_closed_env_in Γ (ind_uparams D) _ Fσ Hσ HΓ HcΓ nil ρ Hs HU HUΓ Hw HwΓ Hρ) as [_ Hinst].
    set (ρu := inst_closed_env Γ (ind_uparams D) Fσ nil ρ) in *.
    assert (Eu : set_env_values (ind_uparams D) ρu = elim_uniform_values ρ D Fσ).
    { unfold ρu. pose proof (inst_closed_env_values Γ (ind_uparams D) Fσ nil ρ) as E. cbn [List.app] in E.
      rewrite E, List.app_nil_r. reflexivity. }
    destruct (set_group_ok_carriers _ _ _ _ _ HG ρu Hinst) as (s & U & l & [_ HC]).
    rewrite Eu in HC. destruct HC as [_ _ Hcar].
    (* the parameters' closed environment *)
    destruct (set_closed_inst_env T γ Hfn Hmods _ _ _ _ HFι HΓ HPctx HPs0 HPw HPwΓ ρ Hρ) as [Hθc _].
    set (θc := set_env_moved (List.length (im_params D Mm)) (set_env_drop (List.length Γ)) (Fι ρ)) in *.
    assert (Eθc : forall x, x < List.length (im_params D Mm) -> θc x = Fι ρ x)
      by (intros x Hx; unfold θc, set_env_moved; apply set_env_above_lt'; exact Hx).
    assert (Huni : list_set_eq (uniform_values D Mm θc) (elim_uniform_values ρ D Fσ)).
    { unfold uniform_values, elim_uniform_values, Fσ.
      rewrite (set_env_values_agree (ind_uparams D) _ (set_env_drop (im_nn Mm) (Fι ρ))); [apply list_set_eq_refl |].
      intros x Hx. unfold set_env_drop. apply Eθc. rewrite length_im_params. unfold im_np, ind_nu. lia. }
    assert (Ens : set_env_values (im_nparams Mm) θc = set_env_values (im_nparams Mm) (Fι ρ)).
    { apply set_env_values_agree. intros x Hx. apply Eθc. rewrite length_im_params. unfold im_np, im_nn. lia. }
    (* the scrutinee is in its member's carrier *)
    assert (HNr : set_interp_list T γ Γ ρ Ns (set_env_values (im_nparams Mm) θc)).
    { rewrite Ens. apply interp_list_of_sub_agrees; [exact HNl |]. intros y Hy. rewrite <- EPn by exact Hy.
      exact (set_gsub_agrees _ _ _ _ _ _ HFι ρ y Hρ). }
    assert (Hred : exists a, set_interp T γ Γ ρ (ind_mty p D m Us Ns) a /\
                     set_eq (code_carrier a) (set_group_carrier (global_group γ p) m (set_env_values (im_params D Mm) θc)))
      by (eapply elim_mty_reading; eassumption).
    destruct Hred as (a & Ha & Ea).
    assert (Hmem : set_mem (FM ρ) (set_group_carrier (global_group γ p) m (set_env_values (im_params D Mm) θc))).
    { pose proof HMw as [HFA _ _ _ HFMm]. eapply set_mem_eq_r; [exact Ea |].
      eapply set_mem_eq_r; [apply code_carrier_resp; apply set_eq_sym; exact (set_denotes_unique _ _ _ _ _ HFA _ _ _ Hρ Ha) |].
      exact (HFMm ρ Hρ). }
    rewrite <- Ens. eapply elim_at_scrutinee; eassumption. }
  (* the eliminator's denotation, and its type's *)
  pose proof HMw as [_ HFM _ _ _].
  pose proof HMotw as [_ HFMot _ _ _].
  assert (HNr : forall ρ, set_env_in T γ Γ ρ -> set_interp_list T γ Γ ρ Ns (set_env_values (im_nparams Mm) (Fι ρ))).
  { intros ρ Hρ. apply interp_list_of_sub_agrees; [exact HNl |]. intros y Hy. rewrite <- EPn by exact Hy.
    exact (set_gsub_agrees _ _ _ _ _ _ HFι ρ y Hρ). }
  set (θm := fun ρ => set_env_extend_kinded ρ (ctx_kinds (elim_mctx p D m Mm Us)) (set_env_values (im_nparams Mm) (Fι ρ) ++ FM ρ :: nil)).
  set (F := fun ρ => end_value Γ ρ r p Us Bks V m (FM ρ)).
  assert (HF : set_denotes T γ Γ (a_elim r p Us m Bks M) F).
  { apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ. unfold F, end_value.
    destruct Hmk.
    - destruct (proj1 (Hkey ρ Hρ) ltac:(discriminate)) as (res & He & HVr).
      eapply set_interp_elim; [discriminate | exact Hel | exact (set_denotes_exists _ _ _ _ _ HFM _ Hρ) |].
      exact (elim_result_spec Γ ρ _ p Us Bks V Hρ m _ res He HVr).
    - apply set_interp_elim_prop. }
  exists (fun ρ => FMot (θm ρ)), F, F. constructor; [| exact HF | exact HF | intros; apply set_eq_refl |].
  - apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
    destruct (proj2 (Hkey ρ Hρ) bm FSm FMot FMot' Hbm HMotw) as [Hθ _].
    apply (interp_realized (elim_mctx p D m Mm Us ++ Γ) (θm ρ) Γ ρ);
      [exact (HMwf m Mm Hm) | exact (wf_elim_inst_sub _ _ _ _ _ _ _ _ _ Hcl Hm HPl HPs HMt (HMwf m Mm Hm)) | |
       exact (set_denotes_exists _ _ _ _ _ HFMot _ Hθ)].
    intros y. unfold θm. apply sub_agrees_of_list; [| intros z; apply sub_agrees_var; reflexivity].
    apply set_interp_list_app; [exact (HNr ρ Hρ) | constructor; [exact (set_denotes_exists _ _ _ _ _ HFM _ Hρ) | constructor]].
  - intros ρ Hρ. destruct (proj2 (Hkey ρ Hρ) bm FSm FMot FMot' Hbm HMotw) as [_ Hmem]. exact Hmem.
Qed.

End Eliminator.
