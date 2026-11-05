(** * Consequences of Completeness: types are rigid

    Distinct type constructors are never judgmentally equal, and [Typeω@i ≈ Typeω@j]
    forces [i = j].  Each proof reads the judgment at the initial environment and
    inverts the resulting [per_univ]; only the variable-against-variable case needs
    work, since there the values are neutrals whose levels must be turned back
    into indices.  The same-sort theorem for subtyping reads the kind of each
    side's value. *)

From Stdlib Require Import Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core Require Export Completeness.
From Mctt.Core.Completeness Require Import UniverseCases FunctionCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance Telescope.
From Mctt.Core.Completeness.Inductives Require Import Decl Model.
From Mctt.Core.Completeness.Modules Require Import Filed.
From Mctt.Core.Completeness Require Import UnitCases LetCases.
From Mctt.Core.Syntactic.System.Global Require Import Presup DescTyping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing IndCong.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** [x] is bound by an assumption of [Γ], of any tag, not by a
    definition. *)
Definition ctx_ass (Γ : ctx) (x : nat) : Prop :=
  exists κ A, List.nth_error Γ x = Some (ce_ass κ A).

(** A variable bound by an assumption evaluates, in the initial environment of
    its context, to the neutral at its own level. *)
Lemma eval_var_at_initial_env : forall {Γ x} {i : nat} {ρ a},
    ctx_ass Γ x ->
    initial_env_f Γ ρ ->
    ⟦ #x ⟧ ρ ↘ a ->
    Γ ⊢ #x : Typeω@i ->
    x < length Γ /\ exists b, a = ⇑! b (length Γ - x - 1).
Proof.
  intros * (κ & A & Hlookup) Hρ Hev Hx.
  pose proof (initial_env_spec _ _ _ _ _ Hρ Hlookup) as [b Heq].
  assert (Ha : a = ⇑! b (length Γ - x - 1))
    by (eapply functional_eval_exp; [ exact Hev | apply eval_exp_var_eq; exact Heq ]).
  split; [ apply List.nth_error_Some; congruence |].
  exists b; exact Ha.
Qed.

Lemma exp_eq_typ_implies_eq_level : forall {Γ} {i : nat} {j k},
    Γ ⊢ Typeω@i ≈ Typeω@j : Typeω@k ->
    i = j.
Proof.
  intros * H.
  destruct (rel_typ_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq H) (completeness_fundamental_exp_eq _ _ _ _ H)) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  assert (a = 𝕌ω@i) as ->
      by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ]).
  assert (a' = 𝕌ω@j) as ->
      by (eapply functional_eval_exp; [ exact Ha' | apply eval_exp_typ ]).
  invert_per_univ_elem HR; congruence.
Qed.

Hint Resolve exp_eq_typ_implies_eq_level : mctt.

(** The same at either tier, and across them: the universes at two different
    indices are never equal, since their values are not related. *)
Lemma exp_eq_universe_index_term_implies_eq : forall {Γ} {u v : universe_index} {k},
    Γ ⊢ universe_index_term u ≈ universe_index_term v : Typeω@k ->
    u = v.
Proof.
  intros * H.
  destruct (rel_typ_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq H) (completeness_fundamental_exp_eq _ _ _ _ H)) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  assert (a = universe_index_value u) as ->
      by (eapply functional_eval_exp; [ exact Ha | apply eval_universe_index_term ]).
  assert (a' = universe_index_value v) as ->
      by (eapply functional_eval_exp; [ exact Ha' | apply eval_universe_index_term ]).
  destruct u as [n | n], v as [m | m]; cbn in HR;
    invert_per_univ_elem HR; try congruence.
  (** Two small universes at literal levels: their levels are related, so
      they have the same realiser, which is the literal. *)
  match goal with H : per_lvl _ _ |- _ => apply per_lvl_real in H; cbn in H end.
  congruence.
Qed.

Corollary exp_eq_univ_implies_eq_level : forall {Γ} {n m k},
    Γ ⊢ Type⟨𝕃ᵒ n⟩ ≈ Type⟨𝕃ᵒ m⟩ : Typeω@k ->
    n = m.
Proof.
  intros * H.
  assert (us n = us m) as Heq by (eapply (exp_eq_universe_index_term_implies_eq (u := us n) (v := us m)); exact H).
  injection Heq; trivial.
Qed.

Hint Resolve exp_eq_univ_implies_eq_level : mctt.

(** A type of a large universe headed by a type constructor, or a
    variable.  The propositions [⊤], [⊥], [∀ₚ] and [Σₚ] are in [Prop], in no
    universe. *)
Inductive is_typ_constr : typ -> Prop :=
(** A large universe *)
| typ_is_typ_constr : forall i, is_typ_constr Typeω@i
(** A small universe at any level term: in a context with an axiom of type
    [Level] a closed type may be the universe at that axiom. *)
| univ_is_typ_constr : forall t, is_typ_constr Type⟨t⟩
(** A type of levels *)
| level_is_typ_constr : forall n, is_typ_constr Level@n
(** The sort of the types of levels, a type of [Typeω@0]
    ([wf_level_sort]) *)
| level_sort_is_typ_constr : is_typ_constr LevelSort
(** The universe of propositions *)
| prop_is_typ_constr : is_typ_constr Propₘ
(** A [Π] into a universe, its domain of any tag *)
| pi_is_typ_constr : forall κ A B, is_typ_constr (Π{κ} A B)
(** A variable *)
| var_is_typ_constr : forall x, is_typ_constr #x
(** An inductive type at its parameters. *)
| ind_is_typ_constr : forall p k Ms, is_typ_constr (apps_exp (a_ind p k) Ms)
(** A record type at its parameters. *)
| record_is_typ_constr : forall p Ms, is_typ_constr (apps_exp (a_record p) Ms)
.
Hint Constructors is_typ_constr : mctt.

(** A type is rigid in [Γ] when it is a type constructor or a variable bound
    by an assumption.  A variable bound by a definition is not rigid, since it
    is equal to its body. *)
Inductive rigid_typ (Γ : ctx) : typ -> Prop :=
(** A large universe *)
| typ_is_rigid : forall i, rigid_typ Γ Typeω@i
(** A small universe at a literal level *)
| univ_is_rigid : forall n, rigid_typ Γ Type⟨𝕃ᵒ n⟩
(** A type of levels *)
| level_is_rigid : forall n, rigid_typ Γ Level@n
(** The unit type *)
| True_is_rigid : rigid_typ Γ ⊤
(** The empty type *)
| False_is_rigid : rigid_typ Γ ⊥
(** A [Π] into a universe, its domain of any tag *)
| pi_is_rigid : forall κ A B, rigid_typ Γ (Π{κ} A B)
(** A variable bound by an assumption *)
| var_is_rigid : forall x, ctx_ass Γ x -> rigid_typ Γ #x
(** An inductive type at its parameters *)
| ind_is_rigid : forall p k Ms, rigid_typ Γ (apps_exp (a_ind p k) Ms)
(** A record type at its parameters *)
| record_is_rigid : forall p Ms, rigid_typ Γ (apps_exp (a_record p) Ms)
.
Hint Constructors rigid_typ : mctt.

(** An inductive type evaluates to an inductive type value. *)
Lemma eval_apps_ind_inv : forall p k xs ys r, $*| d_ind p k xs & ys | gc_deps ⍮ gc_stack ↘ r -> r = d_ind p k (xs ++ ys).
Proof.
  intros p k xs ys; revert xs; induction ys as [| y ys IH]; intros xs r H; inversion H; subst.
  - rewrite List.app_nil_r; reflexivity.
  - match goal with H1 : $| d_ind _ _ _ & _ | _ ⍮ _ ↘ _ |- _ => inversion H1; subst end.
    match goal with H2 : $*| _ & ys | _ ⍮ _ ↘ _ |- _ => apply IH in H2 end.
    subst; rewrite <- List.app_assoc; reflexivity.
Qed.

Lemma eval_ind_value : forall p k Ms ρ a, ⟦ apps_exp (a_ind p k) Ms ⟧ ρ ↘ a -> exists ms, a = d_ind p k ms.
Proof.
  intros * H; apply eval_apps_exp in H as (f & Hf & Hargs).
  inversion Hf; subst; apply eval_app_args_ind in Hargs as (ms & _ & Hap).
  apply eval_apps_ind_inv in Hap; eauto.
Qed.

(** A record type evaluates to a record type value. *)
Lemma eval_apps_record_inv : forall p xs ys r, $*| d_record p xs & ys | gc_deps ⍮ gc_stack ↘ r -> r = d_record p (xs ++ ys).
Proof.
  intros p xs ys; revert xs; induction ys as [| y ys IH]; intros xs r H; inversion H; subst.
  - rewrite List.app_nil_r; reflexivity.
  - match goal with H1 : $| d_record _ _ & _ | _ ⍮ _ ↘ _ |- _ => inversion H1; subst end.
    match goal with H2 : $*| _ & ys | _ ⍮ _ ↘ _ |- _ => apply IH in H2 end.
    subst; rewrite <- List.app_assoc; reflexivity.
Qed.

Lemma eval_record_value : forall p Ms ρ a, ⟦ apps_exp (a_record p) Ms ⟧ ρ ↘ a -> exists ms, a = d_record p ms.
Proof.
  intros * H; apply eval_apps_exp in H as (f & Hf & Hargs).
  inversion Hf; subst; apply eval_app_args_record in Hargs as (ms & _ & Hap).
  apply eval_apps_record_inv in Hap; eauto.
Qed.

(** An inductive type at parameters evaluates to the type former at the
    parameters' values. *)
Lemma eval_ind_apps_args : forall p k Ms ρ a, ⟦ apps_exp (a_ind p k) Ms ⟧ ρ ↘ a ->
    exists ms, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\ a = d_ind p k ms.
Proof.
  intros * H; apply eval_apps_exp in H as (f & Hf & Hargs).
  inversion Hf; subst; apply eval_app_args_ind in Hargs as (ms & Hms & Hap).
  apply eval_apps_ind_inv in Hap; eauto.
Qed.

(** So does a record type. *)
Lemma eval_record_apps_args : forall p Ms ρ a, ⟦ apps_exp (a_record p) Ms ⟧ ρ ↘ a ->
    exists ms, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\ a = d_record p ms.
Proof.
  intros * H; apply eval_apps_exp in H as (f & Hf & Hargs).
  inversion Hf; subst; apply eval_app_args_record in Hargs as (ms & Hms & Hap).
  apply eval_apps_record_inv in Hap; eauto.
Qed.

(** ** The Parameters of a Type Former

    The normal form of an inductive or record type reads each parameter
    at the parameter's type in the environment of the values of the
    parameters before it ([read_ps]), the types' closures over the empty
    environment.  NbE reads it at its instance [A_j[Id,,M_0,…,M_(j-1)]] in
    the initial environment of the context.  The two type values are
    related, so the two normal forms are equal up to their proofs. *)

(** A type over a closed telescope [C] of relevant parameters, at terms
    valid at its instances: its instance at the terms, at an environment,
    is related to it at the terms' values over the empty environment.
    [closed_inst_typ] asks the instances to be types of relevant sorts
    instead. *)
Lemma closed_instance_typ_evaluated : forall C Γ Ms X (k : nat) RΓ, all_assumptions C -> ⊨ C -> ⊨ Γ -> List.length Ms = List.length C ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    (exists l, rel_params_evaluated ⋅ C l) ->
    List.Forall (exp_scoped (List.length Γ)) Ms ->
    C ⊨ᵗ X ≈ X at k -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> forall ρ, RΓ ρ ρ ->
    exists ms a b i R, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\ ⟦ X[sb_of_list Id Ms] ⟧ ρ ↘ a /\
      ⟦ X ⟧ env_tele nil (List.rev C) ms ↘ b /\ per_univ_elem i R a b.
Proof.
  intros * HCa HC HΓ Hl HMs Hrel HMss HX HRΓ ρ Hρ.
  pose proof (gsub_valid (gsub_closed_inst _ _ _ HCa HC HΓ Hl HMs HMss)) as Hσ.
  destruct (rel_ctx_wf_per_ctx_env HC) as [RC HRC].
  destruct (closed_instance_values_of_sub C Γ Ms RΓ RC HCa HC HΓ HRΓ HRC Hrel Hσ Hl ρ ρ Hρ) as [ms ms' Hms Hms' _ Hev _].
  pose proof (@functional_eval gc_deps gc_stack) as Hfe; destruct Hfe as (_ & _ & Hfs & _).
  pose proof (Hfs _ _ _ Hms _ Hms') as <-.
  (** The instance's environment is related to itself at [C ++ Γ], so at
      [C], and so to the telescope's own extension *)
  destruct (closed_app_sem C Γ HCa HC HΓ) as [HCΓ Hres].
  destruct (rel_ctx_wf_per_ctx_env HCΓ) as [RCΓ HRCΓ].
  destruct (rel_sub_under_ctx_simple Hσ) as (RΓ1 & HRΓ1 & RΔ & HRΔ & Hs).
  assert (E1 : RΓ <~> RΓ1) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E2 : RΔ <~> RCΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E1 _ _) Hρ)) as (y1 & y2 & Ey1 & Ey2 & Hy).
  pose proof (per_ctx_env_resp_agree HRΔ _ _ _ _ (functional_eval_sub _ _ _ _ _ Ey1 Hev)
                (functional_eval_sub _ _ _ _ _ Ey2 Hev) Hy) as HyE.
  pose proof (Hres _ _ HRC HRCΓ _ _ (proj1 (E2 _ _) HyE)) as HEE.
  pose proof (eval_exps_length _ _ _ Hms) as Lms.
  assert (Lt : List.length (List.rev C) = List.length ms) by (rewrite List.length_rev; lia).
  rewrite env_extend_tagged_typed in HEE.
  assert (Lv : List.length (tagged_entries Γ (List.rev C) (ctx_retag Γ ρ) ms) = List.length C)
    by (rewrite tagged_entries_length by exact Lt; lia).
  pose proof (closed_env_tele_right C RC _ _ _ _ nil HCa HC HRC Lv Lv HEE) as Hmix.
  rewrite tagged_entries_fst in Hmix by exact Lt.
  (** The type at both *)
  pose proof (closed_app_type _ _ _ _ _ HCa HC HΓ HX) as HXΓ.
  pose proof (rel_type_inversion HXΓ) as [R0 [HΔ0 HXgen]].
  destruct (HXgen _ _ HRΓ _ _ (rel_sub_under_ctx_refl_left Hσ) _ _ _ _ Hρ Hev Hev) as [a a2 a3 a4 Ha Ha2 _ _ ([R1 HR1] & _)].
  destruct (rel_type_inversion_simple_at HRC HX _ _ Hmix) as (a3' & b & Ha3 & Hb & [R2 HR2]).
  rewrite <- env_extend_tagged_typed in Ha3.
  functional_eval_rewrite_clear.
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR1 HR2) as (R & HR & _).
  exists ms, a, b; eexists; exists R; repeat split; eassumption.
Qed.

(** A closed telescope [C] of parameters of evaluated kinds over [Γ]: the
    parameters of a member of an inductive group, or of a record type,
    in a well-formed context [Γ]. *)
Record evaluated_params_telescope (Γ C : ctx) : Prop := mk_evaluated_params_telescope
  { (** Its entries are assumptions *)
    evaluated_params_telescope_ass : all_assumptions C
    (** It is a valid closed context *)
  ; evaluated_params_telescope_valid : ⊨ C
    (** Each entry is a type of a universe or a type of levels over the
        entries before it ([rel_param_typed]) *)
  ; evaluated_params_telescope_evaluated : forall Δ1 κ A Δ2, C = (Δ1 ++ ce_ass κ A :: Δ2)%list -> exists l, rel_param_typed Δ2 A l
    (** It extends [Γ] *)
  ; evaluated_params_telescope_wf : ⊢ (C ++ Γ)%list }.

(** A global context is the one of its two parts: what the semantic
    validity of the identity embedding ([valid_gctx_embedding_refl_gc]),
    stated at [gc_mk gc_deps gc_stack], is read at. *)
Lemma gc_mk_eta : forall G : GCtx, G = gc_mk (@gc_deps G) (@gc_stack G).
Proof. intros [? ?]; reflexivity. Qed.

(** The parameters of a member of a group found from a well-formed
    context are such a telescope ([im_params_evaluated]). *)
Lemma ind_evaluated_params_telescope : forall Γ p D k Mk, ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D ->
    ind_member D k = Some Mk -> evaluated_params_telescope Γ (im_params D Mk).
Proof.
  intros * HΓ Hl Hk.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  pose proof (valid_gctx_embedding_ind_field _ _ _ _ (valid_gctx_embedding_refl_gc Hg) _ _ Hl) as HD.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [_ Hc].
  rewrite <- gc_mk_eta in HD.
  constructor; [ exact (decl_closed_params_ass _ _ _ Hc Hk) | exact (valid_ind_decl_params _ HD _ _ Hk)
               | exact (im_params_evaluated _ HD _ _ Hk) | exact (params_ctx_wf _ _ _ _ _ Hl Hk HΓ) ].
Qed.

(** So are the parameters of a record type found from a well-formed
    context. *)
Lemma record_evaluated_params_telescope : forall Γ p R, ⊢ Γ -> record_lookup gc_deps gc_stack p = Some R ->
    evaluated_params_telescope Γ (record_params R).
Proof.
  intros * HΓ Hl.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  pose proof (valid_gctx_embedding_record _ _ _ _ (valid_gctx_embedding_refl_gc Hg) _ _ Hl) as HR.
  rewrite <- gc_mk_eta in HR.
  destruct HR as [HP [l HPr] _ _ _].
  pose proof (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ Hl) as Ht.
  pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
  constructor; [ exact (typed_params_ass _ _ _ Ht) | exact HP | intros Δ1 κ A Δ2 E; exists l; rewrite <- (List.app_nil_r Δ2); exact (HPr _ _ _ _ E) |].
  pose proof (record_fctx_app_wf _ _ R 0 Γ ltac:(lia) Hc (typed_params_ass _ _ _ Ht)
                (record_typed_fctx_wf _ _ _ Ht _ (le_n _)) HΓ) as H.
  change (record_fctx R 0) with (@nil centry) in H; exact H.
Qed.

(** NbE of the parameters of a closed telescope [C] of relevant
    parameters agrees, up to proofs, with their readback along [C]: for
    [C = (l : Level) (A : Type@l)] and the parameters [l0, N], NbE reads
    [N] at [Type@l0] in the initial environment of [Γ], [read_ps] reads
    its value at [Type@l] with [l] the value of [l0]. *)
Lemma nbe_params_at_telescope : forall Γ C Ms ρ vs Rs,
    evaluated_params_telescope Γ C -> List.length Ms = List.length C ->
    (forall j P T, List.nth_error Ms j = Some P -> List.nth_error (tele_insts C Id Ms) j = Some T -> Γ ⊢ P : T) ->
    initial_env_f Γ ρ -> ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ vs ->
    Rps vs at List.rev C in gc_deps ⍮ gc_stack ⍮ nil ⍮ List.length Γ ↘ Rs ->
    forall j P T R V, List.nth_error Ms j = Some P -> List.nth_error (tele_insts C Id Ms) j = Some T ->
      List.nth_error Rs j = Some R -> nbe_f Γ P T V -> nf_eq_upto_proofs V R.
Proof.
  intros * [HCa HC HCr HCΓ] Hl HMs Hρ Hvs Hread j P T R V HP HT HR HV.
  assert (HΓw : ⊢ Γ) by (eapply ctx_app_wf_tail; exact HCΓ).
  destruct (tele_insts_nth _ _ _ _ _ HT) as (κ & A & HA & ->).
  (** [C] split at parameter [j]: [C1] holds it and those after it, [C2]
      those before it *)
  destruct (List.nth_error_split _ _ HA) as (l1 & l2 & Hrev & Hl1).
  assert (HCeq : C = (List.rev l2 ++ ce_ass κ A :: List.rev l1)%list)
    by (rewrite <- (List.rev_involutive C), Hrev, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity).
  set (C2 := List.rev l1) in *.
  assert (LC2 : List.length C2 = j) by (unfold C2; rewrite List.length_rev; lia).
  assert (LC : List.length C = List.length l2 + S j)
    by (rewrite HCeq, List.length_app; cbn [List.length]; rewrite LC2, List.length_rev; lia).
  assert (HCa2 : all_assumptions C2)
    by (rewrite HCeq in HCa; unfold all_assumptions in HCa; apply List.Forall_app in HCa as [_ HCa]; inversion HCa; assumption).
  set (C1 := (List.rev l2 ++ ce_ass κ A :: nil)%list).
  assert (HCeq' : C = (C1 ++ C2)%list) by (unfold C1; rewrite HCeq, <- List.app_assoc; reflexivity).
  assert (HC2 : ⊨ C2) by (rewrite HCeq' in HC; eapply rel_ctx_wf_app_r; exact HC).
  assert (HCr2 : exists l, rel_params_evaluated ⋅ C2 l).
  { apply rel_params_evaluated_of_entries; intros Δ1 κB B Δ2 E.
    destruct (HCr (C1 ++ Δ1)%list κB B Δ2) as [l Hl']; [ rewrite HCeq', E, <- List.app_assoc; reflexivity |].
    exists l; rewrite List.app_nil_r; exact Hl'. }
  (** The parameters before [j] are an instance of [C2] *)
  assert (Lj : j < List.length Ms) by (apply List.nth_error_Some; congruence).
  set (Ms2 := List.firstn j Ms).
  assert (LMs2 : List.length Ms2 = List.length C2) by (unfold Ms2; rewrite List.length_firstn; lia).
  assert (Hinsts : tele_insts C Id Ms = (tele_insts C2 Id Ms2 ++ tele_insts C1 (sb_of_list Id Ms2) (List.skipn j Ms))%list)
    by (rewrite HCeq', <- (List.firstn_skipn j Ms) at 1; apply tele_insts_app; [ exact HCa2 | exact LMs2 ]).
  assert (HMs2 : forall k N T, List.nth_error Ms2 k = Some N -> List.nth_error (tele_insts C2 Id Ms2) k = Some T -> Γ ⊢ N : T).
  { intros k N T HN HTk.
    assert (Hk : k < j) by (rewrite <- LC2, <- LMs2; apply List.nth_error_Some; congruence).
    apply (HMs k); [ unfold Ms2 in HN; rewrite nth_error_firstn_lt in HN by exact Hk; exact HN |].
    rewrite Hinsts, List.nth_error_app1; [ exact HTk | apply List.nth_error_Some; congruence ]. }
  assert (HMs2s : forall k N T, List.nth_error Ms2 k = Some N -> List.nth_error (tele_insts C2 Id Ms2) k = Some T -> Γ ⊨ N : T)
    by (intros; apply completeness_fundamental_exp; eapply HMs2; eassumption).
  assert (HMs2sc : List.Forall (exp_scoped (List.length Γ)) Ms2).
  { apply List.Forall_forall; intros N HN.
    destruct (List.In_nth_error _ _ HN) as [k Hk].
    assert (Hk' : k < List.length C2) by (rewrite <- LMs2; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some (tele_insts C2 Id Ms2) k) as [Tk HTk]; [ rewrite length_tele_insts by exact HCa2; lia |].
    exact (wf_exp_scoped_term _ _ _ _ _ (HMs2 _ _ _ Hk HTk)). }
  (** The type of parameter [j] at its instance and at the values before
      it are related *)
  destruct (HCr (List.rev l2) κ A C2 HCeq) as [lA HlA].
  assert (HX : exists kA, C2 ⊨ᵗ A ≈ A at kA)
    by (destruct HlA as [HlA | HlA]; eapply rel_type_of_sort; [ constructor | exact HlA | constructor | exact HlA ]).
  destruct HX as [kA HX].
  pose proof (completeness_fundamental_ctx _ HΓw) as HΓs.
  destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HRΓ].
  assert (HsΓ : ctx_scoped 0 Γ) by (eapply wf_ctx_scoped; exact HΓw).
  pose proof (per_ctx_then_per_env_initial_env HRΓ HsΓ HsΓ) as [ρ' [ρ'' [Hρ' [Hρ'' Hrel]]]].
  assert (ρ' = ρ) as -> by (eapply functional_initial_env; eassumption).
  assert (ρ'' = ρ) as -> by (eapply functional_initial_env; eassumption).
  destruct (closed_instance_typ_evaluated C2 Γ Ms2 A kA RΓ HCa2 HC2 HΓs LMs2 HMs2s HCr2 HMs2sc HX HRΓ ρ Hrel)
    as (ms & a & b & i & R0 & Hms & Ha & Hb & HR0).
  pose proof (@functional_eval gc_deps gc_stack) as Hfe; destruct Hfe as (Hfm & _ & Hfs & _).
  assert (Hms_vs : ms = List.firstn j vs).
  { pose proof Hvs as Hvs'; rewrite <- (List.firstn_skipn j Ms) in Hvs'.
    destruct (eval_exps_app_inv _ _ _ _ _ _ Hvs') as (ms' & ns & Evs & Hms' & _).
    pose proof (Hfs _ _ _ Hms _ Hms') as <-.
    pose proof (eval_exps_length _ _ _ Hms) as L.
    rewrite Evs, List.firstn_app; replace (j - List.length ms) with 0 by lia.
    rewrite List.firstn_O, List.app_nil_r, List.firstn_all2 by lia; reflexivity. }
  (** [read_ps] reads parameter [j] at the second *)
  destruct (eval_exps_nth _ _ _ _ _ Hvs HP) as (v & Hv & HPv).
  destruct (read_ps_nth_type _ _ _ _ _ Hread _ _ _ _ _ HA Hv HR) as (b' & Hb' & HRb).
  assert (Hlms : List.length ms = j) by (rewrite (eval_exps_length _ _ _ Hms); lia).
  assert (Henv : env_tele nil (List.rev C) (List.firstn j vs) = env_tele nil (List.rev C2) ms).
  { rewrite <- Hms_vs, (env_tele_firstn _ (List.rev C)), (env_tele_firstn _ (List.rev C2)), Hlms; f_equal.
    rewrite Hrev, List.firstn_app; replace (j - List.length l1) with 0 by lia.
    rewrite List.firstn_O, List.app_nil_r, List.firstn_all2 by lia.
    unfold C2; rewrite List.rev_involutive, List.firstn_all2 by lia; reflexivity. }
  rewrite Henv in Hb'.
  pose proof (Hfm _ _ _ Hb _ Hb') as <-.
  (** NbE reads it at the first: the two readbacks agree up to proofs *)
  pose proof (completeness_fundamental_exp _ _ _ (HMs _ _ _ HP HT)) as HPs.
  pose proof HPs as [env_relΓ' HΓ' _ _].
  destruct (LetCases.rel_exp_under_ctx_simple_full_at HΓ' HPs) as [kP HM].
  assert (E1 : RΓ <~> env_relΓ') by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (HM _ _ (proj1 (E1 _ _) Hrel)) as (t & t' & R' & Ht & Ht' & HR' & Hexp).
  destruct HV as [ρ0 a0 Hρ0 Ha0 HVt].
  assert (ρ0 = ρ) as -> by (eapply functional_initial_env; eassumption).
  fold Ms2 in Ht, Ht', Ha0.
  pose proof (Hfm _ _ _ Ha _ Ht) as <-; pose proof (Hfm _ _ _ Ha _ Ht') as <-; pose proof (Hfm _ _ _ Ha _ Ha0) as <-.
  assert (E : R' <~> R0) by (eapply per_univ_elem_right_irrel; eassumption).
  pose proof (per_univ_elem_kind _ _ _ _ HR0) as Hrab.
  destruct HVt as [w Hp Hw | m w Hr Hm Hw].
  - destruct (read_nf_propositional _ _ _ _ Hp Hw) as [Q ->].
    destruct (read_nf_propositional _ _ _ _ (eq_trans (eq_sym Hrab) Hp) HRb) as [Q' ->]; exact eq_refl.
  - destruct Hexp as [Hp | (m0 & m0' & Hm0 & Hm0' & Hmm)]; [ rewrite Hp in Hr; inversion Hr |].
    pose proof (Hfm _ _ _ HPv _ Hm) as <-; pose proof (Hfm _ _ _ HPv _ Hm0) as <-; pose proof (Hfm _ _ _ HPv _ Hm0') as <-.
    destruct (per_elem_then_per_top HR0 (proj1 (E _ _) Hmm) (List.length Γ)) as [W1 W2 HW1 HW2 HE].
    functional_read_rewrite_clear; exact HE.
Qed.

(** A universe as a term: a large one, or a small one at any level term. *)
Inductive univ_term : exp -> Prop :=
| univ_term_typ : forall i, univ_term Typeω@i
| univ_term_suniv : forall t, univ_term Type⟨t⟩.
Hint Constructors univ_term : mctt.

Theorem is_typ_constr_and_exp_eq_var_implies_eq_var : forall Γ A x i,
    rigid_typ Γ A ->
    ctx_ass Γ x ->
    Γ ⊢ A ≈ #x : Typeω@i ->
    A = #x.
Proof.
  intros * Histyp Hx H.
  assert (Γ ⊢ A : Typeω@i) by mauto 2.
  assert (Γ ⊢ #x : Typeω@i) by mauto 2.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq H) Hsem)
    as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  destruct (eval_var_at_initial_env Hx Hρ Ha' ltac:(eassumption)) as [Hxlt [b ->]].
  (** Only the variable case survives: [⇑! b _] has no other constructor to be
      related to. *)
  destruct Histyp;
    [ assert (a = 𝕌ω@i0) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ])
    | assert (a = 𝕌@(domain_level_lit n)) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_univ, eval_exp_llit ])
    | inversion Ha; subst
    | assert (a = ⊤ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_True ])
    | assert (a = ⊥ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_False ])
    | idtac
    | match goal with Hc : ctx_ass _ _ |- _ =>
        destruct (eval_var_at_initial_env Hc Hρ Ha ltac:(eassumption)) as [? [? ->]] end
    | destruct (eval_ind_value _ _ _ _ _ Ha) as [? ->]
    | destruct (eval_record_value _ _ _ _ Ha) as [? ->] ];
    invert_per_univ_elem HR.
  (** Two propositions related in [per_prop] read back alike up to their
      proofs: a relevant type or a type former is no neutral variable's,
      up to proofs or not. *)
  all: try solve [ match goal with Hp : per_prop _ _ |- _ =>
                     let Hl := fresh "Hl" in let Ht := fresh "Ht" in let HC := fresh "HC" in let HC' := fresh "HC'" in
                     let HE := fresh "HE" in
                     destruct Hp as [Hl _ Ht];
                     try (match goal with He : ⟦ a_pi _ _ _ _ ⟧ _ ↘ _ |- _ => inversion He; subst end);
                     first [ cbn in Hl; discriminate
                           | destruct (Ht (length Γ)) as [? ? HC HC' HE]; inversion HC; subst; inversion HC'; subst;
                             cbn in HE; discriminate ] end ].
  (** [Π A B] evaluates to a [Π]-value once its domain does. *)
  all: try solve [ match_by_head eval_exp ltac:(fun H => directed dependent destruction H) ].
  (** Two neutral variables related in [per_bot], or as propositions in
      [per_prop]: read both back at [length Γ] and compare the indices they
      produce, which the relation compares exactly. *)
  all: match goal with |- #?y = #?z => f_equal; enough (length Γ - y - 1 = length Γ - z - 1) by lia end.
  all: first [ match_by_head1 per_bot ltac:(fun H => destruct (H (length Γ)) as [? ? ? ? HE])
             | match goal with Hp : per_prop _ _ |- _ =>
                 let Ht := fresh "Ht" in destruct Hp as [_ _ Ht]; destruct (Ht (length Γ)) as [? ? ? ? HE] end;
               match_by_head read_typ ltac:(fun H => directed dependent destruction H) ].
  all: match_by_head read_ne ltac:(fun H => directed dependent destruction H).
  all: unfold nf_eq_upto_proofs, ne_eq_upto_proofs in HE; cbn in HE; apply PeanoNat.Nat.eqb_eq in HE; lia.
Qed.

Hint Resolve is_typ_constr_and_exp_eq_var_implies_eq_var : mctt.

Theorem is_typ_constr_and_exp_eq_typ_implies_eq_typ : forall Γ A i j,
    rigid_typ Γ A ->
    Γ ⊢ A ≈ Typeω@i : Typeω@j ->
    A = Typeω@i.
Proof.
  intros * Histyp H.
  assert (Γ ⊢ A : Typeω@j) by mauto 2.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq H) Hsem)
    as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  assert (a' = 𝕌ω@i) as ->
      by (eapply functional_eval_exp; [ exact Ha' | apply eval_exp_typ ]).
  destruct Histyp;
    [ assert (a = 𝕌ω@i0) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ])
    | assert (a = 𝕌@(domain_level_lit n)) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_univ, eval_exp_llit ])
    | inversion Ha; subst
    | assert (a = ⊤ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_True ])
    | assert (a = ⊥ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_False ])
    | idtac
    | match goal with Hc : ctx_ass _ _ |- _ =>
        destruct (eval_var_at_initial_env Hc Hρ Ha ltac:(eassumption)) as [? [? ->]] end
    | destruct (eval_ind_value _ _ _ _ _ Ha) as [? ->]
    | destruct (eval_record_value _ _ _ _ Ha) as [? ->] ];
    invert_per_univ_elem HR.
  - congruence.
  - match_by_head eval_exp ltac:(fun H => directed dependent destruction H).
Qed.

Hint Resolve is_typ_constr_and_exp_eq_typ_implies_eq_typ : mctt.

Theorem is_typ_constr_and_exp_eq_univ_implies_eq_univ : forall Γ A n j,
    rigid_typ Γ A ->
    Γ ⊢ A ≈ Type⟨𝕃ᵒ n⟩ : Typeω@j ->
    A = Type⟨𝕃ᵒ n⟩.
Proof.
  intros * Histyp H.
  assert (Γ ⊢ A : Typeω@j) by mauto 2.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq H) Hsem)
    as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  assert (a' = 𝕌@(domain_level_lit n)) as ->
      by (eapply functional_eval_exp; [ exact Ha' | apply eval_exp_univ, eval_exp_llit ]).
  destruct Histyp;
    [ assert (a = 𝕌ω@i) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ])
    | assert (a = 𝕌@(domain_level_lit n0)) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_univ, eval_exp_llit ])
    | inversion Ha; subst
    | assert (a = ⊤ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_True ])
    | assert (a = ⊥ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_False ])
    | idtac
    | match goal with Hc : ctx_ass _ _ |- _ =>
        destruct (eval_var_at_initial_env Hc Hρ Ha ltac:(eassumption)) as [? [? ->]] end
    | destruct (eval_ind_value _ _ _ _ _ Ha) as [? ->]
    | destruct (eval_record_value _ _ _ _ Ha) as [? ->] ];
    invert_per_univ_elem HR.
  - (** The two levels are related, so the two literals are the same
        realiser. *)
    match goal with H : per_lvl _ _ |- _ => apply per_lvl_real in H; cbn in H end.
    congruence.
  - match_by_head eval_exp ltac:(fun H => directed dependent destruction H).
Qed.

Hint Resolve is_typ_constr_and_exp_eq_univ_implies_eq_univ : mctt.


(** ** Universe Terms

    A universe as a term: a large one, or a small one at any level term.  The
    small ones at a level term are not [rigid_typ] — their level is a term —
    so these lemmas state what a judgment with a universe term on one side
    says about the other. *)

Lemma univ_term_universe_index_term : forall u, univ_term (universe_index_term u).
Proof. intros []; constructor. Qed.
Hint Resolve univ_term_universe_index_term : mctt.

Lemma pi_not_univ_term : forall κ A B, ~ univ_term (Π{κ} A B).
Proof. intros * H; inversion H. Qed.

(** A rigid type equal to a small universe at a level term is a universe: its
    value is related to a small universe's, and only a small universe's is. *)
Theorem is_typ_constr_and_exp_eq_suniv_tm : forall Γ A t j,
    rigid_typ Γ A ->
    Γ ⊢ A ≈ Type⟨t⟩ : Typeω@j ->
    univ_term A.
Proof.
  intros * Histyp H.
  assert (Γ ⊢ A : Typeω@j) by mauto 2.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq H) Hsem)
    as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha'; subst.
  destruct Histyp; try solve [ constructor ];
    [ inversion Ha; subst
    | assert (a = ⊤ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_True ])
    | assert (a = ⊥ᵈ) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_False ])
    | idtac
    | match goal with Hc : ctx_ass _ _ |- _ =>
        destruct (eval_var_at_initial_env Hc Hρ Ha ltac:(eassumption)) as [? [? ->]] end
    | destruct (eval_ind_value _ _ _ _ _ Ha) as [? ->]
    | destruct (eval_record_value _ _ _ _ Ha) as [? ->] ];
    invert_per_univ_elem HR.
  match_by_head eval_exp ltac:(fun H => directed dependent destruction H).
Qed.

Corollary rigid_typ_eq_univ_term : forall Γ A U k,
    rigid_typ Γ A ->
    univ_term U ->
    Γ ⊢ A ≈ U : Typeω@k ->
    univ_term A.
Proof.
  intros * HA HU H; destruct HU.
  - assert (A = Typeω@i) as -> by mauto 3; constructor.
  - eapply is_typ_constr_and_exp_eq_suniv_tm; eassumption.
Qed.

(** A [Π] is never a universe term. *)
Corollary pi_univ_term_absurd : forall Γ κ A B U k,
    univ_term U ->
    Γ ⊢ Π{κ} A B ≈ U : Typeω@k ->
    False.
Proof.
  intros * HU H.
  eapply pi_not_univ_term, rigid_typ_eq_univ_term; [ constructor | exact HU | exact H ].
Qed.

(** The two tiers are distinct: a large universe is never a small one. *)
Lemma exp_eq_typ_suniv_absurd : forall Γ i t k,
    Γ ⊢ Typeω@i ≈ Type⟨t⟩ : Typeω@k ->
    False.
Proof.
  intros * H.
  destruct (rel_typ_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq H) (completeness_fundamental_exp_eq _ _ _ _ H)) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  assert (a = 𝕌ω@i) as -> by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ]).
  inversion Ha'; subst.
  invert_per_univ_elem HR.
Qed.

(** A rigid type equal to a universe is that universe, at either tier. *)
Corollary rigid_typ_eq_universe_index_term : forall Γ A (u : universe_index) k,
    rigid_typ Γ A ->
    Γ ⊢ A ≈ universe_index_term u : Typeω@k ->
    A = universe_index_term u.
Proof. intros * ? H; destruct u as [n | i]; cbn in H |- *; mauto 3. Qed.

(** A type constructor other than a universe is never a universe: the goal is
    closed by inspecting the two tiers. *)
Lemma var_neq_universe_index_term : forall x (u : universe_index), #x <> universe_index_term u.
Proof. intros ? []; discriminate. Qed.

(** A [Π] is never a universe, at either tier. *)
Corollary pi_universe_index_term_absurd : forall Γ κ A B (u : universe_index) k,
    Γ ⊢ Π{κ} A B ≈ universe_index_term u : Typeω@k ->
    False.
Proof.
  intros * H; destruct u as [n | i]; cbn in H;
    [ assert (Π{κ} A B = Type⟨𝕃ᵒ n⟩) as Heq by mauto 3 | assert (Π{κ} A B = Typeω@i) as Heq by mauto 3 ];
    discriminate Heq.
Qed.

(** The same-sort theorem: the two sides of a subtyping are types of the
    same kind, at an environment of the context their values are of one
    kind, which a subtyping keeps ([per_subtyp_kind]).  It is why
    telescope equations ([wf_ext_eq_ass]) and context refinements
    ([ctx_sub_extend]) lose nothing by giving each side its own sort: the
    two sorts are of the same kind, which only the PER model shows. *)
Theorem subtyp_same_kind : forall Γ A A' r r' (i j : nat),
    Γ ⊢ A ⊆ A' ->
    Γ ⊢ A : abs_kind_sort r Typeω@i ->
    Γ ⊢ A' : abs_kind_sort r' Typeω@j ->
    r = r'.
Proof.
  intros * Hs HA HA'.
  pose proof (completeness_fundamental_subtyp _ _ _ Hs) as [R HR k Hsub].
  pose proof (completeness_fundamental_exp _ _ _ HA) as HAs.
  pose proof (completeness_fundamental_exp _ _ _ HA') as HA's.
  (** An environment of [Γ]: its initial one, the context being scoped. *)
  pose proof (proj1 (proj1 (proj1 (proj2 (proj2 (proj2 wf_scoped))) _ _ _ _ _ Hs))) as HsΓ.
  pose proof (per_ctx_then_per_env_initial_env HR HsΓ HsΓ) as [ρ [ρ' [_ [_ Hρ]]]].
  assert (HPR : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρρ : R ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  destruct (eval_sub_id_rel HR Hρρ) as [Hid Hid'].
  (** The values at [Id] are those at [ρ] ([exp_sub_id]), of the relevance
      of the values at its retagging, which the subtyping relates. *)
  destruct (Hsub _ _ HR _ _ (rel_sub_id (ex_intro _ _ HR)) _ _ _ _ Hρρ Hid Hid')
    as [aσ a0 a'σ' a0' Ha _ Ha' _ [Rl Hll] [Rr Hrr] Hsa].
  rewrite exp_sub_id in Ha, Ha'.
  pose proof (eq_trans (per_univ_elem_kind _ _ _ _ Hll)
                (eq_trans (per_subtyp_kind _ _ _ Hsa) (eq_sym (per_univ_elem_kind _ _ _ _ Hrr)))) as Hr.
  (** A type of the sort at a kind has a value of that kind. *)
  assert (Hrel : forall X s (l : nat), Γ ⊨ X : abs_kind_sort s Typeω@l -> forall x, ⟦ X ⟧ ρ ↘ x -> domain_kind x = s).
  { intros X s l HX x Hx.
    destruct (rel_type_kind_of_sort_kind (sort_kind_abs_kind_sort _ _) HX _ HR _ _ Hρρ) as (x' & Hx' & Hk).
    pose proof (functional_eval_exp _ _ _ _ Hx' Hx) as <-; exact Hk. }
  rewrite <- (Hrel _ _ _ HAs _ Ha), <- (Hrel _ _ _ HA's _ Ha'); exact Hr.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve exp_eq_typ_implies_eq_level exp_eq_univ_implies_eq_level : mctt.
#[export]
Hint Constructors is_typ_constr rigid_typ : mctt.
#[export]
Hint Resolve is_typ_constr_and_exp_eq_var_implies_eq_var : mctt.
#[export]
Hint Resolve is_typ_constr_and_exp_eq_typ_implies_eq_typ : mctt.
#[export]
Hint Resolve is_typ_constr_and_exp_eq_univ_implies_eq_univ : mctt.
#[export]
Hint Resolve pi_universe_index_term_absurd rigid_typ_eq_universe_index_term var_neq_universe_index_term : mctt.
#[export]
Hint Constructors univ_term : mctt.
#[export]
Hint Resolve univ_term_universe_index_term : mctt.
(** A concrete type that is not a universe is not a universe term. *)
#[export] Hint Extern 1 (~ univ_term _) =>
  (let Hu := fresh "Hu" in intro Hu; inversion Hu; fail) : mctt.
#[export] Hint Extern 1 (forall _ : universe_index, _ <> universe_index_term _) => (intros []; discriminate) : mctt.
#[export] Hint Extern 1 (_ <> universe_index_term _) => (destruct_all universe_index; discriminate) : mctt.
