(** * The Contexts of the Arguments of a Group's Constructors, Glued

    The gluing counterpart of [Completeness/Inductives/ArgTypes.v], at
    instances: each prefix of the arguments of a constructor of a member
    of a group of [VP] is a context glued with its types over the member's
    parameters ([glu_group_cargs_all]), and the type of a recursive
    argument after some of its shape's domains is a type of a large
    universe glued at its instances there ([glu_group_shape_typ]).

    A member's type is a declared member's type former at the uniform
    parameters as variables, a view's container's at the view's instance,
    or a record view's record ([glu_group_mty]).  A type former applied to
    terms glued at the instances of its parameters' telescope is glued at
    every instance ([glu_rel_exp_const_apps]): the terms are glued
    arguments at their values ([params_glu_args]), the former at them is
    glued at the value of its type at the canonical environment
    ([ctx_pi_glu_elem_by]), and moves to the value of its type at the
    instance, the type glued there being the witness
    ([glu_univ_elem_exp_conv]).  A view's instance is glued over the
    members as variables ([glu_views_self_is]), at the instance sending
    them to the group's own type formers applied to the uniform
    parameters ([glu_rel_sub_inst_grp_sb]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Telescope.
From Mctt.Core.Completeness.Modules Require Filed.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  Instances
  LevelCases
  LogicalRelation
  SubtypingCases
  VariableCases
  UniverseCases.
From Mctt.Core.Completeness.Inductives Require Import Model ArgTypes.
From Mctt.Core.Soundness.Inductives Require Import Args Params Comps.
From Mctt.Core.Completeness Require Import RecordCases.
From Mctt.Core.Completeness.Records Require Model.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
From Mctt.Core.Syntactic Require Import Records.
From Mctt.Core.Soundness.Records Require Import Former.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Types and Telescopes at Instances *)

(** A type of a large universe glued at its instances is glued there at a
    larger one. *)
Lemma glu_rel_exp_under_sub_kind_sort_lift : forall {Γ A κ} {i k : nat},
    i <= k ->
    glu_rel_exp_under_sub Γ A (abs_kind_sort κ Typeω@i) ->
    glu_rel_exp_under_sub Γ A (abs_kind_sort κ Typeω@k).
Proof.
  intros * Hle HA.
  apply (glu_rel_exp_under_sub_conv_typ (A := abs_kind_sort κ Typeω@i)); [| exact HA ].
  intros Γ' τ _ H; rewrite !abs_kind_sort_sub in *; cbn [exp_sub] in *.
  exact (glu_rel_exp_kind_sort_lift Hle H).
Qed.

(** A [Π] of types of a large universe glued at their instances, at the
    instances: the codomain at the instance lifted over the domain
    ([glu_rel_sub_inst_q]). *)
Lemma glu_rel_exp_under_sub_pi_large : forall {Γ κd κc A B} {i : nat},
    glu_rel_exp_under_sub Γ A (abs_kind_sort κd Typeω@i) ->
    glu_rel_exp_under_sub (Γ ▹{κd} A) B (abs_kind_sort κc Typeω@i) ->
    pi_kinds κd κc ->
    glu_rel_exp_under_sub Γ (a_pi κd κc A B) (abs_kind_sort κc Typeω@i).
Proof.
  intros * HA HB Hk.
  econstructor; [ apply HA |]; intros Γ' τ Hτ.
  pose proof (glu_rel_sub_inst_q Hτ HA (sort_kind_abs_kind_sort κd i)) as Hq.
  pose proof (glu_rel_exp_under_sub_inst_sort HA (sort_kind_type_sort _ _ (sort_kind_abs_kind_sort κd i)) Hτ) as HAτ.
  pose proof (glu_rel_exp_under_sub_inst_sort HB (sort_kind_type_sort _ _ (sort_kind_abs_kind_sort κc i)) Hq) as HBτ.
  rewrite (type_sort_sub _ τ (sort_kind_type_sort _ _ (sort_kind_abs_kind_sort κc i))); cbn [exp_sub].
  exact (glu_rel_exp_pi_large HAτ HBτ Hk).
Qed.

(** The entries of a telescope of assumptions [Δ] over [Γ], each a type of
    the sort of its kind next to a large universe glued at its instances
    over the entries after it. *)
Definition glu_tele_entries (Δ Γ : ctx) : Prop :=
  forall Δ1 κ A Δ2, Δ = Δ1 ++ ce_ass κ A :: Δ2 -> exists j : nat, glu_rel_exp_under_sub (Δ2 ++ Γ) A (abs_kind_sort κ Typeω@j).

Lemma glu_tele_entries_tail : forall e Δ Γ, glu_tele_entries (e :: Δ) Γ -> glu_tele_entries Δ Γ.
Proof. intros * H Δ1 κ A Δ2 E; apply (H (e :: Δ1)); rewrite E; reflexivity. Qed.

(** The entries of a telescope past its last entry, over the context
    extended by it. *)
Lemma glu_tele_entries_snoc : forall Δ e Γ, glu_tele_entries (Δ ++ e :: nil) Γ -> glu_tele_entries Δ (e :: Γ).
Proof.
  intros * H Δ1 κ A Δ2 E.
  destruct (H Δ1 κ A (Δ2 ++ e :: nil)) as [j Hj]; [ rewrite E, <- List.app_assoc; reflexivity |].
  exists j; rewrite <- List.app_assoc in Hj; exact Hj.
Qed.

(** A telescope of glued entries extends a context glued with its types. *)
Lemma glu_rel_ctx_types_app : forall Δ Γ, all_assumptions Δ -> glu_rel_ctx_types Γ -> glu_tele_entries Δ Γ ->
    glu_rel_ctx_types (Δ ++ Γ).
Proof.
  induction Δ as [| e Δ IH]; intros * Hass HΓ HΔ; [ exact HΓ |].
  apply List.Forall_cons_iff in Hass as [(κ & A & ->) Hass].
  destruct (HΔ nil κ A Δ eq_refl) as [j HA].
  exact (glu_rel_ctx_types_extend HA (sort_kind_abs_kind_sort κ j)).
Qed.

(** The [Π] over a telescope of glued entries of a type of a large
    universe glued at its instances. *)
Lemma glu_rel_exp_under_sub_ctx_pi : forall Δ Γ B (i : nat), all_assumptions Δ -> glu_tele_entries Δ Γ ->
    glu_rel_exp_under_sub (Δ ++ Γ) B Typeω@i ->
    exists j : nat, glu_rel_exp_under_sub Γ (ctx_pi Δ B) Typeω@j.
Proof.
  induction Δ as [| e Δ IH]; intros * HΔa HΔ HB; [ exists i; exact HB |].
  apply List.Forall_cons_iff in HΔa as [(κ & A & ->) HΔa].
  destruct (HΔ nil κ A Δ eq_refl) as [k HA].
  cbn [ctx_pi_at].
  apply (IH _ _ (max k i) HΔa (glu_tele_entries_tail _ _ _ HΔ)).
  exact (glu_rel_exp_under_sub_pi_large (glu_rel_exp_under_sub_kind_sort_lift (Nat.le_max_l k i) HA)
           (glu_rel_exp_under_sub_kind_sort_lift (κ := ak_relevant) (Nat.le_max_r k i) HB) (pi_kinds_relevant κ)).
Qed.

(** The instance into nothing. *)
Lemma glu_rel_sub_inst_nil : forall Γ σ, ⊩ Γ -> glu_rel_sub_inst Γ σ ⋅.
Proof.
  intros * HΓ.
  econstructor; [ apply wf_sub_nil'; destruct HΓ as [Sb HSb]; exact (glu_ctx_env_wf_ctx HSb) | exact HΓ
                | intros x A Hx; inversion Hx | intros x U Hx; inversion Hx ].
Qed.

(** An instance extended by terms glued at every renaming at the instances
    of a telescope of glued entries, as [gsub_of_list]. *)
Lemma glu_rel_sub_inst_of_list : forall Δ Γ Γ1 σ0 Ms, all_assumptions Δ -> glu_rel_sub_inst Γ σ0 Γ1 -> ⊢ Δ ++ Γ1 ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ σ0 Ms) k = Some T ->
       glu_rel_exp_under_renaming Γ N T) ->
    glu_rel_sub_inst Γ (sb_of_list σ0 Ms) (Δ ++ Γ1).
Proof.
  induction Δ as [| e Δ IH]; intros Γ Γ1 σ0 Ms Hass Hg0 HΔ Hl HMs.
  - destruct Ms; cbn in Hl; [| discriminate ]; cbn; exact Hg0.
  - apply List.Forall_cons_iff in Hass as [(κ & A & ->) Hass].
    pose proof Hass as HCa'.
    cbn [List.app] in HΔ; inversion HΔ; subst.
    match goal with H : _ ⊢ A : ?S, H' : sort_kind ?S κ |- _ => rename H into HA, H' into HS0, S into S0 end.
    destruct (List.exists_last (l := Ms) ltac:(intros ->; cbn in Hl; discriminate)) as (Ms' & M & ->).
    rewrite List.length_app in Hl; cbn in Hl.
    assert (Hl' : List.length Ms' = List.length Δ) by lia; clear Hl.
    assert (Hti : tele_insts (ce_ass κ A :: Δ) σ0 (Ms' ++ M :: nil) = tele_insts Δ σ0 Ms' ++ A[sb_of_list σ0 Ms'] :: nil).
    { change (ce_ass κ A :: Δ) with ((ce_ass κ A :: nil) ++ Δ).
      rewrite tele_insts_app by (try exact HCa'; lia); reflexivity. }
    assert (HlT : List.length (tele_insts Δ σ0 Ms') = List.length Δ) by (rewrite length_tele_insts by exact HCa'; lia).
    rewrite sb_of_list_app; cbn [sb_of_list List.app].
    eapply (glu_rel_sub_inst_extend (S := S0));
      [ apply (IH _ _ _ _ Hass Hg0 (presup_exp_ctx HA) Hl') | exact HA | exact HS0 |].
    + intros k N T HN HT.
      assert (Hk : k < List.length Δ) by (rewrite <- HlT; apply List.nth_error_Some; congruence).
      apply (HMs k); [ rewrite List.nth_error_app1 by lia; exact HN | rewrite Hti, List.nth_error_app1 by lia; exact HT ].
    + apply (HMs (List.length Δ)); [ rewrite List.nth_error_app2, Hl', Nat.sub_diag by lia; reflexivity |].
      rewrite Hti, List.nth_error_app2, HlT, Nat.sub_diag by lia; reflexivity.
Qed.

(** ** Type Formers Applied at Instances *)

(** A term scoped by a list instance does not see the instance's base. *)
Lemma exp_sub_sb_of_list_base : forall M Ms σ τ, exp_scoped (List.length Ms) M -> M[sb_of_list σ Ms] = M[sb_of_list τ Ms].
Proof.
  intros * Hs; eapply exp_scoped_sub_agree; [ exact Hs |]; intros x Hx.
  rewrite !(sb_of_list_nth _ _ _ (a_var 0)) by lia; reflexivity.
Qed.

(** A list instance followed by a substitution, on a term it scopes: the
    list of the substituted terms. *)
Lemma exp_sub_sb_of_list_compose : forall M Ms σ, exp_scoped (List.length Ms) M ->
    M[sb_of_list Id Ms][σ] = M[sb_of_list Id (List.map (fun N => N[σ]) Ms)].
Proof.
  intros * Hs; rewrite exp_sub_sub; eapply exp_scoped_sub_agree; [ exact Hs |]; intros x Hx.
  cbn [sb_compose]; apply sb_of_list_lt_compose; exact Hx.
Qed.

(** The telescope of the arguments after [Xs], at the list instance of
    [Xs] over two bases, when it is scoped past them. *)
Lemma tele_insts_sb_of_list_base : forall Δt Xs σ τ Ms, all_assumptions Δt -> ctx_scoped (List.length Xs) Δt ->
    tele_insts Δt (sb_of_list σ Xs) Ms = tele_insts Δt (sb_of_list τ Xs) Ms.
Proof.
  intros * Hass Hs; apply (tele_insts_agree _ _ _ _ _ Hass Hs); intros x Hx.
  rewrite !(sb_of_list_nth _ _ _ (a_var 0)) by lia; reflexivity.
Qed.

(** A closed constant [X] applied to terms [Us] glued at the instances of
    the outer part [Γb] of a closed telescope [Δt ++ Γb] is glued at the
    instance of the [Π] over the rest [Δt]: as [ctx_pi_glu_elem_by] says
    of the terms' values at the canonical environment of [Γb], after the
    terms are glued arguments there ([params_glu_args]); then, the values
    of the [Π] at the canonical environment and of its instance at the
    environment being related ([closed_inst_typ]), the instance, glued, is
    the witness the constant moves to ([glu_univ_elem_exp_conv]).  [Fr]
    relates the constant's values to its arguments'; [Hbase] glues it at
    all its arguments. *)
Lemma glu_rel_exp_const_apps : forall (Fr : list domain -> domain -> Prop) X T,
    (forall σ, X[σ] = X) ->
    (forall Δ1 Γ' Sb' Δ' σ' xs x w, T = Δ1 ++ Γ' -> EG Γ' ∈ glu_ctx_env ↘ Sb' ->
       Δ' ⊢ˢ σ' ® env_tele nil (List.rev Γ') (xs ++ x :: nil) ∈ Sb' -> List.length Γ' = S (List.length xs) -> Fr xs w ->
       exists u, $| w & x | gc_deps ⍮ gc_stack ↘ u /\ Fr (xs ++ x :: nil) u) ->
    forall Δt Γb SbB SbT B (i : nat),
      all_assumptions (Δt ++ Γb) -> ctx_scoped 0 (Δt ++ Γb) -> ⊨ Γb -> (exists l, rel_params_evaluated ⋅ Γb l) ->
      EG Γb ∈ glu_ctx_env ↘ SbB -> EG Δt ++ Γb ∈ glu_ctx_env ↘ SbT -> (exists Δ0, T = Δ0 ++ Δt ++ Γb) ->
      (forall Δ1 κ A Δ2, Δt = Δ1 ++ ce_ass κ A :: Δ2 -> glu_entry_valid_at i (Δ2 ++ Γb) κ A) ->
      (forall Δ1 Δ2, Δt = Δ1 ++ Δ2 -> Δ2 ++ Γb ⊢ ctx_pi Δ1 B : Typeω@i) ->
      glu_entry_valid_at i (Δt ++ Γb) ak_relevant B ->
      Γb ⊨ apps X (vars_from 0 (List.length Γb)) : ctx_pi Δt B ->
      (forall xs w, Fr xs w -> List.length xs = List.length Γb ->
         ⟦ apps X (vars_from 0 (List.length Γb)) ⟧ env_tele nil (List.rev Γb) xs ↘ w) ->
      (forall Δ' Ms vs w', ⊢ Δ' -> glu_args Δ' (Δt ++ Γb) Id nil Ms vs -> Fr vs w' ->
         forall b P El, ⟦ B ⟧ env_tele nil (List.rev (Δt ++ Γb)) vs ↘ b -> DG b ∈ glu_univ_elem i ↘ P ↘ El ->
           (forall R, DF b ≈ b ∈ per_univ_elem i ↘ R -> R w' w') ->
           Δ' ⊢ apps X Ms : B[sb_of_list Id Ms] ® w' ∈ El) ->
      forall Γ' Us (i' : nat),
        (forall ρ us, ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ us -> exists w, ⟦ apps X Us ⟧ ρ ↘ w /\ Fr us w) ->
        ⊩ Γ' -> List.length Us = List.length Γb ->
        (forall m N T', List.nth_error Us m = Some N -> List.nth_error (tele_insts Γb Id Us) m = Some T' -> Γ' ⊩ N : T') ->
        Γ' ⊩ (ctx_pi Δt B)[sb_of_list Id Us] : Typeω@i' ->
        Γ' ⊢ apps X Us : (ctx_pi Δt B)[sb_of_list Id Us] ->
        Γ' ⊩ apps X Us : (ctx_pi Δt B)[sb_of_list Id Us].
Proof.
  intros Fr X T HXw Happ Δt Γb SbB SbT B i Hass Hsc HΓb HΓbev HSbB HSbT HT HA HCs HBv HV HXev Hbase
    Γ' Us i' Heval HΓ' HlU HUs Hwit HXt.
  unfold all_assumptions in Hass; pose proof Hass as Hass'; apply List.Forall_app in Hass' as [HassT HassB].
  pose proof Hsc as Hsc'; apply ctx_scoped_app in Hsc' as [HscT HscB].
  pose proof HΓ' as [SbΓ HSbΓ].
  destruct (glu_ctx_env_per_ctx_env HSbΓ) as [RΓ HRΓ].
  pose proof (glu_ctx_env_wf_ctx HSbΓ) as HΓw.
  pose proof (completeness_fundamental_ctx _ HΓw) as HΓs.
  (** The [Π], typed over [Γb] *)
  pose proof (HCs Δt nil ltac:(rewrite List.app_nil_r; reflexivity)) as HPi; cbn [List.app] in HPi.
  assert (HPis : exp_scoped (List.length Γb) (ctx_pi Δt B))
    by exact (proj1 (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ HPi))).
  (** The constant at related values is in the relation of the [Π]: the
      constant at the variables is valid, of a relevant type *)
  assert (HPER : forall xs w R a, Fr xs w -> per_tele_args (List.rev Γb) nil nil xs xs -> List.length xs = List.length Γb ->
             ⟦ ctx_pi Δt B ⟧ env_tele nil (List.rev Γb) xs ↘ a -> DF a ≈ a ∈ per_univ_elem i ↘ R -> R w w).
  { intros xs w R0 a0 Hw Hxs Hlx Ea0 HR0.
    destruct (rel_exp_under_ctx_simple HV) as (RU2 & HRU2 & l & Hsim).
    pose proof (tele_args_env_rel _ _ _ _ _ _ HRU2 HΓb Hlx Hxs) as HρU2.
    destruct (Hsim _ _ HρU2) as (b0 & b0' & R1 & Eb0 & Eb0' & HR1 & [Hp | (m & m' & Em & Em' & Hmm)]).
    { destruct (Completeness.ContextCases.rel_type_kind_of_typ (completeness_fundamental_exp _ _ _ HPi) _ HRU2 _ _ HρU2)
        as (b1 & Eb1 & Hk1).
      assert (b1 = b0) as -> by (eapply functional_eval_exp; eassumption); congruence. }
    pose proof (HXev _ _ Hw Hlx) as Ed.
    assert (m = w) as -> by (eapply functional_eval_exp; eassumption).
    assert (m' = w) as -> by (eapply functional_eval_exp; eassumption).
    assert (b0 = a0) as -> by (eapply functional_eval_exp; eassumption).
    assert (b0' = a0) as -> by (eapply functional_eval_exp; eassumption).
    apply (per_univ_elem_left_irrel _ _ _ _ _ _ _ HR1 HR0); exact Hmm. }
  assert (HUt : forall m N T', List.nth_error Us m = Some N -> List.nth_error (tele_insts Γb Id Us) m = Some T' -> Γ' ⊢ N : T')
    by (intros; eapply glu_rel_exp_to_wf_exp; eauto).
  assert (HUc : forall m N T', List.nth_error Us m = Some N -> List.nth_error (tele_insts Γb Id Us) m = Some T' -> Γ' ⊨ N : T')
    by (intros; eapply completeness_fundamental_exp; eauto).
  pose proof (typed_insts_scoped _ _ _ HassB HlU HUt) as HUss.
  pose proof (closed_inst_sorts Γb Γ' Us HassB HΓb HΓs HΓbev HlU HUc HUss) as HTs.
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := i'); [ exact HSbΓ |].
  intros Δ σ ρ Hσ.
  pose proof (glu_ctx_env_per_env HSbΓ HRΓ Hσ) as Hρ.
  assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ)).
  (** The witness: the instance of the [Π], glued at its value *)
  destruct (glu_rel_exp_of_univ_inversion (u := ul i') HSbΓ Hwit _ _ _ Hσ) as (_ & a' & Ea' & Hper' & HPw & _).
  (** The values of the arguments, and of the [Π] at the instance and at
      the canonical environment *)
  destruct (Completeness.Modules.Filed.closed_inst_typ Γb Γ' Us (ctx_pi Δt B) i RΓ HassB HΓb HΓs HlU HUc HTs HUss
              (rel_type_of_typ (completeness_fundamental_exp _ _ _ HPi)) HRΓ ρ Hρ) as (us & a'' & b & i'' & R & Eus & Ea'' & Eb & HR).
  assert (a'' = a') as -> by (eapply functional_eval_exp; eassumption).
  (** The arguments, glued at their telescope *)
  pose proof (params_glu_args Γb SbB Γ' RΓ SbΓ Δ σ ρ Us us HassB HscB HΓb HΓs HSbB HRΓ HSbΓ Hσ HlU HUc HΓbev HUss HUs Eus)
    as HgU.
  set (Xs := List.map (fun N => N[σ]) Us) in *.
  assert (HSbB0 : EG Γb ++ ⋅ ∈ glu_ctx_env ↘ SbB) by (rewrite List.app_nil_r; exact HSbB).
  assert (Hσb : Δ ⊢ˢ sb_of_list Id Xs ® env_tele nil (List.rev Γb) us ∈ SbB).
  { eapply (glu_sub_of_list Γb ⋅ SbB nil_glu_sub_pred Δ Id nil Xs us);
      [ exact HassB | exact HSbB0 | econstructor; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ] | cbn; apply wf_sub_nil'; exact HΔ
      | exact HgU ]. }
  destruct (Heval _ _ Eus) as (w & Ew & Hw).
  (** The [Π] at the canonical environment, glued *)
  pose proof (glu_args_per_tele_args _ _ _ _ _ _ HassB HgU) as Hgus.
  destruct (rel_ctx_wf_per_ctx_env HΓb) as [RB HRB].
  assert (HEb : RB (env_tele nil (List.rev Γb) us) (env_tele nil (List.rev Γb) us)).
  { apply (tele_args_env_rel _ _ _ _ _ _ HRB HΓb); [| exact Hgus ].
    destruct (glu_args_length _ _ _ _ _ _ HgU) as [_ L]; exact L. }
  destruct (typ_values_rel (κ := ak_relevant) HPi HRB _ _ HEb) as (b1 & b2 & Eb1 & Eb2 & Hbb).
  assert (b1 = b) as -> by (eapply functional_eval_exp; eassumption).
  assert (b2 = b) as -> by (eapply functional_eval_exp; eassumption).
  destruct (per_univ_glu_univ_elem _ _ Hbb) as (Pb & Elb & Hgb).
  (** The type of the constant's application at the arguments' instances *)
  assert (EXt : (ctx_pi Δt B)[sb_of_list Id Us][σ] = (ctx_pi Δt B)[sb_of_list Id Xs])
    by (unfold Xs; apply exp_sub_sb_of_list_compose; rewrite HlU; exact HPis).
  assert (HXσ : Δ ⊢ apps X Xs : (ctx_pi Δt B)[sb_of_list Id Xs]).
  { rewrite <- EXt; unfold Xs.
    replace (apps X (List.map (fun N => N[σ]) Us)) with (apps X Us)[σ] by (rewrite apps_exp_sub, HXw; reflexivity).
    exact (sub_preserves_exp _ _ _ _ _ _ _ HXt (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ)). }
  (** The constant glued at the rest of its arguments: at all of them *)
  assert (HbaseK : forall Δ' φ Ms vs w', Δ' ⊢ᵏ φ : Δ ->
             glu_args Δ' Δt (sb_wk (sb_of_list Id Xs) φ) (env_tele nil (List.rev Γb) us) Ms vs -> Fr (us ++ vs) w' ->
             forall b0 P El, ⟦ B ⟧ env_tele nil (List.rev (Δt ++ Γb)) (us ++ vs) ↘ b0 -> DG b0 ∈ glu_univ_elem i ↘ P ↘ El ->
               (forall R, DF b0 ≈ b0 ∈ per_univ_elem i ↘ R -> R w' w') ->
               Δ' ⊢ apps X (List.map (fun N => N[φ]ʷ) Xs ++ Ms) : B[sb_of_list (sb_wk (sb_of_list Id Xs) φ) Ms] ® w' ∈ El).
  { intros Δ' φ Ms vs w' Hφ HgM Hw' b0 P El Eb0 Hgb0 HPb0.
    assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
    pose proof (glu_args_wk _ _ _ _ _ _ _ HassB HscB Hφ HgU) as HgUφ.
    destruct (glu_args_length _ _ _ _ _ _ HgUφ) as [LX LV].
    assert (HgM' : glu_args Δ' Δt (sb_of_list Id (List.map (fun N => N[φ]ʷ) Xs)) (env_tele nil (List.rev Γb) us) Ms vs).
    { pose proof (glu_args_sb_eq _ _ _ _ _ _ _ (sb_wk_sb_of_list Xs Id φ) HgM) as HgM1.
      destruct HgM1 as [L1 L2 H]; constructor; [ exact L1 | exact L2 |].
      rewrite (tele_insts_sb_of_list_base _ _ (sb_wk Id φ) Id) in H;
        [ exact H | exact HassT | rewrite LX; rewrite Nat.add_0_r in HscT; exact HscT ]. }
    pose proof (proj2 (glu_args_app Δ' Γb Δt Id nil _ Ms us vs HassB LX LV) (conj HgUφ HgM')) as Hall.
    pose proof (Hbase Δ' _ _ w' HΔ' Hall Hw' b0 P El Eb0 Hgb0 HPb0) as H.
    destruct (glu_args_length _ _ _ _ _ _ Hall) as [LA _].
    assert (HBs : exp_scoped (List.length (List.map (fun M => M[φ]ʷ) Xs ++ Ms)) B)
      by (rewrite LA; exact (proj1 (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ (proj1 HBv))))).
    replace (B[sb_of_list (sb_wk (sb_of_list Id Xs) φ) Ms]) with (B[sb_of_list Id (List.map (fun M => M[φ]ʷ) Xs ++ Ms)]);
      [ exact H |].
    eapply exp_scoped_sub_agree; [ exact HBs |]; intros x Hx.
    rewrite List.length_app in Hx; rewrite sb_of_list_app.
    destruct (Nat.lt_ge_cases x (List.length Ms)) as [Hxm | Hxm].
    - rewrite !(sb_of_list_nth Ms _ _ (a_var 0)) by lia; reflexivity.
    - replace x with (List.length Ms + (x - List.length Ms)) by lia; rewrite !sb_of_list_ge.
      rewrite (sb_wk_sb_of_list Xs Id φ (x - List.length Ms)).
      rewrite List.length_map in Hx.
      rewrite !(sb_of_list_nth (List.map _ Xs) _ _ (a_var 0)) by (rewrite List.length_map; lia); reflexivity. }
  assert (HXw' : forall φ, X[φ]ʷ = X) by (intros φ; rewrite <- exp_sub_of_wk; apply HXw).
  pose proof (ctx_pi_glu_elem_by Fr X T HXw' Happ Δt Γb SbB SbT B i HassT HSbB HSbT HT HA HCs HBv Δ (sb_of_list Id Xs) us Xs w
                Hσb ltac:(destruct (glu_args_length _ _ _ _ _ _ HgU) as [_ L]; congruence) Hw HXσ
                (fun R0 a0 Ea0 HR0 => HPER us w R0 a0 Hw Hgus ltac:(destruct (glu_args_length _ _ _ _ _ _ HgU) as [_ L]; exact L)
                                        Ea0 HR0) HbaseK b Pb Elb Eb Hgb) as Hel.
  (** Moved to the value of the instance, its type glued there *)
  destruct (per_univ_glu_univ_elem _ _ Hper') as (P' & El' & Hg').
  assert (Hba : Dom b ≈ a' ∈ per_univ i'') by (eexists; apply per_univ_elem_sym; exact HR).
  rewrite <- EXt in Hel.
  assert (EM : (apps X Us)[σ] = apps X Xs) by (rewrite apps_exp_sub, HXw; reflexivity).
  rewrite <- EM in Hel.
  pose proof (glu_univ_elem_exp_conv_universe_index Hba Hgb Hg' Hel (HPw _ _ Hg')) as Hel'.
  destruct (glu_term_value_intro Hg' HSbΓ Hσ HXt (fun _ => Ew) Hel') as (m' & Hm' & HM').
  econstructor; [ exact Ea' | exact Hm' | exact Hg' | exact HM' ].
Qed.

(** A list instance followed by a substitution: the list of the
    substituted terms over the composed base. *)
Lemma sb_of_list_compose_base : forall Ms σ τ, sb_eq (sb_of_list σ Ms ⨟ τ) (sb_of_list (σ ⨟ τ) (List.map (fun M => M[τ]) Ms)).
Proof.
  induction Ms as [| M Ms IH]; intros σ τ; cbn [sb_of_list List.map]; [ reflexivity |].
  intros x; rewrite (IH (σ,,M) τ x); apply sb_of_list_cong, sb_extend_compose.
Qed.

(** The variables of a closed telescope at an instance of it are glued at
    every renaming at the telescope's instances at them: each is the
    instance's component, its type the instance of the variable's
    ([glu_vars_tele] in the PER model). *)
Lemma glu_rel_sub_inst_vars_past : forall Γ' τ Φ Δ, all_assumptions Δ -> ctx_scoped 0 Δ -> ctx_mvc Δ ->
    glu_rel_sub_inst Γ' τ (Φ ++ Δ) ->
    forall m N T, List.nth_error (List.map (fun X => X[τ]) (vars_from (List.length Φ) (List.length Δ))) m = Some N ->
      List.nth_error (tele_insts Δ Id (List.map (fun X => X[τ]) (vars_from (List.length Φ) (List.length Δ)))) m = Some T ->
      glu_rel_exp_under_renaming Γ' N T.
Proof.
  intros * Hass Hs Hmv Hτ m N T HN HT.
  apply nth_error_map_inv in HN as (V & HV & ->).
  apply vars_from_nth_error in HV as [Hk ->].
  apply tele_insts_nth in HT as (κA & A & HA & ->).
  destruct (List.nth_error_split _ _ HA) as (l1 & l2 & Hrev & Hl1).
  assert (HΔeq : Δ = List.rev l2 ++ ce_ass κA A :: List.rev l1)
    by (rewrite <- (List.rev_involutive Δ), Hrev, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity).
  assert (Hlen : List.length Δ = List.length l2 + S m)
    by (rewrite HΔeq, List.length_app; cbn [List.length]; rewrite !List.length_rev; lia).
  assert (HsA : exp_scoped m A).
  { rewrite HΔeq in Hs; apply ctx_scoped_app in Hs as [_ Hs]; cbn in Hs; destruct Hs as [HsA _].
    rewrite List.length_rev, Nat.add_0_r in HsA; congruence. }
  assert (HmA : exp_mvc 0 A).
  { unfold ctx_mvc in Hmv; rewrite HΔeq in Hmv; apply List.Forall_app in Hmv as [_ Hmv].
    apply List.Forall_cons_iff in Hmv as [HmA _]; exact HmA. }
  (** The variable's type in the telescope past [Φ] *)
  assert (Hx : Φ ++ Δ ∋ #(List.length Φ + (List.length Δ - 1 - m)) : A[wk_shiftn (List.length Φ + List.length l2 + 1)]ʷ).
  { replace (List.length Φ + (List.length Δ - 1 - m)) with (0 + List.length (Φ ++ List.rev l2))
      by (rewrite List.length_app, List.length_rev; lia).
    replace (A[wk_shiftn (List.length Φ + List.length l2 + 1)]ʷ) with (A[wk_shift]ʷ[wk_shiftn (List.length (Φ ++ List.rev l2))]ʷ)
      by (rewrite exp_wk_wk; apply exp_wk_wk_eq; intros x; cbn; rewrite List.length_app, List.length_rev; lia).
    rewrite HΔeq, List.app_assoc; apply ctx_lookup_app_r; constructor. }
  pose proof (glu_rel_sub_inst_comps _ _ _ Hτ _ _ Hx) as H.
  replace (A[sb_of_list Id (List.firstn m (List.map (fun X => X[τ]) (vars_from (List.length Φ) (List.length Δ))))])
    with (A[wk_shiftn (List.length Φ + List.length l2 + 1)]ʷ[τ]); [ exact H |].
  rewrite <- exp_sub_of_wk, exp_sub_sub.
  eapply exp_scoped_mvc_agree; [ exact HsA | exact HmA |]; intros y Hy.
  rewrite List.firstn_map, <- sb_of_list_lt_compose by (rewrite List.length_firstn, length_vars_from; lia).
  rewrite sb_of_list_firstn_vars by lia.
  cbn [sb_compose sb_of_wk sentry_sub sentry_exp wk_shiftn exp_sub].
  f_equal; f_equal; lia.
Qed.

(** The same with nothing past the telescope. *)
Lemma glu_rel_sub_inst_vars : forall Γ' τ Δ, all_assumptions Δ -> ctx_scoped 0 Δ -> ctx_mvc Δ -> glu_rel_sub_inst Γ' τ Δ ->
    forall m N T, List.nth_error (List.map (fun X => X[τ]) (vars_from 0 (List.length Δ))) m = Some N ->
      List.nth_error (tele_insts Δ Id (List.map (fun X => X[τ]) (vars_from 0 (List.length Δ)))) m = Some T ->
      glu_rel_exp_under_renaming Γ' N T.
Proof. intros * Hass Hs Hmv Hτ; exact (glu_rel_sub_inst_vars_past Γ' τ nil Δ Hass Hs Hmv Hτ). Qed.

(** The variables of a closed telescope [Δ] past [Φ] are glued at their
    instances at the telescope's instances at them. *)
Lemma glu_vars_tele_under_sub : forall Φ Δ, all_assumptions Δ -> ctx_scoped 0 Δ -> ctx_mvc Δ -> glu_rel_ctx_types (Φ ++ Δ) ->
    forall m N T, List.nth_error (vars_from (List.length Φ) (List.length Δ)) m = Some N ->
      List.nth_error (tele_insts Δ Id (vars_from (List.length Φ) (List.length Δ))) m = Some T ->
      glu_rel_exp_under_sub (Φ ++ Δ) N T.
Proof.
  intros * Hass Hs Hmv HΦΔ m N T HN HT.
  econstructor; [ exact HΦΔ |]; intros Γ' τ Hτ.
  apply glu_rel_exp_of_under_renaming; [ exact (glu_rel_sub_inst_ctx _ _ _ Hτ) |].
  apply (glu_rel_sub_inst_vars_past Γ' τ Φ Δ Hass Hs Hmv Hτ m); [ rewrite List.nth_error_map, HN; reflexivity |].
  rewrite <- (tele_insts_sub _ 0 Id Id τ _ Hass Hs ltac:(intros; lia)), List.nth_error_map, HT; reflexivity.
Qed.

(** A term glued at its instances over a closed telescope [Δ] is glued
    at them past [Φ], at the variables of [Δ] there: an instance of
    [Φ ++ Δ] at those variables is an instance of [Δ]. *)
Lemma glu_rel_exp_under_sub_at_vars : forall Φ Δ X T, all_assumptions Δ -> ctx_scoped 0 Δ -> ctx_mvc Δ ->
    glu_rel_ctx_types (Φ ++ Δ) -> glu_rel_exp_under_sub Δ X T ->
    glu_rel_exp_under_sub (Φ ++ Δ) X[sb_of_list Id (vars_from (List.length Φ) (List.length Δ))]
      T[sb_of_list Id (vars_from (List.length Φ) (List.length Δ))].
Proof.
  intros * Hass Hs Hmv HΦΔ HX.
  econstructor; [ exact HΦΔ |]; intros Γ' τ Hτ.
  set (Vs := vars_from (List.length Φ) (List.length Δ)).
  rewrite !exp_sub_sub, !(exp_sub_sb_eq _ _ _ (sb_of_list_compose_base Vs Id τ)),
    !(exp_sub_sb_eq _ _ _ (sb_of_list_cong _ _ _ (sb_compose_id_left τ))).
  apply HX.
  assert (HΔw : ⊢ Δ ++ ⋅)
    by (rewrite List.app_nil_r; destruct (glu_rel_ctx_types_ctx _ (glu_rel_exp_under_sub_ctx _ _ _ HX)) as [? HSb];
        exact (glu_ctx_env_wf_ctx HSb)).
  pose proof (glu_rel_sub_inst_of_list Δ Γ' ⋅ τ (List.map (fun N => N[τ]) Vs) Hass
                (glu_rel_sub_inst_nil _ _ (glu_rel_sub_inst_ctx _ _ _ Hτ)) HΔw
                ltac:(unfold Vs; rewrite List.length_map, length_vars_from; reflexivity)) as H.
  rewrite List.app_nil_r in H; apply H.
  intros m N T' HN HT'.
  rewrite (tele_insts_closed_base _ τ Id _ Hass Hs) in HT'.
  exact (glu_rel_sub_inst_vars_past Γ' τ Φ Δ Hass Hs Hmv Hτ m N T' HN HT').
Qed.

(** The variables of a context glued with its types are glued at the
    instances of its telescope at them. *)
Lemma glu_rel_ctx_types_vars : forall Δ, all_assumptions Δ -> ctx_scoped 0 Δ -> ctx_mvc Δ -> glu_rel_ctx_types Δ ->
    forall m N T, List.nth_error (vars_from 0 (List.length Δ)) m = Some N ->
      List.nth_error (tele_insts Δ Id (vars_from 0 (List.length Δ))) m = Some T -> Δ ⊩ N : T.
Proof.
  intros * Hass Hs Hmv HΔ m N T HN HT.
  pose proof (glu_rel_sub_inst_vars Δ Id Δ Hass Hs Hmv (glu_rel_ctx_types_id HΔ) m N T) as H.
  rewrite (List.map_ext _ (fun X => X) exp_sub_id), List.map_id in H.
  exact (glu_rel_exp_of_under_renaming (glu_rel_ctx_types_ctx _ HΔ) (H HN HT)).
Qed.

(** An instance in any pointwise equal form. *)
Lemma glu_rel_sub_inst_sb_eq : forall Γ τ τ' Δ, sb_eq τ τ' -> glu_rel_sub_inst Γ τ Δ -> glu_rel_sub_inst Γ τ' Δ.
Proof.
  intros * E [Hτ HΓ Hc Hm].
  econstructor; [ exact (proj1 (proj2 (proj2 (presup_sub_eq (wf_sub_eq_of_sb_eq _ _ _ _ _ _ Hτ E))))) | exact HΓ | |].
  - intros x A Hx; rewrite <- !(exp_sub_sb_eq _ _ _ E); exact (Hc _ _ Hx).
  - intros x U Hx; rewrite <- (gunit_sub_Proper U U eq_refl _ _ E); exact (Hm _ _ Hx).
Qed.

(** A substitution [σ0] from [Γ0] into [Δ0] that makes an instance of
    [Δ0] of every instance of [Γ0], followed by it. *)
Definition glu_rel_sub_transformer (Γ0 : ctx) (σ0 : sub) (Δ0 : ctx) : Prop :=
  forall Γ' σ, glu_rel_sub_inst Γ' σ Γ0 -> glu_rel_sub_inst Γ' (σ0 ⨟ σ) Δ0.

(** A telescope of glued entries over [Δ0], substituted by such a
    substitution: a telescope of glued entries over [Γ0], extending it to a
    context glued with its types, the substitution lifted over it being
    one such ([glu_rel_sub_qn] in the PER model). *)
Lemma glu_tele_entries_sub : forall Pre Γ0 σ0 Δ0, all_assumptions Pre -> glu_rel_ctx_types Γ0 ->
    Γ0 ⊢ˢ σ0 : Δ0 -> glu_rel_sub_transformer Γ0 σ0 Δ0 -> glu_tele_entries Pre Δ0 ->
    glu_rel_ctx_types (tele_sub Pre σ0 ++ Γ0) /\ tele_sub Pre σ0 ++ Γ0 ⊢ˢ sb_qn (List.length Pre) σ0 : Pre ++ Δ0 /\
      glu_rel_sub_transformer (tele_sub Pre σ0 ++ Γ0) (sb_qn (List.length Pre) σ0) (Pre ++ Δ0) /\
      glu_tele_entries (tele_sub Pre σ0) Γ0.
Proof.
  induction Pre as [| e Pre IH]; intros * Hass HΓ0 Hσ0 HT HP.
  - cbn [tele_sub List.app List.length sb_qn]; split; [ exact HΓ0 | split; [ exact Hσ0 | split; [ exact HT |] ] ].
    intros [] *; discriminate.
  - apply List.Forall_cons_iff in Hass as [(κ & A & ->) Hass].
    destruct (IH _ _ _ Hass HΓ0 Hσ0 HT (glu_tele_entries_tail _ _ _ HP)) as (HC & Hρ & HTρ & HE).
    set (ρ := sb_qn (List.length Pre) σ0) in *.
    destruct (HP nil κ A Pre eq_refl) as [j HA].
    (** The new entry, glued at its instances *)
    assert (HAρ : glu_rel_exp_under_sub (tele_sub Pre σ0 ++ Γ0) A[ρ] (abs_kind_sort κ Typeω@j)).
    { econstructor; [ exact HC |]; intros Γ' σ Hσ.
      rewrite exp_sub_sub, abs_kind_sort_sub; cbn [exp_sub].
      pose proof (glu_rel_exp_under_sub_inst _ _ _ HA _ _ (HTρ _ _ Hσ)) as H.
      rewrite abs_kind_sort_sub in H; exact H. }
    cbn [tele_sub List.app List.length sb_qn centry_sub]; fold ρ.
    pose proof (glu_rel_ctx_types_extend HAρ (sort_kind_abs_kind_sort κ j)) as HC'.
    assert (HC'w : ⊢ (tele_sub Pre σ0 ++ Γ0) ▹{κ} A[ρ])
      by (destruct (glu_rel_ctx_types_ctx _ HC') as [? HSb]; exact (glu_ctx_env_wf_ctx HSb)).
    assert (Hq : (tele_sub Pre σ0 ++ Γ0) ▹{κ} A[ρ] ⊢ˢ q ρ : (Pre ++ Δ0) ▹{κ} A)
      by (eapply wf_sub_q; [ exact Hρ | exact (glu_rel_exp_under_sub_wf HA) | exact (sort_kind_abs_kind_sort κ j)
                           | exact (glu_rel_exp_under_sub_wf HAρ) ]).
    split; [ exact HC' | split; [ exact Hq | split ] ].
    + (** Lifted over the entry: the head, then the tail's instance *)
      intros Γ' σ Hσ.
      pose proof (glu_rel_sub_inst_of_wk_comp Hσ (wf_wk_shift _ _ _ _ HC'w)) as Htl.
      pose proof (HTρ _ _ Htl) as Hρσ.
      assert (E : sb_eq (q ρ ⨟ σ) (sb_extend (ρ ⨟ ((ι ↑) ⨟ σ)) (σ 0))).
      { unfold sb_q; rewrite sb_extend_compose_gen; cbn [sentry_sub].
        intros x; apply sb_extend_Proper; [| reflexivity ].
        rewrite sb_wk_compose, sb_compose_assoc; reflexivity. }
      apply (glu_rel_sub_inst_sb_eq _ _ _ _ (symmetry E)).
      apply (glu_rel_sub_inst_extend_gen (e := ce_ass κ A)); [ exact Hρσ | | | intros U Hx; inversion Hx ].
      * rewrite <- E; exact (wf_sub_compose _ _ _ _ _ _ _ Hq (glu_rel_sub_inst_typed _ _ _ Hσ)).
      * intros A' Hx; inversion Hx; subst.
        rewrite exp_sub_shift_extend.
        assert (Hx0 : (tele_sub Pre σ0 ++ Γ0) ▹{κ} A[ρ] ∋ #0 : A[ρ][↑]ʷ) by constructor.
        pose proof (glu_rel_sub_inst_comps _ _ _ Hσ _ _ Hx0) as H0.
        replace (A[ρ ⨟ ((ι ↑) ⨟ σ)]) with (A[ρ][↑]ʷ[σ])
          by (rewrite <- exp_sub_of_wk, !exp_sub_sub; reflexivity).
        exact H0.
    + intros [| e1 Δ1] κ' A' Δ2 E; cbn [List.app] in E.
      * injection E as <- <- <-; exists j; exact HAρ.
      * injection E as _ E; exact (HE _ _ _ _ E).
Qed.

(** Terms glued at their instances at the instances of a telescope are
    glued at them at the instances of an equal one ([tele_insts_rel_conv]):
    at an instance, each term moves by subtyping ([glu_rel_exp_subtyp]),
    the right telescope's entry, glued at the instance the terms before it
    make, being the witness. *)
Lemma glu_tele_insts_conv_under_sub : forall Γ Δ Δ' Ms, gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Δ ≈ Δ' ->
    all_assumptions Δ -> all_assumptions Δ' -> glu_rel_ctx_types Γ -> glu_tele_entries Δ' Γ ->
    List.length Δ' = List.length Δ -> List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T -> glu_rel_exp_under_sub Γ N T) ->
    forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ' Id Ms) k = Some T -> glu_rel_exp_under_sub Γ N T.
Proof.
  induction Δ as [| e Δ IH]; intros Δ' Ms HX Ha Ha' HΓ HE' Hll Hl HMs k N T HN HT.
  - destruct Ms; [ destruct k; discriminate | discriminate ].
  - destruct Δ' as [| e' Δ']; [ discriminate |].
    inversion Ha as [| ? ? (κ & A & ->) HaΔ]; subst; inversion Ha' as [| ? ? (κ' & A' & ->) HaΔ']; subst.
    cbn [List.length] in Hll, Hl.
    inversion HX; subst.
    match goal with
    | H : gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Δ ≈ Δ', H' : gc_deps ⍮ gc_stack ⍮ Δ ++ Γ ⊢ A ⊆ A' |- _ => rename H into HX0, H' into HAA'
    end.
    rename κ' into κ.
    destruct (List.exists_last (l := Ms) ltac:(intros ->; cbn in Hl; discriminate)) as (Ms0 & M & ->).
    rewrite List.length_app in Hl; cbn in Hl.
    assert (Hl0 : List.length Ms0 = List.length Δ) by lia.
    assert (Hti : forall X Y, all_assumptions Y -> List.length Ms0 = List.length Y ->
               tele_insts (ce_ass κ X :: Y) Id (Ms0 ++ M :: nil) = tele_insts Y Id Ms0 ++ X[sb_of_list Id Ms0] :: nil).
    { intros X Y HY HlY; change (ce_ass κ X :: Y) with ((ce_ass κ X :: nil) ++ Y).
      rewrite tele_insts_app by (try exact HY; lia); reflexivity. }
    assert (HlT : forall Y, all_assumptions Y -> List.length Ms0 = List.length Y -> List.length (tele_insts Y Id Ms0) = List.length Y)
      by (intros Y HY HlY; rewrite length_tele_insts by exact HY; lia).
    pose proof (HlT _ HaΔ Hl0) as HlT0; pose proof (HlT _ HaΔ' ltac:(lia)) as HlT0'.
    rewrite (Hti _ _ HaΔ' ltac:(lia)) in HT.
    assert (HMs0 : forall k N T, List.nth_error Ms0 k = Some N -> List.nth_error (tele_insts Δ Id Ms0) k = Some T ->
                     glu_rel_exp_under_sub Γ N T).
    { intros k0 N0 T0 HN0 HT0.
      assert (Hk0 : k0 < List.length Δ) by (rewrite <- HlT0; apply List.nth_error_Some; congruence).
      apply (HMs k0); [ rewrite List.nth_error_app1 by lia; exact HN0 | rewrite (Hti _ _ HaΔ Hl0), List.nth_error_app1 by lia; exact HT0 ]. }
    pose proof (IH _ _ HX0 HaΔ HaΔ' HΓ (glu_tele_entries_tail _ _ _ HE') ltac:(lia) Hl0 HMs0) as HMs0'.
    destruct (Nat.lt_ge_cases k (List.length Δ')) as [Hk | Hk].
    + rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
      exact (HMs0' _ _ _ HN HT).
    + assert (k = List.length Δ') as ->.
      { assert (Hk' : k < List.length (Ms0 ++ M :: nil)) by (apply List.nth_error_Some; congruence).
        rewrite List.length_app in Hk'; cbn in Hk'; lia. }
      rewrite List.nth_error_app2, HlT0', Nat.sub_diag in HT by lia; injection HT as <-.
      rewrite List.nth_error_app2 in HN by lia.
      replace (List.length Δ' - List.length Ms0) with 0 in HN by lia; injection HN as <-.
      pose proof (HMs (List.length Δ) M (A[sb_of_list Id Ms0])) as HM.
      rewrite List.nth_error_app2 in HM by lia.
      rewrite (Hti _ _ HaΔ Hl0), List.nth_error_app2 in HM by lia.
      rewrite Hl0, HlT0, !Nat.sub_diag in HM.
      specialize (HM eq_refl eq_refl).
      destruct (HE' nil κ A' Δ' eq_refl) as [j HA'].
      pose proof (ext_eq_ctx_right _ _ _ _ _ HX0) as HΔ'w.
      assert (HΔw : ⊢ Δ ++ Γ) by exact (proj1 (presup_subtyp HAA')).
      apply (glu_rel_exp_under_sub_conv_typ (A := A[sb_of_list Id Ms0])); [| exact HM ].
      intros Γ' τ Hτ H.
      set (σs := sb_of_list τ (List.map (fun X => X[τ]) Ms0)).
      assert (Eσ : forall X, X[sb_of_list Id Ms0][τ] = X[σs])
        by (intros X; unfold σs; rewrite exp_sub_sub, (exp_sub_sb_eq _ _ _ (sb_of_list_compose_base _ Id τ)),
                                    (exp_sub_sb_eq _ _ _ (sb_of_list_cong _ _ _ (sb_compose_id_left τ))); reflexivity).
      (** The instances the terms before make, of both telescopes *)
      assert (Hinst : forall Y, all_assumptions Y -> ⊢ Y ++ Γ -> ctx_scoped (List.length Γ) Y -> List.length Ms0 = List.length Y ->
                (forall k N T, List.nth_error Ms0 k = Some N -> List.nth_error (tele_insts Y Id Ms0) k = Some T ->
                   glu_rel_exp_under_sub Γ N T) ->
                glu_rel_sub_inst Γ' σs (Y ++ Γ)).
      { intros Y HY HYw HYs HlY HYMs.
        apply glu_rel_sub_inst_of_list; [ exact HY | exact Hτ | exact HYw | rewrite List.length_map; exact HlY |].
        intros k0 N0 T0 HN0 HT0.
        rewrite <- (tele_insts_sub Y (List.length Γ) Id τ τ Ms0 HY HYs ltac:(intros; reflexivity)) in HT0.
        apply nth_error_map_inv in HN0 as (N1 & HN1 & ->); apply nth_error_map_inv in HT0 as (T1 & HT1 & ->).
        exact (glu_rel_exp_under_sub_inst_renaming (HYMs _ _ _ HN1 HT1) Hτ). }
      destruct (wf_ext_eq_scoped _ _ _ _ _ HX0) as (_ & HsΔ & HsΔ').
      pose proof (Hinst _ HaΔ HΔw HsΔ Hl0 HMs0) as HinstΔ.
      pose proof (Hinst _ HaΔ' HΔ'w HsΔ' ltac:(lia) HMs0') as HinstΔ'.
      pose proof (glu_rel_exp_under_sub_inst _ _ _ HA' _ _ HinstΔ') as HA'τ; rewrite abs_kind_sort_sub in HA'τ; cbn [exp_sub] in HA'τ.
      rewrite !Eσ in *.
      exact (glu_rel_exp_subtyp H HA'τ (sort_kind_type_sort _ _ (sort_kind_abs_kind_sort κ j))
               (sub_preserves_subtyp _ _ _ _ _ _ _ HAA' (glu_rel_sub_inst_typed _ _ _ HinstΔ))).
Qed.

(** ** A Record's Type Former Applied *)

(** A record's type former at terms glued at their instances at the
    instances of its parameters' telescope is a type of a large universe
    glued at its instances: at an instance, the terms' instances are an
    instance of the parameters, where the sort is glued
    ([glued_sort]). *)
Lemma glu_record_apps : forall qr R Ψ Ms, record_lookup gc_deps gc_stack qr = Some R -> glu_record_decl R ->
    glu_rel_ctx_types Ψ -> List.length Ms = List.length (record_params R) ->
    (forall m N T, List.nth_error Ms m = Some N -> List.nth_error (tele_insts (record_params R) Id Ms) m = Some T ->
       glu_rel_exp_under_sub Ψ N T) ->
    exists j : nat, glu_rel_exp_under_sub Ψ (apps (a_record qr) Ms) Typeω@j.
Proof.
  intros qr R Ψ Ms HlR HGR HΨ HMl HMs.
  assert (Hg : ⊢ᵍ gc_deps ⍮ gc_stack)
    by (destruct (glu_rel_ctx_types_ctx _ HΨ) as [? HSb]; eapply ctx_wf_gctx; exact (glu_ctx_env_wf_ctx HSb)).
  pose proof (record_model_at qr R Hg HlR) as Hmodel.
  pose proof (model_closed _ _ Hmodel) as Hc; pose proof (model_params_ass _ _ Hmodel) as Hpa.
  pose proof (closed_params _ Hc) as Hps.
  pose proof (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ HlR) as Ht.
  pose proof (params_mvc _ (typed_mvc _ _ _ Ht)) as Hpm.
  destruct (record_typed_ty _ _ _ Ht) as [i0 Hty].
  pose proof (glued_params _ HGR) as HP.
  destruct (glu_rel_ctx_types_ctx _ HP) as [SbP HSbP].
  assert (HSbP0 : EG record_params R ++ ⋅ ∈ glu_ctx_env ↘ SbP) by (rewrite List.app_nil_r; exact HSbP).
  destruct (glu_ctx_env_entries_valid _ _ _ Hpa HSbP0 i0) as (i & Hji & _).
  assert (Hi : ⋅ ⊢ record_ty R : Typeω@i) by (eapply lift_exp_ge; [ exact Hji | exact Hty ]).
  pose proof Hi as Hi'; unfold record_ty in Hi'.
  destruct (ctx_pi_split_typed _ _ _ _ Hpa Hi') as [HCs0 _].
  pose proof (HCs0 nil _ eq_refl) as HS0; cbn [ctx_pi_at] in HS0.
  pose proof HS0 as HS; rewrite List.app_nil_r in HS.
  (** The sort, a type of a large universe glued at its instances *)
  assert (Hj : exists j : nat, forall Γ' Ms', glu_rel_sub_inst Γ' (sb_of_list Id Ms') (record_params R) ->
                 (Γ' ⊩ apps (a_record qr) Ms' : (record_sort R)[sb_of_list Id Ms'] -> Γ' ⊩ apps (a_record qr) Ms' : Typeω@j) /\
                 Γ' ⊩ (record_sort R)[sb_of_list Id Ms'] : Typeω@i).
  { destruct (glued_sort _ HGR) as [[i1 Heq] | (L & n & Heq & HL)]; rewrite Heq in HS |- *; cbn [exp_sub].
    - exists i1; intros Γ' Ms' Hinst; split; [ intros H; exact H |].
      eapply glu_rel_exp_subtyp; [ exact (glu_rel_exp_typ (glu_rel_sub_inst_ctx _ _ _ Hinst))
                                 | exact (glu_rel_exp_typ (glu_rel_sub_inst_ctx _ _ _ Hinst)) | constructor |].
      pose proof (sub_preserves_subtyp _ _ _ _ _ _ _ (wf_typ_inversion HS) (glu_rel_sub_inst_typed _ _ _ Hinst)) as H'.
      cbn [exp_sub] in H'; exact H'.
    - exists 0; intros Γ' Ms' Hinst.
      pose proof (glu_rel_exp_under_sub_inst _ _ _ HL _ _ Hinst) as HLτ; cbn [exp_sub] in HLτ.
      split; [ intros H; exact (glu_rel_exp_kind_sort_small_large (κ := ak_relevant) HLτ H) |].
      eapply glu_rel_exp_subtyp; [ eapply glu_rel_exp_univ_lvl; exact HLτ | exact (glu_rel_exp_typ (glu_rel_sub_inst_ctx _ _ _ Hinst))
                                 | constructor |].
      pose proof (sub_preserves_subtyp _ _ _ _ _ _ _ (wf_univ_inversion HS) (glu_rel_sub_inst_typed _ _ _ Hinst)) as H'.
      cbn [exp_sub] in H'; exact H'. }
  destruct Hj as [j Hj].
  exists j; econstructor; [ exact HΨ |]; intros Γ' τ Hτ.
  pose proof (glu_rel_sub_inst_ctx _ _ _ Hτ) as HΓ'.
  assert (HΓ'w : ⊢ Γ') by (destruct HΓ' as [? HSb]; exact (glu_ctx_env_wf_ctx HSb)).
  set (Ms' := List.map (fun N => N[τ]) Ms).
  rewrite apps_exp_sub; cbn [exp_sub]; fold Ms'.
  assert (HlM' : List.length Ms' = List.length (record_params R)) by (unfold Ms'; rewrite List.length_map; exact HMl).
  assert (HUs : forall m N T, List.nth_error Ms' m = Some N -> List.nth_error (tele_insts (record_params R) Id Ms') m = Some T ->
                  glu_rel_exp_under_renaming Γ' N T).
  { intros m N T HN HT; unfold Ms' in HN, HT.
    rewrite <- (tele_insts_sub _ 0 Id Id τ Ms Hpa Hps ltac:(intros; lia)) in HT.
    apply nth_error_map_inv in HN as (N0 & HN0 & ->); apply nth_error_map_inv in HT as (T0 & HT0 & ->).
    exact (glu_rel_exp_under_sub_inst_renaming (HMs _ _ _ HN0 HT0) Hτ). }
  assert (Hinst : glu_rel_sub_inst Γ' (sb_of_list Id Ms') (record_params R)).
  { rewrite <- (List.app_nil_r (record_params R)).
    apply glu_rel_sub_inst_of_list; [ exact Hpa | exact (glu_rel_sub_inst_nil _ _ HΓ') | rewrite List.app_nil_r
                                   | exact HlM' | exact HUs ].
    exact (presup_exp_ctx HS). }
  assert (HUt : forall m N T, List.nth_error Ms' m = Some N -> List.nth_error (tele_insts (record_params R) Id Ms') m = Some T ->
                  Γ' ⊢ N : T)
    by (intros; eapply glu_rel_exp_to_wf_exp, glu_rel_exp_of_under_renaming; [ exact HΓ' | eauto ]).
  assert (HXt : Γ' ⊢ apps (a_record qr) Ms' : (record_sort R)[sb_of_list Id Ms']).
  { eapply wf_apps_closed_pi; [ exact Hpa | exact Hps | exact (closed_sort _ Hc) | exact HS | exact HΓ'w | | exact HlM' | exact HUt ].
    exact (record_former_wf qr R Hg HlR _ HΓ'w). }
  destruct (Hj _ _ Hinst) as [Hconv Hwit]; apply Hconv.
  (** The type former at the instances *)
  pose proof (model_valid _ _ Hmodel) as HV0.
  assert (HV : record_params R ⊨ apps (a_record qr) (vars_from 0 (List.length (record_params R))) : record_sort R).
  { apply completeness_fundamental_exp.
    pose proof (glu_rel_ctx_types_vars _ Hpa Hps Hpm HP) as Hvs.
    assert (HPw : ⊢ record_params R) by exact (presup_exp_ctx HS).
    pose proof (wf_apps_closed_pi _ _ _ _ _ _ (a_record qr) (vars_from 0 (List.length (record_params R))) Hpa Hps (closed_sort _ Hc) HS HPw
                  (record_former_wf qr R Hg HlR _ HPw) ltac:(rewrite length_vars_from; reflexivity)
                  ltac:(intros; eapply glu_rel_exp_to_wf_exp, Hvs; eassumption)) as H.
    rewrite (exp_at_vars _ _ _ (closed_sort _ Hc) (sort_mvc _ (typed_mvc _ _ _ Ht))) in H.
    rewrite (exp_wk_id_ext (record_sort R) _ wk_shiftn_zero) in H; exact H. }
  eapply (glu_rel_exp_const_apps (fun xs w => w = d_record qr xs) (a_record qr) (record_params R))
    with (Δt := nil) (Γb := record_params R) (SbB := SbP) (SbT := SbP) (i := i);
    [ reflexivity | | exact Hpa | exact Hps | exact (params_valid _ HV0) | exact (params_evaluated_valid _ HV0) | exact HSbP | exact HSbP
    | exists nil; reflexivity | intros [] ? ? ? E; discriminate | | | exact HV | | | | exact HΓ' | exact HlM'
    | intros m N T HN HT; exact (glu_rel_exp_of_under_renaming HΓ' (HUs m N T HN HT)) | exact Hwit | exact HXt ].
  - intros Δ1 Γ'' Sb' Δ'' σ' xs x w HT _ _ HlΓ ->.
    exists (d_record qr (xs ++ x :: nil)); split; [| reflexivity ].
    eapply eval_app_record; [ exact HlR |].
    assert (List.length Γ'' <= List.length (record_params R)) by (rewrite HT, List.length_app; lia).
    lia.
  - intros Δ1 Δ2 E; symmetry in E; apply List.app_eq_nil in E as [-> ->]; exact HS.
  - cbn [List.app]; rewrite <- (List.app_nil_r (record_params R)) at 1.
    exact (record_sort_entry_valid R HGR i HS0).
  - intros xs w -> Hlx; rewrite <- Hlx.
    apply (Completeness.Records.Model.eval_record_apps qr R HlR); [| rewrite length_vars_from; exact Hlx ].
    pose proof (Decl.eval_vars_from_args (tele_entries nil (List.rev (record_params R)) xs) nil nil) as H.
    rewrite List.app_nil_r, tele_entries_values, Decl.tele_entries_length in H; cbn [List.length] in H; exact H.
  - intros Δ' Ms0 vs w' HΔ' HgM -> b P El Eb Hgb HPb.
    exact (record_former_base qr R Hg HlR HGR i0 Hty Δ' Ms0 vs i b P El HΔ' HgM Eb Hgb HPb).
  - intros ρ us Eus; exists (d_record qr us); split; [| reflexivity ].
    apply (Completeness.Records.Model.eval_record_apps qr R HlR); [ exact Eus | exact HlM' ].
Qed.

(** ** A Group's Type Formers Applied *)

Section IndApps.
  Variables (p : qname) (D : ind_decl).
  Hypotheses (Hg : valid_group p D) (HG : glu_ind_decl D).
  (** The ends of the recursive arguments' shapes are glued ([Comps]) *)
  Hypothesis (Hselfs : glu_self_ends_all p D).
  Let Hl := valid_group_lookup _ _ Hg.
  Let HD := valid_group_valid _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hdt := valid_group_typed _ _ Hg.
  Let Hsu := valid_group_sort _ _ Hg.
  Let Hass := valid_group_ass _ _ Hg.

  (** A type of the group's sort over the uniform parameters and [Ψ],
      glued at its instances, is a type of a large universe glued at them:
      the sort is one, or small at a level glued at its instances
      ([glu_ind_decl_lvl]), weakened. *)
  Lemma glu_group_sort_large : forall Ψ κ A,
      glu_rel_exp_under_sub (Ψ ++ ind_uparams D) A (abs_kind_sort κ (ind_sort D)[wk_shiftn (List.length Ψ)]ʷ) ->
      exists i : nat, glu_rel_exp_under_sub (Ψ ++ ind_uparams D) A (abs_kind_sort κ Typeω@i).
  Proof.
    intros * HA.
    destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq in HA; cbn [exp_wk] in HA; [ exists i0; exact HA |].
    destruct (glu_ind_decl_lvl _ HG) as [n Hn]; rewrite Heq in Hn; cbn [ind_sort_lvl] in Hn.
    pose proof (wf_wk_shiftn_app' _ _ _ _ (presup_exp_ctx (glu_rel_exp_under_sub_wf HA))) as Hw.
    pose proof (glu_rel_exp_under_sub_wk Hn (glu_rel_exp_under_sub_ctx _ _ _ HA) Hw) as Hn'; cbn [exp_wk] in Hn'.
    exists 0; apply (glu_rel_exp_under_sub_conv_typ (A := abs_kind_sort κ Type⟨t[wk_shiftn (List.length Ψ)]ʷ⟩)); [| exact HA ].
    intros Γ' τ Hτ H; rewrite !abs_kind_sort_sub in *; cbn [exp_sub] in *.
    pose proof (glu_rel_exp_under_sub_inst _ _ _ Hn' _ _ Hτ) as HL; cbn [exp_sub] in HL.
    exact (glu_rel_exp_kind_sort_small_large HL H).
  Qed.

  (** The sort, over a member's parameters, is a type of a large universe
      glued at its instances. *)
  Lemma glu_group_sort_typ : forall k Mk, ind_member D k = Some Mk ->
      exists j : nat, glu_rel_exp_under_sub (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ Typeω@j.
  Proof.
    intros * HM.
    pose proof (glu_ind_decl_params _ HG _ _ HM) as HP.
    destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq; cbn [exp_wk].
    - exists (S i0); econstructor; [ exact HP |]; intros Γ' τ Hτ; cbn [exp_sub].
      exact (glu_rel_exp_typ (glu_rel_sub_inst_ctx _ _ _ Hτ)).
    - destruct (glu_ind_decl_lvlP _ HG _ _ HM) as [n Hn]; rewrite Heq in Hn; cbn [ind_sort_lvl exp_wk] in Hn.
      exists 0; econstructor; [ exact HP |]; intros Γ' τ Hτ; cbn [exp_sub].
      pose proof (glu_rel_exp_under_sub_inst _ _ _ Hn _ _ Hτ) as HL; cbn [exp_sub] in HL.
      exact (glu_rel_exp_kind_sort_small_large (κ := ak_relevant) (glu_rel_exp_succl HL) (glu_rel_exp_univ_lvl HL)).
  Qed.

  (** A member's type over the uniform parameters is a type of a large
      universe glued at its instances. *)
  (** A member's non-uniform parameters are glued entries over the
      uniform ones ([glu_ind_decl_nparams], [glu_group_sort_large]). *)
  Lemma glu_nparams_entries : forall j Mj, ind_member D j = Some Mj -> glu_tele_entries (im_nparams Mj) (ind_uparams D).
  Proof.
    intros * HMj Δ1 κ A Δ2 E.
    assert (Hn : List.nth_error (List.rev (im_nparams Mj)) (List.length Δ2) = Some (ce_ass κ A)).
    { rewrite E, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc.
      rewrite List.nth_error_app2 by (rewrite List.length_rev; lia).
      rewrite List.length_rev, Nat.sub_diag; reflexivity. }
    pose proof (glu_ind_decl_nparams _ HG _ _ _ _ _ HMj Hn) as HA.
    assert (EP : nparams_prefix Mj (List.length Δ2) = Δ2).
    { unfold nparams_prefix; rewrite E, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc.
      rewrite firstn_app_exact by (rewrite List.length_rev; reflexivity); apply List.rev_involutive. }
    rewrite EP in HA.
    (** The non-uniform parameters are relevant *)
    rewrite (decl_typed_nparams_kind _ _ _ Hdt _ _ _ _ _ _ HMj E).
    exact (glu_group_sort_large Δ2 ak_relevant A HA).
  Qed.

  Lemma glu_self_ty_under_sub : forall j Mj, ind_member D j = Some Mj ->
      exists i : nat, glu_rel_exp_under_sub (ind_uparams D) (self_ty D Mj) Typeω@i.
  Proof.
    intros * HMj.
    destruct (glu_group_sort_typ _ _ HMj) as [i HS].
    unfold self_ty; unfold im_params in HS.
    exact (glu_rel_exp_under_sub_ctx_pi _ _ _ i (decl_closed_nparams_ass D Hc _ _ HMj) (glu_nparams_entries _ _ HMj) HS).
  Qed.

  (** A member's sort, over its parameters, at the parameters as
      variables. *)
  Lemma sort_shift_at_vars : forall Mk, (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ[sb_of_list Id (vars_from 0 (im_np D Mk))]
                                        = (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ.
  Proof.
    intros Mk; rewrite <- !exp_sub_of_wk, exp_sub_sub.
    eapply exp_scoped_mvc_agree; [ exact (decl_closed_sort _ Hc) | exact (decl_mvc_sort _ (decl_typed_mvc _ _ _ Hdt)) |].
    intros x Hx; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
    rewrite sb_of_list_vars by (unfold im_np, ind_nu in *; lia); cbn; f_equal; lia.
  Qed.

  (** A declared member's type former at its parameters as variables is
      valid at its sort. *)
  Lemma valid_ind_apps_vars : forall k Mk pm, ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
      im_params D Mk ⊨ apps (a_ind p k) (vars_from 0 (im_np D Mk)) : (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ.
  Proof.
    intros k Mk pm HM Hh.
    pose proof (decl_closed_params_ass D k Mk Hc HM) as Hpa.
    pose proof (decl_closed_params D k Mk Hc HM) as Hps.
    pose proof (decl_typed_mvc _ _ _ Hdt) as Hmv.
    assert (Hpm : ctx_mvc (im_params D Mk))
      by (unfold im_params, ctx_mvc; apply List.Forall_app; split;
          [ exact (proj1 (decl_mvc_members _ Hmv _ _ HM)) | exact (decl_mvc_uparams _ Hmv) ]).
    destruct (valid_ind_decl_sort D HD) as [i HS].
    pose proof (valid_ind_decl_params D HD k Mk HM) as HP.
    pose proof HP as HP'; unfold im_params in HP'.
    pose proof (rel_wk_under_ctx_shiftn _ _ HP') as Hw; rewrite length_im_nparams in Hw.
    assert (HB : im_params D Mk ⊨ (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ : Typeω@i)
      by (pose proof (rel_exp_under_ctx_wk Hw HS) as H; cbn [exp_wk] in H; exact H).
    destruct (closed_app_sem _ _ Hpa HP HP) as [HPP _].
    pose proof (closed_app_valid _ _ _ _ _ Hpa HP HP HB) as HBP.
    pose proof (closed_weaken_valid _ _ _ _ HP (valid_exp_under_ctx_ind D HD Hc Hsu p Hl Hass k Mk pm HM Hh)) as HMv.
    unfold ind_ty in HMv.
    assert (Hl0 : List.length (vars_from 0 (im_np D Mk)) = List.length (im_params D Mk))
      by (rewrite length_vars_from, length_im_params; reflexivity).
    pose proof (valid_vars_tele nil (im_params D Mk) Hpa Hps Hpm HP) as Hvars; cbn [List.length List.app] in Hvars.
    rewrite length_im_params in Hvars.
    assert (Hvs : List.Forall (exp_scoped (List.length (im_params D Mk))) (vars_from 0 (im_np D Mk))).
    { apply List.Forall_forall; intros N HN; destruct (List.In_nth_error _ _ HN) as [m Hm].
      apply vars_from_nth_error in Hm as [Hm ->]; cbn; rewrite length_im_params; lia. }
    pose proof (rel_exp_apps_ctx_pi_n _ (im_params D Mk) (im_params D Mk) _ i (a_ind p k) (vars_from 0 (im_np D Mk)) eq_refl Hpa
                  HPP HBP HMv Hl0 Hvars Hvs) as HR.
    rewrite sort_shift_at_vars in HR; exact HR.
  Qed.

  (** A declared member's type former at its parameters as variables, at
      the canonical environment of their values. *)
  Lemma eval_ind_apps_vars : forall k Mk C xs, ind_member D k = Some Mk -> List.length xs <= im_np D Mk ->
      ⟦ apps (a_ind p k) (vars_from 0 (List.length xs)) ⟧ env_tele nil C xs ↘ d_ind p k xs.
  Proof.
    intros * HM Hlx.
    apply Modules.eval_apps_exp; exists (d_ind p k nil); split; [ constructor |].
    apply Modules.eval_app_args_ind; exists xs; split; [| exact (eval_apps_indty p D k Mk xs nil Hl HM ltac:(cbn; lia)) ].
    pose proof (Decl.eval_vars_from_args (tele_entries nil C xs) nil nil) as H.
    rewrite List.app_nil_r, tele_entries_values, Decl.tele_entries_length in H; cbn [List.length] in H; exact H.
  Qed.

  (** A declared member's type former at terms glued at the instances of
      the outer part [Γb] of its parameters (the uniform ones, or all of
      them) is glued at the instance of the [Π] over the rest. *)
  Lemma glu_rel_exp_ind_apps_gen : forall k Mk pm Δt Γb Γ' Us (i' : nat), ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
      im_params D Mk = Δt ++ Γb -> Γb = ind_uparams D \/ Δt = nil ->
      ⊩ Γ' -> List.length Us = List.length Γb ->
      (forall m N T', List.nth_error Us m = Some N -> List.nth_error (tele_insts Γb Id Us) m = Some T' -> Γ' ⊩ N : T') ->
      Γ' ⊩ (ctx_pi Δt (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ)[sb_of_list Id Us] : Typeω@i' ->
      Γ' ⊢ apps (a_ind p k) Us : (ctx_pi Δt (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ)[sb_of_list Id Us] ->
      Γ' ⊩ apps (a_ind p k) Us : (ctx_pi Δt (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ)[sb_of_list Id Us].
  Proof.
    intros k Mk pm Δt Γb Γ' Us i' HM Hh EP Hcase HΓ' HlU HUs Hwit HXt.
    pose proof (decl_closed_params_ass D k Mk Hc HM) as HassP.
    pose proof (decl_closed_params D k Mk Hc HM) as HsP.
    assert (Hg0 : ⊢ᵍ gc_deps ⍮ gc_stack) by (eapply ctx_wf_gctx; exact (member_params_wf _ _ _ _ _ Hdt HM)).
    assert (HΔ0 : ⊢ ⋅) by (constructor; exact Hg0).
    assert (Hlt : k < ind_ndecl D) by (eapply decl_member_lt; [ exact HΔ0 | eassumption | eassumption | eassumption ]).
    destruct (ind_ty_typed0 _ _ _ _ _ Hdt HM) as [j Hj].
    destruct (glu_rel_ctx_types_ctx _ (glu_ind_decl_params _ HG _ _ HM)) as [SbP HSbP].
    pose proof HassP as HassP'; rewrite EP in HassP'.
    pose proof HassP' as HassP''; unfold all_assumptions in HassP''; apply List.Forall_app in HassP'' as [HassT HassB].
    pose proof HSbP as HSbT; rewrite EP in HSbT.
    destruct (glu_ctx_env_entries_valid _ _ _ HassT HSbT j) as (i & Hji & HAents).
    destruct (glu_ctx_env_suffix _ _ _ HassT HSbT) as [SbB HSbB].
    assert (Hi : ⋅ ⊢ ind_ty D Mk : Typeω@i) by (eapply lift_exp_ge; [ exact Hji | exact Hj ]).
    pose proof Hi as Hi'; unfold ind_ty in Hi'.
    destruct (ctx_pi_split_typed _ _ _ _ HassP Hi') as [HCs0 _].
    pose proof (valid_ind_decl_params D HD k Mk HM) as HP; rewrite EP in HP.
    pose proof (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HP) as HPb.
    assert (HBev : exists l, rel_params_evaluated ⋅ Γb l).
    { apply rel_params_evaluated_of_entries; intros Δ1 κ A Δ2 E.
      destruct (im_params_evaluated D HD k Mk HM (Δt ++ Δ1) κ A Δ2 ltac:(rewrite EP, E, List.app_assoc; reflexivity)) as [l Hl0].
      exists l; rewrite List.app_nil_r; exact Hl0. }
    assert (Hlen : forall C, im_params D Mk = C -> List.length C = im_np D Mk) by (intros C <-; apply length_im_params).
    eapply (glu_rel_exp_const_apps (fun xs w => w = d_ind p k xs) (a_ind p k) (im_params D Mk))
      with (Δt := Δt) (Γb := Γb) (SbB := SbB) (SbT := SbP) (i := i);
      [ reflexivity | | exact HassP' | rewrite <- EP; exact HsP | exact HPb | exact HBev | exact HSbB | rewrite <- EP; exact HSbP
      | exists nil; rewrite EP; reflexivity | exact HAents | | | | | | | exact HΓ' | exact HlU | exact HUs | exact Hwit | exact HXt ].
    - (** One more argument: the former at it *)
      intros Δ1 Γ'' Sb' Δ'' σ' xs x w HT _ _ HlΓ ->.
      exists (d_ind p k (xs ++ x :: nil)); split; [| reflexivity ].
      eapply eval_app_indty; [ exact Hl | exact HM |].
      assert (List.length Γ'' <= List.length (im_params D Mk)) by (rewrite HT, List.length_app; lia).
      rewrite length_im_params in *; lia.
    - intros Δ1 Δ2 Heq.
      pose proof (HCs0 Δ1 (Δ2 ++ Γb) ltac:(rewrite EP, Heq, List.app_assoc; reflexivity)) as H.
      rewrite List.app_nil_r in H; exact H.
    - pose proof (sort_entry_valid D HG Hsu k Mk i HM (HCs0 nil _ eq_refl)) as H.
      rewrite List.app_nil_r, EP in H; exact H.
    - destruct Hcase as [-> | ->].
      + assert (Δt = im_nparams Mk) as -> by (unfold im_params in EP; apply List.app_inv_tail in EP; congruence).
        exact (valid_self_apps D HD Hc Hsu p Hl Hass (decl_typed_order _ _ _ Hdt) (decl_typed_mvc _ _ _ Hdt) k Mk HM Hlt).
      + cbn [List.app] in EP; subst Γb; rewrite length_im_params; exact (valid_ind_apps_vars k Mk pm HM Hh).
    - intros xs w -> Hlx; rewrite <- Hlx.
      apply (eval_ind_apps_vars k Mk); [ exact HM | rewrite Hlx; pose proof (Hlen _ EP) as E; rewrite List.length_app in E; lia ].
    - intros Δ' Ms vs w' HΔ' HgM -> b P El Eb Hgb HPb'.
      rewrite <- EP in HgM, Eb.
      exact (ind_former_base p D Hl HG Hc Hdt Hsu Hass Hselfs k Mk pm Δ' _ _ i b P El HM Hh HΔ' HgM Eb Hgb HPb').
    - intros ρ us Eus; exists (d_ind p k us); split; [| reflexivity ].
      pose proof (Completeness.Inductives.Model.eval_exps_length _ _ _ Eus) as Lus.
      apply Modules.eval_apps_exp; exists (d_ind p k nil); split; [ constructor |].
      apply Modules.eval_app_args_ind; exists us; split; [ exact Eus |].
      apply (eval_apps_indty p D k Mk us nil Hl HM); cbn.
      pose proof (Hlen _ EP) as E; rewrite List.length_app in E; lia.
  Qed.

  (** A list instance of the variables of the uniform parameters
      at an instance, on a term over them: the instance. *)
  Lemma uparams_vars_inst : forall M τ, exp_scoped (ind_nu D) M -> exp_mvc 0 M ->
      M[τ] = M[sb_of_list Id (List.map (fun X => X[τ]) (vars_from 0 (ind_nu D)))].
  Proof.
    intros * Hs Hm; eapply exp_scoped_mvc_agree; [ exact Hs | exact Hm |]; intros x Hx.
    rewrite <- sb_of_list_lt_compose by (rewrite length_vars_from; exact Hx).
    rewrite sb_of_list_vars by exact Hx; reflexivity.
  Qed.

  (** A declared member's type former at the uniform parameters as
      variables is glued at its instances at the member's type. *)
  Lemma glu_self_apps_under_sub : forall j Mj, ind_member D j = Some Mj -> j < ind_ndecl D ->
      glu_rel_exp_under_sub (ind_uparams D) (apps (a_ind p j) (vars_from 0 (ind_nu D))) (self_ty D Mj).
  Proof.
    intros * HMj Hj.
    destruct (member_lt_decl _ _ _ _ _ Hdt HMj Hj) as [pm Hh].
    destruct (glu_self_ty_under_sub _ _ HMj) as [i HST].
    pose proof (decl_closed_ass _ Hc) as HassU.
    pose proof (decl_closed_uparams _ Hc) as HsU.
    pose proof (decl_mvc_uparams _ (decl_typed_mvc _ _ _ Hdt)) as HmU.
    econstructor; [ exact (glu_rel_exp_under_sub_ctx _ _ _ HST) |]; intros Γ' τ Hτ.
    pose proof (glu_rel_sub_inst_ctx _ _ _ Hτ) as HΓ'.
    set (Us := List.map (fun X => X[τ]) (vars_from 0 (ind_nu D))).
    assert (EU : (apps (a_ind p j) (vars_from 0 (ind_nu D)))[τ] = apps (a_ind p j) Us) by (rewrite apps_exp_sub; reflexivity).
    assert (ET : (self_ty D Mj)[τ] = (self_ty D Mj)[sb_of_list Id Us])
      by exact (uparams_vars_inst _ τ (self_ty_scoped _ _ _ Hc HMj) (self_ty_mvc _ _ _ Hc (decl_typed_mvc _ _ _ Hdt) HMj)).
    assert (HlU : List.length Us = List.length (ind_uparams D)) by (unfold Us; rewrite List.length_map, length_vars_from; reflexivity).
    assert (HUs : forall m N T, List.nth_error Us m = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) m = Some T ->
                    Γ' ⊩ N : T)
      by (intros m N T HN HT; exact (glu_rel_exp_of_under_renaming HΓ' (glu_rel_sub_inst_vars Γ' τ _ HassU HsU HmU Hτ m N T HN HT))).
    pose proof (glu_rel_exp_under_sub_inst _ _ _ HST _ _ Hτ) as HSTτ; cbn [exp_sub] in HSTτ.
    rewrite EU, ET.
    apply (glu_rel_exp_ind_apps_gen j Mj pm (im_nparams Mj) (ind_uparams D) Γ' Us i HMj Hh eq_refl (or_introl eq_refl) HΓ' HlU HUs);
      fold (self_ty D Mj); [ rewrite <- ET; exact HSTτ |].
    eapply wf_apps_closed_pi; [ exact HassU | exact HsU | exact (self_ty_scoped _ _ _ Hc HMj) | exact (glu_rel_exp_under_sub_wf HST)
                              | destruct HΓ' as [? HSb]; exact (glu_ctx_env_wf_ctx HSb) | | exact HlU
                              | intros; eapply glu_rel_exp_to_wf_exp; eauto ].
    unfold self_ty; rewrite <- ctx_pi_app; change (ctx_pi (im_nparams Mj ++ ind_uparams D) (ind_sort D)[wk_shiftn (im_nn Mj)]ʷ)
      with (ind_ty D Mj).
    eapply wf_ind; [ destruct HΓ' as [? HSb]; exact (glu_ctx_env_wf_ctx HSb) | eassumption .. ].
  Qed.

  (** A declared member's type former at terms glued at their instances
      at the instances of its parameters' telescope is a type of a large
      universe glued at its instances ([valid_group_valid_ind_apps]): at an
      instance, the terms' instances are an instance of the parameters,
      where the sort is glued ([glu_group_sort_typ]). *)
  Lemma glu_group_ind_apps : forall k Mk pm Ψ Ms, ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
      glu_rel_ctx_types Ψ -> List.length Ms = im_np D Mk ->
      (forall m N T, List.nth_error Ms m = Some N -> List.nth_error (tele_insts (im_params D Mk) Id Ms) m = Some T ->
         glu_rel_exp_under_sub Ψ N T) ->
      exists j : nat, glu_rel_exp_under_sub Ψ (apps (a_ind p k) Ms) Typeω@j.
  Proof.
    intros k Mk pm Ψ Ms HM Hh HΨ HMl HMs.
    pose proof (decl_closed_params_ass D k Mk Hc HM) as Hpa.
    pose proof (decl_closed_params D k Mk Hc HM) as Hps.
    destruct (glu_group_sort_typ k Mk HM) as [i HS].
    assert (Hj : exists j : nat, forall Γ', ⊩ Γ' -> forall Ms', glu_rel_sub_inst Γ' (sb_of_list Id Ms') (im_params D Mk) ->
                 Γ' ⊩ apps (a_ind p k) Ms' : (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ[sb_of_list Id Ms'] ->
                 Γ' ⊩ apps (a_ind p k) Ms' : Typeω@j).
    { destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq; cbn [exp_wk exp_sub].
      - exists i0; intros; assumption.
      - destruct (glu_ind_decl_lvlP _ HG _ _ HM) as [n Hn]; rewrite Heq in Hn; cbn [ind_sort_lvl exp_wk] in Hn.
        exists 0; intros Γ' HΓ' Ms' Hinst H.
        pose proof (glu_rel_exp_under_sub_inst _ _ _ Hn _ _ Hinst) as HL; cbn [exp_sub] in HL.
        exact (glu_rel_exp_kind_sort_small_large (κ := ak_relevant) HL H). }
    destruct Hj as [j Hj].
    exists j; econstructor; [ exact HΨ |]; intros Γ' τ Hτ.
    pose proof (glu_rel_sub_inst_ctx _ _ _ Hτ) as HΓ'.
    assert (HΓ'w : ⊢ Γ') by (destruct HΓ' as [? HSb]; exact (glu_ctx_env_wf_ctx HSb)).
    set (Ms' := List.map (fun N => N[τ]) Ms).
    rewrite apps_exp_sub; cbn [exp_sub]; fold Ms'.
    assert (HlM' : List.length Ms' = List.length (im_params D Mk)) by (unfold Ms'; rewrite List.length_map, length_im_params; exact HMl).
    assert (HUs : forall m N T, List.nth_error Ms' m = Some N -> List.nth_error (tele_insts (im_params D Mk) Id Ms') m = Some T ->
                    glu_rel_exp_under_renaming Γ' N T).
    { intros m N T HN HT; unfold Ms' in HN, HT.
      rewrite <- (tele_insts_sub _ 0 Id Id τ Ms Hpa Hps ltac:(intros; lia)) in HT.
      apply nth_error_map_inv in HN as (N0 & HN0 & ->); apply nth_error_map_inv in HT as (T0 & HT0 & ->).
      exact (glu_rel_exp_under_sub_inst_renaming (HMs _ _ _ HN0 HT0) Hτ). }
    assert (Hinst : glu_rel_sub_inst Γ' (sb_of_list Id Ms') (im_params D Mk)).
    { rewrite <- (List.app_nil_r (im_params D Mk)).
      apply glu_rel_sub_inst_of_list; [ exact Hpa | exact (glu_rel_sub_inst_nil _ _ HΓ') | rewrite List.app_nil_r
                                     | exact HlM' | exact HUs ].
      exact (member_params_wf _ _ _ _ _ Hdt HM). }
    pose proof (glu_rel_exp_under_sub_inst _ _ _ HS _ _ Hinst) as HSτ; cbn [exp_sub] in HSτ.
    apply (Hj _ HΓ' _ Hinst).
    apply (glu_rel_exp_ind_apps_gen k Mk pm nil (im_params D Mk) Γ' Ms' i HM Hh eq_refl (or_intror eq_refl) HΓ' HlM'
             (fun m N T HN HT => glu_rel_exp_of_under_renaming HΓ' (HUs m N T HN HT)) HSτ).
    eapply wf_apps_closed_pi; [ exact Hpa | exact Hps | rewrite length_im_params; exact (sort_shift_scoped D Hc Mk)
                              | exact (glu_rel_exp_under_sub_wf HS) | exact HΓ'w | | exact HlM'
                              | intros; eapply glu_rel_exp_to_wf_exp, glu_rel_exp_of_under_renaming; [ exact HΓ' | eauto ] ].
    change (ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ) with (ind_ty D Mk).
    assert (Hlt : k < ind_ndecl D) by (eapply decl_member_lt; [ exact HΓ'w | eassumption .. ]).
    eapply wf_ind; [ exact HΓ'w | eassumption .. ].
  Qed.

  (** *** The Members as Variables

      The gluing counterpart of [Model]'s [Selfs] section: the context of
      the members as variables over the uniform parameters, glued with its
      types, and [grp_sb p D] at an instance of the uniform parameters, an
      instance of it. *)

  Lemma glu_grp_selfs_prefix : forall n, n <= ind_ndecl D ->
      glu_rel_ctx_types (grp_selfs_from D 0 (List.firstn n (ind_members D)) ++ ind_uparams D) /\
      glu_tele_entries (grp_selfs_from D 0 (List.firstn n (ind_members D))) (ind_uparams D).
  Proof.
    induction n as [| n IH]; intros Hn.
    - destruct (glu_ind_decl_lvl _ HG) as [l Hlv].
      split; [ exact (glu_rel_exp_under_sub_ctx _ _ _ Hlv) | intros [] *; discriminate ].
    - pose proof (ind_ndecl_le D) as Hle.
      destruct (List.nth_error (ind_members D) n) as [Mn |] eqn:HMn; [| apply List.nth_error_None in HMn; lia ].
      rewrite (firstn_S_nth_error _ _ _ HMn), grp_selfs_from_snoc; cbn [Nat.add].
      destruct (IH ltac:(lia)) as [HC HE].
      assert (HMn' : ind_member D n = Some Mn) by exact HMn.
      destruct (glu_self_ty_under_sub _ _ HMn') as [i Hi].
      set (S0 := grp_selfs_from D 0 (List.firstn n (ind_members D))) in *.
      assert (HS0 : List.length S0 = n)
        by (unfold S0; rewrite length_grp_selfs_from, List.length_firstn; lia).
      assert (Hlf : List.length (List.firstn n (ind_members D)) = n) by (rewrite List.length_firstn; lia).
      rewrite Hlf.
      pose proof (wf_wk_shiftn_app' _ _ _ _ ltac:(destruct (glu_rel_ctx_types_ctx _ HC) as [? HSb]; exact (glu_ctx_env_wf_ctx HSb)))
        as Hw; rewrite HS0 in Hw.
      pose proof (glu_rel_exp_under_sub_wk Hi HC Hw) as Hiw; cbn [exp_wk] in Hiw.
      split.
      + exact (glu_rel_ctx_types_extend Hiw (sort_kind_abs_kind_sort ak_relevant i)).
      + intros [| e Δ1] κ A Δ2 E; cbn [List.app] in E.
        * injection E as <- <- <-; exists i; exact Hiw.
        * injection E as _ E; exact (HE _ _ _ _ E).
  Qed.

  (** The members as variables over the uniform parameters, glued with its
      types. *)
  Lemma glu_grp_selfs_ctx_types : glu_rel_ctx_types (grp_selfs_ctx D).
  Proof. unfold grp_selfs_ctx, grp_selfs; exact (proj1 (glu_grp_selfs_prefix _ (le_n _))). Qed.

  (** [grp_sb p D] followed by an instance of the uniform parameters is an
      instance of the members as variables: the group's type formers at
      the instance's uniform parameters ([glu_self_apps_under_sub]). *)
  Lemma glu_rel_sub_inst_grp_sb : forall Γ' τ, glu_rel_sub_inst Γ' τ (ind_uparams D) ->
      glu_rel_sub_inst Γ' (sb_of_list τ (List.map (fun X => X[τ])
                                          (List.map (fun j => apps (a_ind p j) (vars_from 0 (ind_nu D))) (List.seq 0 (ind_ndecl D)))))
        (grp_selfs_ctx D).
  Proof.
    intros * Hτ.
    pose proof (decl_closed_ass _ Hc) as HassU.
    assert (Hsa : all_assumptions (grp_selfs D)).
    { unfold grp_selfs; generalize 0; induction (List.firstn (ind_ndecl D) (ind_members D)) as [| M ms IH]; intros j;
        cbn [grp_selfs_from]; [ constructor |].
      apply List.Forall_app; split; [ apply IH | constructor; [ do 2 eexists; reflexivity | constructor ] ]. }
    unfold grp_selfs_ctx.
    apply glu_rel_sub_inst_of_list;
      [ exact Hsa | exact Hτ
      | destruct (glu_rel_ctx_types_ctx _ glu_grp_selfs_ctx_types) as [? HSb]; exact (glu_ctx_env_wf_ctx HSb) | |].
    - unfold grp_selfs; rewrite List.length_map, length_grp_sb_list, length_grp_selfs_from, List.length_firstn.
      pose proof (ind_ndecl_le D); lia.
    - intros k N T HN HT.
      rewrite !List.nth_error_map in HN.
      destruct (List.nth_error (List.seq 0 (ind_ndecl D)) k) as [j |] eqn:Hj; cbn in HN; [| discriminate ].
      injection HN as <-.
      assert (Hk : k < ind_ndecl D)
        by (rewrite <- (List.length_seq (ind_ndecl D) 0); apply List.nth_error_Some; congruence).
      assert (j = k) as -> by (rewrite (List.nth_error_nth' _ 0 (n := k)) in Hj by (rewrite List.length_seq; exact Hk);
                               injection Hj as <-; rewrite List.seq_nth by exact Hk; reflexivity).
      apply tele_insts_nth in HT as (κA & A & HA & ->).
      destruct (nth_rev_grp_selfs D (ind_ndecl D) k (le_n _) Hk) as (Mk & HMk & HAk).
      unfold grp_selfs in HA; rewrite HAk in HA; injection HA as <- <-.
      replace ((self_ty D Mk)[wk_shiftn k]ʷ[sb_of_list τ (List.firstn k (List.map (fun X => X[τ])
                 (List.map (fun j => apps (a_ind p j) (vars_from 0 (ind_nu D))) (List.seq 0 (ind_ndecl D)))))])
        with ((self_ty D Mk)[τ]).
      + exact (glu_rel_exp_under_sub_inst_renaming (glu_self_apps_under_sub _ _ HMk Hk) Hτ).
      + rewrite <- exp_sub_of_wk, exp_sub_sub; apply exp_sub_sb_eq; intros x.
        cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
        set (L := List.firstn k _).
        assert (HL : List.length L = k)
          by (unfold L; rewrite List.length_firstn, !List.length_map, List.length_seq; lia).
        replace (x + k) with (List.length L + x) by lia.
        symmetry; apply sb_of_list_ge.
  Qed.

  (** A view's instance is glued at its instances at the container's
      uniform telescope over the group's uniform parameters: its instance
      over the members as variables ([glu_views_self_is]), at the instance
      [grp_sb p D] makes of an instance of the uniform parameters
      ([valid_group_views_view_is]). *)
  Lemma glu_group_view_is : forall k Mk qc k' Is vm Dq j I T, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq -> decl_closed Dq -> List.nth_error Is j = Some I ->
      List.nth_error (tele_insts (ind_uparams Dq) Id Is) j = Some T ->
      glu_rel_exp_under_sub (ind_uparams D) I T.
  Proof.
    intros * HMk Hh Hq HcQ HI HT.
    destruct (glu_ind_decl_view_self _ HG) as [IsS HV].
    rewrite (glu_views_self_link _ _ HV _ (valid_group_mpath _ _ Hg) _ _ _ _ _ _ HMk Hh) in HI, HT.
    rewrite <- (tele_insts_sub (ind_uparams Dq) 0 Id Id (grp_sb p D) (IsS k) (decl_closed_ass _ HcQ) (decl_closed_uparams _ HcQ)
                  ltac:(intros; lia)) in HT.
    apply nth_error_map_inv in HI as (I0 & HI0 & ->); apply nth_error_map_inv in HT as (T0 & HT0 & ->).
    pose proof (glu_views_self_is _ _ HV _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HI0 HT0) as H0.
    destruct (glu_ind_decl_lvl _ HG) as [l Hlv].
    econstructor; [ exact (glu_rel_exp_under_sub_ctx _ _ _ Hlv) |]; intros Γ' τ Hτ.
    pose proof (glu_rel_exp_under_sub_inst _ _ _ H0 _ _ (glu_rel_sub_inst_grp_sb _ _ Hτ)) as H.
    unfold grp_sb; rewrite !exp_sub_sub, !(exp_sub_sb_eq _ _ _ (sb_of_list_compose_base _ Id τ)).
    rewrite !(exp_sub_sb_eq _ _ _ (sb_of_list_cong _ _ _ (sb_compose_id_left τ))).
    exact H.
  Qed.

  (** A record view's instance is glued at its instances at the record's
      parameters over the group's uniform parameters, likewise
      ([glu_views_self_record_instances]). *)
  Lemma glu_group_rview_is : forall k Mk qr Is fl R j I T, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
      record_lookup gc_deps gc_stack qr = Some R -> all_assumptions (record_params R) -> ctx_scoped 0 (record_params R) ->
      List.nth_error Is j = Some I -> List.nth_error (tele_insts (record_params R) Id Is) j = Some T ->
      glu_rel_exp_under_sub (ind_uparams D) I T.
  Proof.
    intros * HMk Hh HlR HaR HsR HI HT.
    destruct (glu_ind_decl_view_self _ HG) as [IsS HV].
    rewrite (glu_views_self_record_link _ _ HV _ (valid_group_mpath _ _ Hg) _ _ _ _ _ HMk Hh) in HI, HT.
    rewrite <- (tele_insts_sub (record_params R) 0 Id Id (grp_sb p D) (IsS k) HaR HsR ltac:(intros; lia)) in HT.
    apply nth_error_map_inv in HI as (I0 & HI0 & ->); apply nth_error_map_inv in HT as (T0 & HT0 & ->).
    pose proof (glu_views_self_record_instances _ _ HV _ _ _ _ _ _ _ _ _ HMk Hh HlR HI0 HT0) as H0.
    destruct (glu_ind_decl_lvl _ HG) as [l Hlv].
    econstructor; [ exact (glu_rel_exp_under_sub_ctx _ _ _ Hlv) |]; intros Γ' τ Hτ.
    pose proof (glu_rel_exp_under_sub_inst _ _ _ H0 _ _ (glu_rel_sub_inst_grp_sb _ _ Hτ)) as H.
    unfold grp_sb; rewrite !exp_sub_sub, !(exp_sub_sb_eq _ _ _ (sb_of_list_compose_base _ Id τ)).
    rewrite !(exp_sub_sb_eq _ _ _ (sb_of_list_cong _ _ _ (sb_compose_id_left τ))).
    exact H.
  Qed.

End IndApps.

(** ** The Types of a Group's Members

    The type of a member at the uniform parameters as variables and terms
    glued at their instances at its non-uniform parameters' types is a
    type of a large universe glued at its instances
    ([valid_group_mty_valid]): a declared member's former, a view's
    container's at the view's instance, or a record view's record.  The
    containers are groups of [VP]. *)
Lemma glu_group_mty : forall VP, valid_groups VP -> (forall qn G, VP qn G -> glu_ind_decl G) ->
    (forall qn G, VP qn G -> glu_self_ends_all qn G) -> forall p D, VP p D ->
    forall j Mj Z nn L Ns, ind_member D j = Some Mj -> glu_rel_ctx_types (Z ++ ind_uparams D) -> all_assumptions Z ->
    List.length Z = L + nn -> List.length Ns = im_nn Mj ->
    (forall m N T, List.nth_error Ns m = Some N ->
       List.nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D nn L)) Ns) m = Some T ->
       glu_rel_exp_under_sub (Z ++ ind_uparams D) N T) ->
    exists i : nat, glu_rel_exp_under_sub (Z ++ ind_uparams D) (ind_mty p D j (ind_uvars D nn L) Ns) Typeω@i.
Proof.
  intros VP HVP HGall HSall p D HPD j Mj Z nn L Ns HMj HΨ HZa HlZ HlN HNs.
  pose proof (valid_groups_valid VP HVP p D HPD) as Hg; pose proof (HGall _ _ HPD) as HG; pose proof (HSall _ _ HPD) as HS.
  pose proof (valid_group_closed _ _ Hg) as Hc; pose proof (decl_typed_mvc _ _ _ (valid_group_typed _ _ Hg)) as Hmv.
  pose proof (decl_closed_ass _ Hc) as HUa.
  assert (HΨw : ⊢ Z ++ ind_uparams D) by (destruct (glu_rel_ctx_types_ctx _ HΨ) as [? HSb]; exact (glu_ctx_env_wf_ctx HSb)).
  assert (Hgw : ⊢ᵍ gc_deps ⍮ gc_stack) by (eapply ctx_wf_gctx; exact HΨw).
  set (Us := ind_uvars D nn L) in *.
  assert (HUs : Us = vars_from (List.length Z) (List.length (ind_uparams D))) by (unfold Us, ind_uvars, ind_nu; rewrite HlZ; reflexivity).
  pose proof (glu_vars_tele_under_sub Z (ind_uparams D) HUa (decl_closed_uparams _ Hc) (decl_mvc_uparams _ Hmv) HΨ) as HUv.
  rewrite <- HUs in HUv.
  assert (HlU : List.length Us = ind_nu D) by (unfold Us, ind_uvars; apply length_vars_from).
  assert (HlTU : List.length (tele_insts (ind_uparams D) Id Us) = ind_nu D)
    by (rewrite length_tele_insts by exact HUa; unfold ind_nu in *; lia).
  unfold ind_mty; rewrite HMj; unfold im_ty_at, im_ref, im_pre.
  destruct (im_head Mj) as [pm | qc kc Is vm | qr Is fl] eqn:Hh; cbn [fst snd].
  - (** A declared member: its former *)
    apply (glu_group_ind_apps p D Hg HG HS j Mj pm); [ exact HMj | exact Hh | exact HΨ | rewrite List.length_app; unfold im_np; lia |].
    intros m N T HN HT.
    unfold im_params in HT; rewrite tele_insts_app in HT by (exact HUa || (unfold ind_nu in *; lia)).
    destruct (Nat.lt_ge_cases m (ind_nu D)) as [Hm | Hm].
    + rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
      exact (HUv _ _ _ HN HT).
    + rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HT by lia.
      rewrite HlU in HN; rewrite HlTU in HT.
      exact (HNs _ _ _ HN HT).
  - (** A view: the container's former at the view's instance *)
    destruct (decl_typed_view _ _ _ (valid_group_typed _ _ Hg) _ _ _ _ _ _ HMj Hh) as (Dq & Mk' & Hq & HMk' & Hkd & HIl & _ & Hvm & _).
    pose proof (valid_groups_containers _ HVP _ _ _ _ _ _ _ _ _ HPD HMj Hh Hq) as HVPq.
    pose proof (valid_groups_valid VP HVP _ _ HVPq) as HgQ; pose proof (HGall _ _ HVPq) as HGQ; pose proof (HSall _ _ HVPq) as HSQ.
    pose proof (valid_group_closed _ _ HgQ) as HcQ; pose proof (decl_typed_mvc _ _ _ (valid_group_typed _ _ HgQ)) as HmvQ.
    pose proof (decl_closed_ass _ HcQ) as HaQ.
    assert (Hhd : exists pm, im_head Mk' = mh_decl pm).
    { pose proof (proj2 (decl_typed_order _ _ _ (valid_group_typed _ _ HgQ) _ _ HMk') Hkd) as Hd.
      unfold im_is_decl in Hd; destruct (im_head Mk'); [ eauto | discriminate .. ]. }
    destruct Hhd as [pm Hhd].
    destruct (decl_typed_view_wrap _ _ _ (valid_group_typed _ _ Hg) _ _ _ _ _ _ HMj Hh) as (D2 & Hq2 & Hvw).
    rewrite Hq in Hq2; injection Hq2 as <-.
    destruct (view_wrap_ok_members _ _ _ Hvw _ _ _ HMk' Hvm) as (Mv & HMv & Hnn & _).
    rewrite HMj in HMv; injection HMv as <-.
    set (IsU := List.map (fun I => I[sb_of_list Id Us]) Is).
    assert (HlIsU : List.length IsU = ind_nu Dq) by (unfold IsU; rewrite List.length_map; exact HIl).
    assert (HlTI : List.length (tele_insts (ind_uparams Dq) Id IsU) = ind_nu Dq)
      by (rewrite length_tele_insts by exact HaQ; unfold ind_nu in *; lia).
    pose proof (decl_closed_head_scoped _ Hc _ _ _ _ _ _ HMj Hh) as HsIs.
    pose proof (proj1 (proj2 (decl_mvc_members _ Hmv _ _ HMj))) as HmIs; rewrite Hh in HmIs; cbn in HmIs.
    (** The view's instance, glued at its instances over the uniform
        parameters there *)
    assert (HIs : forall m I T0, List.nth_error Is m = Some I -> List.nth_error (tele_insts (ind_uparams Dq) Id Is) m = Some T0 ->
                    glu_rel_exp_under_sub (ind_uparams D) I T0)
      by (intros m I T0 HI HT0; exact (glu_group_view_is p D Hg HG HS j Mj qc kc Is vm Dq m I T0 HMj Hh Hq HcQ HI HT0)).
    apply (glu_group_ind_apps qc Dq HgQ HGQ HSQ kc Mk' pm); [ exact HMk' | exact Hhd | exact HΨ | rewrite List.length_app; unfold im_np; lia |].
    intros m N T HN HT.
    unfold im_params in HT; rewrite tele_insts_app in HT by (exact HaQ || (unfold ind_nu in *; lia)).
    destruct (Nat.lt_ge_cases m (ind_nu Dq)) as [Hm | Hm].
    + (** The instance, of the container's uniform parameters' types *)
      rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
      unfold IsU in HN; rewrite List.nth_error_map in HN.
      destruct (List.nth_error Is m) as [I |] eqn:HI; cbn in HN; [ injection HN as <- | discriminate ].
      assert (Hm' : m < List.length (tele_insts (ind_uparams Dq) Id Is))
        by (rewrite length_tele_insts by exact HaQ; unfold ind_nu in *; lia).
      destruct (nth_error_lt_some' _ _ Hm') as [T0 HT0].
      pose proof (tele_insts_closed_sub _ _ (sb_of_list Id Us) _ _ HaQ (decl_closed_uparams _ HcQ) HT0) as HT1.
      fold IsU in HT1; rewrite HT in HT1; injection HT1 as ->.
      rewrite HUs; exact (glu_rel_exp_under_sub_at_vars Z (ind_uparams D) I T0 HUa (decl_closed_uparams _ Hc) (decl_mvc_uparams _ Hmv) HΨ
                            (HIs _ _ _ HI HT0)).
    + (** The non-uniform arguments, at the container's non-uniform
          parameters at the instance: the view's, by the view's equation *)
      rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HT by lia.
      rewrite HlIsU in HN; rewrite HlTI in HT.
      set (τ := sb_of_wk (wk_shiftn (List.length Z))).
      pose proof (wf_wk_shiftn_app' _ _ _ _ HΨw) as Hw.
      pose proof (wf_sub_of_wk _ _ _ _ _ Hw) as Hτt.
      pose proof (Syntactic.System.Global.Presup.decl_typed_view_nparams _ _ p D Hgw (valid_group_typed _ _ Hg) (valid_group_lookup _ _ Hg)
                    _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hq HMk' Hvm HMj) as HX.
      pose proof (sub_preserves_ext _ _ _ _ _ _ _ HX Hτt) as HXτ.
      pose proof (decl_closed_nparams_ass D Hc _ _ HMj) as HaX.
      pose proof (decl_closed_nparams_ass Dq HcQ _ _ HMk') as HaY.
      assert (EX : tele_insts (im_nparams Mj) (sb_of_list Id Us) Ns = tele_insts (tele_sub (im_nparams Mj) τ) Id Ns).
      { rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ _ _ (sb_compose_id_right τ)).
        apply (tele_insts_agree_mvc _ (ind_nu D));
          [ exact HaX | exact (proj1 (decl_mvc_members _ Hmv _ _ HMj)) | exact (decl_closed_nparams_scoped _ Hc _ _ HMj) |].
        intros x Hx; rewrite HUs, sb_of_list_vars by (unfold ind_nu in Hx; exact Hx).
        unfold τ, sb_of_wk, wk_shiftn; cbn; f_equal; lia. }
      assert (EY : tele_insts (im_nparams Mk') (sb_of_list Id IsU) Ns
                   = tele_insts (tele_sub (tele_sub (im_nparams Mk') (sb_of_list Id Is)) τ) Id Ns).
      { rewrite !tele_insts_tele_sub.
        apply (tele_insts_agree_mvc _ (ind_nu Dq));
          [ exact HaY | exact (proj1 (decl_mvc_members _ HmvQ _ _ HMk')) | exact (decl_closed_nparams_scoped _ HcQ _ _ HMk') |].
        intros x Hx.
        assert (HxI : x < List.length Is) by (unfold ind_nu in *; lia).
        assert (HlIsU' : List.length IsU = List.length Is) by (unfold IsU; apply List.length_map).
        rewrite (sb_of_list_nth IsU _ x a_prop) by lia.
        unfold sb_compose; rewrite (sb_of_list_nth Is _ x a_prop HxI).
        rewrite HlIsU'.
        destruct (nth_error_lt_some' Is (List.length Is - 1 - x) ltac:(lia)) as [I HI'].
        assert (HIU : List.nth_error IsU (List.length Is - 1 - x) = Some I[sb_of_list Id Us])
          by (unfold IsU; rewrite List.nth_error_map, HI'; reflexivity).
        rewrite (List.nth_error_nth _ _ _ HI'), (List.nth_error_nth _ _ _ HIU); cbn [sentry_sub sentry_exp].
        pose proof (List.nth_error_In _ _ HI') as HIin.
        change (fun x0 : nat => sentry_sub (τ x0) Id) with (τ ⨟ Id).
        unfold τ; rewrite <- exp_sub_sub, exp_sub_id, exp_sub_of_wk, HUs.
        rewrite (exp_at_vars _ _ _ (proj1 (List.Forall_forall _ _) HsIs I HIin) (proj1 (List.Forall_forall _ _) HmIs I HIin)).
        reflexivity. }
      rewrite EY, tele_sub_sub in HT.
      assert (HMsτ : forall m0 N0 T0, List.nth_error Ns m0 = Some N0 ->
                 List.nth_error (tele_insts (tele_sub (im_nparams Mj) τ) Id Ns) m0 = Some T0 ->
                 glu_rel_exp_under_sub (Z ++ ind_uparams D) N0 T0)
        by (intros m0 N0 T0 HN0 HT0; rewrite <- EX in HT0; exact (HNs _ _ _ HN0 HT0)).
      (** The container's non-uniform parameters at the instance, glued
          entries there ([glu_tele_entries_sub]) *)
      set (σ0 := sb_of_list Id Is ⨟ τ).
      assert (HTσ0 : glu_rel_sub_transformer (Z ++ ind_uparams D) σ0 (ind_uparams Dq)).
      { intros Γ' σ Hσ.
        pose proof (glu_rel_sub_inst_of_wk_comp Hσ Hw) as HUσ.
        set (σ' := (ι (wk_shiftn (List.length Z))) ⨟ σ) in *.
        assert (E : sb_eq (σ0 ⨟ σ) (sb_of_list σ' (List.map (fun I => I[σ']) Is))).
        { unfold σ0, τ; rewrite sb_compose_assoc, sb_of_list_compose_base, (sb_of_list_cong _ _ _ (sb_compose_id_left _)).
          reflexivity. }
        apply (glu_rel_sub_inst_sb_eq _ _ _ _ (symmetry E)).
        rewrite <- (List.app_nil_r (ind_uparams Dq)).
        apply glu_rel_sub_inst_of_list;
          [ exact HaQ | exact (glu_rel_sub_inst_nil _ _ (glu_rel_sub_inst_ctx _ _ _ Hσ))
          | rewrite List.app_nil_r; destruct (glu_rel_ctx_types_ctx _ (glu_ind_decl_params _ HGQ _ _ HMk')) as [? HSb];
            unfold im_params in HSb; exact (ctx_app_wf_tail _ _ _ _ (glu_ctx_env_wf_ctx HSb))
          | rewrite List.length_map; unfold ind_nu in HIl; exact HIl |].
        intros m0 N0 T0 HN0 HT0.
        rewrite (tele_insts_closed_base _ σ' Id _ HaQ (decl_closed_uparams _ HcQ)) in HT0.
        rewrite <- (tele_insts_sub _ 0 Id Id σ' Is HaQ (decl_closed_uparams _ HcQ) ltac:(intros; lia)) in HT0.
        apply nth_error_map_inv in HN0 as (I0 & HI0 & ->); apply nth_error_map_inv in HT0 as (T1 & HT1 & ->).
        exact (glu_rel_exp_under_sub_inst_renaming (HIs _ _ _ HI0 HT1) HUσ). }
      assert (Hσ0t : Z ++ ind_uparams D ⊢ˢ σ0 : ind_uparams Dq).
      { pose proof (glu_rel_sub_inst_typed _ _ _ (HTσ0 _ _ (glu_rel_ctx_types_id HΨ))) as H.
        exact (proj1 (proj2 (proj2 (presup_sub_eq (wf_sub_eq_of_sb_eq _ _ _ _ _ _ H (sb_compose_id_right σ0)))))). }
      destruct (glu_tele_entries_sub (im_nparams Mk') (Z ++ ind_uparams D) σ0 (ind_uparams Dq) HaY HΨ Hσ0t HTσ0
                  (glu_nparams_entries qc Dq HgQ HGQ _ _ HMk')) as (_ & _ & _ & E2).
      exact (glu_tele_insts_conv_under_sub _ _ _ Ns ltac:(rewrite tele_sub_sub in HXτ; exact HXτ)
               (all_assumptions_sub _ _ HaX) (all_assumptions_sub _ _ HaY) HΨ E2
               ltac:(rewrite !length_tele_sub, !length_im_nparams; lia) ltac:(rewrite length_tele_sub, length_im_nparams; lia)
               HMsτ _ _ _ HN HT).
  - (** A record view: the record at the view's instance, of no
        non-uniform parameter *)
    pose proof (rview_struct_nparams _ _ _ (decl_typed_record_struct _ _ _ (valid_group_typed _ _ Hg)) _ _ _ _ _ HMj Hh) as Hnp.
    destruct Ns; [| unfold im_nn in HlN; rewrite Hnp in HlN; discriminate HlN ].
    rewrite List.app_nil_r.
    destruct (valid_group_records _ _ Hg _ _ _ _ _ HMj Hh) as [R HR].
    pose proof (valid_rview_record_lookup _ _ HR) as HlR.
    destruct (glu_ind_decl_view_self _ HG) as [IsS HV].
    pose proof (glu_views_self_records _ _ HV _ _ _ _ _ _ HMj Hh HlR) as HGR.
    pose proof (record_lookup_typed _ _ Hgw (gctx_valid_syn _ _ Hgw) _ _ HlR) as HtR.
    pose proof (typed_params_ass _ _ _ HtR) as HaR.
    pose proof (closed_params _ (valid_rview_record_closed _ _ HR)) as HsR.
    assert (HIl : List.length Is = List.length (record_params R)).
    { pose proof (Completeness.Inductives.FiledViews.rview_record_len p D Hg j Mj qr Is fl R HMj Hh HR) as HIl.
      exact HIl. }
    apply (glu_record_apps qr R (Z ++ ind_uparams D) (List.map (fun I => I[sb_of_list Id Us]) Is) HlR HGR HΨ
             ltac:(rewrite List.length_map; exact HIl)).
    intros m N T HN HT.
    rewrite List.nth_error_map in HN.
    destruct (List.nth_error Is m) as [I |] eqn:HI; cbn in HN; [ injection HN as <- | discriminate ].
    assert (Hm' : m < List.length (tele_insts (record_params R) Id Is))
      by (rewrite length_tele_insts by exact HaR; pose proof (nth_error_lt_length _ _ _ HI); lia).
    destruct (nth_error_lt_some' _ _ Hm') as [T0 HT0].
    pose proof (tele_insts_closed_sub _ _ (sb_of_list Id Us) _ _ HaR HsR HT0) as HT1.
    rewrite HT in HT1; injection HT1 as ->.
    rewrite HUs; exact (glu_rel_exp_under_sub_at_vars Z (ind_uparams D) I T0 HUa (decl_closed_uparams _ Hc) (decl_mvc_uparams _ Hmv) HΨ
                          (glu_group_rview_is p D Hg HG HS j Mj qr Is fl R m I T0 HMj Hh HlR HaR HsR HI HT0)).
Qed.

(** ** The Contexts of the Arguments of a Group's Members

    As [shape_domains_ctx_wk_gen] and [shape_domains_ctx_sem_gen] in the
    PER model: the domains of a recursive argument's shape over the
    arguments before it, its type, and the arguments before a constructor's
    argument, each glued at its instances. *)
Section GluArgsCtx.
  Variable (VP : qname -> ind_decl -> Prop).
  Hypotheses (HVP : valid_groups VP) (HGall : forall qn G, VP qn G -> glu_ind_decl G)
    (HSall : forall qn G, VP qn G -> glu_self_ends_all qn G).
  Variables (p : qname) (D : ind_decl) (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
  Hypotheses (HPD : VP p D) (HM : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs).
  Let Hg := valid_groups_valid VP HVP p D HPD.
  Let HG := HGall _ _ HPD.

  Let Hl := valid_group_lookup _ _ Hg.
  Let HD := valid_group_valid _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hdt := valid_group_typed _ _ Hg.
  Let Hin := cons_lookup_in _ _ _ Hcon.
  Let Hgw : ⊢ᵍ gc_deps ⍮ gc_stack := ctx_wf_gctx _ _ _ (member_params_wf _ _ _ _ _ Hdt HM).
  Let HDs : decls_typed gc_deps gc_stack := decls_of_ctx _ _ _ (wf_ctx_empty _ _ Hgw).

  (** A non-recursive argument's type, over the non-recursive arguments
      before it, is a type of a large universe of its kind glued at its
      instances *)
  Lemma glu_group_arg_large : forall gs1 r A gs2, gs = gs1 ++ ca_arg r A :: gs2 ->
      exists i : nat, glu_rel_exp_under_sub (cargs_nonrec_ctx gs1 ++ im_params D Mk) A (abs_kind_sort r Typeω@i).
  Proof.
    intros * Heq.
    assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
      by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
    pose proof (nonrec_kind_at gs1 gs2 r A) as Hr; rewrite <- Heq in Hr.
    pose proof (glu_ind_decl_arg _ HG _ _ _ _ _ _ _ HM Hcon HA Hr) as HAg.
    rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HAg.
    assert (Hlen : List.length (cargs_nonrec_ctx gs1 ++ im_nparams Mk) = List.length (cargs_nonrec gs1) + im_nn Mk)
      by (rewrite List.length_app, cargs_nonrec_ctx_rev_tele, List.length_rev, length_cargs_nonrec_tele, length_im_nparams; reflexivity).
    unfold im_params in HAg |- *; rewrite List.app_assoc, <- Hlen in HAg; rewrite List.app_assoc.
    exact (glu_group_sort_large p D Hg HG _ _ _ HAg).
  Qed.

  (** A domain of a recursive argument's shape, over the domains before it
      and the non-recursive arguments before the argument, is a type of a
      large universe glued at its instances *)
  Lemma glu_group_dom_large : forall gs1 t gs2 j B, gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error (ptyp_doms t) j = Some B ->
      exists i : nat, glu_rel_exp_under_sub (doms_ctx (List.firstn j (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_params D Mk) B Typeω@i.
  Proof.
    intros * Heq HB.
    pose proof (glu_ind_decl_dom _ HG _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as HBg.
    rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HBg.
    assert (Hj : j < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
    assert (Hlen : List.length (doms_ctx (List.firstn j (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_nparams Mk)
                   = j + List.length (cargs_nonrec gs1) + im_nn Mk)
      by (rewrite !List.length_app, length_doms_ctx, List.length_firstn, cargs_nonrec_ctx_rev_tele, List.length_rev,
            length_cargs_nonrec_tele, length_im_nparams; lia).
    unfold im_params in HBg |- *.
    set (Ψ := doms_ctx (List.firstn j (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_nparams Mk) in *.
    replace (doms_ctx (List.firstn j (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_nparams Mk ++ ind_uparams D)
      with (Ψ ++ ind_uparams D) in HBg |- * by (unfold Ψ; rewrite <- !List.app_assoc; reflexivity).
    rewrite <- Hlen in HBg.
    change ((ind_sort D)[wk_shiftn (List.length Ψ)]ʷ) with (abs_kind_sort ak_relevant (ind_sort D)[wk_shiftn (List.length Ψ)]ʷ) in HBg.
    exact (glu_group_sort_large p D Hg HG _ _ _ HBg).
  Qed.

  (** The domains of a recursive argument's shape over the arguments before
      it, a context glued with its types. *)
  Lemma glu_shape_domains_ctx_gen : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      glu_rel_ctx_types (cargs_ctx p D Mk gs1 ++ im_params D Mk) ->
      forall j, j <= List.length (ptyp_doms t) ->
        glu_rel_ctx_types (shape_domains_ctx (cargs_pat gs1) (List.firstn j (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk).
  Proof.
    intros * Heq HC0; induction j as [| j IH]; intros Hj.
    - exact HC0.
    - destruct (nth_error_lt_some' (ptyp_doms t) j ltac:(lia)) as [B HB].
      destruct (shape_prefix_wf _ _ _ _ _ _ _ _ Hgw HDs Hl HM Hin _ _ _ Heq j ltac:(lia)) as (_ & _ & Hw).
      destruct (glu_group_dom_large _ _ _ _ _ Heq HB) as [i HBg].
      pose proof (glu_rel_exp_under_sub_wk HBg (IH ltac:(lia)) Hw) as HBw; cbn [exp_wk] in HBw.
      rewrite (Tele.firstn_S_snoc _ _ _ HB), shape_domains_ctx_snoc, List.length_firstn, Nat.min_l by lia.
      cbn [List.app].
      exact (glu_rel_ctx_types_extend HBw (sort_kind_abs_kind_sort ak_relevant i)).
  Qed.

  (** The type of a recursive argument after some of its shape's domains,
      over the arguments before it and those domains, is a type of a large
      universe glued at its instances: a [Π] over the next domain, or the
      type of the member the shape ends in ([glu_group_mty]). *)
  Lemma glu_group_shape_typ : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      glu_rel_ctx_types (cargs_ctx p D Mk gs1 ++ im_params D Mk) ->
      forall kk, kk <= List.length (ptyp_doms t) ->
        exists j : nat, glu_rel_exp_under_sub
          (shape_domains_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk)
          (ptyp_ty p D (im_nn Mk) (List.repeat false kk ++ cargs_pat gs1) (ptyp_skip kk t)) Typeω@j.
  Proof.
    intros gs1 t gs2 Heq HC0 kk Hk.
    pose proof (glu_shape_domains_ctx_gen _ _ _ Heq HC0) as HCs.
    set (pat := cargs_pat gs1).
    remember (ptyp_skip kk t) as t' eqn:Hsk; symmetry in Hsk.
    revert kk Hk Hsk; induction t' as [m Ps | B t'' IH]; intros kk Hk Hsk.
    - (** The end: the member's type at the uniform parameters as
          variables and the shape's parameters, weakened past the recursive
          arguments *)
      destruct (Tele.ptyp_skip_self _ _ _ _ Hsk) as (HkL & Hm & HPs).
      assert (Hkd : kk = List.length (ptyp_doms t)) by lia; subst kk.
      destruct (length_rec_ps D HD k Mk HM c gs gs1 t gs2 Hcon Heq) as (Mj & HMj & HlPs).
      rewrite Hm in HMj; rewrite HPs in HlPs.
      set (L := List.length (ptyp_doms t)) in *.
      set (pat' := List.repeat false L ++ pat).
      set (Φ := shape_domains_ctx pat (ptyp_doms t)).
      assert (HlΦ : List.length Φ = L) by (unfold Φ; apply length_shape_domains_ctx).
      pose proof (HCs L (le_n _)) as HΦ; unfold L in HΦ; rewrite List.firstn_all in HΦ; fold Φ pat in HΦ.
      destruct (shape_prefix_wf _ _ _ _ _ _ _ _ Hgw HDs Hl HM Hin _ _ _ Heq L (le_n _)) as (_ & _ & HwΦ).
      unfold L in HwΦ; rewrite List.firstn_all in HwΦ; fold Φ pat pat' L in HwΦ.
      cbn [ptyp_ty]; rewrite (List.firstn_all2 (n := L)) by lia; fold Φ in HΦ, HwΦ |- *; fold pat' in HwΦ.
      assert (HE : glu_rel_ctx_types ((Φ ++ cargs_ctx p D Mk gs1 ++ im_nparams Mk) ++ ind_uparams D))
        by (unfold im_params in HΦ; rewrite <- !List.app_assoc; exact HΦ).
      assert (HZa : all_assumptions (Φ ++ cargs_ctx p D Mk gs1 ++ im_nparams Mk)).
      { apply List.Forall_app; split; [ apply shape_domains_ctx_ass |].
        apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_closed_nparams_ass D Hc _ _ HM) ]. }
      assert (Hpat : List.length pat = List.length gs1) by apply length_cargs_pat.
      assert (Hpat' : List.length pat' = L + List.length gs1) by (unfold pat'; rewrite List.length_app, List.repeat_length; lia).
      assert (Hnargs : pat_nargs pat' = L + List.length (cargs_nonrec_ctx gs1)).
      { unfold pat', pat; rewrite pat_nargs_app, pat_nargs_cargs_pat; f_equal.
        clear; induction L as [| L IH]; cbn; lia. }
      pose proof (decl_typed_mvc _ _ _ Hdt) as Hmv.
      destruct (glu_group_mty VP HVP HGall HSall p D HPD m Mj (Φ ++ cargs_ctx p D Mk gs1 ++ im_nparams Mk) (im_nn Mk)
                  (List.length pat') (List.map (fun P => P[wk_pat pat']ʷ) Ps) HMj HE HZa) as [j0 Hv].
      + rewrite !List.length_app, length_cargs_ctx, length_im_nparams; lia.
      + rewrite List.length_map; exact HlPs.
      + intros m0 N T HN HT.
        apply nth_error_map_inv in HN as (P & HPm & ->).
        set (s := L + List.length (cargs_nonrec_ctx gs1) + im_nn Mk).
        assert (Hti : tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mk) (List.length pat')))
                        (List.map (fun P => P[wk_pat pat']ʷ) Ps)
                      = List.map (fun T => T[wk_pat pat']ʷ) (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn s)) Ps)).
        { rewrite <- !map_sub_of_wk; symmetry.
          eapply (tele_insts_sub_mvc _ (ind_nu D));
            [ exact (decl_closed_nparams_ass D Hc _ _ HMj) | exact (proj1 (decl_mvc_members _ Hmv _ _ HMj))
            | exact (decl_closed_nparams_scoped _ Hc _ _ HMj) |].
          intros x Hx; unfold ind_uvars; rewrite sb_of_list_vars by exact Hx; cbn.
          unfold s, wk_shiftn; rewrite <- Hnargs.
          replace (x + (pat_nargs pat' + im_nn Mk)) with (pat_nargs pat' + (im_nn Mk + x)) by lia.
          rewrite wk_pat_ge; f_equal; lia. }
        rewrite Hti in HT; apply nth_error_map_inv in HT as (T0 & HT0 & ->).
        assert (Hσ : s = ptyp_depth t + List.length (cargs_nonrec gs1) + im_nn Mk)
          by (unfold s, ptyp_depth; fold L; rewrite cargs_nonrec_ctx_rev_tele, List.length_rev, length_cargs_nonrec_tele; reflexivity).
        rewrite Hσ in HT0.
        rewrite <- HPs in HPm, HT0.
        pose proof (glu_ind_decl_rec_field _ HG k Mk c gs gs1 t gs2 Mj m0 P T0 HM Hcon Heq ltac:(rewrite Hm; exact HMj) HPm HT0)
          as HP0.
        rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HP0.
        pose proof (glu_rel_exp_under_sub_wk HP0 HΦ HwΦ) as H.
        unfold im_params in H; rewrite <- !List.app_assoc; exact H.
      + exists j0; unfold im_params; rewrite <- !List.app_assoc in Hv; exact Hv.
    - (** A domain: the [Π] over it of the rest *)
      destruct (Tele.ptyp_skip_pi _ _ _ _ Hsk) as [HB Hs'].
      assert (Hkl : kk < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
      destruct (IH (S kk) ltac:(lia) Hs') as [j1 Hrest].
      rewrite (Tele.firstn_S_snoc _ _ _ HB), shape_domains_ctx_snoc, List.length_firstn, Nat.min_l in Hrest by lia.
      cbn [List.repeat List.app] in Hrest.
      destruct (shape_prefix_wf _ _ _ _ _ _ _ _ Hgw HDs Hl HM Hin _ _ _ Heq kk ltac:(lia)) as (_ & _ & Hw).
      destruct (glu_group_dom_large _ _ _ _ _ Heq HB) as [i HBg].
      pose proof (glu_rel_exp_under_sub_wk HBg (HCs kk ltac:(lia)) Hw) as HBw; cbn [exp_wk] in HBw.
      cbn [ptyp_ty].
      exists (max i j1).
      exact (glu_rel_exp_under_sub_pi_large (κd := ak_relevant) (κc := ak_relevant)
               (glu_rel_exp_under_sub_kind_sort_lift (κ := ak_relevant) (Nat.le_max_l i j1) HBw)
               (glu_rel_exp_under_sub_kind_sort_lift (κ := ak_relevant) (Nat.le_max_r i j1) Hrest) (pi_kinds_relevant ak_relevant)).
  Qed.

  (** Each prefix of the arguments of the constructor is a context glued
      with its types over the member's parameters
      ([valid_group_cargs_sem_all]). *)
  Lemma glu_group_cargs_all : forall gs1 gs2, gs = gs1 ++ gs2 -> glu_rel_ctx_types (cargs_ctx p D Mk gs1 ++ im_params D Mk).
  Proof.
    induction gs1 as [| g gs1 IH] using List.rev_ind; intros gs2 Heq.
    - exact (glu_ind_decl_params _ HG _ _ HM).
    - rewrite <- List.app_assoc in Heq; cbn [List.app] in Heq.
      pose proof (IH _ Heq) as HΨ.
      destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hgw HDs Hl HM Hin gs1 _ Heq) as (_ & _ & Hw).
      rewrite cargs_ctx_snoc.
      destruct g as [r A | t]; cbn [cargs_ctx_aux List.app].
      + destruct (glu_group_arg_large gs1 r A gs2 Heq) as [j HA].
        pose proof (glu_rel_exp_under_sub_wk HA HΨ Hw) as HAw; rewrite abs_kind_sort_wk in HAw; cbn [exp_wk] in HAw.
        exact (glu_rel_ctx_types_extend HAw (sort_kind_abs_kind_sort r j)).
      + destruct (glu_group_shape_typ gs1 t gs2 Heq HΨ 0 ltac:(lia)) as [j Hj].
        cbn [List.firstn shape_domains_ctx List.repeat List.app ptyp_skip] in Hj.
        exact (glu_rel_ctx_types_extend Hj (sort_kind_abs_kind_sort ak_relevant j)).
  Qed.

End GluArgsCtx.

(** The context of a constructor's arguments over its member's parameters
    is glued with its types, for every group of [VP]. *)
Corollary glu_group_cargs : forall VP, valid_groups VP -> (forall qn G, VP qn G -> glu_ind_decl G) ->
    (forall qn G, VP qn G -> glu_self_ends_all qn G) ->
    forall q0 G0 j Mj c0 gs0, VP q0 G0 -> ind_member G0 j = Some Mj -> ind_con Mj c0 = Some gs0 ->
      glu_rel_ctx_types (cargs_ctx q0 G0 Mj gs0 ++ im_params G0 Mj).
Proof.
  intros * HVP HGall HSall * HPD HM Hcon.
  exact (glu_group_cargs_all VP HVP HGall HSall q0 G0 j Mj c0 gs0 HPD HM Hcon gs0 nil (eq_sym (List.app_nil_r gs0))).
Qed.

End Fixed_GCtx.
