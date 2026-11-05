(** * The Constructors of a Valid Group

    A constructor of a member [k] of a valid group [D] at [p] is an element
    of its type ([valid_exp_under_ctx_con]): at related parameters and
    arguments, its value is related at the type of the member there.  The
    type's relation is the group's canonical one at [k]
    ([member_type_rel]), at a view through the agreement of the view with
    its container ([view_agreement_canonical_all]); the value is a
    constructor of the member in it ([con_rel]), its recursive arguments
    related by their shapes ([shape_char]).

    At a view, the constructor takes the group's uniform parameters and is
    then its container's constructor at the view's instance there: its
    values along the arguments are a relation ([con_value]), not a
    function of them, so its type is read by [ctx_pi_rel_elem_by]. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing.
From Mctt.Core.Syntactic.System.Global Require Import Presup MemberLemmas.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Instance Telescope.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews ArgTypes CargsRel ViewEquations RviewEnds ViewArgs.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence ViewCount.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** The Sorts of a Constructor's Arguments *)

(** Corresponding arguments of a view's and of its container's
    constructors are of the same kind ([cargs_correspond]). *)
Lemma cargs_correspond_tags : forall vm gs' gs j, cargs_correspond vm gs' gs ->
    match List.nth_error gs' j with Some (ca_arg r _) => r | _ => ak_relevant end =
    match List.nth_error gs j with Some (ca_arg r _) => r | _ => ak_relevant end.
Proof.
  intros vm; induction gs' as [| g' gs' IH]; intros [| g gs] j H; cbn in H; try contradiction.
  - destruct j; reflexivity.
  - destruct g'; contradiction.
  - destruct g' as [r' A' | t'], g as [r A | t]; cbn in H; try contradiction; destruct j as [| j]; cbn [List.nth_error].
    + destruct H as [-> _]; reflexivity.
    + apply IH; tauto.
    + destruct H as [-> _]; reflexivity.
    + apply IH; tauto.
    + reflexivity.
    + apply IH; tauto.
Qed.

(** So the two constructors' arguments have the same kinds. *)
Lemma cargs_correspond_kinds : forall vm gs' gs, cargs_correspond vm gs' gs -> cargs_kinds gs' = cargs_kinds gs.
Proof.
  intros vm; induction gs' as [| [r' A' | t'] gs' IH]; intros [| [r A | t] gs] H; cbn in H; try contradiction; [ reflexivity | | |];
    unfold cargs_kinds in *; cbn [List.map]; f_equal; try (apply IH; tauto); tauto.
Qed.

(** A concatenation split inside its right part. *)
Lemma app_split_right : forall {X} (l1 l2 m1 m2 : list X) x, l1 ++ l2 = m1 ++ x :: m2 -> List.length m2 < List.length l2 ->
    exists m1', l2 = m1' ++ x :: m2.
Proof.
  intros * E Hl; destruct (List.app_eq_app _ _ _ _ E) as (l & [[E1 E2] | [E1 E2]]); [| eauto ].
  destruct l as [| y l]; cbn in E2; [ exists nil; cbn; symmetry; exact E2 |].
  injection E2 as _ E2; exfalso; pose proof (f_equal (@List.length _) E2) as L; rewrite List.length_app in L; lia.
Qed.

(** And inside its left part. *)
Lemma app_split_left : forall {X} (l1 l2 m1 m2 : list X) x, l1 ++ l2 = m1 ++ x :: m2 -> List.length l2 <= List.length m2 ->
    exists Y, m2 = Y ++ l2 /\ l1 = m1 ++ x :: Y.
Proof.
  intros * E Hl; destruct (List.app_eq_app _ _ _ _ E) as (l & [[E1 E2] | [E1 E2]]).
  - destruct l as [| y l]; cbn in E2.
    + exfalso; pose proof (f_equal (@List.length _) E2) as L; cbn in L; lia.
    + injection E2 as <- E2; exists l; split; [ exact E2 | exact E1 ].
  - exfalso; pose proof (f_equal (@List.length _) E2) as L; rewrite List.length_app in L; cbn in L; lia.
Qed.

(** Two concatenations around an element, with tails of one length. *)
Lemma app_cons_inj : forall {X} (l1 l2 r1 r2 : list X) x y, l1 ++ x :: r1 = l2 ++ y :: r2 ->
    List.length r1 = List.length r2 -> l1 = l2 /\ x = y /\ r1 = r2.
Proof.
  intros X; induction l1 as [| a l1 IH]; intros [| b l2] * E Hl; cbn in E.
  - injection E as -> ->; auto.
  - injection E as -> E; exfalso; pose proof (f_equal (@List.length _) E) as L; rewrite List.length_app in L; cbn in L; lia.
  - injection E as <- E; exfalso; pose proof (f_equal (@List.length _) E) as L; rewrite List.length_app in L; cbn in L; lia.
  - injection E as -> E; destruct (IH _ _ _ _ _ E Hl) as (-> & -> & ->); auto.
Qed.

(** The type of a recursive argument, ending in a member, is a relevant
    type. *)
Lemma ptyp_ty_relevant : forall pq D nn pat t ρ b Mj, ind_member D (ptyp_mem t) = Some Mj ->
    ⟦ ptyp_ty pq D nn pat t ⟧ ρ ↘ b -> domain_kind b = ak_relevant.
Proof.
  intros * HMj Eb; destruct t as [j Ps | A t]; cbn [ptyp_ty] in Eb; [| inversion Eb; reflexivity ].
  cbn [ptyp_mem] in HMj; unfold ind_mty, im_ty_at in Eb; rewrite HMj in Eb.
  destruct (im_head Mj).
  - apply eval_apps_exp_ind in Eb as (ns & _ & Hap); rewrite (apps_ind_val _ _ _ _ _ Hap); reflexivity.
  - apply eval_apps_exp_ind in Eb as (ns & _ & Hap); rewrite (apps_ind_val _ _ _ _ _ Hap); reflexivity.
  - apply eval_apps_exp_record in Eb as (ns & _ & Hap); rewrite (apps_record_val _ _ _ _ Hap); reflexivity.
Qed.

(** A parameter tagged with an evaluated kind is taken at that kind
    ([tele_param_kind]). *)
Lemma tele_param_kind_of_nth : forall T n κ A, List.nth_error T n = Some (ce_ass κ A) -> evaluated_kind κ ->
    tele_param_kind T n = κ.
Proof. intros * H Hk; unfold tele_param_kind; rewrite H; destruct Hk; reflexivity. Qed.

(** No parameter is taken as a proof. *)
Lemma tele_param_kind_not_propositional : forall T n, tele_param_kind T n <> ak_propositional.
Proof. intros T n E; pose proof (tele_param_kind_evaluated T n) as Hk; rewrite E in Hk; inversion Hk. Qed.

(** Past the uniform parameters, a member's parameters are its non-uniform
    ones, all relevant ([decl_typed_nparams_kind]). *)
Lemma tele_param_kind_nparams : forall Θ Ξ D, decl_typed Θ Ξ D -> forall k Mk n, ind_member D k = Some Mk -> ind_nu D <= n ->
    tele_param_kind (List.rev (im_params D Mk)) n = ak_relevant.
Proof.
  intros * Hdt k Mk n HM Hn; unfold tele_param_kind, im_params.
  rewrite List.rev_app_distr, List.nth_error_app2 by (rewrite List.length_rev; unfold ind_nu in Hn; exact Hn).
  destruct (List.nth_error (List.rev (im_nparams Mk)) _) as [e |] eqn:He; [| reflexivity ].
  pose proof (List.nth_error_In _ _ He) as Hin; apply List.in_rev in Hin.
  destruct (proj1 (List.Forall_forall _ _) (decl_typed_nparams_ass _ _ _ Hdt _ _ HM) e Hin) as (κ & T & ->).
  destruct (List.in_split _ _ Hin) as (Δ1 & Δ2 & E).
  rewrite (decl_typed_nparams_kind _ _ _ Hdt _ _ _ _ _ _ HM E); reflexivity.
Qed.

(** ** The Elements of a [Π] over a Telescope, Read by a Relation

    [ctx_pi_rel_elem] with a family of values given by a relation [Fr]
    between the arguments so far and the value: each side applies to the
    next argument, when the extensions so far, one more, are related at
    the context PER of the telescope so far over a context [Γ] the base
    environments are related at.  As in [ctx_pi_rel_elem], the [Π]
    extends at the values of its domains, so the premises are stated at
    related extensions with any types. *)
Lemma ctx_pi_rel_elem_by : forall (Fr : list domain -> domain -> Prop) B ts Γ RΓ, tele_ass ts ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> ⊨ List.rev ts ++ Γ ->
    forall E E' xs xs' v v' a a' (i : universe_index) R,
      RΓ E E' -> Fr xs v -> Fr xs' v' ->
      (forall ts1 κ A ts2 R1 vts vts' y y' t t' w, ts = ts1 ++ ce_ass κ A :: ts2 ->
         EF List.rev (ts1 ++ ce_ass κ A :: nil) ++ Γ ≈ List.rev (ts1 ++ ce_ass κ A :: nil) ++ Γ ∈ per_ctx_env ↘ R1 ->
         List.length vts = List.length ts1 -> List.length vts' = List.length ts1 ->
         R1 (env_extend_typed E (vts ++ (y, t) :: nil)) (env_extend_typed E' (vts' ++ (y', t') :: nil)) ->
         Fr (xs ++ List.map fst vts) w ->
         exists u, $| w & y | gc_deps ⍮ gc_stack ↘ u /\ Fr (xs ++ List.map fst vts ++ y :: nil) u) ->
      (forall ts1 κ A ts2 R1 vts vts' y y' t t' w', ts = ts1 ++ ce_ass κ A :: ts2 ->
         EF List.rev (ts1 ++ ce_ass κ A :: nil) ++ Γ ≈ List.rev (ts1 ++ ce_ass κ A :: nil) ++ Γ ∈ per_ctx_env ↘ R1 ->
         List.length vts = List.length ts1 -> List.length vts' = List.length ts1 ->
         R1 (env_extend_typed E (vts ++ (y, t) :: nil)) (env_extend_typed E' (vts' ++ (y', t') :: nil)) ->
         Fr (xs' ++ List.map fst vts') w' ->
         exists u', $| w' & y' | gc_deps ⍮ gc_stack ↘ u' /\ Fr (xs' ++ List.map fst vts' ++ y' :: nil) u') ->
      (forall ts1 κ A ts2 R1 vts vts' w b, ts = ts1 ++ ce_ass κ A :: ts2 ->
         EF List.rev ts1 ++ Γ ≈ List.rev ts1 ++ Γ ∈ per_ctx_env ↘ R1 ->
         List.length vts = List.length ts1 -> List.length vts' = List.length ts1 ->
         R1 (env_extend_typed E vts) (env_extend_typed E' vts') ->
         Fr (xs ++ List.map fst vts) w -> ⟦ A ⟧ env_extend_typed E vts ↘ b ->
         arg_kind gc_deps gc_stack w = domain_kind b) ->
      (forall ts1 κ A ts2 R1 vts vts' w' b', ts = ts1 ++ ce_ass κ A :: ts2 ->
         EF List.rev ts1 ++ Γ ≈ List.rev ts1 ++ Γ ∈ per_ctx_env ↘ R1 ->
         List.length vts = List.length ts1 -> List.length vts' = List.length ts1 ->
         R1 (env_extend_typed E vts) (env_extend_typed E' vts') ->
         Fr (xs' ++ List.map fst vts') w' -> ⟦ A ⟧ env_extend_typed E' vts' ↘ b' ->
         arg_kind gc_deps gc_stack w' = domain_kind b') ->
      ⟦ ctx_pi (List.rev ts) B ⟧ E ↘ a -> ⟦ ctx_pi (List.rev ts) B ⟧ E' ↘ a' ->
      DF a ≈ a' ∈ per_univ_elem i ↘ R ->
      (forall R1 vts vts' w w', EF List.rev ts ++ Γ ≈ List.rev ts ++ Γ ∈ per_ctx_env ↘ R1 ->
         List.length vts = List.length ts -> List.length vts' = List.length ts ->
         R1 (env_extend_typed E vts) (env_extend_typed E' vts') ->
         Fr (xs ++ List.map fst vts) w -> Fr (xs' ++ List.map fst vts') w' ->
         Dom w ≈ w' ∈ per_head B B (env_extend_typed E vts) (env_extend_typed E' vts')) ->
      Dom v ≈ v' ∈ R.
Proof.
  intros Fr B ts; induction ts as [| e ts IH]; intros Γ RΓ Hts HΓ HC * HE Hv Hv' HstL HstR HarL HarR Ha Ha' HR Hbase.
  - cbn [List.rev ctx_pi] in Ha, Ha'.
    specialize (Hbase RΓ nil nil v v' HΓ eq_refl eq_refl HE ltac:(cbn [List.map]; rewrite List.app_nil_r; exact Hv)
                  ltac:(cbn [List.map]; rewrite List.app_nil_r; exact Hv')).
    exact (Hbase _ _ _ _ Ha Ha' HR).
  - assert (He : exists κ A, e = ce_ass κ A) by (inversion Hts as [| ? ? He _]; exact He).
    destruct He as (κ & A & ->).
    assert (Hts' : tele_ass ts) by (inversion Hts; assumption).
    cbn [List.rev] in Ha, Ha', HC; rewrite ctx_pi_snoc in Ha, Ha'.
    rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
    (** The context PER of [Γ] extended by the parameter. *)
    destruct (rel_ctx_wf_ass_typ (rel_ctx_wf_app_r _ _ HC)) as [j HAv].
    pose proof (per_ctx_env_of_typ (κ := κ) HΓ HAv) as HΓA.
    inversion Ha; subst a; inversion Ha'; subst a'.
    match goal with E1 : ⟦ A ⟧ E ↘ ?b |- _ => rename b into a0; rename E1 into Ea0 end.
    match goal with E1 : ⟦ A ⟧ E' ↘ ?b |- _ => rename b into a0'; rename E1 into Ea0' end.
    basic_invert_per_univ_elem HR.
    apply_relation_equivalence.
    (** The two sides take arguments of the domain's sorts. *)
    constructor;
      [ exact (HarL nil _ A ts RΓ nil nil v a0 eq_refl HΓ eq_refl eq_refl HE
                 ltac:(cbn [List.map]; rewrite List.app_nil_r; exact Hv) Ea0)
      | exact (HarR nil _ A ts RΓ nil nil v' a0' eq_refl HΓ eq_refl eq_refl HE
                 ltac:(cbn [List.map]; rewrite List.app_nil_r; exact Hv') Ea0') |].
    intros c c' Hc.
    destruct_rel_mod_eval.
    (** The environments extended by the arguments, at the domain's values,
        are related at the extended context. *)
    pose proof (entry_readable_of_elem equiv_a_a' Hc) as [Rc Rc'].
    assert (HE1 : per_env_extend A A RΓ (E ↦ c ⦂ entry_type_value a0) (E' ↦ c' ⦂ entry_type_value a0'))
      by (apply per_env_extend_intro';
          [ exact HE | eapply per_head_of; [ exact Ea0 | exact Ea0' | exact equiv_a_a' | exact Hc ] | exact Rc | exact Rc' ]).
    destruct (HstL nil _ A ts _ nil nil c c' (entry_type_value a0) (entry_type_value a0') v eq_refl HΓA eq_refl eq_refl HE1
                ltac:(cbn [List.map]; rewrite List.app_nil_r; exact Hv)) as (u & Eu & Hu).
    destruct (HstR nil _ A ts _ nil nil c c' (entry_type_value a0) (entry_type_value a0') v' eq_refl HΓA eq_refl eq_refl HE1
                ltac:(cbn [List.map]; rewrite List.app_nil_r; exact Hv')) as (u' & Eu' & Hu').
    cbn [List.map List.app] in Hu, Hu'.
    econstructor; [ exact Eu | exact Eu' |].
    (** The inversion has replaced the entry's kind by the domain's. *)
    eapply (IH (ce_ass (domain_kind a0) A :: Γ) _ Hts' HΓA HC (E ↦ c ⦂ entry_type_value a0) (E' ↦ c' ⦂ entry_type_value a0')
              (xs ++ c :: nil) (xs' ++ c' :: nil));
      [ exact HE1 | exact Hu | exact Hu' | | | | | eassumption | eassumption | eassumption |].
    + intros ts1 κj Aj ts2 R1 vts vts' y y' t t' w -> HR1 Hlv Hlv' HEv Hw.
      rewrite <- List.app_assoc in Hw; cbn [List.app] in Hw.
      destruct (HstL (ce_ass (domain_kind a0) A :: ts1) κj Aj ts2 R1 ((c, entry_type_value a0) :: vts) ((c', entry_type_value a0') :: vts')
                  y y' t t' w eq_refl ltac:(cbn [List.rev List.app]; rewrite <- List.app_assoc; exact HR1)
                  ltac:(cbn; lia) ltac:(cbn; lia) HEv Hw) as (u0 & Eu0 & Hu0).
      exists u0; split; [ exact Eu0 |].
      rewrite <- List.app_assoc; cbn [List.map List.app fst] in Hu0 |- *; exact Hu0.
    + intros ts1 κj Aj ts2 R1 vts vts' y y' t t' w' -> HR1 Hlv Hlv' HEv Hw'.
      rewrite <- List.app_assoc in Hw'; cbn [List.app] in Hw'.
      destruct (HstR (ce_ass (domain_kind a0) A :: ts1) κj Aj ts2 R1 ((c, entry_type_value a0) :: vts) ((c', entry_type_value a0') :: vts')
                  y y' t t' w' eq_refl ltac:(cbn [List.rev List.app]; rewrite <- List.app_assoc; exact HR1)
                  ltac:(cbn; lia) ltac:(cbn; lia) HEv Hw') as (u0 & Eu0 & Hu0).
      exists u0; split; [ exact Eu0 |].
      rewrite <- List.app_assoc; cbn [List.map List.app fst] in Hu0 |- *; exact Hu0.
    + intros ts1 κj Aj ts2 R1 vts vts' w b -> HR1 Hlv Hlv' HEv Hw Eb.
      rewrite <- List.app_assoc in Hw; cbn [List.app] in Hw.
      exact (HarL (ce_ass (domain_kind a0) A :: ts1) κj Aj ts2 R1 ((c, entry_type_value a0) :: vts) ((c', entry_type_value a0') :: vts') w b eq_refl
               ltac:(cbn [List.rev]; rewrite <- List.app_assoc; exact HR1) ltac:(cbn; lia) ltac:(cbn; lia) HEv Hw Eb).
    + intros ts1 κj Aj ts2 R1 vts vts' w' b' -> HR1 Hlv Hlv' HEv Hw' Eb'.
      rewrite <- List.app_assoc in Hw'; cbn [List.app] in Hw'.
      exact (HarR (ce_ass (domain_kind a0) A :: ts1) κj Aj ts2 R1 ((c, entry_type_value a0) :: vts) ((c', entry_type_value a0') :: vts') w' b' eq_refl
               ltac:(cbn [List.rev]; rewrite <- List.app_assoc; exact HR1) ltac:(cbn; lia) ltac:(cbn; lia) HEv Hw' Eb').
    + intros R1 vts vts' w w' HR1 Hlv Hlv' HEv Hw Hw'.
      rewrite <- List.app_assoc in Hw, Hw'; cbn [List.app] in Hw, Hw'.
      exact (Hbase R1 ((c, entry_type_value a0) :: vts) ((c', entry_type_value a0') :: vts') w w'
               ltac:(cbn [List.rev]; rewrite <- List.app_assoc; exact HR1) ltac:(cbn; lia) ltac:(cbn; lia) HEv Hw Hw').
Qed.

(** ** The Relation of a Member's Type

    The type of the member [k] at the uniform parameters as variables,
    after more variables [zs], at two related environments: its relation
    is the group's at [k].  At a declared member it is the group's
    canonical one directly; at a view, by the agreement of the view with
    its container ([view_end_rel_all]); at a record view, by the coherence
    of the record view with its record ([rview_end_rel_all]). *)
Lemma member_type_rel : forall P p D, valid_groups P -> P p D ->
    forall k Mk ups ups' Z RZ zs zs' nn L Ns bs bs' a a' i R, ind_member D k = Some Mk ->
    List.length ups = ind_nu D -> per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
    ⊨ Z ++ ind_uparams D -> EF Z ++ ind_uparams D ≈ Z ++ ind_uparams D ∈ per_ctx_env ↘ RZ ->
    List.length zs = List.length Z -> List.length zs' = List.length Z -> L + nn = List.length zs ->
    RZ (components_env D ups (List.rev Z) zs) (components_env D ups' (List.rev Z) zs') ->
    List.length Ns = im_nn Mk ->
    ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups (List.rev Z) zs ↘ bs ->
    ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups' (List.rev Z) zs' ↘ bs' ->
    ⟦ ind_mty p D k (ind_uvars D nn L) Ns ⟧ components_env D ups (List.rev Z) zs ↘ a ->
    ⟦ ind_mty p D k (ind_uvars D nn L) Ns ⟧ components_env D ups' (List.rev Z) zs' ↘ a' ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    (R <~> grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups) k ups ups' bs bs').
Proof.
  intros P p D HP HPD * HM Hu Hgu HZ HRZ Hlz Hlz' HL HE HlN Ebs Ebs' Ea Ea' HR.
  pose proof (valid_groups_valid P HP p D HPD) as Hg.
  pose proof (containers_valid_of_groups P HP p D HPD) as Hcv.
  pose proof (uparams_refl_l D (valid_group_valid _ _ Hg) (valid_group_closed _ _ Hg) _ _ Hgu) as Hgd.
  pose proof (length_ups_gargs D _ _ Hgu Hu) as Hu'.
  pose proof (uparams_refl_l D (valid_group_valid _ _ Hg) (valid_group_closed _ _ Hg) _ _
                (uparams_sym D (valid_group_valid _ _ Hg) (valid_group_closed _ _ Hg) _ _ Hgu Hu)) as Hgd'.
  assert (HPZ : PER RZ) by (eapply per_env_PER; exact HRZ).
  assert (HEl : RZ (components_env D ups (List.rev Z) zs) (components_env D ups (List.rev Z) zs)) by (etransitivity; [ exact HE | symmetry; exact HE ]).
  assert (HEr : RZ (components_env D ups' (List.rev Z) zs') (components_env D ups' (List.rev Z) zs')) by (etransitivity; [ symmetry; exact HE | exact HE ]).
  destruct (im_head Mk) as [pm | qc kc Is vm | qr Is fl] eqn:Hh.
  3: { (** A record view: the record at its instance, of no non-uniform
           parameter. *)
       destruct (eval_mty_inv_rview _ _ _ _ _ _ _ _ _ _ _ HM Hh Ea) as (cs & bs0 & Ecs & Ebs0 & ->).
       destruct (eval_mty_inv_rview _ _ _ _ _ _ _ _ _ _ _ HM Hh Ea') as (cs' & bs0' & Ecs' & Ebs0' & ->).
       pose proof (functional_eval_exps' _ _ _ _ Ebs0 Ebs) as ->; pose proof (functional_eval_exps' _ _ _ _ Ebs0' Ebs') as ->.
       pose proof (rview_struct_nparams _ _ _ (decl_typed_record_struct _ _ _ (valid_group_typed _ _ Hg)) _ _ _ _ _ HM Hh) as Hnp.
       unfold im_nn in HlN; rewrite Hnp in HlN; destruct Ns; [| discriminate HlN ].
       inversion Ebs; subst; inversion Ebs'; subst; rewrite !List.app_nil_r in HR.
       destruct (valid_group_records _ _ Hg _ _ _ _ _ HM Hh) as [R0 HR0].
       destruct (rview_pre_values p D Hg k Mk qr Is fl R0 ups Z RZ zs nn L cs HM Hh HR0 Hu Hgd HZ HRZ Hlz HL HEl Ecs)
         as (cups & Ecups & Hgc).
       destruct (rview_pre_values p D Hg k Mk qr Is fl R0 ups' Z RZ zs' nn L cs' HM Hh HR0 Hu' Hgd' HZ HRZ Hlz' ltac:(lia)
                   HEr Ecs') as (cups' & Ecups' & Hgc').
       exact (rview_end_rel_all P p D HP HPD ups ups' Hgu Hu k Mk qr Is fl R0 cups cups' HM Hh (valid_rview_record_lookup _ _ HR0)
                Ecups Ecups' cs cs' i R Hgc Hgc' HR). }
  all: destruct (eval_mty_inv _ _ _ _ _ _ _ _ HM ltac:(unfold im_is_rview; rewrite Hh; reflexivity) Ea) as (cs & bs0 & Ecs & Ebs0 & ->);
       destruct (eval_mty_inv _ _ _ _ _ _ _ _ HM ltac:(unfold im_is_rview; rewrite Hh; reflexivity) Ea') as (cs' & bs0' & Ecs' & Ebs0' & ->);
       pose proof (functional_eval_exps' _ _ _ _ Ebs0 Ebs) as ->; pose proof (functional_eval_exps' _ _ _ _ Ebs0' Ebs') as ->.
  - unfold im_pre, im_ref in *; rewrite Hh in *; cbn [fst snd] in *.
    assert (HU : forall u w, List.length u = ind_nu D -> List.length w = List.length Z ->
                   ⟦ ind_uvars D nn L ⟧* gc_deps ⍮ gc_stack ⍮ components_env D u (List.rev Z) w ↘ u)
      by (intros u w Hlu Hlw; apply eval_uvars_components; lia).
    pose proof (functional_eval_exps' _ _ _ _ Ecs (HU _ _ Hu Hlz)) as ->.
    pose proof (functional_eval_exps' _ _ _ _ Ecs' (HU _ _ Hu' Hlz')) as ->.
    exact (proj1 (valid_group_type_rel_base p D Hg k Mk pm ups ups' ups ups' bs bs' i R HM Hh Hgu Hu Hgd Hgd' HR)).
  - destruct (decl_typed_view _ _ _ (valid_group_typed _ _ Hg) _ _ _ _ _ _ HM Hh) as (Dq & Mk' & Hq & _).
    assert (Ecs1 : ⟦ im_pre Mk (ind_uvars D nn L) ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups (List.rev Z) zs ↘ cs) by exact Ecs.
    assert (Ecs1' : ⟦ im_pre Mk (ind_uvars D nn L) ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups' (List.rev Z) zs' ↘ cs') by exact Ecs'.
    destruct (view_pre_values p D Hg Hcv k Mk qc kc Is vm Dq ups Z RZ zs nn L cs HM Hh Hq Hu Hgd HZ HRZ Hlz HL HEl Ecs1)
      as (cups & Ecups & Hgc).
    destruct (view_pre_values p D Hg Hcv k Mk qc kc Is vm Dq ups' Z RZ zs' nn L cs' HM Hh Hq Hu' Hgd' HZ HRZ Hlz' ltac:(lia)
                HEr Ecs1') as (cups' & Ecups' & Hgc').
    unfold im_ref in HR; rewrite Hh in HR; cbn [fst snd] in HR.
    exact (view_end_rel_all P p D HP HPD ups ups' Hgu Hu k Mk qc kc Is vm Dq cups cups' HM Hh Hq Ecups Ecups'
             cs cs' bs bs' i R Hgc Hgc' HR).
Qed.

(** ** A View's Constructor at its Container

    A constructor of a view is one of the container's member the view
    views, with corresponding arguments. *)
Lemma view_con_container : forall (p : qname) D, grp_tele_ass D -> decl_typed gc_deps gc_stack D ->
    forall k Mk qc kc Is vm Dq Mk' c gs, ind_member D k = Some Mk -> im_head Mk = mh_view qc kc Is vm ->
    ind_lookup gc_deps gc_stack qc = Some Dq -> ind_member Dq kc = Some Mk' -> ind_con Mk c = Some gs ->
    exists gs', ind_con Mk' c = Some gs' /\ cargs_correspond vm gs' gs.
Proof.
  intros p D Hass Hdt * HM Hh Hq HMk' Hc.
  destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (Dq2 & Mk2 & Hq2 & HMk2 & _ & _ & _ & Hvm & _).
  rewrite Hq in Hq2; injection Hq2 as <-; rewrite HMk' in HMk2; injection HMk2 as <-.
  destruct (view_agree_members p D k Mk qc kc Is vm Dq Hass HM Hh Hq kc Mk' HMk') as (v & Mv & Hvmb).
  assert (v = k) as -> by (pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvmb) as Hv; rewrite Hvm in Hv; congruence).
  assert (Mv = Mk) as -> by (pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMv; rewrite HM in HMv; congruence).
  exact (view_member_cons' _ _ _ _ _ _ _ _ _ Hvmb _ _ Hc).
Qed.

(** ** The Values of a Constructor along its Arguments

    The value of the constructor [c] of the member [k] after the arguments
    [xs]: the constructor at them for a declared member; for a view, the
    view's constructor before the last uniform parameter, then the
    container's constructor at the view's instance at the uniform
    parameters, and the rest. *)
Inductive con_value (p : qname) (D : ind_decl) (k : nat) (Mk : imember) (c : String.string) : list domain -> domain -> Prop :=
(** A declared member: the constructor at the arguments *)
| con_value_decl : forall pm xs, im_head Mk = mh_decl pm -> con_value p D k Mk c xs (d_con p k c xs)
(** A view, before its last uniform parameter: the view's constructor *)
| con_value_view_uparams : forall qc kc Is vm xs, im_head Mk = mh_view qc kc Is vm -> List.length xs < ind_nu D ->
    con_value p D k Mk c xs (d_con p k c xs)
(** A view, after its uniform parameters: the container's constructor at
    the instance, then the rest *)
| con_value_view : forall qc kc Is vm xs cs, im_head Mk = mh_view qc kc Is vm -> ind_nu D <= List.length xs ->
    ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D (List.firstn (ind_nu D) xs) ↘ cs ->
    con_value p D k Mk c xs (d_con qc kc c (cs ++ List.skipn (ind_nu D) xs))
(** A record view, before its last argument: its pseudo-constructor at
    the arguments so far *)
| con_value_rview : forall qr Is fl xs, im_head Mk = mh_record qr Is fl -> List.length xs < ind_nu D + List.length fl ->
    con_value p D k Mk c xs (d_con p k c xs)
(** A record view, at all its arguments: the tuple of its fields, by
    name *)
| con_value_rview_full : forall qr Is fl xs, im_head Mk = mh_record qr Is fl -> List.length xs = ind_nu D + List.length fl ->
    con_value p D k Mk c xs (d_tuple (List.combine fl (List.skipn (ind_nu D) xs))).

(** ** The Closed Environments of a Constructor's Telescope *)

(** The closed environment of a telescope after the uniform parameters:
    the components after them. *)
Lemma env_tele_closed_components : forall D ups Z zs, List.length ups = ind_nu D ->
    env_tele nil (List.rev (Z ++ ind_uparams D)) (ups ++ zs) = components_env D ups (List.rev Z) zs.
Proof. intros * Hu; unfold components_env, decl_env; apply env_tele_closed_app; exact Hu. Qed.

(** The non-uniform parameters as variables, past the arguments: their
    values. *)
Lemma eval_nvars_components : forall D ups Tn Ta ns as1, List.length ns = List.length Tn ->
    ⟦ vars_from (List.length as1) (List.length ns) ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups (Tn ++ Ta) (ns ++ as1) ↘ ns.
Proof.
  intros * Hl; unfold components_env, env_tele.
  rewrite tele_entries_app by exact Hl.
  pose proof (eval_vars_from_args (tele_entries (decl_env D ups) Tn ns) (decl_env D ups)
                (tele_entries (env_tele (decl_env D ups) Tn ns) Ta as1)) as H.
  rewrite tele_entries_values, !tele_entries_length in H; exact H.
Qed.

(** ** The Parameters of a Member, Split at the Uniform Ones *)
Lemma params_valid_split : forall D k Mk Γ Ps, decl_closed D -> ind_member D k = Some Mk ->
    List.length Ps = im_np D Mk ->
    (forall j P T, List.nth_error Ps j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id Ps) j = Some T -> Γ ⊨ P : T) ->
    (forall j U T, List.nth_error (List.firstn (ind_nu D) Ps) j = Some U ->
       List.nth_error (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) j = Some T -> Γ ⊨ U : T) /\
    (forall j N T, List.nth_error (List.skipn (ind_nu D) Ps) j = Some N ->
       List.nth_error (tele_insts (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) (List.skipn (ind_nu D) Ps)) j
         = Some T ->
       Γ ⊨ N : T).
Proof.
  intros * Hc HM Hl HPs.
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in Hl; lia).
  assert (Hti : tele_insts (im_params D Mk) Id Ps
                = tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)
                  ++ tele_insts (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) (List.skipn (ind_nu D) Ps)).
  { rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; unfold im_params; apply tele_insts_app;
      [ exact (decl_uparams_ass D Hc) | rewrite HUl; reflexivity ]. }
  assert (Hl2 : List.length (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) = ind_nu D)
    by (rewrite length_tele_insts by exact (decl_uparams_ass D Hc); rewrite HUl; unfold ind_nu; lia).
  split; intros j N T HN HT.
  - apply (HPs j); [ rewrite <- (List.firstn_skipn (ind_nu D) Ps), List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HN |].
    rewrite Hti, List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HT.
  - apply (HPs (ind_nu D + j)).
    + rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; rewrite List.nth_error_app2 by lia.
      rewrite HUl; replace (ind_nu D + j - ind_nu D) with j by lia; exact HN.
    + rewrite Hti, List.nth_error_app2 by lia; rewrite Hl2; replace (ind_nu D + j - ind_nu D) with j by lia; exact HT.
Qed.

(** The type of a member at its parameters as variables, past more
    variables [Φ], is a valid type. *)
Lemma mty_vars_valid_at : forall p D, valid_group p D -> containers_valid D ->
    forall k Mk Φ, ind_member D k = Some Mk -> ⊨ Φ ++ im_params D Mk ->
    exists i : nat, Φ ++ im_params D Mk
      ⊨ ind_mty p D k (ind_uvars D (im_nn Mk) (List.length Φ)) (vars_from (List.length Φ) (im_nn Mk)) : Typeω@i.
Proof.
  intros p D Hg Hcv k Mk Φ HM HP.
  pose proof (valid_group_valid _ _ Hg) as HD; pose proof (valid_group_closed _ _ Hg) as Hc.
  assert (Hvars : forall j N T, List.nth_error (vars_from (List.length Φ) (im_np D Mk)) j = Some N ->
             List.nth_error (tele_insts (im_params D Mk) Id (vars_from (List.length Φ) (im_np D Mk))) j = Some T ->
             Φ ++ im_params D Mk ⊨ N : T).
  { intros j N T HN HT.
    rewrite <- length_im_params in HN, HT.
    exact (valid_vars_tele Φ (im_params D Mk) (member_params_ass D Hc _ _ HM) (decl_closed_params D _ _ Hc HM)
             (decl_params_mvc _ _ _ (valid_group_typed _ _ Hg) _ _ HM) HP _ _ _ HN HT). }
  destruct (params_valid_split D k Mk (Φ ++ im_params D Mk) (vars_from (List.length Φ) (im_np D Mk)) Hc HM (length_vars_from _ _) Hvars)
    as [_ HNs].
  assert (Hsk : List.skipn (ind_nu D) (vars_from (List.length Φ) (im_np D Mk)) = vars_from (List.length Φ) (im_nn Mk)).
  { unfold im_np; rewrite Nat.add_comm, <- vars_from_app.
    rewrite skipn_app_len by (rewrite length_vars_from; reflexivity); reflexivity. }
  assert (Hfs : List.firstn (ind_nu D) (vars_from (List.length Φ) (im_np D Mk)) = ind_uvars D (im_nn Mk) (List.length Φ)).
  { unfold im_np, ind_uvars; rewrite Nat.add_comm, <- vars_from_app.
    rewrite firstn_app_len by (rewrite length_vars_from; reflexivity); reflexivity. }
  rewrite Hsk, Hfs in HNs.
  assert (HZ : ⊨ (Φ ++ im_nparams Mk) ++ ind_uparams D) by (rewrite <- List.app_assoc; exact HP).
  destruct (valid_group_mty_valid p D Hg Hcv k Mk (Φ ++ im_nparams Mk) (im_nn Mk) (List.length Φ) (vars_from (List.length Φ) (im_nn Mk)) HM HZ
              ltac:(rewrite List.length_app, length_im_nparams; lia) (length_vars_from _ _)
              ltac:(intros * HN HT; rewrite <- List.app_assoc; exact (HNs _ _ _ HN HT))
              (vars_from_scoped (List.length Φ) (im_nn Mk) (List.length ((Φ ++ im_nparams Mk) ++ ind_uparams D))
                 ltac:(rewrite !List.length_app, length_im_nparams; lia))) as [i Hi].
  exists i; rewrite <- List.app_assoc in Hi; exact Hi.
Qed.

(** ** The Constructor as an Element of its Type *)
Section ConValue.
  Variable (P : qname -> ind_decl -> Prop).
  Variables (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups P) (HPD : P p D).
  Let Hg := valid_groups_valid P HP p D HPD.
  Let Hcv := containers_valid_of_groups P HP p D HPD.
  Let HD := valid_group_valid _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hass := valid_group_ass _ _ Hg.
  Let Hdt := valid_group_typed _ _ Hg.
  Variables (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
  Hypotheses (HM : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs).
  Let HΨ := valid_group_cargs_sem p D Hg Hcv k Mk c gs HM Hcon.

  (** A record view's constructor has one argument per field. *)
  Lemma con_rview_len : forall qr Is fl, im_head Mk = mh_record qr Is fl -> List.length gs = List.length fl.
  Proof.
    intros * Hh.
    destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HM Hh) as (gs0 & Hcs & Hl).
    pose proof Hcon as Hc0; unfold ind_con in Hc0; rewrite Hcs in Hc0; cbn in Hc0.
    destruct (String.eqb c rview_con); [ injection Hc0 as <-; exact Hl | discriminate Hc0 ].
  Qed.

  Lemma con_rview_cons : forall qr Is fl, im_head Mk = mh_record qr Is fl -> im_cons Mk = (c, gs) :: nil.
  Proof.
    intros * Hh.
    destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HM Hh) as (gs0 & Hcs & _).
    pose proof Hcon as Hc0; unfold ind_con in Hc0; rewrite Hcs in Hc0 |- *; cbn in Hc0.
    destruct (String.eqb c rview_con) eqn:E; [ injection Hc0 as -> | discriminate Hc0 ].
    apply String.eqb_eq in E; rewrite E; reflexivity.
  Qed.

  Lemma con_rview_np : forall qr Is fl, im_head Mk = mh_record qr Is fl -> im_np D Mk = ind_nu D.
  Proof.
    intros * Hh; unfold im_np, im_nn.
    rewrite (rview_struct_nparams _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HM Hh); cbn; lia.
  Qed.

  (** The constructor, at no argument. *)
  Lemma con_value_start : forall ρ, exists v, ⟦ a_con p k c ⟧ ρ ↘ v /\ con_value p D k Mk c nil v.
  Proof.
    intros ρ.
    destruct (im_head Mk) as [pm | qc kc Is vm | qr Is fl] eqn:Hh.
    3: { (** A record view: its pseudo-constructor, or at once the empty
             tuple. *)
         destruct (Nat.eq_dec (ind_nu D) 0) as [H0 | H0]; [ destruct fl as [| f fl] |].
         - exists (d_tuple nil); split.
           + eapply eval_exp_con_rview_empty; [ exact (valid_group_lookup _ _ Hg) | exact HM | exact Hh | exact H0 ].
           + pose proof (con_value_rview_full p D k Mk c qr Is nil nil Hh ltac:(cbn; lia)) as H; cbn in H; exact H.
         - exists (d_con p k c nil); split.
           + eapply eval_exp_con_rview; [ exact (valid_group_lookup _ _ Hg) | exact HM | exact Hh | exact H0 | cbn; lia ].
           + apply (con_value_rview p D k Mk c qr Is (f :: fl) nil Hh); cbn; lia.
         - exists (d_con p k c nil); split.
           + eapply eval_exp_con; [ exact (valid_group_lookup _ _ Hg) | exact HM |].
             unfold im_starts, im_is_decl; rewrite Hh; cbn [orb]; apply Nat.ltb_lt; lia.
           + apply (con_value_rview p D k Mk c qr Is fl nil Hh); cbn; lia. }
    - exists (d_con p k c nil); split; [| exact (con_value_decl _ _ _ _ _ pm nil Hh) ].
      eapply eval_exp_con; [ exact (valid_group_lookup _ _ Hg) | exact HM |].
      unfold im_starts, im_is_decl; rewrite Hh; reflexivity.
    - destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (Dq & Mk' & Hq & _).
      destruct (Nat.eq_dec (ind_nu D) 0) as [H0 | H0].
      + assert (Hg0 : per_gargs (List.rev (ind_uparams D)) nil nil nil nil) by constructor.
        destruct (valid_group_views_view_args_values p D Hg Hcv _ _ _ _ _ _ _ HM Hh Hq nil nil Hg0 ltac:(cbn [List.length]; lia))
          as (cups & _ & Ecups & _ & _).
        exists (d_con qc kc c (cups ++ List.skipn (ind_nu D) nil)); split.
        * rewrite List.skipn_nil, List.app_nil_r.
          eapply eval_exp_con_view; [ exact (valid_group_lookup _ _ Hg) | exact HM | exact Hh | exact H0 | exact Ecups ].
        * apply (con_value_view p D k Mk c qc kc Is vm nil cups Hh ltac:(cbn [List.length]; lia)).
          rewrite List.firstn_nil; exact Ecups.
      + exists (d_con p k c nil); split; [| exact (con_value_view_uparams p D k Mk c qc kc Is vm nil Hh ltac:(cbn [List.length]; lia)) ].
        eapply eval_exp_con; [ exact (valid_group_lookup _ _ Hg) | exact HM |].
        unfold im_starts, im_is_decl; rewrite Hh; cbn [orb]; apply Nat.ltb_lt; lia.
  Qed.

  (** The constructor takes the next argument, its view's instance
      evaluating at the last uniform parameter. *)
  Lemma con_value_step : forall ys y w, List.length ys < im_np D Mk + List.length gs ->
      (forall qc kc Is vm, im_head Mk = mh_view qc kc Is vm -> S (List.length ys) = ind_nu D ->
         exists cs, ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D (ys ++ y :: nil) ↘ cs) ->
      con_value p D k Mk c ys w -> exists u, $| w & y | gc_deps ⍮ gc_stack ↘ u /\ con_value p D k Mk c (ys ++ y :: nil) u.
  Proof.
    intros ys y w Hlys Hev Hw.
    inversion Hw as [pm xs Hh | qc kc Is vm xs Hh Hlt | qc kc Is vm xs cs Hh Hle Ecs | qr Is fl xs Hh Hlt | qr Is fl xs Hh Hle]; subst.
    4: { (** A record view: its pseudo-constructor takes the next argument;
             at the last one, the tuple of the fields. *)
         pose proof (con_rview_len _ _ _ Hh) as Hlg; pose proof (con_rview_np _ _ _ Hh) as Hnp.
         destruct (Nat.lt_ge_cases (S (List.length ys)) (ind_nu D + List.length fl)) as [Hlt' | Hge].
         - exists (d_con p k c (ys ++ y :: nil)); split.
           + eapply eval_app_con_rview; [ exact (valid_group_lookup _ _ Hg) | exact HM | exact Hh | exact Hlt' ].
           + apply (con_value_rview _ _ _ _ _ qr Is fl _ Hh); rewrite List.length_app; cbn [List.length]; lia.
         - exists (d_tuple (List.combine fl (List.skipn (ind_nu D) (ys ++ y :: nil)))); split.
           + eapply eval_app_con_rview_full; [ exact (valid_group_lookup _ _ Hg) | exact HM | exact Hh | lia ].
           + apply (con_value_rview_full _ _ _ _ _ qr Is fl _ Hh); rewrite List.length_app; cbn [List.length]; lia. }
    4: { pose proof (con_rview_len _ _ _ Hh) as Hlg; pose proof (con_rview_np _ _ _ Hh) as Hnp; lia. }
    - exists (d_con p k c (ys ++ y :: nil)); split; [| exact (con_value_decl _ _ _ _ _ pm _ Hh) ].
      eapply eval_app_con; [ exact (valid_group_lookup _ _ Hg) | exact HM | exact Hh | exact Hcon | exact Hlys ].
    - destruct (Nat.lt_ge_cases (S (List.length ys)) (ind_nu D)) as [Hlt' | Hge].
      + exists (d_con p k c (ys ++ y :: nil)); split.
        * eapply eval_app_con_view; [ exact (valid_group_lookup _ _ Hg) | exact HM | exact Hh | exact Hlt' ].
        * apply (con_value_view_uparams _ _ _ _ _ qc kc Is vm _ Hh); rewrite List.length_app; cbn [List.length]; lia.
      + destruct (Hev _ _ _ _ Hh ltac:(lia)) as [cs Ecs].
        assert (Hl1 : List.length (ys ++ y :: nil) = ind_nu D) by (rewrite List.length_app; cbn [List.length]; lia).
        exists (d_con qc kc c (cs ++ List.skipn (ind_nu D) (ys ++ y :: nil))); split.
        * rewrite List.skipn_all2, List.app_nil_r by lia.
          eapply eval_app_con_view_ups; [ exact (valid_group_lookup _ _ Hg) | exact HM | exact Hh | lia | exact Ecs ].
        * apply (con_value_view p D k Mk c qc kc Is vm (ys ++ y :: nil) cs Hh ltac:(lia)).
          rewrite List.firstn_all2 by lia; exact Ecs.
    - (** The container's constructor takes it. *)
      destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (Dq & Mk' & Hq & HMk' & Hkd & HIl & _ & Hvm & _).
      pose proof (Hcv _ _ _ _ _ _ _ HM Hh Hq) as HgQ.
      assert (Hhd : exists pm, im_head Mk' = mh_decl pm).
      { pose proof (proj2 (decl_typed_order _ _ _ (valid_group_typed _ _ HgQ) _ _ HMk') Hkd) as Hd.
        unfold im_is_decl in Hd; destruct (im_head Mk'); [ eauto | discriminate .. ]. }
      destruct Hhd as [pm Hhd].
      destruct (view_con_container p D Hass Hdt k Mk qc kc Is vm Dq Mk' c gs HM Hh Hq HMk' Hcon) as (gs' & Hcon' & Hcorr).
      destruct (view_agree_members p D k Mk qc kc Is vm Dq Hass HM Hh Hq kc Mk' HMk') as (v & Mv & Hvmb).
      assert (v = k) as -> by (pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvmb) as Hv; rewrite Hvm in Hv; congruence).
      assert (Mv = Mk) as -> by (pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMv; rewrite HM in HMv; congruence).
      pose proof (view_member_nn _ _ _ _ _ _ _ _ _ Hvmb) as Hnn.
      pose proof (cargs_correspond_len _ _ _ Hcorr) as Hlg.
      pose proof (eval_exps_length _ _ _ Ecs) as Hlcs.
      exists (d_con qc kc c (cs ++ List.skipn (ind_nu D) (ys ++ y :: nil))); split.
      + rewrite List.skipn_app; replace (ind_nu D - List.length ys) with 0 by lia; cbn [List.skipn].
        rewrite List.app_assoc.
        eapply eval_app_con; [ exact Hq | exact HMk' | exact Hhd | exact Hcon' |].
        rewrite List.length_app, List.length_skipn, Hlcs, HIl; unfold im_np in *; lia.
      + apply (con_value_view p D k Mk c qc kc Is vm (ys ++ y :: nil) cs Hh ltac:(rewrite List.length_app; lia)).
        rewrite List.firstn_app; replace (ind_nu D - List.length ys) with 0 by lia; cbn [List.firstn]; rewrite List.app_nil_r.
        exact Ecs.
  Qed.

  (** At all the arguments, the constructor is the member's, as stored by
      the group: at uniform arguments of the member's own number. *)
  Lemma con_value_full : forall zs w, im_is_rview Mk = false -> List.length zs = im_np D Mk + List.length gs ->
      con_value p D k Mk c zs w ->
      exists cs, List.length cs = im_unu D Mk /\
        w = d_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c (cs ++ List.skipn (ind_nu D) zs).
  Proof.
    intros zs w Hrv Hlz Hw.
    inversion Hw as [pm xs Hh | qc kc Is vm xs Hh Hlt | qc kc Is vm xs cs Hh Hle Ecs | qr Is fl xs Hh _ | qr Is fl xs Hh _]; subst;
      try (exfalso; exact (not_rview_record _ _ _ _ Hrv Hh)).
    - exists (List.firstn (ind_nu D) zs); unfold im_unu, im_ref; rewrite Hh; cbn [fst snd].
      split; [ rewrite List.length_firstn; unfold im_np in *; lia | rewrite List.firstn_skipn; reflexivity ].
    - unfold im_np in *; lia.
    - exists cs; unfold im_unu, im_ref; rewrite Hh; cbn [fst snd].
      split; [ exact (eval_exps_length _ _ _ Ecs) | reflexivity ].
  Qed.

  (** At a record view, the tuple of the fields. *)
  Lemma con_value_full_rview : forall qr Is fl zs w, im_head Mk = mh_record qr Is fl ->
      List.length zs = im_np D Mk + List.length gs -> con_value p D k Mk c zs w ->
      w = d_tuple (List.combine fl (List.skipn (ind_nu D) zs)).
  Proof.
    intros * Hh Hlz Hw.
    pose proof (con_rview_len _ _ _ Hh) as Hlg; pose proof (con_rview_np _ _ _ Hh) as Hnp.
    inversion Hw as [pm xs Hh' | qc kc Is' vm xs Hh' Hlt | qc kc Is' vm xs cs Hh' Hle Ecs | qr' Is' fl' xs Hh' Hlt | qr' Is' fl' xs Hh' _];
      subst; rewrite Hh in Hh'; try discriminate Hh'; injection Hh' as <- <- <-; [ lia | reflexivity ].
  Qed.

  (** The constructor's value at related parameters and arguments, at its
      codomain. *)
  Lemma con_at_args : forall zs zs' w w', per_gargs (List.rev (cargs_ctx p D Mk gs ++ im_params D Mk)) nil nil zs zs' ->
      List.length zs = List.length (cargs_ctx p D Mk gs ++ im_params D Mk) ->
      con_value p D k Mk c zs w -> con_value p D k Mk c zs' w' ->
      Dom w ≈ w' ∈ per_head (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)))
        (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)))
        (env_tele nil (List.rev (cargs_ctx p D Mk gs ++ im_params D Mk)) zs)
        (env_tele nil (List.rev (cargs_ctx p D Mk gs ++ im_params D Mk)) zs').
  Proof.
    intros * Hg0 Hlz Hw Hw' i0 Rb bb bb' Ebb Ebb' HRb.
    rewrite List.length_app, length_cargs_ctx, length_im_params in Hlz.
    pose proof (per_gargs_length _ _ _ _ _ Hg0) as [Hlz' _].
    set (ps := List.firstn (im_np D Mk) zs); set (ps' := List.firstn (im_np D Mk) zs').
    set (as1 := List.skipn (im_np D Mk) zs); set (as1' := List.skipn (im_np D Mk) zs').
    assert (Hz : zs = ps ++ as1) by (symmetry; apply List.firstn_skipn).
    assert (Hz' : zs' = ps' ++ as1') by (symmetry; apply List.firstn_skipn).
    assert (Hlp : List.length ps = im_np D Mk) by (unfold ps; rewrite List.length_firstn; lia).
    assert (Hlp' : List.length ps' = im_np D Mk) by (unfold ps'; rewrite List.length_firstn; lia).
    assert (Hla : List.length as1 = List.length gs) by (unfold as1; rewrite List.length_skipn; lia).
    assert (Hla' : List.length as1' = List.length gs) by (unfold as1'; rewrite List.length_skipn; lia).
    pose proof Hg0 as Hg1; rewrite Hz, Hz', List.rev_app_distr in Hg1.
    assert (L1 : List.length ps = List.length (List.rev (im_params D Mk))) by (rewrite List.length_rev, length_im_params; exact Hlp).
    assert (L2 : List.length ps' = List.length (List.rev (im_params D Mk))) by (rewrite List.length_rev, length_im_params; exact Hlp').
    destruct (per_gargs_app _ _ _ _ _ _ _ _ L1 Hg1 L2) as [Hgp Hga].
    set (ups := List.firstn (ind_nu D) ps); set (ns := List.skipn (ind_nu D) ps).
    set (ups' := List.firstn (ind_nu D) ps'); set (ns' := List.skipn (ind_nu D) ps').
    assert (Hps : ps = ups ++ ns) by (symmetry; apply List.firstn_skipn).
    assert (Hps' : ps' = ups' ++ ns') by (symmetry; apply List.firstn_skipn).
    pose proof (proj1 (params_split_rel D HD Hc k Mk HM _ _ _ _ Hgp Hlp)) as Hgu; fold ups ups' in Hgu.
    assert (Hu : List.length ups = ind_nu D) by (unfold ups; rewrite List.length_firstn; unfold im_np in *; lia).
    assert (Hlns : List.length ns = im_nn Mk) by (unfold ns; rewrite List.length_skipn; unfold im_np in *; lia).
    assert (Hlns' : List.length ns' = im_nn Mk) by (unfold ns'; rewrite List.length_skipn; unfold im_np in *; lia).
    (** The relation of the codomain. *)
    set (Z := cargs_ctx p D Mk gs ++ im_nparams Mk).
    assert (HZ : ⊨ Z ++ ind_uparams D) by (unfold Z; rewrite <- List.app_assoc; exact HΨ).
    destruct (rel_ctx_wf_per_ctx_env HZ) as [RZ HRZ].
    assert (HlZ : List.length Z = im_nn Mk + List.length gs)
      by (unfold Z; rewrite List.length_app, length_cargs_ctx, length_im_nparams; lia).
    assert (Ezs : zs = ups ++ ns ++ as1) by (rewrite Hz, Hps, List.app_assoc; reflexivity).
    assert (Ezs' : zs' = ups' ++ ns' ++ as1') by (rewrite Hz', Hps', List.app_assoc; reflexivity).
    assert (Hu0' : List.length ups' = ind_nu D) by (unfold ups'; rewrite List.length_firstn; unfold im_np in *; lia).
    (** The closed environments of the telescope, as the components after
        the uniform parameters. *)
    assert (EZ : cargs_ctx p D Mk gs ++ im_params D Mk = Z ++ ind_uparams D)
      by (unfold Z, im_params; rewrite List.app_assoc; reflexivity).
    rewrite EZ in Ebb, Ebb'.
    rewrite Ezs, (env_tele_closed_components D ups Z _ Hu) in Ebb.
    rewrite Ezs', (env_tele_closed_components D ups' Z _ Hu0') in Ebb'.
    assert (HE : RZ (components_env D ups (List.rev Z) (ns ++ as1)) (components_env D ups' (List.rev Z) (ns' ++ as1'))).
    { rewrite <- (env_tele_closed_components D ups Z _ Hu), <- (env_tele_closed_components D ups' Z _ Hu0'), <- Ezs, <- Ezs'.
      apply (gargs_env_rel _ _ _ _ _ _ HRZ HZ); [ rewrite List.length_app, HlZ; unfold im_np, ind_nu in *; lia |].
      rewrite <- EZ; exact Hg0. }
    assert (ERZ : List.rev Z = List.rev (im_nparams Mk) ++ List.rev (cargs_ctx p D Mk gs))
      by (unfold Z; apply List.rev_app_distr).
    assert (Ens : ⟦ vars_from (List.length gs) (im_nn Mk) ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups (List.rev Z) (ns ++ as1) ↘ ns).
    { rewrite ERZ, <- Hla, <- Hlns; apply eval_nvars_components; rewrite List.length_rev, length_im_nparams; exact Hlns. }
    assert (Ens' : ⟦ vars_from (List.length gs) (im_nn Mk) ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups' (List.rev Z) (ns' ++ as1') ↘ ns').
    { rewrite ERZ, <- Hla', <- Hlns'; apply eval_nvars_components; rewrite List.length_rev, length_im_nparams; exact Hlns'. }
    pose proof (member_type_rel P p D HP HPD k Mk ups ups' Z RZ (ns ++ as1) (ns' ++ as1') (im_nn Mk) (List.length gs)
                  _ ns ns' bb bb' i0 Rb HM Hu Hgu HZ HRZ ltac:(rewrite List.length_app, HlZ; lia)
                  ltac:(rewrite List.length_app, HlZ; lia) ltac:(rewrite List.length_app; lia) HE
                  ltac:(apply length_vars_from) Ens Ens' Ebb Ebb' HRb) as ER.
    apply ER.
    (** The constructor's values. *)
    assert (Hu' : List.length ups' = ind_nu D) by (unfold ups'; rewrite List.length_firstn; unfold im_np in *; lia).
    assert (Esk : List.skipn (ind_nu D) zs = ns ++ as1).
    { rewrite Ezs, List.skipn_app, (List.skipn_all2 ups) by lia.
      replace (ind_nu D - List.length ups) with 0 by lia; reflexivity. }
    assert (Esk' : List.skipn (ind_nu D) zs' = ns' ++ as1').
    { rewrite Ezs', List.skipn_app, (List.skipn_all2 ups') by lia.
      replace (ind_nu D - List.length ups') with 0 by lia; reflexivity. }
    (** The relations of the types the shapes end in. *)
    pose proof (uparams_refl_l D HD Hc _ _ Hgu) as Hgd.
    assert (Hends : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
              view_end_rel p D (List.firstn (ind_nu D) ps) (List.firstn (ind_nu D) ps) (ptyp_mem t) /\
              rview_end_rel p D (List.firstn (ind_nu D) ps) (List.firstn (ind_nu D) ps) (ptyp_mem t))
      by (intros; fold ups; split; [ exact (view_end_rel_all P p D HP HPD ups ups Hgd Hu _)
                                   | exact (rview_end_rel_all P p D HP HPD ups ups Hgd Hu _) ]).
    destruct (im_is_rview Mk) eqn:Hrv.
    - (** A record view: the tuples of the fields. *)
      unfold im_is_rview in Hrv; destruct (im_head Mk) as [| | qr Is fl] eqn:Hh; try discriminate Hrv.
      rewrite (con_value_full_rview qr Is fl zs w Hh ltac:(lia) Hw), (con_value_full_rview qr Is fl zs' w' Hh ltac:(lia) Hw'), Esk, Esk'.
      assert (Hns : ns = nil) by (destruct ns; [ reflexivity | unfold im_nn in Hlns; rewrite (rview_struct_nparams _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HM Hh) in Hlns; discriminate Hlns ]).
      assert (Hns' : ns' = nil) by (destruct ns'; [ reflexivity | unfold im_nn in Hlns'; rewrite (rview_struct_nparams _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HM Hh) in Hlns'; discriminate Hlns' ]).
      rewrite Hns, Hns'; cbn [List.app].
      exact (con_rel_rview p D Hg Hcv k Mk qr Is fl c gs HM Hh (con_rview_cons _ _ _ Hh) ps ps' as1 as1' Hgp Hlp Hga Hla Hends).
    - destruct (con_value_full zs w Hrv ltac:(lia) Hw) as (cs & Hcs & ->).
      destruct (con_value_full zs' w' Hrv ltac:(lia) Hw') as (cs' & Hcs' & ->).
      rewrite Esk, Esk', !List.app_assoc.
      exact (con_rel p D Hg Hcv k Mk c gs HM Hcon ps ps' as1 as1' Hgp Hlp Hga Hla Hends cs cs' Hrv Hcs Hcs').
  Qed.

  (** ** The Kinds of the Arguments the Constructor Takes

      At [n] arguments the constructor's value takes the next at the kind
      of the [n]-th entry of its telescope: a parameter's tag
      ([tele_param_kind]), then the argument's tag. *)
  Lemma con_value_arg_kind : forall ys w, List.length ys < im_np D Mk + List.length gs -> con_value p D k Mk c ys w ->
      arg_kind gc_deps gc_stack w
        = if Nat.ltb (List.length ys) (im_np D Mk) then tele_param_kind (List.rev (im_params D Mk)) (List.length ys)
          else con_arg_kind Mk c (List.length ys - im_np D Mk).
  Proof.
    intros ys w Hlys Hw.
    pose proof (valid_group_lookup _ _ Hg) as Hl.
    inversion Hw as [pm xs Hh | qc kc Is vm xs Hh Hlt | qc kc Is vm xs cs Hh Hle Ecs | qr Is fl xs Hh Hlt | qr Is fl xs Hh Hle]; subst.
    - cbn [arg_kind]; rewrite Hl, HM; unfold con_param_count; rewrite Hh; reflexivity.
    - cbn [arg_kind]; rewrite Hl, HM; unfold con_param_count; rewrite Hh; reflexivity.
    - (** A view: the container's constructor, whose arguments are of the
          view's kinds; past the uniform parameters, both members'
          parameters are relevant. *)
      destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (Dq & Mk' & Hq & HMk' & Hkd & HIl & _ & Hvm & _).
      pose proof (Hcv _ _ _ _ _ _ _ HM Hh Hq) as HgQ.
      assert (Hhd : exists pm, im_head Mk' = mh_decl pm).
      { pose proof (proj2 (decl_typed_order _ _ _ (valid_group_typed _ _ HgQ) _ _ HMk') Hkd) as Hd.
        unfold im_is_decl in Hd; destruct (im_head Mk'); [ eauto | discriminate .. ]. }
      destruct Hhd as [pm Hhd].
      destruct (view_con_container p D Hass Hdt k Mk qc kc Is vm Dq Mk' c gs HM Hh Hq HMk' Hcon) as (gs' & Hcon' & Hcorr).
      destruct (view_agree_members p D k Mk qc kc Is vm Dq Hass HM Hh Hq kc Mk' HMk') as (v & Mv & Hvmb).
      assert (v = k) as -> by (pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvmb) as Hv; rewrite Hvm in Hv; congruence).
      assert (Mv = Mk) as -> by (pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMv; rewrite HM in HMv; congruence).
      pose proof (view_member_nn _ _ _ _ _ _ _ _ _ Hvmb) as Hnn.
      pose proof (eval_exps_length _ _ _ Ecs) as Hlcs.
      cbn [arg_kind]; rewrite Hq, HMk'; unfold con_param_count; rewrite Hhd.
      rewrite List.length_app, List.length_skipn, Hlcs, HIl.
      destruct (Nat.ltb_spec (List.length ys) (im_np D Mk)) as [H1 | H1];
        destruct (Nat.ltb_spec (ind_nu Dq + (List.length ys - ind_nu D)) (im_np Dq Mk')) as [H2 | H2];
        unfold im_np in *; try lia.
      + rewrite (tele_param_kind_nparams _ _ _ (valid_group_typed _ _ HgQ) _ _ _ HMk') by lia.
        rewrite (tele_param_kind_nparams _ _ _ Hdt _ _ _ HM) by lia; reflexivity.
      + unfold con_arg_kind; rewrite Hcon, Hcon'.
        replace (ind_nu Dq + (List.length ys - ind_nu D) - (im_nn Mk' + ind_nu Dq)) with (List.length ys - (im_nn Mk + ind_nu D)) by lia.
        exact (cargs_correspond_tags _ _ _ _ Hcorr).
    - cbn [arg_kind]; rewrite Hl, HM; unfold con_param_count; rewrite Hh, (con_rview_np _ _ _ Hh); reflexivity.
    - exfalso; pose proof (con_rview_len _ _ _ Hh); pose proof (con_rview_np _ _ _ Hh); lia.
  Qed.

  (** The values of an entry of the constructor's telescope, at arguments
      an environment related to itself at the entries before it, are of
      the entry's kind. *)
  Lemma con_tele_dom_kind : forall ts1 κ A ts2 R ρ b,
      List.rev (cargs_ctx p D Mk gs ++ im_params D Mk) = ts1 ++ ce_ass κ A :: ts2 ->
      EF List.rev ts1 ≈ List.rev ts1 ∈ per_ctx_env ↘ R -> R ρ ρ -> ⟦ A ⟧ ρ ↘ b ->
      domain_kind b
        = if Nat.ltb (List.length ts1) (im_np D Mk) then tele_param_kind (List.rev (im_params D Mk)) (List.length ts1)
          else con_arg_kind Mk c (List.length ts1 - im_np D Mk).
  Proof.
    intros * Heq HR Hz Eb.
    assert (HCe : cargs_ctx p D Mk gs ++ im_params D Mk = List.rev ts2 ++ ce_ass κ A :: List.rev ts1)
      by (rewrite <- (List.rev_involutive (cargs_ctx p D Mk gs ++ im_params D Mk)), Heq, List.rev_app_distr; cbn [List.rev];
          rewrite <- List.app_assoc; reflexivity).
    assert (HlC : List.length (List.rev ts1) = List.length ts1) by apply List.length_rev.
    destruct (Nat.ltb_spec (List.length ts1) (im_np D Mk)) as [Hlt | Hge].
    - (** A parameter: of its tag, an evaluated kind. *)
      destruct (app_split_right _ _ _ _ _ HCe ltac:(rewrite length_im_params, HlC; exact Hlt)) as [X HX].
      destruct (im_params_evaluated D HD k Mk HM _ _ _ _ HX) as [i HA].
      destruct (rel_param_typed_evaluated HA) as (r & Hr & HAr).
      destruct (HAr _ HR _ _ Hz) as (b0 & Eb0 & Hb0).
      assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
      (** The entry's tag is the type's kind. *)
      assert (HWe : ⊨ List.rev ts1 ▹{κ} A).
      { pose proof HΨ as H; rewrite HCe in H; exact (rel_ctx_wf_app_r _ _ H). }
      destruct (rel_ctx_wf_ass_kind HWe _ HR _ _ Hz) as (b1 & Eb1 & Hb1).
      assert (b1 = b) as -> by (eapply functional_eval_exp; eassumption).
      assert (Hn : List.nth_error (List.rev (im_params D Mk)) (List.length ts1) = Some (ce_ass κ A)).
      { rewrite HX, List.rev_app_distr; cbn [List.rev]; rewrite List.rev_involutive, <- List.app_assoc; cbn [List.app].
        rewrite List.nth_error_app2, Nat.sub_diag by lia; reflexivity. }
      rewrite (tele_param_kind_of_nth _ _ _ _ Hn ltac:(rewrite <- Hb1, Hb0; exact Hr)); congruence.
    - (** An argument: of its tag. *)
      destruct (app_split_left _ _ _ _ _ HCe ltac:(rewrite length_im_params, HlC; exact Hge)) as (Y & HY1 & HY2).
      set (j := List.length ts1 - im_np D Mk).
      assert (HlY : List.length Y = j)
        by (unfold j; rewrite <- HlC, HY1, List.length_app, length_im_params; lia).
      assert (Hjg : j < List.length gs)
        by (pose proof (f_equal (@List.length _) HY2) as L; rewrite List.length_app, length_cargs_ctx in L; cbn in L; lia).
      destruct (nth_error_lt_some' gs j Hjg) as [g Hgj].
      destruct (List.nth_error_split _ _ Hgj) as (gs1 & gs2 & Egs & Hl1).
      (** The entry is the argument's type over the arguments before it. *)
      assert (Ecg : cargs_ctx p D Mk gs
                    = cargs_ctx_aux p D (im_nn Mk) (cargs_pat (gs1 ++ g :: nil) ++ nil) gs2
                        ++ cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) (g :: nil) ++ cargs_ctx p D Mk gs1).
      { rewrite Egs; replace (gs1 ++ g :: gs2) with ((gs1 ++ g :: nil) ++ gs2) by (rewrite <- List.app_assoc; reflexivity).
        unfold cargs_ctx at 1; rewrite cargs_ctx_aux_app.
        change (cargs_ctx_aux p D (im_nn Mk) nil (gs1 ++ g :: nil)) with (cargs_ctx p D Mk (gs1 ++ g :: nil)).
        rewrite cargs_ctx_snoc; reflexivity. }
      destruct (valid_group_cargs_sem_all p D Hg Hcv k Mk c gs HM Hcon gs1 (g :: gs2) Egs) as [HW Hw].
      destruct g as [r A0 | t]; cbn [cargs_ctx_aux List.app] in Ecg; rewrite Ecg in HY2.
      + destruct (app_cons_inj _ _ _ _ _ _ HY2 ltac:(rewrite length_cargs_ctx; lia)) as (_ & HAe & HYe).
        injection HAe as <- <-.
        rewrite <- HYe in HY1; rewrite HY1 in HR.
        assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A0)
          by (rewrite Egs, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
        pose proof (nonrec_kind_at gs1 gs2 r A0) as Hr; rewrite <- Egs in Hr.
        destruct (valid_ind_decl_arg _ HD _ _ _ _ _ _ _ HM Hcon HA Hr) as (_ & i & HAv).
        rewrite Egs, <- nonrec_args_prefix_cargs_strat in HAv.
        pose proof (rel_exp_under_ctx_wk Hw HAv) as HAw; rewrite abs_kind_sort_wk in HAw; cbn [exp_wk] in HAw.
        destruct (rel_exp_of_abs_kind_sort_at HR HAw _ _ Hz) as (b0 & Eb0 & Hr0).
        assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
        fold j; unfold con_arg_kind; rewrite Hcon, Hgj; exact Hr0.
      + destruct (app_cons_inj _ _ _ _ _ _ HY2 ltac:(rewrite length_cargs_ctx; lia)) as (_ & HAe & _).
        injection HAe as <- <-.
        destruct (length_rec_ps D HD k Mk HM c gs gs1 t gs2 Hcon Egs) as (Mj & HMj & _).
        rewrite (ptyp_ty_relevant _ _ _ _ _ _ _ _ HMj Eb).
        fold j; unfold con_arg_kind; rewrite Hcon, Hgj; reflexivity.
  Qed.

  (** ** The Constructor *)
  Lemma valid_exp_under_ctx_con : forall i, ⋅ ⊨ con_ty p D k Mk gs : Typeω@i -> ⋅ ⊨ a_con p k c : con_ty p D k Mk gs.
  Proof.
    intros i HT.
    destruct (rel_exp_of_typ_inversion_simple HT) as (R & HR & Hsimp).
    assert (HRall : forall ρ ρ', R ρ ρ') by (intros; inversion HR; subst; match goal with H : _ <~> _ |- _ => apply H; exact I end).
    apply (rel_exp_closed_intro _ _ i); [ intros; exact (con_ty_sub p D k Mk c gs _ Hc HM Hcon) | intros; reflexivity |].
    intros ρ ρ'.
    destruct (Hsimp ρ ρ' (HRall _ _)) as (a & a' & Ea & Ea' & [R0 HR0]).
    destruct (con_value_start ρ) as (v & Ev & Hv).
    destruct (con_value_start ρ') as (v' & Ev' & Hv').
    exists a, a', R0, v, v'.
    split; [ exact Ea | split; [ exact Ea' | split; [ exact HR0 | split; [ exact Ev | split; [ exact Ev' |] ] ] ] ].
    destruct (Hsimp nil nil (HRall _ _)) as (b & b' & Eb & Eb' & [Rpi HRpi]).
    destruct (Hsimp ρ nil (HRall _ _)) as (a0 & b0 & Ea0 & Eb0 & [R2 HR2]).
    assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR2 HRpi) as (R3 & HR3 & E3).
    assert (E : R0 <~> Rpi)
      by (etransitivity; [ eapply per_univ_elem_right_irrel; [ exact HR0 | exact HR2 ] |];
          etransitivity; [ exact E3 | eapply per_univ_elem_left_irrel; [ exact HR3 | exact HRpi ] ]).
    apply E.
    set (ts := List.rev (cargs_ctx p D Mk gs ++ im_params D Mk)).
    assert (Hts : tele_ass ts)
      by (apply List.Forall_rev, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc k Mk HM) ]).
    unfold con_ty in Eb, Eb'; rewrite <- ctx_pi_app, <- (List.rev_involutive (cargs_ctx p D Mk gs ++ im_params D Mk)) in Eb, Eb'.
    fold ts in Eb, Eb'.
    assert (Hlts : List.length ts = im_np D Mk + List.length gs)
      by (unfold ts; rewrite List.length_rev, List.length_app, length_cargs_ctx, length_im_params; lia).
    assert (HC : ⊨ List.rev ts ++ ⋅) by (unfold ts; rewrite List.rev_involutive, List.app_nil_r; exact HΨ).
    (** Extensions of the empty environment related at a prefix of the
        telescope are of arguments related at it. *)
    assert (Hgpre : forall ts1 ts2 R1 vts vts', ts = ts1 ++ ts2 ->
              EF List.rev ts1 ++ ⋅ ≈ List.rev ts1 ++ ⋅ ∈ per_ctx_env ↘ R1 ->
              List.length vts = List.length ts1 -> List.length vts' = List.length ts1 ->
              R1 (env_extend_typed nil vts) (env_extend_typed nil vts') ->
              per_gargs ts1 nil nil (List.map fst vts) (List.map fst vts')).
    { intros * Heq HR1 Hl Hl' HEv.
      assert (Hts1 : tele_ass ts1) by (pose proof Hts as H; rewrite Heq in H; apply List.Forall_app in H; exact (proj1 H)).
      assert (HC1 : ⊨ List.rev ts1 ++ ⋅)
        by (pose proof HC as H; rewrite Heq, List.rev_app_distr, <- List.app_assoc in H; exact (rel_ctx_wf_app_r _ _ H)).
      exact (proj2 (rel_gargs ts1 ⋅ _ R1 per_ctx_env_nil_true HC1 Hts1 HR1 nil nil vts vts' Hl Hl' HEv)). }
    (** At the last uniform parameter, the view's instance evaluates. *)
    assert (Hup : forall ts1 κ A ts2 R1 vts vts' y y' t t', ts = ts1 ++ ce_ass κ A :: ts2 ->
               EF List.rev (ts1 ++ ce_ass κ A :: nil) ++ ⋅ ≈ List.rev (ts1 ++ ce_ass κ A :: nil) ++ ⋅ ∈ per_ctx_env ↘ R1 ->
               List.length vts = List.length ts1 -> List.length vts' = List.length ts1 ->
               R1 (env_extend_typed nil (vts ++ (y, t) :: nil)) (env_extend_typed nil (vts' ++ (y', t') :: nil)) ->
               forall qc kc Is vm, im_head Mk = mh_view qc kc Is vm -> S (List.length ts1) = ind_nu D ->
                 (exists cs, ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D (List.map fst vts ++ y :: nil) ↘ cs) /\
                 (exists cs', ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D (List.map fst vts' ++ y' :: nil) ↘ cs')).
    { intros * Heq HR1 Hlv Hlv' HEv qc kc Is vm Hh Hnu.
      destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (Dq & Mk' & Hq & _).
      assert (Heq' : ts = (ts1 ++ ce_ass κ A :: nil) ++ ts2) by (rewrite <- List.app_assoc; exact Heq).
      pose proof (Hgpre _ _ R1 (vts ++ (y, t) :: nil) (vts' ++ (y', t') :: nil) Heq' HR1
                    ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia) HEv) as Hgy.
      rewrite !List.map_app in Hgy; cbn [List.map fst] in Hgy.
      assert (Hft : ts1 ++ ce_ass κ A :: nil = List.rev (ind_uparams D)).
      { assert (E1 : List.firstn (S (List.length ts1)) ts = ts1 ++ ce_ass κ A :: nil)
          by (rewrite Heq'; apply firstn_app_exact; rewrite List.length_app; cbn; lia).
        rewrite <- E1; unfold ts; rewrite List.rev_app_distr, rev_im_params, <- List.app_assoc, Hnu.
        apply firstn_app_exact; rewrite List.length_rev; reflexivity. }
      rewrite Hft in Hgy.
      destruct (valid_group_views_view_args_values p D Hg Hcv _ _ _ _ _ _ _ HM Hh Hq _ _ Hgy
                  ltac:(rewrite List.length_app, List.length_map; cbn [List.length]; lia))
        as (cs & cs' & Ecs & Ecs' & _).
      split; [ exists cs; exact Ecs | exists cs'; exact Ecs' ]. }
    (** The codomain is a valid type over the telescope. *)
    destruct (mty_vars_valid_at p D Hg Hcv k Mk (cargs_ctx p D Mk gs) HM HΨ) as [j Hj].
    rewrite length_cargs_ctx in Hj.
    assert (HB : List.rev ts ++ ⋅ ⊨ᵗ ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk))
                   ≈ ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)) at j)
      by (unfold ts; rewrite List.rev_involutive, List.app_nil_r; exact (rel_type_of_typ Hj)).
    eapply (ctx_pi_rel_elem_by (con_value p D k Mk c) _ ts ⋅ _ Hts per_ctx_env_nil_true HC nil nil nil nil v v');
      [ exact I | exact Hv | exact Hv' | | | | | exact Eb | exact Eb' | exact HRpi | ].
    - intros ts1 κj Aj ts2 R1 vts vts' y y' t t' w Heq HR1 Hlv Hlv' HEv Hw; cbn [List.app] in Hw |- *.
      assert (Hn : List.length (List.map fst vts) < im_np D Mk + List.length gs)
        by (rewrite List.length_map; pose proof (f_equal (@List.length _) Heq) as L; rewrite List.length_app in L; cbn in L; lia).
      apply (con_value_step (List.map fst vts) y w Hn); [| exact Hw ].
      intros * Hh Hnu; rewrite List.length_map, Hlv in Hnu.
      exact (proj1 (Hup _ _ _ _ _ _ _ _ _ _ _ Heq HR1 Hlv Hlv' HEv _ _ _ _ Hh Hnu)).
    - intros ts1 κj Aj ts2 R1 vts vts' y y' t t' w' Heq HR1 Hlv Hlv' HEv Hw'; cbn [List.app] in Hw' |- *.
      assert (Hn : List.length (List.map fst vts') < im_np D Mk + List.length gs)
        by (rewrite List.length_map; pose proof (f_equal (@List.length _) Heq) as L; rewrite List.length_app in L; cbn in L; lia).
      apply (con_value_step (List.map fst vts') y' w' Hn); [| exact Hw' ].
      intros * Hh Hnu; rewrite List.length_map, Hlv' in Hnu.
      exact (proj2 (Hup _ _ _ _ _ _ _ _ _ _ _ Heq HR1 Hlv Hlv' HEv _ _ _ _ Hh Hnu)).
    - (** Each side takes its arguments at the kinds of the entries. *)
      intros ts1 κj Aj ts2 R1 vts vts' w bj Heq HR1 Hlv Hlv' HEv Hw Ebj; cbn [List.app] in Hw.
      assert (HPR1 : PER R1) by (eapply per_env_PER; exact HR1).
      rewrite List.app_nil_r in HR1.
      assert (Hn : List.length (List.map fst vts) < im_np D Mk + List.length gs)
        by (rewrite List.length_map; pose proof (f_equal (@List.length _) Heq) as L; rewrite List.length_app in L; cbn in L; lia).
      rewrite (con_value_arg_kind _ w Hn Hw), List.length_map, Hlv; symmetry.
      exact (con_tele_dom_kind ts1 κj Aj ts2 R1 _ bj Heq HR1 ltac:(etransitivity; [ exact HEv | symmetry; exact HEv ]) Ebj).
    - intros ts1 κj Aj ts2 R1 vts vts' w' bj' Heq HR1 Hlv Hlv' HEv Hw' Ebj'; cbn [List.app] in Hw'.
      assert (HPR1 : PER R1) by (eapply per_env_PER; exact HR1).
      rewrite List.app_nil_r in HR1.
      assert (Hn : List.length (List.map fst vts') < im_np D Mk + List.length gs)
        by (rewrite List.length_map; pose proof (f_equal (@List.length _) Heq) as L; rewrite List.length_app in L; cbn in L; lia).
      rewrite (con_value_arg_kind _ w' Hn Hw'), List.length_map, Hlv'; symmetry.
      exact (con_tele_dom_kind ts1 κj Aj ts2 R1 _ bj' Heq HR1 ltac:(etransitivity; [ symmetry; exact HEv | exact HEv ]) Ebj').
    - (** At all the arguments: the codomain at the closed environments,
          the retaggings of the extensions. *)
      intros R1 vts vts' w w' HR1 Hlv Hlv' HEv Hw Hw'; cbn [List.app] in Hw, Hw'.
      assert (HPR1 : PER R1) by (eapply per_env_PER; exact HR1).
      pose proof (Hgpre ts nil R1 vts vts' ltac:(rewrite List.app_nil_r; reflexivity) HR1 Hlv Hlv' HEv) as Hg0.
      assert (Er : ctx_retag (List.rev ts ++ ⋅) (env_extend_typed nil vts) = env_tele nil ts (List.map fst vts))
        by exact (ctx_retag_extend_typed ts ⋅ nil vts eq_refl Hlv).
      assert (Er' : ctx_retag (List.rev ts ++ ⋅) (env_extend_typed nil vts') = env_tele nil ts (List.map fst vts'))
        by exact (ctx_retag_extend_typed ts ⋅ nil vts' eq_refl Hlv').
      apply (per_head_of_type_resp HR1 HB _ _ (env_tele nil ts (List.map fst vts)) (env_tele nil ts (List.map fst vts'))).
      { apply rel_chain_4; [ exact HEv | | ].
        - rewrite <- Er; apply (per_ctx_env_retag_right HR1); symmetry; exact HEv.
        - rewrite <- Er, <- Er'; exact (per_ctx_env_retag HR1 _ _ HEv). }
      unfold ts; apply con_at_args;
        [ exact Hg0 | rewrite List.length_map, Hlv; unfold ts; rewrite List.length_rev; reflexivity | exact Hw | exact Hw' ].
  Qed.
End ConValue.

End Fixed_GCtx.
