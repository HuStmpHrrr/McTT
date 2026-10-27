(** * The Equations of a View

    A view's constructor at the group's uniform parameters is the
    container's at the view's arguments there ([wf_exp_eq_con_view]).  The
    two values are the container's constructor, their stored uniform
    parameters apart, and no type's elements read those. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing Views.
From Mctt.Core.Syntactic.System.Global Require Import Presup MemberLemmas MemberWf.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Instance Telescope.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness Require Import VariableCases FunctionCases LevelCases SubtypingCases.
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews ArgTypes ViewEquations ViewArgs Con Elim.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** The Stored Uniform Parameters of a Constructor Are Not Read

    A constructor's value is not a type. *)
Lemma per_univ_elem_not_con : forall i R a b, DF a ≈ b ∈ per_univ_elem i ↘ R ->
    forall hd k c vs, a <> d_con hd k c vs.
Proof.
  intros * H; per_univ_elem_induction H; intros * E; discriminate.
Qed.

(** At any type, the stored uniform parameters of a value of a declared
    member's constructor can change, their number kept. *)
Lemma per_elem_con_prefix : forall i R a b, DF a ≈ b ∈ per_univ_elem i ↘ R ->
    forall hd Dq kq Mq pm c cs cs' ms y, ind_lookup gc_deps gc_stack hd = Some Dq -> ind_member Dq kq = Some Mq ->
    im_head Mq = mh_decl pm -> List.length cs = ind_nu Dq -> List.length cs' = ind_nu Dq ->
    R (d_con hd kq c (cs ++ ms)) y -> R (d_con hd kq c (cs' ++ ms)) y.
Proof.
  intros * H; per_univ_elem_induction H; intros * Hq HMq Hh Lc Lc' Hx.
  - match goal with HE : elem_rel <~> per_univ _ |- _ => apply HE in Hx end; destruct Hx as [R0 HR0].
    exfalso; exact (per_univ_elem_not_con _ _ _ _ HR0 _ _ _ _ eq_refl).
  - match goal with HE : elem_rel <~> per_univ _ |- _ => apply HE in Hx end; destruct Hx as [R0 HR0].
    exfalso; exact (per_univ_elem_not_con _ _ _ _ HR0 _ _ _ _ eq_refl).
  - match goal with HE : elem_rel <~> per_lvl_at _ |- _ => apply HE in Hx end.
    destruct (Hx 0) as [L0 HL0 _ _]; inversion HL0.
  - match goal with HE : elem_rel <~> per_True |- _ => apply HE end; exact I.
  - match goal with HE : elem_rel <~> per_ne |- _ => apply HE in Hx end; inversion Hx.
  - match goal with HE : elem_rel <~> _, HB : forall c c' (e : in_rel c c'), rel_mod_eval _ _ _ _ _ _ |- _ =>
      apply (proj2 (HE _ _)); pose proof (proj1 (HE _ _) Hx) as Hx'; cbn beta in Hx'; rename HB into HBo end.
    intros c0 c0' Hc0.
    destruct (Hx' c0 c0' Hc0) as [fa f'a' Efa Ef'a' Hfa].
    inversion Efa; subst;
      match goal with H1 : ind_lookup _ _ hd = Some ?D1 |- _ => rewrite Hq in H1; injection H1 as <- end;
      match goal with H1 : ind_member Dq kq = Some ?M1 |- _ => rewrite HMq in H1; injection H1 as <- end;
      try congruence.
    destruct (HBo c0 c0' Hc0) as [b0 b0' Eb Eb' [HR0 IH0]].
    econstructor; [ eapply eval_app_con; [ exact Hq | exact HMq | exact Hh | eassumption | rewrite List.length_app in *; lia ]
                  | exact Ef'a' |].
    rewrite <- !List.app_assoc in *.
    eapply IH0; [ exact Hq | exact HMq | exact Hh | exact Lc | exact Lc' | eassumption ].
  - match goal with HE : elem_rel <~> per_ne |- _ => apply HE in Hx end; inversion Hx.
  - match goal with HE : elem_rel <~> grp_rel _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      apply (proj2 (HE _ _)); pose proof (proj1 (HE _ _) Hx) as Hx' end.
    match goal with HL : ind_lookup _ _ p = Some D, HM : ind_member D k = Some M, HH : im_head M = mh_decl _ |- _ =>
      rename HL into HlD; rename HM into HMk; rename HH into HhM end.
    inversion Hx'; subst;
      (** not a record view's element: [M] is a declared member *)
      try (match goal with H1 : ind_member D k = Some ?M1, H2 : im_head ?M1 = mh_record _ _ _ |- _ =>
             rewrite HMk in H1; injection H1 as <-; congruence end).
    match goal with H1 : ind_member D k = Some ?M1 |- _ => rewrite HMk in H1; injection H1 as <- end.
    match goal with H1 : im_ref p k M = (hd, kq) |- _ => unfold im_ref in H1; rewrite HhM in H1; injection H1 as <- <- end.
    rewrite HlD in Hq; injection Hq as <-.
    eapply ind_rel_con_prefix_l; [ exact HMk | unfold im_unu; rewrite HhM; exact Lc | lia | exact Hx' ].
  - (* a record type: a constructor has no projection, so the record has
       no field and every value is its element *)
    match goal with HE : elem_rel <~> record_rel _ _ |- _ =>
      apply (proj2 (HE _ _)); pose proof (proj1 (HE _ _) Hx) as Hx' end.
    destruct Hx' as [vs vs' Hl Hr Hrel]; unfold record_projs in Hl.
    inversion Hl; subst;
      [| match goal with Hp : eval_proj _ _ _ (d_con _ _ _ _) _ |- _ => inversion Hp end ].
    econstructor; [| exact Hr | exact Hrel ].
    unfold record_projs; match goal with Hf : nil = record_fields _ |- _ => rewrite <- Hf end; constructor.
Qed.

(** A declared member's constructor along any arguments it takes. *)
Lemma eval_apps_con_decl_inv : forall qh Dq kq Mq pm c ys xs r, ind_lookup gc_deps gc_stack qh = Some Dq ->
    ind_member Dq kq = Some Mq -> im_head Mq = mh_decl pm ->
    $*| d_con qh kq c xs & ys | gc_deps ⍮ gc_stack ↘ r -> r = d_con qh kq c (xs ++ ys).
Proof.
  intros qh Dq kq Mq pm c; induction ys as [| y ys IH]; intros xs r Hq HM Hh E; inversion E; subst;
    [ rewrite List.app_nil_r; reflexivity |].
  match goal with H : eval_app _ _ _ y _ |- _ => inversion H; subst end;
    match goal with H1 : ind_lookup _ _ qh = Some ?D1 |- _ => rewrite Hq in H1; injection H1 as <- end;
    match goal with H1 : ind_member Dq kq = Some ?M1 |- _ => rewrite HM in H1; injection H1 as <- end;
    try congruence.
  rewrite (IH _ _ Hq HM Hh ltac:(eassumption)), <- List.app_assoc; reflexivity.
Qed.

(** ** A View's Constructor

    The constructor of a view [j] of a valid group at the group's uniform
    parameters [Us] and any further arguments [Ms], and the container's at
    the view's instance there: at an environment, both are the container's
    constructor at the values of [Ms], their stored uniform parameters
    apart. *)
Lemma con_view_values : forall P p D, valid_groups P -> P p D ->
    forall j Mj qc kc Is vm c ρ Us Ms l r, ind_member D j = Some Mj -> im_head Mj = mh_view qc kc Is vm ->
    List.length Us = ind_nu D ->
    ⟦ apps (a_con p j c) (Us ++ Ms) ⟧ ρ ↘ l -> ⟦ apps (a_con qc kc c) (im_pre Mj Us ++ Ms) ⟧ ρ ↘ r ->
    exists Dq Mk pm cs cs' ms, ind_lookup gc_deps gc_stack qc = Some Dq /\ ind_member Dq kc = Some Mk /\ im_head Mk = mh_decl pm /\
      List.length cs = ind_nu Dq /\ List.length cs' = ind_nu Dq /\
      l = d_con qc kc c (cs ++ ms) /\ r = d_con qc kc c (cs' ++ ms).
Proof.
  intros P p D HP HPD * HMj Hh HUl El Er.
  destruct (view_target_decl P p D HP HPD j Mj HMj qc kc Is vm Hh) as (Dq & Mk & pm & Hq & HMk & Hh' & HIl).
  apply eval_apps_exp in El as (f & zs & Ef & Ezs & Eap).
  apply eval_exps_app_inv in Ezs as (us & ms & -> & Eus & Ems).
  apply eval_apps_exp in Er as (f' & zs' & Ef' & Ezs' & Eap').
  apply eval_exps_app_inv in Ezs' as (cs' & ms' & -> & Ecs' & Ems').
  pose proof (functional_eval_exps' _ _ _ _ Ems' Ems) as ->.
  assert (Lus : List.length us = ind_nu D) by (rewrite (eval_exps_length _ _ _ Eus); exact HUl).
  (** The left side: the view's constructor, then the container's. *)
  destruct (con_value_start P p D HP HPD j Mj c HMj ρ) as (f0 & Ef0 & Hf0).
  pose proof (functional_eval_exp _ _ _ _ Ef Ef0) as ->.
  apply eval_apps_app in Eap as (g & Eg & Eap).
  pose proof (con_value_apps P p D HP HPD j Mj c nil HMj us nil f0 g ltac:(cbn [List.length]; unfold im_np; lia) Hf0 Eg) as Hg.
  cbn [List.app] in Hg.
  inversion Hg as [pm' xs Hh0 | qc' kc' Is' vm' xs Hh0 Hlt | qc' kc' Is' vm' xs cs Hh0 Hle Ecs
                  | qr' Is' fl' xs Hh0 Hlt | qr' Is' fl' xs Hh0 Hlt]; subst; rewrite Hh in Hh0;
    try discriminate; [ lia |].
  injection Hh0 as <- <- <- <-.
  rewrite List.skipn_all2, List.app_nil_r in Eap by lia.
  pose proof (eval_apps_con_decl_inv _ _ _ _ _ _ _ _ _ Hq HMk Hh' Eap) as ->.
  (** The right side: the container's constructor. *)
  assert (Ef1 : ⟦ a_con qc kc c ⟧ ρ ↘ d_con qc kc c nil)
    by (eapply eval_exp_con; [ exact Hq | exact HMk | unfold im_starts, im_is_decl; rewrite Hh'; reflexivity ]).
  pose proof (functional_eval_exp _ _ _ _ Ef' Ef1) as ->.
  pose proof (eval_apps_con_decl_inv _ _ _ _ _ _ _ _ _ Hq HMk Hh' Eap') as ->.
  exists Dq, Mk, pm, cs, cs', ms; repeat split; try assumption; try reflexivity.
  - rewrite (eval_exps_length _ _ _ Ecs); exact HIl.
  - rewrite (eval_exps_length _ _ _ Ecs'); unfold im_pre; rewrite Hh, List.length_map; exact HIl.
Qed.

(** The rule: the two constructors at any type both are at. *)
Theorem rel_exp_under_ctx_con_view : forall P p D, valid_groups P -> P p D ->
    forall Γ j Mj qc kc Is vm c Us Ms A, ind_member D j = Some Mj -> im_head Mj = mh_view qc kc Is vm ->
    List.length Us = ind_nu D ->
    Γ ⊨ apps (a_con p j c) (Us ++ Ms) : A -> Γ ⊨ apps (a_con qc kc c) (im_pre Mj Us ++ Ms) : A ->
    Γ ⊨ apps (a_con p j c) (Us ++ Ms) ≈ apps (a_con qc kc c) (im_pre Mj Us ++ Ms) : A.
Proof.
  intros P p D HP HPD * HMj Hh HUl HL HR.
  pose proof HL as [RΓ HRΓ i0 _].
  destruct (presup_rel_exp_under_ctx HL) as [iA HA].
  apply (rel_exp_under_ctx_of_simple HRΓ HL HR).
  intros ρ ρ' Hρρ'.
  destruct (rel_exp_under_ctx_simple_at HRΓ HL _ _ Hρρ') as (l & l' & El & El' & Hll').
  destruct (rel_exp_under_ctx_simple_at HRΓ HR _ _ Hρρ') as (r & r' & Er & Er' & _).
  exists l, r'; split; [ exact El | split; [ exact Er' |] ].
  destruct (con_view_values P p D HP HPD j Mj qc kc Is vm c ρ' Us Ms l' r' HMj Hh HUl El' Er')
    as (Dq & Mk & pm & cs & cs' & ms & Hq & HMk & Hh' & Lcs & Lcs' & -> & ->).
  destruct (rel_exp_of_typ_inversion_simple_at HRΓ HA _ _ Hρρ') as (t & t' & Et & Et' & [R HR0]).
  pose proof (per_head_iff Et Et' HR0) as ER.
  assert (HPR : PER R) by (eapply per_elem_PER; exact HR0).
  apply ER; apply ER in Hll'.
  symmetry; symmetry in Hll'.
  exact (per_elem_con_prefix _ _ _ _ HR0 _ _ _ _ _ _ _ _ _ _ Hq HMk Hh' Lcs Lcs' Hll').
Qed.

(** ** A Record View's Constructor

    The constructor of a record view at the group's uniform parameters and
    all its fields is the tuple of the fields, by name, at the fields'
    values: the record view's constructor and the tuple evaluate to the
    same value. *)
Lemma con_rview_value : forall P p D, valid_groups P -> P p D ->
    forall j Mj qr Is fl c ρ Us Ms l, ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl ->
    List.length Us = ind_nu D -> List.length Ms = List.length fl ->
    ⟦ apps (a_con p j c) (Us ++ Ms) ⟧ ρ ↘ l ->
    exists ms, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\ l = d_tuple (List.combine fl ms).
Proof.
  intros P p D HP HPD * HMj Hh HUl HMl El.
  pose proof (valid_group_typed _ _ (valid_groups_valid P HP p D HPD)) as Hdt.
  destruct (rview_struct_con _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HMj Hh) as (gs & _ & Hlen).
  pose proof (rview_struct_nparams _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HMj Hh) as Hnp.
  assert (Hnn : im_nn Mj = 0) by (unfold im_nn; rewrite Hnp; reflexivity).
  apply eval_apps_exp in El as (f & zs & Ef & Ezs & Eap).
  apply eval_exps_app_inv in Ezs as (us & ms & -> & Eus & Ems).
  assert (Lus : List.length us = ind_nu D) by (rewrite (eval_exps_length _ _ _ Eus); exact HUl).
  assert (Lms : List.length ms = List.length fl) by (rewrite (eval_exps_length _ _ _ Ems); exact HMl).
  destruct (con_value_start P p D HP HPD j Mj c HMj ρ) as (f0 & Ef0 & Hf0).
  pose proof (functional_eval_exp _ _ _ _ Ef Ef0) as ->.
  pose proof (con_value_apps P p D HP HPD j Mj c gs HMj (us ++ ms) nil f0 l
                ltac:(cbn [List.length]; rewrite List.length_app; unfold im_np; lia) Hf0 Eap) as Hl.
  cbn [List.app] in Hl.
  exists ms; split; [ exact Ems |].
  inversion Hl as [pm' xs Hh0 | qc' kc' Is' vm' xs Hh0 Hlt | qc' kc' Is' vm' xs cs Hh0 Hle Ecs
                  | qr' Is' fl' xs Hh0 Hlt | qr' Is' fl' xs Hh0 Hlt]; subst; rewrite Hh in Hh0; try discriminate.
  - rewrite List.length_app in Hlt; injection Hh0 as <- <- <-; lia.
  - injection Hh0 as <- <- <-.
    rewrite List.skipn_app, List.skipn_all2 by lia.
    replace (ind_nu D - List.length us) with 0 by lia; reflexivity.
Qed.

(** The rule: the record view's constructor and the tuple of its fields,
    at any type both are at. *)
Theorem rel_exp_under_ctx_con_rview : forall P p D, valid_groups P -> P p D ->
    forall Γ j Mj qr Is fl c Us Ms A, ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl ->
    List.length Us = ind_nu D -> List.length Ms = List.length fl ->
    Γ ⊨ apps (a_con p j c) (Us ++ Ms) : A ->
    Γ ⊨ a_tuple (apps (a_record qr) (im_pre Mj Us)) (List.combine fl Ms) : A ->
    Γ ⊨ apps (a_con p j c) (Us ++ Ms) ≈ a_tuple (apps (a_record qr) (im_pre Mj Us)) (List.combine fl Ms) : A.
Proof.
  intros P p D HP HPD * HMj Hh HUl HMl HL HR.
  pose proof HL as [RΓ HRΓ i0 _].
  apply (rel_exp_under_ctx_of_simple HRΓ HL HR).
  intros ρ ρ' Hρρ'.
  destruct (rel_exp_under_ctx_simple_at HRΓ HL _ _ Hρρ') as (l & l' & El & El' & Hll').
  destruct (rel_exp_under_ctx_simple_at HRΓ HR _ _ Hρρ') as (r & r' & Er & Er' & _).
  exists l, r'; split; [ exact El | split; [ exact Er' |] ].
  destruct (con_rview_value P p D HP HPD j Mj qr Is fl c ρ' Us Ms l' HMj Hh HUl HMl El') as (ms & Ems & ->).
  inversion Er'; subst.
  rewrite combine_snd_eq in * by (symmetry; exact HMl).
  rewrite combine_fst_eq by (symmetry; exact HMl).
  match goal with H : ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ' ↘ ?vs |- _ => pose proof (functional_eval_exps' _ _ _ _ H Ems) as -> end.
  exact Hll'.
Qed.
End Fixed_GCtx.
