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
  intros * H; per_univ_elem_induction H; intros * E; try discriminate; subst;
    (** A proposition's head is propositional, a constructor's is not. *)
    match goal with Hp : per_prop _ _ |- _ => pose proof (per_prop_left _ _ Hp) as Hl; discriminate Hl end.
Qed.

(** At any type, the stored uniform parameters of a value of a declared
    member's constructor can change, their number kept. *)
Lemma per_elem_con_prefix : forall i R a b, DF a ≈ b ∈ per_univ_elem i ↘ R ->
    forall hd Dq kq Mq pm c cs cs' ms y, ind_lookup gc_deps gc_stack hd = Some Dq -> ind_member Dq kq = Some Mq ->
    im_head Mq = mh_decl pm -> List.length cs = ind_nu Dq -> List.length cs' = ind_nu Dq ->
    R (d_con hd kq c (cs ++ ms)) y -> R (d_con hd kq c (cs' ++ ms)) y.
Proof.
  intros * H; per_univ_elem_induction H; intros * Hq HMq Hh Lc Lc' Hx.
  1-2: match goal with HE : _ <~> per_universe_elements (per_univ _) |- _ => apply HE in Hx end;
       destruct Hx as [[R0 HR0] _ _]; exfalso; exact (per_univ_elem_not_con _ _ _ _ HR0 _ _ _ _ eq_refl).
  - match goal with HE : _ <~> per_lvl_at _ |- _ => apply HE in Hx end.
    destruct (Hx 0) as [L0 HL0 _ _]; inversion HL0.
  - match goal with HE : _ <~> per_prop |- _ => apply HE in Hx end.
    exfalso; pose proof (per_prop_left _ _ Hx) as Hl; discriminate Hl.
  - (** A type of levels is no constructor's type. *)
    match goal with HE : _ <~> per_level_sort |- _ => apply HE in Hx end.
    exfalso; unfold per_level_sort, per_level_sort_at in Hx; destruct Hx as [[R0 [a0 [Hp | Hp]]] _]; inversion Hp.
  - (** A constructor's value is no proof: it does not read back as one. *)
    match goal with HE : _ <~> per_proof |- _ => apply HE in Hx end.
    exfalso; destruct Hx as [Hx _]; destruct (Hx 0) as [Mx HMx]; inversion HMx.
  - match goal with HE : _ <~> pi_elements _ _ _ _, HB : forall c c' (e : in_rel c c'), rel_mod_eval _ _ _ _ _ _ |- _ =>
      apply (proj2 (HE _ _)); pose proof (proj1 (HE _ _) Hx) as Hx'; cbn beta in Hx'; rename HB into HBo end.
    destruct Hx' as [Hra Hrb Hx'].
    (** The argument sort of a constructor's value reads only the number
        of its arguments. *)
    constructor; [ rewrite <- Hra; cbn [arg_kind]; rewrite Hq, HMq, !List.length_app, Lc, Lc'; reflexivity | exact Hrb |].
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
  - match goal with HE : _ <~> per_ne |- _ => apply HE in Hx end; inversion Hx.
  - match goal with HE : _ <~> grp_rel _ _ _ _ _ _ _ _ _ _ _ |- _ =>
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
    match goal with HE : _ <~> record_rel _ _ |- _ =>
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

(** A declared member's constructor along terms: the values it takes
    after the stored values [xs] are those it takes after any [xs'] as
    long, the sort of each argument depending on its position only.  No
    constructor of that name need exist: it is one as soon as a value is
    taken. *)
Lemma eval_app_args_con_decl_any : forall qh Dq kq Mq pm c Ns ρ xs xs' l, ind_lookup gc_deps gc_stack qh = Some Dq ->
    ind_member Dq kq = Some Mq -> im_head Mq = mh_decl pm -> List.length xs' = List.length xs ->
    eval_app_args gc_deps gc_stack (d_con qh kq c xs) Ns ρ l ->
    exists ms, List.length ms = List.length Ns /\ l = d_con qh kq c (xs ++ ms) /\
      eval_app_args gc_deps gc_stack (d_con qh kq c xs') Ns ρ (d_con qh kq c (xs' ++ ms)).
Proof.
  intros qh Dq kq Mq pm c; induction Ns as [| N Ns IH]; intros ρ xs xs' l Hq HM Hh HL Ea; inversion Ea; subst.
  - exists nil; rewrite !List.app_nil_r; split; [ reflexivity | split; [ reflexivity | constructor ] ].
  - match goal with Har : evaluated_kind (arg_kind _ _ _), En : ⟦ N ⟧ _ ⍮ _ ⍮ ρ ↘ ?n, Eg : eval_app _ _ _ ?n ?g,
                    Er : eval_app_args _ _ ?g Ns ρ l |- _ =>
      inversion Eg; subst;
        match goal with H1 : ind_lookup _ _ qh = Some ?D1 |- _ => rewrite Hq in H1; injection H1 as <- end;
        match goal with H1 : ind_member Dq kq = Some ?M1 |- _ => rewrite HM in H1; injection H1 as <- end;
        try congruence;
      destruct (IH ρ (xs ++ n :: nil) (xs' ++ n :: nil) l Hq HM Hh ltac:(rewrite ?List.length_app, HL; reflexivity) Er)
        as (ms & Lms & -> & Er');
      exists (n :: ms); rewrite <- !List.app_assoc in *; split; [ cbn; lia | split; [ reflexivity |] ];
      eapply eval_app_args_evaluated;
        [ cbn [arg_kind] in Har |- *; rewrite Hq, HM in *; rewrite HL; exact Har | exact En
        | eapply eval_app_con; [ exact Hq | exact HM | exact Hh | eassumption | lia ] | exact Er' ] end.
  - match goal with Har : arg_kind _ _ _ = ak_propositional, Eg : eval_app _ _ _ (⋆ᵈ⟨N, ρ⟩) ?g,
                    Er : eval_app_args _ _ ?g Ns ρ l |- _ =>
      inversion Eg; subst;
        match goal with H1 : ind_lookup _ _ qh = Some ?D1 |- _ => rewrite Hq in H1; injection H1 as <- end;
        match goal with H1 : ind_member Dq kq = Some ?M1 |- _ => rewrite HM in H1; injection H1 as <- end;
        try congruence;
      destruct (IH ρ (xs ++ ⋆ᵈ⟨N, ρ⟩ :: nil) (xs' ++ ⋆ᵈ⟨N, ρ⟩ :: nil) l Hq HM Hh ltac:(rewrite ?List.length_app, HL; reflexivity) Er)
        as (ms & Lms & -> & Er');
      exists (⋆ᵈ⟨N, ρ⟩ :: ms); rewrite <- !List.app_assoc in *; split; [ cbn; lia | split; [ reflexivity |] ];
      eapply eval_app_args_proof;
        [ cbn [arg_kind] in Har |- *; rewrite Hq, HM in *; rewrite HL; exact Har
        | eapply eval_app_con; [ exact Hq | exact HM | exact Hh | eassumption | lia ] | exact Er' ] end.
Qed.

(** A view's constructor along the group's uniform parameters: at the
    last of them, the container's at the view's arguments there. *)
Lemma eval_app_args_con_view_uparams : forall p D j Mj qc kc Is vm c, ind_lookup gc_deps gc_stack p = Some D ->
    ind_member D j = Some Mj -> im_head Mj = mh_view qc kc Is vm ->
    forall Us xs ρ g, List.length xs + List.length Us = ind_nu D -> List.length xs < ind_nu D ->
    eval_app_args gc_deps gc_stack (d_con p j c xs) Us ρ g ->
    exists us cs, ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ us /\ ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D (xs ++ us) ↘ cs /\
      g = d_con qc kc c cs.
Proof.
  intros p D j Mj qc kc Is vm c Hl HM Hh; induction Us as [| U Us IH]; intros xs ρ g Hlen Hlt Ea; [ cbn in Hlen; lia |].
  inversion Ea; subst.
  - match goal with Eg : eval_app _ _ (d_con p j c xs) _ _ |- _ => inversion Eg; subst end;
      match goal with H1 : ind_lookup _ _ p = Some ?D1, H0 : ind_lookup _ _ p = Some ?D2 |- _ =>
        rewrite H1 in H0; injection H0 as <- end;
      match goal with H1 : ind_member D j = Some ?M1, H0 : ind_member D j = Some ?M2 |- _ =>
        rewrite H1 in H0; injection H0 as <- end;
      try congruence.
    + (** Before the last uniform parameter. *)
      destruct (IH (xs ++ n :: nil) ρ g ltac:(rewrite List.length_app; cbn in *; lia) ltac:(rewrite List.length_app; cbn; lia)
                  ltac:(eassumption)) as (us & cs & Eus & Ecs & ->).
      exists (n :: us), cs; rewrite <- List.app_assoc in Ecs; split; [ econstructor; eassumption | split; [ exact Ecs | reflexivity ] ].
    + (** At the last one. *)
      destruct Us as [| U' Us]; [| cbn in Hlen; lia ].
      match goal with Er : eval_app_args _ _ _ nil ρ g |- _ => inversion Er; subst end.
      match goal with Hh2 : im_head Mj = mh_view ?q2 ?k2 ?I2 ?v2 |- _ => rewrite Hh in Hh2; injection Hh2 as <- <- <- <- end.
      eexists (n :: nil), _; split; [ econstructor; [ eassumption | constructor ] | split; [ eassumption | reflexivity ] ].
  - (** No uniform parameter is a proof. *)
    exfalso; match goal with Har : arg_kind _ _ _ = ak_propositional |- _ =>
      revert Har; cbn [arg_kind]; rewrite Hl, HM; unfold con_param_count, im_np; rewrite Hh;
      destruct (Nat.ltb_spec (List.length xs) (im_nn Mj + ind_nu D)); [ apply tele_param_kind_not_propositional | lia ] end.
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
  pose proof (valid_group_lookup _ _ (valid_groups_valid P HP p D HPD)) as Hl.
  (** The left side: the view's constructor, the container's after the
      uniform parameters, at the view's arguments. *)
  apply eval_apps_exp in El as (f & Ef & Ea).
  apply eval_app_args_app in Ea as (g & Eg & Ea).
  assert (Hg : exists cs, List.length cs = ind_nu Dq /\ g = d_con qc kc c cs).
  { inversion Ef; subst;
      match goal with H1 : ind_lookup _ _ p = Some ?D1 |- _ => rewrite Hl in H1; injection H1 as <- end;
      match goal with H1 : ind_member D j = Some ?M1 |- _ => rewrite HMj in H1; injection H1 as <- end;
      try congruence.
    - match goal with Hs : im_starts D Mj = true |- _ =>
        unfold im_starts, im_is_decl in Hs; rewrite Hh in Hs; cbn [orb] in Hs; apply Nat.ltb_lt in Hs end.
      destruct (eval_app_args_con_view_uparams p D j Mj qc kc Is vm c Hl HMj Hh Us nil ρ g ltac:(cbn [List.length]; lia)
                  ltac:(cbn [List.length]; lia) Eg) as (us & cs & _ & Ecs & ->).
      exists cs; split; [ rewrite (eval_exps_length _ _ _ Ecs); exact HIl | reflexivity ].
    - match goal with Hh2 : im_head Mj = mh_view ?q2 ?k2 ?I2 ?v2 |- _ => rewrite Hh in Hh2; injection Hh2 as <- <- <- <- end.
      destruct Us; [| cbn in HUl; lia ]; inversion Eg; subst.
      match goal with Ecs : ⟦ Is ⟧* _ ⍮ _ ⍮ _ ↘ ?cs |- _ =>
        exists cs; split; [ rewrite (eval_exps_length _ _ _ Ecs); exact HIl | reflexivity ] end. }
  (** The right side: the container's constructor, at the view's instance
      and then the same values. *)
  apply eval_apps_exp in Er as (f' & Ef' & Ea').
  assert (Ef1 : ⟦ a_con qc kc c ⟧ ρ ↘ d_con qc kc c nil)
    by (eapply eval_exp_con; [ exact Hq | exact HMk | unfold im_starts, im_is_decl; rewrite Hh'; reflexivity ]).
  pose proof (functional_eval_exp _ _ _ _ Ef' Ef1) as ->.
  apply eval_app_args_app in Ea' as (g' & Eg' & Ea').
  destruct (eval_app_args_con_decl_any qc Dq kc Mk pm c (im_pre Mj Us) ρ nil nil g' Hq HMk Hh' eq_refl Eg')
    as (cs' & Lcs' & -> & _).
  destruct Hg as (cs & Lcs & ->).
  assert (Lc' : List.length cs' = ind_nu Dq) by (rewrite Lcs'; unfold im_pre; rewrite Hh, List.length_map; exact HIl).
  destruct (eval_app_args_con_decl_any qc Dq kc Mk pm c Ms ρ cs cs' l Hq HMk Hh' ltac:(rewrite Lc', Lcs; reflexivity) Ea)
    as (ms & _ & -> & Ea2).
  pose proof (functional_eval_app_args _ _ _ _ _ Ea' Ea2) as ->.
  exists Dq, Mk, pm, cs, cs', ms; repeat split; assumption.
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
  destruct (rel_exp_under_ctx_simple_at HRΓ HL _ _ Hρρ') as [Hp | (l & l' & El & El' & Hll')]; [ left; exact Hp |].
  destruct (rel_exp_under_ctx_simple_at HRΓ HR _ _ Hρρ') as [Hp | (r & r' & Er & Er' & _)]; [ left; exact Hp |].
  right; exists l, r'; split; [ exact El | split; [ exact Er' |] ].
  destruct (con_view_values P p D HP HPD j Mj qc kc Is vm c ρ' Us Ms l' r' HMj Hh HUl El' Er')
    as (Dq & Mk & pm & cs & cs' & ms & Hq & HMk & Hh' & Lcs & Lcs' & -> & ->).
  destruct (rel_type_inversion_simple_at HRΓ HA _ _ Hρρ') as (t & t' & Et & Et' & [R HR0]).
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
    forall j Mj qr Is fl c gs R ρ Us Ms l, ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl ->
    ind_con Mj c = Some gs -> record_lookup gc_deps gc_stack qr = Some R ->
    List.length Us = ind_nu D -> List.length Ms = List.length fl ->
    ⟦ apps (a_con p j c) (Us ++ Ms) ⟧ ρ ↘ l ->
    exists ms, eval_field_vals gc_deps gc_stack (record_field_kinds R) Ms ρ ms /\ l = d_tuple (List.combine fl ms).
Proof.
  intros P p D HP HPD * HMj Hh Hcon HR HUl HMl El.
  pose proof (decl_typed_record_struct _ _ _ (valid_group_typed _ _ (valid_groups_valid P HP p D HPD))) as Hrs.
  pose proof (con_rview_cons P p D HP HPD j Mj c gs HMj Hcon qr Is fl Hh) as Hcs.
  pose proof (con_rview_np P p D HP HPD j Mj HMj qr Is fl Hh) as Hnp.
  destruct (rview_struct_con _ _ _ Hrs _ _ _ _ _ HMj Hh) as (gs0 & Hcs0 & _).
  rewrite Hcs in Hcs0; injection Hcs0 as -> <-.
  (** The constructor takes its fields at the record's sorts. *)
  pose proof (rview_struct_kinds _ _ _ Hrs _ _ _ _ _ _ _ HMj Hh HR Hcs) as Hrel.
  apply eval_apps_exp in El as (f & Ef & Ea).
  destruct (con_value_start P p D HP HPD j Mj rview_con HMj ρ) as (f0 & Ef0 & Hf0).
  pose proof (functional_eval_exp _ _ _ _ Ef Ef0) as ->.
  destruct (con_value_app_args_sorted P p D HP HPD j Mj rview_con gs HMj Hcon (Us ++ Ms) nil f0 ρ l
              ltac:(cbn [List.length]; rewrite List.length_app, Hnp, HUl, HMl,
                      (con_rview_len P p D HP HPD j Mj rview_con gs HMj Hcon qr Is fl Hh); lia) Hf0 Ea)
    as (zs & Ezs & Hl).
  cbn [List.length List.skipn List.app] in Ezs, Hl.
  destruct (Mctt.Core.Completeness.Records.Model.eval_field_vals_app_inv _ _ _ _ _ Ezs) as (us & ms & -> & Eus & Ems).
  rewrite (con_kinds_skipn D j Mj gs (valid_group_typed _ _ (valid_groups_valid P HP p D HPD)) HMj (List.length Us)) in Ems
    by (rewrite ?Hnp, HUl; lia).
  rewrite Hnp, HUl, Nat.sub_diag in Ems; cbn [List.repeat List.app] in Ems.
  pose proof (Mctt.Core.Completeness.Records.Model.eval_field_vals_length _ _ _ _ Eus) as Lus.
  pose proof (Mctt.Core.Completeness.Records.Model.eval_field_vals_length _ _ _ _ Ems) as Lms.
  exists ms; split; [ rewrite <- Hrel; exact Ems |].
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
    forall Γ j Mj qr Is fl c gs Us Ms A, ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl ->
    ind_con Mj c = Some gs ->
    List.length Us = ind_nu D -> List.length Ms = List.length fl ->
    Γ ⊨ apps (a_con p j c) (Us ++ Ms) : A ->
    Γ ⊨ a_tuple (apps (a_record qr) (im_pre Mj Us)) (List.combine fl Ms) : A ->
    Γ ⊨ apps (a_con p j c) (Us ++ Ms) ≈ a_tuple (apps (a_record qr) (im_pre Mj Us)) (List.combine fl Ms) : A.
Proof.
  intros P p D HP HPD * HMj Hh Hcon HUl HMl HL HR.
  pose proof (decl_typed_record_struct _ _ _ (valid_group_typed _ _ (valid_groups_valid P HP p D HPD))) as Hrs.
  destruct (rview_struct_record _ _ _ Hrs _ _ _ _ _ HMj Hh) as [Rr HRr].
  pose proof (rview_record_lookup _ _ _ _ _ _ HRr) as HlR.
  pose proof HL as [RΓ HRΓ i0 _].
  apply (rel_exp_under_ctx_of_simple HRΓ HL HR).
  intros ρ ρ' Hρρ'.
  destruct (rel_exp_under_ctx_simple_at HRΓ HL _ _ Hρρ') as [Hp | (l & l' & El & El' & Hll')]; [ left; exact Hp |].
  destruct (rel_exp_under_ctx_simple_at HRΓ HR _ _ Hρρ') as [Hp | (r & r' & Er & Er' & _)]; [ left; exact Hp |].
  right; exists l, r'; split; [ exact El | split; [ exact Er' |] ].
  destruct (con_rview_value P p D HP HPD j Mj qr Is fl c gs Rr ρ' Us Ms l' HMj Hh Hcon HlR HUl HMl El') as (ms & Ems & ->).
  inversion Er'; subst.
  (** The tuple's record is the view's. *)
  match goal with ET : ⟦ apps_exp (a_record qr) _ ⟧ _ ↘ d_record ?p0 _, HL0 : record_lookup _ _ ?p0 = Some ?R0 |- _ =>
    apply eval_apps_exp_record in ET as (ns0 & _ & Hap0);
    destruct (Mctt.Core.Completeness.Records.Model.eval_apps_record_shape _ _ _ _ Hap0) as (zs0 & Ez0); injection Ez0 as -> _;
    rewrite HlR in HL0; injection HL0 as <- end.
  rewrite combine_snd_eq in * by (symmetry; exact HMl).
  rewrite combine_fst_eq by (symmetry; exact HMl).
  match goal with H : eval_field_vals _ _ (record_field_kinds Rr) Ms ρ' ?vs |- _ =>
    pose proof (functional_eval_field_vals _ _ _ _ _ H Ems) as -> end.
  exact Hll'.
Qed.
End Fixed_GCtx.
