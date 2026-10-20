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
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews ArgTypes ViewEquations ViewArgs.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** The Elements of a [Π] over a Telescope, Read by a Relation

    [ctx_pi_rel_elem] with a family of values given by a relation [Fr]
    between the arguments so far and the value: each side applies to the
    next argument, when the arguments are related at the telescope so
    far. *)
Lemma ctx_pi_rel_elem_by : forall (Fr : list domain -> domain -> Prop) B ts, tele_ass ts ->
    forall ρ ρ' xs xs' v v' a a' (i : uidx) R,
      List.length xs' = List.length xs -> Fr xs v -> Fr xs' v' ->
      (forall ys ys' y y' w, List.length ys < List.length ts ->
         per_gargs (List.firstn (S (List.length ys)) ts) (env_args ρ xs) (env_args ρ' xs') (ys ++ y :: nil) (ys' ++ y' :: nil) ->
         Fr (xs ++ ys) w -> exists u, $| w & y | gc_deps ⍮ gc_stack ↘ u /\ Fr (xs ++ ys ++ y :: nil) u) ->
      (forall ys ys' y y' w', List.length ys < List.length ts ->
         per_gargs (List.firstn (S (List.length ys)) ts) (env_args ρ xs) (env_args ρ' xs') (ys ++ y :: nil) (ys' ++ y' :: nil) ->
         Fr (xs' ++ ys') w' -> exists u', $| w' & y' | gc_deps ⍮ gc_stack ↘ u' /\ Fr (xs' ++ ys' ++ y' :: nil) u') ->
      ⟦ ctx_pi (List.rev ts) B ⟧ env_args ρ xs ↘ a -> ⟦ ctx_pi (List.rev ts) B ⟧ env_args ρ' xs' ↘ a' ->
      DF a ≈ a' ∈ per_univ_elem i ↘ R ->
      (forall ys ys' w w', per_gargs ts (env_args ρ xs) (env_args ρ' xs') ys ys' -> List.length ys = List.length ts ->
         Fr (xs ++ ys) w -> Fr (xs' ++ ys') w' ->
         Dom w ≈ w' ∈ per_head B B (env_args ρ (xs ++ ys)) (env_args ρ' (xs' ++ ys'))) ->
      Dom v ≈ v' ∈ R.
Proof.
  intros Fr B ts; induction ts as [| e ts IH]; intros Hts * Hl Hv Hv' HstL HstR Ha Ha' HR Hbase.
  - cbn [List.rev ctx_pi] in Ha, Ha'.
    specialize (Hbase nil nil v v' ltac:(constructor) eq_refl ltac:(rewrite List.app_nil_r; exact Hv)
                  ltac:(rewrite List.app_nil_r; exact Hv')).
    rewrite !List.app_nil_r in Hbase.
    exact (Hbase _ _ _ _ Ha Ha' HR).
  - assert (He : exists A, e = ce_ass A) by (inversion Hts as [| ? ? He _]; exact He).
    destruct He as [A ->].
    assert (Hts' : tele_ass ts) by (inversion Hts; assumption).
    cbn [List.rev] in Ha, Ha'; rewrite ctx_pi_snoc in Ha, Ha'.
    inversion Ha; subst a; inversion Ha'; subst a'.
    basic_invert_per_univ_elem HR.
    apply_relation_equivalence.
    intros c c' Hc.
    destruct_rel_mod_eval.
    match goal with E1 : ⟦ A ⟧ env_args ρ xs ↘ ?b, E2 : ⟦ A ⟧ env_args ρ' xs' ↘ ?b' |- _ =>
      destruct (per_univ_elem_to_nat _ _ _ _ equiv_a_a') as [n Hn];
      pose proof (mk_rel_mod_eval b b' E1 E2 Hn) as Hrm end.
    assert (Hgc : per_gargs (ce_ass A :: nil) (env_args ρ xs) (env_args ρ' xs') (c :: nil) (c' :: nil))
      by (econstructor; [ exact Hrm | exact Hc | constructor ]).
    destruct (HstL nil nil c c' v ltac:(cbn; lia) ltac:(cbn; exact Hgc) ltac:(rewrite List.app_nil_r; exact Hv))
      as (u & Eu & Hu).
    destruct (HstR nil nil c c' v' ltac:(cbn; lia) ltac:(cbn; exact Hgc) ltac:(rewrite List.app_nil_r; exact Hv'))
      as (u' & Eu' & Hu').
    cbn [List.app] in Hu, Hu'.
    econstructor; [ exact Eu | exact Eu' |].
    rewrite <- !env_args_snoc in *.
    eapply (IH Hts' ρ ρ' (xs ++ c :: nil) (xs' ++ c' :: nil));
      [ rewrite !List.length_app; cbn; lia | exact Hu | exact Hu' | | | eassumption | eassumption | eassumption |].
    + intros ys ys' y y' w Hly Hg Hw.
      rewrite <- !List.app_assoc in Hw |- *; cbn [List.app] in Hw |- *.
      apply (HstL (c :: ys) (c' :: ys') y y' w ltac:(cbn; lia)); [| exact Hw ].
      cbn [List.length List.app]; rewrite List.firstn_cons.
      econstructor; [ exact Hrm | exact Hc |].
      rewrite <- !env_args_snoc; exact Hg.
    + intros ys ys' y y' w' Hly Hg Hw'.
      rewrite <- !List.app_assoc in Hw' |- *; cbn [List.app] in Hw' |- *.
      apply (HstR (c :: ys) (c' :: ys') y y' w' ltac:(cbn; lia)); [| exact Hw' ].
      cbn [List.length List.app]; rewrite List.firstn_cons.
      econstructor; [ exact Hrm | exact Hc |].
      rewrite <- !env_args_snoc; exact Hg.
    + intros ys ys' w w' Hys Hlys Hw Hw'.
      rewrite <- (List.app_assoc xs (c :: nil) ys) in Hw |- *; rewrite <- (List.app_assoc xs' (c' :: nil) ys') in Hw' |- *.
      cbn [List.app] in Hw, Hw' |- *.
      apply Hbase; [| cbn; lia | exact Hw | exact Hw' ].
      econstructor; [ exact Hrm | exact Hc |].
      rewrite <- !env_args_snoc; exact Hys.
Qed.

(** ** The Relation of a Member's Type

    Every view of a group of a valid family agrees with its container, so
    the relation of a view's type, the container's at the view's instance,
    is the group's at the view; at a declared member, it is the group's
    canonical one directly.  The type of the member [k] at the uniform
    parameters as variables, after more variables [zs], at two related
    environments: its relation is the group's at [k]. *)
Lemma view_end_rel_all : forall P p D, valid_groups P -> P p D ->
    forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
    forall j, view_end_rel p D ups ups' j.
Proof.
  intros * HP HPD * Hgu Hu j.
  exact (view_end_rel_of_agreement p D (valid_groups_valid P HP p D HPD) (containers_valid_of_groups P HP p D HPD)
           ups ups' Hgu Hu j (view_agreement_canonical_all P p D HP HPD ups ups' Hgu Hu j)).
Qed.

Lemma member_type_rel : forall P p D, valid_groups P -> P p D ->
    forall k Mk ups ups' Z RZ zs zs' nn L Ns bs bs' a a' i R, ind_member D k = Some Mk ->
    List.length ups = ind_nu D -> per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
    ⊨ Z ++ ind_uparams D -> EF Z ++ ind_uparams D ≈ Z ++ ind_uparams D ∈ per_ctx_env ↘ RZ ->
    List.length zs = List.length Z -> List.length zs' = List.length Z -> L + nn = List.length zs ->
    RZ (env_args nil (ups ++ zs)) (env_args nil (ups' ++ zs')) ->
    ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ zs) ↘ bs ->
    ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups' ++ zs') ↘ bs' ->
    ⟦ ind_mty p D k (ind_uvars D nn L) Ns ⟧ env_args nil (ups ++ zs) ↘ a ->
    ⟦ ind_mty p D k (ind_uvars D nn L) Ns ⟧ env_args nil (ups' ++ zs') ↘ a' ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    (R <~> grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) k ups ups' bs bs').
Proof.
  intros P p D HP HPD * HM Hu Hgu HZ HRZ Hlz Hlz' HL HE Ebs Ebs' Ea Ea' HR.
  pose proof (valid_groups_valid P HP p D HPD) as Hg.
  pose proof (containers_valid_of_groups P HP p D HPD) as Hcv.
  pose proof (uparams_refl_l D (vgr_valid _ _ Hg) (vgr_closed _ _ Hg) _ _ Hgu) as Hgd.
  pose proof (length_ups_gargs D _ _ Hgu Hu) as Hu'.
  pose proof (uparams_refl_l D (vgr_valid _ _ Hg) (vgr_closed _ _ Hg) _ _
                (uparams_sym D (vgr_valid _ _ Hg) (vgr_closed _ _ Hg) _ _ Hgu Hu)) as Hgd'.
  assert (HPZ : PER RZ) by (eapply per_env_PER; exact HRZ).
  assert (HEl : RZ (env_args nil (ups ++ zs)) (env_args nil (ups ++ zs))) by (etransitivity; [ exact HE | symmetry; exact HE ]).
  assert (HEr : RZ (env_args nil (ups' ++ zs')) (env_args nil (ups' ++ zs'))) by (etransitivity; [ symmetry; exact HE | exact HE ]).
  destruct (eval_mty_inv _ _ _ _ _ _ _ _ HM Ea) as (cs & bs0 & Ecs & Ebs0 & ->).
  destruct (eval_mty_inv _ _ _ _ _ _ _ _ HM Ea') as (cs' & bs0' & Ecs' & Ebs0' & ->).
  pose proof (functional_eval_exps' _ _ _ _ Ebs0 Ebs) as ->; pose proof (functional_eval_exps' _ _ _ _ Ebs0' Ebs') as ->.
  destruct (im_head Mk) as [pm | qc kc Is vm] eqn:Hh.
  - unfold im_pre, im_ref in *; rewrite Hh in *; cbn [fst snd] in *.
    assert (HU : forall u w, List.length u = ind_nu D -> List.length w = List.length Z ->
                   ⟦ ind_uvars D nn L ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (u ++ w) ↘ u).
    { intros u w Hlu Hlw; unfold ind_uvars; rewrite HL, Hlz, <- Hlw, <- Hlu; apply eval_vars_from_args. }
    pose proof (functional_eval_exps' _ _ _ _ Ecs (HU _ _ Hu Hlz)) as ->.
    pose proof (functional_eval_exps' _ _ _ _ Ecs' (HU _ _ Hu' Hlz')) as ->.
    exact (proj1 (vg_type_rel_base p D Hg k Mk pm ups ups' ups ups' bs bs' i R HM Hh Hgu Hu Hgd Hgd' HR)).
  - destruct (dt_view _ _ _ (vgr_typed _ _ Hg) _ _ _ _ _ _ HM Hh) as (Dq & Mk' & Hq & _).
    assert (Ecs1 : ⟦ im_pre Mk (ind_uvars D nn L) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ zs) ↘ cs) by exact Ecs.
    assert (Ecs1' : ⟦ im_pre Mk (ind_uvars D nn L) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups' ++ zs') ↘ cs') by exact Ecs'.
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
    exists gs', ind_con Mk' c = Some gs' /\ cargs_corr vm gs' gs.
Proof.
  intros p D Hass Hdt * HM Hh Hq HMk' Hc.
  destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (Dq2 & Mk2 & Hq2 & HMk2 & _ & _ & _ & Hvm & _).
  rewrite Hq in Hq2; injection Hq2 as <-; rewrite HMk' in HMk2; injection HMk2 as <-.
  destruct (view_agree_members p D k Mk qc kc Is vm Dq Hass HM Hh Hq kc Mk' HMk') as (v & Mv & Hvmb).
  assert (v = k) as -> by (pose proof (vmb_v _ _ _ _ _ _ _ _ _ Hvmb) as Hv; rewrite Hvm in Hv; congruence).
  assert (Mv = Mk) as -> by (pose proof (vmb_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMv; rewrite HM in HMv; congruence).
  exact (vmb_cons' _ _ _ _ _ _ _ _ _ Hvmb _ _ Hc).
Qed.

(** ** The Values of a Constructor along its Arguments

    The value of the constructor [c] of the member [k] after the arguments
    [xs]: the constructor at them for a declared member; for a view, the
    view's constructor before the last uniform parameter, then the
    container's constructor at the view's instance at the uniform
    parameters, and the rest. *)
Inductive con_value (p : qname) (D : ind_decl) (k : nat) (Mk : imember) (c : String.string) : list domain -> domain -> Prop :=
| con_value_decl : forall pm xs, im_head Mk = mh_decl pm -> con_value p D k Mk c xs (d_con p k c xs)
| con_value_view_uparams : forall qc kc Is vm xs, im_head Mk = mh_view qc kc Is vm -> List.length xs < ind_nu D ->
    con_value p D k Mk c xs (d_con p k c xs)
| con_value_view : forall qc kc Is vm xs cs, im_head Mk = mh_view qc kc Is vm -> ind_nu D <= List.length xs ->
    ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (List.firstn (ind_nu D) xs) ↘ cs ->
    con_value p D k Mk c xs (d_con qc kc c (cs ++ List.skipn (ind_nu D) xs)).

(** ** A Constructor at Related Arguments

    Parameters [ps], [ps'] related at the member's telescope and arguments
    [as1], [as1'] related at the constructor's: the constructor at them, at
    any stored uniform arguments (the group's, or a view's instance), is an
    element of the member at the canonical relations. *)
Section ConArgs.
  Variable (P : qname -> ind_decl -> Prop).
  Variables (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups P) (HPD : P p D).
  Let Hg := valid_groups_valid P HP p D HPD.
  Let Hcv := containers_valid_of_groups P HP p D HPD.
  Let HD := vgr_valid _ _ Hg.
  Let Hc := vgr_closed _ _ Hg.
  Let Hass := vgr_ass _ _ Hg.
  Variables (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
  Hypotheses (HM : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs).
  Let HΨ := vg_cargs_sem p D Hg Hcv k Mk c gs HM Hcon.
  Variables (ps ps' as1 as1' : list domain).
  Hypotheses (Hgp : per_gargs (List.rev (im_params D Mk)) nil nil ps ps') (Hlp : List.length ps = im_np D Mk)
    (Hga : per_gargs (List.rev (cargs_ctx p D Mk gs)) (env_args nil ps) (env_args nil ps') as1 as1')
    (Hla : List.length as1 = List.length gs).
  Let ups := List.firstn (ind_nu D) ps.
  Let ns := List.skipn (ind_nu D) ps.
  Let ups' := List.firstn (ind_nu D) ps'.
  Let ns' := List.skipn (ind_nu D) ps'.

  Lemma con_ps : ps = ups ++ ns.
  Proof. symmetry; apply List.firstn_skipn. Qed.

  Lemma con_ps_len' : List.length ps' = im_np D Mk.
  Proof. destruct (per_gargs_length _ _ _ _ _ Hgp) as [H _]; lia. Qed.

  Lemma con_ups_rel : per_gargs (List.rev (ind_uparams D)) nil nil ups ups'.
  Proof. exact (proj1 (params_split_rel D HD Hc k Mk HM _ _ _ _ Hgp Hlp)). Qed.

  Lemma con_ups_len : List.length ups = ind_nu D.
  Proof. unfold ups; rewrite List.length_firstn; unfold im_np in Hlp; lia. Qed.

  Lemma con_ups_refl : per_gargs (List.rev (ind_uparams D)) nil nil ups ups.
  Proof. exact (uparams_refl_l D HD Hc _ _ con_ups_rel). Qed.

  Lemma con_ns_len : List.length ns = im_nn Mk.
  Proof. unfold ns; rewrite List.length_skipn; unfold im_np in Hlp; lia. Qed.

  Lemma con_ns_rel : tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns'.
  Proof.
    destruct (params_split_rel D HD Hc k Mk HM _ _ _ _ Hgp Hlp) as (_ & Hgn & _ & _).
    eapply (gargs_tele_canon _ (canon_nparams_rel D ups k) (env_args nil ups));
      [ | exact Hgn | rewrite List.length_rev, length_im_nparams; exact con_ns_len ].
    intros j A pre HA; unfold canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ _ _ HM HA), env_args_app; reflexivity.
  Qed.

  Lemma con_ns_refl : tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns.
  Proof.
    destruct (vg_canon p D Hg ups con_ups_refl con_ups_len) as [CnP CnI CaP CaI CdP CdI].
    exact (nparams_rel_refl_l p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI k Mk HM _ _ con_ns_rel).
  Qed.

  Lemma con_las' : List.length as1' = List.length gs.
  Proof. destruct (per_gargs_length _ _ _ _ _ Hga) as [H _]; lia. Qed.

  Lemma con_args_split : forall gs1 gs2, gs = gs1 ++ gs2 ->
      per_gargs (List.rev (cargs_ctx p D Mk gs1)) (env_args nil ps) (env_args nil ps')
        (List.firstn (List.length gs1) as1) (List.firstn (List.length gs1) as1') /\
      per_gargs (List.rev (cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) gs2))
        (env_args nil (ps ++ List.firstn (List.length gs1) as1)) (env_args nil (ps' ++ List.firstn (List.length gs1) as1'))
        (List.skipn (List.length gs1) as1) (List.skipn (List.length gs1) as1').
  Proof.
    intros * Heq.
    pose proof con_las' as Hla'.
    set (n := List.length gs1).
    assert (Hk : n <= List.length gs) by (unfold n; rewrite Heq, List.length_app; lia).
    pose proof Hga as H.
    unfold cargs_ctx in H; rewrite Heq, cargs_ctx_aux_app, List.app_nil_r, List.rev_app_distr in H.
    rewrite <- (List.firstn_skipn n as1), <- (List.firstn_skipn n as1') in H.
    assert (L1 : List.length (List.firstn n as1) = List.length (List.rev (cargs_ctx_aux p D (im_nn Mk) nil gs1)))
      by (rewrite List.length_firstn, List.length_rev, length_cargs_ctx_aux; unfold n; lia).
    assert (L2 : List.length (List.firstn n as1') = List.length (List.rev (cargs_ctx_aux p D (im_nn Mk) nil gs1)))
      by (rewrite List.length_firstn, List.length_rev, length_cargs_ctx_aux; unfold n; lia).
    destruct (per_gargs_app (List.rev (cargs_ctx_aux p D (im_nn Mk) nil gs1)) (List.rev (cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) gs2))
                _ _ (List.firstn n as1) (List.firstn n as1') (List.skipn n as1) (List.skipn n as1') L1 H L2) as [H1 H2].
    split; [ exact H1 | rewrite !env_args_app; exact H2 ].
  Qed.

  (** The environment of the parameters and the first arguments is one of
      the context of their types. *)
  Lemma con_prefix_env : forall gs1 gs2, gs = gs1 ++ gs2 ->
      forall R, EF cargs_ctx p D Mk gs1 ++ im_params D Mk ≈ cargs_ctx p D Mk gs1 ++ im_params D Mk ∈ per_ctx_env ↘ R ->
        R (env_args nil (ps ++ List.firstn (List.length gs1) as1)) (env_args nil (ps ++ List.firstn (List.length gs1) as1)).
  Proof.
    intros * Heq R HR.
    pose proof (cargs_prefix_sem D p Mk gs HΨ _ _ Heq) as HC.
    pose proof con_las' as Hla'.
    assert (HPR : PER R) by (eapply per_env_PER; exact HR).
    assert (Hk : List.length gs1 <= List.length gs) by (rewrite Heq, List.length_app; lia).
    assert (Hcross : R (env_args nil (ps ++ List.firstn (List.length gs1) as1)) (env_args nil (ps' ++ List.firstn (List.length gs1) as1'))).
    { apply (gargs_env_rel _ _ _ _ _ _ HR HC).
      - rewrite !List.length_app, length_cargs_ctx, List.length_firstn, length_im_params; unfold im_np in *; lia.
      - rewrite List.rev_app_distr; apply per_gargs_app_intro; [ rewrite List.length_rev, length_im_params; exact Hlp | exact Hgp |].
        exact (proj1 (con_args_split _ _ Heq)). }
    etransitivity; [ exact Hcross | symmetry; exact Hcross ].
  Qed.

  (** The argument at a position, related at its type. *)
  Lemma con_entry : forall gs1 g gs2, gs = gs1 ++ g :: gs2 -> forall x x',
      List.nth_error as1 (List.length gs1) = Some x -> List.nth_error as1' (List.length gs1) = Some x' ->
      per_gargs (List.rev (cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) (g :: nil)))
        (env_args nil (ps ++ List.firstn (List.length gs1) as1)) (env_args nil (ps' ++ List.firstn (List.length gs1) as1'))
        (x :: nil) (x' :: nil).
  Proof.
    intros * Heq x x' Hx Hx'.
    destruct (con_args_split _ _ Heq) as [_ H2].
    rewrite (skipn_nth_cons' _ _ _ Hx), (skipn_nth_cons' _ _ _ Hx') in H2.
    destruct g as [A | t]; cbn [cargs_ctx_aux List.app] in H2 |- *; rewrite List.rev_app_distr in H2; cbn [List.rev List.app] in H2 |- *;
      inversion H2 as [| i T ? ? ? ? ? ? ? R HT Hxx]; subst;
      (econstructor; [ exact HT | exact Hxx | constructor ]).
  Qed.

  Lemma con_arg_step : forall gs1 A gs2, gs = gs1 ++ ca_arg A :: gs2 -> forall x x',
      List.nth_error as1 (List.length gs1) = Some x -> List.nth_error as1' (List.length gs1) = Some x' ->
      canon_args_rel D ups k ns c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1)) x x' /\
      canon_args_rel D ups k ns c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1)) x x.
  Proof.
    intros * Heq x x' Hx Hx'.
    assert (Hlk : List.length (List.firstn (List.length gs1) as1) = List.length gs1)
      by (rewrite List.length_firstn; rewrite Hla, Heq, List.length_app; cbn; lia).
    pose proof (con_entry _ _ _ Heq x x' Hx Hx') as He.
    cbn [cargs_ctx_aux List.app List.rev] in He.
    inversion He as [| i T ? ? ? ? ? ? ? Rk [t t' Et Et' HRk] Hxx]; clear He.
    assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
      by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
    destruct (vid_arg _ HD _ _ _ _ _ _ HM Hcon HA) as (_ & jA & HAv).
    rewrite Heq, <- nonrec_args_prefix_cargs_strat in HAv.
    destruct (rel_exp_under_ctx_wk_simple (cargs_wk D p k Mk c gs HD HM Hcon HΨ _ _ Heq) HAv) as (RΓ & HΓ & i0 & Hwk).
    pose proof (con_prefix_env _ _ Heq _ HΓ) as HE1.
    destruct (Hwk _ _ HE1) as (y & y' & Ry & Ey & Ey' & HRy & m & m' & Em & Em' & Hmm).
    assert (Hy : y = d_univ jA) by (cbn in Ey; inversion Ey; reflexivity).
    rewrite Hy in HRy; clear Hy Ey Ey'.
    destruct (per_univ_elem_univ _ _ _ _ HRy (or_introl (ex_intro _ _ eq_refl))) as [_ ERy].
    apply ERy in Hmm; destruct Hmm as [Rm HRm].
    assert (m = t) as -> by (eapply functional_eval_exp; eassumption).
    rewrite env_args_app, eval_wk_pat_args, <- env_args_app in Em' by exact Hlk.
    assert (ERk : Rk <~> Rm) by (eapply per_univ_elem_right_irrel; [ exact HRk | exact HRm ]).
    pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRm) HRm) as HRd.
    assert (Hcan : canon_args_rel D ups k ns c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1))
                     <~> Rm).
    { unfold canon_args_rel; rewrite (nth_atyp_eq _ _ _ _ _ _ _ HM Hcon HA).
      rewrite List.app_assoc, <- con_ps.
      symmetry; exact (per_head_iff Em' Em' HRd). }
    assert (HPk : PER Rk) by (eapply per_elem_PER; exact HRk).
    split.
    - apply Hcan, ERk, Hxx.
    - apply Hcan, ERk; etransitivity; [ exact Hxx | symmetry; exact Hxx ].
  Qed.

  Lemma con_rec_step : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      tele_prefix_rel (canon_args_rel D ups k ns c) (List.length (cargs_nonrec gs1))
        (nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1)) ->
      tele_prefix_rel (canon_args_rel D ups k ns c) (List.length (cargs_nonrec gs1))
        (nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1')) ->
      forall x x', List.nth_error as1 (List.length gs1) = Some x -> List.nth_error as1' (List.length gs1) = Some x' ->
        rec_arg_rel p D (okr_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups)
          k ups ups' (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1))
          (ns' ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1')) t x x'.
  Proof.
    intros * Heq INV INVc x x' Hx Hx'.
    pose proof (con_entry _ _ _ Heq x x' Hx Hx') as He.
    cbn [cargs_ctx_aux List.app List.rev] in He.
    inversion He as [| i T ? ? ? ? ? ? ? Rk [a a' Ea Ea' HRk] Hxx]; clear He.
    pose proof (per_univ_trans _ _ _ _ _ _ HRk (per_univ_sym _ _ _ _ HRk)) as HRd.
    assert (Hlk : List.length (List.firstn (List.length gs1) as1) = List.length gs1)
      by (rewrite List.length_firstn; rewrite Hla, Heq, List.length_app; cbn; lia).
    assert (Hpre : forall R, EF cargs_ctx p D Mk gs1 ++ im_params D Mk ≈ cargs_ctx p D Mk gs1 ++ im_params D Mk ∈ per_ctx_env ↘ R ->
               R (env_args nil (ups ++ ns ++ List.firstn (List.length gs1) as1)) (env_args nil (ups ++ ns ++ List.firstn (List.length gs1) as1))).
    { intros R HR; rewrite List.app_assoc, <- con_ps; exact (con_prefix_env _ _ Heq R HR). }
    rewrite con_ps, <- List.app_assoc in Ea.
    pose proof (view_end_rel_all P p D HP HPD ups ups con_ups_refl con_ups_len (ptyp_mem t)) as Hend.
    pose proof (shape_char p D Hg Hcv k Mk c gs HM Hcon HΨ _ _ _ Heq ups ns _ con_ups_len con_ns_len Hlk con_ups_refl con_ns_refl
                  INV Hpre Hend (List.length (ptyp_doms t)) 0 nil a i Rk eq_refl (tele_prefix_rel_nil _) ltac:(cbn; constructor)
                  ltac:(rewrite List.app_nil_r; exact Ea) HRd) as Hsh.
    rewrite List.app_nil_r in Hsh; cbn [ptyp_skip] in Hsh; apply Hsh in Hxx.
    apply (vg_rec_arg_move_right p D Hg k Mk c gs1 t gs2 ups ups' ns ns' _ _ x x' HM ltac:(rewrite <- Heq; exact Hcon)
             con_ups_rel con_ups_len con_ns_rel INVc).
    exact Hxx.
  Qed.

  Lemma con_split_at : forall n g, List.nth_error gs n = Some g ->
      gs = List.firstn n gs ++ g :: List.skipn (S n) gs /\ List.length (List.firstn n gs) = n.
  Proof.
    intros * Hg0; split; [ rewrite <- (skipn_nth_cons' _ _ _ Hg0), List.firstn_skipn; reflexivity |].
    rewrite List.length_firstn; assert (n < List.length gs) by (apply List.nth_error_Some; congruence); lia.
  Qed.

  Lemma con_prefix : forall n, n <= List.length gs ->
      tele_prefix_rel (canon_args_rel D ups k ns c) (List.length (cargs_nonrec (List.firstn n gs)))
        (nonrec_arg_vals (List.firstn n gs) (List.firstn n as1)) (nonrec_arg_vals (List.firstn n gs) (List.firstn n as1')) /\
      tele_prefix_rel (canon_args_rel D ups k ns c) (List.length (cargs_nonrec (List.firstn n gs)))
        (nonrec_arg_vals (List.firstn n gs) (List.firstn n as1)) (nonrec_arg_vals (List.firstn n gs) (List.firstn n as1)).
  Proof.
    pose proof con_las' as Hla'.
    induction n as [| n IH]; intros Hn; [ cbn; split; apply tele_prefix_rel_nil |].
    destruct (IH ltac:(lia)) as [IHc IHd].
    destruct (nth_error_lt_some' gs n ltac:(lia)) as [g Hg0].
    destruct (nth_error_lt_some' as1 n ltac:(lia)) as [x Hx].
    destruct (nth_error_lt_some' as1' n ltac:(lia)) as [x' Hx'].
    destruct (con_split_at _ _ Hg0) as [Heq Hlf].
    rewrite (firstn_S_snoc _ _ _ Hg0), (firstn_S_snoc _ _ _ Hx), (firstn_S_snoc _ _ _ Hx').
    rewrite !nonrec_arg_vals_app by (rewrite !List.length_firstn; lia).
    rewrite cargs_nonrec_app.
    destruct g as [A | t]; cbn [nonrec_arg_vals cargs_nonrec].
    - rewrite <- Hlf in Hx, Hx'.
      destruct (con_arg_step _ _ _ Heq x x' Hx Hx') as [Hr Hrd].
      rewrite Hlf in Hr, Hrd.
      rewrite List.length_app, Nat.add_1_r.
      split; apply tele_prefix_rel_snoc; assumption.
    - rewrite !List.app_nil_r; split; assumption.
  Qed.

  Lemma con_args_relate : forall gs2 gs1, gs = gs1 ++ gs2 ->
      con_args_rel p D (okr_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups)
        k ups ups' (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1))
        (ns' ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1')) gs2
        (List.skipn (List.length gs1) as1) (List.skipn (List.length gs1) as1').
  Proof.
    pose proof con_las' as Hla'.
    induction gs2 as [| g gs2 IH]; intros gs1 Heq.
    - rewrite List.app_nil_r in Heq.
      rewrite (List.skipn_all2 as1), (List.skipn_all2 as1') by (rewrite <- Heq; lia); constructor.
    - assert (Hk : List.length gs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some' as1 (List.length gs1) ltac:(lia)) as [x Hx].
      destruct (nth_error_lt_some' as1' (List.length gs1) ltac:(lia)) as [x' Hx'].
      rewrite (skipn_nth_cons' _ _ _ Hx), (skipn_nth_cons' _ _ _ Hx').
      assert (Heq' : gs = (gs1 ++ g :: nil) ++ gs2) by (rewrite <- List.app_assoc; exact Heq).
      pose proof (IH _ Heq') as IHg.
      rewrite List.length_app in IHg; cbn [List.length] in IHg; rewrite Nat.add_1_r in IHg.
      rewrite (firstn_S_snoc _ _ _ Hx), (firstn_S_snoc _ _ _ Hx'), !nonrec_arg_vals_app in IHg by (rewrite List.length_firstn; lia).
      destruct g as [A | t]; cbn [nonrec_arg_vals] in IHg.
      + constructor.
        rewrite <- !List.app_assoc; exact IHg.
      + assert (Hpre : List.firstn (List.length gs1) gs = gs1)
          by (rewrite Heq, firstn_app_exact by reflexivity; reflexivity).
        destruct (con_prefix (List.length gs1) ltac:(lia)) as [INVc INVd].
        rewrite Hpre in INVc, INVd.
        constructor; [ exact (con_rec_step _ _ _ Heq INVd INVc x x' Hx Hx') |].
        repeat rewrite List.app_nil_r in IHg; exact IHg.
  Qed.

  Lemma con_rel : forall cs cs', List.length cs = im_unu D Mk -> List.length cs' = im_unu D Mk ->
      ind_rel p D (okr_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups)
        k ups ups' ns ns'
        (d_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c ((cs ++ ns) ++ as1))
        (d_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c ((cs' ++ ns') ++ as1')).
  Proof.
    intros cs cs' Hcs Hcs'.
    pose proof con_las' as Hla'.
    pose proof con_ps_len' as Hlp'.
    assert (Hsk : forall (l1 l2 : list domain), List.length l1 = im_unu D Mk -> List.skipn (im_unu D Mk) (l1 ++ l2) = l2)
      by (intros l1 l2 Hl1; rewrite <- Hl1, List.skipn_app, List.skipn_all, Nat.sub_diag; reflexivity).
    assert (Hlns' : List.length ns' = im_nn Mk) by (unfold ns'; rewrite List.length_skipn; unfold im_np in *; lia).
    destruct (vg_canon p D Hg ups con_ups_refl con_ups_len) as [CnP CnI CaP CaI CdP CdI].
    destruct (con_prefix (List.length gs) (le_n _)) as [Hnr _].
    rewrite List.firstn_all, !List.firstn_all2 in Hnr by lia.
    eapply ind_rel_con with (gs := gs) (Mk := Mk);
      [ exact HM | apply surjective_pairing | exact con_ns_rel | exact Hcon
      | rewrite List.length_app, Hcs, con_ns_len; lia | rewrite List.length_app, Hcs', Hlns'; lia
      | rewrite (Hsk _ _ Hcs); exact con_ns_refl
      | rewrite (Hsk _ _ Hcs'); exact (nparams_rel_refl_r p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HM _ _ con_ns_rel)
      | rewrite (Hsk _ _ Hcs); exact (tele_rel_of_pre _ _ _ _ Hnr) |].
    rewrite (Hsk _ _ Hcs), (Hsk _ _ Hcs').
    pose proof (con_args_relate gs nil eq_refl) as H; cbn [List.length List.skipn nonrec_arg_vals List.firstn] in H.
    repeat rewrite List.app_nil_r in H; exact H.
  Qed.
End ConArgs.

(** ** The Constructor as an Element of its Type *)
Section ConValue.
  Variable (P : qname -> ind_decl -> Prop).
  Variables (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups P) (HPD : P p D).
  Let Hg := valid_groups_valid P HP p D HPD.
  Let Hcv := containers_valid_of_groups P HP p D HPD.
  Let HD := vgr_valid _ _ Hg.
  Let Hc := vgr_closed _ _ Hg.
  Let Hass := vgr_ass _ _ Hg.
  Let Hdt := vgr_typed _ _ Hg.
  Variables (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
  Hypotheses (HM : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs).
  Let HΨ := vg_cargs_sem p D Hg Hcv k Mk c gs HM Hcon.

  (** The constructor, at no argument. *)
  Lemma con_value_start : forall ρ, exists v, ⟦ a_con p k c ⟧ ρ ↘ v /\ con_value p D k Mk c nil v.
  Proof.
    intros ρ.
    destruct (im_head Mk) as [pm | qc kc Is vm] eqn:Hh.
    - exists (d_con p k c nil); split; [| exact (con_value_decl _ _ _ _ _ pm nil Hh) ].
      eapply eval_exp_con; [ exact (vgr_lookup _ _ Hg) | exact HM |].
      unfold im_starts, im_is_decl; rewrite Hh; reflexivity.
    - destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (Dq & Mk' & Hq & _).
      destruct (Nat.eq_dec (ind_nu D) 0) as [H0 | H0].
      + assert (Hg0 : per_gargs (List.rev (ind_uparams D)) nil nil nil nil) by constructor.
        destruct (vg_view_args_values p D Hg Hcv _ _ _ _ _ _ _ HM Hh Hq nil nil Hg0 ltac:(cbn [List.length]; lia))
          as (cups & _ & Ecups & _ & _).
        exists (d_con qc kc c (cups ++ List.skipn (ind_nu D) nil)); split.
        * rewrite List.skipn_nil, List.app_nil_r.
          eapply eval_exp_con_view; [ exact (vgr_lookup _ _ Hg) | exact HM | exact Hh | exact H0 | exact Ecups ].
        * apply (con_value_view p D k Mk c qc kc Is vm nil cups Hh ltac:(cbn [List.length]; lia)).
          rewrite List.firstn_nil; exact Ecups.
      + exists (d_con p k c nil); split; [| exact (con_value_view_uparams p D k Mk c qc kc Is vm nil Hh ltac:(cbn [List.length]; lia)) ].
        eapply eval_exp_con; [ exact (vgr_lookup _ _ Hg) | exact HM |].
        unfold im_starts, im_is_decl; rewrite Hh; cbn [orb]; apply Nat.ltb_lt; lia.
  Qed.

  (** The constructor takes the next argument, its view's instance
      evaluating at the last uniform parameter. *)
  Lemma con_value_step : forall ys y w, List.length ys < im_np D Mk + List.length gs ->
      (forall qc kc Is vm, im_head Mk = mh_view qc kc Is vm -> S (List.length ys) = ind_nu D ->
         exists cs, ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ys ++ y :: nil) ↘ cs) ->
      con_value p D k Mk c ys w -> exists u, $| w & y | gc_deps ⍮ gc_stack ↘ u /\ con_value p D k Mk c (ys ++ y :: nil) u.
  Proof.
    intros ys y w Hlys Hev Hw.
    inversion Hw as [pm xs Hh | qc kc Is vm xs Hh Hlt | qc kc Is vm xs cs Hh Hle Ecs]; subst.
    - exists (d_con p k c (ys ++ y :: nil)); split; [| exact (con_value_decl _ _ _ _ _ pm _ Hh) ].
      eapply eval_app_con; [ exact (vgr_lookup _ _ Hg) | exact HM | exact Hh | exact Hcon | exact Hlys ].
    - destruct (Nat.lt_ge_cases (S (List.length ys)) (ind_nu D)) as [Hlt' | Hge].
      + exists (d_con p k c (ys ++ y :: nil)); split.
        * eapply eval_app_con_view; [ exact (vgr_lookup _ _ Hg) | exact HM | exact Hh | exact Hlt' ].
        * apply (con_value_view_uparams _ _ _ _ _ qc kc Is vm _ Hh); rewrite List.length_app; cbn [List.length]; lia.
      + destruct (Hev _ _ _ _ Hh ltac:(lia)) as [cs Ecs].
        assert (Hl1 : List.length (ys ++ y :: nil) = ind_nu D) by (rewrite List.length_app; cbn [List.length]; lia).
        exists (d_con qc kc c (cs ++ List.skipn (ind_nu D) (ys ++ y :: nil))); split.
        * rewrite List.skipn_all2, List.app_nil_r by lia.
          eapply eval_app_con_view_ups; [ exact (vgr_lookup _ _ Hg) | exact HM | exact Hh | lia | exact Ecs ].
        * apply (con_value_view p D k Mk c qc kc Is vm (ys ++ y :: nil) cs Hh ltac:(lia)).
          rewrite List.firstn_all2 by lia; exact Ecs.
    - (** The container's constructor takes it. *)
      destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (Dq & Mk' & Hq & HMk' & Hkd & HIl & _ & Hvm & _).
      pose proof (Hcv _ _ _ _ _ _ _ HM Hh Hq) as HgQ.
      assert (Hhd : exists pm, im_head Mk' = mh_decl pm).
      { pose proof (proj2 (dt_order _ _ _ (vgr_typed _ _ HgQ) _ _ HMk') Hkd) as Hd.
        unfold im_is_decl in Hd; destruct (im_head Mk'); [ eauto | discriminate ]. }
      destruct Hhd as [pm Hhd].
      destruct (view_con_container p D Hass Hdt k Mk qc kc Is vm Dq Mk' c gs HM Hh Hq HMk' Hcon) as (gs' & Hcon' & Hcorr).
      destruct (view_agree_members p D k Mk qc kc Is vm Dq Hass HM Hh Hq kc Mk' HMk') as (v & Mv & Hvmb).
      assert (v = k) as -> by (pose proof (vmb_v _ _ _ _ _ _ _ _ _ Hvmb) as Hv; rewrite Hvm in Hv; congruence).
      assert (Mv = Mk) as -> by (pose proof (vmb_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMv; rewrite HM in HMv; congruence).
      pose proof (vmb_nn _ _ _ _ _ _ _ _ _ Hvmb) as Hnn.
      pose proof (cargs_corr_len _ _ _ Hcorr) as Hlg.
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
  Lemma con_value_full : forall zs w, List.length zs = im_np D Mk + List.length gs -> con_value p D k Mk c zs w ->
      exists cs, List.length cs = im_unu D Mk /\
        w = d_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c (cs ++ List.skipn (ind_nu D) zs).
  Proof.
    intros zs w Hlz Hw.
    inversion Hw as [pm xs Hh | qc kc Is vm xs Hh Hlt | qc kc Is vm xs cs Hh Hle Ecs]; subst.
    - exists (List.firstn (ind_nu D) zs); unfold im_unu, im_ref; rewrite Hh; cbn [fst snd].
      split; [ rewrite List.length_firstn; unfold im_np in *; lia | rewrite List.firstn_skipn; reflexivity ].
    - unfold im_np in *; lia.
    - exists cs; unfold im_unu, im_ref; rewrite Hh; cbn [fst snd].
      split; [ exact (eval_exps_length _ _ _ Ecs) | reflexivity ].
  Qed.

  (** The constructor's value at related parameters and arguments, at its
      codomain. *)
  Lemma con_at_args : forall zs zs' w w', per_gargs (List.rev (cargs_ctx p D Mk gs ++ im_params D Mk)) nil nil zs zs' ->
      List.length zs = List.length (cargs_ctx p D Mk gs ++ im_params D Mk) ->
      con_value p D k Mk c zs w -> con_value p D k Mk c zs' w' ->
      Dom w ≈ w' ∈ per_head (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)))
        (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)))
        (env_args nil zs) (env_args nil zs').
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
    assert (HE : RZ (env_args nil (ups ++ ns ++ as1)) (env_args nil (ups' ++ ns' ++ as1'))).
    { rewrite <- Ezs, <- Ezs'.
      apply (gargs_env_rel _ _ _ _ _ _ HRZ HZ); [ rewrite List.length_app, HlZ; unfold im_np, ind_nu in *; lia |].
      unfold Z; rewrite <- List.app_assoc; exact Hg0. }
    assert (Ens : ⟦ vars_from (List.length gs) (im_nn Mk) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns ++ as1) ↘ ns).
    { rewrite env_args_app, <- Hla, <- Hlns; apply eval_vars_from_args. }
    assert (Ens' : ⟦ vars_from (List.length gs) (im_nn Mk) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups' ++ ns' ++ as1') ↘ ns').
    { rewrite env_args_app, <- Hla', <- Hlns'; apply eval_vars_from_args. }
    rewrite Ezs in Ebb; rewrite Ezs' in Ebb'.
    pose proof (member_type_rel P p D HP HPD k Mk ups ups' Z RZ (ns ++ as1) (ns' ++ as1') (im_nn Mk) (List.length gs)
                  _ ns ns' bb bb' i0 Rb HM Hu Hgu HZ HRZ ltac:(rewrite List.length_app, HlZ; lia)
                  ltac:(rewrite List.length_app, HlZ; lia) ltac:(rewrite List.length_app; lia) HE Ens Ens' Ebb Ebb' HRb) as ER.
    apply ER.
    (** The constructor's values. *)
    destruct (con_value_full zs w ltac:(lia) Hw) as (cs & Hcs & ->).
    destruct (con_value_full zs' w' ltac:(lia) Hw') as (cs' & Hcs' & ->).
    assert (Hu' : List.length ups' = ind_nu D) by (unfold ups'; rewrite List.length_firstn; unfold im_np in *; lia).
    assert (Esk : List.skipn (ind_nu D) zs = ns ++ as1).
    { rewrite Ezs, List.skipn_app, (List.skipn_all2 ups) by lia.
      replace (ind_nu D - List.length ups) with 0 by lia; reflexivity. }
    assert (Esk' : List.skipn (ind_nu D) zs' = ns' ++ as1').
    { rewrite Ezs', List.skipn_app, (List.skipn_all2 ups') by lia.
      replace (ind_nu D - List.length ups') with 0 by lia; reflexivity. }
    rewrite Esk, Esk', !List.app_assoc.
    exact (con_rel P p D HP HPD k Mk c gs HM Hcon ps ps' as1 as1' Hgp Hlp Hga Hla cs cs' Hcs Hcs').
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
    destruct (Hsimp nil nil (HRall _ _)) as (b & b' & Eb & Eb' & [R1 HR1]).
    destruct (Hsimp ρ nil (HRall _ _)) as (a0 & b0 & Ea0 & Eb0 & [R2 HR2]).
    assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR2 HR1) as (R3 & HR3 & E3).
    assert (E : R0 <~> R1)
      by (etransitivity; [ eapply per_univ_elem_right_irrel; [ exact HR0 | exact HR2 ] |];
          etransitivity; [ exact E3 | eapply per_univ_elem_left_irrel; [ exact HR3 | exact HR1 ] ]).
    apply E.
    set (ts := List.rev (cargs_ctx p D Mk gs ++ im_params D Mk)).
    assert (Hts : tele_ass ts)
      by (apply List.Forall_rev, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc k Mk HM) ]).
    unfold con_ty in Eb, Eb'; rewrite <- ctx_pi_app, <- (List.rev_involutive (cargs_ctx p D Mk gs ++ im_params D Mk)) in Eb, Eb'.
    fold ts in Eb, Eb'.
    assert (Hlts : List.length ts = im_np D Mk + List.length gs)
      by (unfold ts; rewrite List.length_rev, List.length_app, length_cargs_ctx, length_im_params; lia).
    (** At the last uniform parameter, the view's instance evaluates. *)
    assert (Hup : forall ys ys' y y', List.length ys < List.length ts ->
               per_gargs (List.firstn (S (List.length ys)) ts) (env_args nil nil) (env_args nil nil) (ys ++ y :: nil) (ys' ++ y' :: nil) ->
               forall qc kc Is vm, im_head Mk = mh_view qc kc Is vm -> S (List.length ys) = ind_nu D ->
                 (exists cs, ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ys ++ y :: nil) ↘ cs) /\
                 (exists cs', ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ys' ++ y' :: nil) ↘ cs')).
    { intros * Hly Hgy qc kc Is vm Hh Hnu.
      destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (Dq & Mk' & Hq & _).
      assert (Hft : List.firstn (S (List.length ys)) ts = List.rev (ind_uparams D)).
      { unfold ts; rewrite List.rev_app_distr, rev_im_params, <- List.app_assoc, Hnu.
        apply firstn_app_exact; rewrite List.length_rev; reflexivity. }
      rewrite Hft in Hgy.
      destruct (vg_view_args_values p D Hg Hcv _ _ _ _ _ _ _ HM Hh Hq _ _ Hgy ltac:(rewrite List.length_app; cbn [List.length]; lia))
        as (cs & cs' & Ecs & Ecs' & _).
      split; [ exists cs; exact Ecs | exists cs'; exact Ecs' ]. }
    eapply (ctx_pi_rel_elem_by (con_value p D k Mk c) _ ts Hts nil nil nil nil v v');
      [ reflexivity | exact Hv | exact Hv' | | | exact Eb | exact Eb' | exact HR1 | ].
    - intros ys ys' y y' w Hly Hgy Hw; cbn [List.app] in Hw |- *.
      apply (con_value_step ys y w ltac:(lia)); [| exact Hw ].
      intros * Hh Hnu; exact (proj1 (Hup _ _ _ _ Hly Hgy _ _ _ _ Hh Hnu)).
    - intros ys ys' y y' w' Hly Hgy Hw'; cbn [List.app] in Hw' |- *.
      pose proof (per_gargs_length _ _ _ _ _ Hgy) as [Hl' _]; rewrite !List.length_app in Hl'; cbn in Hl'.
      apply (con_value_step ys' y' w' ltac:(lia)); [| exact Hw' ].
      intros * Hh Hnu; exact (proj2 (Hup _ _ _ _ Hly Hgy _ _ _ _ Hh ltac:(lia))).
    - intros zs zs' w w' Hg0 Hlz Hw Hw'; cbn [List.app env_args] in *.
      apply con_at_args; [ exact Hg0 | rewrite Hlz; unfold ts; rewrite List.length_rev; reflexivity | exact Hw | exact Hw' ].
  Qed.
End ConValue.

End Fixed_GCtx.
