(** * The View Equations, Read in the PER Model

    The semantic view equations of a group ([views_self_valid]) are
    judgments over the context [grp_sctx D] of the group's members as
    variables.  At an environment [ρS] of that context related to itself,
    they relate the group's telescopes, weakened past the members
    ([self_wk]), to the container's, instantiated at the view's arguments.
    Read back through the two substitutions, they relate the group's
    telescopes at its uniform parameters [ups] (the value of [self_wk] at
    [ρS]) to the container's at [cups] (the value of the view's arguments
    at [ρS]): position by position, the types are related, so their head
    PERs, which are the canonical relations of the two groups, agree.

    This file proves the generic step for two telescopes equal under two
    substitutions ([tele_link], [tele_link_gargs]), the change of base of a
    closed telescope ([tele_base_change]), and the syntactic fields of
    [view_agreement] ([view_agree_members], [view_agree_recursive_targets]).
    The semantic fields at the canonical relations are in [ViewArgs]. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic.PER Require Import Tele.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Instance Telescope.
From Mctt.Core.Completeness Require Import UnitCases.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Inductives Require Import Decl.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Positions of a Context Equation *)

(** An assumption at the head of two related contexts: related tails, and
    a type related at related tails. *)
Lemma per_ctx_env_ass_inv : forall Γ Γ' A A' R,
    EF Γ ▹ A ≈ Γ' ▹ A' ∈ per_ctx_env ↘ R ->
    exists RT, EF Γ ≈ Γ' ∈ per_ctx_env ↘ RT /\
      (forall ρ ρ', R ρ ρ' -> RT ρ↯ ρ'↯) /\
      (forall ρ ρ', RT ρ ρ' -> exists i R0, rel_typ i A ρ A' ρ' R0).
Proof.
  intros * H.
  inversion H as [| ? ? ? ? ? tail_rel head_rel ? HT _ Hhead Hiff | |]; subst.
  exists tail_rel; split; [ exact HT | split ].
  - intros ρ ρ' Hρ; apply Hiff in Hρ; destruct Hρ as [Ht _]; exact Ht.
  - intros ρ ρ' Hρ; exists i, (head_rel _ _ Hρ); exact (Hhead _ _ Hρ).
Qed.

(** A telescope under a substitution, split at a position: the entries
    inside it, the one at it, and the prefix before it. *)
Lemma tele_sub_rev_split : forall t j A σ, List.nth_error t j = Some (ce_ass A) ->
    tele_sub (List.rev t) σ =
      tele_sub (List.rev (List.skipn (S j) t)) (sb_qn (S j) σ) ++ ce_ass A[sb_qn j σ] :: tele_sub (List.rev (List.firstn j t)) σ.
Proof.
Proof.
  intros * H.
  assert (Hj : j < List.length t) by (apply List.nth_error_Some; congruence).
  assert (Hf : List.length (List.firstn j t) = j) by (rewrite List.length_firstn; lia).
  rewrite <- (List.firstn_skipn_middle _ _ H) at 1.
  rewrite List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; cbn [List.app].
  rewrite tele_sub_app; cbn [List.length]; rewrite List.length_rev, Hf; cbn [tele_sub centry_sub].
  rewrite List.length_rev, Hf; reflexivity.
Qed.

(** ** Two Telescopes Equal under Two Substitutions

    Over a context [Γ] (the group's [Self] context), the group's telescope
    [tg] over [Bg] under [σg] and the container's [tc] over [Bc] under [σc]
    are equal ([Heq]).  At an environment [ρS] of [Γ] related to itself,
    with [Eg] and [Ec] the values of the substitutions there, arguments
    related at both telescopes see related types at each position, and
    arguments related at the container's are related at the group's. *)
Section TeleLink.
  Variables (Γ : ctx) (RΓ : relation env) (ρS : env).
  Hypotheses (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HρS : RΓ ρS ρS).
  Variables (Bg Bc : ctx) (σg σc : sub) (Eg Ec : env).
  Hypotheses (Hσg : Γ ⊨ˢ σg ≈ σg : Bg) (Hσc : Γ ⊨ˢ σc ≈ σc : Bc).
  Hypotheses (HEg : ⟦ σg ⟧s ρS ↘ Eg) (HEc : ⟦ σc ⟧s ρS ↘ Ec).
  Variables (tg tc : list centry).
  Hypotheses (Hag : tele_ass tg) (Hac : tele_ass tc) (Hlen : List.length tg = List.length tc).
  Hypotheses (HWg : ⊨ List.rev tg ++ Bg) (HWc : ⊨ List.rev tc ++ Bc).
  Hypothesis (HTg : forall j A, List.nth_error tg j = Some (ce_ass A) ->
                 exists i : nat, List.rev (List.firstn j tg) ++ Bg ⊨ A : Typeω@i).
  Hypothesis (HTc : forall j A, List.nth_error tc j = Some (ce_ass A) ->
                 exists i : nat, List.rev (List.firstn j tc) ++ Bc ⊨ A : Typeω@i).
  Hypothesis (Heq : Γ ⊨ˣ tele_sub (List.rev tg) σg ≈ tele_sub (List.rev tc) σc).

  Lemma tele_ass_firstn : forall t j, tele_ass t -> tele_ass (List.rev (List.firstn j t)).
  Proof.
    intros t j H; apply List.Forall_rev.
    rewrite <- (List.firstn_skipn j t) in H; apply List.Forall_app in H as [H _]; exact H.
  Qed.

  Lemma rel_ctx_wf_firstn : forall t B j, ⊨ List.rev t ++ B -> ⊨ List.rev (List.firstn j t) ++ B.
  Proof.
    intros t B j H; rewrite <- (List.firstn_skipn j t), List.rev_app_distr, <- List.app_assoc in H.
    exact (rel_ctx_wf_app_r _ _ H).
  Qed.

  (** The head PERs at a position agree. *)
  Lemma tele_link_head : forall j vs G C, List.length vs = j ->
      List.nth_error tg j = Some (ce_ass G) -> List.nth_error tc j = Some (ce_ass C) ->
      per_gargs (List.firstn j tg) Eg Eg vs vs -> per_gargs (List.firstn j tc) Ec Ec vs vs ->
      (per_head C C (env_args Ec vs) (env_args Ec vs) <~> per_head G G (env_args Eg vs) (env_args Eg vs)) /\
      exists (i : nat) R b, ⟦ G ⟧ env_args Eg vs ↘ b /\ DF b ≈ b ∈ per_univ_elem i ↘ R.
  Proof.
    intros j vs G C Hl HG HC Hgg Hgc.
    assert (Hj : j < List.length tg) by (apply List.nth_error_Some; congruence).
    assert (Hfg : List.length (List.firstn j tg) = j) by (rewrite List.length_firstn; lia).
    assert (Hfc : List.length (List.firstn j tc) = j) by (rewrite List.length_firstn; lia).
    (** The equation, cut at the position: the types there, under the two
        substitutions, are related at related environments of the prefixes. *)
    destruct Heq as [_ _ [R HR]].
    rewrite (tele_sub_rev_split _ _ _ _ HG), (tele_sub_rev_split _ _ _ _ HC), <- !List.app_assoc in HR.
    cbn [List.app] in HR.
    assert (Hlt : List.length (tele_sub (List.rev (List.skipn (S j) tg)) (sb_qn (S j) σg)) =
                  List.length (tele_sub (List.rev (List.skipn (S j) tc)) (sb_qn (S j) σc)))
      by (rewrite !length_tele_sub, !List.length_rev, !List.length_skipn; lia).
    destruct (per_ctx_env_app_tail _ _ _ _ _ Hlt HR) as (RT & HRT).
    destruct (per_ctx_env_ass_inv _ _ _ _ _ HRT) as (RT0 & HRT0 & _ & Hty).
    (** The arguments, over [ρS], at the group's prefix under [σg]. *)
    pose proof (tele_ass_firstn _ j Hag) as Hag'; pose proof (tele_ass_firstn _ j Hac) as Hac'.
    pose proof (rel_ctx_wf_firstn _ _ j HWg) as HWg'; pose proof (rel_ctx_wf_firstn _ _ j HWc) as HWc'.
    rewrite <- (List.rev_involutive (List.firstn j tg)) in Hgg; rewrite <- (List.rev_involutive (List.firstn j tc)) in Hgc.
    assert (Hlg : List.length vs = List.length (List.rev (List.firstn j tg))) by (rewrite List.length_rev; lia).
    assert (Hlc : List.length vs = List.length (List.rev (List.firstn j tc))) by (rewrite List.length_rev; lia).
    destruct (outer_base _ _ _ _ _ _ _ Hag' HWg' HRΓ Hσg HρS HEg _ Hgg Hlg) as (RSg & _ & _ & HRSg & HEg' & _).
    assert (E : RT0 <~> RSg) by (eapply per_ctx_env_right_irrel; eassumption).
    destruct (Hty _ _ (proj2 (E _ _) HEg')) as (i0 & R0 & Ht0).
    (** Each side's type under its substitution, against the type at the
        substitution's value. *)
    destruct (HTg _ _ HG) as [ig HGv]; destruct (HTc _ _ HC) as [ic HCv].
    destruct (outer_typ_link _ _ _ _ _ _ _ _ _ _ Hag' HWg' HGv HRΓ Hσg HρS HEg _ Hgg Hlg) as (ag & bg & Eag & Ebg & [Rg HRg]).
    destruct (outer_typ_link _ _ _ _ _ _ _ _ _ _ Hac' HWc' HCv HRΓ Hσc HρS HEc _ Hgc Hlc) as (ac & bc & Eac & Ebc & [Rc HRc]).
    rewrite List.length_rev, Hfg in Eag; rewrite List.length_rev, Hfc in Eac.
    destruct Ht0 as [a1 a2 Ea1 Ea2 HR0].
    assert (a1 = ag) as -> by (eapply functional_eval_exp; eassumption).
    assert (a2 = ac) as -> by (eapply functional_eval_exp; eassumption).
    split.
    - etransitivity; [ symmetry; exact (per_head_right Eac Ebc HRc) |].
      etransitivity; [ symmetry; exact (per_univ_elem_chain_iff _ _ _ _ _ _ _ HR0 HRc) |].
      etransitivity; [ symmetry; exact (per_univ_elem_chain_iff _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRg) HR0) |].
      exact (per_head_left Ebg Eag (per_univ_sym _ _ _ _ HRg)).
    - exists ig, Rg, bg; split; [ exact Ebg |].
      exact (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRg) HRg).
  Qed.

  (** The two types at a position are related to each other. *)
  Lemma tele_link_types : forall j vs G C, List.length vs = j ->
      List.nth_error tg j = Some (ce_ass G) -> List.nth_error tc j = Some (ce_ass C) ->
      per_gargs (List.firstn j tg) Eg Eg vs vs -> per_gargs (List.firstn j tc) Ec Ec vs vs ->
      exists (i : nat) R b a, ⟦ G ⟧ env_args Eg vs ↘ b /\ ⟦ C ⟧ env_args Ec vs ↘ a /\ DF b ≈ a ∈ per_univ_elem i ↘ R.
  Proof.
    intros j vs G C Hl HG HC Hgg Hgc.
    assert (Hj : j < List.length tg) by (apply List.nth_error_Some; congruence).
    assert (Hfg : List.length (List.firstn j tg) = j) by (rewrite List.length_firstn; lia).
    assert (Hfc : List.length (List.firstn j tc) = j) by (rewrite List.length_firstn; lia).
    destruct Heq as [_ _ [R HR]].
    rewrite (tele_sub_rev_split _ _ _ _ HG), (tele_sub_rev_split _ _ _ _ HC), <- !List.app_assoc in HR.
    cbn [List.app] in HR.
    assert (Hlt : List.length (tele_sub (List.rev (List.skipn (S j) tg)) (sb_qn (S j) σg)) =
                  List.length (tele_sub (List.rev (List.skipn (S j) tc)) (sb_qn (S j) σc)))
      by (rewrite !length_tele_sub, !List.length_rev, !List.length_skipn; lia).
    destruct (per_ctx_env_app_tail _ _ _ _ _ Hlt HR) as (RT & HRT).
    destruct (per_ctx_env_ass_inv _ _ _ _ _ HRT) as (RT0 & HRT0 & _ & Hty).
    pose proof (tele_ass_firstn _ j Hag) as Hag'; pose proof (tele_ass_firstn _ j Hac) as Hac'.
    pose proof (rel_ctx_wf_firstn _ _ j HWg) as HWg'; pose proof (rel_ctx_wf_firstn _ _ j HWc) as HWc'.
    rewrite <- (List.rev_involutive (List.firstn j tg)) in Hgg; rewrite <- (List.rev_involutive (List.firstn j tc)) in Hgc.
    assert (Hlg : List.length vs = List.length (List.rev (List.firstn j tg))) by (rewrite List.length_rev; lia).
    assert (Hlc : List.length vs = List.length (List.rev (List.firstn j tc))) by (rewrite List.length_rev; lia).
    destruct (outer_base _ _ _ _ _ _ _ Hag' HWg' HRΓ Hσg HρS HEg _ Hgg Hlg) as (RSg & _ & _ & HRSg & HEg' & _).
    assert (E : RT0 <~> RSg) by (eapply per_ctx_env_right_irrel; eassumption).
    destruct (Hty _ _ (proj2 (E _ _) HEg')) as (i0 & R0 & Ht0).
    destruct (HTg _ _ HG) as [ig HGv]; destruct (HTc _ _ HC) as [ic HCv].
    destruct (outer_typ_link _ _ _ _ _ _ _ _ _ _ Hag' HWg' HGv HRΓ Hσg HρS HEg _ Hgg Hlg) as (ag & bg & Eag & Ebg & [Rg HRg]).
    destruct (outer_typ_link _ _ _ _ _ _ _ _ _ _ Hac' HWc' HCv HRΓ Hσc HρS HEc _ Hgc Hlc) as (ac & bc & Eac & Ebc & [Rc HRc]).
    rewrite List.length_rev, Hfg in Eag; rewrite List.length_rev, Hfc in Eac.
    destruct Ht0 as [a1 a2 Ea1 Ea2 HR0].
    assert (a1 = ag) as -> by (eapply functional_eval_exp; eassumption).
    assert (a2 = ac) as -> by (eapply functional_eval_exp; eassumption).
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRg) HR0) as (R1 & H1 & _).
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ H1 HRc) as (R2 & H2 & _).
    exists ig, R2, bg, bc; split; [ exact Ebg | split; [ exact Ebc | exact H2 ] ].
  Qed.

  (** Arguments related at a prefix of the container's telescope are
      related at the group's. *)
  Lemma tele_link_gargs : forall j, j <= List.length tg -> forall vs, List.length vs = j ->
      per_gargs (List.firstn j tc) Ec Ec vs vs -> per_gargs (List.firstn j tg) Eg Eg vs vs.
  Proof.
    induction j as [| j IH]; intros Hj vs Hl Hgc; [ destruct vs; [ constructor | discriminate ] |].
    destruct (List.exists_last (l := vs) ltac:(intros ->; discriminate)) as (vs0 & x & ->).
    rewrite List.length_app in Hl; cbn in Hl.
    destruct (List.nth_error tg j) as [eg |] eqn:Eg0; [| apply List.nth_error_None in Eg0; lia ].
    destruct (List.nth_error tc j) as [ec |] eqn:Ec0; [| apply List.nth_error_None in Ec0; lia ].
    destruct (proj1 (List.Forall_forall _ _) Hag eg (List.nth_error_In _ _ Eg0)) as [G ->].
    destruct (proj1 (List.Forall_forall _ _) Hac ec (List.nth_error_In _ _ Ec0)) as [C ->].
    assert (Hfg : List.length (List.firstn j tg) = j) by (rewrite List.length_firstn; lia).
    assert (Hfc : List.length (List.firstn j tc) = j) by (rewrite List.length_firstn; lia).
    rewrite (firstn_S_nth _ _ _ Ec0) in Hgc; rewrite (firstn_S_nth _ _ _ Eg0).
    assert (Hl0c : List.length vs0 = List.length (List.firstn j tc)) by lia.
    assert (Hl0g : List.length vs0 = List.length (List.firstn j tg)) by lia.
    destruct (per_gargs_app (List.firstn j tc) (ce_ass C :: nil) Ec Ec vs0 vs0 (x :: nil) (x :: nil) Hl0c Hgc Hl0c)
      as [Hgc0 Hx].
    inversion Hx as [| ? ? ? ? ? ? ? ? ? Rx HCx Hxx _]; subst.
    pose proof (IH ltac:(lia) vs0 ltac:(lia) Hgc0) as Hgg0.
    destruct (tele_link_head j vs0 G C ltac:(lia) Eg0 Ec0 Hgg0 Hgc0) as [Eq (ib & Rg & b & Eb & HRb)].
    apply (per_gargs_snoc (List.firstn j tg) G Eg Eg vs0 vs0 x x ib Rg Hl0g Hgg0); [ econstructor; [ exact Eb | exact Eb | exact HRb ] |].
    destruct HCx as [c1 c2 Ec1 Ec2 HRx].
    apply (per_head_left Eb Eb HRb), Eq, (per_head_left Ec1 Ec2 HRx); exact Hxx.
  Qed.

  (** Hence, at arguments related at a prefix of the container's
      telescope, the head PERs of the two types after it agree. *)
  Corollary tele_link : forall j vs G C, List.length vs = j ->
      List.nth_error tg j = Some (ce_ass G) -> List.nth_error tc j = Some (ce_ass C) ->
      per_gargs (List.firstn j tc) Ec Ec vs vs ->
      per_head C C (env_args Ec vs) (env_args Ec vs) <~> per_head G G (env_args Eg vs) (env_args Eg vs).
  Proof.
    intros * Hl HG HC Hgc.
    assert (Hj : j < List.length tg) by (apply List.nth_error_Some; congruence).
    exact (proj1 (tele_link_head j vs G C Hl HG HC (tele_link_gargs j ltac:(lia) vs Hl Hgc) Hgc)).
  Qed.
End TeleLink.

(** ** A Telescope over Two Related Bases

    Arguments related at a prefix of a telescope over one environment of
    its base are related over a related one, and the head PERs after them
    agree. *)
Lemma tele_base_change : forall t B RB E1 E2, tele_ass t -> ⊨ List.rev t ++ B ->
    (forall j A, List.nth_error t j = Some (ce_ass A) -> exists i : nat, List.rev (List.firstn j t) ++ B ⊨ A : Typeω@i) ->
    EF B ≈ B ∈ per_ctx_env ↘ RB -> RB E1 E2 ->
    forall j vs, List.length vs = j -> j <= List.length t -> per_gargs (List.firstn j t) E1 E1 vs vs ->
      per_gargs (List.firstn j t) E2 E2 vs vs /\
      forall A, List.nth_error t j = Some (ce_ass A) ->
        (per_head A A (env_args E1 vs) (env_args E1 vs) <~> per_head A A (env_args E2 vs) (env_args E2 vs)).
Proof.
  intros * Ha HW HT HRB H12 j vs Hl Hj Hg.
  assert (HPB : PER RB) by (eapply per_env_PER; exact HRB).
  assert (H11 : RB E1 E1) by (etransitivity; [ exact H12 | symmetry; exact H12 ]).
  assert (H22 : RB E2 E2) by (etransitivity; [ symmetry; exact H12 | exact H12 ]).
  pose proof (rel_ctx_wf_firstn _ _ j HW) as HW'.
  assert (Ha' : tele_ass (List.firstn j t))
    by (rewrite <- (List.firstn_skipn j t) in Ha; apply List.Forall_app in Ha as [Ha _]; exact Ha).
  assert (HW'' : ⊨ List.rev (List.firstn j t) ++ B) by exact HW'.
  split.
  - exact (per_gargs_base _ _ _ HRB HW'' Ha' E1 E1 E2 E2 vs vs H11 H12 H12 Hg).
  - intros A HA.
    pose proof (per_gargs_base _ _ _ HRB HW'' Ha' E1 E1 E1 E2 vs vs H11 H11 H12 Hg) as Hg12.
    destruct (rel_ctx_wf_per_ctx_env HW') as [RΔ HRΔ].
    rewrite <- (List.rev_involutive (List.firstn j t)) in Hg12.
    assert (Hlr : List.length vs = List.length (List.rev (List.firstn j t)))
      by (rewrite List.length_rev, List.length_firstn; lia).
    pose proof (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRB HRΔ HW' H12 Hlr Hg12) as HE.
    destruct (HT _ _ HA) as [i HAv].
    destruct (rel_exp_of_typ_inversion_simple_at HRΔ HAv _ _ HE) as (a1 & a2 & Ea1 & Ea2 & [R HR]).
    etransitivity; [ symmetry; exact (per_head_left Ea1 Ea2 HR) | exact (per_head_right Ea1 Ea2 HR) ].
Qed.

(** ** The Members a View Takes the Container's To

    The field [agree_members] of [view_agreement]: syntactic, from the group's
    conditions ([gta_vwrap], [gta_vm], [gta_views]). *)
Lemma view_agree_members : forall p D k Mk qc k' Is vm Dq, grp_tele_ass D ->
    ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq ->
    forall i' Mi', ind_member Dq i' = Some Mi' -> exists v Mv, view_member p D qc Dq vm i' Mi' v Mv.
Proof.
  intros * Hass HMk Hh HDq i' Mi' HMi'.
  destruct (gta_vwrap _ Hass _ _ _ _ _ _ HMk Hh) as (D' & HD' & Hvw).
  rewrite HDq in HD'; injection HD' as <-.
  destruct (gta_vm _ Hass _ _ _ _ _ _ _ _ _ HMk Hh HDq HMi') as [v Mv Hv HMv Hnn Hhead].
  destruct (gta_views _ Hass _ _ _ _ _ _ HMk Hh) as (Dq' & Mc & HDq' & _ & _ & HlIs).
  rewrite HDq in HDq'; injection HDq' as <-.
  destruct (vwo_members _ _ _ Hvw _ _ _ HMi' Hv) as (Mv' & HMv' & _ & Hnames & Hcorr).
  rewrite HMv in HMv'; injection HMv' as <-.
  exists v, Mv; refine (mk_view_member _ _ _ _ _ _ _ _ _ Hv HMv _ _ Hnn _ _).
  - unfold im_ref; destruct (im_head Mi') as [? | qv kv Is'' vm''];
      [ destruct Hhead as [vm' ->] | destruct Hhead as (Is' & vm' & -> & _) ]; reflexivity.
  - unfold im_unu; destruct (im_head Mi') as [? | qv kv Is'' vm''];
      [ destruct Hhead as [vm' ->]; exact HlIs | destruct Hhead as (Is' & vm' & -> & HlI); exact HlI ].
  - intros c gs' Hc.
    pose proof (cons_lookup_in _ _ _ Hc) as Hin.
    assert (Hn : List.In c (List.map fst (im_cons Mv))) by (rewrite Hnames; exact (List.in_map fst _ (c, gs') Hin)).
    apply List.in_map_iff in Hn; destruct Hn as ([c0 gs0] & Ec & Hin0); cbn in Ec; subst c0.
    destruct (cons_lookup_of_in _ _ _ Hin0) as [gs HCv].
    exists gs; split; [ exact HCv | exact (Hcorr c gs' gs Hin HCv) ].
  - intros c gs Hc.
    pose proof (cons_lookup_in _ _ _ Hc) as Hin.
    assert (Hn : List.In c (List.map fst (im_cons Mi'))) by (rewrite <- Hnames; exact (List.in_map fst _ (c, gs) Hin)).
    apply List.in_map_iff in Hn; destruct Hn as ([c0 gs0] & Ec & Hin0); cbn in Ec; subst c0.
    destruct (cons_lookup_of_in _ _ _ Hin0) as [gs' HCi].
    exists gs'; split; [ exact HCi | exact (Hcorr c gs' gs (cons_lookup_in _ _ _ HCi) Hc) ].
Qed.

(** The field [agree_recursive_targets]: a recursive argument of the container's
    ends in a member of its group ([gta_plen] of the container). *)
Lemma view_agree_recursive_targets : forall Dq, grp_tele_ass Dq ->
    forall i' Mi' c gs1' t' gs2', ind_member Dq i' = Some Mi' -> ind_con Mi' c = Some (gs1' ++ ca_rec t' :: gs2') ->
      exists Mj', ind_member Dq (ptyp_mem t') = Some Mj'.
Proof.
  intros * Hass * HMi' Hc.
  destruct (gta_plen _ Hass _ _ _ _ HMi' (cons_lookup_in _ _ _ Hc) _ _ _ eq_refl) as (Mj & HMj & _).
  exists Mj; exact HMj.
Qed.

End Fixed_GCtx.
