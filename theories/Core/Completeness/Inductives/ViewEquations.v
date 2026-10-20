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
    closed telescope ([tele_base_change]), the reading of canonical
    relations as arguments ([canon_prefix_gargs]) and, from them, the
    non-uniform parameters' field of [view_coh_ok] at the canonical
    relations ([view_nparams_canon]), under the hypothesis that [ρS] is
    related to itself at [grp_sctx D]. *)

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

(** Arguments related at the canonical relation of a telescope (the head
    PER of the type at each position, [canon_nparams_rel]) are related at
    the telescope, on the left values. *)
Lemma canon_prefix_gargs : forall t B RB E, tele_ass t -> ⊨ List.rev t ++ B ->
    (forall j A, List.nth_error t j = Some (ce_ass A) -> exists i : nat, List.rev (List.firstn j t) ++ B ⊨ A : Typeω@i) ->
    EF B ≈ B ∈ per_ctx_env ↘ RB -> RB E E ->
    forall (tr : nat -> list domain -> relation domain),
      (forall k pre x y, tr k pre x y -> per_head (nth_ctyp t k) (nth_ctyp t k) (env_args E pre) (env_args E pre) x y) ->
    forall j, j <= List.length t -> forall vs vs', tele_prefix_rel tr j vs vs' -> per_gargs (List.firstn j t) E E vs vs.
Proof.
  intros * Ha HW HT HRB HE tr Htr.
  induction j as [| j IH]; intros Hj vs vs' Hp.
  - destruct Hp as [Hl _]; destruct vs; [ constructor | discriminate ].
  - pose proof Hp as Hp'; rewrite tele_prefix_rel_iff in Hp'; destruct Hp' as (Hl & Hl' & Hr).
    destruct (List.exists_last (l := vs) ltac:(intros ->; discriminate)) as (vs0 & x & ->).
    destruct (List.exists_last (l := vs') ltac:(intros ->; discriminate)) as (vs0' & x' & ->).
    rewrite List.length_app in Hl, Hl'; cbn in Hl, Hl'.
    pose proof (tele_prefix_rel_of_pre _ _ _ _ j Hp ltac:(lia)) as Hp0.
    rewrite !firstn_app_exact in Hp0 by lia.
    pose proof (IH ltac:(lia) _ _ Hp0) as Hg0.
    destruct (List.nth_error t j) as [e |] eqn:Ee; [| apply List.nth_error_None in Ee; lia ].
    destruct (proj1 (List.Forall_forall _ _) Ha e (List.nth_error_In _ _ Ee)) as [A ->].
    assert (Hx : per_head A A (env_args E vs0) (env_args E vs0) x x').
    { assert (E1 : List.nth_error (vs0 ++ x :: nil) j = Some x)
        by (rewrite List.nth_error_app2 by lia; replace (j - List.length vs0) with 0 by lia; reflexivity).
      assert (E2 : List.nth_error (vs0' ++ x' :: nil) j = Some x')
        by (rewrite List.nth_error_app2 by lia; replace (j - List.length vs0') with 0 by lia; reflexivity).
      pose proof (Htr _ _ _ _ (Hr j x x' E1 E2)) as H.
      rewrite firstn_app_exact in H by lia; unfold nth_ctyp in H; rewrite Ee in H; exact H. }
    pose proof (rel_ctx_wf_firstn _ _ j HW) as HW'.
    destruct (rel_ctx_wf_per_ctx_env HW') as [RΔ HRΔ].
    assert (Hlr : List.length vs0 = List.length (List.rev (List.firstn j t)))
      by (rewrite List.length_rev, List.length_firstn; lia).
    assert (Hg0' : per_gargs (List.rev (List.rev (List.firstn j t))) E E vs0 vs0) by (rewrite List.rev_involutive; exact Hg0).
    pose proof (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRB HRΔ HW' HE Hlr Hg0') as HEv.
    destruct (HT _ _ Ee) as [i HAv].
    destruct (rel_exp_of_typ_inversion_simple_at HRΔ HAv _ _ HEv) as (a1 & a2 & Ea1 & Ea2 & [R HR]).
    assert (a2 = a1) as -> by (eapply functional_eval_exp; eassumption).
    assert (HPR : PER R) by (eapply per_elem_PER; exact HR).
    apply (per_head_left Ea1 Ea1 HR) in Hx.
    rewrite (firstn_S_nth _ _ _ Ee).
    assert (Hlf : List.length vs0 = List.length (List.firstn j t)) by (rewrite List.length_firstn; lia).
    apply (per_gargs_snoc (List.firstn j t) A E E vs0 vs0 x x i R Hlf Hg0); [ econstructor; eassumption |].
    etransitivity; [ exact Hx | symmetry; exact Hx ].
Qed.

(** ** The Non-Uniform Parameters of a View, Canonically

    The group [D], valid, with semantic view equations [IsS]; a view
    member [k] of [D] into the container [Dq] (valid), its container member
    [i'] taken to the group's member [v].  The [Self] environment [ρS]
    extends the group's uniform parameters [ups] by values [svals] of the
    members, and is related to itself at [grp_sctx D] (the [Self]-env
    hypothesis); [cups] are the values of the view's arguments there. *)
Section ViewNparams.
  Variables (D : ind_decl) (IsS : nat -> list exp).
  Hypotheses (HvD : valid_ind_decl D) (Hvsv : views_self_valid D IsS).
  Variables (k : nat) (Mk : imember) (qc : qname) (k' : nat) (Is : list exp) (vm : list nat).
  Variables (Dq : ind_decl) (i' : nat) (Mi' : imember) (v : nat) (Mv : imember).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hh : im_head Mk = mh_view qc k' Is vm).
  Hypotheses (HDq : ind_lookup gc_deps gc_stack qc = Some Dq) (HvDq : valid_ind_decl Dq).
  Hypotheses (HMi' : ind_member Dq i' = Some Mi') (Hv : List.nth_error vm i' = Some v) (HMv : ind_member D v = Some Mv).
  (** Syntactic facts of the declarations (presupposition). *)
  Hypotheses (Hsl : List.length (grp_selfs D) = ind_ndecl D) (HaQ : tele_ass (ind_uparams Dq)).
  Hypothesis (HlIs : List.length (IsS k) = List.length (ind_uparams Dq)).
  Hypotheses (Hav : tele_ass (im_nparams Mv)) (Hai : tele_ass (im_nparams Mi')) (Hnn : im_nn Mv = im_nn Mi').
  (** The [Self] environment. *)
  Variables (ups svals cups : list domain) (RS : relation env).
  Hypotheses (Hsv : List.length svals = ind_ndecl D) (HWS : ⊨ grp_sctx D).
  Hypotheses (HRS : EF grp_sctx D ≈ grp_sctx D ∈ per_ctx_env ↘ RS)
             (HρS : RS (env_args (env_args nil ups) svals) (env_args (env_args nil ups) svals)).
  Hypotheses (Hcups : ⟦ IsS k ⟧* gc_deps ⍮ gc_stack ⍮ env_args (env_args nil ups) svals ↘ cups)
             (Hlcups : List.length cups = ind_nu Dq).

  #[local] Abbreviation ρS := (env_args (env_args nil ups) svals).

  (** The group's substitution: past the members. *)
  Lemma self_wk_rel : grp_sctx D ⊨ˢ sb_of_wk (self_wk D 0) ≈ sb_of_wk (self_wk D 0) : ind_uparams D.
  Proof.
    pose proof (vid_uparams _ HvD) as HU.
    destruct (rel_ctx_wf_per_ctx_env HU) as [RU HRU].
    apply rel_sub_of_wk; unfold self_wk; cbn [wk_qn].
    apply (rel_wk_under_ctx_intro HRS HRU).
    rewrite <- Hsl; exact (rel_wk_shiftn (grp_selfs D) (ind_uparams D) RS RU HRS HRU).
  Qed.

  Lemma self_wk_eval : ⟦ sb_of_wk (self_wk D 0) ⟧s ρS ↘ env_args nil ups.
  Proof.
    unfold self_wk; cbn [wk_qn].
    replace (env_args nil ups) with (⟪wk_shiftn (ind_ndecl D)⟫ ρS) at 2
      by (rewrite <- Hsv; apply eval_wk_shiftn_args).
    exact (eval_sub_of_wk (wk_shiftn (ind_ndecl D)) ρS (Hφ := WkMono_shiftn _)).
  Qed.

  (** The container's substitution: the view's arguments. *)
  Lemma view_args_rel : grp_sctx D ⊨ˢ sb_of_list Id (IsS k) ≈ sb_of_list Id (IsS k) : ind_uparams Dq ++ grp_sctx D.
  Proof.
    apply gsub_valid, gsub_of_list; [ constructor; exact HWS | exact HaQ
                                    | exact (proj1 (closed_app_sem _ _ HaQ (vid_uparams _ HvDq) HWS)) | exact HlIs |].
    intros j N T HN HT; exact (vsv_is _ _ Hvsv _ _ _ _ _ _ _ _ _ _ HMk Hh HDq HN HT).
  Qed.

  Lemma view_args_eval : ⟦ sb_of_list Id (IsS k) ⟧s ρS ↘ env_args ρS cups.
  Proof. apply eval_sb_of_list; [ apply eval_sub_id | exact Hcups ]. Qed.

  (** The view's arguments over [ρS] and over the empty environment are
      related at the container's uniform parameters. *)
  Lemma view_args_base : forall RQ, EF ind_uparams Dq ≈ ind_uparams Dq ∈ per_ctx_env ↘ RQ ->
      RQ (env_args nil cups) (env_args ρS cups).
  Proof.
    intros RQ HRQ.
    pose proof (vid_uparams _ HvDq) as HWQ.
    destruct (rel_sub_under_ctx_simple view_args_rel) as (RΓ0 & HRΓ0 & RΔ0 & HRΔ0 & Hs).
    assert (E : RΓ0 <~> RS) by (eapply per_ctx_env_right_irrel; eassumption).
    destruct (Hs _ _ (proj2 (E _ _) HρS)) as (y1 & y2 & Ey1 & Ey2 & Hy).
    assert (E1 : env_eq y1 (env_args ρS cups)) by (eapply functional_eval_sub; [ exact Ey1 | exact view_args_eval ]).
    assert (E2 : env_eq y2 (env_args ρS cups)) by (eapply functional_eval_sub; [ exact Ey2 | exact view_args_eval ]).
    pose proof (per_ctx_env_resp_env_eq HRΔ0 _ _ _ _ E1 E2 Hy) as HE.
    pose proof (proj2 (closed_app_sem _ _ HaQ HWQ HWS) RQ RΔ0 HRQ HRΔ0 _ _ HE) as HEQ.
    assert (HaQ' : tele_ass (List.rev (ind_uparams Dq))) by (apply List.Forall_rev; exact HaQ).
    assert (HWQ' : ⊨ List.rev (List.rev (ind_uparams Dq)) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HWQ).
    assert (HRQ' : EF List.rev (List.rev (ind_uparams Dq)) ++ ⋅ ≈ List.rev (List.rev (ind_uparams Dq)) ++ ⋅ ∈ per_ctx_env ↘ RQ)
      by (rewrite List.rev_involutive, List.app_nil_r; exact HRQ).
    assert (Hl : List.length cups = List.length (List.rev (ind_uparams Dq))) by (rewrite List.length_rev; exact Hlcups).
    destruct (rel_gargs _ _ _ _ per_ctx_env_nil_true HWQ' HaQ' HRQ' ρS ρS cups cups Hl Hl HEQ) as [_ Hg].
    pose proof (per_gargs_base _ _ _ per_ctx_env_nil_true HWQ' HaQ' ρS ρS nil ρS cups cups I I I Hg) as Hg'.
    assert (HWQ0 : ⊨ ind_uparams Dq ++ ⋅) by (rewrite List.app_nil_r; exact HWQ).
    assert (HRQ0 : EF ind_uparams Dq ++ ⋅ ≈ ind_uparams Dq ++ ⋅ ∈ per_ctx_env ↘ RQ) by (rewrite List.app_nil_r; exact HRQ).
    exact (gargs_env_rel_gen _ _ _ _ _ _ _ _ per_ctx_env_nil_true HRQ0 HWQ0 I Hlcups Hg').
  Qed.

  (** The field [vco_N] of [view_coh_ok] at the canonical relations of the
      group at [ups] and of the container at [cups]. *)
  Theorem view_nparams_canon : forall j vs vs', j < im_nn Mi' ->
      tele_prefix_rel (canon_nparams_rel Dq cups i') j vs vs' ->
      (canon_nparams_rel Dq cups i' j vs <~> canon_nparams_rel D ups v j vs).
  Proof.
    intros j vs vs' Hj Hp.
    pose proof (vid_uparams _ HvDq) as HWQu.
    assert (Hac : tele_ass (List.rev (im_nparams Mi'))) by (apply List.Forall_rev; exact Hai).
    assert (Hag : tele_ass (List.rev (im_nparams Mv))) by (apply List.Forall_rev; exact Hav).
    assert (Hlen : List.length (List.rev (im_nparams Mv)) = List.length (List.rev (im_nparams Mi')))
      by (rewrite !List.length_rev; exact Hnn).
    assert (Hjc : j < List.length (List.rev (im_nparams Mi'))) by (rewrite List.length_rev; exact Hj).
    destruct (List.nth_error (List.rev (im_nparams Mi')) j) as [ec |] eqn:HC; [| apply List.nth_error_None in HC; lia ].
    destruct (proj1 (List.Forall_forall _ _) Hac ec (List.nth_error_In _ _ HC)) as [C ->].
    destruct (List.nth_error (List.rev (im_nparams Mv)) j) as [eg |] eqn:HG; [| apply List.nth_error_None in HG; lia ].
    destruct (proj1 (List.Forall_forall _ _) Hag eg (List.nth_error_In _ _ HG)) as [G ->].
    assert (HWQ : ⊨ List.rev (List.rev (im_nparams Mi')) ++ ind_uparams Dq)
      by (rewrite List.rev_involutive; exact (vid_params _ HvDq _ _ HMi')).
    assert (HTQ : forall j0 A, List.nth_error (List.rev (im_nparams Mi')) j0 = Some (ce_ass A) ->
               exists i : nat, List.rev (List.firstn j0 (List.rev (im_nparams Mi'))) ++ ind_uparams Dq ⊨ A : Typeω@i)
      by (intros j0 A HA; exact (proj2 (vid_npar _ HvDq _ _ _ _ HMi' HA))).
    destruct (rel_ctx_wf_per_ctx_env HWQu) as [RQ HRQ].
    pose proof (view_args_base RQ HRQ) as HBQ.
    assert (HPQ : PER RQ) by (eapply per_env_PER; exact HRQ).
    assert (H11 : RQ (env_args nil cups) (env_args nil cups)) by (etransitivity; [ exact HBQ | symmetry; exact HBQ ]).
    (** The arguments, at the container's telescope over the empty base,
        then over [ρS]. *)
    assert (Htr : forall k0 pre x y, canon_nparams_rel Dq cups i' k0 pre x y ->
                per_head (nth_ctyp (List.rev (im_nparams Mi')) k0) (nth_ctyp (List.rev (im_nparams Mi')) k0)
                  (env_args (env_args nil cups) pre) (env_args (env_args nil cups) pre) x y).
    { intros * H; unfold canon_nparams_rel, member_nparams in H; rewrite HMi', env_args_app in H; exact H. }
    pose proof (canon_prefix_gargs _ _ _ _ Hac HWQ HTQ HRQ H11 _ Htr j ltac:(lia) vs vs' Hp) as Hg1.
    assert (Hl : List.length vs = j) by (destruct Hp as [Hl _]; exact Hl).
    destruct (tele_base_change _ _ _ _ _ Hac HWQ HTQ HRQ HBQ j vs Hl ltac:(lia) Hg1) as [Hg2 Hbc].
    (** The two telescopes over [grp_sctx D]. *)
    assert (HWg : ⊨ List.rev (List.rev (im_nparams Mv)) ++ ind_uparams D)
      by (rewrite List.rev_involutive; exact (vid_params _ HvD _ _ HMv)).
    assert (HaP : tele_ass (im_params Dq Mi')) by (apply List.Forall_app; split; assumption).
    assert (HWc : ⊨ List.rev (List.rev (im_nparams Mi')) ++ ind_uparams Dq ++ grp_sctx D).
    { rewrite List.rev_involutive, List.app_assoc.
      exact (proj1 (closed_app_sem _ _ HaP (vid_params _ HvDq _ _ HMi') HWS)). }
    assert (HTg : forall j0 A, List.nth_error (List.rev (im_nparams Mv)) j0 = Some (ce_ass A) ->
               exists i : nat, List.rev (List.firstn j0 (List.rev (im_nparams Mv))) ++ ind_uparams D ⊨ A : Typeω@i)
      by (intros j0 A HA; exact (proj2 (vid_npar _ HvD _ _ _ _ HMv HA))).
    assert (HTc : forall j0 A, List.nth_error (List.rev (im_nparams Mi')) j0 = Some (ce_ass A) ->
               exists i : nat, List.rev (List.firstn j0 (List.rev (im_nparams Mi'))) ++ ind_uparams Dq ++ grp_sctx D ⊨ A : Typeω@i).
    { intros j0 A HA; destruct (HTQ _ _ HA) as [i HAi]; exists i.
      rewrite List.app_assoc.
      assert (Ha0 : tele_ass (List.rev (List.firstn j0 (List.rev (im_nparams Mi'))) ++ ind_uparams Dq))
        by (apply List.Forall_app; split; [ apply tele_ass_firstn; exact Hac | exact HaQ ]).
      pose proof (rel_ctx_wf_firstn _ _ j0 HWQ) as HW0.
      destruct (closed_app_sem _ _ Ha0 HW0 HWS) as [HW0S Hres].
      destruct (rel_ctx_wf_per_ctx_env HW0) as [R0 HR0]; destruct (rel_ctx_wf_per_ctx_env HW0S) as [R0S HR0S].
      exact (rel_exp_under_ctx_restrict HR0S HR0 (Hres _ _ HR0 HR0S) HAi). }
    assert (Heq : grp_sctx D ⊨ˣ tele_sub (List.rev (List.rev (im_nparams Mv))) (sb_of_wk (self_wk D 0))
                    ≈ tele_sub (List.rev (List.rev (im_nparams Mi'))) (sb_of_list Id (IsS k))).
    { rewrite !List.rev_involutive, tele_sub_of_wk.
      exact (vsv_nparams _ _ Hvsv _ _ _ _ _ _ _ _ _ _ _ HMk Hh HDq HMi' Hv HMv). }
    pose proof (tele_link _ _ _ HRS HρS _ _ _ _ _ _ self_wk_rel view_args_rel self_wk_eval view_args_eval
                  _ _ Hag Hac Hlen HWg HWc HTg HTc Heq j vs G C Hl HG HC Hg2) as Hlink.
    (** The canonical relations are these head PERs. *)
    unfold canon_nparams_rel, member_nparams; rewrite HMi', HMv, !env_args_app.
    unfold nth_ctyp; rewrite HC, HG.
    etransitivity; [ exact (Hbc _ HC) | exact Hlink ].
  Qed.
End ViewNparams.

End Fixed_GCtx.
