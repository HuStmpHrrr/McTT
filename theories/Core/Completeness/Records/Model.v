(** * Record Types: the Canonical Model and the Type Former

    A record whose declaration is valid in the PER model (its parameters a
    context, its sort a universe over them, each field a type of the sort
    over the fields before it) is, at related parameters, a type of the
    universe its sort denotes, with the canonical relations of
    [Core.Semantic.RecordPER] ([record_relate]).  Its type former is then an
    element of its [Π]-type ([valid_exp_under_ctx_record]).

    The validity of the declaration is the hypotheses of [RecordModel]; a
    valid global context provides them for every record it files.  The
    first section states, for any closed telescope and any sort over it,
    what [Inductives/Model.v] states for the uniform parameters and the
    sort of a group. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases VariableCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases LevelCases PropCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance Telescope.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Inductives Require Import Decl Model.
From Mctt.Core.Semantic Require Import Realizability RecordPER Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** A Telescope at a Sort

    A closed telescope [C] and a universe [S] over it.  A type over [C],
    and a context [Pre] over it, of [S] shifted past [Pre], evaluates at
    related arguments to types of the universe [S] denotes at the
    arguments of [C]. *)
Section SortTele.
  Variables (C : ctx) (S : typ).
  Hypothesis (HCv : ⊨ C) (HCa : tele_ass C) (Hsu : ind_sort_univ S) (HS : exists i : nat, C ⊨ S : Typeω@i).

  Lemma sort_tele_univ : forall ρ b, ⟦ S ⟧ ρ ↘ b -> is_univ b.
  Proof.
    intros * Hb; destruct Hsu as [[i Heq] | [t Heq]]; rewrite Heq in Hb; inversion Hb; subst; unfold is_univ; eauto.
  Qed.

  Lemma sort_tele_wk_univ : forall φ ρ b, ⟦ S[φ]ʷ ⟧ ρ ↘ b -> is_univ b.
  Proof.
    intros * Hb; destruct Hsu as [[i Heq] | [t Heq]]; rewrite Heq in Hb; cbn in Hb; inversion Hb; subst;
      unfold is_univ; eauto.
  Qed.

  Lemma sort_tele_rel : forall Pre T, ⊨ Pre ++ C ->
      Pre ++ C ⊨ T : S[wk_shiftn (List.length Pre)]ʷ ->
      forall ns ns' zs zs', List.length zs = List.length Pre -> List.length zs' = List.length Pre ->
        List.length ns = List.length C -> List.length ns' = List.length C ->
        per_gargs (List.rev (Pre ++ C)) nil nil (ns ++ zs) (ns' ++ zs') ->
        forall a, ⟦ S ⟧ env_args nil ns ↘ a ->
        exists t t', ⟦ T ⟧ env_args nil (ns ++ zs) ↘ t /\ ⟦ T ⟧ env_args nil (ns' ++ zs') ↘ t' /\
          Dom t ≈ t' ∈ per_univ (univ_idx a).
  Proof.
    intros * HC HT * Hz Hz' Hu Hu' Hg a Ha.
    destruct (rel_ctx_wf_per_ctx_env HC) as [R HR].
    assert (HRe : R (env_args nil (ns ++ zs)) (env_args nil (ns' ++ zs'))).
    { apply (gargs_env_rel _ _ _ _ _ _ HR HC); [ rewrite !List.length_app; lia | exact Hg ]. }
    assert (HPR : PER R) by (eapply per_env_PER; exact HR).
    assert (HRee : R (env_args nil (ns ++ zs)) (env_args nil (ns ++ zs)))
      by (etransitivity; [ exact HRe | symmetry; exact HRe ]).
    destruct (rel_exp_under_ctx_simple_full_at HR HT) as [i0 Hsimp].
    destruct (Hsimp _ _ HRe) as (b & b' & R0 & Eb & Eb' & HR0 & Htt).
    (** The type is of a universe, so the terms are related. *)
    destruct Htt as [Hp | (t & t' & Et & Et' & Htt)];
      [ destruct (sort_tele_wk_univ _ _ _ Eb) as [[? ->] | [? ->]]; discriminate |].
    destruct (per_univ_elem_univ _ _ _ _ HR0 (sort_tele_wk_univ _ _ _ Eb)) as [_ ER0].
    destruct HS as [i HSi].
    destruct (rel_exp_under_ctx_wk_simple (rel_wk_under_ctx_shiftn _ _ HC) HSi) as (RΓ & HΓ & j & Hwk).
    assert (E : R <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    destruct (Hwk _ _ (proj1 (E _ _) HRee)) as (x & x' & Rx & Ex & Ex' & HRx & Hmm).
    destruct Hmm as [Hp | (m & m' & Em & Em' & Hmm)]; [ cbn in Ex; inversion Ex; subst; discriminate |].
    rewrite env_args_app, <- Hz, eval_wk_shiftn_args in Em'.
    assert (m' = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (m = b) as -> by (eapply functional_eval_exp; eassumption).
    cbn in Ex; inversion Ex; subst.
    basic_invert_per_univ_elem HRx.
    match goal with Hm : ?r b a, H : ?r <~> _ |- _ => apply H in Hm; destruct Hm as [[Rm HRm] _ _] end.
    destruct (per_univ_elem_univ _ _ _ _ HRm (sort_tele_wk_univ _ _ _ Eb)) as [Hidx _].
    exists t, t'; split; [ exact Et | split; [ exact Et' |] ].
    rewrite Hidx; apply ER0; exact Htt.
  Qed.

  (** The same at either sort: a proposition evaluates to related
      propositions, related at every universe. *)
  Lemma sort_rel_tele_rel : forall r Pre T, ⊨ Pre ++ C ->
      Pre ++ C ⊨ T : relevance_sort r S[wk_shiftn (List.length Pre)]ʷ ->
      forall ns ns' zs zs', List.length zs = List.length Pre -> List.length zs' = List.length Pre ->
        List.length ns = List.length C -> List.length ns' = List.length C ->
        per_gargs (List.rev (Pre ++ C)) nil nil (ns ++ zs) (ns' ++ zs') ->
        forall a, ⟦ S ⟧ env_args nil ns ↘ a ->
        exists t t', ⟦ T ⟧ env_args nil (ns ++ zs) ↘ t /\ ⟦ T ⟧ env_args nil (ns' ++ zs') ↘ t' /\
          Dom t ≈ t' ∈ per_univ (univ_idx a).
  Proof.
    intros [] * HC HT * Hz Hz' Hu Hu' Hg a Ha; [ exact (sort_tele_rel _ _ HC HT _ _ _ _ Hz Hz' Hu Hu' Hg a Ha) |].
    destruct (rel_ctx_wf_per_ctx_env HC) as [R HR].
    assert (HRe : R (env_args nil (ns ++ zs)) (env_args nil (ns' ++ zs'))).
    { apply (gargs_env_rel _ _ _ _ _ _ HR HC); [ rewrite !List.length_app; lia | exact Hg ]. }
    destruct (rel_exp_of_prop_inversion_simple_at HR HT _ _ HRe) as (t & t' & Et & Et' & Hp).
    exists t, t'; split; [ exact Et | split; [ exact Et' |] ].
    exists per_proof; apply per_univ_elem_of_prop; exact Hp.
  Qed.

  (** Arguments related at a telescope of types at the sort or
      propositions, by the canonical relations, are arguments related at
      it. *)
  Lemma sort_tele_canon_gargs : forall (ts : list centry) (Pre0 : ctx) (tr : nat -> list domain -> relation domain)
      ns ns' zs zs' a,
      tele_ass ts ->
      List.length ns = List.length C -> List.length ns' = List.length C ->
      List.length zs = List.length Pre0 -> List.length zs' = List.length Pre0 ->
      per_gargs (List.rev (Pre0 ++ C)) nil nil (ns ++ zs) (ns' ++ zs') ->
      ⟦ S ⟧ env_args nil ns ↘ a ->
      (forall j A, List.nth_error ts j = Some (ce_ass A) ->
         ⊨ List.rev (List.firstn j ts) ++ Pre0 ++ C /\
         exists r, List.rev (List.firstn j ts) ++ Pre0 ++ C ⊨ A : relevance_sort r S[wk_shiftn (j + List.length Pre0)]ʷ) ->
      (forall j A pre, List.nth_error ts j = Some (ce_ass A) ->
         (tr j pre <~> per_head A A (env_args nil (ns ++ zs ++ pre)) (env_args nil (ns ++ zs ++ pre)))) ->
      forall k vs vs', k <= List.length ts -> tele_prefix_rel tr k vs vs' ->
        per_gargs (List.firstn k ts) (env_args nil (ns ++ zs)) (env_args nil (ns' ++ zs')) vs vs'.
  Proof.
    intros * Hts Hu Hu' Hz Hz' Hg Ha Hv Htr k.
    induction k as [| k IH]; intros vs vs' Hk Hp.
    - rewrite tele_prefix_rel_iff in Hp; destruct Hp as (Hl & Hl' & _).
      destruct vs, vs'; cbn in *; try discriminate; constructor.
    - pose proof Hp as Hp0; rewrite tele_prefix_rel_iff in Hp0; destruct Hp0 as (Hl & Hl' & Hr).
      destruct (nth_error_lt_some' ts k ltac:(lia)) as [e He].
      assert (HA : exists A, e = ce_ass A)
        by (unfold tele_ass in Hts; rewrite List.Forall_forall in Hts; apply Hts; eapply List.nth_error_In; exact He).
      destruct HA as [A ->].
      destruct (nth_error_lt_some' vs k ltac:(lia)) as [v Hv0].
      destruct (nth_error_lt_some' vs' k ltac:(lia)) as [v' Hv0'].
      rewrite (firstn_S_snoc _ _ _ He).
      assert (Hvs : vs = List.firstn k vs ++ v :: nil)
        by (rewrite <- (firstn_S_snoc _ _ _ Hv0), List.firstn_all2 by lia; reflexivity).
      assert (Hvs' : vs' = List.firstn k vs' ++ v' :: nil)
        by (rewrite <- (firstn_S_snoc _ _ _ Hv0'), List.firstn_all2 by lia; reflexivity).
      pose proof (IH _ _ ltac:(lia) (tele_prefix_rel_of_pre _ _ _ _ k Hp ltac:(lia))) as IHk.
      rewrite Hvs, Hvs'.
      destruct (Hv _ _ He) as [HC [r HT]].
      assert (Hlf : List.length (List.firstn k ts) = k) by (rewrite List.length_firstn; lia).
      assert (Hlv : List.length (List.firstn k vs) = k) by (rewrite List.length_firstn; lia).
      assert (Hlv' : List.length (List.firstn k vs') = k) by (rewrite List.length_firstn; lia).
      assert (Hg' : per_gargs (List.rev (List.rev (List.firstn k ts) ++ Pre0 ++ C)) nil nil
                      (ns ++ zs ++ List.firstn k vs) (ns' ++ zs' ++ List.firstn k vs')).
      { rewrite List.rev_app_distr, List.rev_involutive, !List.app_assoc.
        apply per_gargs_app_intro; [ rewrite List.length_app, List.length_rev, List.length_app; lia | exact Hg |].
        exact IHk. }
      set (Pre := List.rev (List.firstn k ts) ++ Pre0).
      assert (HC' : ⊨ Pre ++ C) by (unfold Pre; rewrite <- List.app_assoc; exact HC).
      assert (HT' : Pre ++ C ⊨ A : relevance_sort r S[wk_shiftn (List.length Pre)]ʷ)
        by (unfold Pre; rewrite <- List.app_assoc, List.length_app, List.length_rev, Hlf; exact HT).
      assert (Hg'' : per_gargs (List.rev (Pre ++ C)) nil nil
                       (ns ++ (zs ++ List.firstn k vs)) (ns' ++ (zs' ++ List.firstn k vs')))
        by (unfold Pre; rewrite <- List.app_assoc; exact Hg').
      destruct (sort_rel_tele_rel r Pre A HC' HT' ns ns' (zs ++ List.firstn k vs) (zs' ++ List.firstn k vs')
                  ltac:(unfold Pre; rewrite !List.length_app, List.length_rev; lia)
                  ltac:(unfold Pre; rewrite !List.length_app, List.length_rev; lia)
                  Hu Hu' Hg'' a Ha)
        as (t & t' & Et & Et' & [R0 HR0]).
      destruct (per_univ_elem_to_nat _ _ _ _ HR0) as [n Hn].
      apply (per_gargs_snoc _ _ _ _ _ _ _ _ n R0); [ lia | exact IHk | |].
      + rewrite <- !env_args_app, <- !List.app_assoc; exact (mk_rel_mod_eval t t' Et Et' Hn).
      + pose proof (Hr _ _ _ Hv0 Hv0') as Hrv.
        apply (Htr _ _ _ He) in Hrv.
        assert (HRtt : DF t ≈ t ∈ per_univ_elem n ↘ R0)
          by (eapply per_univ_trans; [ exact Hn | apply per_univ_sym; exact Hn ]).
        exact (Hrv _ _ _ _ Et Et HRtt).
  Qed.

  Lemma rev_tele_sem : ⊨ List.rev (List.rev C) ++ ⋅.
  Proof. rewrite List.rev_involutive, List.app_nil_r; exact HCv. Qed.

  Lemma rev_tele_ass : tele_ass (List.rev C).
  Proof. apply List.Forall_rev, HCa. Qed.

  Lemma tele_gargs_refl_l : forall ns ns', per_gargs (List.rev C) nil nil ns ns' -> per_gargs (List.rev C) nil nil ns ns.
  Proof.
    intros * Hg; eapply (per_gargs_refl_l _ _ _ per_ctx_env_nil_true rev_tele_sem); [ exact rev_tele_ass | exact I | exact Hg ].
  Qed.

  Lemma length_tele_gargs : forall ns ns', per_gargs (List.rev C) nil nil ns ns' ->
      List.length ns = List.length C -> List.length ns' = List.length C.
  Proof. intros * Hg Hu; destruct (per_gargs_length _ _ _ _ _ Hg) as [Hl _]; lia. Qed.

  (** The sort at arguments related to themselves has a value. *)
  Lemma sort_tele_value : forall ns, per_gargs (List.rev C) nil nil ns ns -> List.length ns = List.length C ->
      exists a, ⟦ S ⟧ env_args nil ns ↘ a.
  Proof.
    intros ns Hg Hu.
    destruct HS as [i HSi].
    destruct (rel_ctx_wf_per_ctx_env HCv) as [RU HRU].
    assert (HRU0 : RU (env_args nil ns) (env_args nil ns))
      by (apply (gargs_env_rel _ _ _ _ _ _ HRU HCv); [ exact Hu | exact Hg ]).
    destruct (rel_exp_of_typ_inversion_simple_at HRU HSi _ _ HRU0) as (a & _ & Ea & _ & _); eauto.
  Qed.
End SortTele.

(** ** Lists Related as a Telescope, Position by Position

    Each position related at the left prefix, given the prefixes before it
    related. *)
Lemma tele_rel_build : forall {X} tr (T : list X) A B,
    List.length A = List.length T -> List.length B = List.length T ->
    (forall k x y, List.nth_error A k = Some x -> List.nth_error B k = Some y ->
       tele_prefix_rel tr k (List.firstn k A) (List.firstn k B) -> tr k (List.firstn k A) x y) ->
    tele_rel tr T A B.
Proof.
  intros * HA HB H.
  assert (Hall : forall k, k <= List.length T -> tele_prefix_rel tr k (List.firstn k A) (List.firstn k B)).
  { induction k as [| k IH]; intros Hk; [ apply tele_prefix_rel_nil |].
    destruct (nth_error_lt_some' A k ltac:(lia)) as [x Hx].
    destruct (nth_error_lt_some' B k ltac:(lia)) as [y Hy].
    rewrite (firstn_S_snoc _ _ _ Hx), (firstn_S_snoc _ _ _ Hy).
    apply tele_prefix_rel_snoc; [ apply IH; lia | apply H; [ exact Hx | exact Hy | apply IH; lia ] ]. }
  apply tele_rel_of_pre; pose proof (Hall _ (le_n _)) as Hp.
  rewrite !List.firstn_all2 in Hp by lia; exact Hp.
Qed.

Lemma eval_exps_firstn : forall Ms ρ vs k, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ vs ->
    ⟦ List.firstn k Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ List.firstn k vs.
Proof.
  intros * H; revert k; induction H; intros [| k]; cbn; try solve [ constructor ]; econstructor; eauto.
Qed.

(** ** Values of Fields by Their Sorts *)

(** The sort a list of sorts gives a field past its head: the rest's. *)
Lemma nth_tl_relevance : forall (rs : list relevance) k, List.nth k (List.tl rs) relevant = List.nth (S k) rs relevant.
Proof. intros [| r rs] k; [ destruct k | ]; reflexivity. Qed.

(** The fields have values when the relevant ones do. *)
Lemma eval_field_vals_each : forall Ms rs ρ,
    (forall k M, List.nth_error Ms k = Some M -> List.nth k rs relevant = relevant -> exists m, ⟦ M ⟧ ρ ↘ m) ->
    exists vs, eval_field_vals gc_deps gc_stack rs Ms ρ vs.
Proof.
  induction Ms as [| M Ms IH]; intros rs ρ H; [ exists nil; constructor |].
  destruct (IH (List.tl rs) ρ) as [vs Hvs].
  { intros k N HN Hr; apply (H (S k) N HN); rewrite <- nth_tl_relevance; exact Hr. }
  destruct (List.hd relevant rs) eqn:Er.
  - destruct (H 0 M eq_refl ltac:(destruct rs; cbn in *; [ reflexivity | exact Er ])) as [m Hm].
    exists (m :: vs); eapply eval_field_vals_relevant; eassumption.
  - exists (⋆ᵈ :: vs); eapply eval_field_vals_proof; eassumption.
Qed.

(** A field's value: the term's at a relevant field, the proof at a
    propositional one. *)
Lemma eval_field_vals_nth : forall rs Ms ρ vs, eval_field_vals gc_deps gc_stack rs Ms ρ vs ->
    forall k M, List.nth_error Ms k = Some M ->
      exists v, List.nth_error vs k = Some v /\
        (List.nth k rs relevant = relevant -> ⟦ M ⟧ ρ ↘ v) /\ (List.nth k rs relevant = propositional -> v = ⋆ᵈ).
Proof.
  induction 1 as [rs ρ | rs M ρ m Ms ms Hr Hm Hms IH | rs M ρ Ms ms Hr Hms IH]; intros [| k] N HN; cbn in HN; try discriminate.
  - injection HN as <-; exists m; split; [ reflexivity |].
    split; [ intros _; exact Hm | intros Hp; destruct rs; cbn in *; congruence ].
  - destruct (IH k N HN) as (v & Hv & Hv1 & Hv2); exists v; split; [ exact Hv |].
    rewrite <- !nth_tl_relevance; split; assumption.
  - injection HN as <-; exists ⋆ᵈ; split; [ reflexivity |].
    split; [ intros Hp; destruct rs; cbn in *; congruence | intros _; reflexivity ].
  - destruct (IH k N HN) as (v & Hv & Hv1 & Hv2); exists v; split; [ exact Hv |].
    rewrite <- !nth_tl_relevance; split; assumption.
Qed.

(** And conversely: values of the fields' sorts pointwise are their
    values. *)
Lemma eval_field_vals_of_nth : forall Ms rs ρ vs, List.length vs = List.length Ms ->
    (forall k M v, List.nth_error Ms k = Some M -> List.nth_error vs k = Some v ->
       (List.nth k rs relevant = relevant -> ⟦ M ⟧ ρ ↘ v) /\ (List.nth k rs relevant = propositional -> v = ⋆ᵈ)) ->
    eval_field_vals gc_deps gc_stack rs Ms ρ vs.
Proof.
  induction Ms as [| M Ms IH]; intros rs ρ [| v vs] Hl H; cbn in Hl; try discriminate; [ constructor |].
  assert (Hrest : eval_field_vals gc_deps gc_stack (List.tl rs) Ms ρ vs).
  { apply IH; [ lia |]; intros k N w HN Hw; rewrite !nth_tl_relevance; exact (H (S k) N w HN Hw). }
  destruct (H 0 M v eq_refl eq_refl) as [Hr Hp].
  destruct (List.hd relevant rs) eqn:Er.
  - eapply eval_field_vals_relevant; [ exact Er | apply Hr; destruct rs; cbn in *; [ reflexivity | exact Er ] | exact Hrest ].
  - rewrite (Hp ltac:(destruct rs; cbn in *; [ discriminate | exact Er ])).
    eapply eval_field_vals_proof; [ exact Er | exact Hrest ].
Qed.

Lemma eval_field_vals_length : forall rs Ms ρ vs, eval_field_vals gc_deps gc_stack rs Ms ρ vs -> List.length vs = List.length Ms.
Proof. induction 1; cbn; congruence. Qed.

(** The first fields' values are the values of the first fields. *)
Lemma eval_field_vals_firstn : forall rs Ms ρ vs, eval_field_vals gc_deps gc_stack rs Ms ρ vs ->
    forall k, eval_field_vals gc_deps gc_stack rs (List.firstn k Ms) ρ (List.firstn k vs).
Proof.
  induction 1 as [rs ρ | rs M ρ m Ms ms Hr Hm Hms IH | rs M ρ Ms ms Hr Hms IH]; intros [| k]; cbn; try solve [ constructor ].
  - eapply eval_field_vals_relevant; [ exact Hr | exact Hm | apply IH ].
  - eapply eval_field_vals_proof; [ exact Hr | apply IH ].
Qed.

(** A substitution extended by fields, at a context extended by entries
    [ts] whose sorts are the fields', evaluated: to the fields' values. *)
Lemma eval_sb_of_list_fields : forall Fs ts σ Δ ρ ρσ rs vs,
    ⟦ σ : Δ ⟧s ρ ↘ ρσ -> eval_field_vals gc_deps gc_stack rs Fs ρ vs -> List.length ts = List.length Fs ->
    (forall j e, List.nth_error ts j = Some e ->
       (List.nth j rs relevant = relevant ->
          ~ head_propositional gc_deps gc_stack e (List.rev (List.firstn j ts) ++ Δ) (env_args ρσ (List.firstn j vs))) /\
       (List.nth j rs relevant = propositional ->
          head_propositional gc_deps gc_stack e (List.rev (List.firstn j ts) ++ Δ) (env_args ρσ (List.firstn j vs)))) ->
    ⟦ sb_of_list σ Fs : List.rev ts ++ Δ ⟧s ρ ↘ env_args ρσ vs.
Proof.
  induction Fs as [| M Fs IH]; intros [| e ts] * Hσ Hvs Hl Hst; cbn [List.length] in Hl; try discriminate.
  - inversion Hvs; subst; exact Hσ.
  - cbn [sb_of_list List.rev]; rewrite <- List.app_assoc; cbn [List.app].
    destruct (Hst 0 e eq_refl) as [Hr0 Hp0]; cbn [List.firstn List.rev List.app env_args] in Hr0, Hp0.
    inversion Hvs; subst;
      match goal with Hms : eval_field_vals _ _ _ Fs ρ ?ms |- _ => rename Hms into Hms'; rename ms into ms' end;
      rename Hms' into Hms; rename ms' into ms.
    + match goal with Hm : ⟦ M ⟧ _ ⍮ _ ⍮ ρ ↘ ?m, Hhd : List.hd relevant rs = relevant |- _ =>
        rename Hm into Hm'; rename Hhd into Hhd'; rename m into m' end.
      rename Hm' into Hm; rename Hhd' into Hhd; rename m' into m.
      change (env_args ρσ (m :: ms)) with (env_args (ρσ ↦ m) ms).
      apply (IH ts (σ ,, M) (e :: Δ) ρ (ρσ ↦ m) (List.tl rs) ms); [ | exact Hms | lia |].
      * apply eval_sub_extend; [ exact Hσ | | exact Hm ].
        apply Hr0; destruct rs; cbn in *; [ reflexivity | exact Hhd ].
      * intros j e' He'; destruct (Hst (S j) e' He') as [Hr Hp].
        cbn [List.firstn List.rev] in Hr, Hp; rewrite <- List.app_assoc in Hr, Hp; cbn [List.app] in Hr, Hp.
        rewrite nth_tl_relevance; split; assumption.
    + match goal with Hhd : List.hd relevant rs = propositional |- _ => rename Hhd into Hhd' end.
      rename Hhd' into Hhd.
      change (env_args ρσ (⋆ᵈ :: ms)) with (env_args (ρσ ↦ ⋆ᵈ) ms).
      apply (IH ts (σ ,, M) (e :: Δ) ρ (ρσ ↦ ⋆ᵈ) (List.tl rs) ms); [ | exact Hms | lia |].
      * apply eval_sub_extend_proof; [ exact Hσ |].
        apply Hp0; destruct rs; cbn in *; [ discriminate | exact Hhd ].
      * intros j e' He'; destruct (Hst (S j) e' He') as [Hr Hp].
        cbn [List.firstn List.rev] in Hr, Hp; rewrite <- List.app_assoc in Hr, Hp; cbn [List.app] in Hr, Hp.
        rewrite nth_tl_relevance; split; assumption.
Qed.

(** A type related to a record type former at parameters is one. *)
Lemma per_univ_elem_record_right : forall i R x p ns, DF x ≈ d_record p ns ∈ per_univ_elem i ↘ R ->
    exists ns', x = d_record p ns'.
Proof. intros * H; basic_invert_per_univ_elem H; eauto. Qed.

Lemma per_univ_elem_record_left : forall i R y p ns, DF d_record p ns ≈ y ∈ per_univ_elem i ↘ R ->
    exists ns', y = d_record p ns'.
Proof. intros * H; basic_invert_per_univ_elem H; eauto. Qed.

(** The first field so named in a list of distinct names. *)
Lemma field_lookup_combine_nth : forall (ns : list String.string) (vs : list domain) k f v,
    List.NoDup ns -> List.length ns = List.length vs ->
    List.nth_error ns k = Some f -> List.nth_error vs k = Some v -> field_lookup (List.combine ns vs) f = Some v.
Proof.
  induction ns as [| g ns IH]; intros [| v0 vs] [| k] * Hnd Hl Hf Hv; cbn in *; try discriminate; try lia.
  - injection Hf as <-; injection Hv as <-; rewrite String.eqb_refl; reflexivity.
  - inversion Hnd as [| ? ? Hg Hnd']; subst.
    destruct (String.eqb_spec f g) as [-> | Hne].
    + exfalso; apply Hg; eapply List.nth_error_In; exact Hf.
    + exact (IH vs k f v Hnd' ltac:(lia) Hf Hv).
Qed.

(** ** The Fields as a Telescope *)

(** The types of the fields, outermost first. *)
Definition field_tele (R : record_decl) : list centry := List.map (fun fT => ce_ass (snd fT)) (record_fields R).

Lemma rev_record_fctx : forall R k, List.rev (record_fctx R k) = List.firstn k (field_tele R).
Proof. intros; unfold record_fctx, field_tele; rewrite List.rev_involutive, List.firstn_map; reflexivity. Qed.

Lemma field_tele_ass : forall R, tele_ass (field_tele R).
Proof. intros; unfold field_tele, tele_ass; apply List.Forall_map, List.Forall_forall; intros; eauto. Qed.

Lemma field_tele_nth : forall R j A, List.nth_error (field_tele R) j = Some (ce_ass A) ->
    exists f, List.nth_error (record_fields R) j = Some (f, A).
Proof.
  intros * H; unfold field_tele in H; rewrite List.nth_error_map in H.
  destruct (List.nth_error (record_fields R) j) as [[f T] |] eqn:Hj; cbn in H; [ injection H as -> | discriminate ].
  exists f; reflexivity.
Qed.

Lemma length_field_tele : forall R, List.length (field_tele R) = List.length (record_fields R).
Proof. intros; unfold field_tele; rewrite List.length_map; reflexivity. Qed.

(** ** A Valid Record

    The hypotheses are the judgments of the record's declaration, read in
    the PER model: the fields over the parameters are a context, the sort
    is a universe over the parameters, and each field is a type of the
    sort over the fields before it. *)
Section RecordModel.
  Variables (p : qname) (R : record_decl).
  Hypothesis (Hl : record_lookup gc_deps gc_stack p = Some R) (Hc : record_closed R)
    (Hass : tele_ass (record_params R)) (Hnd : List.NoDup (List.map fst (record_fields R)))
    (Hsu : ind_sort_univ (record_sort R))
    (HF : ⊨ record_fctx R (List.length (record_fields R)) ++ record_params R)
    (HS : exists i : nat, record_params R ⊨ record_sort R : Typeω@i)
    (HT : forall k f T, List.nth_error (record_fields R) k = Some (f, T) ->
       record_fctx R k ++ record_params R ⊨ T : relevance_sort (record_field_rel R k) (record_sort R)[wk_shiftn k]ʷ)
    (HPr : exists l, forall Δ1 T Δ2, record_params R = Δ1 ++ ce_ass T :: Δ2 -> Δ2 ⊨ T : Typeω@l).

  Lemma record_fctx_sem : forall k, k <= List.length (record_fields R) -> ⊨ record_fctx R k ++ record_params R.
  Proof.
    intros k Hk.
    assert (Hs : record_fctx R (List.length (record_fields R))
                 = List.rev (List.map (fun fT => ce_ass (snd fT)) (List.skipn k (record_fields R))) ++ record_fctx R k).
    { unfold record_fctx; rewrite List.firstn_all, <- (List.firstn_skipn k (record_fields R)) at 1.
      rewrite List.map_app, List.rev_app_distr; reflexivity. }
    pose proof HF as H; rewrite Hs, <- List.app_assoc in H; exact (rel_ctx_wf_app_r _ _ H).
  Qed.

  Lemma record_params_sem : ⊨ record_params R.
  Proof. pose proof (record_fctx_sem 0 ltac:(lia)) as H; exact H. Qed.

  (** The canonical relations of the fields at related parameters are
      those of their telescope. *)
  Lemma canon_fields_gargs : forall ns ns' a, per_gargs (List.rev (record_params R)) nil nil ns ns' ->
      List.length ns = List.length (record_params R) -> ⟦ record_sort R ⟧ env_args nil ns ↘ a ->
      forall k vs vs', k <= List.length (record_fields R) -> tele_prefix_rel (canon_fields_rel R ns) k vs vs' ->
        per_gargs (List.firstn k (field_tele R)) (env_args nil ns) (env_args nil ns') vs vs'.
  Proof.
    intros * Hg Hu Ha * Hk Hp.
    pose proof (length_tele_gargs (record_params R) _ _ Hg Hu) as Hu'.
    pose proof (sort_tele_canon_gargs (record_params R) (record_sort R) Hsu HS
                  (field_tele R) nil (canon_fields_rel R ns) ns ns' nil nil a
                  (field_tele_ass R) Hu Hu' eq_refl eq_refl ltac:(rewrite !List.app_nil_r; exact Hg) Ha) as Hcan.
    rewrite !List.app_nil_r in Hcan; apply Hcan; [ | | rewrite length_field_tele; exact Hk | exact Hp ].
    - intros j A HA; cbn [List.app List.length]; rewrite Nat.add_0_r.
      destruct (field_tele_nth _ _ _ HA) as [f Hj].
      assert (Hjl : j < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hj).
      rewrite <- rev_record_fctx, List.rev_involutive.
      split; [ apply record_fctx_sem; lia | exists (record_field_rel R j); exact (HT _ _ _ Hj) ].
    - intros j A pre HA; destruct (field_tele_nth _ _ _ HA) as [f Hj].
      unfold canon_fields_rel; rewrite (nth_ftyp_eq _ _ _ _ Hj); reflexivity.
  Qed.

  (** The fields' types at related parameters and canonically related
      prefixes are related, in the universe the sort denotes. *)
  Lemma record_fields_related : forall ns ns' a, per_gargs (List.rev (record_params R)) nil nil ns ns' ->
      List.length ns = List.length (record_params R) -> ⟦ record_sort R ⟧ env_args nil ns ↘ a ->
      fields_related (univ_idx a) R ns ns'.
  Proof.
    intros * Hg Hu Ha k f T vs vs' Hk Hp.
    pose proof (length_tele_gargs (record_params R) _ _ Hg Hu) as Hu'.
    assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hk).
    pose proof (canon_fields_gargs _ _ _ Hg Hu Ha k vs vs' ltac:(lia) Hp) as Hgv.
    pose proof Hp as Hp0; rewrite tele_prefix_rel_iff in Hp0; destruct Hp0 as (Hlv & Hlv' & _).
    assert (HLk : List.length (record_fctx R k) = k) by (apply length_record_fctx; lia).
    pose proof (HT _ _ _ Hk) as HTk; rewrite <- HLk in HTk at 3.
    destruct (sort_rel_tele_rel (record_params R) (record_sort R) Hsu HS _ (record_fctx R k) T (record_fctx_sem k ltac:(lia)) HTk
                ns ns' vs vs' ltac:(lia) ltac:(lia) Hu Hu' ltac:(rewrite List.rev_app_distr, rev_record_fctx;
                                                              apply per_gargs_app_intro;
                                                              [ rewrite List.length_rev; exact Hu | exact Hg | exact Hgv ]) a Ha)
      as (t & t' & Et & Et' & Htt).
    exists t, t'; split; [ exact Et | split; [ exact Et' | exact Htt ] ].
  Qed.

  (** ** The Canonical Model

      The record at related parameters is a type of the universe its sort
      denotes, its elements those of the canonical record relation. *)
  Lemma record_relate : forall ns ns' a, per_gargs (List.rev (record_params R)) nil nil ns ns' ->
      List.length ns = List.length (record_params R) -> ⟦ record_sort R ⟧ env_args nil ns ↘ a ->
      DF d_record p ns ≈ d_record p ns' ∈ per_univ_elem (univ_idx a) ↘ record_rel R (canon_fields_rel R ns).
  Proof.
    intros * Hg Hu Ha.
    pose proof (length_tele_gargs (record_params R) _ _ Hg Hu) as Hu'.
    apply (per_univ_elem_record_canon (univ_idx a) p R ns ns' Hl Hnd Hu Hu');
      [ intros s; exact (per_gargs_top _ _ _ _ _ Hg ltac:(rewrite List.length_rev; exact Hu) s)
      | exact (record_fields_related _ _ _ Hg Hu Ha) |].
    (** The sorts: at related arguments of the fields' telescope, each
        field's type is of its sort. *)
    intros k f T vs vs' Hk Hp.
    assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hk).
    pose proof (canon_fields_gargs _ _ _ Hg Hu Ha k vs vs' ltac:(lia) Hp) as Hgv.
    pose proof Hp as Hp0; rewrite tele_prefix_rel_iff in Hp0; destruct Hp0 as (Hlv & _ & _).
    assert (HC : ⊨ record_fctx R k ++ record_params R) by (apply record_fctx_sem; lia).
    destruct (rel_ctx_wf_per_ctx_env HC) as [RC HRC].
    assert (HE : RC (env_args nil (ns ++ vs)) (env_args nil (ns' ++ vs'))).
    { apply (gargs_env_rel _ _ _ _ _ _ HRC HC); [ rewrite !List.length_app, length_record_fctx by lia; lia |].
      rewrite List.rev_app_distr, rev_record_fctx.
      apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hu | exact Hg | exact Hgv ]. }
    destruct (record_field_rel R k) eqn:Er.
    - assert (HTl : exists l : nat, record_fctx R k ++ record_params R ⊨ T : Typeω@l).
      { pose proof (HT _ _ _ Hk) as H; rewrite Er in H; cbn [relevance_sort] in H.
        destruct Hsu as [[i Heq] | [t Heq]]; rewrite Heq in H; cbn [exp_wk] in H;
          [ exists i; exact H | exists 0; eapply rel_exp_suniv_tm_large; exact H ]. }
      destruct HTl as [l HTl].
      destruct (rel_exp_of_typ_relevant_at HRC HTl _ _ HE) as (t & Et & Ht); exists t; split; assumption.
    - pose proof (HT _ _ _ Hk) as HTp; rewrite Er in HTp; cbn [relevance_sort] in HTp.
      destruct (rel_exp_of_prop_inversion_simple_at HRC HTp _ _ HE) as (t & _ & Et & _ & [Ht _ _]).
      exists t; split; assumption.
  Qed.

  (** The type former at related parameters, at the sort's universe. *)
  Lemma record_at_params : forall ρ ρ' ys ys', per_gargs (List.rev (record_params R)) ρ ρ' ys ys' ->
      List.length ys = List.length (record_params R) ->
      Dom d_record p ys ≈ d_record p ys' ∈ per_head (record_sort R) (record_sort R) (env_args ρ ys) (env_args ρ' ys').
  Proof.
    intros * Hg Hlen i0 R0 b b' Eb Eb' HR0.
    pose proof (per_gargs_base _ _ _ per_ctx_env_nil_true (rev_tele_sem _ record_params_sem) (rev_tele_ass _ Hass)
                  ρ ρ' nil nil _ _ I I I Hg) as Hg0.
    pose proof (tele_gargs_refl_l _ record_params_sem Hass _ _ Hg0) as Hgd.
    destruct (sort_tele_value _ _ record_params_sem HS _ Hgd Hlen) as [a Ea].
    destruct HS as [i HSi].
    destruct (rel_ctx_wf_per_ctx_env record_params_sem) as [RU HRU].
    assert (HRU0 : RU (env_args nil ys) (env_args nil ys))
      by (apply (gargs_env_rel _ _ _ _ _ _ HRU record_params_sem); [ exact Hlen | exact Hgd ]).
    assert (HRUρ : RU (env_args ρ ys) (env_args nil ys))
      by (exact (closed_env_base _ _ _ _ _ _ _ _ Hass record_params_sem HRU Hlen Hlen HRU0)).
    assert (Hub : is_univ b) by exact (sort_tele_univ (record_params R) _ Hsu HS _ _ Eb).
    destruct (per_univ_elem_univ _ _ _ _ HR0 Hub) as [_ ER0].
    pose proof (univ_idx_rel _ _ _ _ _ _ _ _ HRU HSi HRUρ Eb Ea Hub) as Hi.
    apply ER0; split; [| reflexivity | reflexivity ]; rewrite <- Hi.
    eexists; exact (record_relate _ _ _ Hg0 Hlen Ea).
  Qed.

  (** The application of the type former to its parameters. *)
  Lemma eval_app_record_args : forall xs x, List.length xs < List.length (record_params R) ->
      $| d_record p xs & x | gc_deps ⍮ gc_stack ↘ d_record p (xs ++ x :: nil).
  Proof. intros * Hx; eapply eval_app_record; eassumption. Qed.

  (** ** The Type Former *)
  Lemma valid_exp_under_ctx_record : ⋅ ⊨ a_record p : record_ty R.
  Proof.
    destruct HS as [i HSi].
    destruct (rel_exp_ctx_pi (record_params R) ⋅ (record_sort R) i Hass ltac:(rewrite List.app_nil_r; exact record_params_sem)
                ltac:(rewrite List.app_nil_r; exact HSi)) as [j HTy].
    destruct (rel_exp_of_typ_inversion_simple HTy) as (RT & HRT & Hsimp).
    apply (rel_exp_closed_intro _ _ j); [ intros; apply record_ty_sub, Hc | intros; reflexivity |].
    intros ρ ρ'.
    assert (Hρ : RT ρ ρ') by (inversion HRT; subst; match goal with H : _ <~> _ |- _ => apply H; exact I end).
    destruct (Hsimp ρ ρ' Hρ) as (a & a' & Ea & Ea' & [R0 HR0]).
    exists a, a', R0, (d_record p nil), (d_record p nil).
    split; [ exact Ea | split; [ exact Ea' | split; [ exact HR0 | split; [ constructor | split; [ constructor |] ] ] ] ].
    unfold record_ty in Ea, Ea'; rewrite <- (List.rev_involutive (record_params R)) in Ea, Ea'.
    (** The parameters are relevant. *)
    assert (Hrel : forall Δ1 T Δ2, record_params R = Δ1 ++ ce_ass T :: Δ2 -> exists i : nat, Δ2 ⊨ T : Typeω@i)
      by (destruct HPr as [l HPl]; intros * E; exists l; exact (HPl _ _ _ E)).
    eapply (ctx_pi_rel_elem (List.length (record_params R)) (d_record p) _ eval_app_record_args
              (fun _ _ => eq_refl) (List.rev (record_params R)) (rev_tele_ass _ Hass) ρ ρ' nil nil);
      [ rewrite List.length_rev; reflexivity | reflexivity
      | intros * Heq Hg Hlen Eb; cbn [List.app] in Eb;
        exact (closed_relevant_dom _ record_params_sem Hrel _ _ _ _ _ _ _ _ Heq Hg Hlen Eb)
      | exact Ea | exact Ea' | exact HR0 | ].
    intros ys ys' Hg Hlen; cbn [List.app]; apply record_at_params; [ exact Hg | rewrite Hlen, List.length_rev; reflexivity ].
  Qed.

  (** ** Evaluation of the Type Former at Parameters *)

  Lemma eval_apps_record : forall ys xs, List.length xs + List.length ys <= List.length (record_params R) ->
      $*| d_record p xs & ys | gc_deps ⍮ gc_stack ↘ d_record p (xs ++ ys).
  Proof.
    induction ys as [| y ys IH]; intros xs Hlen; [ rewrite List.app_nil_r; constructor |].
    econstructor; [ eapply eval_app_record; [ exact Hl | cbn in *; lia ] |].
    replace (xs ++ y :: ys) with ((xs ++ y :: nil) ++ ys) by (rewrite <- List.app_assoc; reflexivity).
    apply IH; rewrite List.length_app; cbn in *; lia.
  Qed.

  Lemma eval_record_apps : forall E Ns ns, ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ ns ->
      List.length Ns = List.length (record_params R) -> ⟦ apps_exp (a_record p) Ns ⟧ E ↘ d_record p ns.
  Proof.
    intros * Hns Hn; apply eval_apps_exp_record; exists ns.
    split; [ exact Hns |].
    apply (eval_apps_record ns nil); rewrite (eval_exps_length _ _ _ Hns); cbn; lia.
  Qed.

  (** The value of the type former at parameters: at their values. *)
  Lemma eval_record_apps_inv : forall E Ns a, ⟦ apps_exp (a_record p) Ns ⟧ E ↘ a ->
      List.length Ns = List.length (record_params R) ->
      exists ns, ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ ns /\ a = d_record p ns.
  Proof.
    intros * Ha Hn; apply eval_apps_exp_record in Ha as (ns & Ens & Hap).
    exists ns; split; [ exact Ens |].
    apply ((proj1 (proj2 (proj2 (proj2 (@functional_eval gc_deps gc_stack))))) _ _ _ Hap).
    apply (eval_apps_record ns nil); rewrite (eval_exps_length _ _ _ Ens); cbn; lia.
  Qed.

  (** ** The Fields' Types at Instances *)

  (** A relevant field's type is a type of a universe. *)
  Lemma field_typ_large : forall k f T, List.nth_error (record_fields R) k = Some (f, T) ->
      record_field_rel R k = relevant ->
      exists j : nat, record_fctx R k ++ record_params R ⊨ T : Typeω@j.
  Proof.
    intros * Hk Hr; pose proof (HT _ _ _ Hk) as H; rewrite Hr in H; cbn [relevance_sort] in H.
    destruct Hsu as [[i Heq] | [t Heq]]; rewrite Heq in H; cbn [exp_wk] in H;
      [ exists i; exact H | exists 0; eapply rel_exp_suniv_tm_large; exact H ].
  Qed.

  (** Any field's type is a type of a sort. *)
  Lemma field_typ_sort : forall k f T, List.nth_error (record_fields R) k = Some (f, T) ->
      exists S, type_sort S /\ record_fctx R k ++ record_params R ⊨ T : S.
  Proof.
    intros * Hk; destruct (record_field_rel R k) eqn:Er.
    - destruct (field_typ_large _ _ _ Hk Er) as [j Hj]; exists Typeω@j; split; [ constructor | exact Hj ].
    - pose proof (HT _ _ _ Hk) as H; rewrite Er in H; cbn [relevance_sort] in H.
      exists Propₘ; split; [ constructor | exact H ].
  Qed.

  (** A field's type at an instance of the fields' telescope by valid
      terms, against the field's type at the instance's value. *)
  Lemma field_inst_link_sub : forall Γ k f U Ms RΓ E ms,
      List.nth_error (record_fields R) k = Some (f, U) -> ⊨ Γ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
      List.length Ms = k + List.length (record_params R) ->
      (forall j N A, List.nth_error Ms j = Some N ->
         List.nth_error (tele_insts (record_fctx R k ++ record_params R) Id Ms) j = Some A -> Γ ⊨ N : A) ->
      RΓ E E -> List.length ms = List.length Ms ->
      ⟦ sb_of_list Id Ms : (record_fctx R k ++ record_params R) ++ Γ ⟧s E ↘ env_args E ms ->
      exists (j : nat) t u, ⟦ U[sb_of_list Id Ms] ⟧ E ↘ t /\ ⟦ U ⟧ env_args nil ms ↘ u /\ Dom t ≈ u ∈ per_univ j.
  Proof.
    intros * Hk HΓ HRΓ HMl HMs HE Hlms0 Hev.
    set (C := record_fctx R k ++ record_params R) in *.
    assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hk).
    assert (HCa : tele_ass C) by (apply record_fctx_params_ass; exact Hass).
    assert (HC : ⊨ C) by (apply record_fctx_sem; lia).
    assert (HlC : List.length Ms = List.length C) by (unfold C; rewrite List.length_app, length_record_fctx by lia; exact HMl).
    assert (Hlms : List.length ms = List.length C) by lia.
    destruct (field_typ_sort _ _ _ Hk) as (S & HS' & HU).
    pose proof (gsub_closed_inst C Γ Ms HCa HC HΓ HlC HMs) as Hg.
    destruct (gsub_props Hg) as [Hτ _].
    pose proof (closed_app_valid _ _ _ _ _ HCa HC HΓ HU) as HUΓ.
    assert (HUt : exists j : nat, C ⊨ᵗ U ≈ U at j /\ C ++ Γ ⊨ᵗ U ≈ U at j)
      by (destruct HS' as [j |];
          [ exists j; split; apply rel_type_of_typ; assumption | exists 0; split; apply rel_type_of_prop; assumption ]).
    destruct HUt as (j & HUc & HUΓt).
    destruct (typ_inst_link _ _ _ _ _ _ _ _ _ HUΓt HRΓ Hτ HE Hev) as (t & b & Et & Eb & Htb).
    destruct (closed_app_sem C Γ HCa HC HΓ) as [HCΓ Hres].
    destruct (rel_ctx_wf_per_ctx_env HC) as [RC HRC]; destruct (rel_ctx_wf_per_ctx_env HCΓ) as [RCΓ HRCΓ].
    assert (HEτ : RCΓ (env_args E ms) (env_args E ms)) by exact (rel_sub_under_ctx_at' Hτ HRΓ HRCΓ _ _ _ _ HE Hev Hev).
    pose proof (Hres _ _ HRC HRCΓ _ _ HEτ) as HEC.
    pose proof (closed_env_base C RC ms ms E E E nil HCa HC HRC Hlms Hlms HEC) as HEC'.
    destruct (rel_type_inversion_simple_at HRC HUc _ _ HEC') as (b1 & u & Eb1 & Eu & Hbu).
    assert (b1 = b) as -> by (eapply functional_eval_exp; eassumption).
    exists j, t, u; split; [ exact Et | split; [ exact Eu | etransitivity; [ exact Htb | exact Hbu ] ] ].
  Qed.

  (** The same, at the terms' own values, when those values hold the proof
      at the telescope's propositions. *)
  Lemma field_inst_link : forall Γ k f U Ms RΓ E ms,
      List.nth_error (record_fields R) k = Some (f, U) -> ⊨ Γ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
      List.length Ms = k + List.length (record_params R) ->
      (forall j N A, List.nth_error Ms j = Some N ->
         List.nth_error (tele_insts (record_fctx R k ++ record_params R) Id Ms) j = Some A -> Γ ⊨ N : A) ->
      RΓ E E -> ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ ms ->
      env_proofs gc_deps gc_stack (record_fctx R k ++ record_params R) (env_args nil ms) ->
      exists (j : nat) t u, ⟦ U[sb_of_list Id Ms] ⟧ E ↘ t /\ ⟦ U ⟧ env_args nil ms ↘ u /\ Dom t ≈ u ∈ per_univ j.
  Proof.
    intros * Hk HΓ HRΓ HMl HMs HE Ems Hpf.
    set (C := record_fctx R k ++ record_params R) in *.
    assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hk).
    assert (HCa : tele_ass C) by (apply record_fctx_params_ass; exact Hass).
    assert (HC : ⊨ C) by (apply record_fctx_sem; lia).
    assert (HlC : List.length Ms = List.length C) by (unfold C; rewrite List.length_app, length_record_fctx by lia; exact HMl).
    assert (Hlms : List.length ms = List.length C) by (rewrite (eval_exps_length _ _ _ Ems); exact HlC).
    (** The value of the substitution: the terms' values, which hold the
        proofs at the telescope's propositions. *)
    assert (Hev : ⟦ sb_of_list Id Ms : C ++ Γ ⟧s E ↘ env_args E ms).
    { rewrite <- (List.rev_involutive C).
      apply eval_sb_of_list;
        [ apply eval_sub_id, (proj1 (per_ctx_env_proofs _ _ _ HRΓ _ _ HE)) | exact Ems | rewrite List.length_rev; symmetry; exact HlC |].
      intros x Hx Hpx; rewrite List.rev_involutive in Hpx; rewrite List.length_rev in Hx.
      pose proof (Hpf x (entry_propositional_args_base C Γ E nil ms x Hlms Hx Hpx)) as H0.
      rewrite (env_entry_args_lt E nil ms x) by lia; exact H0. }
    exact (field_inst_link_sub Γ k f U Ms RΓ E ms Hk HΓ HRΓ HMl HMs HE ltac:(lia) Hev).
  Qed.

  (** A field's type is of the field's sort at every environment of the
      fields before it the context PER relates. *)
  Lemma field_type_relevance : forall Γ j f U RCΓ ρ ρ' u, List.nth_error (record_fields R) j = Some (f, U) -> ⊨ Γ ->
      EF (record_fctx R j ++ record_params R) ++ Γ ≈ (record_fctx R j ++ record_params R) ++ Γ ∈ per_ctx_env ↘ RCΓ ->
      RCΓ ρ ρ' -> ⟦ U ⟧ ρ ↘ u -> domain_relevance u = record_field_rel R j.
  Proof.
    intros * Hj HΓ HRCΓ Hρ Eu.
    assert (Hjl : j < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hj).
    assert (HCa : tele_ass (record_fctx R j ++ record_params R)) by (apply record_fctx_params_ass; exact Hass).
    assert (HC : ⊨ record_fctx R j ++ record_params R) by (apply record_fctx_sem; lia).
    destruct (record_field_rel R j) eqn:Er.
    - destruct (field_typ_large _ _ _ Hj Er) as [l HU].
      destruct (rel_exp_of_typ_relevant_at HRCΓ (closed_app_valid _ _ _ _ _ HCa HC HΓ HU) _ _ Hρ) as (u0 & Eu0 & Hr).
      assert (u0 = u) as -> by (eapply functional_eval_exp; eassumption); exact Hr.
    - pose proof (HT _ _ _ Hj) as HU; rewrite Er in HU; cbn [relevance_sort] in HU.
      destruct (rel_exp_of_prop_inversion_simple_at HRCΓ (closed_app_valid _ _ _ _ _ HCa HC HΓ HU) _ _ Hρ)
        as (a & a' & Ea & _ & [Hla _ _]).
      assert (a = u) as -> by (eapply functional_eval_exp; eassumption); exact Hla.
  Qed.

  (** The substitution of the parameters and the first [k] fields of a
      tuple, at the fields' values by their sorts, when those values are
      related arguments of the fields' telescope prefix by prefix. *)
  Lemma tuple_inst_eval : forall Γ RΓ E Ns ns Fs vs k,
      ⊨ Γ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ E E ->
      List.length Ns = List.length (record_params R) -> ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ ns ->
      k <= List.length (record_fields R) -> List.length Fs = k ->
      eval_field_vals gc_deps gc_stack (record_field_relevance R) Fs E vs ->
      (forall j, j <= k -> per_gargs (List.rev (record_fctx R j ++ record_params R)) nil nil
                              (ns ++ List.firstn j vs) (ns ++ List.firstn j vs)) ->
      ⟦ sb_of_list Id (Ns ++ Fs) : (record_fctx R k ++ record_params R) ++ Γ ⟧s E ↘ env_args E (ns ++ vs).
  Proof.
    intros * HΓ HRΓ HE Hn Ens Hk HlF Evs Hgj.
    pose proof (eval_exps_length _ _ _ Ens) as Hlns.
    pose proof (eval_field_vals_length _ _ _ _ Evs) as Hlvs.
    (** The context PER of each prefix over [Γ] relates the prefix's values. *)
    assert (Hrel : forall j, j <= k -> exists RCΓ,
               EF (record_fctx R j ++ record_params R) ++ Γ ≈ (record_fctx R j ++ record_params R) ++ Γ ∈ per_ctx_env ↘ RCΓ /\
               RCΓ (env_args E (ns ++ List.firstn j vs)) (env_args E (ns ++ List.firstn j vs))).
    { intros j Hj.
      assert (HCa : tele_ass (record_fctx R j ++ record_params R)) by (apply record_fctx_params_ass; exact Hass).
      assert (HC : ⊨ record_fctx R j ++ record_params R) by (apply record_fctx_sem; lia).
      destruct (closed_app_sem _ _ HCa HC HΓ) as [HCΓ _].
      destruct (rel_ctx_wf_per_ctx_env HCΓ) as [RCΓ HRCΓ].
      exists RCΓ; split; [ exact HRCΓ |].
      apply (closed_args_rel_over _ _ _ _ _ _ _ _ HCa HC HΓ HRΓ HRCΓ HE); [| exact (Hgj j Hj) ].
      rewrite !List.length_app, List.length_firstn, length_record_fctx by lia; lia. }
    (** The parameters: relevant, so their values. *)
    assert (Hev1 : ⟦ sb_of_list Id Ns : record_params R ++ Γ ⟧s E ↘ env_args E ns).
    { destruct (Hrel 0 ltac:(lia)) as (RP & HRP & HEP); cbn [List.firstn] in HEP; rewrite List.app_nil_r in HEP.
      change (record_fctx R 0) with (@nil centry) in HRP; cbn [List.app] in HRP.
      assert (Hpr : forall Δ1 T Δ2, record_params R = Δ1 ++ ce_ass T :: Δ2 -> exists i : nat, Δ2 ++ Γ ⊨ T : Typeω@i)
        by exact (closed_relevant_over _ _ Hass record_params_sem HΓ HPr).
      rewrite <- (List.rev_involutive (record_params R)).
      apply eval_sb_of_list; [ apply eval_sub_id, (proj1 (per_ctx_env_proofs _ _ _ HRΓ _ _ HE)) | exact Ens | rewrite List.length_rev; lia |].
      intros x Hx Hpx; exfalso; rewrite List.rev_involutive in Hpx; rewrite List.length_rev in Hx.
      exact (relevant_entries_not_propositional _ _ _ Hass Hpr HRP _ _ HEP x Hx Hpx). }
    (** The fields: by their sorts. *)
    rewrite sb_of_list_app, <- List.app_assoc, env_args_app.
    rewrite <- (List.rev_involutive (record_fctx R k)), rev_record_fctx.
    apply (eval_sb_of_list_fields _ _ _ _ _ _ _ _ Hev1 Evs); [ rewrite List.length_firstn, length_field_tele; lia |].
    intros j e Hje.
    assert (Hjk : j < k) by (pose proof (nth_error_lt_length _ _ _ Hje) as Hx; rewrite List.length_firstn in Hx; lia).
    rewrite List.nth_error_firstn in Hje; destruct (Nat.ltb_spec j k) as [_ |]; [| lia ].
    unfold field_tele in Hje; rewrite List.nth_error_map in Hje.
    destruct (List.nth_error (record_fields R) j) as [[f U] |] eqn:Hj; cbn in Hje; [ injection Hje as <- | discriminate ].
    rewrite List.firstn_firstn, Nat.min_l by lia; rewrite <- rev_record_fctx, List.rev_involutive.
    rewrite <- env_args_app, List.app_assoc.
    destruct (Hrel j ltac:(lia)) as (RCΓ & HRCΓ & HEj).
    (** The field's type over the prefix, of the field's sort. *)
    assert (HCa : tele_ass (record_fctx R j ++ record_params R)) by (apply record_fctx_params_ass; exact Hass).
    assert (HC : ⊨ record_fctx R j ++ record_params R) by (apply record_fctx_sem; lia).
    destruct (field_typ_sort _ _ _ Hj) as (S & HS' & HU).
    destruct (rel_type_of_sort HS' (closed_app_valid _ _ _ _ _ HCa HC HΓ HU)) as [iU HUt].
    destruct (rel_type_inversion_simple_at HRCΓ HUt _ _ HEj) as (u & _ & Eu & _ & _).
    pose proof (field_type_relevance _ _ _ _ _ _ _ _ Hj HΓ HRCΓ HEj Eu) as Hr.
    pose proof (head_propositional_iff (e := ce_ass U) HRCΓ eq_refl (rel_type_inversion_simple_at HRCΓ HUt) HEj Eu) as Hiff.
    unfold record_field_rel in Hr.
    split; [ intros Hrel'; rewrite Hiff; congruence | intros Hp; apply Hiff; congruence ].
  Qed.

  (** ** Projections *)

  (** The values of the projections of [M] before field [k] are the first
      [k] projections of its value. *)
  Lemma eval_record_pre : forall E M m vs, ⟦ M ⟧ E ↘ m -> record_projs R m vs ->
      forall k, k <= List.length (record_fields R) -> ⟦ record_pre R k M ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ List.firstn k vs.
  Proof.
    intros * Hm Hvs k; induction k as [| k IH]; intros Hk; [ constructor |].
    destruct (nth_error_lt_some' (record_fields R) k ltac:(lia)) as [[f U] Hfk].
    pose proof (List.Forall2_length Hvs) as Hlv.
    destruct (nth_error_lt_some' vs k ltac:(lia)) as [v Hv].
    rewrite (record_pre_succ _ _ _ _ M Hfk), (firstn_succ_nth _ _ _ Hv).
    apply eval_exps_app; [ apply IH; lia |].
    econstructor; [ econstructor; [ exact Hm | exact (Forall2_nth_both _ _ _ _ _ _ Hvs Hfk Hv) ] | constructor ].
  Qed.

  (** The parameters and the projections before field [k], valid at the
      fields' telescope when the projections before are. *)
  Lemma record_pre_insts : forall Γ M Ns k, List.length Ns = List.length (record_params R) ->
      k <= List.length (record_fields R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A -> Γ ⊨ N : A) ->
      (forall j f U, j < k -> List.nth_error (record_fields R) j = Some (f, U) ->
         Γ ⊨ a_proj f M : U[sb_of_list Id (Ns ++ record_pre R j M)]) ->
      forall j N A, List.nth_error (Ns ++ record_pre R k M) j = Some N ->
        List.nth_error (tele_insts (record_fctx R k ++ record_params R) Id (Ns ++ record_pre R k M)) j = Some A ->
        Γ ⊨ N : A.
  Proof.
    intros * Hn Hk HNs HPs j N A HN HA.
    rewrite tele_insts_app in HA by (try exact Hass; exact Hn).
    assert (HlT : List.length (tele_insts (record_params R) Id Ns) = List.length Ns)
      by (rewrite length_tele_insts by exact Hass; lia).
    destruct (Nat.lt_ge_cases j (List.length Ns)) as [Hj | Hj].
    - rewrite List.nth_error_app1 in HN by exact Hj; rewrite List.nth_error_app1 in HA by lia.
      exact (HNs _ _ _ HN HA).
    - rewrite List.nth_error_app2 in HN by exact Hj; rewrite List.nth_error_app2, HlT in HA by lia.
      set (j' := j - List.length Ns) in *.
      assert (Hj'k : j' < k)
        by (pose proof (nth_error_lt_length _ _ _ HN) as Hx; rewrite length_record_pre in Hx by exact Hk; exact Hx).
      unfold record_pre in HN; rewrite List.nth_error_map, List.nth_error_firstn in HN.
      destruct (Nat.ltb_spec j' k); [| lia ].
      destruct (List.nth_error (record_fields R) j') as [[f U] |] eqn:Hj'; cbn in HN; [ injection HN as <- | discriminate ].
      destruct (tele_insts_nth _ _ _ _ _ HA) as (A0 & HA0 & ->).
      rewrite rev_record_fctx, List.nth_error_firstn in HA0; destruct (Nat.ltb_spec j' k); [| lia ].
      unfold field_tele in HA0; rewrite List.nth_error_map, Hj' in HA0; cbn in HA0; injection HA0 as <-.
      rewrite <- sb_of_list_app.
      replace (List.firstn j' (record_pre R k M)) with (record_pre R j' M)
        by (unfold record_pre; rewrite List.firstn_map, List.firstn_firstn, Nat.min_l by lia; reflexivity).
      exact (HPs _ _ _ Hj'k Hj').
  Qed.

  (** The element relation of a record type at a value of the type former
      at parameters is the canonical one there, with its conditions. *)
  Lemma record_typ_facts : forall i a ns RM, DF a ≈ d_record p ns ∈ per_univ_elem i ↘ RM ->
      record_canon_facts i R ns ns RM.
  Proof.
    intros * H.
    pose proof (per_univ_sym _ _ _ _ H) as H'.
    pose proof (per_univ_trans _ _ _ _ _ _ H' H) as Hd.
    exact (per_univ_elem_record_facts _ _ _ _ _ _ Hl Hd).
  Qed.

  (** The values of valid parameters at related environments are related
      arguments of the parameters' telescope: the parameters are relevant,
      so the substitution of the parameters' instance holds their values. *)
  Lemma params_inst_gargs : forall Γ Ns RΓ E E' ns ns', ⊨ Γ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
      List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A -> Γ ⊨ N : A) ->
      RΓ E E' -> ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ ns -> ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ E' ↘ ns' ->
      per_gargs (List.rev (record_params R)) nil nil ns ns'.
  Proof.
    intros * HΓ HRΓ Hn HNs HE Ens Ens'.
    pose proof (gsub_closed_inst (record_params R) Γ Ns Hass record_params_sem HΓ Hn HNs) as Hg.
    destruct (gsub_props Hg) as [Hτ _].
    destruct (rel_sub_under_ctx_simple Hτ) as (RΓ0 & HRΓ0 & RΔ0 & HRΔ0 & Hs).
    assert (E0 : RΓ <~> RΓ0) by (eapply per_ctx_env_right_irrel; eassumption).
    destruct (Hs _ _ (proj1 (E0 _ _) HE)) as (y1 & y2 & Ey1 & Ey2 & Hy).
    assert (Hrel : forall Δ1 T Δ2, record_params R = Δ1 ++ ce_ass T :: Δ2 -> exists i : nat, Δ2 ++ Γ ⊨ T : Typeω@i)
      by exact (closed_relevant_over _ _ Hass record_params_sem HΓ HPr).
    assert (HlP : List.length (List.rev (record_params R)) = List.length Ns) by (rewrite List.length_rev; lia).
    assert (HPΔ : PER RΔ0) by (eapply per_env_PER; exact HRΔ0).
    assert (Hy11 : RΔ0 y1 y1) by (etransitivity; [ exact Hy | symmetry; exact Hy ]).
    assert (Hy22 : RΔ0 y2 y2) by (etransitivity; [ symmetry; exact Hy | exact Hy ]).
    assert (Hnp : forall y, RΔ0 y y -> forall x, x < List.length (List.rev (record_params R)) ->
                ~ entry_propositional gc_deps gc_stack (List.rev (List.rev (record_params R)) ++ Γ) y x)
      by (intros y Hyy x Hx; rewrite List.rev_involutive; rewrite List.length_rev in Hx;
          exact (relevant_entries_not_propositional _ _ _ Hass Hrel HRΔ0 _ _ Hyy x Hx)).
    destruct (per_ctx_env_proofs _ _ _ HRΓ _ _ HE) as [Hp1 Hp2].
    rewrite <- (List.rev_involutive (record_params R)) in Ey1, Ey2.
    destruct (eval_sb_of_list_inv _ _ _ _ _ _ _ HlP Ey1 (Hnp _ Hy11) (eval_sub_id _ _ Hp1)) as (ms1 & Ems1 & A1).
    destruct (eval_sb_of_list_inv _ _ _ _ _ _ _ HlP Ey2 (Hnp _ Hy22) (eval_sub_id _ _ Hp2)) as (ms2 & Ems2 & A2).
    pose proof (functional_eval_exps _ _ _ _ Ems1 Ens) as ->.
    pose proof (functional_eval_exps _ _ _ _ Ems2 Ens') as ->.
    assert (HEΔ : RΔ0 (env_args E ns) (env_args E' ns')).
    { rewrite List.length_rev in A1, A2.
      eapply (per_ctx_env_resp_agree HRΔ0); [ rewrite List.length_app; exact A1 | rewrite List.length_app; exact A2 | exact Hy ]. }
    destruct (closed_app_sem _ _ Hass record_params_sem HΓ) as [_ Hres].
    destruct (rel_ctx_wf_per_ctx_env record_params_sem) as [RQ HRQ].
    pose proof (Hres RQ RΔ0 HRQ HRΔ0 _ _ HEΔ) as HEQ.
    assert (HRQ' : EF List.rev (List.rev (record_params R)) ++ ⋅ ≈ List.rev (List.rev (record_params R)) ++ ⋅ ∈ per_ctx_env ↘ RQ)
      by (rewrite List.rev_involutive, List.app_nil_r; exact HRQ).
    pose proof (eval_exps_length _ _ _ Ens) as Hl1; pose proof (eval_exps_length _ _ _ Ens') as Hl2.
    destruct (rel_gargs _ _ _ _ per_ctx_env_nil_true (rev_tele_sem _ record_params_sem) (rev_tele_ass _ Hass) HRQ' _ _ ns ns'
                ltac:(rewrite List.length_rev; lia) ltac:(rewrite List.length_rev; lia) HEQ)
      as [_ Hgc].
    exact (per_gargs_base _ _ _ per_ctx_env_nil_true (rev_tele_sem _ record_params_sem) (rev_tele_ass _ Hass) _ _ nil nil _ _ I I I Hgc).
  Qed.

  (** The field [k] of equal elements of a record type at valid
      parameters, when the projections of the left one before it are
      valid: equal at the field's type at the parameters and those
      projections, whose instance of the fields' telescope is then
      valid. *)
  Lemma rel_exp_under_ctx_proj_core : forall Γ M M' Ns k f U, ⊨ Γ ->
      Γ ⊨ M ≈ M' : apps_exp (a_record p) Ns -> List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A -> Γ ⊨ N : A) ->
      List.nth_error (record_fields R) k = Some (f, U) ->
      (forall j f0 U0, j < k -> List.nth_error (record_fields R) j = Some (f0, U0) ->
         Γ ⊨ a_proj f0 M : U0[sb_of_list Id (Ns ++ record_pre R j M)]) ->
      Γ ⊨ a_proj f M ≈ a_proj f M' : U[sb_of_list Id (Ns ++ record_pre R k M)].
  Proof.
    intros * HΓ HM Hn HNs Hjf HPs.
    assert (Hk0 : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hjf).
    pose proof (record_pre_insts Γ M Ns k Hn ltac:(lia) HNs HPs) as Hins.
    assert (HCa : tele_ass (record_fctx R k ++ record_params R)) by (apply record_fctx_params_ass; exact Hass).
    assert (HC : ⊨ record_fctx R k ++ record_params R) by (apply record_fctx_sem; lia).
    assert (HlM : List.length (Ns ++ record_pre R k M) = k + List.length (record_params R))
      by (rewrite List.length_app, length_record_pre by lia; lia).
    assert (HlC : List.length (Ns ++ record_pre R k M) = List.length (record_fctx R k ++ record_params R))
      by (rewrite HlM, List.length_app, length_record_fctx by lia; reflexivity).
    pose proof (gsub_closed_inst _ Γ _ HCa HC HΓ HlC Hins) as Hg.
    (** A propositional field: its projections are proofs. *)
    destruct (record_field_rel R k) eqn:Erk.
    2:{ apply rel_exp_under_ctx_proof.
        pose proof (HT _ _ _ Hjf) as HUp; rewrite Erk in HUp; cbn [relevance_sort] in HUp.
        pose proof (rel_exp_under_ctx_gsub Hg (closed_app_valid _ _ _ _ _ HCa HC HΓ HUp)) as HUτ; cbn [exp_sub] in HUτ.
        exact HUτ. }
    destruct (field_typ_large _ _ _ Hjf Erk) as [l HU].
    pose proof (rel_exp_under_ctx_gsub Hg (closed_app_valid _ _ _ _ _ HCa HC HΓ HU)) as HUτ; cbn [exp_sub] in HUτ.
    destruct (rel_type_inversion (rel_type_of_typ HUτ)) as [RΓ [HRΓ HUgen]].
    destruct HM as [RΓ2 HRΓ2 iM HMgen].
    eexists_rel_exp_with l.
    intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
    destruct (HUgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [t1 t2 t3 t4 Et1 Et2 Et3 Et4 Htch].
    functionalize_per_univ_chain Htch RT.
    destruct (HMgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [RM [Htyp Hexp]].
    pose proof Htyp as [a1 a2 a3 a4 Ea1 Ea2 Ea3 Ea4 Hach].
    (** The record type at the parameters' values in the middle: relevant,
        so the terms are related *)
    destruct (eval_record_apps_inv _ _ _ Ea2 Hn) as (ns2 & Ens2 & ->).
    apply (rel_exp_or_prop_relevant Htyp (ex_intro _ (d_record p ns2) (conj Ea2 eq_refl))) in Hexp.
    destruct Hexp as [m1 m2 m3 m4 Em1 Em2 Em3 Em4 Hmch].
    assert (Ha23 : DF d_record p ns2 ≈ a3 ∈ per_univ_elem iM ↘ RM) by pairwise.
    pose proof (record_typ_facts _ _ _ _ (per_univ_sym _ _ _ _ Ha23)) as Hf.
    destruct Hf as [_ Hln2 _ _ _ HfI _ HfS HE].
    assert (Hm12 : RM m1 m2) by pairwise.
    assert (Hm23 : RM m2 m3) by pairwise.
    assert (Hm34 : RM m3 m4) by pairwise.
    destruct (proj1 (HE _ _) Hm12) as [P1 P2 HP1 HP2 Hr12].
    destruct (proj1 (HE _ _) Hm23) as [P2' P3 HP2' HP3 Hr23].
    destruct (proj1 (HE _ _) Hm34) as [P3' P4 HP3' HP4 Hr34].
    pose proof (record_projs_functional _ _ _ _ HP2' HP2) as ->.
    pose proof (record_projs_functional _ _ _ _ HP3' HP3) as ->.
    assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hjf).
    pose proof (List.Forall2_length HP1) as Hl1; pose proof (List.Forall2_length HP2) as Hl2.
    pose proof (List.Forall2_length HP3) as Hl3; pose proof (List.Forall2_length HP4) as Hl4.
    destruct (nth_error_lt_some' P1 k ltac:(lia)) as [r1 Hr1].
    destruct (nth_error_lt_some' P2 k ltac:(lia)) as [r2 Hr2].
    destruct (nth_error_lt_some' P3 k ltac:(lia)) as [r3 Hr3].
    destruct (nth_error_lt_some' P4 k ltac:(lia)) as [r4 Hr4].
    pose proof (Forall2_nth_both _ _ _ _ _ _ HP1 Hjf Hr1) as Ep1.
    pose proof (Forall2_nth_both _ _ _ _ _ _ HP2 Hjf Hr2) as Ep2.
    pose proof (Forall2_nth_both _ _ _ _ _ _ HP3 Hjf Hr3) as Ep3.
    pose proof (Forall2_nth_both _ _ _ _ _ _ HP4 Hjf Hr4) as Ep4.
    cbn [fst] in Ep1, Ep2, Ep3, Ep4.
    (** The links of the projections, at the field's relation at the middle
        prefix *)
    set (Q := canon_fields_rel R ns2 k (List.firstn k P2)).
    assert (Hq12 : Q r1 r2).
    { pose proof Hr12 as H; rewrite tele_rel_iff in H; destruct H as (_ & _ & H).
      pose proof (H _ _ _ Hr1 Hr2) as Hx.
      pose proof (tele_prefix_rel_of_full _ _ _ _ k Hr12 ltac:(lia)) as Hpre.
      exact (proj1 (HfI _ _ _ _ _ Hjf Hpre _ _) Hx). }
    assert (Hq23 : Q r2 r3).
    { pose proof Hr23 as H; rewrite tele_rel_iff in H; destruct H as (_ & _ & H); exact (H _ _ _ Hr2 Hr3). }
    assert (Hq34 : Q r3 r4).
    { pose proof Hr34 as H; rewrite tele_rel_iff in H; destruct H as (_ & _ & H).
      pose proof (H _ _ _ Hr3 Hr4) as Hx.
      pose proof (tele_prefix_rel_of_full _ _ _ _ k Hr23 ltac:(lia)) as Hpre.
      exact (proj2 (HfI _ _ _ _ _ Hjf Hpre _ _) Hx). }
    (** The field's type at the middle values, against the field's
        relation there *)
    assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
    assert (Hρσ : RΓ ρσ ρ'σ') by exact (rel_sub_under_ctx_at' Hσ HΓ' HRΓ _ _ _ _ Hρ Hev Hev').
    assert (Hρσρσ : RΓ ρσ ρσ) by (etransitivity; [ exact Hρσ | symmetry; exact Hρσ ]).
    assert (Ems : ⟦ Ns ++ record_pre R k M ⟧* gc_deps ⍮ gc_stack ⍮ ρσ ↘ ns2 ++ List.firstn k P2)
      by (apply eval_exps_app; [ exact Ens2 | exact (eval_record_pre _ _ _ _ Em2 HP2 k ltac:(lia)) ]).
    (** The middle values hold the proofs at the fields' telescope: the
        parameters' and fields' values are related arguments of it. *)
    assert (Hpf : env_proofs gc_deps gc_stack (record_fctx R k ++ record_params R) (env_args nil (ns2 ++ List.firstn k P2))).
    { pose proof (params_inst_gargs Γ Ns RΓ ρσ ρσ ns2 ns2 HΓ HRΓ Hn HNs Hρσρσ Ens2 Ens2) as Hgp.
      destruct (sort_tele_value _ _ record_params_sem HS _ Hgp Hln2) as [a Ha].
      pose proof (canon_fields_gargs _ _ _ Hgp Hln2 Ha k (List.firstn k P2) (List.firstn k P3) ltac:(lia)
                    (tele_prefix_rel_of_full _ _ _ _ k Hr23 ltac:(lia))) as Hgf.
      apply (gargs_env_proofs _ _ (ns2 ++ List.firstn k P3) nil nil HC).
      - rewrite !List.length_app, List.length_firstn, length_record_fctx by lia; lia.
      - rewrite List.rev_app_distr, rev_record_fctx.
        apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hln2 | exact Hgp | exact Hgf ]. }
    destruct (field_inst_link Γ k f U _ RΓ ρσ _ Hjf HΓ HRΓ HlM Hins Hρσρσ Ems Hpf) as (jb & t & u & Et & Eu & [Ru HRu]).
    assert (t = t2) as -> by (eapply functional_eval_exp; eassumption).
    assert (ERT : RT <~> Ru) by (eapply per_univ_chain_rel_irrel; [ exact Htch | exact HRu | solve_in ]).
    pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRu) HRu) as HRuu.
    assert (EQ : Q <~> RT).
    { unfold Q, canon_fields_rel; rewrite (nth_ftyp_eq _ _ _ _ Hjf).
      etransitivity; [ symmetry; exact (per_head_iff Eu Eu HRuu) | symmetry; exact ERT ]. }
    exists RT; split.
    - apply (mk_rel_exp t1 t2 t3 t4); [ exact Et1 | exact Et2 | exact Et3 | exact Et4 | exact Htch ].
    - right; apply (mk_rel_exp r1 r2 r3 r4);
        [ cbn [exp_sub]; econstructor; [ exact Em1 | exact Ep1 ] | econstructor; [ exact Em2 | exact Ep2 ]
        | econstructor; [ exact Em3 | exact Ep3 ] | cbn [exp_sub]; econstructor; [ exact Em4 | exact Ep4 ] |].
      apply rel_chain_4; apply EQ; assumption.
  Qed.

  (** A field of an element of a record type at valid parameters: valid,
      by induction on the field. *)
  Lemma valid_exp_under_ctx_proj : forall Γ M Ns, ⊨ Γ ->
      Γ ⊨ M : apps_exp (a_record p) Ns -> List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A -> Γ ⊨ N : A) ->
      forall k f U, List.nth_error (record_fields R) k = Some (f, U) ->
        Γ ⊨ a_proj f M : U[sb_of_list Id (Ns ++ record_pre R k M)].
  Proof.
    intros * HΓ HM Hn HNs.
    enough (Hall : forall k, k <= List.length (record_fields R) -> forall j f U, j < k ->
              List.nth_error (record_fields R) j = Some (f, U) -> Γ ⊨ a_proj f M : U[sb_of_list Id (Ns ++ record_pre R j M)]).
    { intros k f U Hk; pose proof (nth_error_lt_length _ _ _ Hk) as Hkl.
      exact (Hall (S k) ltac:(lia) k f U ltac:(lia) Hk). }
    induction k as [| k IH]; intros Hk j f U Hj Hjf; [ lia |].
    destruct (Nat.lt_ge_cases j k) as [Hjk | Hjk]; [ exact (IH ltac:(lia) j f U Hjk Hjf) |].
    assert (j = k) as -> by lia.
    exact (rel_exp_under_ctx_proj_core Γ M M Ns k f U HΓ HM Hn HNs Hjf (fun j0 f0 U0 Hj0 => IH ltac:(lia) j0 f0 U0 Hj0)).
  Qed.

  (** The field [k] of equal elements: equal. *)
  Lemma rel_exp_under_ctx_proj_cong : forall Γ M M' Ns k f U, ⊨ Γ ->
      Γ ⊨ M ≈ M' : apps_exp (a_record p) Ns -> List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A -> Γ ⊨ N : A) ->
      List.nth_error (record_fields R) k = Some (f, U) ->
      Γ ⊨ a_proj f M ≈ a_proj f M' : U[sb_of_list Id (Ns ++ record_pre R k M)].
  Proof.
    intros * HΓ HM Hn HNs Hjf.
    apply (rel_exp_under_ctx_proj_core _ _ _ _ _ _ _ HΓ HM Hn HNs Hjf).
    intros j f0 U0 _ Hj; exact (valid_exp_under_ctx_proj _ _ _ HΓ (rel_exp_under_ctx_refl_left HM) Hn HNs _ _ _ Hj).
  Qed.

  (** ** Tuples *)

  (** The projections of a tuple of the record's fields are its values. *)
  Lemma tuple_projs : forall (fs : list (String.string * exp)) vs,
      List.map fst fs = List.map fst (record_fields R) -> List.length vs = List.length (record_fields R) ->
      record_projs R (d_tuple (List.combine (List.map fst fs) vs)) vs.
  Proof.
    intros * Hfs Hlv; apply Forall2_of_nth; [ exact (eq_sym Hlv) |].
    intros k [g T] v Hk Hv; cbn [fst]; constructor.
    apply (field_lookup_combine_nth _ _ k); [ rewrite Hfs; exact Hnd | rewrite Hfs, List.length_map; lia
                                           | rewrite Hfs, List.nth_error_map, Hk; reflexivity | exact Hv ].
  Qed.

  (** The parameters and the fields before field [k] of a tuple, valid at
      the fields' telescope. *)
  Lemma tuple_insts : forall Γ Ns (fs : list (String.string * exp)), List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A -> Γ ⊨ N : A) ->
      List.map fst fs = List.map fst (record_fields R) ->
      (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
         Γ ⊨ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
      forall k, k <= List.length (record_fields R) ->
      forall j N A, List.nth_error (Ns ++ List.firstn k (List.map snd fs)) j = Some N ->
        List.nth_error (tele_insts (record_fctx R k ++ record_params R) Id (Ns ++ List.firstn k (List.map snd fs))) j = Some A ->
        Γ ⊨ N : A.
  Proof.
    intros * Hn HNs Hfs HMs k Hk j N A HN HA.
    assert (Hlf : List.length fs = List.length (record_fields R))
      by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
    rewrite tele_insts_app in HA by (try exact Hass; exact Hn).
    assert (HlT : List.length (tele_insts (record_params R) Id Ns) = List.length Ns)
      by (rewrite length_tele_insts by exact Hass; lia).
    destruct (Nat.lt_ge_cases j (List.length Ns)) as [Hj | Hj].
    - rewrite List.nth_error_app1 in HN by exact Hj; rewrite List.nth_error_app1 in HA by lia.
      exact (HNs _ _ _ HN HA).
    - rewrite List.nth_error_app2 in HN by exact Hj; rewrite List.nth_error_app2, HlT in HA by lia.
      set (j' := j - List.length Ns) in *.
      rewrite List.nth_error_firstn in HN; destruct (Nat.ltb_spec j' k) as [Hj'k |]; [| discriminate ].
      rewrite List.nth_error_map in HN.
      destruct (List.nth_error fs j') as [[g M] |] eqn:Hg; cbn in HN; [ injection HN as <- | discriminate ].
      destruct (nth_error_lt_some' (record_fields R) j' ltac:(lia)) as [[f U] Hj'].
      assert (g = f) as ->.
      { pose proof (List.map_nth_error fst _ _ Hg) as E1; pose proof (List.map_nth_error fst _ _ Hj') as E2.
        rewrite Hfs in E1; rewrite E1 in E2; injection E2 as ->; reflexivity. }
      destruct (tele_insts_nth _ _ _ _ _ HA) as (A0 & HA0 & ->).
      rewrite rev_record_fctx, List.nth_error_firstn in HA0; destruct (Nat.ltb_spec j' k); [| lia ].
      unfold field_tele in HA0; rewrite List.nth_error_map, Hj' in HA0; cbn in HA0; injection HA0 as <-.
      rewrite <- sb_of_list_app, List.firstn_firstn, Nat.min_l by lia.
      exact (HMs _ _ _ _ Hg Hj').
  Qed.

  (** Values canonically related at a prefix of the fields, after related
      parameters, are related arguments of each shorter prefix. *)
  Lemma prefix_gargs : forall ns vs vs' a k, per_gargs (List.rev (record_params R)) nil nil ns ns ->
      List.length ns = List.length (record_params R) -> ⟦ record_sort R ⟧ env_args nil ns ↘ a ->
      k <= List.length (record_fields R) -> tele_prefix_rel (canon_fields_rel R ns) k vs vs' ->
      forall j, j <= k -> per_gargs (List.rev (record_fctx R j ++ record_params R)) nil nil
                            (ns ++ List.firstn j vs) (ns ++ List.firstn j vs).
  Proof.
    intros * Hg Hln Ha Hk Hp j Hj.
    pose proof (tele_prefix_rel_of_pre _ _ _ _ j Hp Hj) as Hpj.
    pose proof (canon_fields_gargs _ _ _ Hg Hln Ha j _ _ ltac:(lia) Hpj) as Hgf.
    assert (Hg' : per_gargs (List.rev (record_fctx R j ++ record_params R)) nil nil
                    (ns ++ List.firstn j vs) (ns ++ List.firstn j vs')).
    { rewrite List.rev_app_distr, rev_record_fctx.
      apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hln | exact Hg | exact Hgf ]. }
    exact (tele_gargs_refl_l _ (record_fctx_sem j ltac:(lia)) ltac:(apply record_fctx_params_ass; exact Hass) _ _ Hg').
  Qed.

  (** At a propositional field, after related values of the fields before
      it, the canonical relation relates the proofs. *)
  Lemma field_canon_proof : forall k f U ns pre, List.nth_error (record_fields R) k = Some (f, U) ->
      record_field_rel R k = propositional -> List.length ns = List.length (record_params R) -> List.length pre = k ->
      per_gargs (List.rev (record_fctx R k ++ record_params R)) nil nil (ns ++ pre) (ns ++ pre) ->
      canon_fields_rel R ns k pre ⋆ᵈ ⋆ᵈ.
  Proof.
    intros * Hk Hr Hln Hlp Hg.
    assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hk).
    assert (HC : ⊨ record_fctx R k ++ record_params R) by (apply record_fctx_sem; lia).
    destruct (rel_ctx_wf_per_ctx_env HC) as [RC HRC].
    assert (HE : RC (env_args nil (ns ++ pre)) (env_args nil (ns ++ pre)))
      by (apply (gargs_env_rel _ _ _ _ _ _ HRC HC); [ rewrite !List.length_app, length_record_fctx by lia; lia | exact Hg ]).
    pose proof (HT _ _ _ Hk) as HU; rewrite Hr in HU; cbn [relevance_sort] in HU.
    destruct (rel_exp_of_prop_inversion_simple_at HRC HU _ _ HE) as (u & _ & Eu & _ & [Hu _ _]).
    unfold canon_fields_rel; rewrite (nth_ftyp_eq _ _ _ _ Hk).
    exact (per_head_proof Eu Hu).
  Qed.

  (** A tuple of valid fields at a record type at valid parameters: valid.
      The fields' values are by their sorts; the fields of the four tuples
      are related one link at a time, the field's relation read at the
      middle prefix and moved along the invariance of the canonical
      relations, a propositional field's proofs related by its type. *)
  Lemma valid_exp_under_ctx_tuple : forall Γ T Ns (fs : list (String.string * exp)) (i : nat), ⊨ Γ ->
      Γ ⊨ T ≈ apps_exp (a_record p) Ns : Typeω@i -> List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A -> Γ ⊨ N : A) ->
      List.map fst fs = List.map fst (record_fields R) ->
      (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
         Γ ⊨ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
      Γ ⊨ a_tuple T fs : T.
  Proof.
    intros * HΓ HTeq Hn HNs Hfs HMs.
    assert (Hlf : List.length fs = List.length (record_fields R))
      by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
    pose proof (rel_exp_under_ctx_refl_left HTeq) as HTl.
    destruct (rel_type_inversion (rel_type_of_typ HTl)) as [RΓ [HRΓ HTgen]].
    (** A relevant field's instance type is a type of a universe. *)
    assert (HUk : forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
               record_field_rel R k = relevant ->
               exists j : nat, Γ ⊨ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] : Typeω@j).
    { intros k f M U Hk Hfk Hr.
      assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
      assert (HCa : tele_ass (record_fctx R k ++ record_params R)) by (apply record_fctx_params_ass; exact Hass).
      assert (HC : ⊨ record_fctx R k ++ record_params R) by (apply record_fctx_sem; lia).
      assert (HlC : List.length (Ns ++ List.firstn k (List.map snd fs)) = List.length (record_fctx R k ++ record_params R))
        by (rewrite !List.length_app, List.length_firstn, List.length_map, length_record_fctx by lia; lia).
      pose proof (gsub_closed_inst _ Γ _ HCa HC HΓ HlC (tuple_insts Γ Ns fs Hn HNs Hfs HMs k ltac:(lia))) as Hg.
      destruct (field_typ_large _ _ _ Hfk Hr) as [j HU].
      exists j; pose proof (rel_exp_under_ctx_gsub Hg (closed_app_valid _ _ _ _ _ HCa HC HΓ HU)) as H; cbn [exp_sub] in H; exact H. }
    eexists_rel_exp_with i.
    intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
    destruct (HTgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [t1 t2 t3 t4 Et1 Et2 Et3 Et4 Htch].
    functionalize_per_univ_chain Htch RT.
    assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
    assert (Hρσ : RΓ ρσ ρ'σ') by exact (rel_sub_under_ctx_at' Hσ HΓ' HRΓ _ _ _ _ Hρ Hev Hev').
    assert (Hρσρσ : RΓ ρσ ρσ) by (etransitivity; [ exact Hρσ | symmetry; exact Hρσ ]).
    (** The record type at the parameters' values in the middle *)
    destruct (rel_exp_of_typ_inversion_simple_at HRΓ HTeq _ _ Hρσρσ) as (t2' & a2 & Et2' & Ea2 & [Rx HRx]).
    assert (t2' = t2) as -> by (eapply functional_eval_exp; eassumption).
    destruct (eval_record_apps_inv _ _ _ Ea2 Hn) as (ns2 & Ens2 & ->).
    pose proof (record_typ_facts _ _ _ _ HRx) as [_ Hln2 _ _ _ HfI _ HfS HE].
    assert (ERT : RT <~> Rx) by (eapply per_univ_chain_rel_irrel; [ exact Htch | exact HRx | solve_in ]).
    pose proof (params_inst_gargs Γ Ns RΓ ρσ ρσ ns2 ns2 HΓ HRΓ Hn HNs Hρσρσ Ens2 Ens2) as Hgp.
    destruct (sort_tele_value _ _ record_params_sem HS _ Hgp Hln2) as [a Ha].
    (** Each relevant field: its four values, related at the relation of its
        instance type at the middle *)
    assert (Hch : forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
               record_field_rel R k = relevant ->
               exists Rk w1 w2 w3 w4 b (jb : nat), ⟦ M[σ] ⟧ ρ ↘ w1 /\ ⟦ M ⟧ ρσ ↘ w2 /\ ⟦ M ⟧ ρ'σ' ↘ w3 /\ ⟦ M[σ'] ⟧ ρ' ↘ w4 /\
                 rel_chain Rk (w1 :: w2 :: w3 :: w4 :: nil) /\
                 ⟦ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] ⟧ ρσ ↘ b /\ DF b ≈ b ∈ per_univ_elem jb ↘ Rk).
    { intros k f M U Hk Hfk Hr.
      destruct (HUk _ _ _ _ Hk Hfk Hr) as [jU HUτ].
      destruct (HMs _ _ _ _ Hk Hfk) as [RΓk HRΓk lk HMgen].
      destruct (HMgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [Rk [Htyp Hexp]].
      pose proof Htyp as [b1 b2 b3 b4 Eb1 Eb2 Eb3 Eb4 Hbch].
      destruct (rel_exp_of_typ_relevant_at HRΓ HUτ _ _ Hρσρσ) as (b0 & Eb0 & Hr0).
      assert (b0 = b2) as -> by (eapply functional_eval_exp; eassumption).
      apply (rel_exp_or_prop_relevant Htyp (ex_intro _ b2 (conj Eb2 Hr0))) in Hexp.
      destruct Hexp as [w1 w2 w3 w4 Ew1 Ew2 Ew3 Ew4 Hwch].
      exists Rk, w1, w2, w3, w4, b2, lk.
      destruct Hbch as (_ & Hb23 & _).
      repeat (split; [ assumption |]).
      eapply per_univ_trans; [ exact Hb23 | apply per_univ_sym; exact Hb23 ]. }
    (** The values of the fields at the four environments *)
    assert (Hnm : forall m g M, List.nth_error fs m = Some (g, M) -> exists U, List.nth_error (record_fields R) m = Some (g, U)).
    { intros m g M Hm; destruct (nth_error_lt_some' (record_fields R) m) as [[g' U] Hm'];
        [ rewrite <- Hlf; exact (nth_error_lt_length _ _ _ Hm) |].
      exists U; pose proof (List.map_nth_error fst _ _ Hm) as E1; pose proof (List.map_nth_error fst _ _ Hm') as E2.
      rewrite Hfs in E1; rewrite E1 in E2; injection E2 as ->; exact Hm'. }
    set (rs := record_field_relevance R).
    destruct (eval_field_vals_each (List.map (fun f => (snd f)[σ]) fs) rs ρ) as [V1 EV1].
    { intros m M' Hm Hr; rewrite List.nth_error_map in Hm.
      destruct (List.nth_error fs m) as [[g M] |] eqn:Hg; cbn in Hm; [ injection Hm as <- | discriminate ].
      destruct (Hnm _ _ _ Hg) as [U HU]; destruct (Hch _ _ _ _ Hg HU Hr) as (Rk & w1 & _ & _ & _ & _ & _ & Ew1 & _); eauto. }
    destruct (eval_field_vals_each (List.map snd fs) rs ρσ) as [V2 EV2].
    { intros m M' Hm Hr; rewrite List.nth_error_map in Hm.
      destruct (List.nth_error fs m) as [[g M] |] eqn:Hg; cbn in Hm; [ injection Hm as <- | discriminate ].
      destruct (Hnm _ _ _ Hg) as [U HU]; destruct (Hch _ _ _ _ Hg HU Hr) as (Rk & _ & w2 & _ & _ & _ & _ & _ & Ew2 & _); eauto. }
    destruct (eval_field_vals_each (List.map snd fs) rs ρ'σ') as [V3 EV3].
    { intros m M' Hm Hr; rewrite List.nth_error_map in Hm.
      destruct (List.nth_error fs m) as [[g M] |] eqn:Hg; cbn in Hm; [ injection Hm as <- | discriminate ].
      destruct (Hnm _ _ _ Hg) as [U HU]; destruct (Hch _ _ _ _ Hg HU Hr) as (Rk & _ & _ & w3 & _ & _ & _ & _ & _ & Ew3 & _); eauto. }
    destruct (eval_field_vals_each (List.map (fun f => (snd f)[σ']) fs) rs ρ') as [V4 EV4].
    { intros m M' Hm Hr; rewrite List.nth_error_map in Hm.
      destruct (List.nth_error fs m) as [[g M] |] eqn:Hg; cbn in Hm; [ injection Hm as <- | discriminate ].
      destruct (Hnm _ _ _ Hg) as [U HU]; destruct (Hch _ _ _ _ Hg HU Hr) as (Rk & _ & _ & _ & w4 & _ & _ & _ & _ & _ & Ew4 & _); eauto. }
    pose proof (eval_field_vals_length _ _ _ _ EV1) as Hl1; pose proof (eval_field_vals_length _ _ _ _ EV2) as Hl2.
    pose proof (eval_field_vals_length _ _ _ _ EV3) as Hl3; pose proof (eval_field_vals_length _ _ _ _ EV4) as Hl4.
    rewrite List.length_map in Hl1, Hl2, Hl3, Hl4.
    (** Each field's values in the lists: the proofs at a propositional
        field, the related values at a relevant one *)
    assert (Hfv : forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
               exists v1 v2 v3 v4, List.nth_error V1 k = Some v1 /\ List.nth_error V2 k = Some v2 /\
                 List.nth_error V3 k = Some v3 /\ List.nth_error V4 k = Some v4 /\
                 (record_field_rel R k = propositional -> v1 = ⋆ᵈ /\ v2 = ⋆ᵈ /\ v3 = ⋆ᵈ /\ v4 = ⋆ᵈ) /\
                 (record_field_rel R k = relevant -> exists Rk b (jb : nat), Rk v1 v2 /\ Rk v2 v3 /\ Rk v3 v4 /\
                    ⟦ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] ⟧ ρσ ↘ b /\ DF b ≈ b ∈ per_univ_elem jb ↘ Rk)).
    { intros k f M U Hk Hfk.
      assert (HM1 : List.nth_error (List.map (fun f => (snd f)[σ]) fs) k = Some M[σ]) by (rewrite List.nth_error_map, Hk; reflexivity).
      assert (HM2 : List.nth_error (List.map snd fs) k = Some M) by (rewrite List.nth_error_map, Hk; reflexivity).
      assert (HM4 : List.nth_error (List.map (fun f => (snd f)[σ']) fs) k = Some M[σ']) by (rewrite List.nth_error_map, Hk; reflexivity).
      destruct (eval_field_vals_nth _ _ _ _ EV1 _ _ HM1) as (v1 & Hv1 & Ev1 & Pv1).
      destruct (eval_field_vals_nth _ _ _ _ EV2 _ _ HM2) as (v2 & Hv2 & Ev2 & Pv2).
      destruct (eval_field_vals_nth _ _ _ _ EV3 _ _ HM2) as (v3 & Hv3 & Ev3 & Pv3).
      destruct (eval_field_vals_nth _ _ _ _ EV4 _ _ HM4) as (v4 & Hv4 & Ev4 & Pv4).
      exists v1, v2, v3, v4; do 4 (split; [ assumption |]).
      split; [ intros Hp; repeat split; [ apply Pv1 | apply Pv2 | apply Pv3 | apply Pv4 ]; exact Hp |].
      intros Hr.
      destruct (Hch _ _ _ _ Hk Hfk Hr) as (Rk & w1 & w2 & w3 & w4 & b & jb & Ew1 & Ew2 & Ew3 & Ew4 & Hwch & Eb & Hbb).
      assert (v1 = w1) as -> by (eapply functional_eval_exp; [ exact (Ev1 Hr) | exact Ew1 ]).
      assert (v2 = w2) as -> by (eapply functional_eval_exp; [ exact (Ev2 Hr) | exact Ew2 ]).
      assert (v3 = w3) as -> by (eapply functional_eval_exp; [ exact (Ev3 Hr) | exact Ew3 ]).
      assert (v4 = w4) as -> by (eapply functional_eval_exp; [ exact (Ev4 Hr) | exact Ew4 ]).
      exists Rk, b, jb; destruct Hwch as (Hw12 & Hw23 & Hw34); repeat split; assumption. }
    (** The canonical relations at the middle prefixes: a relevant field's,
        the relation of its instance type; a propositional field's, relating
        the proofs *)
    assert (Hcan : forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
               tele_prefix_rel (canon_fields_rel R ns2) k (List.firstn k V2) (List.firstn k V3) ->
               (record_field_rel R k = propositional -> canon_fields_rel R ns2 k (List.firstn k V2) ⋆ᵈ ⋆ᵈ) /\
               (forall Rk b (jb : nat), ⟦ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] ⟧ ρσ ↘ b ->
                  DF b ≈ b ∈ per_univ_elem jb ↘ Rk -> (Rk <~> canon_fields_rel R ns2 k (List.firstn k V2)))).
    { intros k f M U Hk Hfk Hpre.
      assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
      pose proof (prefix_gargs _ _ _ _ k Hgp Hln2 Ha ltac:(lia) Hpre) as Hgj.
      assert (Hlk : List.length (List.firstn k V2) = k) by (rewrite List.length_firstn; lia).
      split.
      - intros Hp; apply (field_canon_proof _ _ _ _ _ Hfk Hp Hln2 Hlk).
        pose proof (Hgj k (le_n _)) as H; rewrite List.firstn_firstn, Nat.min_id in H; exact H.
      - intros Rk b jb Eb Hbb.
        assert (HlM : List.length (Ns ++ List.firstn k (List.map snd fs)) = k + List.length (record_params R))
          by (rewrite List.length_app, List.length_firstn, List.length_map; lia).
        assert (Hev_k : ⟦ sb_of_list Id (Ns ++ List.firstn k (List.map snd fs)) : (record_fctx R k ++ record_params R) ++ Γ ⟧s
                          ρσ ↘ env_args ρσ (ns2 ++ List.firstn k V2)).
        { apply (tuple_inst_eval Γ RΓ ρσ Ns ns2 _ _ k HΓ HRΓ Hρσρσ Hn Ens2 ltac:(lia));
            [ rewrite List.length_firstn, List.length_map; lia | exact (eval_field_vals_firstn _ _ _ _ EV2 k) |].
          exact Hgj. }
        destruct (field_inst_link_sub Γ k f U _ RΓ ρσ (ns2 ++ List.firstn k V2) Hfk HΓ HRΓ HlM
                    (tuple_insts Γ Ns fs Hn HNs Hfs HMs k ltac:(lia)) Hρσρσ
                    ltac:(rewrite !List.length_app, !List.length_firstn, List.length_map; lia) Hev_k)
          as (jb' & t & u & Et & Eu & [Ru HRu]).
        assert (t = b) as -> by (eapply functional_eval_exp; eassumption).
        assert (ERk : Rk <~> Ru) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hbb HRu).
        pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRu) HRu) as HRuu.
        unfold canon_fields_rel; rewrite (nth_ftyp_eq _ _ _ _ Hfk).
        etransitivity; [ exact ERk | exact (per_head_iff Eu Eu HRuu) ]. }
    (** The links of the fields *)
    assert (H23 : tele_rel (canon_fields_rel R ns2) (record_fields R) V2 V3).
    { apply tele_rel_build; [ lia | lia |].
      intros k x y Hx Hy Hpre.
      destruct (nth_error_lt_some' fs k ltac:(rewrite <- Hl2; exact (nth_error_lt_length _ _ _ Hx))) as [[f M] Hk].
      destruct (Hnm _ _ _ Hk) as [U Hfk].
      destruct (Hfv _ _ _ _ Hk Hfk) as (v1 & v2 & v3 & v4 & Hv1 & Hv2 & Hv3 & Hv4 & Hprop & Hrel).
      rewrite Hx in Hv2; injection Hv2 as <-; rewrite Hy in Hv3; injection Hv3 as <-.
      destruct (Hcan _ _ _ _ Hk Hfk Hpre) as [Cp Cr].
      destruct (record_field_rel R k) eqn:Er.
      - destruct (Hrel eq_refl) as (Rk & b & jb & _ & H23 & _ & Eb & Hbb); apply (Cr _ _ _ Eb Hbb); exact H23.
      - destruct (Hprop eq_refl) as (_ & -> & -> & _); exact (Cp eq_refl). }
    assert (H12 : tele_rel (canon_fields_rel R ns2) (record_fields R) V1 V2).
    { apply tele_rel_build; [ lia | lia |].
      intros k x y Hx Hy Hpre.
      destruct (nth_error_lt_some' fs k ltac:(rewrite <- Hl1; exact (nth_error_lt_length _ _ _ Hx))) as [[f M] Hk].
      destruct (Hnm _ _ _ Hk) as [U Hfk].
      destruct (Hfv _ _ _ _ Hk Hfk) as (v1 & v2 & v3 & v4 & Hv1 & Hv2 & Hv3 & Hv4 & Hprop & Hrel).
      rewrite Hx in Hv1; injection Hv1 as <-; rewrite Hy in Hv2; injection Hv2 as <-.
      assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
      pose proof (tele_prefix_rel_of_full _ _ _ _ k H23 ltac:(lia)) as Hpre23.
      destruct (Hcan _ _ _ _ Hk Hfk Hpre23) as [Cp Cr].
      apply (HfI _ _ _ _ _ Hfk Hpre).
      destruct (record_field_rel R k) eqn:Er.
      - destruct (Hrel eq_refl) as (Rk & b & jb & H12 & _ & _ & Eb & Hbb); apply (Cr _ _ _ Eb Hbb); exact H12.
      - destruct (Hprop eq_refl) as (-> & -> & _ & _); exact (Cp eq_refl). }
    assert (H34 : tele_rel (canon_fields_rel R ns2) (record_fields R) V3 V4).
    { rewrite tele_rel_iff; split; [ lia | split; [ lia |] ].
      intros k x y Hx Hy.
      destruct (nth_error_lt_some' fs k ltac:(rewrite <- Hl3; exact (nth_error_lt_length _ _ _ Hx))) as [[f M] Hk].
      destruct (Hnm _ _ _ Hk) as [U Hfk].
      destruct (Hfv _ _ _ _ Hk Hfk) as (v1 & v2 & v3 & v4 & Hv1 & Hv2 & Hv3 & Hv4 & Hprop & Hrel).
      rewrite Hx in Hv3; injection Hv3 as <-; rewrite Hy in Hv4; injection Hv4 as <-.
      assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
      pose proof (tele_prefix_rel_of_full _ _ _ _ k H23 ltac:(lia)) as Hpre.
      destruct (Hcan _ _ _ _ Hk Hfk Hpre) as [Cp Cr].
      apply (HfI _ _ _ _ _ Hfk Hpre).
      destruct (record_field_rel R k) eqn:Er.
      - destruct (Hrel eq_refl) as (Rk & b & jb & _ & _ & H34 & Eb & Hbb); apply (Cr _ _ _ Eb Hbb); exact H34.
      - destruct (Hprop eq_refl) as (_ & _ & -> & ->); exact (Cp eq_refl). }
    (** The record types at the four environments are type formers *)
    pose proof Htch as (H12t & H23t & H34t).
    destruct (per_univ_elem_record_right _ _ _ _ _ HRx) as [ns2' ->].
    destruct (per_univ_elem_record_right _ _ _ _ _ H12t) as [ns1 ->].
    destruct (per_univ_elem_record_left _ _ _ _ _ H23t) as [ns3 ->].
    destruct (per_univ_elem_record_left _ _ _ _ _ H34t) as [ns4 ->].
    (** The four tuples *)
    assert (Hn1 : List.map fst (List.map (fun f => (fst f, (snd f)[σ])) fs) = List.map fst fs) by apply tuple_names_sub.
    assert (Hn4 : List.map fst (List.map (fun f => (fst f, (snd f)[σ'])) fs) = List.map fst fs) by apply tuple_names_sub.
    assert (Hs1 : List.map snd (List.map (fun f => (fst f, (snd f)[σ])) fs) = List.map (fun f => (snd f)[σ]) fs)
      by (rewrite List.map_map; reflexivity).
    assert (Hs4 : List.map snd (List.map (fun f => (fst f, (snd f)[σ'])) fs) = List.map (fun f => (snd f)[σ']) fs)
      by (rewrite List.map_map; reflexivity).
    exists RT; split.
    - apply (mk_rel_exp (d_record p ns1) (d_record p ns2') (d_record p ns3) (d_record p ns4));
        [ exact Et1 | exact Et2 | exact Et3 | exact Et4 | exact Htch ].
    - right; apply (mk_rel_exp (d_tuple (List.combine (List.map fst fs) V1)) (d_tuple (List.combine (List.map fst fs) V2))
                        (d_tuple (List.combine (List.map fst fs) V3)) (d_tuple (List.combine (List.map fst fs) V4))).
      + cbn [exp_sub]; rewrite <- Hn1; eapply eval_exp_tuple; [ exact Et1 | exact Hl | rewrite Hs1; exact EV1 ].
      + eapply eval_exp_tuple; [ exact Et2 | exact Hl | exact EV2 ].
      + eapply eval_exp_tuple; [ exact Et3 | exact Hl | exact EV3 ].
      + cbn [exp_sub]; rewrite <- Hn4; eapply eval_exp_tuple; [ exact Et4 | exact Hl | rewrite Hs4; exact EV4 ].
      + apply rel_chain_4; apply ERT, HE.
        * exact (mk_record_rel _ _ _ _ V1 V2 (tuple_projs _ V1 Hfs ltac:(lia)) (tuple_projs _ V2 Hfs ltac:(lia)) H12).
        * exact (mk_record_rel _ _ _ _ V2 V3 (tuple_projs _ V2 Hfs ltac:(lia)) (tuple_projs _ V3 Hfs ltac:(lia)) H23).
        * exact (mk_record_rel _ _ _ _ V3 V4 (tuple_projs _ V3 Hfs ltac:(lia)) (tuple_projs _ V4 Hfs ltac:(lia)) H34).
  Qed.

  (** The element relation of the record type at parameters, at two
      related environments: the canonical one at the left values. *)
  Lemma record_typ_at_envs : forall Γ Ns RΓ ρ ρ', ⊨ Γ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
      (exists i : nat, Γ ⊨ apps_exp (a_record p) Ns : Typeω@i) -> List.length Ns = List.length (record_params R) ->
      RΓ ρ ρ' ->
      exists ns, ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns /\
        (per_head (apps_exp (a_record p) Ns) (apps_exp (a_record p) Ns) ρ ρ' <~> record_rel R (canon_fields_rel R ns)).
  Proof.
    intros * HΓ HRΓ [i HA] Hn Hρ.
    destruct (rel_exp_of_typ_inversion_simple_at HRΓ HA _ _ Hρ) as (a & a' & Ea & Ea' & [X HX]).
    destruct (eval_record_apps_inv _ _ _ Ea Hn) as (ns & Ens & ->).
    pose proof (record_typ_facts _ _ _ _ (per_univ_sym _ _ _ _ HX)) as Hf.
    pose proof (per_head_iff Ea Ea' HX) as E1.
    assert (E2 : X <~> record_rel R (canon_fields_rel R ns)).
    { pose proof (per_univ_trans _ _ _ _ _ _ HX (per_univ_sym _ _ _ _ HX)) as Hd.
      etransitivity; [ eapply per_univ_elem_right_irrel; [ exact HX | exact Hd ] |].
      exact (record_canon_facts_elem _ _ _ _ _ (per_univ_elem_record_facts _ _ _ _ _ _ Hl Hd)). }
    exists ns; split; [ exact Ens | etransitivity; [ symmetry; exact E1 | exact E2 ] ].
  Qed.

  (** η: an element is equal to the tuple of its projections. *)
  Lemma rel_exp_under_ctx_record_eta : forall Γ M Ns, ⊨ Γ ->
      Γ ⊨ M : apps_exp (a_record p) Ns -> List.length Ns = List.length (record_params R) ->
      Γ ⊨ a_tuple (apps_exp (a_record p) Ns) (record_eta_fields R M) : apps_exp (a_record p) Ns ->
      Γ ⊨ M ≈ a_tuple (apps_exp (a_record p) Ns) (record_eta_fields R M) : apps_exp (a_record p) Ns.
  Proof.
    intros * HΓ HM Hn Ht.
    destruct (rel_ctx_wf_per_ctx_env HΓ) as [RΓ HRΓ].
    apply (rel_exp_under_ctx_of_simple HRΓ HM Ht).
    intros ρ ρ' Hρ; right.
    (** The record type at the two environments, and its element relation:
        the canonical one, whose fields are of their sorts. *)
    destruct (presup_rel_exp_under_ctx HM) as [iT HT0].
    destruct (rel_type_inversion_simple_at HRΓ HT0 _ _ Hρ) as (a & a' & Ea & Ea' & [X HX]).
    destruct (eval_record_apps_inv _ _ _ Ea Hn) as (ns & _ & ->).
    destruct (eval_record_apps_inv _ _ _ Ea' Hn) as (ns' & _ & ->).
    pose proof (per_univ_elem_record_facts _ _ _ _ _ _ Hl HX) as [_ Hln _ _ HfP HfI HfE HfS HEX].
    pose proof (per_head_iff Ea Ea' HX) as EH.
    destruct (rel_exp_under_ctx_simple_at HRΓ HM _ _ Hρ) as [(a0 & Ea0 & Hp) | (m & m' & Em & Em' & Hmm)].
    { assert (a0 = d_record p ns) as -> by (eapply functional_eval_exp; eassumption); discriminate. }
    apply EH, HEX in Hmm; destruct Hmm as [P P' HP HP' Hrel].
    pose proof (List.Forall2_length HP) as HlP; pose proof (List.Forall2_length HP') as HlP'.
    (** The projections at the propositional fields are the proofs. *)
    assert (HP'p : forall k f U v', List.nth_error (record_fields R) k = Some (f, U) -> record_field_rel R k = propositional ->
                     List.nth_error P' k = Some v' -> v' = ⋆ᵈ).
    { intros k f U v' Hk Hr Hv'.
      assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hk).
      destruct (nth_error_lt_some' P k ltac:(lia)) as [v Hv].
      pose proof Hrel as H; rewrite tele_rel_iff in H; destruct H as (_ & _ & H); pose proof (H _ _ _ Hv Hv') as Hcv.
      pose proof (tele_prefix_rel_of_full _ _ _ _ k Hrel ltac:(lia)) as Hpre.
      destruct (HfS _ _ _ _ _ Hk Hpre) as (u & Eu & Hu); rewrite Hr in Hu.
      destruct (HfE _ _ _ _ _ Hk Hpre) as [u0 u0' Eu0 Eu0' HRu].
      assert (u0 = u) as -> by (eapply functional_eval_exp; eassumption).
      exact (proj2 (proj1 (per_univ_elem_propositional _ _ _ _ HRu Hu _ _) Hcv)). }
    (** The tuple of the projections at the right environment: by the
        fields' sorts, the projections of the right value. *)
    assert (Ew : eval_field_vals gc_deps gc_stack (record_field_relevance R) (List.map snd (record_eta_fields R M)) ρ' P').
    { apply eval_field_vals_of_nth; [ unfold record_eta_fields; rewrite !List.length_map; lia |].
      intros k N v HN Hv.
      unfold record_eta_fields in HN; rewrite List.map_map, List.nth_error_map in HN.
      destruct (List.nth_error (record_fields R) k) as [[f U] |] eqn:Hk; cbn in HN; [ injection HN as <- | discriminate ].
      split.
      - intros _; econstructor; [ exact Em' | exact (Forall2_nth_both _ _ _ _ _ _ HP' Hk Hv) ].
      - intros Hr; exact (HP'p _ _ _ _ Hk Hr Hv). }
    exists m, (d_tuple (List.combine (List.map fst (record_eta_fields R M)) P')).
    split; [ exact Em | split; [ eapply eval_exp_tuple; [ exact Ea' | exact Hl | exact Ew ] |] ].
    apply EH, HEX; refine (mk_record_rel _ _ _ _ P P' HP (tuple_projs _ P' (record_eta_fields_names R M) ltac:(lia)) Hrel).
  Qed.

  (** Tuples of equal fields are equal. *)
  Lemma rel_exp_under_ctx_tuple_cong : forall Γ T T' Ns (fs fs' : list (String.string * exp)) (i : nat), ⊨ Γ ->
      Γ ⊨ a_tuple T fs : T -> Γ ⊨ T ≈ T' : Typeω@i -> Γ ⊨ T ≈ apps_exp (a_record p) Ns : Typeω@i ->
      List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A -> Γ ⊨ N : A) ->
      List.map fst fs = List.map fst (record_fields R) -> List.map fst fs' = List.map fst fs ->
      (forall k f M M' U, List.nth_error fs k = Some (f, M) -> List.nth_error fs' k = Some (f, M') ->
         List.nth_error (record_fields R) k = Some (f, U) ->
         Γ ⊨ M ≈ M' : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
      Γ ⊨ a_tuple T' fs' : T ->
      Γ ⊨ a_tuple T fs ≈ a_tuple T' fs' : T.
  Proof.
    intros * HΓ Ht HTT HTeq Hn HNs Hfs Hfs' HMM Ht'.
    assert (Hlf : List.length fs = List.length (record_fields R))
      by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
    assert (Hlf' : List.length fs' = List.length fs)
      by (rewrite <- (List.length_map fst fs'), <- (List.length_map fst fs), Hfs'; reflexivity).
    assert (Hfs'' : List.map fst fs' = List.map fst (record_fields R)) by (rewrite Hfs'; exact Hfs).
    (** The left fields are valid. *)
    assert (HMs : forall k0 f0 M0 U0, List.nth_error fs k0 = Some (f0, M0) -> List.nth_error (record_fields R) k0 = Some (f0, U0) ->
               Γ ⊨ M0 : U0[sb_of_list Id (Ns ++ List.firstn k0 (List.map snd fs))]).
    { intros k0 f0 M0 U0 Hk0 Hfk0.
      destruct (nth_error_lt_some' fs' k0 ltac:(rewrite Hlf'; exact (nth_error_lt_length _ _ _ Hk0))) as [[g M0'] Hk0'].
      assert (g = f0) as ->.
      { pose proof (List.map_nth_error fst _ _ Hk0') as E1; pose proof (List.map_nth_error fst _ _ Hk0) as E2.
        rewrite Hfs' in E1; rewrite E1 in E2; injection E2 as ->; reflexivity. }
      exact (rel_exp_under_ctx_refl_left (HMM _ _ _ _ _ Hk0 Hk0' Hfk0)). }
    (** A relevant field's instance type is a type of a universe. *)
    assert (HUk : forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
               record_field_rel R k = relevant ->
               exists j : nat, Γ ⊨ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] : Typeω@j).
    { intros k f M U Hk Hfk Hr.
      assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
      assert (HCa : tele_ass (record_fctx R k ++ record_params R)) by (apply record_fctx_params_ass; exact Hass).
      assert (HC : ⊨ record_fctx R k ++ record_params R) by (apply record_fctx_sem; lia).
      assert (HlC : List.length (Ns ++ List.firstn k (List.map snd fs)) = List.length (record_fctx R k ++ record_params R))
        by (rewrite !List.length_app, List.length_firstn, List.length_map, length_record_fctx by lia; lia).
      pose proof (gsub_closed_inst _ Γ _ HCa HC HΓ HlC (tuple_insts Γ Ns fs Hn HNs Hfs HMs k ltac:(lia))) as Hg.
      destruct (field_typ_large _ _ _ Hfk Hr) as [j HU].
      exists j; pose proof (rel_exp_under_ctx_gsub Hg (closed_app_valid _ _ _ _ _ HCa HC HΓ HU)) as H; cbn [exp_sub] in H; exact H. }
    destruct (rel_ctx_wf_per_ctx_env HΓ) as [RΓ HRΓ].
    assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
    apply (rel_exp_under_ctx_of_simple HRΓ Ht Ht').
    intros ρ ρ' Hρ; right.
    assert (Hρρ : RΓ ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
    (** The relation of [T] at the two environments: the canonical record
        relation at the parameters' left values *)
    pose proof (rel_exp_under_ctx_refl_left HTeq) as HTl.
    destruct (rel_exp_of_typ_inversion_simple_at HRΓ HTl _ _ Hρ) as (t & t' & Et & Et' & [RT HRT]).
    destruct (rel_exp_of_typ_inversion_simple_at HRΓ HTeq _ _ Hρρ) as (t0 & a & Et0 & Ea & [Rx HRx]).
    assert (t0 = t) as -> by (eapply functional_eval_exp; eassumption).
    destruct (eval_record_apps_inv _ _ _ Ea Hn) as (ns & Ens & ->).
    pose proof (record_typ_facts _ _ _ _ HRx) as [_ Hlns _ _ _ _ _ HfS HE].
    assert (EH : per_head T T ρ ρ' <~> record_rel R (canon_fields_rel R ns)).
    { etransitivity; [ symmetry; exact (per_head_iff Et Et' HRT) |].
      etransitivity; [ eapply per_univ_elem_right_irrel; [ exact HRT | exact HRx ] | exact HE ]. }
    pose proof (params_inst_gargs Γ Ns RΓ ρ ρ ns ns HΓ HRΓ Hn HNs Hρρ Ens Ens) as Hgp.
    destruct (sort_tele_value _ _ record_params_sem HS _ Hgp Hlns) as [a0 Ha0].
    (** The two annotations evaluate to record type formers. *)
    destruct (per_univ_elem_record_right _ _ _ _ _ HRx) as [ns1 ->].
    destruct (rel_exp_of_typ_inversion_simple_at HRΓ HTT _ _ Hρ) as (t1 & t1' & Et1 & Et1' & [R1 HR1]).
    assert (t1 = d_record p ns1) as -> by (eapply functional_eval_exp; eassumption).
    destruct (per_univ_elem_record_left _ _ _ _ _ HR1) as [ns1' ->].
    (** Each relevant field: its values at the two environments, related at
        its instance type *)
    assert (Hch : forall k f M M' U, List.nth_error fs k = Some (f, M) -> List.nth_error fs' k = Some (f, M') ->
               List.nth_error (record_fields R) k = Some (f, U) -> record_field_rel R k = relevant ->
               exists v v' b b' Rb (jb : nat), ⟦ M ⟧ ρ ↘ v /\ ⟦ M' ⟧ ρ' ↘ v' /\
                 ⟦ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] ⟧ ρ ↘ b /\
                 ⟦ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] ⟧ ρ' ↘ b' /\
                 DF b ≈ b' ∈ per_univ_elem jb ↘ Rb /\ Rb v v').
    { intros k f M M' U Hk Hk' Hfk Hr.
      pose proof (HMM _ _ _ _ _ Hk Hk' Hfk) as HMk.
      destruct (HUk _ _ _ _ Hk Hfk Hr) as [jU HUτ].
      destruct (rel_exp_of_typ_inversion_simple_at HRΓ HUτ _ _ Hρ) as (b & b' & Eb & Eb' & [Rb HRb]).
      destruct (rel_exp_under_ctx_simple_at HRΓ HMk _ _ Hρ) as [(a1 & Ea1 & Hp) | (v & v' & Ev & Ev' & Hvv)].
      { exfalso; destruct (rel_exp_of_typ_relevant_at HRΓ HUτ _ _ Hρ) as (b0 & Eb0 & Hr0).
        assert (a1 = b0) as -> by (eapply functional_eval_exp; eassumption); congruence. }
      apply (per_head_iff Eb Eb' HRb) in Hvv.
      exists v, v', b, b', Rb, jU; repeat split; assumption. }
    (** The values of the fields, by their sorts *)
    assert (Hnm : forall m g M, List.nth_error fs m = Some (g, M) ->
               exists U M', List.nth_error (record_fields R) m = Some (g, U) /\ List.nth_error fs' m = Some (g, M')).
    { intros m g M Hm.
      destruct (nth_error_lt_some' (record_fields R) m) as [[g' U] Hm']; [ rewrite <- Hlf; exact (nth_error_lt_length _ _ _ Hm) |].
      destruct (nth_error_lt_some' fs' m) as [[g'' M'] Hm'']; [ rewrite Hlf'; exact (nth_error_lt_length _ _ _ Hm) |].
      pose proof (List.map_nth_error fst _ _ Hm) as E1; pose proof (List.map_nth_error fst _ _ Hm') as E2.
      pose proof (List.map_nth_error fst _ _ Hm'') as E3.
      rewrite Hfs in E1; rewrite E1 in E2; injection E2 as ->.
      rewrite Hfs'' in E3; rewrite (List.map_nth_error fst _ _ Hm') in E3; injection E3 as ->.
      exists U, M'; split; assumption. }
    set (rs := record_field_relevance R).
    destruct (eval_field_vals_each (List.map snd fs) rs ρ) as [V EV].
    { intros m M Hm Hr; rewrite List.nth_error_map in Hm.
      destruct (List.nth_error fs m) as [[g M0] |] eqn:Hg; cbn in Hm; [ injection Hm as <- | discriminate ].
      destruct (Hnm _ _ _ Hg) as (U & M' & HU & HM'); destruct (Hch _ _ _ _ _ Hg HM' HU Hr) as (v & _ & _ & _ & _ & _ & Ev & _); eauto. }
    destruct (eval_field_vals_each (List.map snd fs') rs ρ') as [V' EV'].
    { intros m M' Hm Hr; rewrite List.nth_error_map in Hm.
      destruct (List.nth_error fs' m) as [[g M0'] |] eqn:Hg'; cbn in Hm; [ injection Hm as <- | discriminate ].
      destruct (nth_error_lt_some' fs m) as [[g0 M0] Hg]; [ rewrite <- Hlf'; exact (nth_error_lt_length _ _ _ Hg') |].
      destruct (Hnm _ _ _ Hg) as (U & M1 & HU & HM1); rewrite Hg' in HM1; injection HM1 as <- <-.
      destruct (Hch _ _ _ _ _ Hg Hg' HU Hr) as (_ & v' & _ & _ & _ & _ & _ & Ev' & _); eauto. }
    pose proof (eval_field_vals_length _ _ _ _ EV) as HlV; pose proof (eval_field_vals_length _ _ _ _ EV') as HlV'.
    rewrite List.length_map in HlV, HlV'.
    (** Each field's values in the lists *)
    assert (Hfv : forall k f M M' U, List.nth_error fs k = Some (f, M) -> List.nth_error fs' k = Some (f, M') ->
               List.nth_error (record_fields R) k = Some (f, U) ->
               exists v v', List.nth_error V k = Some v /\ List.nth_error V' k = Some v' /\
                 (record_field_rel R k = propositional -> v = ⋆ᵈ /\ v' = ⋆ᵈ) /\
                 (record_field_rel R k = relevant -> exists b b' Rb (jb : nat),
                    ⟦ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] ⟧ ρ ↘ b /\
                    ⟦ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] ⟧ ρ' ↘ b' /\
                    DF b ≈ b' ∈ per_univ_elem jb ↘ Rb /\ Rb v v')).
    { intros k f M M' U Hk Hk' Hfk.
      assert (HM1 : List.nth_error (List.map snd fs) k = Some M) by (rewrite List.nth_error_map, Hk; reflexivity).
      assert (HM2 : List.nth_error (List.map snd fs') k = Some M') by (rewrite List.nth_error_map, Hk'; reflexivity).
      destruct (eval_field_vals_nth _ _ _ _ EV _ _ HM1) as (v & Hv & Ev & Pv).
      destruct (eval_field_vals_nth _ _ _ _ EV' _ _ HM2) as (v' & Hv' & Ev' & Pv').
      exists v, v'; split; [ exact Hv | split; [ exact Hv' |] ].
      split; [ intros Hp; split; [ apply Pv | apply Pv' ]; exact Hp |].
      intros Hr.
      destruct (Hch _ _ _ _ _ Hk Hk' Hfk Hr) as (w & w' & b & b' & Rb & jb & Ew & Ew' & Eb & Eb' & HRb & Hww).
      assert (v = w) as -> by (eapply functional_eval_exp; [ exact (Ev Hr) | exact Ew ]).
      assert (v' = w') as -> by (eapply functional_eval_exp; [ exact (Ev' Hr) | exact Ew' ]).
      exists b, b', Rb, jb; repeat split; assumption. }
    (** The canonical relations at the left prefixes *)
    assert (Hcan : forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
               tele_prefix_rel (canon_fields_rel R ns) k (List.firstn k V) (List.firstn k V') ->
               (record_field_rel R k = propositional -> canon_fields_rel R ns k (List.firstn k V) ⋆ᵈ ⋆ᵈ) /\
               (forall b b' Rb (jb : nat), ⟦ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] ⟧ ρ ↘ b ->
                  DF b ≈ b' ∈ per_univ_elem jb ↘ Rb -> (Rb <~> canon_fields_rel R ns k (List.firstn k V)))).
    { intros k f M U Hk Hfk Hpre.
      assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
      pose proof (prefix_gargs _ _ _ _ k Hgp Hlns Ha0 ltac:(lia) Hpre) as Hgj.
      assert (Hlk : List.length (List.firstn k V) = k) by (rewrite List.length_firstn; lia).
      split.
      - intros Hp; apply (field_canon_proof _ _ _ _ _ Hfk Hp Hlns Hlk).
        pose proof (Hgj k (le_n _)) as H; rewrite List.firstn_firstn, Nat.min_id in H; exact H.
      - intros b b' Rb jb Eb HRb.
        assert (HlM : List.length (Ns ++ List.firstn k (List.map snd fs)) = k + List.length (record_params R))
          by (rewrite List.length_app, List.length_firstn, List.length_map; lia).
        assert (Hev_k : ⟦ sb_of_list Id (Ns ++ List.firstn k (List.map snd fs)) : (record_fctx R k ++ record_params R) ++ Γ ⟧s
                          ρ ↘ env_args ρ (ns ++ List.firstn k V)).
        { apply (tuple_inst_eval Γ RΓ ρ Ns ns _ _ k HΓ HRΓ Hρρ Hn Ens ltac:(lia));
            [ rewrite List.length_firstn, List.length_map; lia | exact (eval_field_vals_firstn _ _ _ _ EV k) | exact Hgj ]. }
        destruct (field_inst_link_sub Γ k f U _ RΓ ρ (ns ++ List.firstn k V) Hfk HΓ HRΓ HlM
                    (tuple_insts Γ Ns fs Hn HNs Hfs HMs k ltac:(lia)) Hρρ
                    ltac:(rewrite !List.length_app, !List.length_firstn, List.length_map; lia) Hev_k)
          as (jb' & t2 & u & Et2 & Eu & [Ru HRu]).
        assert (t2 = b) as -> by (eapply functional_eval_exp; eassumption).
        assert (ERb : Rb <~> Ru) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRb HRu).
        pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRu) HRu) as HRuu.
        unfold canon_fields_rel; rewrite (nth_ftyp_eq _ _ _ _ Hfk).
        etransitivity; [ exact ERb | exact (per_head_iff Eu Eu HRuu) ]. }
    exists (d_tuple (List.combine (List.map fst fs) V)), (d_tuple (List.combine (List.map fst fs') V')).
    split; [ eapply eval_exp_tuple; [ exact Et | exact Hl | exact EV ] |].
    split; [ eapply eval_exp_tuple; [ exact Et1' | exact Hl | exact EV' ] |].
    apply EH; apply (mk_record_rel _ _ _ _ V V' (tuple_projs _ V Hfs ltac:(lia)) (tuple_projs _ V' Hfs'' ltac:(lia))).
    apply tele_rel_build; [ lia | lia |].
    intros k x y Hx Hy Hpre.
    destruct (nth_error_lt_some' fs k ltac:(rewrite <- HlV; exact (nth_error_lt_length _ _ _ Hx))) as [[f M] Hk].
    destruct (Hnm _ _ _ Hk) as (U & M' & HU & HM').
    destruct (Hfv _ _ _ _ _ Hk HM' HU) as (v & v' & Hv & Hv' & Hprop & Hrel).
    rewrite Hx in Hv; injection Hv as <-; rewrite Hy in Hv'; injection Hv' as <-.
    destruct (Hcan _ _ _ _ Hk HU Hpre) as [Cp Cr].
    destruct (record_field_rel R k) eqn:Er.
    - destruct (Hrel eq_refl) as (b & b' & Rb & jb & Eb & _ & HRb & Hxy); apply (Cr _ _ _ _ Eb HRb); exact Hxy.
    - destruct (Hprop eq_refl) as (-> & ->); exact (Cp eq_refl).
  Qed.
End RecordModel.

(** ** Field-β

    The field of a tuple is its field of that name: at a relevant field,
    its value is the field's. *)

(** The record type former, applied, is one. *)
Lemma eval_apps_record_shape : forall ys p xs a, $*| d_record p xs & ys | gc_deps ⍮ gc_stack ↘ a ->
    exists zs, a = d_record p zs.
Proof.
  induction ys as [| y ys IH]; intros * H; inversion H; subst; [ eauto |].
  match goal with Ha : $| d_record _ _ & _ | _ ⍮ _ ↘ _ |- _ => inversion Ha; subst end.
  eapply IH; eassumption.
Qed.

(** The value of the first field so named is at its position. *)
Lemma field_lookup_combine_at : forall (fs : list (String.string * exp)) (vs : list domain) f k x,
    List.length vs = List.length fs -> field_index fs f = Some k ->
    field_lookup (List.combine (List.map fst fs) vs) f = Some x -> List.nth_error vs k = Some x.
Proof.
  induction fs as [| [g N] fs IH]; intros [| v vs] * Hl Hk Hx; cbn in Hl, Hk, Hx |- *; try discriminate.
  destruct (String.eqb f g); [ injection Hk as <-; injection Hx as <-; reflexivity |].
  destruct (field_index fs f) as [k0 |] eqn:E; cbn in Hk; [| discriminate ].
  injection Hk as <-; exact (IH vs f k0 x ltac:(lia) E Hx).
Qed.

Lemma rel_exp_under_ctx_field_beta : forall Γ T (fs : list (String.string * exp)) f M A p Ns R k (i : nat), ⊨ Γ ->
    Γ ⊨ T ≈ apps_exp (a_record p) Ns : Typeω@i -> record_lookup gc_deps gc_stack p = Some R ->
    field_index fs f = Some k -> record_field_rel R k = relevant ->
    Γ ⊨ a_proj f (a_tuple T fs) : A -> field_lookup fs f = Some M -> Γ ⊨ M : A ->
    Γ ⊨ a_proj f (a_tuple T fs) ≈ M : A.
Proof.
  intros * HΓ HTeq Hl Hk Hr HP HM HMv.
  destruct (rel_ctx_wf_per_ctx_env HΓ) as [RΓ HRΓ].
  assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
  apply (rel_exp_under_ctx_of_simple HRΓ HP HMv).
  intros ρ ρ' Hρ.
  assert (Hρρ : RΓ ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  destruct (rel_exp_under_ctx_simple_at HRΓ HP _ _ Hρρ) as [Hp | (x & _ & Ex & _ & _)]; [ left; exact Hp |].
  destruct (rel_exp_under_ctx_simple_at HRΓ HMv _ _ Hρ) as [Hp | (m & m' & Em & Em' & Hmm)]; [ left; exact Hp | right ].
  (** The annotation is the record type former at [ρ]. *)
  destruct (rel_exp_of_typ_inversion_simple_at HRΓ HTeq _ _ Hρρ) as (t & a & Et & Ea & [Rx HRx]).
  apply eval_apps_exp_record in Ea as (ns0 & _ & Hap).
  destruct (eval_apps_record_shape _ _ _ _ Hap) as [zs ->].
  destruct (per_univ_elem_record_right _ _ _ _ _ HRx) as [ns1 ->].
  (** The projection's value is the field's at its position. *)
  pose proof Ex as Ex0; inversion Ex0; subst.
  match goal with H : ⟦ a_tuple _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?t, Hp : eval_proj _ _ _ ?t _ |- _ =>
    inversion H; subst; inversion Hp; subst end.
  match goal with H : eval_exp _ _ T ρ (d_record ?p0 ?ns) |- _ =>
    assert_fails constr_eq p0 p; assert (Ep : d_record p ns1 = d_record p0 ns) by (eapply functional_eval_exp; [ exact Et | exact H ]);
    injection Ep as <- _ end.
  match goal with Hl0 : record_lookup _ _ p = Some ?R0 |- _ => assert_fails constr_eq R0 R;
    rewrite Hl in Hl0; injection Hl0 as <- end.
  match goal with Hvs : eval_field_vals _ _ _ _ _ ?vs, Hx : field_lookup (List.combine _ ?vs) f = Some x |- _ =>
    pose proof (field_lookup_combine_at _ _ _ _ _
                  ltac:(rewrite (eval_field_vals_length _ _ _ _ Hvs), List.length_map; reflexivity) Hk Hx) as Hxk;
    assert (HMk : List.nth_error (List.map snd fs) k = Some M)
      by (rewrite List.nth_error_map, (field_index_lookup _ _ _ _ Hk HM); reflexivity);
    destruct (eval_field_vals_nth _ _ _ _ Hvs _ _ HMk) as (v & Hv & Hrel & _)
  end.
  rewrite Hxk in Hv; injection Hv as <-.
  assert (x = m) as -> by (eapply functional_eval_exp; [ exact (Hrel Hr) | exact Em ]).
  exists m, m'; split; [ exact Ex | split; [ exact Em' | exact Hmm ] ].
Qed.

End Fixed_GCtx.
