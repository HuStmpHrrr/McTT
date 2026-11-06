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
From Mctt.Core.Completeness Require Import LetCases UnitCases LevelCases PropCases FunctionCases.
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
  Hypothesis (HCv : ⊨ C) (HCa : all_assumptions C) (Hsu : ind_sort_univ S) (HS : exists i : nat, C ⊨ S : Typeω@i).

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
        per_tele_args (List.rev (Pre ++ C)) nil nil (ns ++ zs) (ns' ++ zs') ->
        forall a, ⟦ S ⟧ env_tele nil (List.rev C) ns ↘ a ->
        exists t t', ⟦ T ⟧ env_tele (env_tele nil (List.rev C) ns) (List.rev Pre) zs ↘ t /\
          ⟦ T ⟧ env_tele (env_tele nil (List.rev C) ns') (List.rev Pre) zs' ↘ t' /\
          Dom t ≈ t' ∈ per_univ (univ_idx a).
  Proof.
    intros * HC HT * Hz Hz' Hu Hu' Hg a Ha.
    destruct (rel_ctx_wf_per_ctx_env HC) as [R HR].
    assert (HRe : R (env_tele (env_tele nil (List.rev C) ns) (List.rev Pre) zs) (env_tele (env_tele nil (List.rev C) ns') (List.rev Pre) zs')).
    { rewrite <- !env_tele_closed_app by assumption.
      apply (tele_args_env_rel _ _ _ _ _ _ HR HC); [ rewrite !List.length_app; lia | exact Hg ]. }
    assert (HPR : PER R) by (eapply per_env_PER; exact HR).
    assert (HRee : R (env_tele (env_tele nil (List.rev C) ns) (List.rev Pre) zs) (env_tele (env_tele nil (List.rev C) ns) (List.rev Pre) zs))
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
    rewrite <- Hz, eval_wk_shiftn_env_tele in Em'.
    assert (m' = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (m = b) as -> by (eapply functional_eval_exp; eassumption).
    cbn in Ex; inversion Ex; subst.
    basic_invert_per_univ_elem HRx.
    match goal with Hm : ?r b a, H : ?r <~> _ |- _ => apply H in Hm; destruct Hm as [[Rm HRm] _ _] end.
    destruct (per_univ_elem_univ _ _ _ _ HRm (sort_tele_wk_univ _ _ _ Eb)) as [Hidx _].
    exists t, t'; split; [ exact Et | split; [ exact Et' |] ].
    rewrite Hidx; apply ER0; exact Htt.
  Qed.

  (** The same at either kind of a field ([field_kind]): a proposition
      evaluates to related propositions, related at every universe. *)
  Lemma sort_rel_tele_rel : forall r Pre T, field_kind r -> ⊨ Pre ++ C ->
      Pre ++ C ⊨ T : abs_kind_sort r S[wk_shiftn (List.length Pre)]ʷ ->
      forall ns ns' zs zs', List.length zs = List.length Pre -> List.length zs' = List.length Pre ->
        List.length ns = List.length C -> List.length ns' = List.length C ->
        per_tele_args (List.rev (Pre ++ C)) nil nil (ns ++ zs) (ns' ++ zs') ->
        forall a, ⟦ S ⟧ env_tele nil (List.rev C) ns ↘ a ->
        exists t t', ⟦ T ⟧ env_tele (env_tele nil (List.rev C) ns) (List.rev Pre) zs ↘ t /\
          ⟦ T ⟧ env_tele (env_tele nil (List.rev C) ns') (List.rev Pre) zs' ↘ t' /\
          Dom t ≈ t' ∈ per_univ (univ_idx a).
  Proof.
    intros r Pre T Hr HC HT * Hz Hz' Hu Hu' Hg a Ha; destruct Hr; cbn [abs_kind_sort] in HT;
      [ exact (sort_tele_rel _ _ HC HT _ _ _ _ Hz Hz' Hu Hu' Hg a Ha) |].
    destruct (rel_ctx_wf_per_ctx_env HC) as [R HR].
    assert (HRe : R (env_tele (env_tele nil (List.rev C) ns) (List.rev Pre) zs) (env_tele (env_tele nil (List.rev C) ns') (List.rev Pre) zs')).
    { rewrite <- !env_tele_closed_app by assumption.
      apply (tele_args_env_rel _ _ _ _ _ _ HR HC); [ rewrite !List.length_app; lia | exact Hg ]. }
    destruct (rel_exp_of_prop_inversion_simple_at HR HT _ _ HRe) as (t & t' & Et & Et' & Hp).
    exists t, t'; split; [ exact Et | split; [ exact Et' |] ].
    exists per_proof; apply per_univ_elem_of_prop; exact Hp.
  Qed.

  (** Arguments related at a telescope of types at the sort or
      propositions, by the canonical relations, are arguments related at
      it. *)
  Lemma sort_tele_canon_tele_args : forall (ts : list centry) (Pre0 : ctx) (tr : nat -> list domain -> relation domain)
      ns ns' zs zs' a,
      all_assumptions ts ->
      List.length ns = List.length C -> List.length ns' = List.length C ->
      List.length zs = List.length Pre0 -> List.length zs' = List.length Pre0 ->
      per_tele_args (List.rev (Pre0 ++ C)) nil nil (ns ++ zs) (ns' ++ zs') ->
      ⟦ S ⟧ env_tele nil (List.rev C) ns ↘ a ->
      (forall j κ A, List.nth_error ts j = Some (ce_ass κ A) ->
         ⊨ List.rev (List.firstn j ts) ++ Pre0 ++ C /\
         exists r, field_kind r /\ List.rev (List.firstn j ts) ++ Pre0 ++ C ⊨ A : abs_kind_sort r S[wk_shiftn (j + List.length Pre0)]ʷ) ->
      (forall j κ A pre, List.nth_error ts j = Some (ce_ass κ A) -> List.length pre = j ->
         (tr j pre <~> per_head A A (env_tele (env_tele nil (List.rev C) ns) (List.rev Pre0 ++ ts) (zs ++ pre))
                                   (env_tele (env_tele nil (List.rev C) ns) (List.rev Pre0 ++ ts) (zs ++ pre)))) ->
      forall k vs vs', k <= List.length ts -> tele_prefix_rel tr k vs vs' ->
        per_tele_args (List.firstn k ts) (env_tele (env_tele nil (List.rev C) ns) (List.rev Pre0) zs)
          (env_tele (env_tele nil (List.rev C) ns') (List.rev Pre0) zs') vs vs'.
  Proof.
    intros * Hts Hu Hu' Hz Hz' Hg Ha Hv Htr k.
    induction k as [| k IH]; intros vs vs' Hk Hp.
    - rewrite tele_prefix_rel_iff in Hp; destruct Hp as (Hl & Hl' & _).
      destruct vs, vs'; cbn in *; try discriminate; constructor.
    - pose proof Hp as Hp0; rewrite tele_prefix_rel_iff in Hp0; destruct Hp0 as (Hl & Hl' & Hr).
      destruct (nth_error_lt_some' ts k ltac:(lia)) as [e He].
      assert (HA : exists κ A, e = ce_ass κ A)
        by (unfold all_assumptions in Hts; rewrite List.Forall_forall in Hts; apply Hts; eapply List.nth_error_In; exact He).
      destruct HA as (κ & A & ->).
      destruct (nth_error_lt_some' vs k ltac:(lia)) as [v Hv0].
      destruct (nth_error_lt_some' vs' k ltac:(lia)) as [v' Hv0'].
      rewrite (firstn_S_snoc _ _ _ He).
      assert (Hvs : vs = List.firstn k vs ++ v :: nil)
        by (rewrite <- (firstn_S_snoc _ _ _ Hv0), List.firstn_all2 by lia; reflexivity).
      assert (Hvs' : vs' = List.firstn k vs' ++ v' :: nil)
        by (rewrite <- (firstn_S_snoc _ _ _ Hv0'), List.firstn_all2 by lia; reflexivity).
      pose proof (IH _ _ ltac:(lia) (tele_prefix_rel_of_pre _ _ _ _ k Hp ltac:(lia))) as IHk.
      rewrite Hvs, Hvs'.
      destruct (Hv _ _ _ He) as [HC (r & Hrk & HT)].
      assert (Hlf : List.length (List.firstn k ts) = k) by (rewrite List.length_firstn; lia).
      assert (Hlv : List.length (List.firstn k vs) = k) by (rewrite List.length_firstn; lia).
      assert (Hlv' : List.length (List.firstn k vs') = k) by (rewrite List.length_firstn; lia).
      assert (Hg' : per_tele_args (List.rev (List.rev (List.firstn k ts) ++ Pre0 ++ C)) nil nil
                      (ns ++ zs ++ List.firstn k vs) (ns' ++ zs' ++ List.firstn k vs')).
      { rewrite List.rev_app_distr, List.rev_involutive, !List.app_assoc.
        apply per_tele_args_app_intro; [ rewrite List.length_app, List.length_rev, List.length_app; lia | exact Hg |].
        rewrite !env_tele_closed_app by assumption; exact IHk. }
      set (Pre := List.rev (List.firstn k ts) ++ Pre0).
      assert (HC' : ⊨ Pre ++ C) by (unfold Pre; rewrite <- List.app_assoc; exact HC).
      assert (HT' : Pre ++ C ⊨ A : abs_kind_sort r S[wk_shiftn (List.length Pre)]ʷ)
        by (unfold Pre; rewrite <- List.app_assoc, List.length_app, List.length_rev, Hlf; exact HT).
      assert (Hg'' : per_tele_args (List.rev (Pre ++ C)) nil nil
                       (ns ++ (zs ++ List.firstn k vs)) (ns' ++ (zs' ++ List.firstn k vs')))
        by (unfold Pre; rewrite <- List.app_assoc; exact Hg').
      destruct (sort_rel_tele_rel r Pre A Hrk HC' HT' ns ns' (zs ++ List.firstn k vs) (zs' ++ List.firstn k vs')
                  ltac:(unfold Pre; rewrite !List.length_app, List.length_rev; lia)
                  ltac:(unfold Pre; rewrite !List.length_app, List.length_rev; lia)
                  Hu Hu' Hg'' a Ha)
        as (t & t' & Et & Et' & [R0 HR0]).
      destruct (per_univ_elem_to_nat _ _ _ _ HR0) as [n Hn].
      unfold Pre in Et, Et'; rewrite List.rev_app_distr, List.rev_involutive in Et, Et'.
      apply (per_tele_args_snoc _ _ _ _ _ _ _ _ _ n R0); [ lia | exact IHk | |].
      + rewrite env_tele_app in Et, Et' by (rewrite List.length_rev; lia).
        exact (mk_rel_mod_eval t t' Et Et' Hn).
      + pose proof (Hr _ _ _ Hv0 Hv0') as Hrv.
        apply (Htr _ _ _ _ He Hlv) in Hrv.
        assert (HRtt : DF t ≈ t ∈ per_univ_elem n ↘ R0)
          by (eapply per_univ_trans; [ exact Hn | apply per_univ_sym; exact Hn ]).
        rewrite (env_tele_app_firstn _ (List.rev Pre0) ts zs (List.firstn k vs)) in Hrv
          by (rewrite ?List.length_rev; lia).
        rewrite Hlv in Hrv.
        exact (Hrv _ _ _ _ Et Et HRtt).
  Qed.

  Lemma rev_tele_sem : ⊨ List.rev (List.rev C) ++ ⋅.
  Proof. rewrite List.rev_involutive, List.app_nil_r; exact HCv. Qed.

  Lemma rev_all_assumptions : all_assumptions (List.rev C).
  Proof. apply List.Forall_rev, HCa. Qed.

  Lemma record_params_args_refl_l : forall ns ns', per_tele_args (List.rev C) nil nil ns ns' -> per_tele_args (List.rev C) nil nil ns ns.
  Proof.
    intros * Hg; eapply (per_tele_args_refl_l _ _ _ per_ctx_env_nil_true rev_tele_sem); [ exact rev_all_assumptions | exact I | exact Hg ].
  Qed.

  Lemma length_record_params_args : forall ns ns', per_tele_args (List.rev C) nil nil ns ns' ->
      List.length ns = List.length C -> List.length ns' = List.length C.
  Proof. intros * Hg Hu; destruct (per_tele_args_length _ _ _ _ _ Hg) as [Hl _]; lia. Qed.

  (** The sort at arguments related to themselves has a value. *)
  Lemma sort_tele_value : forall ns, per_tele_args (List.rev C) nil nil ns ns -> List.length ns = List.length C ->
      exists a, ⟦ S ⟧ env_tele nil (List.rev C) ns ↘ a.
  Proof.
    intros ns Hg Hu.
    destruct HS as [i HSi].
    destruct (rel_ctx_wf_per_ctx_env HCv) as [RU HRU].
    assert (HRU0 : RU (env_tele nil (List.rev C) ns) (env_tele nil (List.rev C) ns))
      by (apply (tele_args_env_rel _ _ _ _ _ _ HRU HCv); [ exact Hu | exact Hg ]).
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

(** ** Values of Fields by Their Kinds *)

(** The kind a list of kinds gives a field past its head: the rest's. *)
Lemma nth_tl_kind : forall (rs : list abs_kind) k, List.nth k (List.tl rs) ak_relevant = List.nth (S k) rs ak_relevant.
Proof. intros [| r rs] k; [ destruct k | ]; reflexivity. Qed.

(** The head kind is the kind at [0]. *)
Lemma hd_nth_kind : forall (rs : list abs_kind), List.hd ak_relevant rs = List.nth 0 rs ak_relevant.
Proof. intros []; reflexivity. Qed.

(** The fields have values when those of an evaluated kind do. *)
Lemma eval_field_vals_each : forall Ms rs ρ,
    (forall k M, List.nth_error Ms k = Some M -> evaluated_kind (List.nth k rs ak_relevant) -> exists m, ⟦ M ⟧ ρ ↘ m) ->
    exists vs, eval_field_vals gc_deps gc_stack rs Ms ρ vs.
Proof.
  induction Ms as [| M Ms IH]; intros rs ρ H; [ exists nil; constructor |].
  destruct (IH (List.tl rs) ρ) as [vs Hvs].
  { intros k N HN Hr; apply (H (S k) N HN); rewrite <- nth_tl_kind; exact Hr. }
  destruct (evaluated_kind_or_propositional (List.hd ak_relevant rs)) as [Er | Er].
  - destruct (H 0 M eq_refl ltac:(rewrite <- hd_nth_kind; exact Er)) as [m Hm].
    exists (m :: vs); eapply eval_field_vals_evaluated; eassumption.
  - exists (⋆ᵈ⟨M, ρ⟩ :: vs); eapply eval_field_vals_proof; eassumption.
Qed.

(** A field's value: the term's at a field of an evaluated kind, the
    proof at a propositional one. *)
Lemma eval_field_vals_nth : forall rs Ms ρ vs, eval_field_vals gc_deps gc_stack rs Ms ρ vs ->
    forall k M, List.nth_error Ms k = Some M ->
      exists v, List.nth_error vs k = Some v /\
        (evaluated_kind (List.nth k rs ak_relevant) -> ⟦ M ⟧ ρ ↘ v) /\
        (List.nth k rs ak_relevant = ak_propositional -> v = ⋆ᵈ⟨M, ρ⟩).
Proof.
  induction 1 as [rs ρ | rs M ρ m Ms ms Hr Hm Hms IH | rs M ρ Ms ms Hr Hms IH]; intros [| k] N HN; cbn in HN; try discriminate.
  - injection HN as <-; exists m; split; [ reflexivity |].
    split; [ intros _; exact Hm | intros Hp; rewrite <- hd_nth_kind in Hp; rewrite Hp in Hr; inversion Hr ].
  - destruct (IH k N HN) as (v & Hv & Hv1 & Hv2); exists v; split; [ exact Hv |].
    rewrite <- !nth_tl_kind; split; assumption.
  - injection HN as <-; eexists; split; [ reflexivity |].
    split; [ intros Hev; rewrite <- hd_nth_kind, Hr in Hev; inversion Hev | intros _; reflexivity ].
  - destruct (IH k N HN) as (v & Hv & Hv1 & Hv2); exists v; split; [ exact Hv |].
    rewrite <- !nth_tl_kind; split; assumption.
Qed.

(** And conversely: values of the fields' kinds pointwise are their
    values. *)
Lemma eval_field_vals_of_nth : forall Ms rs ρ vs, List.length vs = List.length Ms ->
    (forall k M v, List.nth_error Ms k = Some M -> List.nth_error vs k = Some v ->
       (evaluated_kind (List.nth k rs ak_relevant) -> ⟦ M ⟧ ρ ↘ v) /\
       (List.nth k rs ak_relevant = ak_propositional -> v = ⋆ᵈ⟨M, ρ⟩)) ->
    eval_field_vals gc_deps gc_stack rs Ms ρ vs.
Proof.
  induction Ms as [| M Ms IH]; intros rs ρ [| v vs] Hl H; cbn in Hl; try discriminate; [ constructor |].
  assert (Hrest : eval_field_vals gc_deps gc_stack (List.tl rs) Ms ρ vs).
  { apply IH; [ lia |]; intros k N w HN Hw; rewrite !nth_tl_kind; exact (H (S k) N w HN Hw). }
  destruct (H 0 M v eq_refl eq_refl) as [Hr Hp].
  destruct (evaluated_kind_or_propositional (List.hd ak_relevant rs)) as [Er | Er].
  - eapply eval_field_vals_evaluated; [ exact Er | apply Hr; rewrite <- hd_nth_kind; exact Er | exact Hrest ].
  - rewrite (Hp ltac:(rewrite <- hd_nth_kind; exact Er)).
    eapply eval_field_vals_proof; [ exact Er | exact Hrest ].
Qed.

Lemma eval_field_vals_length : forall rs Ms ρ vs, eval_field_vals gc_deps gc_stack rs Ms ρ vs -> List.length vs = List.length Ms.
Proof. induction 1; cbn; congruence. Qed.

(** The first fields' values are the values of the first fields. *)
Lemma eval_field_vals_firstn : forall rs Ms ρ vs, eval_field_vals gc_deps gc_stack rs Ms ρ vs ->
    forall k, eval_field_vals gc_deps gc_stack rs (List.firstn k Ms) ρ (List.firstn k vs).
Proof.
  induction 1 as [rs ρ | rs M ρ m Ms ms Hr Hm Hms IH | rs M ρ Ms ms Hr Hms IH]; intros [| k]; cbn; try solve [ constructor ].
  - eapply eval_field_vals_evaluated; [ exact Hr | exact Hm | apply IH ].
  - eapply eval_field_vals_proof; [ exact Hr | apply IH ].
Qed.

(** The values of fields followed by more: the first fields', then the
    rest's at the sorts past them. *)
Lemma eval_field_vals_app : forall Us rs Ms ρ us zs, eval_field_vals gc_deps gc_stack rs Us ρ us ->
    eval_field_vals gc_deps gc_stack (List.skipn (List.length Us) rs) Ms ρ zs ->
    eval_field_vals gc_deps gc_stack rs (Us ++ Ms) ρ (us ++ zs).
Proof.
  induction Us as [| U Us IH]; intros rs Ms ρ us zs Hus Hzs; inversion Hus; subst; [ exact Hzs | |].
  - eapply eval_field_vals_evaluated; [ assumption | eassumption | apply IH; [ assumption |] ].
    destruct rs; cbn in *; [ rewrite ?List.skipn_nil in *; exact Hzs | exact Hzs ].
  - eapply eval_field_vals_proof; [ assumption | apply IH; [ assumption |] ].
    destruct rs; cbn in *; [ rewrite ?List.skipn_nil in *; exact Hzs | exact Hzs ].
Qed.

(** And conversely. *)
Lemma eval_field_vals_app_inv : forall Us rs Ms ρ vs, eval_field_vals gc_deps gc_stack rs (Us ++ Ms) ρ vs ->
    exists us zs, vs = us ++ zs /\ eval_field_vals gc_deps gc_stack rs Us ρ us /\
      eval_field_vals gc_deps gc_stack (List.skipn (List.length Us) rs) Ms ρ zs.
Proof.
  induction Us as [| U Us IH]; intros rs Ms ρ vs Hvs; [ exists nil, vs; split; [ reflexivity | split; [ constructor | exact Hvs ] ] |].
  inversion Hvs; subst.
  - match goal with H : eval_field_vals _ _ (List.tl rs) (Us ++ Ms) ρ ?ms |- _ =>
      destruct (IH _ _ _ _ H) as (us & zs & -> & Hus & Hzs) end.
    eexists (_ :: us), zs; split; [ reflexivity | split; [ eapply eval_field_vals_evaluated; eassumption |] ].
    destruct rs; cbn in *; [ rewrite ?List.skipn_nil in *; exact Hzs | exact Hzs ].
  - match goal with H : eval_field_vals _ _ (List.tl rs) (Us ++ Ms) ρ ?ms |- _ =>
      destruct (IH _ _ _ _ H) as (us & zs & -> & Hus & Hzs) end.
    exists (⋆ᵈ⟨U, ρ⟩ :: us), zs; split; [ reflexivity | split; [ eapply eval_field_vals_proof; eassumption |] ].
    destruct rs; cbn in *; [ rewrite ?List.skipn_nil in *; exact Hzs | exact Hzs ].
Qed.

(** Fields all of evaluated kinds: their values are the terms'. *)
Lemma eval_field_vals_of_exps : forall Ms rs ρ ms, (forall j, j < List.length Ms -> evaluated_kind (List.nth j rs ak_relevant)) ->
    ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms -> eval_field_vals gc_deps gc_stack rs Ms ρ ms.
Proof.
  induction Ms as [| M Ms IH]; intros rs ρ ms Hr Hms; inversion Hms; subst; [ constructor |].
  eapply eval_field_vals_evaluated; [ rewrite hd_nth_kind; exact (Hr 0 ltac:(cbn; lia)) | eassumption |].
  apply IH; [| assumption ]; intros j Hj; rewrite nth_tl_kind; apply Hr; cbn; lia.
Qed.

(** And conversely. *)
Lemma eval_exps_of_field_vals : forall rs Ms ρ ms, eval_field_vals gc_deps gc_stack rs Ms ρ ms ->
    (forall j, j < List.length Ms -> evaluated_kind (List.nth j rs ak_relevant)) -> ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms.
Proof.
  induction 1 as [rs ρ | rs M ρ m Ms ms Hr Hm Hms IH | rs M ρ Ms ms Hr Hms IH]; intros Hall; [ constructor | |].
  - constructor; [ exact Hm | apply IH; intros j Hj; rewrite nth_tl_kind; apply Hall; cbn; lia ].
  - exfalso; specialize (Hall 0 ltac:(cbn; lia)); rewrite <- hd_nth_kind, Hr in Hall; inversion Hall.
Qed.

(** A substitution extended by fields, at a context extended by entries
    [ts] whose kinds are the fields', evaluated: to the fields' values. *)
Lemma eval_sb_of_list_fields : forall Fs ts σ Δ ρ ρσ rs vs,
    ⟦ σ : Δ ⟧s ρ ↘ ρσ -> eval_field_vals gc_deps gc_stack rs Fs ρ vs -> List.length ts = List.length Fs ->
    (forall j e, List.nth_error ts j = Some e ->
       (evaluated_kind (List.nth j rs ak_relevant) ->
          ~ head_propositional gc_deps gc_stack e (List.rev (List.firstn j ts) ++ Δ)
              (env_extend_tagged Δ (List.firstn j ts) ρσ (List.firstn j vs))) /\
       (List.nth j rs ak_relevant = ak_propositional ->
          head_propositional gc_deps gc_stack e (List.rev (List.firstn j ts) ++ Δ)
            (env_extend_tagged Δ (List.firstn j ts) ρσ (List.firstn j vs)))) ->
    ⟦ sb_of_list σ Fs : List.rev ts ++ Δ ⟧s ρ ↘ env_extend_tagged Δ ts ρσ vs.
Proof.
  induction Fs as [| M Fs IH]; intros [| e ts] * Hσ Hvs Hl Hst; cbn [List.length] in Hl; try discriminate.
  - inversion Hvs; subst; exact Hσ.
  - cbn [sb_of_list List.rev]; rewrite <- List.app_assoc; cbn [List.app].
    destruct (Hst 0 e eq_refl) as [Hr0 Hp0]; cbn [List.firstn List.rev List.app env_extend_tagged] in Hr0, Hp0.
    inversion Hvs; subst;
      match goal with Hms : eval_field_vals _ _ _ Fs ρ ?ms |- _ => rename Hms into Hms'; rename ms into ms' end;
      rename Hms' into Hms; rename ms' into ms.
    + match goal with Hm : ⟦ M ⟧ _ ⍮ _ ⍮ ρ ↘ ?m, Hhd : evaluated_kind (List.hd ak_relevant rs) |- _ =>
        rename Hm into Hm'; rename Hhd into Hhd'; rename m into m' end.
      rename Hm' into Hm; rename Hhd' into Hhd; rename m' into m.
      change (env_extend_tagged Δ (e :: ts) ρσ (m :: ms)) with (env_extend_tagged (e :: Δ) ts (ρσ ↦ m ⦂ centry_tag e Δ ρσ) ms).
      apply (IH ts (σ ,, M) (e :: Δ) ρ (ρσ ↦ m ⦂ centry_tag e Δ ρσ) (List.tl rs) ms); [ | exact Hms | lia |].
      * apply eval_sub_extend; [ exact Hσ | | exact Hm ].
        apply Hr0; rewrite <- hd_nth_kind; exact Hhd.
      * intros j e' He'; destruct (Hst (S j) e' He') as [Hr Hp].
        cbn [List.firstn List.rev] in Hr, Hp; rewrite <- List.app_assoc in Hr, Hp; cbn [List.app] in Hr, Hp.
        rewrite nth_tl_kind; split; assumption.
    + match goal with Hhd : List.hd ak_relevant rs = ak_propositional |- _ => rename Hhd into Hhd' end.
      rename Hhd' into Hhd.
      change (env_extend_tagged Δ (e :: ts) ρσ (⋆ᵈ⟨M, ρ⟩ :: ms))
        with (env_extend_tagged (e :: Δ) ts (ρσ ↦ ⋆ᵈ⟨M, ρ⟩ ⦂ centry_tag e Δ ρσ) ms).
      apply (IH ts (σ ,, M) (e :: Δ) ρ (ρσ ↦ ⋆ᵈ⟨M, ρ⟩ ⦂ centry_tag e Δ ρσ) (List.tl rs) ms); [ | exact Hms | lia |].
      * apply eval_sub_extend_proof; [ exact Hσ |].
        apply Hp0; rewrite <- hd_nth_kind; exact Hhd.
      * intros j e' He'; destruct (Hst (S j) e' He') as [Hr Hp].
        cbn [List.firstn List.rev] in Hr, Hp; rewrite <- List.app_assoc in Hr, Hp; cbn [List.app] in Hr, Hp.
        rewrite nth_tl_kind; split; assumption.
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

(** The types of the fields, outermost first, each at its kind. *)
Definition field_tele (R : record_decl) : list centry := fields_tele_in_order (record_fields R) (record_field_kinds R).

(** It is the fields' telescope of the PER clause. *)
Lemma record_fields_tele_eq : forall R, record_fields_tele R = field_tele R.
Proof. intros; unfold record_fields_tele, field_tele; apply rev_fields_tele. Qed.

Lemma rev_record_fctx : forall R k, List.rev (record_fctx R k) = List.firstn k (field_tele R).
Proof. intros; unfold record_fctx, field_tele; rewrite rev_fields_tele, firstn_fields_tele_in_order; reflexivity. Qed.

(** The environment of the parameters and the first [k] fields is the
    closed environment of the fields' context at [k]. *)
Lemma record_fields_env_closed : forall R ns vs, List.length ns = List.length (record_params R) ->
    record_fields_env R ns vs = env_tele nil (List.rev (record_fctx R (List.length vs) ++ record_params R)) (ns ++ vs).
Proof.
  intros * Hl; unfold record_fields_env.
  rewrite (env_tele_firstn _ (record_fields_tele R) vs).
  rewrite record_fields_tele_eq, <- rev_record_fctx, <- env_tele_closed_app by assumption.
  reflexivity.
Qed.

Lemma field_tele_all_assumptions : forall R, all_assumptions (field_tele R).
Proof.
  intros R; unfold field_tele, all_assumptions; generalize (record_field_kinds R).
  induction (record_fields R) as [| fT fl IH]; intros κs; cbn [fields_tele_in_order]; constructor; eauto.
Qed.

(** An entry of the fields in order: the field's type, at its kind. *)
Lemma fields_tele_in_order_nth : forall fl κs j κ A, List.nth_error (fields_tele_in_order fl κs) j = Some (ce_ass κ A) ->
    exists f, List.nth_error fl j = Some (f, A) /\ κ = List.nth j κs ak_relevant.
Proof.
  induction fl as [| [f T] fl IH]; intros κs [| j] κ A H; cbn [fields_tele_in_order List.nth_error] in H; try discriminate.
  - injection H as <- <-; exists f; split; [ reflexivity | destruct κs; reflexivity ].
  - destruct (IH _ _ _ _ H) as (f' & Hf & ->); exists f'; split; [ exact Hf |].
    destruct κs as [| κ0 κs]; cbn; [ destruct j; reflexivity | reflexivity ].
Qed.

Lemma field_tele_nth : forall R j κ A, List.nth_error (field_tele R) j = Some (ce_ass κ A) ->
    exists f, List.nth_error (record_fields R) j = Some (f, A) /\ κ = record_field_kind R j.
Proof. intros * H; exact (fields_tele_in_order_nth _ _ _ _ _ H). Qed.

(** Conversely, the entry of a field: its type at its kind. *)
Lemma field_tele_nth_of : forall R j f A, List.nth_error (record_fields R) j = Some (f, A) ->
    List.nth_error (field_tele R) j = Some (ce_ass (record_field_kind R j) A).
Proof.
  intros R; unfold field_tele, record_field_kind; generalize (record_field_kinds R).
  induction (record_fields R) as [| [g T] fl IH]; intros κs [| j] f A H; cbn in H |- *; try discriminate.
  - injection H as <- <-; destruct κs; reflexivity.
  - rewrite (IH _ _ _ _ H); destruct κs as [| κ0 κs]; [ destruct j |]; reflexivity.
Qed.

Lemma length_field_tele : forall R, List.length (field_tele R) = List.length (record_fields R).
Proof.
  intros R; unfold field_tele; generalize (record_field_kinds R).
  induction (record_fields R) as [| fT fl IH]; intros κs; cbn; [ reflexivity | rewrite IH; reflexivity ].
Qed.

(** ** A Valid Record

    The hypotheses are the judgments of the record's declaration, read in
    the PER model: the fields over the parameters are a context, the sort
    is a universe over the parameters, and each field is a type of the
    sort over the fields before it. *)
Section RecordModel.
  Variables (p : qname) (R : record_decl).
  Hypothesis (Hl : record_lookup gc_deps gc_stack p = Some R) (Hc : record_closed R)
    (Hass : all_assumptions (record_params R)) (Hnd : List.NoDup (List.map fst (record_fields R)))
    (Hsu : ind_sort_univ (record_sort R))
    (HF : ⊨ record_fctx R (List.length (record_fields R)) ++ record_params R)
    (HS : exists i : nat, record_params R ⊨ record_sort R : Typeω@i)
    (HT : forall k f T, List.nth_error (record_fields R) k = Some (f, T) ->
       record_fctx R k ++ record_params R ⊨ T : abs_kind_sort (record_field_kind R k) (record_sort R)[wk_shiftn k]ʷ)
    (HPr : exists l, rel_params_evaluated ⋅ (record_params R) l).
  (** No field is of a type of levels ([fields_kind_valid]). *)
  Hypothesis (HFk : forall k, field_kind (record_field_kind R k)).

  (** So each field is relevant or a proposition. *)
  Lemma field_kind_cases : forall k, record_field_kind R k = ak_relevant \/ record_field_kind R k = ak_propositional.
  Proof. intros k; pose proof (HFk k) as H; inversion H; auto. Qed.

  (** A field of an evaluated kind is relevant. *)
  Lemma field_kind_evaluated_relevant : forall k, evaluated_kind (record_field_kind R k) -> record_field_kind R k = ak_relevant.
  Proof. intros k Hk; destruct (field_kind_cases k) as [E | E]; [ exact E | rewrite E in Hk; inversion Hk ]. Qed.

  (** And a relevant field's kind is evaluated, read off the kinds. *)
  Lemma field_relevant_evaluated : forall k, record_field_kind R k = ak_relevant ->
      evaluated_kind (List.nth k (record_field_kinds R) ak_relevant).
  Proof. intros k E; change (evaluated_kind (record_field_kind R k)); rewrite E; constructor. Qed.

  Lemma record_fctx_sem : forall k, k <= List.length (record_fields R) -> ⊨ record_fctx R k ++ record_params R.
  Proof.
    intros k Hk.
    assert (Hs : exists X, record_fctx R (List.length (record_fields R)) = X ++ record_fctx R k).
    { unfold record_fctx; rewrite List.firstn_all.
      exists (fields_tele (List.skipn k (record_fields R)) (List.skipn (List.length (List.firstn k (record_fields R))) (record_field_kinds R))).
      rewrite <- fields_tele_app, List.firstn_skipn; reflexivity. }
    destruct Hs as [X Hs].
    pose proof HF as H; rewrite Hs, <- List.app_assoc in H; exact (rel_ctx_wf_app_r _ _ H).
  Qed.

  Lemma record_params_sem : ⊨ record_params R.
  Proof. pose proof (record_fctx_sem 0 ltac:(lia)) as H; exact H. Qed.

  (** The canonical relations of the fields at related parameters are
      those of their telescope. *)
  Lemma canon_fields_tele_args : forall ns ns' a, per_tele_args (List.rev (record_params R)) nil nil ns ns' ->
      List.length ns = List.length (record_params R) -> ⟦ record_sort R ⟧ env_tele nil (List.rev (record_params R)) ns ↘ a ->
      forall k vs vs', k <= List.length (record_fields R) -> tele_prefix_rel (canon_fields_rel R ns) k vs vs' ->
        per_tele_args (List.firstn k (field_tele R)) (env_tele nil (List.rev (record_params R)) ns)
          (env_tele nil (List.rev (record_params R)) ns') vs vs'.
  Proof.
    intros * Hg Hu Ha * Hk Hp.
    pose proof (length_record_params_args (record_params R) _ _ Hg Hu) as Hu'.
    pose proof (sort_tele_canon_tele_args (record_params R) (record_sort R) Hsu HS
                  (field_tele R) nil (canon_fields_rel R ns) ns ns' nil nil a
                  (field_tele_all_assumptions R) Hu Hu' eq_refl eq_refl ltac:(rewrite !List.app_nil_r; exact Hg) Ha) as Hcan.
    cbn [List.rev List.app List.length] in Hcan.
    assert (Hce : forall u, env_tele (env_tele nil (List.rev (record_params R)) u) nil nil = env_tele nil (List.rev (record_params R)) u)
      by reflexivity.
    rewrite !Hce in Hcan; apply Hcan; [ | | rewrite length_field_tele; exact Hk | exact Hp ].
    - intros j κ A HA; rewrite Nat.add_0_r.
      destruct (field_tele_nth _ _ _ _ HA) as (f & Hj & _).
      assert (Hjl : j < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hj).
      rewrite <- rev_record_fctx, List.rev_involutive.
      split; [ apply record_fctx_sem; lia |].
      exists (record_field_kind R j); split; [ exact (HFk j) | exact (HT _ _ _ Hj) ].
    - intros j κ A pre HA _; destruct (field_tele_nth _ _ _ _ HA) as (f & Hj & _).
      unfold canon_fields_rel, record_fields_env; rewrite (nth_ftyp_eq _ _ _ _ Hj), record_fields_tele_eq; reflexivity.
  Qed.

  (** The fields' types at related parameters and canonically related
      prefixes are related, in the universe the sort denotes. *)
  Lemma record_fields_related : forall ns ns' a, per_tele_args (List.rev (record_params R)) nil nil ns ns' ->
      List.length ns = List.length (record_params R) -> ⟦ record_sort R ⟧ env_tele nil (List.rev (record_params R)) ns ↘ a ->
      fields_related (univ_idx a) R ns ns'.
  Proof.
    intros * Hg Hu Ha k f T vs vs' Hk Hp.
    pose proof (length_record_params_args (record_params R) _ _ Hg Hu) as Hu'.
    assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hk).
    pose proof (canon_fields_tele_args _ _ _ Hg Hu Ha k vs vs' ltac:(lia) Hp) as Hgv.
    pose proof Hp as Hp0; rewrite tele_prefix_rel_iff in Hp0; destruct Hp0 as (Hlv & Hlv' & _).
    assert (HLk : List.length (record_fctx R k) = k) by (apply length_record_fctx; lia).
    pose proof (HT _ _ _ Hk) as HTk; rewrite <- HLk in HTk at 3.
    destruct (sort_rel_tele_rel (record_params R) (record_sort R) Hsu HS _ (record_fctx R k) T (HFk k) (record_fctx_sem k ltac:(lia)) HTk
                ns ns' vs vs' ltac:(lia) ltac:(lia) Hu Hu' ltac:(rewrite List.rev_app_distr, rev_record_fctx;
                                                              apply per_tele_args_app_intro;
                                                              [ rewrite List.length_rev; exact Hu | exact Hg | exact Hgv ]) a Ha)
      as (t & t' & Et & Et' & Htt).
    unfold record_fields_env.
    rewrite (env_tele_firstn _ (record_fields_tele R) vs), (env_tele_firstn _ (record_fields_tele R) vs'), Hlv, Hlv'.
    rewrite record_fields_tele_eq, <- rev_record_fctx.
    exists t, t'; split; [ exact Et | split; [ exact Et' | exact Htt ] ].
  Qed.

  (** ** The Canonical Model

      The record at related parameters is a type of the universe its sort
      denotes, its elements those of the canonical record relation. *)
  Lemma record_relate : forall ns ns' a, per_tele_args (List.rev (record_params R)) nil nil ns ns' ->
      List.length ns = List.length (record_params R) -> ⟦ record_sort R ⟧ env_tele nil (List.rev (record_params R)) ns ↘ a ->
      DF d_record p ns ≈ d_record p ns' ∈ per_univ_elem (univ_idx a) ↘ record_rel R (canon_fields_rel R ns).
  Proof.
    intros * Hg Hu Ha.
    pose proof (length_record_params_args (record_params R) _ _ Hg Hu) as Hu'.
    apply (per_univ_elem_record_canon (univ_idx a) p R ns ns' Hl Hnd Hu Hu');
      [ exact (per_tele_args_per_top_ps _ _ _ Hg ltac:(rewrite List.length_rev; exact Hu))
      | exact (record_fields_related _ _ _ Hg Hu Ha) | | | exact HFk ].
    (** The sorts, and that no field's type is [LevelSort]: at related
        arguments of the fields' telescope, each field's type is of its
        sort. *)
    all: intros k f T vs vs' Hk Hp.
    all: assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hk).
    all: pose proof (canon_fields_tele_args _ _ _ Hg Hu Ha k vs vs' ltac:(lia) Hp) as Hgv.
    all: pose proof Hp as Hp0; rewrite tele_prefix_rel_iff in Hp0; destruct Hp0 as (Hlv & Hlv' & _).
    all: assert (HC : ⊨ record_fctx R k ++ record_params R) by (apply record_fctx_sem; lia).
    all: destruct (rel_ctx_wf_per_ctx_env HC) as [RC HRC].
    all: assert (HE : RC (record_fields_env R ns vs) (record_fields_env R ns' vs'))
      by (unfold record_fields_env;
          rewrite (env_tele_firstn _ (record_fields_tele R) vs), (env_tele_firstn _ (record_fields_tele R) vs'), Hlv, Hlv';
          rewrite record_fields_tele_eq, <- rev_record_fctx, <- !env_tele_closed_app by assumption;
          apply (tele_args_env_rel _ _ _ _ _ _ HRC HC); [ rewrite !List.length_app, length_record_fctx by lia; lia |];
          rewrite List.rev_app_distr, rev_record_fctx;
          apply per_tele_args_app_intro; [ rewrite List.length_rev; exact Hu | exact Hg | exact Hgv ]).
    all: assert (HTl : record_field_kind R k = ak_relevant -> exists l : nat, record_fctx R k ++ record_params R ⊨ T : Typeω@l)
      by (intros Er; pose proof (HT _ _ _ Hk) as H; rewrite Er in H; cbn [abs_kind_sort] in H;
          destruct Hsu as [[i Heq] | [t Heq]]; rewrite Heq in H; cbn [exp_wk] in H;
          [ exists i; exact H | exists 0; eapply rel_exp_suniv_tm_large; exact H ]).
    all: destruct (field_kind_cases k) as [Er | Er].
    - destruct (HTl Er) as [l HTl'].
      destruct (rel_exp_of_typ_relevant_at HRC HTl' _ _ HE) as (t & Et & Ht); exists t; split; [ exact Et | rewrite Er; exact Ht ].
    - pose proof (HT _ _ _ Hk) as HTp; rewrite Er in HTp; cbn [abs_kind_sort] in HTp.
      destruct (rel_exp_of_prop_inversion_simple_at HRC HTp _ _ HE) as (t & _ & Et & _ & [Ht _ _]).
      exists t; split; [ exact Et | rewrite Er; exact Ht ].
    - destruct (HTl Er) as [l HTl'].
      exact (rel_exp_of_typ_not_level_sort HTl' _ HRC _ _ HE).
    - pose proof (HT _ _ _ Hk) as HTp; rewrite Er in HTp; cbn [abs_kind_sort] in HTp.
      exact (rel_exp_of_prop_not_level_sort HTp _ HRC _ _ HE).
  Qed.

  (** The type former at related parameters, at the sort's universe. *)
  Lemma record_at_params : forall RU ρ ρ' vts vts', EF record_params R ≈ record_params R ∈ per_ctx_env ↘ RU ->
      List.length vts = List.length (record_params R) -> List.length vts' = List.length (record_params R) ->
      RU (env_extend_typed ρ vts) (env_extend_typed ρ' vts') ->
      Dom d_record p (List.map fst vts) ≈ d_record p (List.map fst vts')
        ∈ per_head (record_sort R) (record_sort R) (env_extend_typed ρ vts) (env_extend_typed ρ' vts').
  Proof.
    intros * HRU Hlen Hlen' HE i0 R0 b b' Eb Eb' HR0.
    assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
    assert (HEE : RU (env_extend_typed ρ vts) (env_extend_typed ρ vts)) by (etransitivity; [ exact HE | symmetry; exact HE ]).
    assert (HRU' : EF List.rev (List.rev (record_params R)) ++ ⋅ ≈ List.rev (List.rev (record_params R)) ++ ⋅ ∈ per_ctx_env ↘ RU)
      by (rewrite List.rev_involutive, List.app_nil_r; exact HRU).
    destruct (per_tele_args_of_env_extend _ _ _ _ per_ctx_env_nil_true (rev_tele_sem _ record_params_sem) (rev_all_assumptions _ Hass) HRU' ρ ρ' vts vts'
                ltac:(rewrite List.length_rev; exact Hlen) ltac:(rewrite List.length_rev; exact Hlen') HE) as [_ Hg].
    destruct (per_tele_args_of_env_extend_readable _ _ _ _ per_ctx_env_nil_true (rev_tele_sem _ record_params_sem) (rev_all_assumptions _ Hass) HRU' ρ ρ vts vts
                ltac:(rewrite List.length_rev; exact Hlen) ltac:(rewrite List.length_rev; exact Hlen) HEE) as [Rv _].
    set (ys := List.map fst vts) in *; set (ys' := List.map fst vts') in *.
    assert (Hlys : List.length ys = List.length (record_params R)) by (unfold ys; rewrite List.length_map; exact Hlen).
    pose proof (per_tele_args_base _ _ _ per_ctx_env_nil_true (rev_tele_sem _ record_params_sem) (rev_all_assumptions _ Hass)
                  ρ ρ' nil nil _ _ I I I Hg) as Hg0.
    pose proof (record_params_args_refl_l _ record_params_sem Hass _ _ Hg0) as Hgd.
    destruct (sort_tele_value _ _ record_params_sem HS _ Hgd Hlys) as [a Ea].
    destruct HS as [i HSi].
    pose proof (per_tele_args_entries_readable _ _ _ _ _ Hgd) as [Rt _].
    assert (HRUρ : RU (env_extend_typed ρ vts) (env_tele nil (List.rev (record_params R)) ys)).
    { unfold env_tele.
      exact (closed_env_base _ _ vts vts vts (tele_entries nil (List.rev (record_params R)) ys) ρ ρ ρ nil
               Hass record_params_sem HRU Hlen Hlen eq_refl ltac:(rewrite tele_entries_values; reflexivity) Rv Rt HEE). }
    assert (Hub : is_univ b) by exact (sort_tele_univ (record_params R) _ Hsu HS _ _ Eb).
    destruct (per_univ_elem_univ _ _ _ _ HR0 Hub) as [_ ER0].
    pose proof (univ_idx_rel _ _ _ _ _ _ _ _ HRU HSi HRUρ Eb Ea Hub) as Hi.
    apply ER0; split; [| reflexivity | reflexivity | discriminate | discriminate ].
    rewrite <- Hi.
    eexists; exact (record_relate _ _ _ Hg0 Hlys Ea).
  Qed.

  (** The type former takes its next parameter at the kind the parameter
      is tagged with, when that kind is evaluated ([tele_param_kind]). *)
  Lemma arg_kind_record_param : forall vs κ A,
      List.nth_error (List.rev (record_params R)) (List.length vs) = Some (ce_ass κ A) -> evaluated_kind κ ->
      arg_kind gc_deps gc_stack (d_record p vs) = κ.
  Proof. intros * Hn Hev; cbn [arg_kind]; rewrite Hl; unfold tele_param_kind; rewrite Hn; destruct Hev; reflexivity. Qed.

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
    assert (Hrel : forall Δ1 κ T Δ2, record_params R = Δ1 ++ ce_ass κ T :: Δ2 -> exists i : nat, rel_param_typed Δ2 T i)
      by (destruct HPr as [l HPl]; intros * E; exists l; pose proof (HPl _ _ _ _ E) as H; rewrite List.app_nil_r in H; exact H).
    eapply (ctx_pi_rel_elem (List.length (record_params R)) (d_record p) _ (List.rev (record_params R)) eval_app_record_args
              ltac:(intros xs κ A _ Hn Hev; exact (arg_kind_record_param xs κ A Hn Hev))
              (List.rev (record_params R)) ⋅ RT (rev_all_assumptions _ Hass) HRT (rev_tele_sem _ record_params_sem)
              ρ ρ' nil nil);
      [ rewrite List.length_rev; reflexivity | reflexivity | exact Hρ | reflexivity
      | | exact Ea | exact Ea' | exact HR0 | ].
    - (** The parameters are relevant or levels: of evaluated kinds. *)
      intros ts1 κ A ts2 R1 vts vts' b Heq HR1 Hl1 Hl1' HE1 Eb.
      assert (Hpe : record_params R = List.rev ts2 ++ ce_ass κ A :: List.rev ts1)
        by (rewrite <- (List.rev_involutive (record_params R)), Heq, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity).
      destruct (Hrel _ _ _ _ Hpe) as [i0 HA]; rewrite <- (List.app_nil_r (List.rev ts1)) in HA.
      destruct (rel_param_typed_evaluated HA) as (r & Hr0 & HAr).
      destruct (HAr _ HR1 _ _ HE1) as (b0 & Eb0 & Hr).
      assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption); rewrite Hr; exact Hr0.
    - intros R1 vts vts' HR1 Hl1 Hl1' HE1; cbn [List.app].
      rewrite List.rev_involutive, List.app_nil_r in HR1; rewrite List.length_rev in Hl1, Hl1'.
      exact (record_at_params R1 ρ ρ' vts vts' HR1 Hl1 Hl1' HE1).
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
      record_field_kind R k = ak_relevant ->
      exists j : nat, record_fctx R k ++ record_params R ⊨ T : Typeω@j.
  Proof.
    intros * Hk Hr; pose proof (HT _ _ _ Hk) as H; rewrite Hr in H; cbn [abs_kind_sort] in H.
    destruct Hsu as [[i Heq] | [t Heq]]; rewrite Heq in H; cbn [exp_wk] in H;
      [ exists i; exact H | exists 0; eapply rel_exp_suniv_tm_large; exact H ].
  Qed.

  (** Any field's type is a type of a sort of its kind. *)
  Lemma field_typ_sort : forall k f T, List.nth_error (record_fields R) k = Some (f, T) ->
      exists S, sort_kind S (record_field_kind R k) /\ record_fctx R k ++ record_params R ⊨ T : S.
  Proof.
    intros * Hk.
    destruct (field_kind_cases k) as [Er | Er]; rewrite Er.
    - destruct (field_typ_large _ _ _ Hk Er) as [j Hj]; exists Typeω@j; split; [ constructor | exact Hj ].
    - pose proof (HT _ _ _ Hk) as H; rewrite Er in H; cbn [abs_kind_sort] in H.
      exists Propₘ; split; [ constructor | exact H ].
  Qed.

  (** One more field in the fields' context, at its kind. *)
  Lemma record_fctx_S : forall k f T, List.nth_error (record_fields R) k = Some (f, T) ->
      record_fctx R (S k) = ce_ass (record_field_kind R k) T :: record_fctx R k.
  Proof.
    intros * H; unfold record_fctx; rewrite (firstn_S_snoc _ _ _ H), fields_tele_snoc.
    rewrite List.length_firstn, Nat.min_l by (apply Nat.lt_le_incl, (nth_error_lt_length _ _ _ H)); reflexivity.
  Qed.

  (** The entry [x] of the first [k] fields over the parameters, a field:
      the field [k - 1 - x], over the fields before it. *)
  Lemma record_ctx_field_at : forall k x, k <= List.length (record_fields R) -> x < k ->
      exists f T, List.nth_error (record_fields R) (k - 1 - x) = Some (f, T) /\
        List.skipn x (record_fctx R k ++ record_params R)
        = ce_ass (record_field_kind R (k - 1 - x)) T :: record_fctx R (k - 1 - x) ++ record_params R.
  Proof.
    induction k as [| k IH]; intros x Hk Hx; [ lia |].
    destruct (nth_error_lt_some' (record_fields R) k ltac:(lia)) as [[f T] HT0].
    rewrite (record_fctx_S _ _ _ HT0); cbn [List.app].
    destruct x as [| x].
    - exists f, T; replace (S k - 1 - 0) with k by lia; split; [ exact HT0 | reflexivity ].
    - destruct (IH x ltac:(lia) ltac:(lia)) as (f' & T' & HT' & Hs).
      exists f', T'; replace (S k - 1 - S x) with (k - 1 - x) by lia; split; [ exact HT' | exact Hs ].
  Qed.

  (** The entry [x] past the first [k] fields: a parameter. *)
  Lemma record_ctx_param_at : forall k x, k <= List.length (record_fields R) -> k <= x ->
      List.skipn x (record_fctx R k ++ record_params R) = List.skipn (x - k) (record_params R).
  Proof.
    intros * Hk Hx; rewrite List.skipn_app, length_record_fctx, List.skipn_all2 by (rewrite ?length_record_fctx; lia).
    reflexivity.
  Qed.

  (** The kind of the entry [x] of the first [k] fields over the
      parameters, as evaluation reads it: a field's kind, and [ak_relevant]
      at a parameter (relevant or a level, evaluated either way). *)
  Definition record_ctx_sort (k x : nat) : abs_kind := if x <? k then record_field_kind R (k - 1 - x) else ak_relevant.

  (** The parameters and the first [k] fields of a tuple, against their
      values: each value is the term's, or the entry is propositional. *)
  Lemma tuple_prefix_vals_sorted : forall Ns ns Fs E vs k,
      ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ ns -> eval_field_vals gc_deps gc_stack (record_field_kinds R) Fs E vs ->
      k <= List.length Fs ->
      forall j N m, List.nth_error (Ns ++ List.firstn k Fs) j = Some N -> List.nth_error (ns ++ List.firstn k vs) j = Some m ->
        ⟦ N ⟧ E ↘ m \/ record_ctx_sort k (List.length (Ns ++ List.firstn k Fs) - 1 - j) = ak_propositional.
  Proof.
    intros * Ens EV Hk j N m HN Hm.
    pose proof (eval_exps_length _ _ _ Ens) as Hln.
    pose proof (eval_field_vals_length _ _ _ _ EV) as Hlv.
    destruct (Nat.lt_ge_cases j (List.length Ns)) as [Hj | Hj].
    - rewrite List.nth_error_app1 in HN by exact Hj; rewrite List.nth_error_app1 in Hm by lia.
      destruct (eval_exps_nth _ _ _ _ _ Ens HN) as (m' & Hm' & Em'); rewrite Hm in Hm'; injection Hm' as <-.
      left; exact Em'.
    - rewrite List.nth_error_app2 in HN by exact Hj; rewrite List.nth_error_app2 in Hm by lia.
      rewrite Hln in Hm.
      rewrite List.nth_error_firstn in HN, Hm; destruct (Nat.ltb_spec (j - List.length Ns) k) as [Hjk |]; [| discriminate ].
      destruct (eval_field_vals_nth _ _ _ _ EV _ _ HN) as (v & Hv & Ev & _); rewrite Hm in Hv; injection Hv as <-.
      destruct (evaluated_kind_or_propositional (List.nth (j - List.length Ns) (record_field_kinds R) ak_relevant)) as [Er | Er];
        [ left; exact (Ev Er) | right ].
      rewrite List.length_app, List.length_firstn, Nat.min_l by lia.
      replace (List.length Ns + k - 1 - j) with (k - 1 - (j - List.length Ns)) by lia.
      unfold record_ctx_sort; destruct (Nat.ltb_spec (k - 1 - (j - List.length Ns)) k); [| lia ].
      unfold record_field_kind; replace (k - 1 - (k - 1 - (j - List.length Ns))) with (j - List.length Ns) by lia; exact Er.
  Qed.

  (** An entry of the first [k] fields over the parameters, over [Γ], is a
      parameter type ([rel_param_typed]) at an evaluated kind, a field a
      type of a universe, a parameter of a universe or of levels, and a
      proposition at the propositional one. *)
  Lemma record_ctx_entry_typed : forall k Γ, k <= List.length (record_fields R) -> ⊨ Γ ->
      forall Δ1 κ T Δ2, record_fctx R k ++ record_params R = Δ1 ++ ce_ass κ T :: Δ2 ->
        (evaluated_kind (record_ctx_sort k (List.length Δ1)) -> exists i : nat, rel_param_typed (Δ2 ++ Γ) T i) /\
        (record_ctx_sort k (List.length Δ1) = ak_propositional -> Δ2 ++ Γ ⊨ T : Propₘ).
  Proof.
    intros * Hk HΓ * E.
    assert (Hs : List.skipn (List.length Δ1) (record_fctx R k ++ record_params R) = ce_ass κ T :: Δ2)
      by (rewrite E, List.skipn_app, Nat.sub_diag, List.skipn_all; reflexivity).
    unfold record_ctx_sort; destruct (Nat.ltb_spec (List.length Δ1) k) as [Hlt | Hge].
    - destruct (record_ctx_field_at k (List.length Δ1) Hk Hlt) as (f & T' & HT' & Hs').
      rewrite Hs in Hs'; injection Hs' as _ <- ->.
      assert (Hk' : k - 1 - List.length Δ1 <= List.length (record_fields R)) by lia.
      split.
      + (** An evaluated field kind is [ak_relevant] ([field_kind]). *)
        intros Hr.
        destruct (field_kind_cases (k - 1 - List.length Δ1)) as [Hrr | Hpp]; [| rewrite Hpp in Hr; inversion Hr ].
        destruct (field_typ_large _ _ _ HT' Hrr) as [i Hi].
        exists i; left; exact (closed_app_valid _ _ _ _ _ (record_fctx_params_ass _ _ Hass) (record_fctx_sem _ Hk') HΓ Hi).
      + intros Hp; pose proof (HT _ _ _ HT') as H; rewrite Hp in H; cbn [abs_kind_sort] in H.
        exact (closed_app_valid _ _ _ _ _ (record_fctx_params_ass _ _ Hass) (record_fctx_sem _ Hk') HΓ H).
    - rewrite (record_ctx_param_at k _ Hk Hge) in Hs.
      split; [| discriminate ].
      intros _.
      destruct HPr as [l Hl0].
      assert (Hpe : record_params R = List.firstn (List.length Δ1 - k) (record_params R) ++ ce_ass κ T :: Δ2)
        by (rewrite <- Hs, List.firstn_skipn; reflexivity).
      exact (closed_evaluated_over _ _ Hass record_params_sem HΓ (ex_intro _ l Hl0) _ _ _ _ Hpe).
  Qed.

  (** A field's type at an instance of the fields' telescope by valid
      terms, against the field's type at the values [ms]: the terms'
      values at the relevant entries, any arguments related at the
      telescope at the propositional ones (a proof is related to any
      other). *)
  Lemma field_inst_link : forall Γ k f U Ms RΓ E ms,
      List.nth_error (record_fields R) k = Some (f, U) -> ⊨ Γ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
      List.length Ms = k + List.length (record_params R) ->
      (forall j N A, List.nth_error Ms j = Some N ->
         List.nth_error (tele_insts (record_fctx R k ++ record_params R) Id Ms) j = Some A -> Γ ⊨ N : A) ->
      List.Forall (exp_scoped (List.length Γ)) Ms ->
      RΓ E E -> List.length ms = List.length Ms ->
      per_tele_args (List.rev (record_fctx R k ++ record_params R)) nil nil ms ms ->
      (forall j N m, List.nth_error Ms j = Some N -> List.nth_error ms j = Some m ->
         ⟦ N ⟧ E ↘ m \/ record_ctx_sort k (List.length Ms - 1 - j) = ak_propositional) ->
      exists (j : nat) t u, ⟦ U[sb_of_list Id Ms] ⟧ E ↘ t /\
        ⟦ U ⟧ env_tele nil (List.rev (record_fctx R k ++ record_params R)) ms ↘ u /\ Dom t ≈ u ∈ per_univ j.
  Proof.
    intros * Hk HΓ HRΓ HMl HMs HMss HE Hlms0 Hgms Hms.
    set (C := record_fctx R k ++ record_params R) in *.
    assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hk).
    assert (HCa : all_assumptions C) by (apply record_fctx_params_ass; exact Hass).
    assert (HC : ⊨ C) by (apply record_fctx_sem; lia).
    assert (HlC : List.length Ms = List.length C) by (unfold C; rewrite List.length_app, length_record_fctx by lia; exact HMl).
    assert (Hlms : List.length ms = List.length C) by lia.
    destruct (field_typ_sort _ _ _ Hk) as (Srt & HS' & HU).
    pose proof (gsub_closed_inst C Γ Ms HCa HC HΓ HlC HMs HMss) as Hg.
    destruct (gsub_props Hg) as [Hτ _].
    assert (HUt : exists j : nat, C ⊨ᵗ U ≈ U at j /\ C ++ Γ ⊨ᵗ U ≈ U at j).
    { pose proof (closed_app_valid _ _ _ _ _ HCa HC HΓ HU) as HUΓ.
      destruct (rel_type_of_sort_ge (sort_kind_type_sort _ _ HS') HU) as [i1 H1];
        destruct (rel_type_of_sort_ge (sort_kind_type_sort _ _ HS') HUΓ) as [i2 H2].
      exists (max i1 i2); split; [ apply H1 | apply H2 ]; lia. }
    destruct HUt as (j & HUc & HUΓt).
    (** The substitution's value at [E], and the field's type there. *)
    destruct (closed_app_sem C Γ HCa HC HΓ) as [HCΓ Hres].
    destruct (rel_ctx_wf_per_ctx_env HC) as [RC HRC]; destruct (rel_ctx_wf_per_ctx_env HCΓ) as [RCΓ HRCΓ].
    destruct (rel_sub_under_ctx_simple Hτ) as (RΓ' & HRΓ' & RCΓ' & HRCΓ' & Hs).
    assert (E0 : RΓ <~> RΓ') by (eapply per_ctx_env_right_irrel; eassumption).
    assert (EC : RCΓ' <~> RCΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    destruct (Hs _ _ (proj1 (E0 _ _) HE)) as (X & X' & EvX & _ & HXX').
    assert (HPC : PER RCΓ) by (eapply per_env_PER; exact HRCΓ).
    assert (HXX : RCΓ X X) by (apply EC; etransitivity; [ exact HXX' | symmetry; exact HXX' ]).
    destruct (typ_inst_link _ _ _ _ _ _ _ _ _ HUΓt HRΓ Hτ HE EvX) as (t & b & Et & Eb & Htb).
    (** Its entries: the terms' values at the relevant ones, the terms kept
        as proofs at the propositional ones. *)
    assert (HlC' : List.length (List.rev C) = List.length Ms) by (rewrite List.length_rev; lia).
    rewrite <- (List.rev_involutive C) in EvX.
    destruct (eval_sb_of_list_sorted_split Ms (List.rev C) Id Γ E X (record_ctx_sort k) HlC' EvX) as (xs & Hlxs & Hxs & HXag).
    { intros x Hx Hr; rewrite List.rev_involutive; rewrite List.length_rev in Hx.
      refine (evaluated_entry_not_propositional C Γ RCΓ x HCa Hx _ HRCΓ X X HXX).
      intros Δ1 κ T Δ2 HD HΔ1; rewrite <- HΔ1 in Hr; exact (proj1 (record_ctx_entry_typed k Γ ltac:(lia) HΓ _ _ _ _ HD) Hr). }
    { intros x Hx Hp; rewrite List.rev_involutive; rewrite List.length_rev in Hx.
      refine (prop_entry_propositional C Γ RCΓ x HCa Hx _ HRCΓ X X HXX).
      intros Δ1 κ T Δ2 HD HΔ1; rewrite <- HΔ1 in Hp.
      exact (proj2 (record_ctx_entry_typed k Γ ltac:(lia) HΓ _ _ _ _ HD) Hp). }
    rewrite List.length_rev in HXag.
    (** The extension by these values over the tail, related at [C]. *)
    set (Y := env_extend_tagged Γ (List.rev C) (List.skipn (List.length C) X) xs) in *.
    assert (HYY : RCΓ Y Y)
      by (eapply (per_ctx_env_resp_agree HRCΓ); [ intros y _; apply HXag | intros y _; apply HXag | exact HXX ]).
    pose proof (Hres _ _ HRC HRCΓ _ _ HYY) as HYC.
    assert (HlxC : List.length (List.rev C) = List.length xs) by lia.
    unfold Y in HYC; rewrite env_extend_tagged_typed in HYC.
    assert (HRC' : EF List.rev (List.rev C) ++ ⋅ ≈ List.rev (List.rev C) ++ ⋅ ∈ per_ctx_env ↘ RC)
      by (rewrite List.rev_involutive, List.app_nil_r; exact HRC).
    assert (HCr : ⊨ List.rev (List.rev C) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HC).
    assert (HCra : all_assumptions (List.rev C)) by (apply List.Forall_rev; exact HCa).
    assert (Hlt : List.length (tagged_entries Γ (List.rev C) (List.skipn (List.length C) X) xs) = List.length (List.rev C))
      by (rewrite tagged_entries_length by exact HlxC; lia).
    destruct (per_tele_args_of_env_extend _ _ _ _ per_ctx_env_nil_true HCr HCra HRC' _ _ _ _ Hlt Hlt HYC) as [_ Hgx].
    destruct (per_tele_args_of_env_extend_readable _ _ _ _ per_ctx_env_nil_true HCr HCra HRC' _ _ _ _ Hlt Hlt HYC) as [Rx _].
    rewrite tagged_entries_fst in Hgx by exact HlxC.
    pose proof (per_tele_args_base _ _ _ per_ctx_env_nil_true HCr HCra _ _ nil nil _ _ I I I Hgx) as Hgx0.
    (** These values and [ms] differ only at the propositions. *)
    assert (Hgxm : per_tele_args (List.rev C) nil nil xs ms).
    { apply (per_tele_args_equal_up_to_proofs _ _ _ per_ctx_env_nil_true HCr HCra nil nil xs ms I Hgx0 Hgms ltac:(lia)).
      intros i x m Hx Hm.
      pose proof (nth_error_lt_length _ _ _ Hx) as Hix.
      destruct (nth_error_lt_some' Ms i ltac:(lia)) as [N HN].
      destruct (Hxs _ _ _ HN Hx) as [Hxr Hxp].
      destruct (evaluated_kind_or_propositional (record_ctx_sort k (List.length Ms - 1 - i))) as [Es | Es].
      - left; destruct (Hms _ _ _ HN Hm) as [Em | Ep]; [| rewrite Ep in Es; inversion Es ].
        eapply functional_eval_exp; [ exact (Hxr Es) | exact Em ].
      - right.
        assert (Hi : i < List.length (List.rev C)) by lia.
        destruct (nth_error_lt_some' (List.rev C) i Hi) as [e He].
        destruct (proj1 (List.Forall_forall _ _) HCra e (List.nth_error_In _ _ He)) as (κA & A & ->).
        exists κA, A; split; [ exact He |]; rewrite List.app_nil_r.
        (** The entry [i] of [rev C] is the entry [|C| - 1 - i] of [C]. *)
        destruct (List.nth_error_split _ _ He) as (l1 & l2 & Hrc & Hl1).
        assert (HD : C = List.rev l2 ++ ce_ass κA A :: List.rev l1)
          by (rewrite <- (List.rev_involutive C), Hrc, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity).
        assert (HlD : List.length (List.rev l2) = List.length Ms - 1 - i).
        { assert (Hcl : List.length (List.rev C) = List.length l1 + S (List.length l2))
            by (rewrite Hrc, List.length_app; cbn; lia).
          rewrite List.length_rev; rewrite List.length_rev in Hcl; lia. }
        pose proof (proj2 (record_ctx_entry_typed k ⋅ ltac:(lia) rel_ctx_wf_nil _ _ _ _ HD)) as Hp0.
        rewrite HlD in Hp0; pose proof (Hp0 Es) as Hp1; rewrite List.app_nil_r in Hp1.
        rewrite Hrc, List.firstn_app, <- Hl1, Nat.sub_diag, List.firstn_all; cbn [List.firstn]; rewrite !List.app_nil_r.
        exact Hp1. }
    (** So [X] and the values [ms] are related environments of [C]. *)
    pose proof (per_tele_args_entries_readable _ _ _ _ _ Hgms) as [Rms _].
    pose proof (per_tele_args_base _ _ _ per_ctx_env_nil_true HCr HCra nil nil (List.skipn (List.length C) X) nil _ _ I I I Hgxm) as Hgxm'.
    rewrite <- (tagged_entries_fst (List.rev C) Γ (List.skipn (List.length C) X) xs HlxC) in Hgxm'.
    rewrite <- (tele_entries_values ms nil (List.rev C)) in Hgxm'.
    assert (HXY : RC (env_extend_typed (List.skipn (List.length C) X) (tagged_entries Γ (List.rev C) (List.skipn (List.length C) X) xs))
                     (env_tele nil (List.rev C) ms))
      by (assert (Hlt2 : List.length (tele_entries nil (List.rev C) ms) = List.length (List.rev C))
            by (rewrite tele_entries_length, List.length_rev; lia);
          exact (tele_args_env_rel_typed _ _ _ _ per_ctx_env_nil_true HCr HCra HRC' _ _ _ _ I Hlt Hlt2 Hgxm' Rx Rms)).
    rewrite <- env_extend_tagged_typed in HXY.
    assert (HXY' : RC X (env_tele nil (List.rev C) ms))
      by (eapply (per_ctx_env_resp_agree HRC); [ intros y _; symmetry; apply HXag | reflexivity | exact HXY ]).
    destruct (rel_type_inversion_simple_at HRC HUc _ _ HXY') as (b1 & u & Eb1 & Eu & Hbu).
    assert (b1 = b) as -> by (eapply functional_eval_exp; eassumption).
    exists j, t, u; split; [ exact Et | split; [ exact Eu | etransitivity; [ exact Htb | exact Hbu ] ] ].
  Qed.

  (** A field's type is of the field's kind at every environment of the
      fields before it the context PER relates. *)
  Lemma field_type_kind : forall Γ j f U RCΓ ρ ρ' u, List.nth_error (record_fields R) j = Some (f, U) -> ⊨ Γ ->
      EF (record_fctx R j ++ record_params R) ++ Γ ≈ (record_fctx R j ++ record_params R) ++ Γ ∈ per_ctx_env ↘ RCΓ ->
      RCΓ ρ ρ' -> ⟦ U ⟧ ρ ↘ u -> domain_kind u = record_field_kind R j.
  Proof.
    intros * Hj HΓ HRCΓ Hρ Eu.
    assert (Hjl : j < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hj).
    assert (HCa : all_assumptions (record_fctx R j ++ record_params R)) by (apply record_fctx_params_ass; exact Hass).
    assert (HC : ⊨ record_fctx R j ++ record_params R) by (apply record_fctx_sem; lia).
    destruct (field_kind_cases j) as [Er | Er]; rewrite Er.
    - destruct (field_typ_large _ _ _ Hj Er) as [l HU].
      destruct (rel_exp_of_typ_relevant_at HRCΓ (closed_app_valid _ _ _ _ _ HCa HC HΓ HU) _ _ Hρ) as (u0 & Eu0 & Hr).
      assert (u0 = u) as -> by (eapply functional_eval_exp; eassumption); exact Hr.
    - pose proof (HT _ _ _ Hj) as HU; rewrite Er in HU; cbn [abs_kind_sort] in HU.
      destruct (rel_exp_of_prop_inversion_simple_at HRCΓ (closed_app_valid _ _ _ _ _ HCa HC HΓ HU) _ _ Hρ)
        as (a & a' & Ea & _ & [Hla _ _]).
      assert (a = u) as -> by (eapply functional_eval_exp; eassumption); exact Hla.
  Qed.

  (** ** Projections *)

  (** The projections of a scoped term are scoped. *)
  Lemma record_pre_scoped : forall n k M, exp_scoped n M -> List.Forall (exp_scoped n) (record_pre R k M).
  Proof.
    intros * HM; unfold record_pre; apply List.Forall_map, List.Forall_forall; intros; exact HM.
  Qed.

  (** Scoped parameters and the first [k] of scoped fields are scoped. *)
  Lemma tuple_prefix_scoped : forall n Ns Fs k, List.Forall (exp_scoped n) Ns -> List.Forall (exp_scoped n) Fs ->
      List.Forall (exp_scoped n) (Ns ++ List.firstn k Fs).
  Proof.
    intros * HNs HFs; apply List.Forall_app; split; [ exact HNs |].
    rewrite <- (List.firstn_skipn k Fs) in HFs; apply List.Forall_app in HFs as [H _]; exact H.
  Qed.

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
      destruct (tele_insts_nth _ _ _ _ _ HA) as (κA & A0 & HA0 & ->).
      rewrite rev_record_fctx, List.nth_error_firstn in HA0; destruct (Nat.ltb_spec j' k); [| lia ].
      destruct (field_tele_nth _ _ _ _ HA0) as (f1 & Hf1 & _); rewrite Hj' in Hf1; injection Hf1 as _ <-.
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
  Lemma params_inst_tele_args : forall Γ Ns RΓ E E' ns ns', ⊨ Γ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
      List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A -> Γ ⊨ N : A) ->
      List.Forall (exp_scoped (List.length Γ)) Ns ->
      RΓ E E' -> ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ ns -> ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ E' ↘ ns' ->
      per_tele_args (List.rev (record_params R)) nil nil ns ns'.
  Proof.
    intros * HΓ HRΓ Hn HNs HNss HE Ens Ens'.
    pose proof (gsub_closed_inst (record_params R) Γ Ns Hass record_params_sem HΓ Hn HNs HNss) as Hg.
    destruct (gsub_props Hg) as [Hτ _].
    destruct (rel_sub_under_ctx_simple Hτ) as (RΓ0 & HRΓ0 & RΔ0 & HRΔ0 & Hs).
    assert (E0 : RΓ <~> RΓ0) by (eapply per_ctx_env_right_irrel; eassumption).
    destruct (Hs _ _ (proj1 (E0 _ _) HE)) as (y1 & y2 & Ey1 & Ey2 & Hy).
    assert (Hrel : forall Δ1 κ T Δ2, record_params R = Δ1 ++ ce_ass κ T :: Δ2 -> exists i : nat, rel_param_typed (Δ2 ++ Γ) T i)
      by exact (closed_evaluated_over _ _ Hass record_params_sem HΓ HPr).
    assert (HlP : List.length (List.rev (record_params R)) = List.length Ns) by (rewrite List.length_rev; lia).
    assert (HPΔ : PER RΔ0) by (eapply per_env_PER; exact HRΔ0).
    assert (Hy11 : RΔ0 y1 y1) by (etransitivity; [ exact Hy | symmetry; exact Hy ]).
    assert (Hy22 : RΔ0 y2 y2) by (etransitivity; [ symmetry; exact Hy | exact Hy ]).
    assert (Hnp : forall y, RΔ0 y y -> forall x, x < List.length (List.rev (record_params R)) ->
                ~ entry_propositional gc_deps gc_stack (List.rev (List.rev (record_params R)) ++ Γ) y x)
      by (intros y Hyy x Hx; rewrite List.rev_involutive; rewrite List.length_rev in Hx;
          exact (evaluated_entries_not_propositional _ _ _ Hass Hrel HRΔ0 _ _ Hyy x Hx)).
    rewrite <- (List.rev_involutive (record_params R)) in Ey1, Ey2.
    destruct (eval_sb_of_list_inv _ _ _ _ _ _ _ HlP Ey1 (Hnp _ Hy11) (eval_sub_id _ _)) as (ms1 & Ems1 & A1).
    destruct (eval_sb_of_list_inv _ _ _ _ _ _ _ HlP Ey2 (Hnp _ Hy22) (eval_sub_id _ _)) as (ms2 & Ems2 & A2).
    pose proof (functional_eval_exps _ _ _ _ Ems1 Ens) as ->.
    pose proof (functional_eval_exps _ _ _ _ Ems2 Ens') as ->.
    assert (HEΔ : RΔ0 (env_extend_tagged Γ (List.rev (record_params R)) (ctx_retag Γ E) ns)
                      (env_extend_tagged Γ (List.rev (record_params R)) (ctx_retag Γ E') ns')).
    { rewrite List.length_rev in A1, A2.
      eapply (per_ctx_env_resp_agree HRΔ0); [ rewrite List.length_app; exact A1 | rewrite List.length_app; exact A2 | exact Hy ]. }
    destruct (closed_app_sem _ _ Hass record_params_sem HΓ) as [_ Hres].
    destruct (rel_ctx_wf_per_ctx_env record_params_sem) as [RQ HRQ].
    pose proof (Hres RQ RΔ0 HRQ HRΔ0 _ _ HEΔ) as HEQ.
    assert (HRQ' : EF List.rev (List.rev (record_params R)) ++ ⋅ ≈ List.rev (List.rev (record_params R)) ++ ⋅ ∈ per_ctx_env ↘ RQ)
      by (rewrite List.rev_involutive, List.app_nil_r; exact HRQ).
    pose proof (eval_exps_length _ _ _ Ens) as Hl1; pose proof (eval_exps_length _ _ _ Ens') as Hl2.
    assert (Hl1' : List.length (List.rev (record_params R)) = List.length ns) by (rewrite List.length_rev; lia).
    assert (Hl2' : List.length (List.rev (record_params R)) = List.length ns') by (rewrite List.length_rev; lia).
    rewrite !env_extend_tagged_typed in HEQ.
    destruct (per_tele_args_of_env_extend _ _ _ _ per_ctx_env_nil_true (rev_tele_sem _ record_params_sem) (rev_all_assumptions _ Hass) HRQ' _ _ _ _
                ltac:(rewrite tagged_entries_length by exact Hl1'; lia) ltac:(rewrite tagged_entries_length by exact Hl2'; lia) HEQ)
      as [_ Hgc].
    rewrite !tagged_entries_fst in Hgc by assumption.
    exact (per_tele_args_base _ _ _ per_ctx_env_nil_true (rev_tele_sem _ record_params_sem) (rev_all_assumptions _ Hass) _ _ nil nil _ _ I I I Hgc).
  Qed.

  (** The field [k] of equal elements of a record type at valid
      parameters, when the projections of the left one before it are
      valid: equal at the field's type at the parameters and those
      projections, whose instance of the fields' telescope is then
      valid. *)
  Lemma rel_exp_under_ctx_proj_core : forall Γ M M' Ns k f U, ⊨ Γ ->
      Γ ⊨ M ≈ M' : apps_exp (a_record p) Ns -> List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A -> Γ ⊨ N : A) ->
      List.Forall (exp_scoped (List.length Γ)) Ns -> exp_scoped (List.length Γ) M ->
      List.nth_error (record_fields R) k = Some (f, U) ->
      (forall j f0 U0, j < k -> List.nth_error (record_fields R) j = Some (f0, U0) ->
         Γ ⊨ a_proj f0 M : U0[sb_of_list Id (Ns ++ record_pre R j M)]) ->
      Γ ⊨ a_proj f M ≈ a_proj f M' : U[sb_of_list Id (Ns ++ record_pre R k M)].
  Proof.
    intros * HΓ HM Hn HNs HNss HMs Hjf HPs.
    assert (HMss : List.Forall (exp_scoped (List.length Γ)) (Ns ++ record_pre R k M))
      by (apply List.Forall_app; split; [ exact HNss | exact (record_pre_scoped _ k _ HMs) ]).
    assert (Hk0 : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hjf).
    pose proof (record_pre_insts Γ M Ns k Hn ltac:(lia) HNs HPs) as Hins.
    assert (HCa : all_assumptions (record_fctx R k ++ record_params R)) by (apply record_fctx_params_ass; exact Hass).
    assert (HC : ⊨ record_fctx R k ++ record_params R) by (apply record_fctx_sem; lia).
    assert (HlM : List.length (Ns ++ record_pre R k M) = k + List.length (record_params R))
      by (rewrite List.length_app, length_record_pre by lia; lia).
    assert (HlC : List.length (Ns ++ record_pre R k M) = List.length (record_fctx R k ++ record_params R))
      by (rewrite HlM, List.length_app, length_record_fctx by lia; reflexivity).
    pose proof (gsub_closed_inst _ Γ _ HCa HC HΓ HlC Hins HMss) as Hg.
    (** A propositional field: its projections are proofs. *)
    destruct (field_kind_cases k) as [Erk | Erk].
    2:{ apply rel_exp_under_ctx_proof.
        pose proof (HT _ _ _ Hjf) as HUp; rewrite Erk in HUp; cbn [abs_kind_sort] in HUp.
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
    apply (rel_exp_or_prop_evaluated Htyp (ex_intro _ (d_record p ns2) (conj Ea2 evaluated_kind_relevant))) in Hexp.
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
    (** The middle values are related arguments of the fields' telescope:
        the parameters' values and the middle projections, related to
        themselves. *)
    assert (Hm22 : RM m2 m2) by pairwise.
    destruct (proj1 (HE _ _) Hm22) as [P2a P2b HP2a HP2b Hr22].
    pose proof (record_projs_functional _ _ _ _ HP2a HP2) as ->.
    pose proof (record_projs_functional _ _ _ _ HP2b HP2) as ->.
    assert (Hgms : per_tele_args (List.rev (record_fctx R k ++ record_params R)) nil nil
                     (ns2 ++ List.firstn k P2) (ns2 ++ List.firstn k P2)).
    { pose proof (params_inst_tele_args Γ Ns RΓ ρσ ρσ ns2 ns2 HΓ HRΓ Hn HNs HNss Hρσρσ Ens2 Ens2) as Hgp.
      destruct (sort_tele_value _ _ record_params_sem HS _ Hgp Hln2) as [a Ha].
      pose proof (canon_fields_tele_args _ _ _ Hgp Hln2 Ha k (List.firstn k P2) (List.firstn k P2) ltac:(lia)
                    (tele_prefix_rel_of_full _ _ _ _ k Hr22 ltac:(lia))) as Hgf.
      rewrite List.rev_app_distr, rev_record_fctx.
      apply per_tele_args_app_intro; [ rewrite List.length_rev; exact Hln2 | exact Hgp | exact Hgf ]. }
    assert (Hlms : List.length (ns2 ++ List.firstn k P2) = List.length (Ns ++ record_pre R k M))
      by (rewrite HlM, List.length_app, List.length_firstn; lia).
    destruct (field_inst_link Γ k f U _ RΓ ρσ _ Hjf HΓ HRΓ HlM Hins HMss Hρσρσ Hlms Hgms) as (jb & t & u & Et & Eu & [Ru HRu]).
    { intros j N m HN Hm; left.
      destruct (eval_exps_nth _ _ _ _ _ Ems HN) as (m' & Hm' & Em'); rewrite Hm in Hm'; injection Hm' as <-; exact Em'. }
    assert (t = t2) as -> by (eapply functional_eval_exp; eassumption).
    assert (ERT : RT <~> Ru) by (eapply per_univ_chain_rel_irrel; [ exact Htch | exact HRu | solve_in ]).
    pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRu) HRu) as HRuu.
    assert (EQ : Q <~> RT).
    { unfold Q, canon_fields_rel; rewrite (nth_ftyp_eq _ _ _ _ Hjf).
      rewrite (record_fields_env_closed R ns2 (List.firstn k P2) Hln2), List.length_firstn, Nat.min_l by lia.
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
      List.Forall (exp_scoped (List.length Γ)) Ns -> exp_scoped (List.length Γ) M ->
      forall k f U, List.nth_error (record_fields R) k = Some (f, U) ->
        Γ ⊨ a_proj f M : U[sb_of_list Id (Ns ++ record_pre R k M)].
  Proof.
    intros * HΓ HM Hn HNs HNss HMs.
    enough (Hall : forall k, k <= List.length (record_fields R) -> forall j f U, j < k ->
              List.nth_error (record_fields R) j = Some (f, U) -> Γ ⊨ a_proj f M : U[sb_of_list Id (Ns ++ record_pre R j M)]).
    { intros k f U Hk; pose proof (nth_error_lt_length _ _ _ Hk) as Hkl.
      exact (Hall (S k) ltac:(lia) k f U ltac:(lia) Hk). }
    induction k as [| k IH]; intros Hk j f U Hj Hjf; [ lia |].
    destruct (Nat.lt_ge_cases j k) as [Hjk | Hjk]; [ exact (IH ltac:(lia) j f U Hjk Hjf) |].
    assert (j = k) as -> by lia.
    exact (rel_exp_under_ctx_proj_core Γ M M Ns k f U HΓ HM Hn HNs HNss HMs Hjf (fun j0 f0 U0 Hj0 => IH ltac:(lia) j0 f0 U0 Hj0)).
  Qed.

  (** The field [k] of equal elements: equal. *)
  Lemma rel_exp_under_ctx_proj_cong : forall Γ M M' Ns k f U, ⊨ Γ ->
      Γ ⊨ M ≈ M' : apps_exp (a_record p) Ns -> List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A -> Γ ⊨ N : A) ->
      List.Forall (exp_scoped (List.length Γ)) Ns -> exp_scoped (List.length Γ) M ->
      List.nth_error (record_fields R) k = Some (f, U) ->
      Γ ⊨ a_proj f M ≈ a_proj f M' : U[sb_of_list Id (Ns ++ record_pre R k M)].
  Proof.
    intros * HΓ HM Hn HNs HNss HMs Hjf.
    apply (rel_exp_under_ctx_proj_core _ _ _ _ _ _ _ HΓ HM Hn HNs HNss HMs Hjf).
    intros j f0 U0 _ Hj; exact (valid_exp_under_ctx_proj _ _ _ HΓ (rel_exp_under_ctx_refl_left HM) Hn HNs HNss HMs _ _ _ Hj).
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
      destruct (tele_insts_nth _ _ _ _ _ HA) as (κA & A0 & HA0 & ->).
      rewrite rev_record_fctx, List.nth_error_firstn in HA0; destruct (Nat.ltb_spec j' k); [| lia ].
      destruct (field_tele_nth _ _ _ _ HA0) as (f1 & Hf1 & _); rewrite Hj' in Hf1; injection Hf1 as _ <-.
      rewrite <- sb_of_list_app, List.firstn_firstn, Nat.min_l by lia.
      exact (HMs _ _ _ _ Hg Hj').
  Qed.

  (** Values canonically related at a prefix of the fields, after related
      parameters, are related arguments of each shorter prefix. *)
  Lemma prefix_tele_args : forall ns vs vs' a k, per_tele_args (List.rev (record_params R)) nil nil ns ns ->
      List.length ns = List.length (record_params R) -> ⟦ record_sort R ⟧ env_tele nil (List.rev (record_params R)) ns ↘ a ->
      k <= List.length (record_fields R) -> tele_prefix_rel (canon_fields_rel R ns) k vs vs' ->
      forall j, j <= k -> per_tele_args (List.rev (record_fctx R j ++ record_params R)) nil nil
                            (ns ++ List.firstn j vs) (ns ++ List.firstn j vs).
  Proof.
    intros * Hg Hln Ha Hk Hp j Hj.
    pose proof (tele_prefix_rel_of_pre _ _ _ _ j Hp Hj) as Hpj.
    pose proof (canon_fields_tele_args _ _ _ Hg Hln Ha j _ _ ltac:(lia) Hpj) as Hgf.
    assert (Hg' : per_tele_args (List.rev (record_fctx R j ++ record_params R)) nil nil
                    (ns ++ List.firstn j vs) (ns ++ List.firstn j vs')).
    { rewrite List.rev_app_distr, rev_record_fctx.
      apply per_tele_args_app_intro; [ rewrite List.length_rev; exact Hln | exact Hg | exact Hgf ]. }
    exact (record_params_args_refl_l _ (record_fctx_sem j ltac:(lia)) ltac:(apply record_fctx_params_ass; exact Hass) _ _ Hg').
  Qed.

  (** At a propositional field, after related values of the fields before
      it, the canonical relation relates any two readable proofs. *)
  Lemma field_canon_proof : forall k f U ns pre, List.nth_error (record_fields R) k = Some (f, U) ->
      record_field_kind R k = ak_propositional -> List.length ns = List.length (record_params R) -> List.length pre = k ->
      per_tele_args (List.rev (record_fctx R k ++ record_params R)) nil nil (ns ++ pre) (ns ++ pre) ->
      forall v v', proof_readable v -> proof_readable v' -> canon_fields_rel R ns k pre v v'.
  Proof.
    intros * Hk Hr Hln Hlp Hg v v' Hv Hv'.
    assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hk).
    assert (HC : ⊨ record_fctx R k ++ record_params R) by (apply record_fctx_sem; lia).
    destruct (rel_ctx_wf_per_ctx_env HC) as [RC HRC].
    assert (HE : RC (env_tele nil (List.rev (record_fctx R k ++ record_params R)) (ns ++ pre))
                    (env_tele nil (List.rev (record_fctx R k ++ record_params R)) (ns ++ pre)))
      by (apply (tele_args_env_rel _ _ _ _ _ _ HRC HC); [ rewrite !List.length_app, length_record_fctx by lia; lia | exact Hg ]).
    pose proof (HT _ _ _ Hk) as HU; rewrite Hr in HU; cbn [abs_kind_sort] in HU.
    destruct (rel_exp_of_prop_inversion_simple_at HRC HU _ _ HE) as (u & _ & Eu & _ & [Hu _ _]).
    unfold canon_fields_rel; rewrite (nth_ftyp_eq _ _ _ _ Hk), (record_fields_env_closed R ns pre Hln), Hlp.
    exact (per_head_proof Eu Hu Hv Hv').
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
      List.Forall (exp_scoped (List.length Γ)) Ns -> List.Forall (exp_scoped (List.length Γ)) (List.map snd fs) ->
      Γ ⊨ a_tuple T fs : T.
  Proof.
    intros * HΓ HTeq Hn HNs Hfs HMs HNss HFss.
    assert (Hlf : List.length fs = List.length (record_fields R))
      by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
    assert (Hpss : forall k, List.Forall (exp_scoped (List.length Γ)) (Ns ++ List.firstn k (List.map snd fs)))
      by (intros k; exact (tuple_prefix_scoped _ _ _ _ HNss HFss)).
    pose proof (rel_exp_under_ctx_refl_left HTeq) as HTl.
    destruct (rel_type_inversion (rel_type_of_typ HTl)) as [RΓ [HRΓ HTgen]].
    (** A relevant field's instance type is a type of a universe. *)
    assert (HUk : forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
               record_field_kind R k = ak_relevant ->
               exists j : nat, Γ ⊨ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] : Typeω@j).
    { intros k f M U Hk Hfk Hr.
      assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
      assert (HCa : all_assumptions (record_fctx R k ++ record_params R)) by (apply record_fctx_params_ass; exact Hass).
      assert (HC : ⊨ record_fctx R k ++ record_params R) by (apply record_fctx_sem; lia).
      assert (HlC : List.length (Ns ++ List.firstn k (List.map snd fs)) = List.length (record_fctx R k ++ record_params R))
        by (rewrite !List.length_app, List.length_firstn, List.length_map, length_record_fctx by lia; lia).
      pose proof (gsub_closed_inst _ Γ _ HCa HC HΓ HlC (tuple_insts Γ Ns fs Hn HNs Hfs HMs k ltac:(lia)) (Hpss k)) as Hg.
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
    pose proof (params_inst_tele_args Γ Ns RΓ ρσ ρσ ns2 ns2 HΓ HRΓ Hn HNs HNss Hρσρσ Ens2 Ens2) as Hgp.
    destruct (sort_tele_value _ _ record_params_sem HS _ Hgp Hln2) as [a Ha].
    (** Each relevant field: its four values, related at the relation of its
        instance type at the middle *)
    assert (Hch : forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
               record_field_kind R k = ak_relevant ->
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
      assert (Hev2 : evaluated_kind (domain_kind b2)) by (rewrite Hr0; constructor).
      apply (rel_exp_or_prop_evaluated Htyp (ex_intro _ b2 (conj Eb2 Hev2))) in Hexp.
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
    set (rs := record_field_kinds R).
    destruct (eval_field_vals_each (List.map (fun f => (snd f)[σ]) fs) rs ρ) as [V1 EV1].
    { intros m M' Hm Hr; rewrite List.nth_error_map in Hm.
      destruct (List.nth_error fs m) as [[g M] |] eqn:Hg; cbn in Hm; [ injection Hm as <- | discriminate ].
      destruct (Hnm _ _ _ Hg) as [U HU]; destruct (Hch _ _ _ _ Hg HU (field_kind_evaluated_relevant m Hr)) as (Rk & w1 & _ & _ & _ & _ & _ & Ew1 & _); eauto. }
    destruct (eval_field_vals_each (List.map snd fs) rs ρσ) as [V2 EV2].
    { intros m M' Hm Hr; rewrite List.nth_error_map in Hm.
      destruct (List.nth_error fs m) as [[g M] |] eqn:Hg; cbn in Hm; [ injection Hm as <- | discriminate ].
      destruct (Hnm _ _ _ Hg) as [U HU]; destruct (Hch _ _ _ _ Hg HU (field_kind_evaluated_relevant m Hr)) as (Rk & _ & w2 & _ & _ & _ & _ & _ & Ew2 & _); eauto. }
    destruct (eval_field_vals_each (List.map snd fs) rs ρ'σ') as [V3 EV3].
    { intros m M' Hm Hr; rewrite List.nth_error_map in Hm.
      destruct (List.nth_error fs m) as [[g M] |] eqn:Hg; cbn in Hm; [ injection Hm as <- | discriminate ].
      destruct (Hnm _ _ _ Hg) as [U HU]; destruct (Hch _ _ _ _ Hg HU (field_kind_evaluated_relevant m Hr)) as (Rk & _ & _ & w3 & _ & _ & _ & _ & _ & Ew3 & _); eauto. }
    destruct (eval_field_vals_each (List.map (fun f => (snd f)[σ']) fs) rs ρ') as [V4 EV4].
    { intros m M' Hm Hr; rewrite List.nth_error_map in Hm.
      destruct (List.nth_error fs m) as [[g M] |] eqn:Hg; cbn in Hm; [ injection Hm as <- | discriminate ].
      destruct (Hnm _ _ _ Hg) as [U HU]; destruct (Hch _ _ _ _ Hg HU (field_kind_evaluated_relevant m Hr)) as (Rk & _ & _ & _ & w4 & _ & _ & _ & _ & _ & Ew4 & _); eauto. }
    pose proof (eval_field_vals_length _ _ _ _ EV1) as Hl1; pose proof (eval_field_vals_length _ _ _ _ EV2) as Hl2.
    pose proof (eval_field_vals_length _ _ _ _ EV3) as Hl3; pose proof (eval_field_vals_length _ _ _ _ EV4) as Hl4.
    rewrite List.length_map in Hl1, Hl2, Hl3, Hl4.
    (** Each field's values in the lists: readable kept proofs at a
        propositional field, as the field is scoped, the related values at
        a relevant one *)
    pose proof Hσ as [? _ ? _ _ Hσs].
    assert (Hfv : forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
               exists v1 v2 v3 v4, List.nth_error V1 k = Some v1 /\ List.nth_error V2 k = Some v2 /\
                 List.nth_error V3 k = Some v3 /\ List.nth_error V4 k = Some v4 /\
                 (record_field_kind R k = ak_propositional ->
                    proof_readable v1 /\ proof_readable v2 /\ proof_readable v3 /\ proof_readable v4) /\
                 (record_field_kind R k = ak_relevant -> exists Rk b (jb : nat), Rk v1 v2 /\ Rk v2 v3 /\ Rk v3 v4 /\
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
      split.
      { intros Hp; rewrite (Pv1 Hp), (Pv2 Hp), (Pv3 Hp), (Pv4 Hp).
        assert (HMsc : exp_scoped (List.length Γ) M)
          by exact (proj1 (List.Forall_forall _ _) HFss M (List.nth_error_In _ _ HM2)).
        assert (HMσ : exp_scoped (List.length Γ') M[σ])
          by (eapply exp_scoped_sub; [ exact HMsc | intros x Hx; exact (proj1 (Hσs x Hx)) ]).
        assert (HMσ' : exp_scoped (List.length Γ') M[σ'])
          by (eapply exp_scoped_sub; [ exact HMsc | intros x Hx; exact (proj2 (Hσs x Hx)) ]).
        destruct (per_ctx_env_kept_proof_readable _ _ _ M[σ] HΓ' (exp_scoped_free_bound _ _ HMσ) _ _ Hρ) as [Rp1 _].
        destruct (per_ctx_env_kept_proof_readable _ _ _ M[σ'] HΓ' (exp_scoped_free_bound _ _ HMσ') _ _ Hρ) as [_ Rp4].
        destruct (per_ctx_env_kept_proof_readable _ _ _ M HRΓ (exp_scoped_free_bound _ _ HMsc) _ _ Hρσ) as [Rp2 Rp3].
        repeat split; assumption. }
      intros Hr.
      assert (Hevk : evaluated_kind (List.nth k rs ak_relevant))
        by (unfold rs; change (evaluated_kind (record_field_kind R k)); rewrite Hr; constructor).
      destruct (Hch _ _ _ _ Hk Hfk Hr) as (Rk & w1 & w2 & w3 & w4 & b & jb & Ew1 & Ew2 & Ew3 & Ew4 & Hwch & Eb & Hbb).
      assert (v1 = w1) as -> by (eapply functional_eval_exp; [ exact (Ev1 Hevk) | exact Ew1 ]).
      assert (v2 = w2) as -> by (eapply functional_eval_exp; [ exact (Ev2 Hevk) | exact Ew2 ]).
      assert (v3 = w3) as -> by (eapply functional_eval_exp; [ exact (Ev3 Hevk) | exact Ew3 ]).
      assert (v4 = w4) as -> by (eapply functional_eval_exp; [ exact (Ev4 Hevk) | exact Ew4 ]).
      exists Rk, b, jb; destruct Hwch as (Hw12 & Hw23 & Hw34); repeat split; assumption. }
    (** The canonical relations at the middle prefixes: a relevant field's,
        the relation of its instance type; a propositional field's, relating
        the proofs *)
    assert (Hcan : forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
               tele_prefix_rel (canon_fields_rel R ns2) k (List.firstn k V2) (List.firstn k V3) ->
               (record_field_kind R k = ak_propositional -> forall v v', proof_readable v -> proof_readable v' ->
                  canon_fields_rel R ns2 k (List.firstn k V2) v v') /\
               (forall Rk b (jb : nat), ⟦ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] ⟧ ρσ ↘ b ->
                  DF b ≈ b ∈ per_univ_elem jb ↘ Rk -> (Rk <~> canon_fields_rel R ns2 k (List.firstn k V2)))).
    { intros k f M U Hk Hfk Hpre.
      assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
      pose proof (prefix_tele_args _ _ _ _ k Hgp Hln2 Ha ltac:(lia) Hpre) as Hgj.
      assert (Hlk : List.length (List.firstn k V2) = k) by (rewrite List.length_firstn; lia).
      split.
      - intros Hp v v' Hv Hv'; refine (field_canon_proof _ _ _ _ _ Hfk Hp Hln2 Hlk _ v v' Hv Hv').
        pose proof (Hgj k (le_n _)) as H; rewrite List.firstn_firstn, Nat.min_id in H; exact H.
      - intros Rk b jb Eb Hbb.
        assert (HlM : List.length (Ns ++ List.firstn k (List.map snd fs)) = k + List.length (record_params R))
          by (rewrite List.length_app, List.length_firstn, List.length_map; lia).
        pose proof (Hgj k (le_n _)) as Hgk; rewrite List.firstn_firstn, Nat.min_id in Hgk.
        destruct (field_inst_link Γ k f U _ RΓ ρσ (ns2 ++ List.firstn k V2) Hfk HΓ HRΓ HlM
                    (tuple_insts Γ Ns fs Hn HNs Hfs HMs k ltac:(lia)) (Hpss k) Hρσρσ
                    ltac:(rewrite !List.length_app, !List.length_firstn, List.length_map; lia) Hgk
                    (tuple_prefix_vals_sorted _ _ _ _ _ k Ens2 EV2 ltac:(rewrite List.length_map; lia)))
          as (jb' & t & u & Et & Eu & [Ru HRu]).
        assert (t = b) as -> by (eapply functional_eval_exp; eassumption).
        assert (ERk : Rk <~> Ru) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hbb HRu).
        pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRu) HRu) as HRuu.
        unfold canon_fields_rel; rewrite (nth_ftyp_eq _ _ _ _ Hfk).
        rewrite (record_fields_env_closed R ns2 (List.firstn k V2) Hln2), Hlk.
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
      destruct (field_kind_cases k) as [Er | Er].
      - destruct (Hrel Er) as (Rk & b & jb & _ & H23 & _ & Eb & Hbb); apply (Cr _ _ _ Eb Hbb); exact H23.
      - destruct (Hprop Er) as (_ & Rpx & Rpy & _); exact (Cp Er _ _ Rpx Rpy). }
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
      destruct (field_kind_cases k) as [Er | Er].
      - destruct (Hrel Er) as (Rk & b & jb & H12 & _ & _ & Eb & Hbb); apply (Cr _ _ _ Eb Hbb); exact H12.
      - destruct (Hprop Er) as (Rpx & Rpy & _ & _); exact (Cp Er _ _ Rpx Rpy). }
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
      destruct (field_kind_cases k) as [Er | Er].
      - destruct (Hrel Er) as (Rk & b & jb & _ & _ & H34 & Eb & Hbb); apply (Cr _ _ _ Eb Hbb); exact H34.
      - destruct (Hprop Er) as (_ & _ & Rpx & Rpy); exact (Cp Er _ _ Rpx Rpy). }
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
    (** The type is a record type, not [LevelSort]. *)
    assert (HTn : rel_type_not_level_sort Γ (apps_exp (a_record p) Ns)).
    { apply (rel_type_not_level_sort_of_values HM); intros ρ0 a0 Ea0.
      destruct (eval_record_apps_inv _ _ _ Ea0 Hn) as (ns0 & _ & ->); discriminate. }
    destruct (presup_rel_exp_under_ctx HM HTn) as [iT HT0].
    destruct (rel_type_inversion_simple_at HRΓ HT0 _ _ Hρ) as (a & a' & Ea & Ea' & [X HX]).
    destruct (eval_record_apps_inv _ _ _ Ea Hn) as (ns & _ & ->).
    destruct (eval_record_apps_inv _ _ _ Ea' Hn) as (ns' & _ & ->).
    pose proof (per_univ_elem_record_facts _ _ _ _ _ _ Hl HX) as [_ Hln _ _ HfP HfI HfE HfS HEX].
    pose proof (per_head_iff Ea Ea' HX) as EH.
    destruct (rel_exp_under_ctx_simple_at HRΓ HM _ _ Hρ) as [(a0 & Ea0 & Hp) | (m & m' & Em & Em' & Hmm)].
    { assert (a0 = d_record p ns) as -> by (eapply functional_eval_exp; eassumption); discriminate. }
    apply EH, HEX in Hmm; destruct Hmm as [P P' HP HP' Hrel].
    pose proof (List.Forall2_length HP) as HlP; pose proof (List.Forall2_length HP') as HlP'.
    (** The tuple of the projections at the right environment: the
        projections of the right value at the relevant fields, the kept
        proofs at the propositional ones. *)
    set (Fs := List.map snd (record_eta_fields R M)).
    assert (HFs : forall k N, List.nth_error Fs k = Some N ->
               exists f U, List.nth_error (record_fields R) k = Some (f, U) /\ N = a_proj f M).
    { intros k N HN; unfold Fs, record_eta_fields in HN; rewrite List.map_map, List.nth_error_map in HN.
      destruct (List.nth_error (record_fields R) k) as [[f U] |] eqn:Hk; cbn in HN; [ injection HN as <-; eauto | discriminate ]. }
    destruct (eval_field_vals_each Fs (record_field_kinds R) ρ') as [P'' Ew].
    { intros k N HN _; destruct (HFs _ _ HN) as (f & U & Hk & ->).
      destruct (nth_error_lt_some' P' k ltac:(pose proof (nth_error_lt_length _ _ _ Hk); lia)) as [v' Hv'].
      exists v'; econstructor; [ exact Em' | exact (Forall2_nth_both _ _ _ _ _ _ HP' Hk Hv') ]. }
    pose proof (eval_field_vals_length _ _ _ _ Ew) as HlP''.
    assert (HlFs : List.length Fs = List.length (record_fields R))
      by (unfold Fs, record_eta_fields; rewrite !List.length_map; reflexivity).
    assert (Et'' : ⟦ a_tuple (apps_exp (a_record p) Ns) (record_eta_fields R M) ⟧ ρ' ↘
                     d_tuple (List.combine (List.map fst (record_eta_fields R M)) P''))
      by (eapply eval_exp_tuple; [ exact Ea' | exact Hl | exact Ew ]).
    (** The tuple's values related, by its validity: its kept proofs read
        back. *)
    destruct (rel_exp_under_ctx_simple_at HRΓ Ht _ _ Hρ) as [(a0 & Ea0 & Hp) | (t & t' & Et & Et' & Htt)].
    { assert (a0 = d_record p ns) as -> by (eapply functional_eval_exp; eassumption); discriminate. }
    assert (t' = d_tuple (List.combine (List.map fst (record_eta_fields R M)) P'')) as ->
      by (eapply functional_eval_exp; [ exact Et' | exact Et'' ]).
    apply EH, HEX in Htt; destruct Htt as [Q Q'' HQ HQ'' Hrel'].
    assert (Q'' = P'') as -> by exact (record_projs_functional _ _ _ _ HQ'' (tuple_projs _ P'' (record_eta_fields_names R M) ltac:(lia))).
    exists m, (d_tuple (List.combine (List.map fst (record_eta_fields R M)) P'')).
    split; [ exact Em | split; [ exact Et'' |] ].
    apply EH, HEX; refine (mk_record_rel _ _ _ _ P P'' HP (tuple_projs _ P'' (record_eta_fields_names R M) ltac:(lia)) _).
    (** Field by field: the right value's projection at a relevant field,
        two readable proofs at a propositional one. *)
    rewrite tele_rel_iff; split; [ lia | split; [ lia |] ].
    intros k v v'' Hv Hv''.
    assert (Hkl : k < List.length (record_fields R)) by (pose proof (nth_error_lt_length _ _ _ Hv); lia).
    destruct (nth_error_lt_some' (record_fields R) k Hkl) as [[f U] Hk].
    destruct (nth_error_lt_some' P' k ltac:(lia)) as [v' Hv'].
    pose proof Hrel as H; rewrite tele_rel_iff in H; destruct H as (_ & _ & H); pose proof (H _ _ _ Hv Hv') as Hcv.
    assert (HN : List.nth_error Fs k = Some (a_proj f M))
      by (unfold Fs, record_eta_fields; rewrite List.map_map, List.nth_error_map, Hk; reflexivity).
    destruct (eval_field_vals_nth _ _ _ _ Ew _ _ HN) as (w & Hw & Ew1 & Ew2); rewrite Hv'' in Hw; injection Hw as <-.
    destruct (field_kind_cases k) as [Er | Er].
    - assert (v'' = v') as ->.
      { eapply functional_eval_exp; [ exact (Ew1 (field_relevant_evaluated k Er)) |].
        econstructor; [ exact Em' | exact (Forall2_nth_both _ _ _ _ _ _ HP' Hk Hv') ]. }
      exact Hcv.
    - pose proof (tele_prefix_rel_of_full _ _ _ _ k Hrel ltac:(lia)) as Hpre.
      destruct (HfS _ _ _ _ _ Hk Hpre) as (u & Eu & Hu); rewrite Er in Hu.
      destruct (HfE _ _ _ _ _ Hk Hpre) as [u0 u0' Eu0 Eu0' HRu].
      assert (u0 = u) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (proj1 (per_univ_elem_propositional _ _ _ _ HRu Hu _ _) Hcv) as [Rv _].
      (** The tuple's kept proof, related to the left tuple's value. *)
      destruct (nth_error_lt_some' Q k ltac:(pose proof (List.Forall2_length HQ); lia)) as [w0 Hw0].
      pose proof Hrel' as H'; rewrite tele_rel_iff in H'; destruct H' as (_ & _ & H'); pose proof (H' _ _ _ Hw0 Hv'') as Hcq.
      pose proof (tele_prefix_rel_of_full _ _ _ _ k Hrel' ltac:(lia)) as Hpre'.
      destruct (HfS _ _ _ _ _ Hk Hpre') as (u1 & Eu1 & Hu1); rewrite Er in Hu1.
      destruct (HfE _ _ _ _ _ Hk Hpre') as [u2 u2' Eu2 Eu2' HRu2].
      assert (u2 = u1) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (proj1 (per_univ_elem_propositional _ _ _ _ HRu2 Hu1 _ _) Hcq) as [_ Rv''].
      exact (proj2 (per_univ_elem_propositional _ _ _ _ HRu Hu _ _) (conj Rv Rv'')).
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
      List.Forall (exp_scoped (List.length Γ)) Ns -> List.Forall (exp_scoped (List.length Γ)) (List.map snd fs) ->
      List.Forall (exp_scoped (List.length Γ)) (List.map snd fs') ->
      Γ ⊨ a_tuple T fs ≈ a_tuple T' fs' : T.
  Proof.
    intros * HΓ Ht HTT HTeq Hn HNs Hfs Hfs' HMM Ht' HNss HFss HFss'.
    assert (Hpss : forall k, List.Forall (exp_scoped (List.length Γ)) (Ns ++ List.firstn k (List.map snd fs)))
      by (intros k; exact (tuple_prefix_scoped _ _ _ _ HNss HFss)).
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
               record_field_kind R k = ak_relevant ->
               exists j : nat, Γ ⊨ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] : Typeω@j).
    { intros k f M U Hk Hfk Hr.
      assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
      assert (HCa : all_assumptions (record_fctx R k ++ record_params R)) by (apply record_fctx_params_ass; exact Hass).
      assert (HC : ⊨ record_fctx R k ++ record_params R) by (apply record_fctx_sem; lia).
      assert (HlC : List.length (Ns ++ List.firstn k (List.map snd fs)) = List.length (record_fctx R k ++ record_params R))
        by (rewrite !List.length_app, List.length_firstn, List.length_map, length_record_fctx by lia; lia).
      pose proof (gsub_closed_inst _ Γ _ HCa HC HΓ HlC (tuple_insts Γ Ns fs Hn HNs Hfs HMs k ltac:(lia)) (Hpss k)) as Hg.
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
    pose proof (params_inst_tele_args Γ Ns RΓ ρ ρ ns ns HΓ HRΓ Hn HNs HNss Hρρ Ens Ens) as Hgp.
    destruct (sort_tele_value _ _ record_params_sem HS _ Hgp Hlns) as [a0 Ha0].
    (** The two annotations evaluate to record type formers. *)
    destruct (per_univ_elem_record_right _ _ _ _ _ HRx) as [ns1 ->].
    destruct (rel_exp_of_typ_inversion_simple_at HRΓ HTT _ _ Hρ) as (t1 & t1' & Et1 & Et1' & [R1 HR1]).
    assert (t1 = d_record p ns1) as -> by (eapply functional_eval_exp; eassumption).
    destruct (per_univ_elem_record_left _ _ _ _ _ HR1) as [ns1' ->].
    (** Each relevant field: its values at the two environments, related at
        its instance type *)
    assert (Hch : forall k f M M' U, List.nth_error fs k = Some (f, M) -> List.nth_error fs' k = Some (f, M') ->
               List.nth_error (record_fields R) k = Some (f, U) -> record_field_kind R k = ak_relevant ->
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
    set (rs := record_field_kinds R).
    destruct (eval_field_vals_each (List.map snd fs) rs ρ) as [V EV].
    { intros m M Hm Hr; rewrite List.nth_error_map in Hm.
      destruct (List.nth_error fs m) as [[g M0] |] eqn:Hg; cbn in Hm; [ injection Hm as <- | discriminate ].
      destruct (Hnm _ _ _ Hg) as (U & M' & HU & HM');
        destruct (Hch _ _ _ _ _ Hg HM' HU (field_kind_evaluated_relevant m Hr)) as (v & _ & _ & _ & _ & _ & Ev & _); eauto. }
    destruct (eval_field_vals_each (List.map snd fs') rs ρ') as [V' EV'].
    { intros m M' Hm Hr; rewrite List.nth_error_map in Hm.
      destruct (List.nth_error fs' m) as [[g M0'] |] eqn:Hg'; cbn in Hm; [ injection Hm as <- | discriminate ].
      destruct (nth_error_lt_some' fs m) as [[g0 M0] Hg]; [ rewrite <- Hlf'; exact (nth_error_lt_length _ _ _ Hg') |].
      destruct (Hnm _ _ _ Hg) as (U & M1 & HU & HM1); rewrite Hg' in HM1; injection HM1 as <- <-.
      destruct (Hch _ _ _ _ _ Hg Hg' HU (field_kind_evaluated_relevant m Hr)) as (_ & v' & _ & _ & _ & _ & _ & Ev' & _); eauto. }
    pose proof (eval_field_vals_length _ _ _ _ EV) as HlV; pose proof (eval_field_vals_length _ _ _ _ EV') as HlV'.
    rewrite List.length_map in HlV, HlV'.
    (** Each field's values in the lists *)
    assert (Hfv : forall k f M M' U, List.nth_error fs k = Some (f, M) -> List.nth_error fs' k = Some (f, M') ->
               List.nth_error (record_fields R) k = Some (f, U) ->
               exists v v', List.nth_error V k = Some v /\ List.nth_error V' k = Some v' /\
                 (record_field_kind R k = ak_propositional -> proof_readable v /\ proof_readable v') /\
                 (record_field_kind R k = ak_relevant -> exists b b' Rb (jb : nat),
                    ⟦ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] ⟧ ρ ↘ b /\
                    ⟦ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] ⟧ ρ' ↘ b' /\
                    DF b ≈ b' ∈ per_univ_elem jb ↘ Rb /\ Rb v v')).
    { intros k f M M' U Hk Hk' Hfk.
      assert (HM1 : List.nth_error (List.map snd fs) k = Some M) by (rewrite List.nth_error_map, Hk; reflexivity).
      assert (HM2 : List.nth_error (List.map snd fs') k = Some M') by (rewrite List.nth_error_map, Hk'; reflexivity).
      destruct (eval_field_vals_nth _ _ _ _ EV _ _ HM1) as (v & Hv & Ev & Pv).
      destruct (eval_field_vals_nth _ _ _ _ EV' _ _ HM2) as (v' & Hv' & Ev' & Pv').
      exists v, v'; split; [ exact Hv | split; [ exact Hv' |] ].
      split.
      { intros Hp; rewrite (Pv Hp), (Pv' Hp).
        assert (HMsc : exp_scoped (List.length Γ) M)
          by exact (proj1 (List.Forall_forall _ _) HFss M (List.nth_error_In _ _ HM1)).
        assert (HM'sc : exp_scoped (List.length Γ) M')
          by exact (proj1 (List.Forall_forall _ _) HFss' M' (List.nth_error_In _ _ HM2)).
        split; [ exact (proj1 (per_ctx_env_kept_proof_readable _ _ _ M HRΓ (exp_scoped_free_bound _ _ HMsc) _ _ Hρ))
               | exact (proj2 (per_ctx_env_kept_proof_readable _ _ _ M' HRΓ (exp_scoped_free_bound _ _ HM'sc) _ _ Hρ)) ]. }
      intros Hr.
      destruct (Hch _ _ _ _ _ Hk Hk' Hfk Hr) as (w & w' & b & b' & Rb & jb & Ew & Ew' & Eb & Eb' & HRb & Hww).
      assert (v = w) as -> by (eapply functional_eval_exp; [ exact (Ev (field_relevant_evaluated k Hr)) | exact Ew ]).
      assert (v' = w') as -> by (eapply functional_eval_exp; [ exact (Ev' (field_relevant_evaluated k Hr)) | exact Ew' ]).
      exists b, b', Rb, jb; repeat split; assumption. }
    (** The canonical relations at the left prefixes *)
    assert (Hcan : forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
               tele_prefix_rel (canon_fields_rel R ns) k (List.firstn k V) (List.firstn k V') ->
               (record_field_kind R k = ak_propositional -> forall v v', proof_readable v -> proof_readable v' ->
                  canon_fields_rel R ns k (List.firstn k V) v v') /\
               (forall b b' Rb (jb : nat), ⟦ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] ⟧ ρ ↘ b ->
                  DF b ≈ b' ∈ per_univ_elem jb ↘ Rb -> (Rb <~> canon_fields_rel R ns k (List.firstn k V)))).
    { intros k f M U Hk Hfk Hpre.
      assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
      pose proof (prefix_tele_args _ _ _ _ k Hgp Hlns Ha0 ltac:(lia) Hpre) as Hgj.
      assert (Hlk : List.length (List.firstn k V) = k) by (rewrite List.length_firstn; lia).
      split.
      - intros Hp v v' Hv Hv'; refine (field_canon_proof _ _ _ _ _ Hfk Hp Hlns Hlk _ v v' Hv Hv').
        pose proof (Hgj k (le_n _)) as H; rewrite List.firstn_firstn, Nat.min_id in H; exact H.
      - intros b b' Rb jb Eb HRb.
        assert (HlM : List.length (Ns ++ List.firstn k (List.map snd fs)) = k + List.length (record_params R))
          by (rewrite List.length_app, List.length_firstn, List.length_map; lia).
        pose proof (Hgj k (le_n _)) as Hgk; rewrite List.firstn_firstn, Nat.min_id in Hgk.
        destruct (field_inst_link Γ k f U _ RΓ ρ (ns ++ List.firstn k V) Hfk HΓ HRΓ HlM
                    (tuple_insts Γ Ns fs Hn HNs Hfs HMs k ltac:(lia)) (Hpss k) Hρρ
                    ltac:(rewrite !List.length_app, !List.length_firstn, List.length_map; lia) Hgk
                    (tuple_prefix_vals_sorted _ _ _ _ _ k Ens EV ltac:(rewrite List.length_map; lia)))
          as (jb' & t2 & u & Et2 & Eu & [Ru HRu]).
        assert (t2 = b) as -> by (eapply functional_eval_exp; eassumption).
        assert (ERb : Rb <~> Ru) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRb HRu).
        pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRu) HRu) as HRuu.
        unfold canon_fields_rel; rewrite (nth_ftyp_eq _ _ _ _ Hfk).
        rewrite (record_fields_env_closed R ns (List.firstn k V) Hlns), Hlk.
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
    destruct (field_kind_cases k) as [Er | Er].
    - destruct (Hrel Er) as (b & b' & Rb & jb & Eb & _ & HRb & Hxy); apply (Cr _ _ _ _ Eb HRb); exact Hxy.
    - destruct (Hprop Er) as (Rpx & Rpy); exact (Cp Er _ _ Rpx Rpy).
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
    field_index fs f = Some k -> record_field_kind R k = ak_relevant ->
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
  assert (x = m) as -> by (eapply functional_eval_exp; [ exact (Hrel (field_relevant_evaluated R k Hr)) | exact Em ]).
  exists m, m'; split; [ exact Ex | split; [ exact Em' | exact Hmm ] ].
Qed.

End Fixed_GCtx.
