(** * Telescopes in the PER Model

    The types of an inductive declaration live in closed contexts, and its
    eliminator binds telescopes of them.  This file relates the three ways
    the proofs meet a telescope:

    - as arguments related at it, one at a time ([per_gargs]);
    - as an environment of a context extended by it ([per_ctx_env]);
    - as the argument of the [Π] it makes ([ctx_pi]).

    A closed telescope is read in any base environment: arguments related at
    it over one pair of bases are related over any other ([per_gargs_base]),
    which is how the proofs move between the environments of a judgment and
    the empty environment the PER clause of an inductive type reads its
    telescopes in. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax.
From Mctt.Core.Semantic.PER Require Import Tele.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Environments Extended by Values

    Environments extended by values carry the types of their entries:
    the arguments of a telescope ([env_tele]) the closures of its types,
    the closures of a Π the values of their domains, the extensions a
    substitution evaluates to the tags of their context's entries
    ([centry_tag]).  The context PERs care
    about these types only through their readability, so statements over
    a context PER take the extensions with any types. *)

(** An argument at the head of a telescope extends the environment at the
    closure of its type there. *)
Lemma env_tele_cons : forall ρ A T x xs,
    env_tele ρ (ce_ass A :: T) (x :: xs) = env_tele (ρ ↦ x ⦂ entry_type_closure A ρ) T xs.
Proof. reflexivity. Qed.

(** One more argument of a telescope, at the type of its entry. *)
Lemma env_tele_snoc_at : forall ρ T vs A v, List.nth_error T (List.length vs) = Some (ce_ass A) ->
    env_tele ρ T (vs ++ v :: nil) = env_tele ρ T vs ↦ v ⦂ entry_type_closure A (env_tele ρ T vs).
Proof.
  intros * HA.
  assert (Hlt : List.length vs < List.length T) by (apply List.nth_error_Some; congruence).
  rewrite env_tele_firstn, List.length_app, Nat.add_1_r.
  rewrite (firstn_S_snoc _ _ _ HA), env_tele_snoc by (rewrite List.length_firstn; lia).
  rewrite <- env_tele_firstn; reflexivity.
Qed.

(** The values of a telescope's entries are the values given. *)
Lemma tele_entries_fst : forall vs ρ T, List.map fst (tele_entries ρ T vs) = vs.
Proof. induction vs as [| v vs IH]; intros ρ T; cbn; [ reflexivity | f_equal; apply IH ]. Qed.

Lemma tele_entries_length : forall vs ρ T, List.length (tele_entries ρ T vs) = List.length vs.
Proof. intros; rewrite <- (List.length_map fst), tele_entries_fst; reflexivity. Qed.

(** Arguments of a telescope [Pre] after a group's uniform parameters,
    from the empty environment: the components after the parameters. *)
Lemma env_tele_uparams : forall D Pre ups zs, List.length ups = ind_nu D ->
    env_tele nil (List.rev (Pre ++ ind_uparams D)) (ups ++ zs) = components_env D ups (List.rev Pre) zs.
Proof.
  intros * Hl; rewrite List.rev_app_distr, env_tele_app by (rewrite List.length_rev; exact Hl); reflexivity.
Qed.

(** The uniform parameters alone. *)
Lemma env_tele_uparams_nil : forall D ups, env_tele nil (List.rev (ind_uparams D)) ups = decl_env D ups.
Proof. reflexivity. Qed.

(** Components after a full prefix read only as many types of the rest
    as there are components. *)
Lemma components_env_app_firstn : forall D u T0 T pre0 pre, List.length pre0 = List.length T0 -> List.length pre <= List.length T ->
    components_env D u (T0 ++ T) (pre0 ++ pre) = components_env D u (T0 ++ List.firstn (List.length pre) T) (pre0 ++ pre).
Proof.
  intros * Hl0 Hl.
  rewrite (components_env_firstn D u (T0 ++ T)), (components_env_firstn D u (T0 ++ List.firstn (List.length pre) T))
    by (rewrite !List.length_app, ?List.length_firstn; lia).
  f_equal; rewrite List.length_app, !List.firstn_app, Hl0, Nat.add_comm, Nat.add_sub, List.firstn_firstn, Nat.min_id.
  rewrite !List.firstn_all2 by lia; reflexivity.
Qed.

(** The shift past the components gives the parameters' environment. *)
Lemma eval_wk_shiftn_components_env : forall D ups T zs,
    ⟪wk_shiftn (List.length zs)⟫ (components_env D ups T zs) = decl_env D ups.
Proof.
  intros; unfold components_env, env_tele.
  rewrite <- (tele_entries_length zs (decl_env D ups) T) at 1; apply eval_wk_shiftn_extend_typed.
Qed.

(** One more typed value. *)
Lemma env_extend_typed_cons : forall ρ x t vts,
    env_extend_typed ρ ((x, t) :: vts) = env_extend_typed (ρ ↦ x ⦂ t) vts.
Proof. reflexivity. Qed.

(** The environment the values [ms] of the terms of an extended
    substitution are entered in, at the entries [ts] (innermost first)
    over [Δ]: each at the tag of its entry over the environment before it
    ([centry_tag]), as [eval_sub_extend] stores it. *)
Fixpoint env_extend_tagged (Δ ts : ctx) (ρ : env) (ms : list domain) : env :=
  match ts, ms with
  | e :: ts', m :: ms' => env_extend_tagged (e :: Δ) ts' (ρ ↦ m ⦂ centry_tag e Δ ρ) ms'
  | _, _ => ρ
  end.

(** The values and tags [env_extend_tagged] enters, as a list. *)
Fixpoint tagged_entries (Δ ts : ctx) (ρ : env) (ms : list domain) : list (domain * entry_type) :=
  match ts, ms with
  | e :: ts', m :: ms' => (m, centry_tag e Δ ρ) :: tagged_entries (e :: Δ) ts' (ρ ↦ m ⦂ centry_tag e Δ ρ) ms'
  | _, _ => nil
  end.

(** The extension at the tags is the typed extension by them. *)
Lemma env_extend_tagged_typed : forall ts Δ ρ ms, env_extend_tagged Δ ts ρ ms = env_extend_typed ρ (tagged_entries Δ ts ρ ms).
Proof. induction ts as [| e ts IH]; intros Δ ρ [| m ms]; cbn [env_extend_tagged tagged_entries]; try reflexivity; apply IH. Qed.

(** Its values are the values given, as many as the entries. *)
Lemma tagged_entries_fst : forall ts Δ ρ ms, List.length ts = List.length ms -> List.map fst (tagged_entries Δ ts ρ ms) = ms.
Proof.
  induction ts as [| e ts IH]; intros Δ ρ [| m ms] Hl; cbn [List.length] in Hl; try discriminate; [ reflexivity |].
  cbn [tagged_entries List.map fst]; f_equal; apply IH; lia.
Qed.

Lemma tagged_entries_length : forall ts Δ ρ ms, List.length ts = List.length ms -> List.length (tagged_entries Δ ts ρ ms) = List.length ms.
Proof. intros * Hl; rewrite <- (List.length_map fst), tagged_entries_fst by exact Hl; reflexivity. Qed.

(** ** Environments of Exactly their Context's Length

    An environment with one entry per entry of its context is its own
    prefix of that length ([env_upto]): the tags a substitution's value
    stores ([centry_tag]) are then the closures a telescope's arguments
    have ([env_tele]), and the identity's retagging ([ctx_retag]) changes
    nothing. *)

Lemma length_env_extend_typed : forall vts ρ, List.length (env_extend_typed ρ vts) = List.length vts + List.length ρ.
Proof.
  induction vts as [| [v t] vts IH]; intros ρ; [ reflexivity |].
  rewrite env_extend_typed_cons, IH; cbn [extend_env List.length]; lia.
Qed.

Lemma env_upto_exact : forall ρ, env_upto (List.length ρ) ρ = ρ.
Proof.
  induction ρ as [| d ρ IH]; [ reflexivity |].
  unfold env_upto in *; cbn [List.length List.seq List.map].
  rewrite <- List.seq_shift, List.map_map; cbn [env_entry List.nth]; f_equal; exact IH.
Qed.

(** Extensions at the tags of [ts] over an environment of [Δ]'s length
    are the telescope's arguments. *)
Lemma env_extend_tagged_exact : forall ts Δ ρ ms, List.length ρ = List.length Δ -> List.length ms = List.length ts ->
    env_extend_tagged Δ ts ρ ms = env_tele ρ ts ms.
Proof.
  induction ts as [| e ts IH]; intros Δ ρ [| m ms] Hρ Hl; cbn [List.length] in Hl; try discriminate; [ reflexivity |].
  cbn [env_extend_tagged]; unfold env_tele; cbn [tele_entries tele_head_type List.tl]; rewrite env_extend_typed_cons.
  assert (Ht : centry_tag e Δ ρ = match centry_type e with Some A => entry_type_closure A ρ | None => entry_type_none end)
    by (unfold centry_tag; rewrite <- Hρ, env_upto_exact; reflexivity).
  rewrite Ht; apply IH; [ cbn [extend_env List.length]; lia | lia ].
Qed.

(** The identity's retagging of a telescope's arguments over an
    environment it does not change, of its context's length, changes
    nothing either. *)
Lemma ctx_retag_env_tele : forall T Δ ρ vs, ctx_retag Δ ρ = ρ -> List.length ρ = List.length Δ ->
    List.length vs = List.length T -> ctx_retag (List.rev T ++ Δ) (env_tele ρ T vs) = env_tele ρ T vs.
Proof.
  induction T as [| e T IH] using List.rev_ind; intros Δ ρ vs HΔ Hρ Hl.
  - destruct vs; [ exact HΔ | discriminate ].
  - rewrite List.length_app in Hl; cbn [List.length] in Hl.
    destruct vs as [| v vs _] using List.rev_ind; [ cbn in Hl; lia |].
    rewrite List.length_app in Hl; cbn [List.length] in Hl.
    rewrite List.rev_app_distr; cbn [List.rev List.app].
    unfold env_tele; rewrite tele_entries_app by lia; fold (env_tele ρ T vs).
    cbn [tele_entries tele_head_type List.tl]; rewrite env_extend_typed_app; cbn [env_extend_typed List.fold_left fst snd].
    cbn [ctx_retag extend_env List.tl List.hd].
    pose proof (IH Δ ρ vs HΔ Hρ ltac:(lia)) as IH'; unfold env_tele in IH'; rewrite IH'.
    assert (HlT : List.length (env_extend_typed ρ (tele_entries ρ T vs)) = List.length (List.rev T ++ Δ)).
    { rewrite length_env_extend_typed, tele_entries_length, List.length_app, List.length_rev; lia. }
    unfold centry_tag; rewrite <- HlT, env_upto_exact.
    destruct e; reflexivity.
Qed.

Lemma length_env_tele : forall ρ T vs, List.length (env_tele ρ T vs) = List.length vs + List.length ρ.
Proof. intros; unfold env_tele; rewrite length_env_extend_typed, tele_entries_length; reflexivity. Qed.

Lemma length_decl_env : forall D ups, List.length (decl_env D ups) = List.length ups.
Proof. intros; unfold decl_env; rewrite length_env_tele; cbn; lia. Qed.

(** In particular the uniform parameters' environment. *)
Corollary ctx_retag_decl_env : forall D ups, List.length ups = ind_nu D ->
    ctx_retag (ind_uparams D) (decl_env D ups) = decl_env D ups.
Proof.
  intros * Hl; unfold decl_env.
  rewrite <- (List.rev_involutive (ind_uparams D)) at 1; rewrite <- (List.app_nil_r (List.rev (List.rev (ind_uparams D)))).
  apply ctx_retag_env_tele; [ reflexivity | reflexivity | rewrite List.length_rev; exact Hl ].
Qed.

(** In particular extensions of the uniform parameters' environment, as
    the identity's value has it: the components after the parameters. *)
Corollary env_extend_tagged_decl_env : forall D ups T ms, List.length ups = ind_nu D -> List.length ms = List.length T ->
    env_extend_tagged (ind_uparams D) T (ctx_retag (ind_uparams D) (decl_env D ups)) ms = components_env D ups T ms.
Proof.
  intros * Hl Hm; rewrite ctx_retag_decl_env by exact Hl.
  apply env_extend_tagged_exact; [ rewrite length_decl_env; exact Hl | exact Hm ].
Qed.

(** ** Arguments at a Telescope *)

Lemma per_gargs_length : forall ts ρ ρ' xs xs', per_gargs ts ρ ρ' xs xs' ->
    List.length xs = List.length xs' /\ List.length xs <= List.length ts.
Proof. induction 1; cbn; [ split; lia |]; destruct IHper_gargs; split; lia. Qed.

Lemma per_gargs_app : forall ts1 ts2 ρ ρ' xs1 xs1' xs2 xs2',
    List.length xs1 = List.length ts1 ->
    per_gargs (ts1 ++ ts2) ρ ρ' (xs1 ++ xs2) (xs1' ++ xs2') ->
    List.length xs1' = List.length ts1 ->
    per_gargs ts1 ρ ρ' xs1 xs1' /\ per_gargs ts2 (env_tele ρ ts1 xs1) (env_tele ρ' ts1 xs1') xs2 xs2'.
Proof.
  induction ts1 as [| e ts1 IH]; intros * Hl H Hl'.
  - destruct xs1, xs1'; cbn in *; try discriminate; split; [ constructor | exact H ].
  - destruct xs1 as [| x xs1], xs1' as [| x' xs1']; cbn in *; try discriminate.
    inversion H; subst.
    match goal with H' : per_gargs (ts1 ++ ts2) (ρ ↦ x ⦂ ?t) (ρ' ↦ x' ⦂ ?t') _ _ |- _ =>
      destruct (IH ts2 (ρ ↦ x ⦂ t) (ρ' ↦ x' ⦂ t') xs1 xs1' xs2 xs2' ltac:(lia) H' ltac:(lia)) as [H1 H2] end.
    split; [ econstructor; eassumption | exact H2 ].
Qed.

Lemma per_gargs_app_intro : forall ts1 ts2 ρ ρ' xs1 xs1' xs2 xs2',
    List.length xs1 = List.length ts1 ->
    per_gargs ts1 ρ ρ' xs1 xs1' -> per_gargs ts2 (env_tele ρ ts1 xs1) (env_tele ρ' ts1 xs1') xs2 xs2' ->
    per_gargs (ts1 ++ ts2) ρ ρ' (xs1 ++ xs2) (xs1' ++ xs2').
Proof.
  induction ts1 as [| e ts1 IH]; intros * Hl H1 H2.
  - destruct xs1; cbn in *; try discriminate; inversion H1; subst; exact H2.
  - destruct xs1 as [| x xs1]; cbn in *; try discriminate.
    inversion H1; subst; cbn; econstructor; [ eassumption | eassumption |].
    apply IH; [ lia | eassumption | exact H2 ].
Qed.

Lemma per_gargs_snoc : forall ts A ρ ρ' xs xs' x x' i R,
    List.length xs = List.length ts ->
    per_gargs ts ρ ρ' xs xs' ->
    rel_typ i A (env_tele ρ ts xs) A (env_tele ρ' ts xs') R -> R x x' ->
    per_gargs (ts ++ ce_ass A :: nil) ρ ρ' (xs ++ x :: nil) (xs' ++ x' :: nil).
Proof.
  intros * Hl H HA Hx; apply per_gargs_app_intro; [ exact Hl | exact H |].
  econstructor; [ exact HA | exact Hx | constructor ].
Qed.

(** A type at a small index is also one at a large index. *)
Lemma per_univ_elem_to_nat : forall (i : universe_index) R a a', DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    exists n : nat, DF a ≈ a' ∈ per_univ_elem n ↘ R.
Proof. intros [o | n] * H; [ exists 0; eapply per_univ_elem_cumu_universe_index; [ exact H | exact I ] | exists n; exact H ]. Qed.

(** ** The Elements of a [Π] over a Telescope

    A family [f] of values, one per list of arguments, that applies by
    taking the next argument, and whose full applications are related at
    the codomain, is an element of the [Π].  Its parameters are relevant:
    each value of the family before the last takes relevant arguments
    ([Hfr]), and each parameter's type is relevant at related arguments
    before it ([Hdom]).

    The [Π] applies to an argument in its environment extended at the
    value of its domain, where the telescope's arguments are at the
    closures of its types ([env_tele]).  So the premises are stated at
    related extensions with any types, related at the context PER of the
    telescope over a context [Γ] the base environments are related at. *)
Lemma ctx_pi_rel_elem : forall N (f : list domain -> domain) B,
    (forall xs x, List.length xs < N -> $| f xs & x | gc_deps ⍮ gc_stack ↘ f (xs ++ x :: nil)) ->
    (forall xs, List.length xs < N -> arg_relevance gc_deps gc_stack (f xs) = relevant) ->
    forall ts Γ RΓ, tele_ass ts -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> ⊨ List.rev ts ++ Γ ->
    forall E E' xs xs' a a' (i : universe_index) R,
      List.length xs + List.length ts = N -> List.length xs' = List.length xs -> RΓ E E' ->
      (forall ts1 A ts2 R1 vts vts' b, ts = ts1 ++ ce_ass A :: ts2 ->
         EF List.rev ts1 ++ Γ ≈ List.rev ts1 ++ Γ ∈ per_ctx_env ↘ R1 ->
         List.length vts = List.length ts1 -> List.length vts' = List.length ts1 ->
         R1 (env_extend_typed E vts) (env_extend_typed E' vts') ->
         ⟦ A ⟧ env_extend_typed E vts ↘ b -> domain_relevance b = relevant) ->
      ⟦ ctx_pi (List.rev ts) B ⟧ E ↘ a -> ⟦ ctx_pi (List.rev ts) B ⟧ E' ↘ a' ->
      DF a ≈ a' ∈ per_univ_elem i ↘ R ->
      (forall R1 vts vts', EF List.rev ts ++ Γ ≈ List.rev ts ++ Γ ∈ per_ctx_env ↘ R1 ->
         List.length vts = List.length ts -> List.length vts' = List.length ts ->
         R1 (env_extend_typed E vts) (env_extend_typed E' vts') ->
         Dom f (xs ++ List.map fst vts) ≈ f (xs' ++ List.map fst vts') ∈
           per_head B B (env_extend_typed E vts) (env_extend_typed E' vts')) ->
      Dom f xs ≈ f xs' ∈ R.
Proof.
  intros N f B Happ Hfr ts; induction ts as [| e ts IH]; intros Γ RΓ Hts HΓ HC * Hl Hl' HE Hdom Ha Ha' HR Hbase.
  - cbn [List.rev ctx_pi] in Ha, Ha'.
    specialize (Hbase RΓ nil nil HΓ eq_refl eq_refl HE); cbn [List.map] in Hbase; rewrite !List.app_nil_r in Hbase.
    exact (Hbase _ _ _ _ Ha Ha' HR).
  - assert (He : exists A, e = ce_ass A) by (inversion Hts as [| ? ? He _]; exact He).
    destruct He as [A ->].
    assert (Hts' : tele_ass ts) by (inversion Hts; assumption).
    cbn [List.rev] in Ha, Ha', HC; rewrite ctx_pi_snoc in Ha, Ha'.
    rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
    (** The context PER of [Γ] extended by the parameter. *)
    destruct (rel_ctx_wf_ass_typ (rel_ctx_wf_app_r _ _ HC)) as [j HAv].
    pose proof (per_ctx_env_of_typ HΓ HAv) as HΓA.
    inversion Ha; subst a; inversion Ha'; subst a'.
    match goal with E1 : ⟦ A ⟧ E ↘ ?b |- _ => rename b into a0; rename E1 into Ea0 end.
    match goal with E1 : ⟦ A ⟧ E' ↘ ?b |- _ => rename b into a0'; rename E1 into Ea0' end.
    basic_invert_per_univ_elem HR.
    apply_relation_equivalence.
    cbn [List.length] in Hl.
    (** The parameter is relevant, and so is what the family takes. *)
    assert (Ha0 : domain_relevance a0 = relevant)
      by exact (Hdom nil A ts RΓ nil nil a0 eq_refl HΓ eq_refl eq_refl HE Ea0).
    constructor;
      [ rewrite Hfr by lia; symmetry; exact Ha0
      | rewrite Hfr by lia; rewrite <- (per_univ_elem_relevance _ _ _ _ equiv_a_a'); symmetry; exact Ha0 |].
    intros c c' Hc.
    destruct_rel_mod_eval.
    econstructor; [ apply Happ; lia | apply Happ; lia |].
    (** The environments extended by the arguments, at the domain's values,
        are related at the extended context. *)
    pose proof (entry_readable_of_elem equiv_a_a' Hc) as [Rc Rc'].
    assert (HE1 : per_env_extend A A RΓ (E ↦ c ⦂ entry_type_value a0) (E' ↦ c' ⦂ entry_type_value a0'))
      by (apply per_env_extend_intro';
          [ exact HE | eapply per_head_of; [ exact Ea0 | exact Ea0' | exact equiv_a_a' | exact Hc ] | exact Rc | exact Rc' ]).
    eapply (IH (Γ ▹ A) _ Hts' HΓA HC (E ↦ c ⦂ entry_type_value a0) (E' ↦ c' ⦂ entry_type_value a0')
              (xs ++ c :: nil) (xs' ++ c' :: nil));
      [ rewrite List.length_app; cbn; lia | rewrite !List.length_app; cbn; lia | exact HE1
      | | eassumption | eassumption | eassumption |].
    + intros ts1 Aj ts2 R1 vts vts' b -> HR1 Hlv Hlv' HEv Eb.
      apply (Hdom (ce_ass A :: ts1) Aj ts2 R1 ((c, entry_type_value a0) :: vts) ((c', entry_type_value a0') :: vts') b);
        [ reflexivity | cbn [List.rev]; rewrite <- List.app_assoc; exact HR1 | cbn; lia | cbn; lia | exact HEv | exact Eb ].
    + intros R1 vts vts' HR1 Hlv Hlv' HEv.
      pose proof (Hbase R1 ((c, entry_type_value a0) :: vts) ((c', entry_type_value a0') :: vts')
                    ltac:(cbn [List.rev]; rewrite <- List.app_assoc; exact HR1) ltac:(cbn; lia) ltac:(cbn; lia) HEv) as Hb.
      cbn [List.map fst] in Hb; rewrite <- !List.app_assoc; cbn [List.app]; exact Hb.
Qed.

(** ** Arguments over Another Base

    The types of a telescope valid over [Tb] are related at related bases,
    so arguments related at it over one pair of bases are over another
    related pair. *)
Lemma per_gargs_base : forall ts Tb RTb,
    EF Tb ≈ Tb ∈ per_ctx_env ↘ RTb -> ⊨ List.rev ts ++ Tb -> tele_ass ts ->
    forall ρ1 ρ2 ρ3 ρ4 xs xs', RTb ρ1 ρ2 -> RTb ρ1 ρ3 -> RTb ρ2 ρ4 ->
      per_gargs ts ρ1 ρ2 xs xs' -> per_gargs ts ρ3 ρ4 xs xs'.
Proof.
  induction ts as [| e ts IH]; intros * HTb HC Hts * H12 H13 H24 Hg; [ inversion Hg; subst; constructor |].
  assert (He : exists A, e = ce_ass A) by (inversion Hts as [| ? ? He _]; exact He).
  destruct He as [A ->].
  assert (Hts' : tele_ass ts) by (inversion Hts; assumption).
  inversion Hg as [| ? A0 ? ? x x' ? ys ys' R HA Hx Hg']; subst; [ constructor |].
  cbn [List.rev] in HC; rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
  destruct (rel_ctx_wf_ass_typ (rel_ctx_wf_app_r _ _ HC)) as [j HAv].
  pose proof (per_ctx_env_of_typ HTb HAv) as HTb'.
  assert (HP : PER RTb) by (eapply per_env_PER; exact HTb).
  assert (H34 : RTb ρ3 ρ4) by (etransitivity; [ symmetry; exact H13 | etransitivity; [ exact H12 | exact H24 ] ]).
  destruct HA as [a1 a2 Ea1 Ea2 HR].
  destruct (rel_type_inversion_simple_at HTb HAv _ _ H13) as (b1 & a3 & Eb1 & Ea3 & [R13 HR13]).
  destruct (rel_type_inversion_simple_at HTb HAv _ _ H24) as (b2 & a4 & Eb2 & Ea4 & [R24 HR24]).
  destruct (rel_type_inversion_simple_at HTb HAv _ _ H34) as (b3 & b4 & Eb3 & Eb4 & [R34 HR34]).
  assert (b1 = a1) as -> by (eapply functional_eval_exp; eassumption).
  assert (b2 = a2) as -> by (eapply functional_eval_exp; eassumption).
  assert (b3 = a3) as -> by (eapply functional_eval_exp; eassumption).
  assert (b4 = a4) as -> by (eapply functional_eval_exp; eassumption).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR13 HR34) as (R14 & HR14 & E14).
  assert (E34 : R34 <~> R14) by (eapply per_univ_elem_left_irrel; [ exact HR34 | exact HR14 ]).
  assert (E13 : R <~> R14) by (eapply per_univ_elem_right_irrel; [ exact HR | exact HR14 ]).
  assert (E24 : R24 <~> R14) by (eapply per_univ_elem_left_irrel; [ exact HR24 | exact HR14 ]).
  assert (HPR : PER R) by (eapply per_elem_PER; exact HR).
  assert (Hxx : R x x) by (etransitivity; [ exact Hx | symmetry; exact Hx ]).
  assert (Hx'x' : R x' x') by (etransitivity; [ symmetry; exact Hx | exact Hx ]).
  econstructor; [ exact (mk_rel_mod_eval a3 a4 Ea3 Ea4 HR34) | exact (proj2 (E34 _ _) (proj1 (E13 _ _) Hx)) |].
  (** The arguments read back at the closures of the parameter's type at
      each base. *)
  assert (Hx13 : R13 x x) by exact (proj2 (E14 _ _) (proj1 (E13 _ _) Hxx)).
  assert (Hx24 : R24 x' x') by exact (proj2 (E24 _ _) (proj1 (E13 _ _) Hx'x')).
  pose proof (entry_readable_of_elem_closure Ea1 Ea2 HR Hx) as [Rx1 Rx2].
  pose proof (entry_readable_of_elem_closure Ea1 Ea3 HR13 Hx13) as [_ Rx3].
  pose proof (entry_readable_of_elem_closure Ea2 Ea4 HR24 Hx24) as [_ Rx4].
  eapply (IH _ _ HTb' HC Hts' (ρ1 ↦ x ⦂ entry_type_closure A ρ1) (ρ2 ↦ x' ⦂ entry_type_closure A ρ2)); [ | | | exact Hg' ].
  - apply per_env_extend_intro'; [ exact H12 | exact (per_head_of Ea1 Ea2 HR Hx) | exact Rx1 | exact Rx2 ].
  - apply per_env_extend_intro'; [ exact H13 | exact (per_head_of Ea1 Ea3 HR13 Hx13) | exact Rx1 | exact Rx3 ].
  - apply per_env_extend_intro'; [ exact H24 | exact (per_head_of Ea2 Ea4 HR24 Hx24) | exact Rx2 | exact Rx4 ].
Qed.

(** The left arguments are related to themselves, over the left base. *)
Lemma per_gargs_refl_l : forall ts Tb RTb,
    EF Tb ≈ Tb ∈ per_ctx_env ↘ RTb -> ⊨ List.rev ts ++ Tb -> tele_ass ts ->
    forall ρ ρ' xs xs', RTb ρ ρ' -> per_gargs ts ρ ρ' xs xs' -> per_gargs ts ρ ρ xs xs.
Proof.
  induction ts as [| e ts IH]; intros * HTb HC Hts * Hρ Hg; [ inversion Hg; subst; constructor |].
  assert (He : exists A, e = ce_ass A) by (inversion Hts as [| ? ? He _]; exact He).
  destruct He as [A ->].
  assert (Hts' : tele_ass ts) by (inversion Hts; assumption).
  inversion Hg as [| ? A0 ? ? x x' ? ys ys' R HA Hx Hg']; subst; [ constructor |].
  cbn [List.rev] in HC; rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
  destruct (rel_ctx_wf_ass_typ (rel_ctx_wf_app_r _ _ HC)) as [j HAv].
  pose proof (per_ctx_env_of_typ HTb HAv) as HTb'.
  assert (HP : PER RTb) by (eapply per_env_PER; exact HTb).
  assert (Hρρ : RTb ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  destruct HA as [a1 a2 Ea1 Ea2 HR].
  destruct (rel_type_inversion_simple_at HTb HAv _ _ Hρρ) as (b1 & b1' & Eb1 & Eb1' & [R11 HR11]).
  assert (b1 = a1) as -> by (eapply functional_eval_exp; eassumption).
  assert (b1' = a1) as -> by (eapply functional_eval_exp; eassumption).
  assert (E : R <~> R11) by (eapply per_univ_elem_right_irrel; [ exact HR | exact HR11 ]).
  assert (HPR : PER R) by (eapply per_elem_PER; exact HR).
  assert (Hxx : R x x) by (etransitivity; [ exact Hx | symmetry; exact Hx ]).
  econstructor; [ exact (mk_rel_mod_eval a1 a1 Ea1 Ea1 HR11) | apply E, Hxx |].
  pose proof (entry_readable_of_elem_closure Ea1 Ea2 HR Hx) as [Rx Rx'].
  eapply (IH _ _ HTb' HC Hts' (ρ ↦ x ⦂ entry_type_closure A ρ) (ρ' ↦ x' ⦂ entry_type_closure A ρ')); [ | exact Hg' ].
  apply per_env_extend_intro'; [ exact Hρ | exact (per_head_of Ea1 Ea2 HR Hx) | exact Rx | exact Rx' ].
Qed.

(** Environments related at an extension are arguments related at its
    telescope, whatever the types the extensions store their values at. *)
Lemma rel_gargs : forall ts Tb RTb R,
    EF Tb ≈ Tb ∈ per_ctx_env ↘ RTb -> ⊨ List.rev ts ++ Tb -> tele_ass ts ->
    EF List.rev ts ++ Tb ≈ List.rev ts ++ Tb ∈ per_ctx_env ↘ R ->
    forall ρ ρ' vts vts', List.length vts = List.length ts -> List.length vts' = List.length ts ->
      R (env_extend_typed ρ vts) (env_extend_typed ρ' vts') ->
      RTb ρ ρ' /\ per_gargs ts ρ ρ' (List.map fst vts) (List.map fst vts').
Proof.
  induction ts as [| e ts IH]; intros * HTb HC Hts HR * Hl Hl' Hρ.
  - destruct vts, vts'; cbn in *; try discriminate. split; [| constructor ].
    assert (E : R <~> RTb) by (eapply per_ctx_env_right_irrel; eassumption). apply E; exact Hρ.
  - assert (He : exists A, e = ce_ass A) by (inversion Hts as [| ? ? He _]; exact He).
    destruct He as [A ->].
    assert (Hts' : tele_ass ts) by (inversion Hts; assumption).
    destruct vts as [| [x t] vts], vts' as [| [x' t'] vts']; cbn in Hl, Hl'; try discriminate.
    cbn [List.rev] in HC, HR; rewrite <- List.app_assoc in HC, HR; cbn [List.app] in HC, HR.
    destruct (rel_ctx_wf_ass_typ (rel_ctx_wf_app_r _ _ HC)) as [j HAv].
    pose proof (per_ctx_env_of_typ HTb HAv) as HTb'.
    destruct (IH _ _ _ HTb' HC Hts' HR (ρ ↦ x ⦂ t) (ρ' ↦ x' ⦂ t') vts vts' ltac:(lia) ltac:(lia) Hρ)
      as [Hext Hg].
    pose proof Hext as [Hb Hh _ _ [Rt _] [Rt' _]].
    split; [ exact Hb |].
    destruct (rel_type_inversion_simple_at HTb HAv _ _ Hb) as (a & a' & Ea & Ea' & [R0 HR0]).
    assert (Hxx' : R0 x x') by exact (Hh _ _ _ _ Ea Ea' HR0).
    cbn [List.map fst].
    econstructor; [ exact (mk_rel_mod_eval a a' Ea Ea' HR0) | exact Hxx' |].
    (** The rest are related over the extensions at the types the values
        were given, which are related to those at the closures of the
        parameter's type. *)
    assert (HP : PER RTb) by (eapply per_env_PER; exact HTb).
    assert (HP0 : PER R0) by (eapply per_elem_PER; exact HR0).
    assert (Hρρ : RTb ρ ρ) by (etransitivity; [ exact Hb | symmetry; exact Hb ]).
    assert (Hρ'ρ' : RTb ρ' ρ') by (etransitivity; [ symmetry; exact Hb | exact Hb ]).
    destruct (rel_type_inversion_simple_at HTb HAv _ _ Hρρ) as (b & b0 & Eb & Eb0 & [R1 HR1]).
    destruct (rel_type_inversion_simple_at HTb HAv _ _ Hρ'ρ') as (b' & b0' & Eb' & Eb0' & [R2 HR2]).
    assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (b0 = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (b' = a') as -> by (eapply functional_eval_exp; eassumption).
    assert (b0' = a') as -> by (eapply functional_eval_exp; eassumption).
    assert (E1 : R1 <~> R0) by (eapply per_univ_elem_right_irrel; [ exact HR1 | exact HR0 ]).
    assert (Hxx : R1 x x) by (apply E1; etransitivity; [ exact Hxx' | symmetry; exact Hxx' ]).
    assert (E2 : R2 <~> R0) by (eapply per_univ_elem_left_irrel; [ exact HR2 | exact HR0 ]).
    assert (Hx'x' : R2 x' x') by (apply E2; etransitivity; [ symmetry; exact Hxx' | exact Hxx' ]).
    pose proof (entry_readable_of_elem_closure Ea Ea HR1 Hxx) as [Rx _].
    pose proof (entry_readable_of_elem_closure Ea' Ea' HR2 Hx'x') as [Rx' _].
    eapply (per_gargs_base _ _ _ HTb' HC Hts' (ρ ↦ x ⦂ t) (ρ' ↦ x' ⦂ t')); [ exact Hext | | | exact Hg ].
    + apply per_env_extend_intro'; [ exact Hρρ | exact (per_head_of Ea Ea HR1 Hxx) | exact Rt | exact Rx ].
    + apply per_env_extend_intro'; [ exact Hρ'ρ' | exact (per_head_of Ea' Ea' HR2 Hx'x') | exact Rt' | exact Rx' ].
Qed.

(** The same at the telescope's own extensions. *)
Corollary rel_gargs_tele : forall ts Tb RTb R,
    EF Tb ≈ Tb ∈ per_ctx_env ↘ RTb -> ⊨ List.rev ts ++ Tb -> tele_ass ts ->
    EF List.rev ts ++ Tb ≈ List.rev ts ++ Tb ∈ per_ctx_env ↘ R ->
    forall ρ ρ' xs xs', List.length xs = List.length ts -> List.length xs' = List.length ts ->
      R (env_tele ρ ts xs) (env_tele ρ' ts xs') -> RTb ρ ρ' /\ per_gargs ts ρ ρ' xs xs'.
Proof.
  intros * HTb HC Hts HR * Hl Hl' H; unfold env_tele in H.
  rewrite <- (tele_entries_fst xs ρ ts), <- (tele_entries_fst xs' ρ' ts).
  apply (rel_gargs _ _ _ _ HTb HC Hts HR); [ rewrite tele_entries_length; exact Hl | rewrite tele_entries_length; exact Hl' | exact H ].
Qed.

(** Arguments related at a telescope read back alike, up to their
    proofs. *)
Lemma per_gargs_top : forall ts ρ ρ' xs xs', per_gargs ts ρ ρ' xs xs' -> List.length xs = List.length ts ->
    forall s, exists Ms Ms', Rps xs at ts in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Ms /\
      Rps xs' at ts in gc_deps ⍮ gc_stack ⍮ ρ' ⍮ s ↘ Ms' /\ List.map nf_erase Ms = List.map nf_erase Ms'.
Proof.
  induction 1 as [ts ρ ρ' | i A ρ ρ' a a' ts args args' R HA Ha Hg IH]; intros Hl s.
  - destruct ts; cbn in Hl; try discriminate; exists nil, nil; split; [ constructor | split; [ constructor | reflexivity ] ].
  - destruct HA as [b b' Eb Eb' HR].
    destruct (IH ltac:(cbn in Hl; lia) s) as (Ms & Ms' & HM & HM' & HE).
    destruct (per_elem_then_per_top HR Ha s) as [V V' HV HV' HEV].
    exists (cons V Ms), (cons V' Ms'); split; [ econstructor; eassumption | split; [ econstructor; eassumption |] ].
    cbn [List.map]; congruence.
Qed.

(** ** Environments of Arguments *)

(** An environment extended at the tags of [ts] past its extension: the
    environment. *)
Lemma skipn_env_extend_tagged : forall ts Δ ρ ms, List.length ts = List.length ms ->
    List.skipn (List.length ms) (env_extend_tagged Δ ts ρ ms) = ρ.
Proof.
  induction ts as [| e ts IH]; intros Δ ρ [| m ms] Hl; cbn [List.length] in Hl; try discriminate; [ reflexivity |].
  cbn [env_extend_tagged List.length].
  replace (S (List.length ms)) with (1 + List.length ms) by lia.
  rewrite <- List.skipn_skipn, IH by lia; reflexivity.
Qed.

(** A substitution extended by terms, at a context extended by entries
    [ts] (outermost first) none of which is a proposition there: the
    environment extended by the terms' values, at the entries' tags. *)
Lemma eval_sb_of_list : forall Ms ts σ Δ ρ ρσ ms,
    ⟦ σ : Δ ⟧s ρ ↘ ρσ -> ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms -> List.length ts = List.length Ms ->
    (forall x, x < List.length ts ->
       ~ entry_propositional gc_deps gc_stack (List.rev ts ++ Δ) (env_extend_tagged Δ ts ρσ ms) x) ->
    ⟦ sb_of_list σ Ms : List.rev ts ++ Δ ⟧s ρ ↘ env_extend_tagged Δ ts ρσ ms.
Proof.
  assert (Hlen : forall Ns ρ0 ns, ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ ns -> List.length ns = List.length Ns)
    by (induction 1; cbn; congruence).
  induction Ms as [| M Ms IH]; intros [| e ts] * Hσ HMs Hl Hnp; pose proof (Hlen _ _ _ HMs) as HlM;
    inversion HMs; subst; cbn [sb_of_list] in *; try discriminate; [ exact Hσ |].
  cbn [env_extend_tagged] in *.
  cbn [List.rev List.length] in *; rewrite <- List.app_assoc in *; cbn [List.app] in *.
  assert (Hl0 : List.length ms0 = List.length ts) by lia.
  apply IH; [ | assumption | lia | intros x Hx; apply Hnp; lia ].
  apply eval_sub_extend; [ exact Hσ | | assumption ].
  (** The head is the entry past the later ones, no proposition. *)
  intros Hh; apply (Hnp (List.length ts) ltac:(lia)).
  rewrite <- (List.length_rev ts), <- (Nat.add_0_r (List.length (List.rev ts))).
  apply entry_propositional_shiftn_intro.
  rewrite List.length_rev, <- Hl0, skipn_env_extend_tagged by lia.
  exact (proj2 (entry_propositional_head _ _ _ _) Hh).
Qed.



(** ** Universes *)

(** The index of the elements of a universe. *)
Definition univ_idx (a : domain) : universe_index :=
  match a with
  | d_univ j => ul j
  | d_suniv l => us (domain_level_real l)
  | _ => ul 0
  end.

Definition is_univ (a : domain) : Prop := (exists j, a = d_univ j) \/ (exists l, a = d_suniv l).

Lemma per_univ_elem_univ : forall (i : universe_index) R a a', DF a ≈ a' ∈ per_univ_elem i ↘ R -> is_univ a ->
    univ_idx a' = univ_idx a /\ (R <~> per_relevant_nonlevel (per_univ (univ_idx a))).
Proof.
  intros * H [[j ->] | [l ->]]; basic_invert_per_univ_elem H; cbn [univ_idx].
  - split; [ reflexivity | assumption ].
  - match goal with Hl : per_lvl l ?l' |- _ => split; [ f_equal; symmetry; apply per_lvl_real; exact Hl | assumption ] end.
Qed.

(** ** Closed Terms

    A closed term of a closed type is valid at [⋅] when its values at any
    two environments are related at the type's values there. *)
Lemma rel_exp_closed_intro : forall T N (i : nat),
    (forall σ, T[σ] = T) -> (forall σ, N[σ] = N) ->
    (forall ρ ρ', exists a a' R n n', ⟦ T ⟧ ρ ↘ a /\ ⟦ T ⟧ ρ' ↘ a' /\ DF a ≈ a' ∈ per_univ_elem i ↘ R /\
       ⟦ N ⟧ ρ ↘ n /\ ⟦ N ⟧ ρ' ↘ n' /\ Dom n ≈ n' ∈ R) ->
    ⋅ ⊨ N : T.
Proof.
  intros * HT HN H.
  refine (mk_rel_exp_under_ctx _ _ _ _ (fun _ _ => True) per_ctx_env_nil_true i _).
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (H ρ ρσ) as (a1 & a2 & R12 & n1 & n2 & Ea1 & Ea2 & HR12 & En1 & En2 & Hn12).
  destruct (H ρσ ρ'σ') as (b2 & a3 & R23 & m2 & n3 & Eb2 & Ea3 & HR23 & Em2 & En3 & Hn23).
  destruct (H ρ'σ' ρ') as (b3 & a4 & R34 & m3 & n4 & Eb3 & Ea4 & HR34 & Em3 & En4 & Hn34).
  assert (b2 = a2) as -> by (eapply functional_eval_exp; eassumption).
  assert (b3 = a3) as -> by (eapply functional_eval_exp; eassumption).
  assert (m2 = n2) as -> by (eapply functional_eval_exp; eassumption).
  assert (m3 = n3) as -> by (eapply functional_eval_exp; eassumption).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR12 HR23) as (R13 & HR13 & E13).
  assert (E12 : R12 <~> R23) by (etransitivity; [ exact E13 | eapply per_univ_elem_left_irrel; [ exact HR13 | exact HR23 ] ]).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR23 HR34) as (R24 & HR24 & E24).
  assert (E34 : R34 <~> R23) by (etransitivity; [ eapply per_univ_elem_left_irrel; [ exact HR34 | exact HR24 ] | symmetry; exact E24 ]).
  exists R23; split.
  - apply (mk_rel_exp a1 a2 a3 a4); [ rewrite HT; exact Ea1 | exact Ea2 | exact Ea3 | rewrite HT; exact Ea4 |].
    apply rel_chain_4; [ eapply per_univ_elem_resp_iff; [ exact HR12 | exact E12 ] | exact HR23
                       | eapply per_univ_elem_resp_iff; [ exact HR34 | exact E34 ] ].
  - right; apply (mk_rel_exp n1 n2 n3 n4); [ rewrite HN; exact En1 | exact En2 | exact En3 | rewrite HN; exact En4 |].
    apply rel_chain_4; [ apply E12, Hn12 | exact Hn23 | apply E34, Hn34 ].
Qed.

(** The index of a universe shifted past a context is that of the
    universe, and the index of a universe is the same at related
    environments. *)
Lemma univ_idx_wk : forall Pre Up S (i : nat) R E E' b a,
    ⊨ Pre ++ Up -> Up ⊨ S : Typeω@i ->
    EF Pre ++ Up ≈ Pre ++ Up ∈ per_ctx_env ↘ R -> R E E' ->
    ⟦ S[wk_shiftn (List.length Pre)]ʷ ⟧ E ↘ b -> ⟦ S ⟧ ⟪wk_shiftn (List.length Pre)⟫ E' ↘ a ->
    is_univ b -> univ_idx a = univ_idx b.
Proof.
  intros * HC HS HR HE Eb Ea Hb.
  destruct (rel_exp_under_ctx_wk_simple (rel_wk_under_ctx_shiftn _ _ HC) HS) as (RΓ & HΓ & j & Hwk).
  assert (ER : R <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hwk _ _ (proj1 (ER _ _) HE)) as (x & x' & Rx & Ex & Ex' & HRx & Hmm0).
  cbn in Ex; inversion Ex; subst.
  (** A universe is a relevant type. *)
  destruct Hmm0 as [Hp | (m & m' & Em & Em' & Hmm)]; [ discriminate Hp |].
  assert (m = b) as -> by (eapply functional_eval_exp; eassumption).
  assert (m' = a) as -> by (eapply functional_eval_exp; eassumption).
  basic_invert_per_univ_elem HRx.
  match goal with Hm : ?r b a, H : ?r <~> _ |- _ => apply H in Hm; destruct Hm as [[Rm HRm] _ _] end.
  exact (proj1 (per_univ_elem_univ _ _ _ _ HRm Hb)).
Qed.

Lemma univ_idx_rel : forall Up S (i : nat) R E E' a a',
    EF Up ≈ Up ∈ per_ctx_env ↘ R -> Up ⊨ S : Typeω@i -> R E E' ->
    ⟦ S ⟧ E ↘ a -> ⟦ S ⟧ E' ↘ a' -> is_univ a -> univ_idx a' = univ_idx a.
Proof.
  intros * HR HS HE Ea Ea' Hu.
  destruct (rel_exp_of_typ_inversion_simple_at HR HS _ _ HE) as (b & b' & Eb & Eb' & [Rb HRb]).
  assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
  assert (b' = a') as -> by (eapply functional_eval_exp; eassumption).
  exact (proj1 (per_univ_elem_univ _ _ _ _ HRb Hu)).
Qed.

(** ** The Weakenings of Constructor Arguments *)

Lemma wk_mono_pat : forall pat, wk_mono (wk_pat pat).
Proof.
  induction pat as [| [] pat IH]; cbn [wk_pat];
    [ apply wk_mono_id | apply wk_mono_compose; [ exact IH | apply wk_mono_shift ] | apply wk_mono_q, IH ].
Qed.

#[export] Instance WkMono_pat (pat : list bool) : WkMono (wk_pat pat) := wk_mono_pat pat.

Lemma eval_wk_q_cons : forall φ `{WkMono φ} ρ v t, ⟪wk_q φ⟫ (ρ ↦ v ⦂ t) = ⟪φ⟫ ρ ↦ v ⦂ t.
Proof.
  intros φ Hφ ρ v t; cbn [extend_env].
  pose proof (eval_wk_q_tail φ (de_term v t :: ρ)) as Ht.
  pose proof (eval_wk_q_zero_entry φ (de_term v t :: ρ)) as Hh.
  assert (Hl : List.length (⟪wk_q φ⟫ (de_term v t :: ρ)) = wk_len (wk_q φ) (S (List.length ρ))) by apply eval_wk_length.
  assert (H0 : 0 < wk_len (wk_q φ) (S (List.length ρ)))
    by (apply wk_len_spec; [ apply wk_mono_q; exact Hφ | cbn; lia ]).
  destruct (⟪wk_q φ⟫ (de_term v t :: ρ)) as [| h t'] eqn:E.
  - change (List.length (@nil dentry)) with 0 in Hl; lia.
  - cbn [drop_env List.tl] in Ht; subst t'; simpl in Hh; subst h; reflexivity.
Qed.

(** The typed values of the non-recursive arguments of a constructor,
    among those of all its arguments. *)
Fixpoint nonrec_typed (gs : list carg) (vts : list (domain * entry_type)) : list (domain * entry_type) :=
  match gs, vts with
  | ca_arg _ _ :: gs, vt :: vts => vt :: nonrec_typed gs vts
  | ca_rec _ :: gs, _ :: vts => nonrec_typed gs vts
  | _, _ => nil
  end.

(** Their values are the values of the non-recursive arguments. *)
Lemma nonrec_typed_values : forall gs vts, List.map fst (nonrec_typed gs vts) = nonrec_arg_vals gs (List.map fst vts).
Proof. induction gs as [| [] gs IH]; intros [| vt vts]; cbn; f_equal; auto. Qed.

Lemma nonrec_typed_app : forall gs gs' vts vts', List.length vts = List.length gs ->
    nonrec_typed (gs ++ gs') (vts ++ vts') = nonrec_typed gs vts ++ nonrec_typed gs' vts'.
Proof.
  induction gs as [| g gs IH]; intros * Hl; destruct vts as [| vt vts]; cbn in Hl; try discriminate; [ reflexivity |].
  destruct g; cbn [List.app nonrec_typed]; rewrite IH by lia; reflexivity.
Qed.

(** [wk_pat] drops the recursive arguments of an environment of arguments,
    whatever their types. *)
Lemma eval_wk_pat_args : forall gs1 E vts, List.length vts = List.length gs1 ->
    ⟪wk_pat (cargs_pat gs1)⟫ (env_extend_typed E vts) = env_extend_typed E (nonrec_typed gs1 vts).
Proof.
  induction gs1 as [| g gs1 IH] using List.rev_ind; intros E vts Hl.
  - destruct vts; cbn in *; try discriminate; apply eval_wk_id.
  - rewrite List.length_app in Hl; cbn in Hl.
    assert (Hvts : exists vts0 vt, vts = vts0 ++ vt :: nil)
      by (destruct vts as [| vt vts0] using List.rev_ind; [ cbn in Hl; lia | eauto ]).
    destruct Hvts as (vts0 & [v t] & ->); rewrite List.length_app in Hl; cbn in Hl.
    rewrite cargs_pat_snoc, nonrec_typed_app by lia.
    rewrite env_extend_typed_app; cbn [env_extend_typed List.fold_left fst snd].
    destruct g as [rA A | Ps]; cbn [wk_pat nonrec_typed].
    + rewrite eval_wk_q_cons by typeclasses eauto; rewrite IH by lia.
      rewrite env_extend_typed_app; reflexivity.
    + rewrite eval_wk_compose by typeclasses eauto.
      rewrite eval_wk_shift; cbn [drop_env List.tl extend_env].
      rewrite IH by lia; rewrite List.app_nil_r; reflexivity.
Qed.

(** ** Variables of an Environment of Arguments *)

Lemma env_entry_extend_typed_app : forall ρ vts i, env_entry (env_extend_typed ρ vts) (List.length vts + i) = env_entry ρ i.
Proof. intros; rewrite <- env_entry_skipn, skipn_env_extend_typed; reflexivity. Qed.

Corollary env_entry_extend_tagged_app : forall ts Δ ρ ms i, List.length ts = List.length ms ->
    env_entry (env_extend_tagged Δ ts ρ ms) (List.length ms + i) = env_entry ρ i.
Proof. intros * Hl; rewrite <- env_entry_skipn, skipn_env_extend_tagged by exact Hl; reflexivity. Qed.

(** ** Environments of Arguments, Inverted *)

(** Evaluated terms are as many as the terms. *)
Lemma eval_exps_count : forall Ms ρ ms, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms -> List.length ms = List.length Ms.
Proof. induction 1; cbn; congruence. Qed.

(** The tags and units of a context extended by [ts], past [ts]: those of
    the context, over the environment's tail. *)
Lemma ctx_entry_tag_app : forall ts Δ y E,
    ctx_entry_tag (ts ++ Δ) (List.length ts + y) E = ctx_entry_tag Δ y (List.skipn (List.length ts) E).
Proof.
  induction ts as [| e ts IH]; intros; [ reflexivity |].
  cbn [List.length List.app Nat.add]; rewrite <- (ctx_entry_tag_drop e), IH.
  destruct E; cbn [List.skipn List.tl drop_env]; [ rewrite !List.skipn_nil |]; reflexivity.
Qed.

Lemma ctx_entry_unit_app : forall ts Δ y, ctx_entry_unit (ts ++ Δ) (List.length ts + y) = ctx_entry_unit Δ y.
Proof. induction ts as [| e ts IH]; intros; [ reflexivity |]; cbn [List.length List.app Nat.add]; rewrite ctx_entry_unit_succ; apply IH. Qed.

#[local] Transparent eval_sub.
(** A substitution extended by terms, evaluated at a context extended by
    entries [ts]: past them, the value of the substitution. *)
Lemma eval_sb_of_list_tail : forall Ms ts σ Δ ρ E, List.length ts = List.length Ms ->
    ⟦ sb_of_list σ Ms : List.rev ts ++ Δ ⟧s ρ ↘ E -> ⟦ σ : Δ ⟧s ρ ↘ List.skipn (List.length ts) E.
Proof.
  intros * Hl H y Hy.
  assert (Hy' : List.length ts + y < List.length (List.rev ts ++ Δ)) by (rewrite List.length_app, List.length_rev; lia).
  destruct (H _ Hy') as [Hp Hn].
  assert (Hσy : sb_of_list σ Ms (List.length ts + y) = σ y) by (rewrite Hl; apply sb_of_list_ge).
  rewrite Hσy in Hp, Hn; rewrite env_entry_skipn.
  rewrite <- (List.length_rev ts), ctx_entry_tag_app, ctx_entry_unit_app, List.length_rev in Hp, Hn; split.
  - intros Hpy; apply Hp.
    rewrite <- (List.length_rev ts); apply entry_propositional_shiftn_intro; rewrite List.length_rev; exact Hpy.
  - intros Hny; apply Hn; intros Hpx; apply Hny.
    pose proof (entry_propositional_shiftn (List.rev ts) Δ E y) as Hs; rewrite List.length_rev in Hs; exact (Hs Hpx).
Qed.

(** The tag of the entry of [ts ++ e :: Δ] at [e]: [e]'s over the
    environment's entries past it. *)
Lemma ctx_entry_tag_app_at : forall ts e Δ E,
    ctx_entry_tag (ts ++ e :: Δ) (List.length ts) E = centry_tag e Δ (List.skipn (S (List.length ts)) E).
Proof.
  intros; unfold ctx_entry_tag, centry_tag, ctx_entry_type.
  rewrite List.nth_error_app2, Nat.sub_diag by lia; cbn [List.nth_error].
  assert (Hs : List.skipn (S (List.length ts)) (ts ++ e :: Δ) = Δ) by (induction ts; cbn in *; auto).
  rewrite Hs; destruct e; reflexivity.
Qed.

(** Extensions at the tags of [ts] of environments with the same entries
    have the same entries. *)
Lemma env_extend_tagged_eq : forall ts Δ X X' ms, (forall x, env_entry X x = env_entry X' x) ->
    forall x, env_entry (env_extend_tagged Δ ts X ms) x = env_entry (env_extend_tagged Δ ts X' ms) x.
Proof.
  induction ts as [| e ts IH]; intros Δ X X' [| m ms] HX; cbn [env_extend_tagged]; try exact HX.
  apply IH; intros [| x]; cbn [env_entry]; [| apply HX ].
  unfold centry_tag; rewrite (env_upto_agree (List.length Δ) X X' (fun y _ => HX y)); reflexivity.
Qed.

(** Extensions at the tags of [ts] over environments that agree on [Δ]
    agree on the whole context: the tags read the first [|Δ|] entries. *)
Lemma env_extend_tagged_agree : forall ts Δ X X' ms, List.length ts = List.length ms ->
    env_agree_upto (List.length Δ) X X' ->
    env_agree_upto (List.length ts + List.length Δ) (env_extend_tagged Δ ts X ms) (env_extend_tagged Δ ts X' ms).
Proof.
  induction ts as [| e ts IH]; intros Δ X X' [| m ms] Hl HX; cbn [List.length] in Hl; try discriminate; [ exact HX |].
  cbn [env_extend_tagged List.length].
  replace (S (List.length ts) + List.length Δ) with (List.length ts + List.length (e :: Δ)) by (cbn; lia).
  apply IH; [ lia |].
  intros [| x] Hx; cbn [List.length] in Hx; cbn [env_entry]; [ unfold centry_tag; rewrite (env_upto_agree _ _ _ HX); reflexivity |].
  apply HX; lia.
Qed.

(** And at the new entries, none a proposition there: the terms' values,
    stored at the entries' tags over the environment's tail. *)
Lemma eval_sb_of_list_vals : forall Ms ts σ Δ ρ E, List.length ts = List.length Ms ->
    ⟦ sb_of_list σ Ms : List.rev ts ++ Δ ⟧s ρ ↘ E ->
    (forall x, x < List.length ts -> ~ entry_propositional gc_deps gc_stack (List.rev ts ++ Δ) E x) ->
    exists ms, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\
      forall x, env_entry E x = env_entry (env_extend_tagged Δ ts (List.skipn (List.length ts) E) ms) x.
Proof.
  induction Ms as [| M Ms IH]; intros [| e ts] * Hl H Hn; cbn [List.length] in Hl; try discriminate.
  - exists nil; split; [ constructor | intros x; reflexivity ].
  - assert (Hl' : List.length ts = List.length Ms) by lia.
    cbn [sb_of_list List.rev] in H, Hn; rewrite <- List.app_assoc in H, Hn; cbn [List.app] in H, Hn.
    destruct (IH ts _ (e :: Δ) _ _ Hl' H ltac:(intros x Hx; apply Hn; cbn [List.length]; lia)) as (ms & Hms & Hag).
    (** The head term, at the entry past the later ones. *)
    assert (Hx : List.length ts < List.length (List.rev ts ++ e :: Δ))
      by (rewrite List.length_app, List.length_rev; cbn [List.length]; lia).
    destruct (H _ Hx) as [_ Hev].
    assert (Hσx : sb_of_list (σ ,, M) Ms (List.length ts) = se_exp M)
      by (rewrite Hl', <- (Nat.add_0_r (List.length Ms)), sb_of_list_ge; reflexivity).
    pose proof (Hev (Hn (List.length ts) ltac:(cbn [List.length]; lia))) as Hm; rewrite Hσx in Hm.
    destruct Hm as (m & Hme & Hm).
    rewrite <- (List.length_rev ts), ctx_entry_tag_app_at, List.length_rev in Hme.
    pose proof (eval_exps_count _ _ _ Hms) as Hlms.
    exists (m :: ms); split; [ econstructor; eassumption |].
    (** The tail past the later entries has the head term's value, at its
        tag, before the rest. *)
    intros x; rewrite Hag; cbn [List.length env_extend_tagged].
    apply env_extend_tagged_eq; intros [| k]; rewrite env_entry_skipn.
    + rewrite Nat.add_0_r, Hme; reflexivity.
    + transitivity (env_entry (List.skipn (S (List.length ts)) E) k); [| reflexivity ].
      rewrite env_entry_skipn; f_equal; lia.
Qed.
#[local] Opaque eval_sub.

(** Both together: the environment agrees with the terms' values over the
    value of the substitution, on the whole context. *)
Lemma eval_sb_of_list_inv : forall Ms ts σ Δ ρ E E0, List.length ts = List.length Ms ->
    ⟦ sb_of_list σ Ms : List.rev ts ++ Δ ⟧s ρ ↘ E ->
    (forall x, x < List.length ts -> ~ entry_propositional gc_deps gc_stack (List.rev ts ++ Δ) E x) ->
    ⟦ σ : Δ ⟧s ρ ↘ E0 ->
    exists ms, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\
      env_agree_upto (List.length ts + List.length Δ) E (env_extend_tagged Δ ts E0 ms).
Proof.
  intros * Hl H Hn H0.
  destruct (eval_sb_of_list_vals _ _ _ _ _ _ Hl H Hn) as (ms & Hms & Hag).
  pose proof (eval_exps_count _ _ _ Hms) as Hlms.
  pose proof (functional_eval_sub _ _ _ _ _ (eval_sb_of_list_tail _ _ _ _ _ _ Hl H) H0) as Ht.
  exists ms; split; [ exact Hms |].
  intros x Hx; rewrite Hag.
  assert (Hlt : List.length ts = List.length ms) by lia.
  exact (env_extend_tagged_agree _ _ _ _ _ Hlt Ht x Hx).
Qed.


(** The variables of the values [vxs] in an environment extended by them
    and then by [vys], whatever their types. *)
Lemma eval_vars_from_args : forall vxs E vys,
    ⟦ vars_from (List.length vys) (List.length vxs) ⟧* gc_deps ⍮ gc_stack ⍮ env_extend_typed E (vxs ++ vys)
      ↘ List.map fst vxs.
Proof.
  induction vxs as [| [x t] vxs IH]; intros; cbn [List.length List.map fst]; [ unfold vars_from; cbn; constructor |].
  rewrite vars_from_S; econstructor; [| exact (IH (E ↦ x ⦂ t) vys) ].
  pose proof (env_entry_extend_typed_app (E ↦ x ⦂ t) (vxs ++ vys) 0) as H.
  rewrite List.length_app, Nat.add_0_r in H.
  change (env_extend_typed E (((x, t) :: vxs) ++ vys)) with (env_extend_typed (E ↦ x ⦂ t) (vxs ++ vys)).
  replace (List.length vys + List.length vxs) with (List.length vxs + List.length vys) by lia.
  assert (Hv : env_var (env_extend_typed (E ↦ x ⦂ t) (vxs ++ vys)) (List.length vxs + List.length vys) = x)
    by (unfold env_var; rewrite H; reflexivity).
  rewrite <- Hv at 2; constructor.
Qed.

End Fixed_GCtx.
