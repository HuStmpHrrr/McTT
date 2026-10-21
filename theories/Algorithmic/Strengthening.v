(** * Strengthening: the Semantic Toolkit

    A judgment in a context that has one more variable can sometimes be read
    back as a judgment in the shorter context: if its subject and type are
    already terms of the shorter one, the extra variable is irrelevant to
    them.  The induction that does this (on normal forms, in the second half of
    this file) descends under binders, so the extra variable sits at an
    arbitrary position [k], between a telescope [Δ] of assumptions and the
    shorter context [Γ]:

      short: Δ ++ Γ          long: tele_wk Δ ↑ ++ A :: Γ        φ := q^k ↑

    where [k = length Δ].  Nothing here inducts on a *derivation*: a derivation
    in the long context may pass through terms that do mention the variable
    (the [P] of [Core.Syntactic.Fresh]'s companion experiment), and those can
    never be strengthened.  Instead every equation whose two ends are typed in
    the short context is pushed through the PER model, where the extra variable
    simply never appears. *)
From Stdlib Require Import Arith Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Lemmas.
From Mctt.Core.Semantic Require Import Consequences Realizability.
From Mctt.Core.Syntactic Require Import CoreInversions Fresh.
From Mctt.Core.Syntactic.Levels Require Import LevelEq.
From Mctt.Core.Syntactic.Inductives Require Import IndCong IndConv.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas MemberWf.
From Mctt.Core.Syntactic.System Require Import Scoping.
From Mctt.Core.Syntactic.System.Global Require Import DescTyping LookupSound Presup.
From Mctt.Algorithmic Require Import Subtyping.
Import Domain_Notations Fixed_Notations Wk_Notations.

(** ** The Weakening that Inserts a Variable

    [q^k ↑] keeps the [k] innermost variables and shifts the rest by one: it is
    the weakening from the long context to the short one.  It is monotone, so
    it acts on environments by [⟪_⟫]. *)
Lemma wk_mono_qn : forall n φ, wk_mono φ -> wk_mono (wk_qn n φ).
Proof. induction n; intros; cbn; [ assumption | apply wk_mono_q; auto ]. Qed.

#[local]
Instance WkMono_qn_shift : forall k, WkMono (wk_qn k ↑).
Proof. intros k; apply wk_mono_qn, wk_mono_shift. Qed.

(** An environment under [q φ] splits: the innermost entry is kept, the rest
    is the environment under [φ].  Both halves are [Core.Semantic.Domain]
    lemmas; this is the two of them as one list equation. *)
Lemma eval_wk_q_cons : forall φ e ρ `{Hφ : WkMono φ},
    ⟪wk_q φ⟫ (e :: ρ) = e :: ⟪φ⟫ ρ.
Proof.
  intros.
  (** A list is determined by its head and its tail. *)
  pose proof (eval_wk_q_tail φ (e :: ρ)) as Htl.
  pose proof (eval_wk_q_zero_entry φ (e :: ρ)) as Hhd.
  destruct (⟪wk_q φ⟫ (e :: ρ)) as [| e' ρ'] eqn:E.
  - (** The result cannot be empty: it has the entry [e] at index 0. *)
    exfalso.
    assert (Hl : List.length (⟪wk_q φ⟫ (e :: ρ)) = 0) by (rewrite E; reflexivity).
    rewrite eval_wk_length in Hl.
    pose proof (wk_len_spec (wk_q φ) (List.length (e :: ρ)) (wk_mono_q φ Hφ) 0) as Hs.
    rewrite Hl in Hs; cbn in Hs; lia.
  - cbn in Htl, Hhd; rewrite Htl; f_equal; exact Hhd.
Qed.

(** Inserting an entry at position [k], and dropping it again. *)
Definition env_ins (k : nat) (e : dentry) (ρ : env) : env :=
  List.firstn k ρ ++ e :: List.skipn k ρ.

Lemma env_ins_zero : forall e ρ, env_ins 0 e ρ = e :: ρ.
Proof. reflexivity. Qed.

Lemma env_ins_succ : forall k e e' ρ, env_ins (S k) e (e' :: ρ) = e' :: env_ins k e ρ.
Proof. reflexivity. Qed.

Lemma eval_wk_qn_shift_ins : forall k e ρ,
    k <= List.length ρ ->
    ⟪wk_qn k ↑⟫ (env_ins k e ρ) = ρ.
Proof.
  induction k as [| k IH]; intros * Hk; cbn [wk_qn].
  - rewrite env_ins_zero; apply eval_wk_shift.
  - destruct ρ as [| e' ρ]; cbn [List.length] in Hk; [ lia |].
    rewrite env_ins_succ, eval_wk_q_cons by typeclasses eauto.
    rewrite IH by lia; reflexivity.
Qed.

(** ** Semantic Weakening at Position [k]

    [rel_wk_under_ctx_q] lifts a semantic weakening over one assumption; the
    telescope is [k] of those.  The entry types come from the well-formedness
    of the short context. *)
Section Fixed_GCtx.
Context {GC : GCtx}.

Lemma rel_wk_under_ctx_qn : forall Δ Γ A,
    tele_ass Δ ->
    ⊢ (Δ ++ Γ)%list ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    ⊨ (Γ ▹ A) ->
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊨ʷ (wk_qn (length Δ) ↑) : (Δ ++ Γ)%list.
Proof.
  induction Δ as [| e Δ IH]; intros * Hass HΓs HΓf HA;
    cbn [tele_wk List.app length wk_qn] in *.
  - apply rel_wk_under_ctx_shift; assumption.
  - (** The head of an assumption telescope is an assumption, so the step is
        [rel_wk_under_ctx_q] with the type the short context gives it. *)
    inversion Hass as [| ? ? [T ->] Hass']; subst.
    assert (⊢ (Δ ++ Γ)%list) by (eapply ctx_decomp_left; eassumption).
    assert (⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list) by (eapply ctx_decomp_left; eassumption).
    destruct (ctx_decomp HΓs) as [_ [i HT]].
    pose proof (IH _ _ Hass' ltac:(eassumption) ltac:(eassumption) HA) as Hψ.
    assert ((Δ ++ Γ)%list ⊨ T ≈ T : Typeω@i)
      by (apply completeness_fundamental_exp_eq; mauto 2).
    cbn [centry_wk]; exact (rel_wk_under_ctx_q Hψ ltac:(eassumption)).
Qed.


(** ** The Long Environment

    Reading back in the short context means reading back at its initial
    environment, so the environment of the long context must be one whose image
    under the drop is exactly that.  It cannot be the long context's own
    initial environment: that gives every variable of [Δ] a level one too big.
    So the initial environment of the short context is used, with an entry for
    the dropped variable spliced in at position [k].  Its level is irrelevant —
    a neutral is related to itself at every level ([var_per_bot]) — and so is
    its type annotation, since the model relates two neutrals by their neutral
    parts alone. *)
(** The length of an initial environment is the length of its context. *)
Lemma initial_env_length : forall Γ ρ, initial_env_f Γ ρ -> List.length ρ = List.length Γ.
Proof. induction 1; cbn; congruence. Qed.

(** A type of the short context, read in the long environment and in its
    image: the two values are related, which is what identifies the head PERs
    of the two contexts. *)
Lemma typ_along_qn : forall Δ Γ A T i ρ,
    tele_ass Δ ->
    ⊢ (Δ ++ Γ)%list ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    (Δ ++ Γ)%list ⊢ T : Typeω@i ->
    forall R,
      EF (tele_wk Δ ↑ ++ Γ ▹ A)%list ≈ (tele_wk Δ ↑ ++ Γ ▹ A)%list ∈ per_ctx_env ↘ R ->
      Dom ρ ≈ ρ ∈ R ->
      exists a b, ⟦ T[wk_qn (length Δ) ↑]ʷ ⟧ ρ ↘ a /\ ⟦ T ⟧ ⟪wk_qn (length Δ) ↑⟫ ρ ↘ b /\
                    Dom a ≈ b ∈ per_univ i.
Proof.
  intros * Hass HΓs HΓf HT * HR Hρ.
  assert (⊨ Γ ▹ A) as HA
    by (apply completeness_fundamental_ctx; eapply ctx_app_wf_tail; exact HΓf).
  pose proof (rel_wk_under_ctx_qn _ _ _ Hass HΓs HΓf HA) as Hψ.
  assert ((Δ ++ Γ)%list ⊨ T ≈ T : Typeω@i)
    by (apply completeness_fundamental_exp_eq; mauto 2).
  pose proof (rel_exp_of_typ_inversion ltac:(eassumption)) as [R0 [HR0 Hgen]].
  destruct (Hgen _ _ HR _ _ (rel_sub_of_wk Hψ) _ _ _ _ Hρ
                 (eval_sub_of_wk _ _) (eval_sub_of_wk _ _)) as [a1 a2 ? ? Ha1 Ha2 ? ? Hchain].
  rewrite exp_sub_of_wk in Ha1.
  exists a1, a2; repeat split; try eassumption.
  (** The first two links of the chain are the two readings of [T]. *)
  destruct Hchain as [H12 _]; exact H12.
Qed.

(** ** The Long Environment

    Reading back in the short context means reading back at its initial
    environment, so the environment of the long context must be one whose image
    under the drop is exactly that.  It cannot be the long context's own
    initial environment: that would give every variable of [Δ] a level one too
    big.  So the short initial environment is used, with an entry for the
    dropped variable spliced in at position [k].  The level of that entry is
    irrelevant — a neutral is related to itself at every level
    ([var_per_bot]) — and the entries of [Δ] keep the type annotations they
    have in the short environment, which [typ_along_qn] shows are related to
    the ones the long context evaluates. *)
Lemma long_env : forall Δ Γ A R ρs,
    tele_ass Δ ->
    ⊢ (Δ ++ Γ)%list ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    EF (tele_wk Δ ↑ ++ Γ ▹ A)%list ≈ (tele_wk Δ ↑ ++ Γ ▹ A)%list ∈ per_ctx_env ↘ R ->
    initial_env_f (Δ ++ Γ)%list ρs ->
    exists ρ, Dom ρ ≈ ρ ∈ R /\ ⟪wk_qn (length Δ) ↑⟫ ρ = ρs.
Proof.
  intros * Hass HΓs HΓf HR Hρs.
  (** The insertion is the construction; its image is the short environment by
      [eval_wk_qn_shift_ins], once the telescope is known to fit. *)
  enough (exists e, Dom (env_ins (length Δ) e ρs) ≈ (env_ins (length Δ) e ρs) ∈ R)
    as [e He].
  { exists (env_ins (length Δ) e ρs); split; [ exact He |].
    apply eval_wk_qn_shift_ins.
    rewrite (initial_env_length _ _ Hρs), length_app; lia. }
  clear - Hass HΓs HΓf HR Hρs.
  revert Γ A R ρs Hass HΓs HΓf HR Hρs.
  induction Δ as [| e Δ IH]; intros * Hass HΓs HΓf HR Hρs;
    cbn [tele_wk List.app length] in *;
    [| inversion Hass as [| ? ? [T ->] Hass']; subst; cbn [centry_wk] in HR ];
    inversion HR; subst;
    (** The extension clause of [per_ctx_env] names the tail PER, the head
        relation, the type's evaluations and the equivalence for [R]; they are
        picked out by shape, since [inversion] chooses the names. *)
    match goal with
    | Hc : per_ctx_env ?tr _ _, Ht : forall ρ ρ' (e : ?tr ρ ρ'), _, Hv : _ <~> _ |- _ =>
        rename Hc into Hctx, Ht into Htyp, Hv into Heqv
    end.
  - (** The dropped variable is outermost: the entry is a neutral at the type
        the context PER evaluates, at any level. *)
    destruct (per_ctx_then_per_env_initial_env Hctx) as (ρ0 & ρ0' & Hρ0 & Hρ0' & Hrel).
    assert (ρ0 = ρs) as -> by (eapply functional_initial_env; eassumption).
    assert (ρ0' = ρs) as -> by (eapply functional_initial_env; eassumption).
    destruct (Htyp _ _ Hrel) as [a1 a2 Ha1 Ha2 Helem].
    exists (de_term (⇑! a1 0)).
    apply Heqv; unfold env_ins; cbn [List.firstn List.skipn List.app].
    exists Hrel.
    functional_eval_rewrite_clear; cbn.
    eapply per_bot_then_per_elem; [ exact Helem | apply var_per_bot ].
  - (** Under an assumption of the telescope: the entry of the short initial
        environment stays where it is, and the insertion moves one position
        inwards.  Its annotation is the short type value, so the head PER is
        reached through [typ_along_qn]. *)
    assert (⊢ (Δ ++ Γ)%list) by (eapply ctx_decomp_left; eassumption).
    assert (⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list) by (eapply ctx_decomp_left; eassumption).
    destruct (ctx_decomp HΓs) as [_ [iT HT]].
    inversion Hρs as [| ? ρ0 ? t Hρs' Ht |  |]; subst.
    destruct (IH _ _ _ _ Hass' ltac:(eassumption) ltac:(eassumption) Hctx Hρs') as [e He].
    exists e.
    assert (Hsucc : forall k (d : dentry) (r : env) m,
               env_ins (S k) d (r ↦ m) = (env_ins k d r) ↦ m) by reflexivity.
    rewrite Hsucc.
    apply Heqv; exists He.
    destruct (Htyp _ _ He) as [a1 a2 Ha1 Ha2 Helem].
    destruct (typ_along_qn _ _ _ _ _ _ Hass' ltac:(eassumption) ltac:(eassumption)
                           HT _ Hctx He) as (b1 & b2 & Hb1 & Hb2 & Hbb).
    (** [b2] is the value of [T] in the short environment, which is [t]; [b1]
        is the long one, which is [a1]. *)
    rewrite eval_wk_qn_shift_ins in Hb2
      by (rewrite (initial_env_length _ _ Hρs'), length_app; lia).
    functional_eval_rewrite_clear.
    cbn.
    eapply per_bot_then_per_elem; [| apply var_per_bot ].
    (** The long and the short value of [T] are related, so the annotation the
        short environment carries sits in the same PER. *)
    destruct Hbb as [R' HR'].
    assert (HR's : per_univ_elem iT R' t a1)
      by (eapply (per_univ_PER.(PER_Symmetric)); exact HR').
    assert (Hiff : head_rel (env_ins (length Δ) e ρ0) (env_ins (length Δ) e ρ0) He <~> R')
      by (eapply per_univ_elem_left_irrel; [ exact Helem | exact HR's ]).
    assert (Htt : per_univ_elem iT R' t t)
      by (eapply (per_univ_PER.(PER_Transitive)); [ exact HR's | exact HR' ]).
    eapply per_univ_elem_resp_iff; [ exact Htt | symmetry; exact Hiff ].
Qed.


(** ** EqStr: Strengthening an Equation

    Both ends are typed in the short context, so each of them has the same
    value in the long environment under the weakening as it has in the short
    one.  The long equation links the two long values; the two instantiations
    of the ends link each long value to its short one; and the chain gives the
    short equation, read back at the short context's own length. *)
Lemma exp_eq_strengthen : forall Δ Γ A M N T,
    tele_ass Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    (Δ ++ Γ)%list ⊢ M : T ->
    (Δ ++ Γ)%list ⊢ N : T ->
    (tele_wk Δ ↑ ++ Γ ▹ A)%list
      ⊢ M[wk_qn (length Δ) ↑]ʷ ≈ N[wk_qn (length Δ) ↑]ʷ : T[wk_qn (length Δ) ↑]ʷ ->
    (Δ ++ Γ)%list ⊢ M ≈ N : T.
Proof.
  intros * Hass HΓf HM HN HL.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; mauto 3).
  assert (HAs : ⊨ (Γ ▹ A))
    by (apply completeness_fundamental_ctx; eapply ctx_app_wf_tail; exact HΓf).
  apply completeness_fundamental_exp in HM as HMs, HN as HNs.
  apply completeness_fundamental_exp_eq in HL as HLs.
  destruct HLs as [R1 HR1 i HLg].
  destruct HMs as [R0 HR0 j HMg].
  destruct HNs as [R0' HR0' k HNg].
  (** The environment of the long context whose image is the short initial
      one. *)
  destruct (per_ctx_then_per_env_initial_env HR0) as (ρs & ρs' & Hρs & Hρs' & Hrels).
  assert (ρs' = ρs) as -> by (eapply functional_initial_env; eassumption).
  destruct (long_env Δ Γ A R1 ρs Hass HΓs HΓf HR1 Hρs) as [ρ [Hρ Himg]].
  assert (⊨ (tele_wk Δ ↑ ++ Γ ▹ A)%list ≈ (tele_wk Δ ↑ ++ Γ ▹ A)%list) as HsA
      by (eexists; exact HR1).
  (** The long equation at the identity. *)
  destruct (HLg _ _ HR1 _ _ (rel_sub_id HsA) _ _ _ _ Hρ (eval_sub_id _) (eval_sub_id _))
    as [er1 [Ht1 He1]].
  (** [M] and [N] along the weakening: each links its long value to its short
      one. *)
  pose proof (rel_sub_of_wk (rel_wk_under_ctx_qn Δ Γ A Hass HΓs HΓf HAs)) as Hs.
  pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_qn (length Δ) ↑) ρ _) as Hev.
  destruct (HMg _ _ HR1 _ _ Hs _ _ _ _ Hρ Hev Hev) as [er2 [Ht2 He2]].
  destruct (HNg _ _ HR1 _ _ Hs _ _ _ _ Hρ Hev Hev) as [er3 [Ht3 He3]].
  destruct Ht1 as [t1 ? ? ? Ht11 ? ? ? Htc1].
  destruct He1 as [m1 ? n3 ? Hm11 ? Hn13 ? Hmc1].
  destruct Ht2 as [? ? ? ? ? ? ? ? Huc].
  destruct He2 as [? ? ? ? ? ? ? ? Hpc].
  destruct Ht3 as [? ? ? ? ? ? ? ? Hvc].
  destruct He3 as [? ? ? ? ? ? ? ? Hqc].
  rewrite !(exp_sub_of_wk_ext _ (wk_qn (length Δ) ↑) (ι (wk_qn (length Δ) ↑))) in * by reflexivity.
  rewrite !exp_sub_id in *.
  functional_eval_rewrite_clear.
  (** The chains, after the values have been identified: [T[φ]] and [M[φ]] have
      one value each in [ρ], [T] and [M] one each in its image, and the links
      are between those. *)
  destruct Huc as [Ht1u3 [Hu _]].
  assert (E12 : er1 <~> er2)
    by (eapply per_univ_elem_right_irrel; [ destruct Htc1 as [Hx _]; exact Hx | exact Ht1u3 ]).
  assert (E32 : er3 <~> er2)
    by (eapply per_univ_elem_right_irrel; [ destruct Hvc as [Hx _]; exact Hx | exact Ht1u3 ]).
  assert (HP : PER er2) by (eapply per_elem_PER; exact Hu).
  (** [⟦M⟧ρs ≈ ⟦M[φ]⟧ρ ≈ ⟦N[φ]⟧ρ ≈ ⟦N⟧ρs]. *)
  match goal with
  | Hp : rel_chain er2 (m1 :: ?p3 :: _), Hq : rel_chain er3 (n3 :: ?q3 :: _) |- _ =>
      assert (H1 : er2 m1 p3) by (destruct Hp as [Hx _]; exact Hx);
      assert (H2 : er2 n3 q3) by (apply E32; destruct Hq as [Hx _]; exact Hx);
      assert (H3 : er2 m1 n3) by (apply E12; destruct Hmc1 as [_ [Hx _]]; exact Hx);
      assert (Hpq : er2 p3 q3)
        by (etransitivity; [ symmetry; exact H1 | etransitivity; [ exact H3 | exact H2 ] ])
  end.
  (** Read back at the short length: the values are already those of the short
      environment, so no shift lemma is needed. *)
  destruct (per_elem_then_per_top Hu Hpq (length (Δ ++ Γ)%list)) as [W [HW HW']].
  assert (nbe_f (Δ ++ Γ)%list M T W) by (econstructor; eassumption).
  assert (nbe_f (Δ ++ Γ)%list N T W) by (econstructor; eassumption).
  transitivity W; [| symmetry ]; eapply soundness'; eassumption.
Qed.


(** The syntactic weakening at position [k], the companion of the semantic one:
    a term of the short context is a term of the long one. *)
Lemma wf_wk_qn : forall Δ Γ A,
    ⊢ (Δ ++ Γ)%list ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ʷ (wk_qn (length Δ) ↑) : (Δ ++ Γ)%list.
Proof.
  intros * HΓs HΓf.
  eapply wf_wk_ext; [| exact HΓf | exact HΓs ].
  (** The base case is the weakening by one, over the inserted assumption. *)
  apply wf_wk_shift; eapply ctx_app_wf_tail; exact HΓf.
Qed.


(** ** ShapePi: a Short Type below a [Π]

    What the long context knows about a short type can be read off in the short
    one as well: a type below a [Π] there has a [Π] for its own normal form
    here.  The subtyping is taken through the PER model rather than through the
    algorithm, because the algorithm would normalize in the long context, whose
    initial environment is not the image of ours: [per_subtyp] has a [Π] on the
    left of nothing but [per_subtyp_pi], so the type's value is a [Πᵈ], and so
    is the value it has in the short environment. *)
Lemma typ_pi_shape_strengthen : forall Δ Γ A T i C D,
    tele_ass Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    (Δ ++ Γ)%list ⊢ T : Typeω@i ->
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ T[wk_qn (length Δ) ↑]ʷ ⊆ Π C D ->
    exists C' D', nbe_ty_f (Δ ++ Γ)%list T (Πⁿ C' D').
Proof.
  intros * Hass HΓf HT Hs.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; mauto 3).
  assert (HAs : ⊨ (Γ ▹ A))
    by (apply completeness_fundamental_ctx; eapply ctx_app_wf_tail; exact HΓf).
  pose proof HT as HTs; apply completeness_fundamental_exp in HTs.
  destruct HTs as [R0 HR0 j HTg].
  (** The long subtyping's own context PER is the one everything is read at. *)
  apply completeness_fundamental_subtyp in Hs as [R1 HR1 i' Hsg].
  destruct (per_ctx_then_per_env_initial_env HR0) as (ρs & ? & Hρs & ? & ?).
  destruct (long_env Δ Γ A R1 ρs Hass HΓs HΓf HR1 Hρs) as [ρ [Hρ Himg]].
  pose proof (rel_sub_of_wk (rel_wk_under_ctx_qn Δ Γ A Hass HΓs HΓf HAs)) as Hsb.
  pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_qn (length Δ) ↑) ρ _) as Hev.
  assert (⊨ (tele_wk Δ ↑ ++ Γ ▹ A)%list ≈ (tele_wk Δ ↑ ++ Γ ▹ A)%list) as HsA
      by (eexists; exact HR1).
  (** The type at the long environment and at its image. *)
  destruct (HTg _ _ HR1 _ _ Hsb _ _ _ _ Hρ Hev Hev) as [er [Ht He]].
  destruct Ht as [? ? ? ? Hu1 ? ? ? Huc].
  destruct He as [? ? ? ? Hp1 Hp2 ? ? Hpc].
  (** The subtyping at the identity: its two values are the ones above. *)
  destruct (Hsg _ _ HR1 _ _ (rel_sub_id HsA) _ _ _ _ Hρ (eval_sub_id _) (eval_sub_id _))
    as [aσ a a'σ' a' Ha1 Ha2 Ha3 Ha4 Hau Ha'u Hsub].
  rewrite !(exp_sub_of_wk_ext _ (wk_qn (length Δ) ↑) (ι (wk_qn (length Δ) ↑))) in * by reflexivity.
  rewrite !exp_sub_id in *.
  functional_eval_rewrite_clear.
  (** The right-hand side is a [Πᵈ], and [per_subtyp_pi] is the only rule with
      one there, so the long value of [T] is a [Πᵈ]; its partner in the short
      environment is one too, since [per_univ_elem] relates only values with the
      same head. *)
  inversion Ha3; subst.
  inversion Hsub; subst.
  simplify_evals.
  assert (Hu : per_univ_elem j er 𝕌ω@i 𝕌ω@i) by (destruct Huc as [Hx _]; exact Hx).
  invert_per_univ_elem Hu.
  apply_relation_equivalence.
  assert (Hmm : per_univ i (Πᵈ a0 ρ0 B) m0) by (destruct Hpc as [Hx _]; exact Hx).
  destruct Hmm as [Rm HRm].
  invert_per_univ_elem HRm.
  (** The short value reads back, and the readback of a [Πᵈ] is a [Πⁿ]. *)
  match goal with
  | Hp : rel_chain _ (_ :: ?v :: _) |- _ =>
      assert (Hshort : per_univ i v v) by (destruct Hpc as [_ [Hx _]]; exact Hx)
  end.
  destruct Hshort as [Rs HRs].
  destruct (per_univ_then_per_top_typ HRs (length (Δ ++ Γ)%list)) as [W [HW1 ?]].
  inversion HW1; subst.
  match goal with
  | HA : Rtyp _ in _ ↘ ?C', HB : Rtyp _ in S _ ↘ ?D' |- _ =>
      exists C', D'
  end.
  econstructor; [ exact Hρs | exact Hp2 | exact HW1 ].
Qed.

(** ** ShapeInd: a Short Type below an Inductive Type

    The same for a type below an inductive type: [per_subtyp] has an
    inductive type on the right only in [per_subtyp_indty], whose left-hand
    side is one, so the type's value is an inductive type, and so is the
    value it has in the short environment, which reads back as an inductive
    type's normal form. *)
Lemma typ_ind_shape_strengthen : forall Δ Γ A T i p k Ps,
    tele_ass Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    (Δ ++ Γ)%list ⊢ T : Typeω@i ->
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ T[wk_qn (length Δ) ↑]ʷ ⊆ apps (a_ind p k) Ps ->
    exists Rs, nbe_ty_f (Δ ++ Γ)%list T (nf_indty p k Rs).
Proof.
  intros * Hass HΓf HT Hs.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; mauto 3).
  assert (HAs : ⊨ (Γ ▹ A))
    by (apply completeness_fundamental_ctx; eapply ctx_app_wf_tail; exact HΓf).
  pose proof HT as HTs; apply completeness_fundamental_exp in HTs.
  destruct HTs as [R0 HR0 j HTg].
  apply completeness_fundamental_subtyp in Hs as [R1 HR1 i' Hsg].
  destruct (per_ctx_then_per_env_initial_env HR0) as (ρs & ? & Hρs & ? & ?).
  destruct (long_env Δ Γ A R1 ρs Hass HΓs HΓf HR1 Hρs) as [ρ [Hρ Himg]].
  pose proof (rel_sub_of_wk (rel_wk_under_ctx_qn Δ Γ A Hass HΓs HΓf HAs)) as Hsb.
  pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_qn (length Δ) ↑) ρ _) as Hev.
  assert (⊨ (tele_wk Δ ↑ ++ Γ ▹ A)%list ≈ (tele_wk Δ ↑ ++ Γ ▹ A)%list) as HsA
      by (eexists; exact HR1).
  destruct (HTg _ _ HR1 _ _ Hsb _ _ _ _ Hρ Hev Hev) as [er [Ht He]].
  destruct Ht as [? ? ? ? Hu1 ? ? ? Huc].
  destruct He as [? ? ? ? Hp1 Hp2 ? ? Hpc].
  destruct (Hsg _ _ HR1 _ _ (rel_sub_id HsA) _ _ _ _ Hρ (eval_sub_id _) (eval_sub_id _))
    as [aσ a a'σ' a' Ha1 Ha2 Ha3 Ha4 Hau Ha'u Hsub].
  rewrite !(exp_sub_of_wk_ext _ (wk_qn (length Δ) ↑) (ι (wk_qn (length Δ) ↑))) in * by reflexivity.
  rewrite !exp_sub_id in *.
  functional_eval_rewrite_clear.
  destruct (eval_ind_value _ _ _ _ _ Ha3) as [ms ->].
  inversion Hsub; subst.
  simplify_evals.
  assert (Hu : per_univ_elem j er 𝕌ω@i 𝕌ω@i) by (destruct Huc as [Hx _]; exact Hx).
  invert_per_univ_elem Hu.
  apply_relation_equivalence.
  match goal with
  | Hp : rel_chain _ (?m1 :: ?m2 :: _) |- _ =>
      assert (Hmm : per_univ i m1 m2) by (destruct Hpc as [Hx _]; exact Hx);
      assert (Hshort : per_univ i m2 m2) by (destruct Hpc as [_ [Hx _]]; exact Hx)
  end.
  destruct Hmm as [Rm HRm].
  invert_per_univ_elem HRm.
  destruct Hshort as [Rs HRs].
  destruct (per_univ_then_per_top_typ HRs (length (Δ ++ Γ)%list)) as [W [HW1 ?]].
  inversion HW1; subst.
  eexists; econstructor; [ exact Hρs | eassumption | exact HW1 ].
Qed.

(** ** ShapeUniv: a Short Type above a Universe

    The same for a type above a universe: [per_subtyp] has a universe on the
    left of nothing but the three universe rules, whose right-hand sides are
    universes, so the type's value is a universe, and so is the value it has in
    the short environment, which reads back as a universe normal form. *)
Lemma typ_univ_shape_strengthen : forall Δ Γ A T i U,
    tele_ass Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    (Δ ++ Γ)%list ⊢ T : Typeω@i ->
    univ_term U ->
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ U ⊆ T[wk_qn (length Δ) ↑]ʷ ->
    (exists j, nbe_ty_f (Δ ++ Γ)%list T (Typeωⁿ@j)) \/ (exists L, nbe_ty_f (Δ ++ Γ)%list T (nf_univ_of L)).
Proof.
  intros * Hass HΓf HT HU Hs.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; mauto 3).
  assert (HAs : ⊨ (Γ ▹ A))
    by (apply completeness_fundamental_ctx; eapply ctx_app_wf_tail; exact HΓf).
  pose proof HT as HTs; apply completeness_fundamental_exp in HTs.
  destruct HTs as [R0 HR0 j HTg].
  apply completeness_fundamental_subtyp in Hs as [R1 HR1 i' Hsg].
  destruct (per_ctx_then_per_env_initial_env HR0) as (ρs & ? & Hρs & ? & ?).
  destruct (long_env Δ Γ A R1 ρs Hass HΓs HΓf HR1 Hρs) as [ρ [Hρ Himg]].
  pose proof (rel_sub_of_wk (rel_wk_under_ctx_qn Δ Γ A Hass HΓs HΓf HAs)) as Hsb.
  pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_qn (length Δ) ↑) ρ _) as Hev.
  assert (⊨ (tele_wk Δ ↑ ++ Γ ▹ A)%list ≈ (tele_wk Δ ↑ ++ Γ ▹ A)%list) as HsA
      by (eexists; exact HR1).
  destruct (HTg _ _ HR1 _ _ Hsb _ _ _ _ Hρ Hev Hev) as [er [Ht He]].
  destruct Ht as [? ? ? ? Hu1 ? ? ? Huc].
  destruct He as [? ? ? ? Hp1 Hp2 ? ? Hpc].
  destruct (Hsg _ _ HR1 _ _ (rel_sub_id HsA) _ _ _ _ Hρ (eval_sub_id _) (eval_sub_id _))
    as [aσ a a'σ' a' Ha1 Ha2 Ha3 Ha4 Hau Ha'u Hsub].
  rewrite !(exp_sub_of_wk_ext _ (wk_qn (length Δ) ↑) (ι (wk_qn (length Δ) ↑))) in * by reflexivity.
  rewrite !exp_sub_id in *.
  rewrite Himg in *.
  functional_eval_rewrite_clear.
  simplify_evals.
  assert (Hu : per_univ_elem j er 𝕌ω@i 𝕌ω@i) by (destruct Huc as [Hx _]; exact Hx).
  invert_per_univ_elem Hu.
  apply_relation_equivalence.
  match type of Hpc with
  | rel_chain _ (?m1 :: ?m2 :: _) =>
      assert (Hmm : per_univ i m1 m2) by (destruct Hpc as [Hx _]; exact Hx);
      assert (Hshort : per_univ i m2 m2) by (destruct Hpc as [_ [Hx _]]; exact Hx)
  end.
  destruct Hmm as [Rm HRm].
  destruct Hshort as [Rs HRs].
  (** The left-hand side is a universe, so the right-hand one is too. *)
  destruct HU; inversion Ha1; subst; inversion Hsub; subst.
  all: invert_per_univ_elem HRm.
  all: destruct (per_univ_then_per_top_typ HRs (length (Δ ++ Γ)%list)) as [W [HW1 ?]].
  all: inversion HW1; subst.
  all: first [ left; eexists; econstructor; [ exact Hρs | eassumption | exact HW1 ]
             | right; eexists; econstructor; [ exact Hρs | eassumption | exact HW1 ] ].
Qed.

(** ** The Semantic Subtyping, Read Back

    Two types related by [per_subtyp] read back, at every length, to normal
    forms the algorithmic subtyping relates.  It is what lets a subtyping in
    the long context be read in the short one: the long subtyping is a
    semantic one between the values the short types have in the short
    initial environment, and their readbacks are the short normal forms. *)
Lemma per_subtyp_read : forall i a b,
    Sub a <: b at i ->
    forall s, exists A B, Rtyp a in s ↘ A /\ Rtyp b in s ↘ B /\ ⊢anf A ⊆ B.
Proof.
  induction 1; intros s.
  1-4: try destruct (H s) as [L [HL HL']];
    do 2 eexists; repeat split; [ econstructor; eassumption | econstructor; eassumption
                                    | first [ apply asnf_level; assumption | constructor; cbn; auto ] ].
  - do 2 eexists; repeat split; [ constructor | constructor | apply asnf_univ; assumption ].
  - destruct (H s) as [[c xs] [d ys] HL HL' Hle].
    do 2 eexists; repeat split; [ econstructor; eassumption | econstructor; eassumption | apply asnf_suniv; exact Hle ].
  - destruct (H s) as [W [HW _]].
    destruct (read_nf_level_real _ _ _ _ HW) as [[c xs] [-> _]].
    do 2 eexists; repeat split; [ econstructor; eassumption | constructor | apply asnf_small_large ].
  - (** The domains read back equally; the codomains at the fresh variable are
        below each other by the induction hypothesis. *)
    assert (Ha : per_univ_elem i in_rel a a)
      by (eapply (proj1 (per_univ_elem_trans _ _ _ _ H)); apply (per_univ_elem_sym _ _ _ _ H)).
    assert (Ha' : per_univ_elem i in_rel a' a')
      by (eapply (proj1 (per_univ_elem_trans _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ H)))); exact H).
    destruct (per_univ_then_per_top_typ H s) as [A [HA HA']].
    destruct (per_univ_elem_pi_clean_inversion Ha H2) as [out1 [Hout1 _]].
    destruct (per_univ_elem_pi_clean_inversion Ha' H3) as [out2 [Hout2 _]].
    destruct (Hout1 _ _ (per_bot_then_per_elem Ha (var_per_bot (n := s)))) as [b ? Hb ? _].
    destruct (Hout2 _ _ (per_bot_then_per_elem Ha' (var_per_bot (n := s)))) as [b' ? Hb' ? _].
    destruct (H1 _ _ _ _ (per_bot_then_per_elem H (var_per_bot (n := s))) Hb Hb' (S s))
      as (C & C' & HC & HC' & HCC').
    exists (Πⁿ A C), (Πⁿ A C'); split; [| split ].
    + eapply read_typ_pi; [ exact HA | exact Hb | exact HC ].
    + eapply read_typ_pi; [ exact HA' | exact Hb' | exact HC' ].
    + apply asnf_pi; [ reflexivity | exact HCC' ].
  - (** Related inductive types read back alike. *)
    destruct (per_univ_then_per_top_typ H s) as [W [HW HW']].
    exists W, W; split; [ exact HW | split; [ exact HW' |] ].
    inversion HW; subst; apply asnf_refl; cbn; auto.
Qed.

(** ** SubStr: Strengthening a Subtyping

    Both sides are short types, so the long subtyping is a semantic one between
    the values they have in the long environment, and those are related to the
    values they have in the short one; the readbacks of the latter are their
    short normal forms ([per_subtyp_read]), so the algorithmic subtyping holds
    in the short context, and with it the declarative one. *)
Lemma subtyp_strengthen : forall Δ Γ A T T' i,
    tele_ass Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    (Δ ++ Γ)%list ⊢ T : Typeω@i ->
    (Δ ++ Γ)%list ⊢ T' : Typeω@i ->
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ T[wk_qn (length Δ) ↑]ʷ ⊆ T'[wk_qn (length Δ) ↑]ʷ ->
    (Δ ++ Γ)%list ⊢ T ⊆ T'.
Proof.
  intros * Hass HΓf HT HT' Hs.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; mauto 3).
  assert (HAs : ⊨ (Γ ▹ A))
    by (apply completeness_fundamental_ctx; eapply ctx_app_wf_tail; exact HΓf).
  pose proof HT as HTs; apply completeness_fundamental_exp in HTs.
  destruct HTs as [R0 HR0 j HTg].
  pose proof HT' as HTs'; apply completeness_fundamental_exp in HTs'.
  destruct HTs' as [R0' HR0' j' HTg'].
  apply completeness_fundamental_subtyp in Hs as [R1 HR1 i' Hsg].
  destruct (per_ctx_then_per_env_initial_env HR0) as (ρs & ? & Hρs & ? & ?).
  destruct (long_env Δ Γ A R1 ρs Hass HΓs HΓf HR1 Hρs) as [ρ [Hρ Himg]].
  pose proof (rel_sub_of_wk (rel_wk_under_ctx_qn Δ Γ A Hass HΓs HΓf HAs)) as Hsb.
  pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_qn (length Δ) ↑) ρ _) as Hev.
  assert (⊨ (tele_wk Δ ↑ ++ Γ ▹ A)%list ≈ (tele_wk Δ ↑ ++ Γ ▹ A)%list) as HsA
      by (eexists; exact HR1).
  destruct (HTg _ _ HR1 _ _ Hsb _ _ _ _ Hρ Hev Hev) as [er [Ht He]].
  destruct (HTg' _ _ HR1 _ _ Hsb _ _ _ _ Hρ Hev Hev) as [er' [Ht' He']].
  destruct (Hsg _ _ HR1 _ _ (rel_sub_id HsA) _ _ _ _ Hρ (eval_sub_id _) (eval_sub_id _))
    as [aσ a a'σ' a' Ha1 Ha2 Ha3 Ha4 Hau Ha'u Hsub].
  destruct Ht as [? ? ? ? Hu1 ? ? ? Huc].
  destruct He as [? ? ? ? Hp1 Hp2 ? ? Hpc].
  destruct Ht' as [? ? ? ? Hv1 ? ? ? Hvc].
  destruct He' as [? ? ? ? Hq1 Hq2 ? ? Hqc].
  rewrite !(exp_sub_of_wk_ext _ (wk_qn (length Δ) ↑) (ι (wk_qn (length Δ) ↑))) in * by reflexivity.
  rewrite !exp_sub_id in *.
  rewrite Himg in *.
  functional_eval_rewrite_clear.
  simplify_evals.
  (** Both type values are in [per_univ i], at the long environment and at its
      image; the subtyping moves along them. *)
  assert (Hu : per_univ_elem j er 𝕌ω@i 𝕌ω@i) by (destruct Huc as [Hx _]; exact Hx).
  assert (Hu' : per_univ_elem j' er' 𝕌ω@i 𝕌ω@i) by (destruct Hvc as [Hx _]; exact Hx).
  invert_per_univ_elem Hu.
  invert_per_univ_elem Hu'.
  apply_relation_equivalence.
  assert (Hm : per_univ i mσ0 m'0) by (destruct Hpc as [Hx _]; exact Hx).
  assert (Hn : per_univ i mσ2 m'2) by (destruct Hqc as [Hx _]; exact Hx).
  destruct Hm as [Rm HRm]; destruct Hn as [Rn HRn].
  assert (Hs2 : Sub m'0 <: m'2 at (max i i')).
  { eapply per_subtyp_transp;
      [ eapply per_subtyp_cumu_right; exact Hsub
      | eapply per_univ_elem_cumu_max_left; exact HRm
      | eapply per_univ_elem_cumu_max_left; exact HRn ]. }
  destruct (per_subtyp_read _ _ _ Hs2 (length (Δ ++ Γ)%list)) as (W & W' & HW & HW' & HWW').
  eapply alg_subtyping_sound; [| exact HT | exact HT' ].
  econstructor; [ econstructor; [ exact Hρs | eassumption | exact HW ]
                | econstructor; [ exact Hρs | eassumption | exact HW' ] | exact HWW' ].
Qed.


(** * Strengthening Normal Forms

    A normal form typed in the long context at a short type is typed at that
    type in the short context.  The induction is on the normal form, not on the
    derivation: each case inverts the long typing of its head ([CoreInversions]),
    strengthens the parts by the induction hypotheses, and moves the remaining
    subtyping and equations with [subtyp_strengthen] and [exp_eq_strengthen].
    A neutral has no type of its own to be checked against, so its statement
    returns one: a short type whose weakening is below the long one. *)

(** ** Syntactic Helpers *)

Lemma exp_wk_sub_id_extend : forall M N φ, M[Id,,N][φ]ʷ = M[wk_q φ]ʷ[Id,,N[φ]ʷ].
Proof.
  intros; rewrite exp_wk_sub_extend_head, exp_sub_wk_q_extend.
  apply exp_sub_sb_eq; pointwise_solve.
Qed.

(** A variable of the long context that is the image of a short one has the
    weakened short type. *)
Lemma lookup_strengthen : forall Δ Γ A x A1,
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ∋ #(wk_qn (length Δ) ↑ x) : A1 ->
    exists T, (Δ ++ Γ)%list ∋ #x : T /\ A1 = T[wk_qn (length Δ) ↑]ʷ.
Proof.
  induction Δ as [| e Δ IH]; intros * H; cbn [tele_wk List.app length wk_qn] in *.
  - inversion H; subst; eexists; split; [ eassumption | reflexivity ].
  - destruct x as [| y]; cbn in H.
    + destruct e; cbn [centry_wk] in H; inversion H; subst.
      all: eexists; split; [ constructor | rewrite exp_wk_shift_wk_q; reflexivity ].
    + inversion H; subst.
      destruct (IH _ _ _ _ ltac:(eassumption)) as [T [HT ->]].
      eexists; split; [ constructor; exact HT | rewrite exp_wk_shift_wk_q; reflexivity ].
Qed.

(** The level expressions: a canonical level is typed at a [Level@n] with
    atoms typed at the same [Level@n], or it is a single atom with no offset,
    which is the atom itself.  The typing rules of the level formers take
    their arguments at a common sort, and [wf_subtyp_level] moves every part
    to the sort of the whole. *)
Lemma succl_n_wf_inv : forall Γ k M C,
    Γ ⊢ succl_n (S k) M : C ->
    exists n, Γ ⊢ succl_n (S k) M : Level@n /\ Γ ⊢ Level@n ⊆ C /\ Γ ⊢ M : Level@n.
Proof.
  intros * H; cbn [succl_n] in H.
  apply wf_succl_inversion in H as (n & HM & HC).
  exists n; split; [ mauto 3 | split; [ exact HC | eapply (wf_succl_n_inversion k); exact HM ] ].
Qed.

Lemma lvl_fold_wf_list : forall Γ n xs hd,
    Γ ⊢ lvl_fold hd xs : Level@n ->
    Γ ⊢ hd : Level@n /\ List.Forall (fun p => Γ ⊢ snd p : Level@n) xs.
Proof.
  intros Γ n xs; induction xs as [| [k a] r IH]; cbn; intros hd H; [ split; [ exact H | constructor ] |].
  apply IH in H as [Hh Hr]; apply wf_maxl_inversion in Hh as (m & Hh & Ha & Hmn).
  split; [ eapply wf_exp_subtyp'; [ exact Hh | exact Hmn ] |].
  constructor; [ cbn; eapply (wf_succl_n_inversion k); eapply wf_exp_subtyp'; [ exact Ha | exact Hmn ] | exact Hr ].
Qed.

Lemma lvl_fold_maxl_inv : forall Γ xs M N C,
    Γ ⊢ lvl_fold (maxl M N) xs : C ->
    exists n, Γ ⊢ lvl_fold (maxl M N) xs : Level@n /\ Γ ⊢ Level@n ⊆ C.
Proof.
  intros Γ xs; induction xs as [| [k a] r IH]; cbn; intros * H.
  - apply wf_maxl_inversion in H as (n & ? & ? & ?); exists n; split; [ mauto 3 | assumption ].
  - apply IH in H; exact H.
Qed.

(** The constant of a fold typed at [Level@n] is a literal of a tier at most
    [n]. *)
Lemma lvl_fold_maxl_cst : forall Γ c X r n,
    Γ ⊢ lvl_fold (maxl (𝕃ᵒ c) X) r : Level@n ->
    fst c <= n.
Proof.
  intros * H; apply lvl_fold_hd_sort in H; apply wf_maxl_inversion in H as (m & Hc & _ & Hs).
  apply subtyp_level_inv in Hs; apply wf_llit_sort in Hc; lia.
Qed.

Lemma lvl_exp_of_inv : forall Γ c xs C,
    Γ ⊢ lvl_exp_of c xs : C ->
    (exists n, Γ ⊢ Level@n ⊆ C /\ fst c <= n /\ List.Forall (fun p => Γ ⊢ snd p : Level@n) xs) \/
      (exists a, c = oz /\ xs = (0, a) :: nil).
Proof.
  intros * H; destruct xs as [| [k a] r].
  - cbn in H; left; destruct (wf_llit_inversion_sort _ _ _ _ _ H) as (n & Hcn & Hn).
    exists n; split; [ exact Hn | split; [ exact Hcn | constructor ] ].
  - destruct (o2_eq_dec c oz) as [-> | Hc]; [ cbn in H |].
    2: assert (E : lvl_exp_of c ((k, a) :: r) = lvl_fold (maxl (𝕃ᵒ c) (succl_n k a)) r)
         by (destruct c as [[|] [|]]; [ exfalso; apply Hc; reflexivity | reflexivity .. ]);
       rewrite E in H; clear E.
    all: destruct r as [| [k' a'] r'], k as [| k]; cbn [lvl_fold] in H.
    + right; eexists; split; reflexivity.
    + left; apply succl_n_wf_inv in H as (n & ? & ? & ?); exists n;
        split; [ assumption | split; [ cbn; lia | repeat constructor; assumption ] ].
    + left; apply lvl_fold_maxl_inv in H as (n & H & HC); exists n; split; [ exact HC | split; [ cbn; lia |] ].
      apply lvl_fold_wf_list in H as [Hh Hr]; apply wf_maxl_inversion in Hh as (m & ? & ? & Hmn).
      constructor; [ eapply wf_exp_subtyp'; eassumption
                   | constructor; [ cbn; eapply (wf_succl_n_inversion k'); eapply wf_exp_subtyp'; eassumption | exact Hr ] ].
    + left; apply lvl_fold_maxl_inv in H as (n & H & HC); exists n; split; [ exact HC | split; [ cbn; lia |] ].
      apply lvl_fold_wf_list in H as [Hh Hr]; apply wf_maxl_inversion in Hh as (m & Hk & ? & Hmn).
      constructor; [ cbn; eapply (wf_succl_n_inversion (S k)); eapply wf_exp_subtyp'; [ exact Hk | exact Hmn ]
                   | constructor; [ cbn; eapply (wf_succl_n_inversion k'); eapply wf_exp_subtyp'; eassumption | exact Hr ] ].
    + left; apply wf_maxl_inversion in H as (n & Hcl & Ha & HC); exists n;
        split; [ exact HC | split; [ exact (wf_llit_sort Hcl) |] ].
      repeat constructor; cbn; exact Ha.
    + left; apply wf_maxl_inversion in H as (n & Hcl & Ha & HC); exists n;
        split; [ exact HC | split; [ exact (wf_llit_sort Hcl) |] ].
      repeat constructor; cbn; eapply (wf_succl_n_inversion (S k)); exact Ha.
    + left; apply lvl_fold_maxl_inv in H as (n & H & HC); exists n; split; [ exact HC |].
      split; [ apply lvl_fold_hd_sort in H; apply wf_maxl_inversion in H as (m0 & H0 & _ & Hs0);
               apply subtyp_level_inv in Hs0; pose proof (lvl_fold_maxl_cst _ _ _ nil _ H0); lia |].
      apply lvl_fold_wf_list in H as [Hh Hr]; apply wf_maxl_inversion in Hh as (m & Hh1 & ? & Hmn).
      apply wf_maxl_inversion in Hh1 as (m' & _ & ? & Hm'm).
      assert (Γ ⊢ Level@m' ⊆ Level@n) by (etransitivity; eassumption).
      constructor; [ eapply wf_exp_subtyp'; eassumption
                   | constructor; [ cbn; eapply (wf_succl_n_inversion k'); eapply wf_exp_subtyp'; eassumption | exact Hr ] ].
    + left; apply lvl_fold_maxl_inv in H as (n & H & HC); exists n; split; [ exact HC |].
      split; [ apply lvl_fold_hd_sort in H; apply wf_maxl_inversion in H as (m0 & H0 & _ & Hs0);
               apply subtyp_level_inv in Hs0; pose proof (lvl_fold_maxl_cst _ _ _ nil _ H0); lia |].
      apply lvl_fold_wf_list in H as [Hh Hr]; apply wf_maxl_inversion in Hh as (m & Hh1 & ? & Hmn).
      apply wf_maxl_inversion in Hh1 as (m' & _ & Hk & Hm'm).
      assert (Γ ⊢ Level@m' ⊆ Level@n) by (etransitivity; eassumption).
      constructor; [ cbn; eapply (wf_succl_n_inversion (S k)); eapply wf_exp_subtyp'; [ exact Hk | eassumption ]
                   | constructor; [ cbn; eapply (wf_succl_n_inversion k'); eapply wf_exp_subtyp'; eassumption | exact Hr ] ].
Qed.

(** A path names a closed module: it is a module expression in every
    well-formed context, denoting the same there ([mdenote_closed_any]). *)
Lemma path_wf_any_ctx : forall H p Γ Γ',
    mod_qname H = Some p ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    ⊢ Γ' ->
    gc_deps ⍮ gc_stack ⍮ Γ' ⊢ᵐ H ≈ H.
Proof.
  induction H as [fp | x | H IH y | H IH N | U]; intros * Hp HH HΓ'; cbn in Hp; try discriminate.
  - destruct (me_denotes _ _ _ _ _ HH) as (R & _ & Hm & _).
    inversion Hm; subst; eapply wf_me_unit; eassumption.
  - destruct (mod_qname H) as [p0 |] eqn:E; [| discriminate ].
    pose proof (ctx_wf_gctx _ _ _ HΓ') as Hg.
    pose proof (gctx_valid_syn _ _ Hg) as Hv.
    pose proof (proj1 (modexp_gen _ _ _ _ _ HH)) as HH0; cbn in HH0.
    destruct (me_denotes _ _ _ _ _ HH) as (R & Rm & Hm & Hmd).
    destruct (desc_ok_tele _ _ _ _ (desc_ok_mod _ _ Hg _ _ _ (me_desc_ok _ _ _ _ _ _ HH Hm) Hmd)
                (ds_mod_is_mod _ _ _ _ Hmd)) as [T HT].
    assert (Hmt : ds_mtele gc_deps gc_stack R = Some T) by (unfold ds_mtele; rewrite Hmd; exact HT).
    pose proof (mdenote_closed_any _ _ (wf_gstack_closed _ _ Hg) _ _ _ Γ' Hm
                  (mod_qname_scoped (me_mem H y) (qname_app p0 (y :: nil)) 0 ltac:(cbn; rewrite E; reflexivity))) as Hm'.
    eapply wf_me_mem; [ eapply IH; [ reflexivity | exact HH0 | exact HΓ' ] | exact Hm' | exact Hmt | exact Hm' | exact Hmt ].
Qed.

(** A member of a path is typed, at a closed type, in every well-formed
    context: the type it is looked up at. *)
Lemma path_mem_any_ctx : forall Γ H p x C,
    mod_qname H = Some p ->
    Γ ⊢ a_mem H x : C ->
    exists T, exp_scoped 0 T /\ Γ ⊢ T ⊆ C /\ (forall Γ', ⊢ Γ' -> Γ' ⊢ a_mem H x : T).
Proof.
  intros * Hp HM.
  remember gc_deps as Θ0 eqn:HΘ; remember gc_stack as Ξ0 eqn:HΞ.
  remember (a_mem H x) as M eqn:EM.
  revert H p x Hp EM.
  induction HM; intros Hm pm xm Hpm EMm; subst; try discriminate; try (injection EMm as <- <-).
  - (** The type the member is looked up at: closed, as the lookup reads
        nothing of the context. *)
    match goal with HH : _ ⍮ _ ⍮ _ ⊢ᵐ ?H0 ≈ ?H0, Hd : mdenote _ _ _ (me_mem ?H0 ?y) ?R, Ht : ds_ty _ _ ?R = Some ?A0,
                    HA0 : _ ⊢ ?A0 : Typeω@_ |- _ =>
      pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg;
      pose proof (wf_gstack_closed _ _ Hg) as Hc;
      assert (HHs : modexp_scoped 0 (me_mem H0 y)) by (cbn; exact (mod_qname_scoped _ _ _ Hpm));
      assert (HA : exp_scoped 0 A0)
        by (pose proof (proj1 (mdenote_scoped_all _ _ Hc) _ _ _ Hd 0 ltac:(intros ? ? Hx; lia) HHs) as HR;
            exact (ds_ty_scoped _ _ _ _ _ Hc HR Ht));
      exists A0; split; [ exact HA | split; [ eapply wf_subtyp_refl'; apply wf_exp_eq_refl; exact HA0 |] ];
      intros Γ' HΓ';
      eapply wf_mem_desc; [ eapply path_wf_any_ctx; [ exact Hpm | exact HH | exact HΓ' ] | | exact Ht ];
      exact (mdenote_closed_any _ _ Hc _ _ _ Γ' Hd HHs) end.
  - match goal with IH : _ = _ -> _ = _ -> forall _ _ _, _ -> _ -> _ |- _ =>
      destruct (IH eq_refl eq_refl _ _ _ Hpm eq_refl) as (T & HT & HTs & HT') end.
    exists T; split; [ exact HT | split; [ etransitivity; eassumption | exact HT' ] ].
Qed.

(** [subtyp_strengthen] with the two sides at their own universes. *)
Corollary subtyp_strengthen' : forall Δ Γ A T T' i j,
    tele_ass Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    (Δ ++ Γ)%list ⊢ T : Typeω@i ->
    (Δ ++ Γ)%list ⊢ T' : Typeω@j ->
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ T[wk_qn (length Δ) ↑]ʷ ⊆ T'[wk_qn (length Δ) ↑]ʷ ->
    (Δ ++ Γ)%list ⊢ T ⊆ T'.
Proof.
  intros * Hass HΓf HT HT' Hs.
  eapply subtyp_strengthen;
    [ exact Hass | exact HΓf | eapply lift_exp_max_left; exact HT | eapply lift_exp_max_right; exact HT' | exact Hs ].
Qed.

(** For a type the weakening fixes, such as a constant. *)
Corollary subtyp_strengthen_closed : forall Δ Γ A K T i j,
    tele_ass Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    (Δ ++ Γ)%list ⊢ K : Typeω@j ->
    (Δ ++ Γ)%list ⊢ T : Typeω@i ->
    K[wk_qn (length Δ) ↑]ʷ = K ->
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ K ⊆ T[wk_qn (length Δ) ↑]ʷ ->
    (Δ ++ Γ)%list ⊢ K ⊆ T.
Proof.
  intros * Hass HΓf HK HT HKφ Hs; rewrite <- HKφ in Hs.
  eapply subtyp_strengthen'; eassumption.
Qed.

(** A [Π] below a [Π]: the domains are equal and the codomains below each
    other, under the left domain. *)
Lemma subtyp_pi_inv : forall Γ A B A' B',
    Γ ⊢ Π A B ⊆ Π A' B' ->
    (exists k, Γ ⊢ A ≈ A' : Typeω@k) /\ Γ ▹ A ⊢ B ⊆ B'.
Proof.
  intros * H.
  destruct (subtyp_spec H) as [[k Heq] | [(U & V & [k1 HU] & [k2 HV] & HUV) | (A1 & A2 & B1 & B2 & [k1 Ha] & [k2 Hb] & [k3 Hab] & Hsub)]].
  - destruct (exp_eq_pi_inversion Heq) as [HA HB].
    split; [ eexists; exact HA | eapply wf_subtyp_refl'; exact HB ].
  - exfalso; destruct (univ_sub_sort_term HUV) as [HUt _].
    eapply (pi_sort_term_absurd HUt); exact HU.
  - destruct (exp_eq_pi_inversion Ha) as [HA1 HA2].
    destruct (exp_eq_pi_inversion Hb) as [HB1 HB2].
    assert (HAB1 : Γ ⊢ A ≈ B1 : Typeω@(max k1 k3))
      by (eapply exp_eq_trans_typ_max; [ exact HA1 | exact Hab ]).
    assert (HId : Γ ▹ A ⊢ˢ Id : Γ ▹ B1) by (eapply wf_sub_id_extend_eq'; symmetry; exact HAB1).
    split; [ eexists; eapply exp_eq_trans_typ_max; [ exact HAB1 | exact HB1 ] |].
    etransitivity; [ eapply wf_subtyp_refl'; exact HA2 |].
    etransitivity; [ eapply ctxsub_subtyp; [ exact HId | exact Hsub ] |].
    eapply wf_subtyp_refl', ctxsub_exp_eq; [ exact HId | exact HB2 ].
Qed.

(** A type above a [Π] is a [Π]. *)
Lemma subtyp_pi_left_shape : forall Γ A B T,
    Γ ⊢ Π A B ⊆ T ->
    exists A' B' k, Γ ⊢ T ≈ Π A' B' : Typeω@k.
Proof.
  intros * H.
  destruct (subtyp_spec H) as [[k Heq] | [(U & V & [k1 HU] & [k2 HV] & HUV) | (A1 & A2 & B1 & B2 & _ & [k2 Hb] & _ & _)]].
  - do 3 eexists; symmetry; exact Heq.
  - exfalso; destruct (univ_sub_sort_term HUV) as [HUt _].
    eapply (pi_sort_term_absurd HUt); exact HU.
  - do 3 eexists; symmetry; exact Hb.
Qed.

(** ** The Arguments of an Application of a Head of a [Π] over a Telescope

    A head every type of which is above a [Π] over a telescope, applied to
    as many arguments, has them of the instances of the telescope's types. *)
Lemma wf_apps_ctx_pi_inv : forall n Δ Γ B i M Ms T,
    List.length Δ = n ->
    tele_ass Δ -> ⊢ (Δ ++ Γ)%list -> (Δ ++ Γ)%list ⊢ B : Typeω@i ->
    (forall T', Γ ⊢ M : T' -> Γ ⊢ ctx_pi Δ B ⊆ T') ->
    List.length Ms = List.length Δ ->
    Γ ⊢ apps M Ms : T ->
    forall k N T', List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T' -> Γ ⊢ N : T'.
Proof.
  induction n as [| n IH]; intros * Hn Hass HΔ HB HP Hl HMs.
  - destruct Δ; [| discriminate ]; destruct Ms; [| discriminate ]; intros [|] ? ? H; discriminate.
  - destruct (List.exists_last (l := Δ)) as (Δ0 & e & ->); [ intros ->; discriminate |].
    rename Δ0 into Δ.
    rewrite List.length_app in Hn; cbn in Hn.
    unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A0 ->] _].
    rewrite List.length_app in Hl; cbn in Hl.
    destruct Ms as [| M0 Ms]; [ cbn in Hl; lia |]; cbn in Hl.
    rewrite <- List.app_assoc in HΔ, HB; cbn [List.app] in HΔ, HB.
    destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ [kA HA0]].
    cbn [apps_exp] in HMs.
    (** The first argument, of the first type. *)
    assert (Happ : forall T', Γ ⊢ M $ M0 : T' -> Γ ⊢ M0 : A0 /\ Γ ⊢ (ctx_pi Δ B)[Id,,M0] ⊆ T').
    { intros T' HT'.
      destruct (wf_app_inversion HT') as (X & Y & HM & HM0 & HYT).
      pose proof (HP _ HM) as Hs; rewrite ctx_pi_snoc in Hs.
      destruct (subtyp_pi_inv _ _ _ _ _ Hs) as [[k HAX] HBY].
      assert (HM0' : Γ ⊢ M0 : A0) by (eapply wf_conv'; [ exact HM0 | symmetry; exact HAX ]).
      split; [ exact HM0' |].
      etransitivity; [| exact HYT ].
      eapply sub_preserves_subtyp; [ exact HBY | eapply wf_sub_single; [ exact HA0 | exact HM0' ] ]. }
    destruct (wf_apps_head _ _ _ HMs) as (T1 & HT1).
    destruct (Happ _ HT1) as [HM0 _].
    pose proof (wf_sub_single _ _ _ _ _ _ HA0 HM0) as Hs.
    assert (HΔ' : ⊢ (tele_sub Δ (Id,,M0) ++ Γ)%list) by (eapply ctx_sub_wf; eassumption).
    pose proof (wf_sub_ext _ _ _ _ _ _ Hs HΔ' HΔ) as Hs'.
    intros [| k'] N T' HN HT'.
    + cbn in HN; injection HN as <-.
      rewrite tele_insts_snoc in HT'; cbn in HT'; injection HT' as <-; rewrite exp_sub_id; exact HM0.
    + cbn in HN.
      eapply (IH (tele_sub Δ (Id,,M0)) Γ (B[sb_qn (List.length Δ) (Id,,M0)]) i (M $ M0) Ms T);
        [ rewrite length_tele_sub; lia | apply tele_ass_sub; exact Hass | exact HΔ'
        | exact (sub_preserves_exp _ _ _ _ _ _ _ HB Hs') | | rewrite length_tele_sub; lia | exact HMs | exact HN |].
      * intros T'' HT''; destruct (Happ _ HT'') as [_ H']; rewrite ctx_pi_sub in H'; exact H'.
      * rewrite tele_insts_snoc in HT'; cbn [List.nth_error] in HT'.
        rewrite tele_insts_tele_sub; rewrite <- HT'; f_equal.
        apply tele_insts_sb_eq; apply sb_compose_id_right.
Qed.

(** The parameters of a member's type former applied, typed at the
    member's telescope. *)
Lemma wf_ind_apps_inv : forall Γ p D k Mk Ms T, ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk ->
    Γ ⊢ apps (a_ind p k) Ms : T -> List.length Ms = im_np D Mk ->
    forall j P T', List.nth_error Ms j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id Ms) j = Some T' -> Γ ⊢ P : T'.
Proof.
  intros * Hl Hk HMs HMl.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  destruct (ind_ty_typed _ _ _ _ _ _ HD Hc Hk HΓ) as [i Hi].
  pose proof (decl_closed_params_ass D k Mk Hc Hk) as Hass.
  pose proof (ctx_pi_inv_outer _ _ _ _ Hass Hi) as HB.
  assert (HPΓ : ⊢ (im_params D Mk ++ Γ)%list) by (gen_presups; assumption).
  eapply (wf_apps_ctx_pi_inv _ (im_params D Mk) Γ _ i (a_ind p k) Ms T eq_refl Hass HPΓ HB);
    [ | rewrite length_im_params; exact HMl | exact HMs ].
  intros T' HT'; destruct (wf_ind_inversion HT') as [D' Mk' Hl' Hk' _ Hsub].
  assert (D' = D) as -> by congruence; assert (Mk' = Mk) as -> by congruence; exact Hsub.
Qed.

(** ** Instances of Telescopes

    An entry of a telescope instantiated at terms of the instances of the
    entries before it is a type; so terms each typed at its instance once
    that instance is a type are all typed. *)
Lemma tele_insts_typed : forall Δ Γ0 Γ σ Ms,
    tele_ass Δ -> ⊢ (Δ ++ Γ0)%list -> Γ ⊢ˢ σ : Γ0 ->
    forall j T, List.nth_error (tele_insts Δ σ Ms) j = Some T ->
      (forall j' N T', j' < j -> List.nth_error Ms j' = Some N -> List.nth_error (tele_insts Δ σ Ms) j' = Some T' ->
         Γ ⊢ N : T') ->
      exists i, Γ ⊢ T : Typeω@i.
Proof.
  induction Δ as [| e Δ IH] using List.rev_ind; intros * Hass HΔ Hσ j T HT HMs.
  - unfold tele_insts in HT; cbn in HT; destruct Ms, j; discriminate.
  - unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A0 ->] _].
    destruct Ms as [| M0 Ms].
    + unfold tele_insts in HT; rewrite List.rev_app_distr in HT; cbn in HT; destruct j; discriminate.
    + rewrite tele_insts_snoc in HT, HMs.
      rewrite <- List.app_assoc in HΔ; cbn [List.app] in HΔ.
      destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ0 [k HA0]].
      destruct j as [| j]; cbn in HT.
      * injection HT as <-; exists k; exact (sub_preserves_exp _ _ _ _ _ _ _ HA0 Hσ).
      * eapply IH; [ exact Hass | exact HΔ | | exact HT |].
        -- eapply wf_sub_extend; [ exact Hσ | exact HA0 |].
           apply (HMs 0); [ lia | reflexivity | reflexivity ].
        -- intros j' N T' Hj' HN HT'; apply (HMs (S j')); [ lia | exact HN | exact HT' ].
Qed.

Lemma tele_insts_typed_all : forall Δ Γ0 Γ σ Ms,
    tele_ass Δ -> ⊢ (Δ ++ Γ0)%list -> Γ ⊢ˢ σ : Γ0 ->
    (forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ σ Ms) j = Some T ->
       (exists i, Γ ⊢ T : Typeω@i) -> Γ ⊢ N : T) ->
    forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ σ Ms) j = Some T -> Γ ⊢ N : T.
Proof.
  intros * Hass HΔ Hσ HMs j; induction j as [j IH] using lt_wf_ind; intros N T HN HT.
  apply (HMs j); [ exact HN | exact HT |].
  eapply tele_insts_typed; [ exact Hass | exact HΔ | exact Hσ | exact HT |].
  intros j' N' T' Hj' HN' HT'; exact (IH j' Hj' _ _ HN' HT').
Qed.

(** ** A Member's Type at the Parameters of its Type Former

    The type of the member [m] of the group at [p], at the uniform
    parameters [Us], is that of the declared member [k] of the group at
    [pc] ([im_ref]) at the member's uniform arguments ([im_pre]) and its
    non-uniform parameters.  Parameters [Rs] of that type former whose
    uniform ones are equal to the member's uniform arguments give the
    member's non-uniform parameters. *)

(** What parameters [Rs] of the type former of [k] at [pc] give the member
    [m], [Mm], of the group [D] at [p], at the uniform parameters [Us]:
    non-uniform parameters [Ns] of the member, and the equality of the two
    types. *)
Record mty_params_link (Γ : ctx) (p : qname) (D : ind_decl) (m : nat) (Mm : imember) (Us Ns : list exp)
    (pc : qname) (k : nat) (Rs : list exp) : Prop := mk_mty_params_link
  { (** As many as the member has *)
    mpl_len : List.length Ns = im_nn Mm
    (** Each at the member's non-uniform telescope at [Us] *)
  ; mpl_typed : forall j N T, List.nth_error Ns j = Some N ->
      List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T -> Γ ⊢ N : T
    (** The type former at [Rs] is the member's type at [Us] and [Ns] *)
  ; mpl_eq : exists i, Γ ⊢ apps (a_ind pc k) Rs ≈ ind_mty p D m Us Ns : Typeω@i }.

(** The uniform arguments of a member's type at typed uniform parameters
    are typed at its type former's uniform telescope. *)
Lemma im_pre_typed : forall Γ p D m Mm pc k Dq Us,
    ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm -> im_ref p m Mm = (pc, k) ->
    ind_lookup gc_deps gc_stack pc = Some Dq ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊢ U : T) ->
    List.length (im_pre Mm Us) = ind_nu Dq /\
    forall j N T, List.nth_error (im_pre Mm Us) j = Some N ->
      List.nth_error (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) j = Some T -> Γ ⊢ N : T.
Proof.
  intros * HΓ Hl Hm Hr Hlq HUl HUs.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hlq) as [HDq Hcq].
  unfold im_ref, im_pre in *; destruct (im_head Mm) as [pm | qc k' Is vm] eqn:Hh; injection Hr as <- <-.
  - assert (Dq = D) as -> by congruence; split; [ exact HUl | exact HUs ].
  - destruct (dt_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D' & Mk' & Hl' & _ & _ & HIl & _).
    assert (D' = Dq) as -> by congruence.
    pose proof (wf_uparams_sub _ _ _ _ _ HD HΓ HUl HUs) as Hσ.
    split; [ rewrite List.length_map; exact HIl |].
    intros j N T HN HT.
    rewrite <- (tele_insts_sub (ind_uparams Dq) 0 Id Id (sb_of_list Id Us) Is (dc_ass _ Hcq) (dc_uparams _ Hcq)
                  ltac:(intros; lia)) in HT.
    apply nth_error_map_inv in HN as (I & HI & ->); apply nth_error_map_inv in HT as (T0 & HT0 & ->).
    exact (sub_preserves_exp _ _ _ _ _ _ _ (dt_view_is _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ Hm Hh Hlq HI HT0) Hσ).
Qed.

(** The group of a member's type former is filed, and has that member. *)
Lemma im_ref_lookup : forall Γ p D m Mm pc k,
    ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm -> im_ref p m Mm = (pc, k) ->
    exists Dq, ind_lookup gc_deps gc_stack pc = Some Dq.
Proof.
  intros * HΓ Hl Hm Hr.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  unfold im_ref in Hr; destruct (im_head Mm) as [pm | qc k1 Is vm] eqn:Hh; injection Hr as <- <-; [ eauto |].
  destruct (dt_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D' & Mk' & Hl' & _); eauto.
Qed.

Lemma im_ref_member : forall Γ p D m Mm pc k Dq,
    ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm -> im_ref p m Mm = (pc, k) ->
    ind_lookup gc_deps gc_stack pc = Some Dq -> exists Mk, ind_member Dq k = Some Mk.
Proof.
  intros * HΓ Hl Hm Hr Hlq.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  unfold im_ref in Hr; destruct (im_head Mm) as [pm | qc k1 Is vm] eqn:Hh; injection Hr as <- <-.
  - assert (Dq = D) as -> by congruence; eauto.
  - destruct (dt_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D' & Mk' & Hl' & Hk' & _).
    assert (D' = Dq) as -> by congruence; eauto.
Qed.

(** A member has as many non-uniform parameters as the member of its type
    former. *)
Lemma im_ref_nn : forall Γ p D m Mm pc k Dq Mk,
    ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm -> im_ref p m Mm = (pc, k) ->
    ind_lookup gc_deps gc_stack pc = Some Dq -> ind_member Dq k = Some Mk -> im_nn Mm = im_nn Mk.
Proof.
  intros * HΓ Hl Hm Hr Hlq Hk.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  unfold im_ref in Hr; destruct (im_head Mm) as [pm | qc k1 Is vm] eqn:Hh; injection Hr as <- <-.
  - assert (Dq = D) as -> by congruence; congruence.
  - destruct (dt_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D' & Mk' & Hl' & Hk' & _ & _ & _ & Hself & _).
    assert (D' = Dq) as -> by congruence; assert (Mk' = Mk) as -> by congruence.
    pose proof (dt_view_nparams _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ _ Hm Hh Hlq Hk Hself Hm) as HNeq.
    unfold im_nn; rewrite (ext_eq_length _ _ _ _ _ HNeq), length_tele_sub; reflexivity.
Qed.

(** The parameters of a member's type former at typed parameters of the
    member are typed. *)
Lemma im_pre_params_typed : forall Γ p D m Mm pc k Dq Mk Us Ns,
    ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm -> im_ref p m Mm = (pc, k) ->
    ind_lookup gc_deps gc_stack pc = Some Dq -> ind_member Dq k = Some Mk ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊢ U : T) ->
    List.length Ns = im_nn Mm ->
    (forall j N T, List.nth_error Ns j = Some N ->
       List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T -> Γ ⊢ N : T) ->
    List.length (im_pre Mm Us ++ Ns) = im_np Dq Mk /\
    forall j P T, List.nth_error (im_pre Mm Us ++ Ns) j = Some P ->
      List.nth_error (tele_insts (im_params Dq Mk) Id (im_pre Mm Us ++ Ns)) j = Some T -> Γ ⊢ P : T.
Proof.
  intros * HΓ Hl Hm Hr Hlq Hk HUl HUs HNl HNs.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hlq) as [HDq Hcq].
  pose proof (im_ref_nn _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hr Hlq Hk) as Hnn.
  destruct (im_pre_typed _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hr Hlq HUl HUs) as [HPl _].
  split; [ rewrite List.length_app, HPl, HNl, Hnn; unfold im_np; lia |].
  unfold im_ref, im_pre in *; destruct (im_head Mm) as [pm | qc k' Is vm] eqn:Hh; injection Hr as <- <-.
  - assert (Dq = D) as -> by congruence; assert (Mk = Mm) as -> by congruence.
    exact (params_typed_join _ _ D Hc _ _ _ Us Ns Hm HUl HUs HNs).
  - destruct (dt_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D' & Mk' & Hl' & Hk' & _ & HIl & _ & Hself & _).
    assert (D' = Dq) as -> by congruence; assert (Mk' = Mk) as -> by congruence.
    exact (proj2 (view_params_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg Hl HDs HD Hc Hcq Hm Hh Hlq Hk Hself HIl HΓ HUl HUs HNl HNs)).
Qed.

Lemma mty_params_conv : forall Γ p D m Mm pc k Dq Mk Us Rs,
    ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm -> im_ref p m Mm = (pc, k) ->
    ind_lookup gc_deps gc_stack pc = Some Dq -> ind_member Dq k = Some Mk ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊢ U : T) ->
    List.length Rs = im_np Dq Mk ->
    (forall j R T, List.nth_error Rs j = Some R -> List.nth_error (tele_insts (im_params Dq Mk) Id Rs) j = Some T -> Γ ⊢ R : T) ->
    (forall j N R T, List.nth_error (im_pre Mm Us) j = Some N -> List.nth_error Rs j = Some R ->
       List.nth_error (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) j = Some T -> Γ ⊢ N ≈ R : T) ->
    mty_params_link Γ p D m Mm Us (List.skipn (ind_nu Dq) Rs) pc k Rs.
Proof.
  intros * HΓ Hl Hm Hr Hlq Hk HUl HUs HRl HRs HPR.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hlq) as [HDq Hcq].
  destruct (im_pre_typed _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hr Hlq HUl HUs) as [HPl HPt].
  set (Ps := im_pre Mm Us) in *.
  set (Ns := List.skipn (ind_nu Dq) Rs).
  assert (HRl' : List.length (List.firstn (ind_nu Dq) Rs) = ind_nu Dq)
    by (rewrite List.length_firstn; unfold im_np in HRl; lia).
  destruct (params_typed_split _ _ Dq Hcq _ _ _ Rs Hk HRl HRs) as [HRu HRn].
  (** The uniform arguments as a substitution, equal to the first [Rs]. *)
  assert (Hσσ : Γ ⊢ˢ sb_of_list Id Ps ≈ sb_of_list Id (List.firstn (ind_nu Dq) Rs) : ind_uparams Dq ++ Γ).
  { eapply wf_sub_eq_of_list; [ exact (dc_ass _ Hcq) | exact (wf_uparams_app _ _ _ HDq Hcq _ HΓ)
                              | apply wf_sub_eq_refl, wf_sub_id, HΓ | rewrite HPl; reflexivity | rewrite HRl'; reflexivity |].
    intros j N R T HN HR HT; apply (HPR j); [ exact HN | | exact HT ].
    rewrite <- (List.firstn_skipn (ind_nu Dq) Rs), List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HR. }
  (** The rest of [Rs], at the type former's non-uniform telescope at the
      uniform arguments. *)
  assert (HNl : List.length Ns = List.length (im_nparams Mk))
    by (unfold Ns; rewrite List.length_skipn, HRl; unfold im_np, im_nn; lia).
  assert (HPΓ : ⊢ (im_nparams Mk ++ ind_uparams Dq ++ Γ)%list)
    by (rewrite List.app_assoc; exact (wf_params_app _ _ _ HDq Hcq _ _ _ Hk HΓ)).
  assert (HNp : forall j N T, List.nth_error Ns j = Some N ->
             List.nth_error (tele_insts (im_nparams Mk) (sb_of_list Id Ps) Ns) j = Some T -> Γ ⊢ N : T).
  { intros j N T HN HT.
    destruct (nth_error_lt_some (tele_insts (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu Dq) Rs)) Ns) j) as [T' HT'].
    { rewrite length_tele_insts by (eapply decl_closed_nparams_ass; eassumption).
      assert (j < List.length Ns) by (apply List.nth_error_Some; congruence); lia. }
    destruct (tele_insts_cong _ _ _ _ _ _ _ (decl_closed_nparams_ass _ Hcq _ _ Hk) HPΓ (wf_sub_eq_sym _ _ _ _ _ _ Hσσ) HNl HNl
                ltac:(intros j1 N1 N1' T1 HN1 HN1' HT1; rewrite HN1 in HN1'; injection HN1' as <-;
                      apply wf_exp_eq_refl; exact (HRn _ _ _ HN1 HT1)) _ _ _ HT' HT) as [i Hi].
    eapply wf_conv'; [ exact (HRn _ _ _ HN HT') | exact Hi ]. }
  (** The type former at the uniform arguments and the rest, equal to it
      at [Rs]. *)
  assert (Hkl : k < ind_ndecl Dq).
  { unfold im_ref in Hr; destruct (im_head Mm) as [pm | qc k' Is vm] eqn:Hh; injection Hr as <- <-.
    - assert (Dq = D) as -> by congruence; assert (Mk = Mm) as -> by congruence; eapply member_decl_lt; eassumption.
    - destruct (dt_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D' & Mk' & Hl' & _ & Hlt & _); congruence. }
  assert (HLc : List.length (Ps ++ Ns) = im_np Dq Mk) by (rewrite List.length_app, HPl, HNl; unfold im_np, im_nn; lia).
  pose proof (params_typed_join _ _ Dq Hcq _ _ _ Ps Ns Hk HPl HPt HNp) as HLt.
  assert (HLR : forall j N R T, List.nth_error (Ps ++ Ns) j = Some N -> List.nth_error Rs j = Some R ->
             List.nth_error (tele_insts (im_params Dq Mk) Id (Ps ++ Ns)) j = Some T -> Γ ⊢ N ≈ R : T).
  { intros j N R T HN HR HT; unfold im_params in HT.
    rewrite tele_insts_app in HT by (try exact (dc_ass _ Hcq); exact HPl).
    assert (Hl1 : List.length (tele_insts (ind_uparams Dq) Id Ps) = ind_nu Dq)
      by (rewrite length_tele_insts by exact (dc_ass _ Hcq); rewrite HPl; unfold ind_nu; lia).
    destruct (Nat.lt_ge_cases j (ind_nu Dq)) as [Hj | Hj].
    - rewrite List.nth_error_app1 in HN, HT by lia; exact (HPR _ _ _ _ HN HR HT).
    - rewrite List.nth_error_app2 in HN, HT by lia; rewrite HPl in HN; rewrite Hl1 in HT.
      assert (HR' : List.nth_error Ns (j - ind_nu Dq) = Some R)
        by (unfold Ns; rewrite List.nth_error_skipn; replace (ind_nu Dq + (j - ind_nu Dq)) with j by lia; exact HR).
      rewrite HN in HR'; injection HR' as <-; apply wf_exp_eq_refl; exact (HNp _ _ _ HN HT). }
  destruct (ind_apps_conv_large _ _ _ _ _ _ _ _ _ Hg HDs Hlq Hk Hkl HΓ HLc HRl HLt HRs HLR) as (i & _ & _ & Heq).
  assert (Hmty : ind_mty p D m Us Ns = apps (a_ind pc k) (Ps ++ Ns))
    by (unfold ind_mty; rewrite Hm; unfold im_ty_at; rewrite Hr; reflexivity).
  clear HLR HLt HRu.
  (** At a view, its own non-uniform telescope is its container's at the
      view's instance. *)
  unfold Ps in *; clear Ps; unfold im_ref in Hr; destruct (im_head Mm) as [pm | qc k' Is vm] eqn:Hh; injection Hr as <- <-.
  - assert (Dq = D) as -> by congruence; assert (Mk = Mm) as -> by congruence.
    assert (Epre : im_pre Mm Us = Us) by (unfold im_pre; rewrite Hh; reflexivity); rewrite Epre in *.
    constructor; [ rewrite HNl; reflexivity | exact HNp | exists i; rewrite Hmty; symmetry; exact Heq ].
  - destruct (dt_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D' & Mk' & Hl' & Hk' & _ & HIl & _ & Hself & _).
    assert (D' = Dq) as -> by congruence; assert (Mk' = Mk) as -> by congruence.
    assert (Epre : im_pre Mm Us = List.map (fun I => I[sb_of_list Id Us]) Is) by (unfold im_pre; rewrite Hh; reflexivity);
      rewrite Epre in *.
    pose proof (dt_view_nparams _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ _ Hm Hh Hlq Hk Hself Hm) as HNeq.
    pose proof (wf_uparams_sub _ _ _ _ _ HD HΓ HUl HUs) as Hσ.
    pose proof (sub_preserves_ext _ _ _ _ _ _ _ HNeq Hσ) as HNeq'.
    rewrite (nparams_sub Dq k' Mk Is (sb_of_list Id Us) Hcq Hk HIl) in HNeq'.
    constructor.
    + rewrite HNl; unfold im_nn; rewrite (ext_eq_length _ _ _ _ _ HNeq), length_tele_sub; reflexivity.
    + intros j N T HN HT.
      rewrite (tele_insts_sb_eq _ (sb_of_list Id Us) (sb_of_list Id Us ⨟ Id)) in HT by (intro; symmetry; apply sb_compose_id_right).
      rewrite <- tele_insts_tele_sub in HT.
      eapply (tele_insts_conv_rev _ _ _ _ _ _ HNeq');
        [ apply tele_ass_sub; exact (dt_nparams_ass _ _ _ HD _ _ Hm)
        | apply tele_ass_sub; exact (dt_nparams_ass _ _ _ HDq _ _ Hk)
        | rewrite length_tele_sub; exact HNl | | exact HN | exact HT ].
      intros k1 N1 T1 HN1 HT1; apply (HNp _ _ _ HN1).
      rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is))) in HT1
        by apply sb_compose_id_right.
      exact HT1.
    + exists i; rewrite Hmty; symmetry; exact Heq.
Qed.

(** Equal terms at the instances of a telescope are equal at those of an
    equal one. *)
Lemma tele_insts_eq_conv_rev : forall Γ Δ Δ' Ms Ms',
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Δ ≈ Δ' -> tele_ass Δ -> tele_ass Δ' ->
    List.length Ms = List.length Δ' -> List.length Ms' = List.length Δ' ->
    (forall j N N' T, List.nth_error Ms j = Some N -> List.nth_error Ms' j = Some N' ->
       List.nth_error (tele_insts Δ' Id Ms) j = Some T -> Γ ⊢ N ≈ N' : T) ->
    forall j N N' T, List.nth_error Ms j = Some N -> List.nth_error Ms' j = Some N' ->
      List.nth_error (tele_insts Δ Id Ms) j = Some T -> Γ ⊢ N ≈ N' : T.
Proof.
  intros * HΔ Ha Ha' Hl Hl' HMs.
  assert (HΓ : ⊢ Γ) by (eapply ctx_app_wf_tail, ext_eq_ctx_left; exact HΔ).
  assert (Hσ : Γ ⊢ˢ sb_of_list Id Ms ≈ sb_of_list Id Ms' : Δ' ++ Γ)
    by (eapply wf_sub_eq_of_list; [ exact Ha' | exact (ext_eq_ctx_right _ _ _ _ _ HΔ) | apply wf_sub_eq_refl, wf_sub_id, HΓ
                                  | exact Hl | exact Hl' | exact HMs ]).
  pose proof (wf_sub_eq_compose_right _ _ _ _ _ _ _ _ (ctxsub_ext _ _ _ _ _ HΔ Ha) Hσ) as Hσ'.
  eapply wf_sub_eq_sb_eq in Hσ'; [| intro; apply sb_compose_id_left | intro; apply sb_compose_id_left ].
  eapply wf_sub_eq_of_list_inv; [ exact Ha | rewrite (ext_eq_length _ _ _ _ _ HΔ); exact Hl
                                | rewrite (ext_eq_length _ _ _ _ _ HΔ); exact Hl' | exact Hσ' ].
Qed.

(** Equal types of a member at the same uniform parameters have equal
    non-uniform parameters. *)
Lemma mty_params_inj : forall Γ p D m Mm Us Ns Ns' i,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊢ U : T) ->
    List.length Ns = im_nn Mm -> List.length Ns' = im_nn Mm ->
    (forall j N T, List.nth_error Ns j = Some N ->
       List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T -> Γ ⊢ N : T) ->
    (forall j N T, List.nth_error Ns' j = Some N ->
       List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns') j = Some T -> Γ ⊢ N : T) ->
    Γ ⊢ ind_mty p D m Us Ns ≈ ind_mty p D m Us Ns' : Typeω@i ->
    forall j N N' T, List.nth_error Ns j = Some N -> List.nth_error Ns' j = Some N' ->
      List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T -> Γ ⊢ N ≈ N' : T.
Proof.
  intros * Hl Hm HUl HUs HNl HNl' HNs HNs' Heq.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  unfold ind_mty in Heq; rewrite Hm in Heq; unfold im_ty_at, im_ref, im_pre in Heq.
  destruct (im_head Mm) as [pm | qc k' Is vm] eqn:Hh; cbn [fst snd] in Heq.
  - pose proof (params_typed_join _ _ D Hc _ _ _ Us Ns Hm HUl HUs HNs) as HX.
    pose proof (params_typed_join _ _ D Hc _ _ _ Us Ns' Hm HUl HUs HNs') as HX'.
    assert (HXl : List.length (Us ++ Ns) = im_np D Mm) by (rewrite List.length_app, HUl, HNl; unfold im_np; lia).
    assert (HXl' : List.length (Us ++ Ns') = im_np D Mm) by (rewrite List.length_app, HUl, HNl'; unfold im_np; lia).
    destruct (exp_eq_ind_apps_inv _ _ _ _ _ _ _ _ Hl Hm Heq HXl HXl' HX HX') as [_ HE].
    destruct (params_eq_split _ D _ _ _ _ Hc Hm HXl HXl' HE) as [_ HEn].
    rewrite !firstn_app_len, !skipn_app_len in HEn by exact HUl; exact HEn.
  - destruct (dt_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (Dq & Mk & Hlq & Hk & _ & HIl & _ & Hself & _).
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hlq) as [HDq Hcq].
    destruct (view_params_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg Hl HDs HD Hc Hcq Hm Hh Hlq Hk Hself HIl HΓ HUl HUs HNl HNs)
      as [HNk HX].
    destruct (view_params_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg Hl HDs HD Hc Hcq Hm Hh Hlq Hk Hself HIl HΓ HUl HUs HNl' HNs')
      as [_ HX'].
    set (Ps := List.map (fun I => I[sb_of_list Id Us]) Is) in *.
    assert (HPl : List.length Ps = ind_nu Dq) by (unfold Ps; rewrite List.length_map; exact HIl).
    assert (HXl : List.length (Ps ++ Ns) = im_np Dq Mk) by (rewrite List.length_app, HPl, HNk; unfold im_np; lia).
    assert (HXl' : List.length (Ps ++ Ns') = im_np Dq Mk) by (rewrite List.length_app, HPl, HNl', <- HNl, HNk; unfold im_np; lia).
    destruct (exp_eq_ind_apps_inv _ _ _ _ _ _ _ _ Hlq Hk Heq HXl HXl' HX HX') as [_ HE].
    destruct (params_eq_split _ Dq _ _ _ _ Hcq Hk HXl HXl' HE) as [_ HEn].
    rewrite !firstn_app_len, !skipn_app_len in HEn by exact HPl.
    pose proof (dt_view_nparams _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ _ Hm Hh Hlq Hk Hself Hm) as HNeq.
    pose proof (wf_uparams_sub _ _ _ _ _ HD HΓ HUl HUs) as Hσ.
    pose proof (sub_preserves_ext _ _ _ _ _ _ _ HNeq Hσ) as HNeq'.
    rewrite (nparams_sub Dq k' Mk Is (sb_of_list Id Us) Hcq Hk HIl) in HNeq'; fold Ps in HNeq'.
    intros j N N' T HN HN' HT.
    rewrite (tele_insts_sb_eq _ (sb_of_list Id Us) (sb_of_list Id Us ⨟ Id)) in HT by (intro; symmetry; apply sb_compose_id_right).
    rewrite <- tele_insts_tele_sub in HT.
    eapply (tele_insts_eq_conv_rev _ _ _ _ _ HNeq');
      [ apply tele_ass_sub; exact (dt_nparams_ass _ _ _ HD _ _ Hm)
      | apply tele_ass_sub; exact (dt_nparams_ass _ _ _ HDq _ _ Hk)
      | rewrite length_tele_sub; unfold im_nn in HNk; exact HNk
      | rewrite length_tele_sub; unfold im_nn in HNk; rewrite HNl', <- HNl; exact HNk | | exact HN | exact HN' | exact HT ].
    intros k1 N1 N1' T1 HN1 HN1' HT1; apply (HEn _ _ _ _ HN1 HN1').
    rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (sb_of_list Id Ps)) in HT1 by apply sb_compose_id_right.
    exact HT1.
Qed.

(** The instances of an entry of a telescope at terms equal up to it are
    equal. *)
Lemma tele_insts_cong_upto : forall Δ Γ0 Γ σ σ' Ms Ms',
    tele_ass Δ -> ⊢ (Δ ++ Γ0)%list -> Γ ⊢ˢ σ ≈ σ' : Γ0 ->
    forall j T T', List.nth_error (tele_insts Δ σ Ms) j = Some T -> List.nth_error (tele_insts Δ σ' Ms') j = Some T' ->
      (forall j' N N' T0, j' < j -> List.nth_error Ms j' = Some N -> List.nth_error Ms' j' = Some N' ->
         List.nth_error (tele_insts Δ σ Ms) j' = Some T0 -> Γ ⊢ N ≈ N' : T0) ->
      exists i, Γ ⊢ T ≈ T' : Typeω@i.
Proof.
  induction Δ as [| e Δ IH] using List.rev_ind; intros * Hass HΔ Hσ j T T' HT HT' HMs.
  - unfold tele_insts in HT; cbn in HT; destruct Ms, j; discriminate.
  - unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A0 ->] _].
    destruct Ms as [| M0 Ms]; [ unfold tele_insts in HT; rewrite List.rev_app_distr in HT; cbn in HT; destruct j; discriminate |].
    destruct Ms' as [| M0' Ms']; [ unfold tele_insts in HT'; rewrite List.rev_app_distr in HT'; cbn in HT'; destruct j; discriminate |].
    rewrite tele_insts_snoc in HT, HT', HMs.
    rewrite <- List.app_assoc in HΔ; cbn [List.app] in HΔ.
    destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ0 [k HA0]].
    assert (HAA : Γ ⊢ A0[σ] ≈ A0[σ'] : Typeω@k) by (eapply sub_eq_preserves_typ; [ exact HA0 | exact Hσ ]).
    destruct j as [| j]; cbn in HT, HT'.
    + injection HT as <-; injection HT' as <-; exists k; exact HAA.
    + assert (HMM : Γ ⊢ M0 ≈ M0' : A0[σ]) by (apply (HMs 0); [ lia | reflexivity | reflexivity | reflexivity ]).
      eapply IH; [ exact Hass | exact HΔ | | exact HT | exact HT' |].
      * eapply wf_sub_eq_extend; [ exact Hσ | exact HA0 | gen_presups; eassumption | | exact HMM ].
        eapply wf_conv'; [ gen_presups; eassumption | exact HAA ].
      * intros j' N N' T0 Hj' HN HN' HT0; apply (HMs (S j')); [ lia | exact HN | exact HN' | exact HT0 ].
Qed.

(** Terms of a closed telescope whose weakenings are equal are equal. *)
Lemma tele_eq_strengthen : forall Δ Γ A Δt Xs Ys,
    tele_ass Δ -> ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list -> tele_ass Δt -> ⊢ (Δt ++ Δ ++ Γ)%list ->
    List.length Xs = List.length Δt -> List.length Ys = List.length Δt ->
    (forall j N T, List.nth_error Xs j = Some N -> List.nth_error (tele_insts Δt Id Xs) j = Some T -> (Δ ++ Γ)%list ⊢ N : T) ->
    (forall j N T, List.nth_error Ys j = Some N -> List.nth_error (tele_insts Δt Id Ys) j = Some T -> (Δ ++ Γ)%list ⊢ N : T) ->
    (forall j N N' T, List.nth_error Xs j = Some N -> List.nth_error Ys j = Some N' ->
       List.nth_error (tele_insts Δt Id Xs) j = Some T ->
       (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ N[wk_qn (length Δ) ↑]ʷ ≈ N'[wk_qn (length Δ) ↑]ʷ : T[wk_qn (length Δ) ↑]ʷ) ->
    forall j N N' T, List.nth_error Xs j = Some N -> List.nth_error Ys j = Some N' ->
      List.nth_error (tele_insts Δt Id Xs) j = Some T -> (Δ ++ Γ)%list ⊢ N ≈ N' : T.
Proof.
  intros * Hass HΓf Hat HΔt HXl HYl HXs HYs HL j; induction j as [j IH] using lt_wf_ind; intros N N' T HN HN' HT.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (eapply ctx_app_wf_tail; exact HΔt).
  destruct (nth_error_lt_some (tele_insts Δt Id Ys) j) as [T' HT'].
  { rewrite length_tele_insts by exact Hat.
    assert (j < List.length Ys) by (apply List.nth_error_Some; congruence); lia. }
  destruct (tele_insts_cong_upto _ _ _ _ _ _ _ Hat HΔt (wf_sub_eq_refl _ _ _ _ _ (wf_sub_id _ _ _ HΓs)) _ _ _ HT HT')
    as [i Hi]; [ intros j' N1 N1' T1 Hj' HN1 HN1' HT1; exact (IH j' Hj' _ _ _ HN1 HN1' HT1) |].
  eapply exp_eq_strengthen; [ exact Hass | exact HΓf | exact (HXs _ _ _ HN HT) | | exact (HL _ _ _ _ HN HN' HT) ].
  eapply wf_conv'; [ exact (HYs _ _ _ HN' HT') | symmetry; exact Hi ].
Qed.


(** Short judgments hold, weakened, in the long context. *)
Lemma short_wk_exp : forall Δ Γ A M T,
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    (Δ ++ Γ)%list ⊢ M : T ->
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ M[wk_qn (length Δ) ↑]ʷ : T[wk_qn (length Δ) ↑]ʷ.
Proof.
  intros * HΓf HM; eapply wk_preserves_exp; [ exact HM | apply wf_wk_qn; [ gen_presups; assumption | exact HΓf ] ].
Qed.

Lemma short_wk_exp_eq : forall Δ Γ A M M' T,
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    (Δ ++ Γ)%list ⊢ M ≈ M' : T ->
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ M[wk_qn (length Δ) ↑]ʷ ≈ M'[wk_qn (length Δ) ↑]ʷ : T[wk_qn (length Δ) ↑]ʷ.
Proof.
  intros * HΓf HM; eapply wk_preserves_exp_eq; [ exact HM | apply wf_wk_qn; [ gen_presups; assumption | exact HΓf ] ].
Qed.

(** ** The Induction on Normal Forms

    What is proved of a neutral: it has a short type whose weakening is below
    the long one. *)
#[warnings="-cannot-define-projection"]
Record short_typ (Γ : ctx) (A : typ) (Δ : ctx) (C : typ) (M : exp) : Prop := mk_short_typ
  { sty_typ : typ
  ; sty_lvl : nat
  ; sty_exp : (Δ ++ Γ)%list ⊢ M : sty_typ
  ; sty_wf : (Δ ++ Γ)%list ⊢ sty_typ : Typeω@sty_lvl
  ; sty_sub : (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ sty_typ[wk_qn (length Δ) ↑]ʷ ⊆ C }.

Definition exp_str (Γ : ctx) (A : typ) (M : exp) : Prop :=
  forall Δ C,
    tele_ass Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    ⊢ (Δ ++ Γ)%list ->
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ M[wk_qn (length Δ) ↑]ʷ : C ->
    short_typ Γ A Δ C M.

Definition ne_str (Γ : ctx) (A : typ) (u : ne) : Prop := exp_str Γ A u.

(** What is proved of a normal form: typed long at a weakened short type, it
    is typed short at that type. *)
Definition nf_str_exp (Γ : ctx) (A : typ) (W : exp) : Prop :=
  forall Δ T i,
    tele_ass Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    (Δ ++ Γ)%list ⊢ T : Typeω@i ->
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ W[wk_qn (length Δ) ↑]ʷ : T[wk_qn (length Δ) ↑]ʷ ->
    (Δ ++ Γ)%list ⊢ W : T.

(** A term strengthened with a short type is strengthened at any short type
    of which the long one is a weakening. *)
Lemma exp_str_at : forall Γ A M, exp_str Γ A M -> nf_str_exp Γ A M.
Proof.
  intros * Hu Δ T i Hass HΓf HT HW.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
  destruct (Hu _ _ Hass HΓf HΓs HW) as [T0 j HuT HT0 Hs].
  eapply wf_exp_subtyp; [ exact HuT | exact HT |].
  eapply subtyp_strengthen'; eassumption.
Qed.

(** An application: the head's short type is a [Π] ([typ_pi_shape_strengthen]),
    whose domain the argument is checked against. *)
Lemma app_str : forall Γ A M w, exp_str Γ A M -> nf_str_exp Γ A w -> exp_str Γ A (a_app M w).
Proof.
  intros Γ A u w IHu IHw Δ C Hass HΓf HΓs HW; cbn [exp_wk] in HW.
  destruct (wf_app_inversion HW) as (X & Y & Hu & Hw & HsC).
  destruct (IHu _ _ Hass HΓf HΓs Hu) as [T0 j0 HuT HT0 Hs0].
  destruct (typ_pi_shape_strengthen _ _ _ _ _ _ _ Hass HΓf HT0 Hs0) as (C' & D' & HCD).
  assert (HTCD : (Δ ++ Γ)%list ⊢ T0 ≈ (Πⁿ C' D' : exp) : Typeω@j0) by (eapply soundness_ty'; eassumption).
  cbn [nf_to_exp] in HTCD.
  assert (HCDt : (Δ ++ Γ)%list ⊢ Π C' D' : Typeω@j0) by (gen_presups; assumption).
  destruct (wf_pi_inversion' HCDt) as [HC HD].
  pose proof (short_wk_exp_eq _ _ _ _ _ _ HΓf HTCD) as HTCDf; cbn [exp_wk] in HTCDf.
  assert (Hs' : (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ Π (C' : exp)[wk_qn (length Δ) ↑]ʷ (D' : exp)[wk_q (wk_qn (length Δ) ↑)]ʷ ⊆ Π X Y)
    by (etransitivity; [ eapply wf_subtyp_refl'; symmetry; exact HTCDf | exact Hs0 ]).
  destruct (subtyp_pi_inv _ _ _ _ _ Hs') as [[k HCX] HDY].
  pose proof (short_wk_exp _ _ _ _ _ HΓf HC) as HCf.
  assert (Hwf : (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ w[wk_qn (length Δ) ↑]ʷ : (C' : exp)[wk_qn (length Δ) ↑]ʷ)
    by (eapply wf_exp_subtyp; [ exact Hw | exact HCf | eapply wf_subtyp_refl'; symmetry; exact HCX ]).
  assert (Hws : (Δ ++ Γ)%list ⊢ w : C') by (eapply (IHw _ _ j0); [ exact Hass | exact HΓf | exact HC | exact Hwf ]).
  assert (Hus : (Δ ++ Γ)%list ⊢ u : Π C' D')
    by (eapply wf_exp_subtyp; [ exact HuT | exact HCDt | eapply wf_subtyp_refl'; exact HTCD ]).
  apply (mk_short_typ _ _ _ _ _ ((D' : exp)[Id,,w]) j0).
  - eapply wf_app; eassumption.
  - eapply (exp_sub_single _ _ _ _ Typeω@j0); [ exact HD | exact Hws ].
  - rewrite exp_wk_sub_id_extend; etransitivity; [| exact HsC ].
    eapply sub_preserves_subtyp; [ exact HDY | eapply wf_sub_single; [ exact HCf | exact Hwf ] ].
Qed.

Lemma apps_str : forall Γ A Xs M, List.Forall (nf_str_exp Γ A) Xs -> exp_str Γ A M -> exp_str Γ A (apps M Xs).
Proof.
  intros Γ A Xs; induction Xs as [| X Xs IH]; intros M HXs HM; cbn [apps_exp]; [ exact HM |].
  inversion HXs as [| ? ? HX HXs']; subst.
  apply IH; [ exact HXs' | exact (app_str _ _ _ _ HM HX) ].
Qed.

(** The type former and the constructors: typed at their closed types in
    every context. *)
Lemma ind_str : forall Γ A p k, exp_str Γ A (a_ind p k).
Proof.
  intros * Δ C Hass HΓf HΓs HW; cbn [exp_wk] in HW.
  destruct (wf_ind_inversion HW) as [D Mk Hl Hk Hlt Hs].
  destruct (decl_of_lookup _ _ _ _ _ HΓs Hl) as [HD Hc].
  destruct (ind_ty_typed _ _ _ _ _ _ HD Hc Hk HΓs) as [j Hj].
  apply (mk_short_typ _ _ _ _ _ (ind_ty D Mk) j); [ eapply wf_ind; eassumption | exact Hj |].
  rewrite (ind_ty_wk D k Mk) by assumption; exact Hs.
Qed.

(** A constructor of any member, at its closed type. *)
Lemma wf_con_closed : forall Γ p D k Mk c gs,
    ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    Γ ⊢ a_con p k c : con_ty p D k Mk gs.
Proof.
  intros * HΓ Hl Hk Hcon.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (con_ty_typed0 _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hcon) as [j0 Hj0].
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hk (cons_lookup_in _ _ _ Hcon) gs nil (eq_sym (List.app_nil_r gs)))
    as (HΨ0 & _ & _).
  eapply wf_con_of_lookup; eassumption.
Qed.

Lemma con_str : forall Γ A p k c, exp_str Γ A (a_con p k c).
Proof.
  intros * Δ C Hass HΓf HΓs HW; cbn [exp_wk] in HW.
  destruct (wf_con_inversion HW) as [D Mk gs Hl Hk Hcon Hs].
  destruct (decl_of_lookup _ _ _ _ _ HΓs Hl) as [HD Hc].
  destruct (con_ty_typed _ _ _ _ _ _ _ _ _ (ctx_wf_gctx _ _ _ HΓs) (decls_of_ctx _ _ _ HΓs) Hl Hk Hcon HΓs) as [j Hj].
  apply (mk_short_typ _ _ _ _ _ (con_ty p D k Mk gs) j); [ eapply wf_con_closed; eassumption | exact Hj |].
  rewrite (con_ty_wk p D k Mk c gs) by assumption; exact Hs.
Qed.

(** A neutral typed at [Level@n] in the long context is in the short one. *)
Lemma ne_str_level : forall Γ A Δ n (u : ne),
    ne_str Γ A u ->
    tele_ass Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    ⊢ (Δ ++ Γ)%list ->
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ (u : exp)[wk_qn (length Δ) ↑]ʷ : Level@n ->
    (Δ ++ Γ)%list ⊢ u : Level@n.
Proof.
  intros * Hu Hass HΓf HΓs H.
  destruct (Hu _ _ Hass HΓf HΓs H) as [T i HuT HT Hs].
  eapply wf_exp_subtyp; [ exact HuT | apply (wf_level_large (i := 0)), HΓs |].
  eapply subtyp_strengthen';
    [ exact Hass | exact HΓf | exact HT | apply (wf_level_large (i := 0)), HΓs | exact Hs ].
Qed.

Lemma la_wf_strengthen : forall Γ A Δ n xs,
    la_all (ne_str Γ A) xs ->
    tele_ass Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    ⊢ (Δ ++ Γ)%list ->
    List.Forall (fun p => (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ snd p : Level@n)
      (List.map (fun p => (fst p, (snd p)[wk_qn (length Δ) ↑]ʷ)) (la_to_list xs)) ->
    @la_wf gc_deps gc_stack n (Δ ++ Γ)%list xs.
Proof.
  intros Γ A Δ n xs; induction xs as [| k s u r IH]; cbn; [ intros; exact I |].
  intros [Hu Hr] Hass HΓf HΓs HF.
  inversion HF as [| ? ? Hk HF']; subst.
  split; [ eapply ne_str_level; eassumption | apply IH; assumption ].
Qed.

(** The atoms of a level expression typed at [Level@n] are. *)
Lemma lvl_exp_of_atoms : forall Γ n c xs,
    Γ ⊢ lvl_exp_of c xs : Level@n ->
    List.Forall (fun p => Γ ⊢ snd p : Level@n) xs.
Proof.
  intros * H; destruct (lvl_exp_of_inv _ _ _ _ H) as [(m & Hmn & _ & HF) | (a & -> & ->)].
  - eapply List.Forall_impl; [| exact HF ]; intros p Hp; eapply wf_exp_subtyp'; [ exact Hp | exact Hmn ].
  - repeat constructor; exact H.
Qed.

(** A weakened atom list with a single entry and no offset. *)
Lemma la_map_single : forall φ xs a,
    List.map (fun p => (fst p, (snd p)[φ]ʷ)) (la_to_list xs) = (0, a) :: nil ->
    exists s u, xs = la_cons 0 s u la_nil /\ a = (u : exp)[φ]ʷ.
Proof.
  intros φ [| k s u [| k' s' u' r]] a H; cbn in H; try discriminate.
  injection H as -> <-; do 2 eexists; split; reflexivity.
Qed.

(** A stuck eliminator, at the uniform parameters it carries: the
    scrutinee's short type is the type former the member's type is headed
    by ([typ_ind_shape_strengthen]), at parameters whose uniform ones are
    the member's uniform arguments ([tele_eq_strengthen]), so the rest are
    the member's non-uniform parameters ([mty_params_conv]), equal to the
    long ones ([mty_params_inj]); the blocks are typed short by the
    induction hypotheses. *)
Lemma elim_str : forall Γ A pc Us k Bks u,
    List.Forall (nf_str_exp Γ A) Us ->
    List.Forall (fun b => eb_ann b = None /\ nf_str_exp Γ A (eb_motive b) /\
                          List.Forall (fun br => nf_str_exp Γ A (snd br)) (eb_brs b)) Bks ->
    exp_str Γ A u ->
    exp_str Γ A (a_elim (Some pc) Us k Bks u).
Proof.
  intros * IHUs IHBs IHu Δ C Hass HΓf HΓs HW.
  rewrite exp_wk_elim in HW.
  set (φ := wk_qn (length Δ) ↑) in *.
  set (Lf := (tele_wk Δ ↑ ++ Γ ▹ A)%list) in *.
  assert (Hwk : Lf ⊢ʷ φ : (Δ ++ Γ)%list) by (apply wf_wk_qn; [ exact HΓs | exact HΓf ]).
  destruct (wf_elim_inversion HW) as [p D Mm bm Ps i Hl Hg Hm Hb HPl HPs HuL HUL HBt Hs].
  destruct Hg as [Eq | [Eq _]]; [ injection Eq as Ep; subst p | discriminate ].
  pose proof (ctx_wf_gctx _ _ _ HΓs) as Hg; pose proof (decls_of_ctx _ _ _ HΓs) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓs Hl) as [HD Hc].
  assert (HUl : List.length Us = ind_nu D)
    by (apply (f_equal (@List.length _)) in HUL; rewrite List.length_map, List.length_firstn in HUL; unfold im_np in HPl; lia).
  destruct (params_typed_split _ _ D Hc _ _ _ Ps Hm HPl HPs) as [HUtL HNtL].
  rewrite <- HUL in HUtL, HNtL, HuL, HBt.
  set (NsL := List.skipn (ind_nu D) Ps) in *.
  (** The uniform parameters, short. *)
  assert (HUt : forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T ->
             (Δ ++ Γ)%list ⊢ U : T).
  { eapply tele_insts_typed_all; [ exact (dc_ass _ Hc) | exact (wf_uparams_app _ _ _ HD Hc _ HΓs) | apply wf_sub_id, HΓs |].
    intros j U T HU HT [iT HTt].
    pose proof (proj1 (List.Forall_forall _ _) IHUs U (List.nth_error_In _ _ HU)) as IHU.
    eapply (IHU Δ T iT Hass HΓf HTt).
    apply (HUtL j); [ rewrite List.nth_error_map, HU; reflexivity |].
    rewrite <- tele_insts_closed_wk by (try exact (dc_ass _ Hc); exact (dc_uparams _ Hc)).
    rewrite List.nth_error_map, HT; reflexivity. }
  (** The scrutinee's short type: the type former the member's type is
      headed by, at parameters [PsS]. *)
  destruct (IHu _ _ Hass HΓf HΓs HuL) as [T0 j0 HuT HT0 Hs0].
  fold φ Lf in Hs0.
  destruct (im_ref pc k Mm) as [qr k'] eqn:Hr.
  assert (Emty : forall Us' Ns', ind_mty pc D k Us' Ns' = apps (a_ind qr k') (im_pre Mm Us' ++ Ns'))
    by (intros; unfold ind_mty; rewrite Hm; unfold im_ty_at; rewrite Hr; reflexivity).
  rewrite Emty in Hs0.
  destruct (typ_ind_shape_strengthen _ _ _ _ _ _ _ _ Hass HΓf HT0 Hs0) as [Rs HRs].
  destruct (typ_ind_shape _ _ _ _ _ _ HT0 HRs) as (Dq & Mk & PsS & Hlq & Hk & HSl & HSt & HTeq & _).
  destruct (decl_of_lookup _ _ _ _ _ HΓs Hlq) as [HDq Hcq].
  pose proof (short_wk_exp_eq _ _ _ _ _ _ HΓf HTeq) as HTeqL; rewrite wk_apps_ind in HTeqL; fold φ Lf in HTeqL.
  assert (HsubL : Lf ⊢ apps (a_ind qr k') (List.map (fun P => P[φ]ʷ) PsS)
                    ⊆ apps (a_ind qr k') (im_pre Mm (List.map (fun U => U[φ]ʷ) Us) ++ NsL))
    by (etransitivity; [ eapply wf_subtyp_refl'; symmetry; exact HTeqL | exact Hs0 ]).
  destruct (subtyp_ind_inv HsubL) as [kk HeqL].
  assert (Hnn : im_nn Mm = im_nn Mk).
  { unfold im_ref in Hr; destruct (im_head Mm) as [pm | qc k1 Is vm] eqn:Hh; injection Hr as <- <-.
    - assert (Dq = D) as -> by congruence; congruence.
    - destruct (dt_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D' & Mk' & Hl' & Hk' & _ & _ & _ & Hself & _).
      assert (D' = Dq) as -> by congruence; assert (Mk' = Mk) as -> by congruence.
      pose proof (dt_view_nparams _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ _ Hm Hh Hlq Hk Hself Hm) as HNeq.
      unfold im_nn; rewrite (ext_eq_length _ _ _ _ _ HNeq), length_tele_sub; reflexivity. }
  (** The long parameters, the short ones weakened, are equal. *)
  assert (HUlL : List.length (List.map (fun U => U[φ]ʷ) Us) = ind_nu D) by (rewrite List.length_map; exact HUl).
  destruct (im_pre_typed _ _ _ _ _ _ _ _ _ HΓf Hl Hm Hr Hlq HUlL HUtL) as [HPlL HPtL].
  assert (HNlL : List.length NsL = im_nn Mm) by (unfold NsL; rewrite List.length_skipn, HPl; unfold im_np; lia).
  assert (HLl : List.length (im_pre Mm (List.map (fun U => U[φ]ʷ) Us) ++ NsL) = im_np Dq Mk)
    by (rewrite List.length_app, HPlL, HNlL, Hnn; unfold im_np; lia).
  assert (HSlL : List.length (List.map (fun P => P[φ]ʷ) PsS) = im_np Dq Mk) by (rewrite List.length_map; exact HSl).
  assert (exists kt, Lf ⊢ ind_mty pc D k (List.map (fun U => U[φ]ʷ) Us) NsL : Typeω@kt) as [kt Hkt] by (gen_presups; eauto).
  rewrite Emty in Hkt.
  pose proof (wf_ind_apps_inv _ _ _ _ _ _ _ Hlq Hk Hkt HLl) as HLt.
  assert (HStL : forall j P T, List.nth_error (List.map (fun P => P[φ]ʷ) PsS) j = Some P ->
             List.nth_error (tele_insts (im_params Dq Mk) Id (List.map (fun P => P[φ]ʷ) PsS)) j = Some T -> Lf ⊢ P : T).
  { intros j P T HP HT.
    rewrite <- tele_insts_closed_wk in HT by (try (eapply decl_closed_params_ass; eassumption); eapply decl_closed_params; eassumption).
    apply nth_error_map_inv in HP as (P0 & HP0 & ->); apply nth_error_map_inv in HT as (T1 & HT1 & ->).
    eapply wk_preserves_exp; [ exact (HSt _ _ _ HP0 HT1) | exact Hwk ]. }
  destruct (exp_eq_ind_apps_inv _ _ _ _ _ _ _ _ Hlq Hk HeqL HSlL HLl HStL HLt) as [_ HPP].
  pose proof (params_eq_sym _ _ _ _ _ _ _ Hlq Hk HΓf HSlL HLl HPP) as HPP'.
  clear HPP HStL HsubL Hs0 HTeqL HRs Hkt HLt.
  (** The short uniform parameters of [PsS] are the member's uniform
      arguments. *)
  destruct (im_pre_typed _ _ _ _ _ _ _ _ _ HΓs Hl Hm Hr Hlq HUl HUt) as [HPlS HPtS].
  destruct (params_typed_split _ _ Dq Hcq _ _ _ PsS Hk HSl HSt) as [HSu HSn].
  assert (HSl' : List.length (List.firstn (ind_nu Dq) PsS) = ind_nu Dq)
    by (rewrite List.length_firstn; unfold im_np in HSl; lia).
  pose proof (im_pre_wk D k Mm Us φ Hc Hm HUl) as Epw.
  clear IHu HSn kt.
  assert (HPR : forall j N R T, List.nth_error (im_pre Mm Us) j = Some N -> List.nth_error PsS j = Some R ->
             List.nth_error (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) j = Some T -> (Δ ++ Γ)%list ⊢ N ≈ R : T).
  { intros j N R T HN HR HT.
    assert (Hj : j < ind_nu Dq) by (rewrite <- HPlS; apply List.nth_error_Some; congruence).
    assert (HR' : List.nth_error (List.firstn (ind_nu Dq) PsS) j = Some R)
      by (rewrite List.nth_error_firstn; destruct (Nat.ltb_spec j (ind_nu Dq)); [ exact HR | lia ]).
    eapply (tele_eq_strengthen _ _ _ (ind_uparams Dq)); [ exact Hass | exact HΓf | exact (dc_ass _ Hcq)
           | exact (wf_uparams_app _ _ _ HDq Hcq _ HΓs) | rewrite HPlS; reflexivity | rewrite HSl'; reflexivity
           | exact HPtS | exact HSu | | exact HN | exact HR' | exact HT ].
    clear j N R T HN HR HT Hj HR'.
    intros j N R T HN HR HT; fold φ Lf.
    assert (Hj : j < ind_nu Dq) by (rewrite <- HPlS; apply List.nth_error_Some; congruence).
    apply (HPP' j).
    - rewrite List.nth_error_app1 by lia; rewrite <- Epw, List.nth_error_map, HN; reflexivity.
    - rewrite List.nth_error_map; rewrite List.nth_error_firstn in HR; destruct (Nat.ltb_spec j (ind_nu Dq)); [| discriminate ].
      rewrite HR; reflexivity.
    - unfold im_params; rewrite tele_insts_app by (try exact (dc_ass _ Hcq); exact HPlL).
      rewrite List.nth_error_app1 by (rewrite length_tele_insts by exact (dc_ass _ Hcq); rewrite HPlL; unfold ind_nu in *; lia).
      rewrite <- Epw, <- tele_insts_closed_wk by (try exact (dc_ass _ Hcq); exact (dc_uparams _ Hcq)).
      rewrite List.nth_error_map, HT; reflexivity. }
  clear HPP' HSu HSl' HPtS HPtL HLl HSlL.
  (** So the rest of [PsS] are the member's non-uniform parameters, and the
      scrutinee is short of the member's type. *)
  destruct (mty_params_conv _ _ _ _ _ _ _ _ _ _ _ HΓs Hl Hm Hr Hlq Hk HUl HUt HSl HSt HPR) as [HNl HNt [iE HE]].
  set (NsS := List.skipn (ind_nu Dq) PsS) in *.
  assert (HuS : (Δ ++ Γ)%list ⊢ u : ind_mty pc D k Us NsS)
    by (eapply wf_conv'; [ eapply wf_conv'; [ exact HuT | exact HTeq ] | exact HE ]).
  pose proof (params_typed_join _ _ D Hc _ _ _ Us NsS Hm HUl HUt HNt) as HPsS.
  set (PsW := List.map (fun P => P[φ]ʷ) (Us ++ NsS)).
  assert (HPWl : List.length PsW = im_np D Mm) by (unfold PsW; rewrite List.length_map, List.length_app, HUl, HNl; unfold im_np; lia).
  assert (HPWt : forall j P T, List.nth_error PsW j = Some P -> List.nth_error (tele_insts (im_params D Mm) Id PsW) j = Some T -> Lf ⊢ P : T).
  { intros j P T HP HT; unfold PsW in HP, HT.
    rewrite <- tele_insts_closed_wk in HT by (try (eapply decl_closed_params_ass; eassumption); eapply decl_closed_params; eassumption).
    apply nth_error_map_inv in HP as (P0 & HP0 & ->); apply nth_error_map_inv in HT as (T1 & HT1 & ->).
    eapply wk_preserves_exp; [ exact (HPsS _ _ _ HP0 HT1) | exact Hwk ]. }
  assert (HPWu : List.firstn (ind_nu D) PsW = List.map (fun U => U[φ]ʷ) Us)
    by (unfold PsW; rewrite List.map_app, firstn_app_len by (rewrite List.length_map; exact HUl); reflexivity).
  assert (HPWn : List.skipn (ind_nu D) PsW = List.map (fun N => N[φ]ʷ) NsS)
    by (unfold PsW; rewrite List.map_app, skipn_app_len by (rewrite List.length_map; exact HUl); reflexivity).
  destruct (params_typed_split _ _ D Hc _ _ _ PsW Hm HPWl HPWt) as [_ HNWt].
  rewrite HPWu, HPWn in HNWt.
  clear HPR HSt HTeq HPsS.
  (** The long non-uniform parameters are the short ones, weakened, so
      the long motive's instance is the short one's, weakened. *)
  pose proof (short_wk_exp_eq _ _ _ _ _ _ HΓf HE) as HEL; rewrite wk_apps_ind, (ind_mty_wk pc D k Us NsS _ Hc HUl) in HEL;
    fold φ Lf in HEL.
  rewrite <- Emty in HeqL.
  assert (HmL : Lf ⊢ ind_mty pc D k (List.map (fun U => U[φ]ʷ) Us) NsL
                  ≈ ind_mty pc D k (List.map (fun U => U[φ]ʷ) Us) (List.map (fun N => N[φ]ʷ) NsS) : Typeω@(max kk iE))
    by (etransitivity; [ symmetry; eapply lift_exp_eq_max_left; exact HeqL | eapply lift_exp_eq_max_right; exact HEL ]).
  assert (HNlW : List.length (List.map (fun N => N[φ]ʷ) NsS) = im_nn Mm) by (rewrite List.length_map; exact HNl).
  pose proof (mty_params_inj _ _ _ _ _ _ _ _ _ Hl Hm HUlL HUtL HNlL HNlW HNtL HNWt HmL) as HNN.
  clear HmL HEL HeqL HE.
  assert (HPPW : forall j P P' T, List.nth_error Ps j = Some P -> List.nth_error PsW j = Some P' ->
             List.nth_error (tele_insts (im_params D Mm) Id Ps) j = Some T -> Lf ⊢ P ≈ P' : T).
  { intros j P P' T HP HP' HT.
    assert (EPs : Ps = List.map (fun U => U[φ]ʷ) Us ++ NsL) by (rewrite HUL; unfold NsL; symmetry; apply List.firstn_skipn).
    assert (EPW : PsW = List.map (fun U => U[φ]ʷ) Us ++ List.map (fun N => N[φ]ʷ) NsS) by (unfold PsW; apply List.map_app).
    rewrite EPs in HP, HT; rewrite EPW in HP'.
    unfold im_params in HT; rewrite tele_insts_app in HT by (try exact (dc_ass _ Hc); exact HUlL).
    assert (Hl1 : List.length (tele_insts (ind_uparams D) Id (List.map (fun U => U[φ]ʷ) Us)) = ind_nu D)
      by (rewrite length_tele_insts by exact (dc_ass _ Hc); rewrite HUlL; unfold ind_nu in *; lia).
    destruct (Nat.lt_ge_cases j (ind_nu D)) as [Hj | Hj].
    - rewrite List.nth_error_app1 in HP, HP', HT by lia; rewrite HP in HP'; injection HP' as <-.
      apply wf_exp_eq_refl; exact (HUtL _ _ _ HP HT).
    - rewrite List.nth_error_app2 in HP, HP', HT by lia; rewrite HUlL in HP, HP'; rewrite Hl1 in HT.
      exact (HNN _ _ _ _ HP HP' HT). }
  rewrite HUL in HuL, HBt.
  destruct (wf_elim_params_conv _ _ _ _ _ _ _ _ _ _ i Hl Hm Hb HPl HPs HPWl HPWt HPPW HuL HBt) as (_ & _ & Hmot).
  fold NsL in Hmot; rewrite HPWn in Hmot.
  clear HPPW HNN HNWt HPWt.
  rewrite <- HUL in HBt, HuL.
  clear Emty Hr Rs HSl HDq Hcq Hnn HPlL HPlS Epw HNtL HPs HPWu HPWn HPWl PsW HNlW.
  (** The blocks, short. *)
  assert (Hbw : forall j b, List.nth_error Bks j = Some b ->
             List.nth_error (blocks_wk Bks φ) j =
               Some (eb_mk (eb_nm b) (option_map (fun Z => Z[wk_qn (eb_nm b - 1) φ]ʷ) (eb_ann b)) (eb_motive b)[wk_qn (eb_nm b) φ]ʷ
                       (List.map (fun br => (fst br, (snd br)[wk_qn (snd (fst br)) φ]ʷ)) (eb_brs b))))
    by (intros j [nm oZ A0 Bs0] Hj; unfold blocks_wk; rewrite List.nth_error_map, Hj; reflexivity).
  assert (HBnm : blocks_nm_ok D Bks).
  { intros j Mj b Hj Hb0; pose proof (bt_nm _ _ _ _ _ _ _ _ HBt _ _ _ Hj (Hbw _ _ Hb0)) as H; exact H. }
  assert (HUt' : forall j Mj, ind_member D j = Some Mj -> ⊢ (elim_mctx pc D j Mj Us ++ Δ ++ Γ)%list)
    by (intros; eapply elim_mctx_wf; eassumption).
  assert (HBmot : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             (elim_mctx pc D j Mj Us ++ Δ ++ Γ)%list ⊢ eb_motive b : Typeω@i).
  { intros j Mj b Hj Hb0.
    pose proof (proj1 (List.Forall_forall _ _) IHBs b (List.nth_error_In _ _ Hb0)) as (_ & IHm & _).
    pose proof (bt_motive _ _ _ _ _ _ _ _ HBt _ _ _ Hj (Hbw _ _ Hb0)) as HmL; cbn [eb_motive] in HmL.
    rewrite (HBnm _ _ _ Hj Hb0) in HmL.
    assert (HLm : (tele_wk (elim_mctx pc D j Mj Us ++ Δ) ↑ ++ Γ ▹ A)%list
                  = (elim_mctx pc D j Mj (List.map (fun U => U[φ]ʷ) Us) ++ Lf)%list)
      by (rewrite tele_wk_app, elim_mctx_wk by assumption; unfold Lf; rewrite <- List.app_assoc; reflexivity).
    rewrite List.app_assoc.
    eapply (IHm (elim_mctx pc D j Mj Us ++ Δ) _ (S i)).
    - apply List.Forall_app; split; [ eapply elim_mctx_ass; eassumption | exact Hass ].
    - rewrite HLm; eapply blocks_mctx_wf; eassumption.
    - rewrite <- List.app_assoc; apply wf_typ; exact (HUt' _ _ Hj).
    - rewrite HLm, List.length_app, length_elim_mctx, wk_qn_plus; cbn [exp_wk]; exact HmL. }
  assert (HBl : List.length Bks = List.length (ind_members D))
    by (pose proof (bt_len _ _ _ _ _ _ _ _ HBt) as H; unfold blocks_wk in H; rewrite List.length_map in H; exact H).
  assert (HAs : motives_typed gc_deps gc_stack (Δ ++ Γ)%list pc D Us (blocks_motives Bks) i).
  { intros j Mj Hj; destruct (blocks_nth _ _ _ _ HBl Hj) as [b Hb0].
    rewrite (blocks_motives_nth _ _ _ Hb0); exact (HBmot _ _ _ Hj Hb0). }
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓs HUl HUt) as Hσ.
  assert (HBbr : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
             (elim_bctx pc D Mj gs (blocks_motives Bks) Us ++ Δ ++ Γ)%list ⊢ B : elim_bty pc j Mj c gs (eb_motive b) Us).
  { intros j Mj b c gs n B Hj Hb0 Hcon Hin.
    pose proof (proj1 (List.Forall_forall _ _) IHBs b (List.nth_error_In _ _ Hb0)) as (_ & _ & IHbr).
    pose proof (proj1 (List.Forall_forall _ _) IHbr _ Hin) as IHB; cbn [snd] in IHB.
    pose proof (List.in_map (fun br => (fst br, (snd br)[wk_qn (snd (fst br)) φ]ʷ)) _ _ Hin) as Hin'; cbn [fst snd] in Hin'.
    pose proof (bt_counts _ _ _ _ _ _ _ _ HBt _ _ _ _ _ _ _ Hj (Hbw _ _ Hb0) Hcon Hin') as Hn.
    pose proof (bt_brs _ _ _ _ _ _ _ _ HBt _ _ _ _ _ _ _ Hj (Hbw _ _ Hb0) Hcon Hin') as HBL; cbn [eb_motive] in HBL.
    rewrite (HBnm _ _ _ Hj Hb0) in HBL.
    pose proof (wf_bty_sub _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hj HΓs HUl HUt HUt' HAs Hcon) as Hbs.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ (HBmot _ _ _ Hj Hb0) Hbs) as Hbt.
    assert (HLb : (tele_wk (elim_bctx pc D Mj gs (blocks_motives Bks) Us ++ Δ) ↑ ++ Γ ▹ A)%list
                  = (elim_bctx pc D Mj gs (blocks_motives (blocks_wk Bks φ)) (List.map (fun U => U[φ]ʷ) Us) ++ Lf)%list).
    { rewrite tele_wk_app; fold φ.
      rewrite (elim_bctx_wk pc D j Mj c gs (blocks_motives Bks) (blocks_motives (blocks_wk Bks φ)) Us φ);
        [ unfold Lf; rewrite <- List.app_assoc; reflexivity | exact Hc | exact Hj | exact (cons_lookup_in _ _ _ Hcon) | exact HUl |].
      intros j' Mj' Hj'; exact (blocks_motives_wk _ _ _ _ _ HBnm Hj'). }
    rewrite List.app_assoc.
    eapply (IHB (elim_bctx pc D Mj gs (blocks_motives Bks) Us ++ Δ) _ i).
    - apply List.Forall_app; split; [ eapply elim_bctx_ass; eassumption | exact Hass ].
    - rewrite HLb; eapply ext_eq_ctx_left; exact (bt_bctx _ _ _ _ _ _ _ _ HBt _ _ _ _ Hj Hcon).
    - rewrite <- List.app_assoc; exact Hbt.
    - rewrite HLb, List.length_app, length_elim_bctx, wk_qn_plus; fold φ.
      replace (cargs_nrec gs + List.length gs + im_nn Mj) with (im_nn Mj + List.length gs + cargs_nrec gs) by lia.
      rewrite (elim_bty_wk pc D j Mj c gs (eb_motive b) Us φ Hc Hj HUl), <- Hn; exact HBL. }
  assert (HBts : blocks_typed gc_deps gc_stack (Δ ++ Γ)%list pc D Us Bks i).
  { constructor; [ exact HBl | exact HBnm | | exact HBmot | | | | | exact HBbr ].
    - intros j Mj b Z Hj Hb0 HZ.
      pose proof (proj1 (List.Forall_forall _ _) IHBs b (List.nth_error_In _ _ Hb0)) as (Hn & _); congruence.
    - intros j Mj Hj; apply ctx_ext_refl; [ eapply elim_mctx_ass; eassumption | exact (HUt' _ _ Hj) ].
    - intros j Mj b Hj Hb0; pose proof (bt_names _ _ _ _ _ _ _ _ HBt _ _ _ Hj (Hbw _ _ Hb0)) as H; cbn [eb_brs] in H.
      unfold brs_names in *; rewrite List.map_map in H; exact H.
    - intros j Mj c gs Hj Hcon; apply ctx_ext_refl; [ eapply elim_bctx_ass; eassumption | eapply elim_bctx_wf; eassumption ].
    - intros j Mj b c gs n B Hj Hb0 Hcon Hin.
      pose proof (List.in_map (fun br => (fst br, (snd br)[wk_qn (snd (fst br)) φ]ʷ)) _ _ Hin) as Hin'; cbn [fst snd] in Hin'.
      exact (bt_counts _ _ _ _ _ _ _ _ HBt _ _ _ _ _ _ _ Hj (Hbw _ _ Hb0) Hcon Hin'). }
  (** The eliminator, short, at a type whose weakening is below [C]. *)
  destruct (blocks_nth _ _ _ _ HBl Hm) as [bm0 Hbm0].
  rewrite (Hbw _ _ Hbm0) in Hb; injection Hb as <-.
  pose proof (wf_elim_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hl (or_introl eq_refl) Hm Hbm0 HBts HUl HUt HNl HNt HuS) as Hel.
  destruct (presup_exp_typ Hel) as [i' Hi'].
  apply (mk_short_typ _ _ _ _ _ _ i' Hel Hi'); fold φ Lf.
  cbn [eb_motive] in Hmot, Hs; rewrite (HBnm _ _ _ Hm Hbm0) in Hmot, Hs.
  rewrite exp_wk_sb_of_list, List.map_app; cbn [List.map].
  replace (List.length (NsS ++ u :: nil)) with (S (im_nn Mm)) by (rewrite List.length_app, HNl; cbn; lia).
  etransitivity; [| exact Hs ].
  eapply wf_subtyp_refl'; symmetry; exact Hmot.
Qed.

Theorem nf_strengthen : forall Γ A,
    (forall (W : nf) Δ T i,
        tele_ass Δ ->
        ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
        (Δ ++ Γ)%list ⊢ T : Typeω@i ->
        (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ (W : exp)[wk_qn (length Δ) ↑]ʷ : T[wk_qn (length Δ) ↑]ʷ ->
        (Δ ++ Γ)%list ⊢ W : T) /\
    (forall u, ne_str Γ A u) /\
    (forall xs, la_all (ne_str Γ A) xs) /\
    (forall Ms : nfs, List.Forall (nf_str_exp Γ A) (nfs_to_exps Ms)) /\
    (forall Bs : nbrs, List.Forall (fun b => nf_str_exp Γ A (snd b)) (nbrs_to_brs Bs)) /\
    (forall Bks : nblocks, List.Forall (fun b => eb_ann b = None /\ nf_str_exp Γ A (eb_motive b) /\
                                                 List.Forall (fun br => nf_str_exp Γ A (snd br)) (eb_brs b))
                             (nblocks_to_blocks Bks)).
Proof.
  intros Γ A; apply nf_mut_ind.
  - intros * Hass HΓf HT HW; cbn [nf_to_exp exp_wk] in HW.
    assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
    apply wf_typ_inversion in HW.
    eapply wf_exp_subtyp; [ apply wf_typ, HΓs | exact HT |].
    eapply subtyp_strengthen_closed; [ exact Hass | exact HΓf | apply wf_typ, HΓs | exact HT | reflexivity | exact HW ].
  - intros c xs IH * Hass HΓf HT HW; cbn [nf_to_exp exp_wk] in HW.
    assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
    pose proof (wf_univ_inversion HW) as Hs.
    apply wf_univ_lvl_inversion in HW as [n HW].
    rewrite lvl_exp_of_wk in HW.
    assert (Hla : @la_wf gc_deps gc_stack n (Δ ++ Γ)%list xs)
      by (eapply la_wf_strengthen; [ exact IH | exact Hass | exact HΓf | exact HΓs | eapply lvl_exp_of_atoms; exact HW ]).
    assert (HL : (Δ ++ Γ)%list ⊢ lvl_exp_of c (la_to_list xs) : Level@n)
      by (apply lvl_exp_of_wf; [ exact (lvl_exp_of_cst_sort HW) | assumption | assumption ]).
    eapply wf_exp_subtyp; [ eapply wf_univ; exact HL | exact HT |].
    eapply subtyp_strengthen';
      [ exact Hass | exact HΓf | apply (wf_univ_large_tm (i := 0) (n := n)); [ exact HΓs | eapply wf_succl; exact HL ] | exact HT | exact Hs ].
  - intros * Hass HΓf HT HW; cbn [nf_to_exp exp_wk] in HW.
    assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
    apply wf_level_inversion in HW.
    eapply wf_exp_subtyp; [ apply wf_level, HΓs | exact HT |].
    eapply subtyp_strengthen_closed; [ exact Hass | exact HΓf | apply (wf_univ_large (i := 0)), HΓs | exact HT | reflexivity | exact HW ].
  - intros c xs IH * Hass HΓf HT HW; cbn [nf_to_exp exp_wk] in HW.
    assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
    rewrite lvl_exp_of_wk in HW.
    destruct (lvl_exp_of_inv _ _ _ _ HW) as [(n & HsL & Hcn & HF) | (a & -> & Hmap)].
    + assert (Hla : @la_wf gc_deps gc_stack n (Δ ++ Γ)%list xs)
        by (eapply la_wf_strengthen; [ exact IH | exact Hass | exact HΓf | exact HΓs | exact HF ]).
      assert (HL : (Δ ++ Γ)%list ⊢ lvl_exp_of c (la_to_list xs) : Level@n)
        by (apply lvl_exp_of_wf; [ exact Hcn | assumption | assumption ]).
      eapply wf_exp_subtyp; [ exact HL | exact HT |].
      eapply subtyp_strengthen_closed;
        [ exact Hass | exact HΓf | apply (wf_level_large (i := 0)), HΓs | exact HT | reflexivity | exact HsL ].
    + (** A single atom with no offset is the atom itself. *)
      destruct (la_map_single _ _ _ Hmap) as (s & u & -> & ->).
      destruct IH as [Hu _].
      cbn in HW |- *.
      destruct (Hu _ _ Hass HΓf HΓs HW) as [T0 j HuT HT0 Hs].
      eapply wf_exp_subtyp; [ exact HuT | exact HT |].
      eapply subtyp_strengthen'; eassumption.
  - intros * Hass HΓf HT HW; cbn [nf_to_exp exp_wk] in HW.
    assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
    apply wf_True_inversion in HW.
    eapply wf_exp_subtyp; [ apply wf_True, HΓs | exact HT |].
    eapply subtyp_strengthen_closed; [ exact Hass | exact HΓf | apply (wf_univ_large (i := 0)), HΓs | exact HT | reflexivity | exact HW ].
  - intros * Hass HΓf HT HW; cbn [nf_to_exp exp_wk] in HW.
    assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
    apply wf_true_inversion in HW.
    eapply wf_exp_subtyp; [ apply wf_true, HΓs | exact HT |].
    eapply subtyp_strengthen_closed; [ exact Hass | exact HΓf | apply (wf_True_large (i := 0)), HΓs | exact HT | reflexivity | exact HW ].
  - intros * Hass HΓf HT HW; cbn [nf_to_exp exp_wk] in HW.
    assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
    apply wf_False_inversion in HW.
    eapply wf_exp_subtyp; [ apply wf_False, HΓs | exact HT |].
    eapply subtyp_strengthen_closed; [ exact Hass | exact HΓf | apply (wf_univ_large (i := 0)), HΓs | exact HT | reflexivity | exact HW ].
  - intros A' IHA B' IHB * Hass HΓf HT HW; cbn [nf_to_exp exp_wk] in HW.
    assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
    assert (Hass' : tele_ass (ce_ass A' :: Δ)) by (constructor; [ eexists; reflexivity | exact Hass ]).
    destruct (wf_pi_inversion HW) as [(j & HA & HB & Hs) | (L & nL & HL & HA & HB & Hs)].
    + assert (HAs : (Δ ++ Γ)%list ⊢ A' : Typeω@j)
        by (eapply (IHA _ _ (S j)); [ exact Hass | exact HΓf | apply wf_typ, HΓs | exact HA ]).
      assert (HΓs' : ⊢ ((Δ ++ Γ) ▹ A')%list) by (eapply wf_ctx_extend; exact HAs).
      assert (HΓf' : ⊢ (tele_wk (ce_ass A' :: Δ) ↑ ++ Γ ▹ A)%list) by (gen_presups; assumption).
      assert (HBs : ((Δ ++ Γ) ▹ A')%list ⊢ B' : Typeω@j)
        by (eapply (IHB (ce_ass A' :: Δ) _ (S j)); [ exact Hass' | exact HΓf' | apply wf_typ, HΓs' | exact HB ]).
      eapply wf_exp_subtyp; [ apply wf_pi_large; eassumption | exact HT |].
      eapply subtyp_strengthen_closed; [ exact Hass | exact HΓf | apply wf_typ, HΓs | exact HT | reflexivity | exact Hs ].
    + (** A small [Π] at a long level: the short type is a universe
          ([typ_univ_shape_strengthen]), and the parts are checked against it. *)
      assert (HΓf1 : ⊢ ((tele_wk Δ ↑ ++ Γ ▹ A) ▹ (A' : exp)[wk_qn (length Δ) ↑]ʷ)%list) by (gen_presups; assumption).
      assert (Hw1 : ((tele_wk Δ ↑ ++ Γ ▹ A) ▹ (A' : exp)[wk_qn (length Δ) ↑]ʷ)%list ⊢ʷ ↑ : (tele_wk Δ ↑ ++ Γ ▹ A)%list)
        by mauto 2.
      assert (HL1 : ((tele_wk Δ ↑ ++ Γ ▹ A) ▹ (A' : exp)[wk_qn (length Δ) ↑]ʷ)%list ⊢ L[↑]ʷ : Level@nL)
        by (eapply (wk_preserves_exp _ _ _ _ Level@nL); eassumption).
      destruct (typ_univ_shape_strengthen _ _ _ _ _ _ Hass HΓf HT (univ_term_suniv L) Hs)
        as [[j Hj] | [M HM]].
      * assert (HTj : (Δ ++ Γ)%list ⊢ T ≈ (Typeωⁿ@j : exp) : Typeω@i) by (eapply soundness_ty'; eassumption).
        cbn [nf_to_exp] in HTj.
        pose proof (short_wk_exp_eq _ _ _ _ _ _ HΓf HTj) as HTjf; cbn [exp_wk] in HTjf.
        assert (Hsj : (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ Type⟨L⟩ ⊆ Typeω@j)
          by (etransitivity; [ exact Hs | eapply wf_subtyp_refl'; exact HTjf ]).
        assert (HAj : (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ (A' : exp)[wk_qn (length Δ) ↑]ʷ : Typeω@j)
          by (eapply wf_exp_subtyp; [ exact HA | apply wf_typ, HΓf | exact Hsj ]).
        assert (HAs : (Δ ++ Γ)%list ⊢ A' : Typeω@j)
          by (eapply (IHA _ _ (S j)); [ exact Hass | exact HΓf | apply wf_typ, HΓs | exact HAj ]).
        assert (HΓs' : ⊢ ((Δ ++ Γ) ▹ A')%list) by (eapply wf_ctx_extend; exact HAs).
        assert (HBj : ((tele_wk Δ ↑ ++ Γ ▹ A) ▹ (A' : exp)[wk_qn (length Δ) ↑]ʷ)%list
                        ⊢ (B' : exp)[wk_q (wk_qn (length Δ) ↑)]ʷ : Typeω@j)
          by (eapply wf_exp_subtyp; [ exact HB | apply wf_typ, HΓf1 | eapply wf_subtyp_small_large; eassumption ]).
        assert (HBs : ((Δ ++ Γ) ▹ A')%list ⊢ B' : Typeω@j)
          by (eapply (IHB (ce_ass A' :: Δ) _ (S j)); [ exact Hass' | exact HΓf1 | apply wf_typ, HΓs' | exact HBj ]).
        eapply wf_exp_subtyp; [ apply wf_pi_large; eassumption | exact HT |].
        eapply wf_subtyp_refl'; symmetry; exact HTj.
      * assert (HTM : (Δ ++ Γ)%list ⊢ T ≈ (nf_univ_of M : exp) : Typeω@i) by (eapply soundness_ty'; eassumption).
        cbn [nf_to_exp nf_univ_of] in HTM.
        set (Mx := lvl_exp_of (fst M) (la_to_list (snd M))) in *.
        assert (exists k, (Δ ++ Γ)%list ⊢ Type⟨Mx⟩ : Typeω@k) as [k Hk] by (gen_presups; eexists; eassumption).
        destruct (wf_univ_lvl_inversion Hk) as [nM HMx].
        pose proof (short_wk_exp_eq _ _ _ _ _ _ HΓf HTM) as HTMf; cbn [exp_wk] in HTMf.
        assert (HsM : (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ Type⟨L⟩ ⊆ Type⟨Mx[wk_qn (length Δ) ↑]ʷ⟩)
          by (etransitivity; [ exact Hs | eapply wf_subtyp_refl'; exact HTMf ]).
        assert (HAM : (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ (A' : exp)[wk_qn (length Δ) ↑]ʷ : Type⟨Mx[wk_qn (length Δ) ↑]ʷ⟩).
        { eapply wf_exp_subtyp; [ exact HA | | exact HsM ].
          eapply (wf_univ_large_tm (i := 0)); [ exact HΓf |].
          exact (short_wk_exp _ _ _ _ _ HΓf HMx). }
        assert (HAs : (Δ ++ Γ)%list ⊢ A' : Type⟨Mx⟩)
          by (eapply (IHA _ _ 0); [ exact Hass | exact HΓf | eapply (wf_univ_large_tm (i := 0)); eassumption | exact HAM ]).
        assert (HΓs' : ⊢ ((Δ ++ Γ) ▹ A')%list) by (eapply wf_ctx_extend, (wf_exp_suniv_large (i := 0) HMx HAs)).
        assert (HMx1 : ((Δ ++ Γ) ▹ A')%list ⊢ Mx[↑]ʷ : Level@nM)
          by (eapply (wk_preserves_exp _ _ _ _ Level@nM); [ exact HMx | mauto 2 ]).
        assert (HBM : ((tele_wk Δ ↑ ++ Γ ▹ A) ▹ (A' : exp)[wk_qn (length Δ) ↑]ʷ)%list
                        ⊢ (B' : exp)[wk_q (wk_qn (length Δ) ↑)]ʷ : Type⟨Mx[↑]ʷ[wk_q (wk_qn (length Δ) ↑)]ʷ⟩).
        { rewrite exp_wk_shift_wk_q.
          eapply wf_exp_subtyp; [ exact HB | |].
          - eapply (wf_univ_large_tm (i := 0)); [ exact HΓf1 |].
            eapply (wk_preserves_exp _ _ _ _ Level@nM); [ exact (short_wk_exp _ _ _ _ _ HΓf HMx) | exact Hw1 ].
          - exact (wk_preserves_subtyp _ _ _ _ _ _ _ HsM Hw1). }
        assert (HBs : ((Δ ++ Γ) ▹ A')%list ⊢ B' : Type⟨Mx[↑]ʷ⟩)
          by (eapply (IHB (ce_ass A' :: Δ) _ 0);
              [ exact Hass' | exact HΓf1 | eapply (wf_univ_large_tm (i := 0)); eassumption | exact HBM ]).
        eapply wf_exp_subtyp; [ eapply wf_pi_lvl; eassumption | exact HT |].
        eapply wf_subtyp_refl'; symmetry; exact HTM.
  - (** A function: its type is a [Π] in the short context ([typ_pi_shape_strengthen]),
        whose domain is the function's, and the body is checked against its codomain. *)
    intros A' IHA M' IHM * Hass HΓf HT HW; cbn [nf_to_exp exp_wk] in HW.
    assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
    assert (Hass' : tele_ass (ce_ass A' :: Δ)) by (constructor; [ eexists; reflexivity | exact Hass ]).
    destruct (wf_fn_inversion HW) as [B [HM Hs]].
    assert (HΓf' : ⊢ ((tele_wk Δ ↑ ++ Γ ▹ A) ▹ (A' : exp)[wk_qn (length Δ) ↑]ʷ)%list) by (gen_presups; assumption).
    destruct (ctx_decomp HΓf') as [_ [j HA]].
    assert (HAs : (Δ ++ Γ)%list ⊢ A' : Typeω@j)
      by (eapply (IHA _ _ (S j)); [ exact Hass | exact HΓf | apply wf_typ, HΓs | exact HA ]).
    destruct (subtyp_pi_left_shape _ _ _ _ Hs) as (X & Y & k0 & HTXY).
    destruct (typ_pi_shape_strengthen _ _ _ _ _ _ _ Hass HΓf HT ltac:(eapply wf_subtyp_refl'; exact HTXY)) as (C & D & HCD).
    assert (HTCD : (Δ ++ Γ)%list ⊢ T ≈ (Πⁿ C D : exp) : Typeω@i) by (eapply soundness_ty'; eassumption).
    cbn [nf_to_exp] in HTCD.
    assert (HCDt : (Δ ++ Γ)%list ⊢ Π C D : Typeω@i) by (gen_presups; assumption).
    destruct (wf_pi_inversion' HCDt) as [HC HD].
    pose proof (short_wk_exp_eq _ _ _ _ _ _ HΓf HTCD) as HTCDf; cbn [exp_wk] in HTCDf.
    assert (Hs' : (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ Π (A' : exp)[wk_qn (length Δ) ↑]ʷ B ⊆ Π (C : exp)[wk_qn (length Δ) ↑]ʷ (D : exp)[wk_q (wk_qn (length Δ) ↑)]ʷ)
      by (etransitivity; [ exact Hs | eapply wf_subtyp_refl'; exact HTCDf ]).
    destruct (subtyp_pi_inv _ _ _ _ _ Hs') as [[k HAC] HBD].
    set (m := max k (max i j)).
    assert (HA'm : (Δ ++ Γ)%list ⊢ A' : Typeω@m) by (eapply lift_exp_ge; [| exact HAs ]; lia).
    assert (HCm : (Δ ++ Γ)%list ⊢ C : Typeω@m) by (eapply lift_exp_ge; [| exact HC ]; lia).
    assert (HACm : (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ (A' : exp)[wk_qn (length Δ) ↑]ʷ ≈ (C : exp)[wk_qn (length Δ) ↑]ʷ : Typeω@m)
      by (eapply lift_exp_eq_ge; [| exact HAC ]; lia).
    assert (HACs : (Δ ++ Γ)%list ⊢ A' ≈ C : Typeω@m)
      by (eapply exp_eq_strengthen; [ exact Hass | exact HΓf | exact HA'm | exact HCm | exact HACm ]).
    assert (HDs : ((Δ ++ Γ) ▹ A')%list ⊢ D : Typeω@i)
      by (eapply ctxsub_exp; [ eapply wf_sub_id_extend_eq'; symmetry; exact HACs | exact HD ]).
    pose proof (short_wk_exp (ce_ass A' :: Δ) _ _ _ _ HΓf' HDs) as HDf.
    assert (HMf : ((tele_wk Δ ↑ ++ Γ ▹ A) ▹ (A' : exp)[wk_qn (length Δ) ↑]ʷ)%list ⊢ (M' : exp)[wk_q (wk_qn (length Δ) ↑)]ʷ : (D : exp)[wk_q (wk_qn (length Δ) ↑)]ʷ)
      by (eapply wf_exp_subtyp; [ exact HM | exact HDf | exact HBD ]).
    assert (HMs : ((Δ ++ Γ) ▹ A')%list ⊢ M' : D)
      by (eapply (IHM (ce_ass A' :: Δ)); [ exact Hass' | exact HΓf' | exact HDs | exact HMf ]).
    eapply wf_exp_subtyp; [ eapply wf_fn; [ exact HAs | exact HMs ] | exact HT |].
    eapply wf_subtyp_refl'.
    eapply exp_eq_trans_typ_max; [| symmetry; exact HTCD ].
    eapply wf_exp_eq_pi_cong_large; [ exact HA'm | exact HACs | eapply wf_exp_eq_refl, lift_exp_ge; [| exact HDs ]; lia ].
  - (** The type former applied. *)
    intros p k Ms IHMs; exact (exp_str_at _ _ _ (apps_str _ _ _ _ IHMs (ind_str _ _ p k))).
  - (** A constructor applied. *)
    intros p k c Ms IHMs; exact (exp_str_at _ _ _ (apps_str _ _ _ _ IHMs (con_str _ _ p k c))).
  - intros u IH * Hass HΓf HT HW; cbn [nf_to_exp] in HW |- *.
    assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
    destruct (IH _ _ Hass HΓf HΓs HW) as [T0 j HuT HT0 Hs].
    eapply wf_exp_subtyp; [ exact HuT | exact HT |].
    eapply subtyp_strengthen'; eassumption.
  - intros A' IHA u IHu Δ C Hass HΓf HΓs HW; cbn [ne_to_exp nf_to_exp exp_wk] in HW.
    destruct (wf_exfalso_inversion _ _ _ _ _ _ HW) as ([j HA] & Hu & HsC).
    assert (HΓf1 : ⊢ ((tele_wk Δ ↑ ++ Γ ▹ A) ▹ ⊥)%list) by (gen_presups; assumption).
    assert (Hass1 : tele_ass (ce_ass ⊥ :: Δ)) by (constructor; [ eexists; reflexivity | exact Hass ]).
    assert (HΓs1 : ⊢ ((Δ ++ Γ) ▹ ⊥)%list) by (eapply wf_ctx_extend, (wf_False_large (i := 0)), HΓs).
    assert (HAs : ((Δ ++ Γ) ▹ ⊥)%list ⊢ A' : Typeω@j)
      by (eapply (IHA (ce_ass ⊥ :: Δ) _ (S j)); [ exact Hass1 | exact HΓf1 | apply wf_typ, HΓs1 | exact HA ]).
    destruct (IHu _ _ Hass HΓf HΓs Hu) as [T0 j0 HuT HT0 Hs0].
    assert (Hus : (Δ ++ Γ)%list ⊢ u : ⊥).
    { eapply wf_exp_subtyp; [ exact HuT | apply (wf_False_large (i := 0)), HΓs |].
      eapply subtyp_strengthen'; [ exact Hass | exact HΓf | exact HT0 | apply (wf_False_large (i := 0)), HΓs | exact Hs0 ]. }
    apply (mk_short_typ _ _ _ _ _ ((A' : exp)[Id,,u]) j).
    + eapply wf_exfalso; eassumption.
    + eapply (exp_sub_single _ _ _ _ Typeω@j); [ exact HAs | exact Hus ].
    + rewrite exp_wk_sub_id_extend; exact HsC.
  - (** A stuck eliminator ([elim_str]). *)
    intros pc Us IHUs k Bks IHBs u IHu; exact (elim_str _ _ _ _ _ _ _ IHUs IHBs IHu).
  - (** An application. *)
    intros u IHu w IHw; exact (app_str _ _ _ _ IHu IHw).
  - (** A variable: the long variable is the image of a short one. *)
    intros x Δ C Hass HΓf HΓs HW; cbn [ne_to_exp exp_wk] in HW.
    destruct (wf_vlookup_inversion HW) as (A1 & Hl & HsC).
    destruct (lookup_strengthen _ _ _ _ _ Hl) as (T & HlT & ->).
    assert (Hx : (Δ ++ Γ)%list ⊢ #x : T) by (apply wf_vlookup; assumption).
    assert (exists j, (Δ ++ Γ)%list ⊢ T : Typeω@j) as [j HTj] by (gen_presups; eexists; eassumption).
    exact (mk_short_typ _ _ _ _ _ T j Hx HTj HsC).
  - (** A global: a closed member of a chain from a unit, typed in any
        context at a closed type. *)
    intros p Δ C Hass HΓf HΓs HW; cbn [ne_to_exp] in HW |- *.
    rewrite qname_term_wk in HW.
    destruct p as [fp ch].
    destruct (List.rev ch) as [| x pre] eqn:Er.
    + apply (f_equal (@List.rev _)) in Er; rewrite List.rev_involutive in Er; cbn in Er; subst ch.
      unfold qname_term in *; cbn [q_unit q_chain member_ref] in *.
      apply wf_true_inversion in HW.
      apply (mk_short_typ _ _ _ _ _ ⊤ 0); [ apply wf_true, HΓs | apply wf_True_large, HΓs | exact HW ].
    + apply (f_equal (@List.rev _)) in Er; rewrite List.rev_involutive in Er; cbn in Er; subst ch.
      change (qname_mk fp (List.rev pre ++ x :: nil)) with (qname_app (qname_mk fp (List.rev pre)) (x :: nil)) in *.
      rewrite qname_term_snoc in *.
      destruct (path_mem_any_ctx _ _ _ _ _ (qname_mod_qname _) HW) as (T & HTc & HsT & Hany).
      pose proof (Hany _ HΓs) as HTs.
      assert (exists j, (Δ ++ Γ)%list ⊢ T : Typeω@j) as [j HTj] by (gen_presups; eexists; eassumption).
      apply (mk_short_typ _ _ _ _ _ T j); [ exact HTs | exact HTj | rewrite exp_closed_wk by exact HTc; exact HsT ].
  - intros; exact I.
  - intros k u IHu xs IHxs; split; assumption.
  - cbn; constructor.
  - intros W IHW Ms IHMs; cbn; constructor; [ exact IHW | exact IHMs ].
  - cbn; constructor.
  - intros c n B IHB Bs IHBs; cbn; constructor; [ exact IHB | exact IHBs ].
  - cbn; constructor.
  - intros nm A' IHA Bs IHBs Bks IHBks; cbn; constructor; [ split; [ reflexivity | split; [ exact IHA | exact IHBs ] ] | exact IHBks ].
Qed.


(** ** At the Outermost Variable *)

(** A normal form typed, weakened, in [Γ ▹ A] at a weakened type of [Γ] is
    typed at that type in [Γ]. *)
Corollary nf_strengthen_shift : forall Γ A (W : nf) T i,
    ⊢ Γ ▹ A ->
    Γ ⊢ T : Typeω@i ->
    Γ ▹ A ⊢ (W : exp)[↑]ʷ : T[↑]ʷ ->
    Γ ⊢ W : T.
Proof.
  intros * HΓA HT HW.
  exact (proj1 (nf_strengthen Γ A) W nil T i ltac:(constructor) HΓA HT HW).
Qed.

(** The case the algorithmic [Π] needs: the level of a codomain's universe,
    when it does not mention the bound variable. *)
Corollary level_nf_strengthen : forall Γ A n (L : nf),
    ⊢ Γ ▹ A ->
    Γ ▹ A ⊢ (L : exp)[↑]ʷ : Level@n ->
    Γ ⊢ L : Level@n.
Proof.
  intros * HΓA HL.
  destruct (ctx_decomp HΓA) as [HΓ _].
  exact (nf_strengthen_shift Γ A L Level@n 0 HΓA (wf_level_large HΓ) HL).
Qed.

End Fixed_GCtx.
