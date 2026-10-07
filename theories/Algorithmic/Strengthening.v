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
From Mctt.Core.Completeness Require Import FundamentalTheorem SubstitutionCases UniverseCases PathCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Lemmas.
From Mctt.Core.Semantic Require Import Consequences Realizability MemberWf.
From Mctt.Core.Syntactic Require Import CoreInversions Fresh LevelEq.
From Mctt.Core.Syntactic.System Require Import MemberLemmas MemberWf Scoping.
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
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊨w (wk_qn (length Δ) ↑) : (Δ ++ Γ)%list.
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
  destruct HLs as [R1 [HR1 [i HLg]]].
  destruct HMs as [R0 [HR0 [j HMg]]].
  destruct HNs as [R0' [HR0' [k HNg]]].
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
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢w (wk_qn (length Δ) ↑) : (Δ ++ Γ)%list.
Proof.
  intros * HΓs HΓf.
  eapply wf_wk_ext; [| exact HΓf | exact HΓs ].
  (** The base case is the weakening by one, over the inserted assumption. *)
  apply wf_wk_shift; eapply ctx_app_wf_tail; exact HΓf.
Qed.

(** ** SubStr at [Level]

    A short type below [Level] in the long context is below it in the short
    one.  The algorithmic subtyping reads the long normal form off as
    [Levelⁿ], which turns the subtyping into an equation, and [exp_eq_strengthen]
    strengthens that. *)
Lemma subtyp_level_strengthen : forall Δ Γ A T i,
    tele_ass Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    (Δ ++ Γ)%list ⊢ T : Typeω@i ->
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ T[wk_qn (length Δ) ↑]ʷ ⊆ Level ->
    (Δ ++ Γ)%list ⊢ T ⊆ Level.
Proof.
  intros * Hass HΓf HT Hs.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; mauto 3).
  assert ((tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ T[wk_qn (length Δ) ↑]ʷ : Typeω@i)
    by (eapply (wk_preserves_exp _ _ _ _ Typeω@i); [ exact HT | apply wf_wk_qn; assumption ]).
  (** [Level] normalizes to [Levelⁿ] in any well-formed context, so the long
      subtyping can only be the reflexive rule, and the subject's normal form
      is [Levelⁿ] too; that turns the subtyping into an equation. *)
  destruct (sem_ctx_per_ctx_env (completeness_fundamental_ctx _ HΓf)) as [Rf HRf].
  destruct (per_ctx_then_per_env_initial_env HRf) as (ρ & ? & Hρ & ? & ?).
  assert (HLn : nbe_ty_f (tele_wk Δ ↑ ++ Γ ▹ A)%list Level Levelⁿ) by (econstructor; mauto 3).
  apply alg_subtyping_complete in Hs.
  inversion Hs as [? ? ? X Y HX HY Hsub]; subst.
  assert (Y = Levelⁿ) as -> by (eapply functional_nbe_ty; eassumption).
  inversion Hsub; subst.
  assert ((tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ T[wk_qn (length Δ) ↑]ʷ ≈ Levelⁿ : Typeω@i) as Heq
      by (eapply soundness_ty'; eassumption).
  assert ((Δ ++ Γ)%list ⊢ T ≈ Level : Typeω@i) as Heq'
      by (eapply exp_eq_strengthen; [ exact Hass | exact HΓf | exact HT
                                    | apply wf_level_large; exact HΓs | exact Heq ]).
  eapply wf_subtyp_refl; [ apply wf_level_large; exact HΓs | exact Heq' ].
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
  destruct HTs as [R0 [HR0 [j HTg]]].
  (** The long subtyping's own context PER is the one everything is read at. *)
  apply completeness_fundamental_subtyp in Hs as [R1 [HR1 [i' Hsg]]].
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
    as (aσ & a & a'σ' & a' & Ha1 & Ha2 & Ha3 & Ha4 & Hau & Ha'u & Hsub).
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
  1-5: try destruct (H s) as [L [HL HL']];
    do 2 eexists; repeat split; [ econstructor; eassumption | econstructor; eassumption | constructor; cbn; auto ].
  - do 2 eexists; repeat split; [ constructor | constructor | apply asnf_univ; assumption ].
  - destruct (H s) as [[c xs] [[d ys] [HL [HL' Hle]]]].
    do 2 eexists; repeat split; [ econstructor; eassumption | econstructor; eassumption | apply asnf_suniv; exact Hle ].
  - destruct (H s) as [W [HW _]].
    destruct (read_nf_level_real _ _ _ HW) as [[c xs] [-> _]].
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
  destruct HTs as [R0 [HR0 [j HTg]]].
  pose proof HT' as HTs'; apply completeness_fundamental_exp in HTs'.
  destruct HTs' as [R0' [HR0' [j' HTg']]].
  apply completeness_fundamental_subtyp in Hs as [R1 [HR1 [i' Hsg]]].
  destruct (per_ctx_then_per_env_initial_env HR0) as (ρs & ? & Hρs & ? & ?).
  destruct (long_env Δ Γ A R1 ρs Hass HΓs HΓf HR1 Hρs) as [ρ [Hρ Himg]].
  pose proof (rel_sub_of_wk (rel_wk_under_ctx_qn Δ Γ A Hass HΓs HΓf HAs)) as Hsb.
  pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_qn (length Δ) ↑) ρ _) as Hev.
  assert (⊨ (tele_wk Δ ↑ ++ Γ ▹ A)%list ≈ (tele_wk Δ ↑ ++ Γ ▹ A)%list) as HsA
      by (eexists; exact HR1).
  destruct (HTg _ _ HR1 _ _ Hsb _ _ _ _ Hρ Hev Hev) as [er [Ht He]].
  destruct (HTg' _ _ HR1 _ _ Hsb _ _ _ _ Hρ Hev Hev) as [er' [Ht' He']].
  destruct (Hsg _ _ HR1 _ _ (rel_sub_id HsA) _ _ _ _ Hρ (eval_sub_id _) (eval_sub_id _))
    as (aσ & a & a'σ' & a' & Ha1 & Ha2 & Ha3 & Ha4 & Hau & Ha'u & Hsub).
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

Lemma exp_wk_sub_natrec_succ : forall M φ,
    M[Wk ⨟ Wk,,succ #1][wk_q (wk_q φ)]ʷ = M[wk_q φ]ʷ[Wk ⨟ Wk,,succ #1].
Proof.
  intros; rewrite exp_wk_sub, exp_sub_wk.
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

(** The level expressions: a canonical level is [Level]-typed with
    [Level]-typed atoms, or it is a single atom with no offset, which is the
    atom itself. *)
Lemma succl_n_wf_inv : forall Γ k M C,
    Γ ⊢ succl_n (S k) M : C ->
    Γ ⊢ succl_n (S k) M : Level /\ Γ ⊢ Level ⊆ C /\ Γ ⊢ M : Level.
Proof.
  intros * H; cbn [succl_n] in H.
  apply wf_succl_inversion in H as [HM HC].
  split; [ mauto 3 | split; [ exact HC | eapply (wf_succl_n_inversion k); exact HM ] ].
Qed.

Lemma lvl_fold_wf_list : forall Γ xs hd,
    Γ ⊢ lvl_fold hd xs : Level ->
    Γ ⊢ hd : Level /\ List.Forall (fun p => Γ ⊢ snd p : Level) xs.
Proof.
  intros Γ xs; induction xs as [| [k a] r IH]; cbn; intros hd H; [ split; [ exact H | constructor ] |].
  apply IH in H as [Hh Hr]; apply wf_maxl_inversion in Hh as (Hh & Ha & _).
  split; [ exact Hh | constructor; [ cbn; eapply (wf_succl_n_inversion k); exact Ha | exact Hr ] ].
Qed.

Lemma lvl_fold_maxl_inv : forall Γ xs M N C,
    Γ ⊢ lvl_fold (maxl M N) xs : C ->
    Γ ⊢ lvl_fold (maxl M N) xs : Level /\ Γ ⊢ Level ⊆ C.
Proof.
  intros Γ xs; induction xs as [| [k a] r IH]; cbn; intros * H.
  - apply wf_maxl_inversion in H as (? & ? & ?); split; [ mauto 3 | assumption ].
  - apply IH in H; exact H.
Qed.

Lemma lvl_exp_of_inv : forall Γ c xs C,
    Γ ⊢ lvl_exp_of c xs : C ->
    (Γ ⊢ Level ⊆ C /\ List.Forall (fun p => Γ ⊢ snd p : Level) xs) \/
      (exists a, c = 0 /\ xs = (0, a) :: nil).
Proof.
  intros * H; destruct xs as [| [k a] r]; cbn in H.
  - left; split; [ eapply wf_llit_inversion; exact H | constructor ].
  - destruct c, r as [| [k' a'] r'], k as [| k]; cbn [lvl_fold] in H.
    + right; eexists; split; reflexivity.
    + left; apply succl_n_wf_inv in H as (? & ? & ?); split; [ assumption | repeat constructor; assumption ].
    + left; apply lvl_fold_maxl_inv in H as [H HC]; split; [ exact HC |].
      apply lvl_fold_wf_list in H as [Hh Hr]; apply wf_maxl_inversion in Hh as (? & ? & _).
      constructor; [ assumption | constructor; [ cbn; eapply (wf_succl_n_inversion k'); eassumption | exact Hr ] ].
    + left; apply lvl_fold_maxl_inv in H as [H HC]; split; [ exact HC |].
      apply lvl_fold_wf_list in H as [Hh Hr]; apply wf_maxl_inversion in Hh as (Hk & ? & _).
      constructor; [ cbn; eapply (wf_succl_n_inversion (S k)); eassumption
                   | constructor; [ cbn; eapply (wf_succl_n_inversion k'); eassumption | exact Hr ] ].
    + left; apply wf_maxl_inversion in H as (? & Ha & HC); split; [ exact HC |].
      repeat constructor; cbn; exact Ha.
    + left; apply wf_maxl_inversion in H as (? & Ha & HC); split; [ exact HC |].
      repeat constructor; cbn; eapply (wf_succl_n_inversion (S k)); exact Ha.
    + left; apply lvl_fold_maxl_inv in H as [H HC]; split; [ exact HC |].
      apply lvl_fold_wf_list in H as [Hh Hr]; apply wf_maxl_inversion in Hh as (Hh1 & ? & _).
      apply wf_maxl_inversion in Hh1 as (_ & ? & _).
      constructor; [ assumption | constructor; [ cbn; eapply (wf_succl_n_inversion k'); eassumption | exact Hr ] ].
    + left; apply lvl_fold_maxl_inv in H as [H HC]; split; [ exact HC |].
      apply lvl_fold_wf_list in H as [Hh Hr]; apply wf_maxl_inversion in Hh as (Hh1 & ? & _).
      apply wf_maxl_inversion in Hh1 as (_ & Hk & _).
      constructor; [ cbn; eapply (wf_succl_n_inversion (S k)); exact Hk
                   | constructor; [ cbn; eapply (wf_succl_n_inversion k'); eassumption | exact Hr ] ].
Qed.

(** A chain from a unit names a closed module: it is a module expression in
    every well-formed context, and a member of it is typed, at a closed type,
    in every well-formed context. *)
Lemma chain_wf_any_ctx : forall H p Γ Γ',
    mod_qname H = Some p ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    ⊢ Γ' ->
    gc_deps ⍮ gc_stack ⍮ Γ' ⊢ᵐ H ≈ H.
Proof.
  induction H as [fp | x | H IH y | H IH N | U]; intros * Hp HH HΓ'; cbn in Hp; try discriminate.
  - destruct (modexp_parts_of_wf _ _ _ _ HH) as [T HT].
    eapply wf_me_glob; [ exact HΓ' | exact Hp | eapply mt_unit_ctx; exact HT ].
  - destruct (mod_qname H) as [p0 |] eqn:E; [| discriminate ].
    destruct (modexp_parts_of_wf _ _ _ _ HH) as [[HH0 [T HT]] | [_ [T HT]]].
    + eapply wf_me_mem; [ eapply IH; [ reflexivity | exact HH0 | exact HΓ' ]
                         | eapply mt_chain_ctx; [ exact E | exact HT ] | eapply mt_chain_ctx; [ exact E | exact HT ] ].
    + eapply wf_me_glob; [ exact HΓ' | cbn; rewrite E; reflexivity |].
      eapply mt_chain_ctx; [| exact HT ]; cbn; rewrite E; reflexivity.
Qed.

Lemma chain_mem_any_ctx : forall Γ H p x C,
    mod_qname H = Some p ->
    Γ ⊢ a_mem H x : C ->
    exists T, exp_scoped 0 T /\ Γ ⊢ T ⊆ C /\ (forall Γ', ⊢ Γ' -> Γ' ⊢ a_mem H x : T).
Proof.
  intros * Hp HM.
  remember gc_deps as Θ0 eqn:HΘ; remember gc_stack as Ξ0 eqn:HΞ.
  remember (a_mem H x) as M eqn:EM.
  revert H p x Hp EM.
  induction HM; intros Hm pm xm Hpm EMm; subst; try discriminate; try (injection EMm as <- <-).
  - (** At its canonical type: the type is closed, as it is at [⋅], and the
        member is typed in any context by [member_wf]. *)
    assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
    assert (HA : exp_scoped 0 A).
    { pose proof (mt_chain_ctx _ _ _ _ nil _ _ _ Hpm H2) as Hm0.
      exact (proj1 (member_type_scoped _ _) _ _ _ _ Hm0 (wf_gctx_closed _ _ _ HΓ) I
               (mod_qname_scoped _ _ _ Hpm)). }
    exists A; split; [ exact HA | split; [ eapply wf_subtyp_refl'; mauto 3 |] ].
    intros Γ' HΓ'.
    assert (HH' : gc_deps ⍮ gc_stack ⍮ Γ' ⊢ᵐ H ≈ H) by (eapply chain_wf_any_ctx; eassumption).
    assert (Hm' : member_type gc_deps gc_stack Γ' H (x :: nil) (mr_term A))
      by (eapply mt_chain_ctx; eassumption).
    destruct (proj1 member_wf _ _ _ _ Hm' HH' ltac:(intros _; discriminate)) as ([j HAj] & HMu & _).
    destruct (HMu eq_refl) as [M' [HM' HM'A]].
    eapply wf_mem; [ eapply mod_qname_noargs; eassumption | exact HH' | exact Hm' | exact HAj | exact HM' | exact HM'A ].
  - (** A chain from a unit has no arguments. *)
    rewrite (mod_qname_spine _ _ Hpm) in *; congruence.
  - exists A; split; [ eapply wf_gc_resolve_type_closed; eassumption |].
    destruct (wf_glob_typ _ _ _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)) as [j ?].
    split; [ eapply wf_subtyp_refl'; mauto 3 |].
    intros Γ' HΓ'; eapply wf_mem_glob; [ exact HΓ' | exact H1 | exact H2 ].
  - destruct (IHHM1 eq_refl eq_refl _ _ _ Hpm eq_refl) as (T & HT & HTs & HT').
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
  - exfalso; destruct (univ_sub_univ_term HUV) as [HUt _].
    eapply (pi_univ_term_absurd _ _ _ _ _ HUt); exact HU.
  - destruct (exp_eq_pi_inversion Ha) as [HA1 HA2].
    destruct (exp_eq_pi_inversion Hb) as [HB1 HB2].
    assert (HAB1 : Γ ⊢ A ≈ B1 : Typeω@(max k1 k3))
      by (eapply exp_eq_trans_typ_max; [ exact HA1 | exact Hab ]).
    assert (HId : Γ ▹ A ⊢s Id : Γ ▹ B1) by (eapply wf_sub_id_extend_eq'; symmetry; exact HAB1).
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
  - exfalso; destruct (univ_sub_univ_term HUV) as [HUt _].
    eapply (pi_univ_term_absurd _ _ _ _ _ HUt); exact HU.
  - do 3 eexists; symmetry; exact Hb.
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
Definition ne_str (Γ : ctx) (A : typ) (u : ne) : Prop :=
  forall Δ C,
    tele_ass Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    ⊢ (Δ ++ Γ)%list ->
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ (u : exp)[wk_qn (length Δ) ↑]ʷ : C ->
    exists T i, (Δ ++ Γ)%list ⊢ u : T /\ (Δ ++ Γ)%list ⊢ T : Typeω@i /\
           (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ T[wk_qn (length Δ) ↑]ʷ ⊆ C.

(** A neutral typed at [Level] in the long context is in the short one. *)
Lemma ne_str_level : forall Γ A Δ (u : ne),
    ne_str Γ A u ->
    tele_ass Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    ⊢ (Δ ++ Γ)%list ->
    (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ (u : exp)[wk_qn (length Δ) ↑]ʷ : Level ->
    (Δ ++ Γ)%list ⊢ u : Level.
Proof.
  intros * Hu Hass HΓf HΓs H.
  destruct (Hu _ _ Hass HΓf HΓs H) as (T & i & HuT & HT & Hs).
  eapply wf_exp_subtyp; [ exact HuT | apply (wf_level_large (i := 0)), HΓs |].
  eapply subtyp_strengthen';
    [ exact Hass | exact HΓf | exact HT | apply (wf_level_large (i := 0)), HΓs | exact Hs ].
Qed.

Lemma la_wf_strengthen : forall Γ A Δ xs,
    la_all (ne_str Γ A) xs ->
    tele_ass Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
    ⊢ (Δ ++ Γ)%list ->
    List.Forall (fun p => (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ snd p : Level)
      (List.map (fun p => (fst p, (snd p)[wk_qn (length Δ) ↑]ʷ)) (la_to_list xs)) ->
    @la_wf gc_deps gc_stack (Δ ++ Γ)%list xs.
Proof.
  intros Γ A Δ xs; induction xs as [| k u r IH]; cbn; [ intros; exact I |].
  intros [Hu Hr] Hass HΓf HΓs HF.
  inversion HF as [| ? ? Hk HF']; subst.
  split; [ eapply ne_str_level; eassumption | apply IH; assumption ].
Qed.

(** The atoms of a level expression typed at [Level] are. *)
Lemma lvl_exp_of_atoms : forall Γ c xs,
    Γ ⊢ lvl_exp_of c xs : Level ->
    List.Forall (fun p => Γ ⊢ snd p : Level) xs.
Proof.
  intros * H; destruct (lvl_exp_of_inv _ _ _ _ H) as [[_ HF] | (a & -> & ->)]; [ exact HF |].
  repeat constructor; exact H.
Qed.

(** A weakened atom list with a single entry and no offset. *)
Lemma la_map_single : forall φ xs a,
    List.map (fun p => (fst p, (snd p)[φ]ʷ)) (la_to_list xs) = (0, a) :: nil ->
    exists u, xs = la_cons 0 u la_nil /\ a = (u : exp)[φ]ʷ.
Proof.
  intros φ [| k u [| k' u' r]] a H; cbn in H; try discriminate.
  injection H as -> <-; eexists; split; reflexivity.
Qed.

Theorem nf_strengthen : forall Γ A,
    (forall (W : nf) Δ T i,
        tele_ass Δ ->
        ⊢ (tele_wk Δ ↑ ++ Γ ▹ A)%list ->
        (Δ ++ Γ)%list ⊢ T : Typeω@i ->
        (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ (W : exp)[wk_qn (length Δ) ↑]ʷ : T[wk_qn (length Δ) ↑]ʷ ->
        (Δ ++ Γ)%list ⊢ W : T) /\
    (forall u, ne_str Γ A u) /\
    (forall xs, la_all (ne_str Γ A) xs).
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
    apply wf_univ_lvl_inversion in HW.
    rewrite lvl_exp_of_wk in HW.
    assert (Hla : @la_wf gc_deps gc_stack (Δ ++ Γ)%list xs)
      by (eapply la_wf_strengthen; [ exact IH | exact Hass | exact HΓf | exact HΓs | eapply lvl_exp_of_atoms; exact HW ]).
    assert (HL : (Δ ++ Γ)%list ⊢ lvl_exp_of c (la_to_list xs) : Level) by (apply lvl_exp_of_wf; assumption).
    eapply wf_exp_subtyp; [ apply wf_univ, HL | exact HT |].
    eapply subtyp_strengthen';
      [ exact Hass | exact HΓf | apply (wf_univ_large_tm (i := 0)); [ exact HΓs | apply wf_succl, HL ] | exact HT | exact Hs ].
  - intros * Hass HΓf HT HW; cbn [nf_to_exp exp_wk] in HW.
    assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
    apply wf_level_inversion in HW.
    eapply wf_exp_subtyp; [ apply wf_level, HΓs | exact HT |].
    eapply subtyp_strengthen_closed; [ exact Hass | exact HΓf | apply (wf_univ_large (i := 0)), HΓs | exact HT | reflexivity | exact HW ].
  - intros c xs IH * Hass HΓf HT HW; cbn [nf_to_exp exp_wk] in HW.
    assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
    rewrite lvl_exp_of_wk in HW.
    destruct (lvl_exp_of_inv _ _ _ _ HW) as [[HsL HF] | (a & -> & Hmap)].
    + assert (Hla : @la_wf gc_deps gc_stack (Δ ++ Γ)%list xs)
        by (eapply la_wf_strengthen; [ exact IH | exact Hass | exact HΓf | exact HΓs | exact HF ]).
      assert (HL : (Δ ++ Γ)%list ⊢ lvl_exp_of c (la_to_list xs) : Level) by (apply lvl_exp_of_wf; assumption).
      eapply wf_exp_subtyp; [ exact HL | exact HT |].
      eapply subtyp_strengthen_closed;
        [ exact Hass | exact HΓf | apply (wf_level_large (i := 0)), HΓs | exact HT | reflexivity | exact HsL ].
    + (** A single atom with no offset is the atom itself. *)
      destruct (la_map_single _ _ _ Hmap) as (u & -> & ->).
      destruct IH as [Hu _].
      cbn in HW |- *.
      destruct (Hu _ _ Hass HΓf HΓs HW) as (T0 & j & HuT & HT0 & Hs).
      eapply wf_exp_subtyp; [ exact HuT | exact HT |].
      eapply subtyp_strengthen'; eassumption.
  - intros * Hass HΓf HT HW; cbn [nf_to_exp exp_wk] in HW.
    assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
    apply wf_nat_inversion in HW.
    eapply wf_exp_subtyp; [ apply wf_nat, HΓs | exact HT |].
    eapply subtyp_strengthen_closed; [ exact Hass | exact HΓf | apply (wf_univ_large (i := 0)), HΓs | exact HT | reflexivity | exact HW ].
  - intros * Hass HΓf HT HW; cbn [nf_to_exp exp_wk] in HW.
    assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
    apply wf_zero_inversion in HW.
    eapply wf_exp_subtyp; [ apply wf_zero, HΓs | exact HT |].
    eapply subtyp_strengthen_closed; [ exact Hass | exact HΓf | apply (wf_nat_large (i := 0)), HΓs | exact HT | reflexivity | exact HW ].
  - intros W IH * Hass HΓf HT HW; cbn [nf_to_exp exp_wk] in HW.
    assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
    apply wf_succ_inversion in HW as [HW Hs].
    assert (HWs : (Δ ++ Γ)%list ⊢ W : ℕ) by (eapply (IH _ _ 0); [ exact Hass | exact HΓf | apply wf_nat_large, HΓs | exact HW ]).
    eapply wf_exp_subtyp; [ apply wf_succ, HWs | exact HT |].
    eapply subtyp_strengthen_closed; [ exact Hass | exact HΓf | apply (wf_nat_large (i := 0)), HΓs | exact HT | reflexivity | exact Hs ].
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
    destruct (wf_pi_inversion HW) as [(j & HA & HB & Hs) | (n & HA & HB & Hs)].
    + assert (HAs : (Δ ++ Γ)%list ⊢ A' : Typeω@j)
        by (eapply (IHA _ _ (S j)); [ exact Hass | exact HΓf | apply wf_typ, HΓs | exact HA ]).
      assert (HΓs' : ⊢ ((Δ ++ Γ) ▹ A')%list) by (eapply wf_ctx_extend; exact HAs).
      assert (HΓf' : ⊢ (tele_wk (ce_ass A' :: Δ) ↑ ++ Γ ▹ A)%list) by (gen_presups; assumption).
      assert (HBs : ((Δ ++ Γ) ▹ A')%list ⊢ B' : Typeω@j)
        by (eapply (IHB (ce_ass A' :: Δ) _ (S j)); [ exact Hass' | exact HΓf' | apply wf_typ, HΓs' | exact HB ]).
      eapply wf_exp_subtyp; [ apply wf_pi; eassumption | exact HT |].
      eapply subtyp_strengthen_closed; [ exact Hass | exact HΓf | apply wf_typ, HΓs | exact HT | reflexivity | exact Hs ].
    + assert (HAs : (Δ ++ Γ)%list ⊢ A' : Type@n)
        by (eapply (IHA _ _ 0); [ exact Hass | exact HΓf | apply wf_univ_large, HΓs | exact HA ]).
      assert (HΓs' : ⊢ ((Δ ++ Γ) ▹ A')%list) by (eapply wf_ctx_extend, (wf_exp_small_large (i := 0) HAs)).
      assert (HΓf' : ⊢ (tele_wk (ce_ass A' :: Δ) ↑ ++ Γ ▹ A)%list) by (gen_presups; assumption).
      assert (HBs : ((Δ ++ Γ) ▹ A')%list ⊢ B' : Type@n)
        by (eapply (IHB (ce_ass A' :: Δ) _ 0); [ exact Hass' | exact HΓf' | apply wf_univ_large, HΓs' | exact HB ]).
      eapply wf_exp_subtyp; [ apply wf_pi_small; eassumption | exact HT |].
      eapply subtyp_strengthen_closed; [ exact Hass | exact HΓf | apply (wf_univ_large (i := 0)), HΓs | exact HT | reflexivity | exact Hs ].
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
    eapply wf_exp_eq_pi_cong; [ exact HA'm | exact HACs | eapply wf_exp_eq_refl, lift_exp_ge; [| exact HDs ]; lia ].
  - intros u IH * Hass HΓf HT HW; cbn [nf_to_exp] in HW |- *.
    assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
    destruct (IH _ _ Hass HΓf HΓs HW) as (T0 & j & HuT & HT0 & Hs).
    eapply wf_exp_subtyp; [ exact HuT | exact HT |].
    eapply subtyp_strengthen'; eassumption.
  - (** The [ℕ]-eliminator: the motive, the branches and the scrutinee by the
        induction hypotheses, the scrutinee's type by [subtyp_strengthen']. *)
    intros A' IHA z IHz s IHs u IHu Δ C Hass HΓf HΓs HW; cbn [ne_to_exp nf_to_exp exp_wk] in HW.
    destruct (wf_natrec_inversion _ _ _ _ _ _ _ _ HW) as (Hz & Hs & Hu & HsC).
    assert (HΓf2 : ⊢ (((tele_wk Δ ↑ ++ Γ ▹ A) ▹ ℕ) ▹ (A' : exp)[wk_q (wk_qn (length Δ) ↑)]ʷ)%list) by (gen_presups; assumption).
    destruct (ctx_decomp HΓf2) as [HΓf1 [j HA]].
    assert (Hass1 : tele_ass (ce_ass ℕ :: Δ)) by (constructor; [ eexists; reflexivity | exact Hass ]).
    assert (HΓs1 : ⊢ ((Δ ++ Γ) ▹ ℕ)%list) by (eapply wf_ctx_extend, (wf_nat_large (i := 0)), HΓs).
    assert (HAs : ((Δ ++ Γ) ▹ ℕ)%list ⊢ A' : Typeω@j)
      by (eapply (IHA (ce_ass ℕ :: Δ) _ (S j)); [ exact Hass1 | exact HΓf1 | apply wf_typ, HΓs1 | exact HA ]).
    destruct (IHu _ _ Hass HΓf HΓs Hu) as (T0 & j0 & HuT & HT0 & Hs0).
    assert (Hus : (Δ ++ Γ)%list ⊢ u : ℕ).
    { eapply wf_exp_subtyp; [ exact HuT | apply (wf_nat_large (i := 0)), HΓs |].
      eapply subtyp_strengthen'; [ exact Hass | exact HΓf | exact HT0 | apply (wf_nat_large (i := 0)), HΓs | exact Hs0 ]. }
    assert (HAz : (Δ ++ Γ)%list ⊢ (A' : exp)[Id,,zero] : Typeω@j)
      by (eapply (exp_sub_single _ _ _ _ Typeω@j); [ exact HAs | apply wf_zero, HΓs ]).
    assert (Hzs : (Δ ++ Γ)%list ⊢ z : (A' : exp)[Id,,zero])
      by (eapply (IHz _ _ j); [ exact Hass | exact HΓf | exact HAz | rewrite exp_wk_sub_id_extend; exact Hz ]).
    assert (Hass2 : tele_ass (ce_ass A' :: ce_ass ℕ :: Δ)) by (constructor; [ eexists; reflexivity | exact Hass1 ]).
    assert (HΓs2 : ⊢ ((Δ ++ Γ) ▹ ℕ ▹ A')%list) by (eapply wf_ctx_extend; exact HAs).
    assert (HAS : ((Δ ++ Γ) ▹ ℕ ▹ A')%list ⊢ (A' : exp)[Wk ⨟ Wk,,succ #1] : Typeω@j) by mauto 3.
    assert (Hss : ((Δ ++ Γ) ▹ ℕ ▹ A')%list ⊢ s : (A' : exp)[Wk ⨟ Wk,,succ #1])
      by (eapply (IHs (ce_ass A' :: ce_ass ℕ :: Δ) _ j);
          [ exact Hass2 | exact HΓf2 | exact HAS | cbn [length wk_qn]; rewrite exp_wk_sub_natrec_succ; exact Hs ]).
    exists ((A' : exp)[Id,,u]), j; split; [| split ].
    + eapply wf_natrec; eassumption.
    + eapply (exp_sub_single _ _ _ _ Typeω@j); [ exact HAs | exact Hus ].
    + rewrite exp_wk_sub_id_extend; exact HsC.
  - intros A' IHA u IHu Δ C Hass HΓf HΓs HW; cbn [ne_to_exp nf_to_exp exp_wk] in HW.
    destruct (wf_exfalso_inversion _ _ _ _ _ _ HW) as ([j HA] & Hu & HsC).
    assert (HΓf1 : ⊢ ((tele_wk Δ ↑ ++ Γ ▹ A) ▹ ⊥)%list) by (gen_presups; assumption).
    assert (Hass1 : tele_ass (ce_ass ⊥ :: Δ)) by (constructor; [ eexists; reflexivity | exact Hass ]).
    assert (HΓs1 : ⊢ ((Δ ++ Γ) ▹ ⊥)%list) by (eapply wf_ctx_extend, (wf_False_large (i := 0)), HΓs).
    assert (HAs : ((Δ ++ Γ) ▹ ⊥)%list ⊢ A' : Typeω@j)
      by (eapply (IHA (ce_ass ⊥ :: Δ) _ (S j)); [ exact Hass1 | exact HΓf1 | apply wf_typ, HΓs1 | exact HA ]).
    destruct (IHu _ _ Hass HΓf HΓs Hu) as (T0 & j0 & HuT & HT0 & Hs0).
    assert (Hus : (Δ ++ Γ)%list ⊢ u : ⊥).
    { eapply wf_exp_subtyp; [ exact HuT | apply (wf_False_large (i := 0)), HΓs |].
      eapply subtyp_strengthen'; [ exact Hass | exact HΓf | exact HT0 | apply (wf_False_large (i := 0)), HΓs | exact Hs0 ]. }
    exists ((A' : exp)[Id,,u]), j; split; [| split ].
    + eapply wf_exfalso; eassumption.
    + eapply (exp_sub_single _ _ _ _ Typeω@j); [ exact HAs | exact Hus ].
    + rewrite exp_wk_sub_id_extend; exact HsC.
  - (** An application: the head's short type is a [Π] ([typ_pi_shape_strengthen]),
        whose domain the argument is checked against. *)
    intros u IHu w IHw Δ C Hass HΓf HΓs HW; cbn [ne_to_exp nf_to_exp exp_wk] in HW.
    destruct (wf_app_inversion HW) as (X & Y & Hu & Hw & HsC).
    destruct (IHu _ _ Hass HΓf HΓs Hu) as (T0 & j0 & HuT & HT0 & Hs0).
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
    assert (Hwf : (tele_wk Δ ↑ ++ Γ ▹ A)%list ⊢ (w : exp)[wk_qn (length Δ) ↑]ʷ : (C' : exp)[wk_qn (length Δ) ↑]ʷ)
      by (eapply wf_exp_subtyp; [ exact Hw | exact HCf | eapply wf_subtyp_refl'; symmetry; exact HCX ]).
    assert (Hws : (Δ ++ Γ)%list ⊢ w : C') by (eapply (IHw _ _ j0); [ exact Hass | exact HΓf | exact HC | exact Hwf ]).
    assert (Hus : (Δ ++ Γ)%list ⊢ u : Π C' D')
      by (eapply wf_exp_subtyp; [ exact HuT | exact HCDt | eapply wf_subtyp_refl'; exact HTCD ]).
    exists ((D' : exp)[Id,,w]), j0; split; [| split ].
    + eapply wf_app; eassumption.
    + eapply (exp_sub_single _ _ _ _ Typeω@j0); [ exact HD | exact Hws ].
    + rewrite exp_wk_sub_id_extend; etransitivity; [| exact HsC ].
      eapply sub_preserves_subtyp; [ exact HDY | eapply wf_sub_single; [ exact HCf | exact Hwf ] ].
  - (** A variable: the long variable is the image of a short one. *)
    intros x Δ C Hass HΓf HΓs HW; cbn [ne_to_exp exp_wk] in HW.
    destruct (wf_vlookup_inversion HW) as (A1 & Hl & HsC).
    destruct (lookup_strengthen _ _ _ _ _ Hl) as (T & HlT & ->).
    assert (Hx : (Δ ++ Γ)%list ⊢ #x : T) by (apply wf_vlookup; assumption).
    assert (exists j, (Δ ++ Γ)%list ⊢ T : Typeω@j) as [j HTj] by (gen_presups; eexists; eassumption).
    exists T, j; split; [ exact Hx | split; [ exact HTj | exact HsC ] ].
  - (** A global: a closed member of a chain from a unit, typed in any
        context at a closed type. *)
    intros p Δ C Hass HΓf HΓs HW; cbn [ne_to_exp] in HW |- *.
    rewrite qname_term_wk in HW.
    destruct p as [fp ch].
    destruct (List.rev ch) as [| x pre] eqn:Er.
    + apply (f_equal (@List.rev _)) in Er; rewrite List.rev_involutive in Er; cbn in Er; subst ch.
      unfold qname_term in *; cbn [q_unit q_chain member_ref] in *.
      apply wf_zero_inversion in HW.
      exists ℕ, 0; split; [ apply wf_zero, HΓs | split; [ apply wf_nat_large, HΓs | exact HW ] ].
    + apply (f_equal (@List.rev _)) in Er; rewrite List.rev_involutive in Er; cbn in Er; subst ch.
      change (qname_mk fp (List.rev pre ++ x :: nil)) with (qname_app (qname_mk fp (List.rev pre)) (x :: nil)) in *.
      rewrite qname_term_snoc in *.
      destruct (chain_mem_any_ctx _ _ _ _ _ (qname_mod_qname _) HW) as (T & HTc & HsT & Hany).
      pose proof (Hany _ HΓs) as HTs.
      assert (exists j, (Δ ++ Γ)%list ⊢ T : Typeω@j) as [j HTj] by (gen_presups; eexists; eassumption).
      exists T, j; split; [ exact HTs | split; [ exact HTj | rewrite exp_closed_wk by exact HTc; exact HsT ] ].
  - intros; exact I.
  - intros k u IHu xs IHxs; split; assumption.
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
Corollary level_nf_strengthen : forall Γ A (L : nf),
    ⊢ Γ ▹ A ->
    Γ ▹ A ⊢ (L : exp)[↑]ʷ : Level ->
    Γ ⊢ L : Level.
Proof.
  intros * HΓA HL.
  destruct (ctx_decomp HΓA) as [HΓ _].
  exact (nf_strengthen_shift Γ A L Level 0 HΓA (wf_level_large HΓ) HL).
Qed.

End Fixed_GCtx.
