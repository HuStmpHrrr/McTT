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
From Mctt.Core.Completeness Require Import FundamentalTheorem SubstitutionCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Lemmas.
From Mctt.Core.Semantic Require Import Consequences Realizability.
From Mctt.Core.Syntactic Require Import CoreInversions Fresh.
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

End Fixed_GCtx.
