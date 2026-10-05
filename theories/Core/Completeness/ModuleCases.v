(** * The Global Rules: Validity along an Embedding

    A judgment of the global context [Θ1] is valid at every [Θ2] it embeds
    into, provided what [Θ1] files is valid at [Θ2] ([sem_emb]): its
    constants, at their types, and its units, in their parts.  Constants and
    units are closed, so an embedding moves nothing: the fundamental theorem
    holds in this form for every rule ([kripke_fundamental]), each case being
    the fixed-context case lemma at the target.  The validity of what a
    well-formed global context files is shown by induction over it
    ([gctx_sem]), so at the identity it is the fixed-context theorem. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import MemberLemmas GlobalPresup.
From Mctt.Core.Completeness Require Import
  ContextCases FunctionCases LetCases NatCases SubstitutionCases SubtypingCases
  TrueFalseCases UniverseCases VariableCases LogicalRelation UnitCases InstanceCases
  MemberCases MemberTyping MemberReps MemberSem ModexpCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. Sound embeddings *)

(** A constant of type [A] and body [oM], if any, valid at [Θ2]; a unit
    valid at [Θ2]. *)
Definition VCs (Θ2 : gctx) (A : exp) (oM : option exp) : Prop :=
  (exists i, @rel_exp_under_ctx (gc_mk Θ2) ⋅ (Type@i) A A) /\
  (forall M, oM = Some M -> @rel_exp_under_ctx (gc_mk Θ2) ⋅ A M M).

Definition VUs (Θ2 : gctx) (U : gunit) : Prop :=
  @sem_unit (gc_mk Θ2) ⋅ U /\ @unit_mt (gc_mk Θ2) Θ2 ⋅ U /\
  @rel_modexp_under_ctx (gc_mk Θ2) ⋅ (me_lit U) (me_lit U).

Record sem_emb (Θ1 Θ2 : gctx) : Prop :=
  { sme_emb : Emb Θ1 Θ2
  ; sme_gv : GV VCs VUs Θ1 Θ2 }.

(** ** 2. Constants from the validity of their types and bodies

    A sealed constant evaluates to a neutral at its type evaluated at [nil],
    an unsealed one to its body evaluated there.  [nil] is reached by
    [sb_zero], which evaluates to [nil] in any environment, so instantiating
    a [⋅] judgment at [sb_zero] relates the value at [nil] to the value
    anywhere. *)

(** A judgment about closed terms at [⋅] holds in every semantically
    well-formed context: [rel_exp_under_ctx_wk] along [wk_id] from [Γ] to [⋅]. *)
Lemma closed_weaken_sem : forall {GC : GCtx} Γ T N N',
    ⊨ Γ ->
    ⋅ ⊨ N ≈ N' : T ->
    T[wk_id]ʷ = T -> N[wk_id]ʷ = N -> N'[wk_id]ʷ = N' ->
    Γ ⊨ N ≈ N' : T.
Proof.
  intros * HΓ H HT HN HN'.
  rewrite <- HT, <- HN, <- HN'.
  eapply rel_exp_under_ctx_wk; [| exact H ].
  destruct (sem_ctx_per_ctx_env HΓ) as [R HR].
  eapply (rel_wk_under_ctx_intro (R' := fun _ _ => True)); [ exact HR | |].
  - apply per_ctx_env_nil; reflexivity.
  - constructor; [ apply wk_mono_id | intros; exact I ].
Qed.

(** δ: a closed term [G] that evaluates anywhere to what [N] evaluates to at
    [nil] is equal to [N]. *)
Lemma rel_exp_delta_nil : forall {GC : GCtx} T N G,
    ⋅ ⊨ N : T ->
    (forall σ, T[σ] = T) -> (forall σ, N[σ] = N) -> (forall σ, G[σ] = G) ->
    (forall ρ m, eval_exp gc_ctx N nil m -> eval_exp gc_ctx G ρ m) ->
    ⋅ ⊨ G ≈ N : T.
Proof.
  intros * HN HT HNc HG Hδ.
  destruct HN as [env_rel [Hnil [i HNgen]]].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HNgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R1 [Ht1 He1]].
  destruct (HNgen _ _ HΓ' _ _ (rel_sub_zero_nil _ _ HΓ') _ _ _ _ Hρ
              (eval_sub_zero_nil _) (eval_sub_zero_nil _)) as [R2 [Ht2 He2]].
  destruct Ht1 as [a1 a2 a3 a4 Ha1 ? ? Ha4 Hty1].
  destruct Ht2 as [b1 b2 b3 b4 Hb1 ? ? Hb4 Hty2].
  destruct He1 as [v1 v2 v3 v4 Hv1 ? ? Hv4 Hc1].
  destruct He2 as [w1 w2 w3 w4 Hw1 ? ? Hw4 Hc2].
  rewrite HT in Ha1, Ha4, Hb1, Hb4.
  rewrite HNc in Hv1, Hv4, Hw1, Hw4.
  functional_eval_rewrite_clear.
  assert (Hm1 : DF a1 ≈ a1 ∈ per_univ_elem i ↘ R1) by pairwise.
  assert (Hm2 : DF a1 ≈ a1 ∈ per_univ_elem i ↘ R2) by pairwise.
  handle_per_univ_elem_irrel.
  exists R1; split.
  - apply (mk_rel_exp a1 a2 a3 a4); rewrite ?HT; assumption.
  - apply (mk_rel_exp w2 w2 v3 v4); rewrite ?HG, ?HNc; try (apply Hδ; assumption); try assumption.
    merge_rel_chain Hc1 Hc2 v1.
Qed.

(** A neutral: a closed [G] that evaluates anywhere to [⇑ a d], [a] the type at
    [nil]. *)
Lemma rel_exp_neut_nil : forall {GC : GCtx} T G i d,
    ⋅ ⊨ T : Type@i ->
    (forall σ, T[σ] = T) -> (forall σ, G[σ] = G) ->
    per_bot d d ->
    (forall ρ a, eval_exp gc_ctx T nil a -> eval_exp gc_ctx G ρ (⇑ a d)) ->
    ⋅ ⊨ G : T.
Proof.
  intros * HT HTc HG Hd Hev0.
  destruct (rel_exp_of_typ_inversion HT) as [env_rel [Hnil HTgen]].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_exp_implies_rel_typ (HTgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')) as [R1 Ht1].
  destruct (rel_exp_implies_rel_typ (HTgen _ _ HΓ' _ _ (rel_sub_zero_nil _ _ HΓ') _ _ _ _ Hρ
              (eval_sub_zero_nil _) (eval_sub_zero_nil _))) as [R2 Ht2].
  exists R1; split; [ exact Ht1 |].
  destruct Ht1 as [a1 a2 a3 a4 Ha1 ? ? Ha4 Hty1].
  destruct Ht2 as [b1 b2 b3 b4 Hb1 ? ? Hb4 Hty2].
  rewrite HTc in Ha1, Ha4, Hb1, Hb4.
  functional_eval_rewrite_clear.
  assert (Hm1 : DF a1 ≈ a1 ∈ per_univ_elem i ↘ R1) by pairwise.
  assert (Hm2 : DF a1 ≈ a1 ∈ per_univ_elem i ↘ R2) by pairwise.
  assert (Hb : DF b2 ≈ b2 ∈ per_univ_elem i ↘ R2) by pairwise.
  pose proof (per_bot_then_per_elem Hb Hd) as Hr.
  handle_per_univ_elem_irrel.
  apply (mk_rel_exp (⇑ b2 d) (⇑ b2 d) (⇑ b2 d) (⇑ b2 d)); rewrite ?HG; try (apply Hev0; assumption).
  cbn; repeat split; exact Hr.
Qed.

(** A constant of a global context its definition is valid at: unsealed and
    with a body, it is its body; otherwise it is a neutral. *)
Lemma const_sem : forall {GC : GCtx} c A oM b,
    gctx_closed gc_ctx -> gc_const gc_ctx c = Some (A, oM, b) ->
    (exists i, ⋅ ⊨ A : Type@i) -> (forall M, oM = Some M -> ⋅ ⊨ M : A) ->
    ⋅ ⊨ a_const c : A /\ (forall M, oM = Some M -> b = true -> ⋅ ⊨ a_const c ≈ M : A).
Proof.
  intros * Hc Hl [i HA] HM.
  destruct (gctx_closed_const_lookup _ _ _ _ _ Hc Hl) as [HsA HsM].
  assert (HcA : forall σ, A[σ] = A) by (intros; apply exp_closed_sub, HsA).
  assert (Hcc : forall σ, (a_const c)[σ] = a_const c) by reflexivity.
  assert (Hδ : forall M, oM = Some M -> b = true -> ⋅ ⊨ a_const c ≈ M : A).
  { intros M -> ->; cbn in HsM.
    eapply rel_exp_delta_nil; [ exact (HM _ eq_refl) | exact HcA | intros; apply exp_closed_sub, HsM | exact Hcc |].
    intros * Hev; eapply eval_exp_const_unfold; eassumption. }
  split; [| exact Hδ ].
  destruct b; [ destruct oM as [M |] |].
  - pose proof (Hδ M eq_refl eq_refl) as H.
    eapply rel_exp_under_ctx_trans; [ exact H | apply rel_exp_under_ctx_sym; exact H ].
  - eapply rel_exp_neut_nil with (d := d_glob c); [ exact HA | exact HcA | exact Hcc | |].
    + intros s; eexists; split; constructor.
    + intros * Hev; eapply eval_exp_const; [ eassumption | right; reflexivity | eassumption ].
  - eapply rel_exp_neut_nil with (d := d_glob c); [ exact HA | exact HcA | exact Hcc | |].
    + intros s; eexists; split; constructor.
    + intros * Hev; eapply eval_exp_const; [ eassumption | left; reflexivity | eassumption ].
Qed.

(** ** 3. The fundamental theorem along an embedding *)

Definition kctx Θ1 Γ : Prop :=
  forall Θ2, sem_emb Θ1 Θ2 -> @sem_ctx (gc_mk Θ2) Γ /\ @ctx_mt (gc_mk Θ2) Θ2 Γ.

Definition kexp_eq Θ1 Γ A M M' : Prop :=
  forall Θ2, sem_emb Θ1 Θ2 ->
    @sem_ctx (gc_mk Θ2) Γ /\ @ctx_mt (gc_mk Θ2) Θ2 Γ /\ @rel_exp_under_ctx (gc_mk Θ2) Γ A M M'.

Definition ksubtyp Θ1 Γ A A' : Prop :=
  forall Θ2, sem_emb Θ1 Θ2 ->
    @sem_ctx (gc_mk Θ2) Γ /\ @ctx_mt (gc_mk Θ2) Θ2 Γ /\ @subtyp_under_ctx (gc_mk Θ2) Γ A A'.

Definition kext Θ1 Γ Ψ Ψ' : Prop :=
  forall Θ2, sem_emb Θ1 Θ2 ->
    @rel_ext_under_ctx (gc_mk Θ2) Γ Ψ Ψ' /\
    @ctx_mt (gc_mk Θ2) Θ2 (Ψ ++ Γ) /\ @ctx_mt (gc_mk Θ2) Θ2 (Ψ' ++ Γ) /\
    @sem_ctx (gc_mk Θ2) Γ /\ @ctx_mt (gc_mk Θ2) Θ2 Γ.

Definition kunit Θ1 Γ U U' : Prop :=
  forall Θ2, sem_emb Θ1 Θ2 ->
    @rel_unit_under_ctx (gc_mk Θ2) Γ U U' /\
    @unit_mt (gc_mk Θ2) Θ2 Γ U /\ @unit_mt (gc_mk Θ2) Θ2 Γ U' /\
    @sem_ctx (gc_mk Θ2) Γ /\ @ctx_mt (gc_mk Θ2) Θ2 Γ.

Definition kmod Θ1 Γ H H' : Prop :=
  forall Θ2, sem_emb Θ1 Θ2 ->
    @rel_modexp_under_ctx (gc_mk Θ2) Γ H H' /\
    @sem_mt (gc_mk Θ2) Θ2 Γ H /\ @sem_mt (gc_mk Θ2) Θ2 Γ H' /\
    @sem_unf (gc_mk Θ2) Θ2 Γ H /\ @sem_unf (gc_mk Θ2) Θ2 Γ H' /\
    @sem_ctx (gc_mk Θ2) Γ /\ @ctx_mt (gc_mk Θ2) Θ2 Γ.

(** The member types and δ-reducts of the source, at the target. *)
Ltac to_target Hsub :=
  match type of Hsub with gc_sub ?S1 ?T1 =>
    repeat match goal with
    | Hm : member_type S1 ?G ?H ?c ?R |- _ =>
        lazymatch goal with
        | _ : member_type T1 G H c R |- _ => fail
        | _ => pose proof (proj1 (member_type_gc_sub _ _ Hsub) _ _ _ _ Hm)
        end
    | Hm : unit_member_type S1 ?G ?U ?c ?R |- _ =>
        lazymatch goal with
        | _ : unit_member_type T1 G U c R |- _ => fail
        | _ => pose proof (proj2 (member_type_gc_sub _ _ Hsub) _ _ _ _ Hm)
        end
    | Hm : member_unfold S1 ?G ?H ?x = ?M |- _ =>
        lazymatch goal with
        | _ : member_unfold T1 G H x = M |- _ => fail
        | _ => pose proof (member_unfold_emb _ _ _ _ _ _ Hsub Hm)
        end
    | Hm : gc_unit S1 ?fp = ?U |- _ =>
        lazymatch goal with
        | _ : gc_unit T1 fp = U |- _ => fail
        | _ => pose proof (gc_sub_unit _ _ _ _ Hsub Hm)
        end
    | Hm : gc_const S1 ?c = ?r |- _ =>
        lazymatch goal with
        | _ : gc_const T1 c = r |- _ => fail
        | _ => pose proof (gc_sub_const _ _ _ _ Hsub Hm)
        end
    end
  end.

Ltac kcase :=
  repeat match goal with IH : forall _, sem_emb _ _ -> _, He : sem_emb _ _ |- _ =>
    specialize (IH _ He) end;
  destruct_conjs.

(** The parts of a context extended by a self slot, in their members. *)
Lemma ctx_mt_self_inv : forall {GC : GCtx} Θm Γ Φ, ctx_mt Θm (self_ent Φ :: Γ) -> ctx_mt Θm Γ /\ body_mt Θm Γ Φ.
Proof.
  intros * H; inversion H as [| | | ? ? H1 H2]; subst.
  inversion H2; subst; split; assumption.
Qed.

Theorem kripke_fundamental :
  (forall Θ Γ, ⊢ Θ ⍮ Γ -> kctx Θ Γ) /\
  (forall Θ Γ A M, Θ ⍮ Γ ⊢ M : A -> kexp_eq Θ Γ A M M) /\
  (forall Θ Γ A M M', Θ ⍮ Γ ⊢ M ≈ M' : A -> kexp_eq Θ Γ A M M') /\
  (forall Θ Γ A A', Θ ⍮ Γ ⊢ A ⊆ A' -> ksubtyp Θ Γ A A') /\
  (forall Θ Γ Ψ Ψ', Θ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> kext Θ Γ Ψ Ψ') /\
  (forall Θ Γ U U', Θ ⍮ Γ ⊢ᵘ U ≈ U' -> kunit Θ Γ U U') /\
  (forall Θ Γ H H', Θ ⍮ Γ ⊢ᵐ H ≈ H' -> kmod Θ Γ H H').
Proof.
  apply syntactic_wf_mut_ind; unfold kctx, kexp_eq, ksubtyp, kext, kunit, kmod; intros;
    match goal with He : sem_emb _ _ |- _ =>
      pose proof (em_res _ _ (sme_emb _ _ He)) as Hsub;
      pose proof (em_wf _ _ (sme_emb _ _ He)) as Hwf2;
      pose proof (sme_gv _ _ He) as [HgC HgU]
    end;
    pose proof (wf_gctx_closed _ _ (wf_ctx_empty _ Hwf2)) as Hgm;
    kcase;
    to_target Hsub.
  (** Contexts. *)
  all: try solve [ split; constructor ].
  all: try solve [ split; [ eapply rel_ctx_extend'; eassumption | constructor; assumption ] ].
  all: try solve [ split; [ eapply rel_ctx_extend_def'; eassumption | constructor; assumption ] ].
  (** Terms whose case lemma predates modules. *)
  all: try (split; [ assumption | split; [ assumption |] ]).
  all: try solve [ apply valid_exp_typ; assumption | apply valid_exp_nat; assumption
    | apply valid_exp_zero; assumption
    | apply rel_exp_succ_cong; assumption
    | eapply rel_exp_natrec_cong; eassumption
    | apply valid_exp_True; assumption | apply valid_exp_False; assumption
    | apply valid_exp_true; assumption
    | eapply rel_exp_exfalso_cong; eassumption
    | apply rel_exp_true_eta; assumption
    | eapply rel_exp_pi_cong; eassumption
    | eapply rel_exp_fn_cong; eassumption
    | eapply rel_exp_app_cong; eassumption
    | eapply valid_exp_let; eassumption
    | eapply rel_exp_let_cong; eassumption
    | eapply rel_exp_let_zeta; eassumption
    | eapply rel_exp_pi_beta; eassumption
    | eapply rel_exp_nat_beta_zero; eassumption
    | eapply rel_exp_nat_beta_succ; eassumption
    | eapply rel_exp_eq_subtyp; eassumption
    | apply rel_exp_under_ctx_sym; assumption
    | eapply rel_exp_under_ctx_trans; eassumption
    | eapply subtyp_refl; eassumption
    | eapply subtyp_trans; eassumption
    | eapply subtyp_pi; eassumption
    | apply subtyp_univ; [assumption | lia] ].
  all: try solve [ eapply valid_exp_var; eassumption | eapply rel_exp_var_delta; eassumption ].
  (** Constants. *)
  all: try solve [
    match goal with HgC : forall c A M b, gc_const ?S c = _ -> VCs ?T _ _,
                    Hl : gc_const ?S ?c = Some _, Hl2 : gc_const ?T ?c = Some _, HΓ : sem_ctx _ |- _ =>
      destruct (HgC _ _ _ _ Hl) as [HA HM];
      destruct (@const_sem (gc_mk T) _ _ _ _ Hgm Hl2 HA HM) as [Hc1 Hc2];
      pose proof (gctx_closed_const_lookup _ _ _ _ _ Hgm Hl2) as [HsA HsM];
      first [ eapply closed_weaken_sem; [ exact HΓ | exact Hc1 | .. ]
            | eapply closed_weaken_sem; [ exact HΓ | exact (Hc2 _ eq_refl eq_refl) | .. ] ];
      solve [ reflexivity | apply exp_closed_wk; assumption ]
    end ].
  all: try solve [ eapply rel_exp_fn_eta; eassumption ].
  (** Module slots and local modules. *)
  all: try solve [ split; [ apply rel_ctx_extend_mod'; assumption | constructor; assumption ] ].
  all: try solve [ eapply valid_exp_let_mod; eassumption | eapply rel_exp_let_mod_cong; eassumption
                 | eapply rel_exp_let_mod_zeta; eassumption ].
  (** Members. *)
  all: try solve [ eapply rel_exp_mem_gen; [ exact Hgm | eassumption | eassumption
                 | eassumption | eassumption ] ].
  all: try solve [ eapply rel_exp_mem_delta; [ exact Hgm | eassumption | eassumption | eassumption
                 | eassumption | eassumption
                 | eassumption | eassumption ] ].
  all: try solve [ eapply valid_exp_mem_app; eassumption | eapply rel_exp_mem_app; eassumption ].
  all: try solve [
    match goal with HM : rel_exp_under_ctx _ _ (a_mem _ _) (a_mem _ _) |- _ =>
      destruct (presup_rel_exp_under_ctx HM) as [? ?];
      eapply rel_exp_mem_gen; [ exact Hgm | eassumption | eassumption
                              | eassumption | eassumption ] end ].
  (** Extensions. *)
  all: try solve [ split; [ apply rel_ext_nil; assumption | cbn [app]; repeat split; assumption ] ].
  all: try solve [ split; [ eapply rel_ext_ass; eassumption | cbn [app]; repeat split; try constructor; assumption ] ].
  all: try solve [ split; [ eapply rel_ext_def; eassumption | cbn [app]; repeat split; try constructor; assumption ] ].
  all: try solve [ split; [ eapply rel_ext_mod; eassumption | cbn [app]; repeat split; try constructor; assumption ] ].
  (** Units. *)
  all: try solve [ split; [ eapply rel_unit_nil; eassumption |];
                   split; [ constructor; constructor |]; split; [ constructor; constructor | split; assumption ] ].
  all: try solve [
    match goal with Hs : @ctx_mt _ _ (self_ent ?Φ :: ?D ++ ?G), Hs' : @ctx_mt _ _ (self_ent ?Φ' :: ?D' ++ ?G) |- _ =>
      destruct (ctx_mt_self_inv _ _ _ Hs) as [_ Hb]; destruct (ctx_mt_self_inv _ _ _ Hs') as [_ Hb'];
      split; [ eapply rel_unit_def; eassumption |];
      split; [ constructor; constructor; exact Hb |]; split; [ constructor; constructor; exact Hb' | split; assumption ]
    end ].
  all: try solve [
    match goal with Hs : @ctx_mt _ _ (self_ent ?Φ :: ?D ++ ?G), Hs' : @ctx_mt _ _ (self_ent ?Φ' :: ?D' ++ ?G) |- _ =>
      destruct (ctx_mt_self_inv _ _ _ Hs) as [_ Hb]; destruct (ctx_mt_self_inv _ _ _ Hs') as [_ Hb'];
      split; [ eapply rel_unit_mod; eassumption |];
      split; [ constructor; econstructor; eassumption |]; split; [ constructor; econstructor; eassumption | split; assumption ]
    end ].
  all: try solve [ split; [ eapply rel_unit_alias; eassumption |];
                   split; [ constructor; assumption |]; split; [ constructor; assumption | split; assumption ] ].
  all: try solve [ split; [ apply rel_unit_sym; assumption | repeat split; assumption ] ].
  all: try solve [ split; [ eapply rel_unit_trans; eassumption | repeat split; assumption ] ].
  (** Module expressions. *)
  all: try solve [
    match goal with Hl : gc_unit ?S1 ?fp = Some ?U, Hl2 : gc_unit ?T2 ?fp = Some ?U, HΓ : @sem_ctx (gc_mk ?T2) _ |- _ =>
      destruct (HgU _ _ Hl) as (HsU & HokU & HUU);
      split; [ exact (@rel_me_unit (gc_mk T2) _ _ _ Hl2 HUU HΓ) |];
      split; [ exact (@sem_mt_unit (gc_mk T2) _ Hgm _ _ _ Hl2 Hl2 HsU HokU HUU HΓ) |];
      split; [ exact (@sem_mt_unit (gc_mk T2) _ Hgm _ _ _ Hl2 Hl2 HsU HokU HUU HΓ) |];
      split; [ exact (@sem_unf_unit (gc_mk T2) _ Hgm _ _ _ Hl2 Hl2 HsU HokU HUU HΓ) |];
      split; [ exact (@sem_unf_unit (gc_mk T2) _ Hgm _ _ _ Hl2 Hl2 HsU HokU HUU HΓ) | split; assumption ] end ].
  all: try solve [
    match goal with Hl : _ ∋ # _ ⇒ₘ _, HΓ : sem_ctx _, Hok : ctx_mt _ _ |- _ =>
      split; [ exact (rel_me_var _ _ _ HΓ Hl) |];
      split; [ exact (sem_mt_var Hgm _ _ _ Hl HΓ Hok) |]; split; [ exact (sem_mt_var Hgm _ _ _ Hl HΓ Hok) |];
      split; [ exact (sem_unf_var Hgm _ _ _ Hl HΓ Hok) |]; split; [ exact (sem_unf_var Hgm _ _ _ Hl HΓ Hok) | split; assumption ] end ].
  all: try solve [
    match goal with HU : rel_unit_under_ctx _ ?U ?U', Hok : unit_mt _ _ ?U, Hok' : unit_mt _ _ ?U', HΓ : sem_ctx _ |- _ =>
      destruct HU as (HU & HsU & HsU');
      assert (Ht : tele_ass (gu_params U)) by (inversion HsU; subst; cbn; assumption);
      assert (Ht' : tele_ass (gu_params U')) by (inversion HsU'; subst; cbn; assumption);
      split; [ exact HU |];
      split; [ exact (sem_mt_lit _ _ HΓ HsU Hok) |]; split; [ exact (sem_mt_lit _ _ HΓ HsU' Hok') |];
      split; [ exact (sem_unf_lit _ _ Ht) |]; split; [ exact (sem_unf_lit _ _ Ht') | split; assumption ] end ].
  all: try solve [
    match goal with HH : rel_modexp_under_ctx _ ?H ?H', HS : sem_mt _ _ ?H, HS' : sem_mt _ _ ?H',
                    HU : sem_unf _ _ ?H, HU' : sem_unf _ _ ?H', Hm : member_type _ _ ?H (_ :: nil) (mr_mod _)
                    |- rel_modexp_under_ctx _ (me_mem _ _) _ /\ _ =>
      split; [ exact (rel_me_mem Hgm _ _ _ _ _ HH HS Hm) |];
      split; [ exact (sem_mt_mem _ _ _ HS) |]; split; [ exact (sem_mt_mem _ _ _ HS') |];
      split; [ exact (sem_unf_mem _ _ _ HU) |]; split; [ exact (sem_unf_mem _ _ _ HU') | split; assumption ] end ].
  all: try solve [
    match goal with HH : rel_modexp_under_ctx _ ?H ?H', HS : sem_mt _ _ ?H, HS' : sem_mt _ _ ?H',
                    HU : sem_unf _ _ ?H, HU' : sem_unf _ _ ?H',
                    Hm : member_type _ _ ?H nil (mr_mod ?T), Hv : tele_view ?T = Some (?B, _),
                    Hm' : member_type _ _ ?H' nil (mr_mod ?T'), Hv' : tele_view ?T' = Some (?B', _),
                    HN : rel_exp_under_ctx _ ?B ?N ?N', HN' : rel_exp_under_ctx _ ?B' ?N' ?N'
                    |- rel_modexp_under_ctx _ (me_app _ _) _ /\ _ =>
      pose proof Hm as Hm2;
      pose proof Hm' as Hm2';
      destruct (arity_pi _ _ _ _ _ HS Hm2 Hv) as (l & HB & _ & HA);
      destruct (arity_pi _ _ _ _ _ HS' Hm2' Hv') as (l' & HB' & _ & HA');
      pose proof (rel_modexp_refl_left HH) as HHl; pose proof (rel_modexp_refl_right HH) as HHr;
      pose proof (rel_exp_under_ctx_refl_left HN) as HNl;
      split; [ exact (rel_me_app Hgm _ _ _ _ _ _ _ _ _ HH HS Hm2 HA HN) |];
      split; [ exact (sem_mt_app Hgm _ _ _ _ _ _ _ HS HHl Hm2 HA HB HNl) |];
      split; [ exact (sem_mt_app Hgm _ _ _ _ _ _ _ HS' HHr Hm2' HA' HB' HN') |];
      split; [ exact (sem_unf_app Hgm _ _ _ _ _ _ _ HS HU HHl Hm2 HA HB HNl) |];
      split; [ exact (sem_unf_app Hgm _ _ _ _ _ _ _ HS' HU' HHr Hm2' HA' HB' HN') | split; assumption ] end ].
  all: try solve [ split; [ apply rel_modexp_sym; assumption | repeat (split; [ assumption |]); assumption ] ].
  all: try solve [ split; [ eapply rel_modexp_trans; eassumption | repeat (split; [ assumption |]); assumption ] ].
Qed.

(** ** 4. Valid global contexts *)

(** A judgment read at a target its source embeds soundly into. *)
Lemma kread : forall Θ Θ2 Γ A M,
    sem_emb Θ Θ2 -> Θ ⍮ Γ ⊢ M : A -> @rel_exp_under_ctx (gc_mk Θ2) Γ A M M.
Proof.
  intros * Hμ HM; destruct kripke_fundamental as (_ & Ke & _).
  destruct (Ke _ _ _ _ HM _ Hμ) as (_ & _ & H); exact H.
Qed.

Lemma VCs_of : forall Θ A oM Θ2, const_wf Θ A oM -> Good VCs VUs Θ -> Emb Θ Θ2 -> VCs Θ2 A oM.
Proof.
  intros * HM HG He.
  pose proof {| sme_emb := He; sme_gv := HG _ He |} as Hμ.
  destruct oM as [M |]; cbn in HM.
  - destruct (presup_exp_typ HM) as [i HA].
    split; [ exists i; exact (kread _ _ _ _ _ Hμ HA) | intros ? [= <-]; exact (kread _ _ _ _ _ Hμ HM) ].
  - destruct HM as [i HA].
    split; [ exists i; exact (kread _ _ _ _ _ Hμ HA) | discriminate ].
Qed.

Lemma VUs_of : forall Θ U Θ2, Θ ⍮ ⋅ ⊢ᵘ U ≈ U -> Good VCs VUs Θ -> Emb Θ Θ2 -> VUs Θ2 U.
Proof.
  intros * HU HG He.
  pose proof {| sme_emb := He; sme_gv := HG _ He |} as Hμ.
  destruct kripke_fundamental as (_ & _ & _ & _ & _ & Ku & _).
  destruct (Ku _ _ _ _ HU _ Hμ) as ((HUU & HsU & _) & Hok & _).
  split; [ exact HsU | split; [ exact Hok | exact HUU ] ].
Qed.

(** Every well-formed global context is semantically sound: the identity is a
    sound embedding. *)
Theorem gctx_sem : forall Θ, ⊢g Θ -> sem_emb Θ Θ.
Proof.
  intros * Hg; constructor; [ apply Emb_refl; exact Hg |].
  exact (global_induction VCs VUs VCs_of VUs_of _ Hg).
Qed.
