(** * The Global Rules: Validity along an Embedding

    A judgment of the global context [Θ1 ⍮ Ξ1] is valid at every [Θ2 ⍮ Ξ2] it
    embeds into, provided what resolves at [Θ1 ⍮ Ξ1] is valid at [Θ2 ⍮ Ξ2] and
    the modules of [Θ2 ⍮ Ξ2] are semantically valid ([sem_emb]).  Entries are
    closed and paths absolute, so an embedding moves nothing: the fundamental
    theorem holds in this form for every rule ([kripke_fundamental]), each case
    being the fixed-context case lemma at the target.  At the identity it is
    the fixed-context theorem. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import MemberLemmas GlobalModules.
From Mctt.Core.Completeness Require Import
  ContextCases FunctionCases LetCases NatCases SubstitutionCases SubtypingCases
  TrueFalseCases UniverseCases VariableCases LogicalRelation UnitCases InstanceCases
  MemberCases MemberTyping MemberReps MemberSem ModexpCases PathCases GlobalSem.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. Sound embeddings *)

Record sem_emb (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  { sme_emb : Emb Θ1 Ξ1 Θ2 Ξ2
  ; sme_glob : forall H mp x b pv A B Γ,
      mod_qname H = Some mp ->
      gc_resolve Θ1 Ξ1 (qname_app mp (x :: nil)) = Some (ge_def b pv A B) ->
      @sem_ctx (gc_mk Θ2 Ξ2) Γ ->
      @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A (a_mem H x) (a_mem H x)
  ; sme_unfold : forall H mp x A M Γ pv,
      mod_qname H = Some mp ->
      gc_resolve Θ1 Ξ1 (qname_app mp (x :: nil)) = Some (ge_def true pv A (Some M)) ->
      @sem_ctx (gc_mk Θ2 Ξ2) Γ ->
      @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A (a_mem H x) M
  ; sme_path : forall p r, gc_module Θ1 Ξ1 p = Some r -> @gpath_at (gc_mk Θ2 Ξ2) Θ2 Ξ2 p
  }.

(** ** 2. The fundamental theorem along an embedding *)

Definition kctx Θ1 Ξ1 Γ : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 -> @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θ2 Ξ2 Γ.

Definition kexp_eq Θ1 Ξ1 Γ A M M' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θ2 Ξ2 Γ /\ @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A M M'.

Definition ksubtyp Θ1 Ξ1 Γ A A' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θ2 Ξ2 Γ /\ @subtyp_under_ctx (gc_mk Θ2 Ξ2) Γ A A'.

Definition kext Θ1 Ξ1 Γ Ψ Ψ' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ Ψ Ψ' /\
    @ctx_mt (gc_mk Θ2 Ξ2) Θ2 Ξ2 (Ψ ++ Γ) /\ @ctx_mt (gc_mk Θ2 Ξ2) Θ2 Ξ2 (Ψ' ++ Γ) /\
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θ2 Ξ2 Γ.

Definition kunit Θ1 Ξ1 Γ U U' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 ->
    @rel_unit_under_ctx (gc_mk Θ2 Ξ2) Γ U U' /\
    @unit_mt (gc_mk Θ2 Ξ2) Θ2 Ξ2 Γ U /\ @unit_mt (gc_mk Θ2 Ξ2) Θ2 Ξ2 Γ U' /\
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θ2 Ξ2 Γ.

Definition kmod Θ1 Ξ1 Γ H H' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 ->
    @rel_modexp_under_ctx (gc_mk Θ2 Ξ2) Γ H H' /\
    @sem_mt (gc_mk Θ2 Ξ2) Θ2 Ξ2 Γ H /\ @sem_mt (gc_mk Θ2 Ξ2) Θ2 Ξ2 Γ H' /\
    @sem_unf (gc_mk Θ2 Ξ2) Θ2 Ξ2 Γ H /\ @sem_unf (gc_mk Θ2 Ξ2) Θ2 Ξ2 Γ H' /\
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θ2 Ξ2 Γ.

(** The member types and δ-reducts of the source, at the target. *)
Ltac to_target Hsub :=
  match type of Hsub with gc_sub ?S1 ?S2 ?T1 ?T2 =>
    repeat match goal with
    | Hm : member_type S1 S2 ?G ?H ?c ?R |- _ =>
        lazymatch goal with
        | _ : member_type T1 T2 G H c R |- _ => fail
        | _ => pose proof (proj1 (member_type_gc_sub _ _ _ _ Hsub) _ _ _ _ Hm)
        end
    | Hm : unit_member_type S1 S2 ?G ?U ?c ?R |- _ =>
        lazymatch goal with
        | _ : unit_member_type T1 T2 G U c R |- _ => fail
        | _ => pose proof (proj2 (member_type_gc_sub _ _ _ _ Hsub) _ _ _ _ Hm)
        end
    | Hm : member_unfold S1 S2 ?G ?H ?x = ?M |- _ =>
        lazymatch goal with
        | _ : member_unfold T1 T2 G H x = M |- _ => fail
        | _ => pose proof (member_unfold_emb _ _ _ _ _ _ _ _ Hsub Hm)
        end
    | Hm : member_unfold_ch S1 S2 ?G ?H ?c = ?M |- _ =>
        lazymatch goal with
        | _ : member_unfold_ch T1 T2 G H c = M |- _ => fail
        | _ => pose proof (member_unfold_gc_sub _ _ _ _ Hsub _ _ _ _ Hm)
        end
    end
  end.

Ltac kcase :=
  repeat match goal with IH : forall _ _, sem_emb _ _ _ _ -> _, He : sem_emb _ _ _ _ |- _ =>
    specialize (IH _ _ He) end;
  destruct_conjs.

Theorem kripke_fundamental :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> kctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> kexp_eq Θ Ξ Γ A M M) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> kexp_eq Θ Ξ Γ A M M') /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> ksubtyp Θ Ξ Γ A A') /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> kext Θ Ξ Γ Ψ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> kunit Θ Ξ Γ U U') /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> kmod Θ Ξ Γ H H').
Proof.
  apply syntactic_wf_mut_ind; unfold kctx, kexp_eq, ksubtyp, kext, kunit, kmod; intros;
    pose proof (em_res _ _ _ _ (sme_emb _ _ _ _ ltac:(eassumption))) as Hsub;
    pose proof (em_wf _ _ _ _ (sme_emb _ _ _ _ ltac:(eassumption))) as Hwf2;
    pose proof (gmod_ok_self _ _ Hwf2) as Hgm;
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
  all: try solve [ eapply sme_unfold; eassumption ].
  all: try solve [ eapply sme_glob; eassumption ].
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
  all: try solve [ split; [ eapply rel_unit_body; eassumption |];
                   split; [ constructor; rewrite <- app_assoc in *; assumption |];
                   split; [ constructor; rewrite <- app_assoc in *; assumption | split; assumption ] ].
  all: try solve [ split; [ eapply rel_unit_alias; eassumption |];
                   split; [ constructor; assumption |]; split; [ constructor; assumption | split; assumption ] ].
  all: try solve [ split; [ apply rel_unit_sym; assumption | repeat split; assumption ] ].
  all: try solve [ split; [ eapply rel_unit_trans; eassumption | repeat split; assumption ] ].
  (** Module expressions. *)
  all: try solve [
    match goal with He : sem_emb ?S1 ?S2 ?T1 ?T2, Hpm : mod_qname ?H = Some ?p,
                    Hm : member_type ?S1 ?S2 _ ?H nil (mr_mod _),
                    Hm2 : member_type ?T1 ?T2 _ ?H nil (mr_mod _), HΓ : sem_ctx _ |- _ =>
      rewrite (mod_qname_inv _ _ Hpm) in Hm, Hm2 |- *;
      destruct (member_type_path_module _ _ _ _ _ Hm) as [r Hr];
      pose proof (sme_path _ _ _ _ He _ _ Hr) as Hp;
      split; [ exact (rel_me_path _ _ _ Hp HΓ Hm2) |];
      split; [ exact (sem_mt_path Hgm _ _ Hp HΓ) |]; split; [ exact (sem_mt_path Hgm _ _ Hp HΓ) |];
      split; [ exact (sem_unf_path _ _ Hp) |]; split; [ exact (sem_unf_path _ _ Hp) | split; assumption ] end ].
  all: try solve [
    match goal with Hl : _ ∋ # _ ⇒ₘ _, HΓ : sem_ctx _, Hok : ctx_mt _ _ _ |- _ =>
      pose proof Hgm as (HGc & HGap & Hc);
      split; [ exact (rel_me_var _ _ _ HΓ Hl) |];
      split; [ exact (sem_mt_var HGc Hc _ _ _ Hl HΓ Hok) |]; split; [ exact (sem_mt_var HGc Hc _ _ _ Hl HΓ Hok) |];
      split; [ exact (sem_unf_var Hgm _ _ _ Hl HΓ Hok) |]; split; [ exact (sem_unf_var Hgm _ _ _ Hl HΓ Hok) | split; assumption ] end ].
  all: try solve [
    match goal with HU : rel_unit_under_ctx _ ?U ?U', Hok : unit_mt _ _ _ ?U, Hok' : unit_mt _ _ _ ?U', HΓ : sem_ctx _ |- _ =>
      destruct HU as (HU & HsU & HsU');
      assert (Ht : tele_ass (gu_params U)) by (inversion HsU; subst; cbn; assumption);
      assert (Ht' : tele_ass (gu_params U')) by (inversion HsU'; subst; cbn; assumption);
      split; [ exact HU |];
      split; [ exact (sem_mt_lit _ _ HΓ HsU Hok) |]; split; [ exact (sem_mt_lit _ _ HΓ HsU' Hok') |];
      split; [ exact (sem_unf_lit _ _ Ht) |]; split; [ exact (sem_unf_lit _ _ Ht') | split; assumption ] end ].
  all: try solve [
    match goal with HH : rel_modexp_under_ctx _ ?H ?H', HS : sem_mt _ _ _ ?H, HS' : sem_mt _ _ _ ?H',
                    HU : sem_unf _ _ _ ?H, HU' : sem_unf _ _ _ ?H', Hm : member_type _ _ _ ?H (_ :: nil) (mr_mod _)
                    |- rel_modexp_under_ctx _ (me_mem _ _) _ /\ _ =>
      split; [ exact (rel_me_mem Hgm _ _ _ _ _ HH HS Hm) |];
      split; [ exact (sem_mt_mem _ _ _ HS) |]; split; [ exact (sem_mt_mem _ _ _ HS') |];
      split; [ exact (sem_unf_mem _ _ _ HU) |]; split; [ exact (sem_unf_mem _ _ _ HU') | split; assumption ] end ].
  all: try solve [
    match goal with HH : rel_modexp_under_ctx _ ?H ?H', HS : sem_mt _ _ _ ?H, HS' : sem_mt _ _ _ ?H',
                    HU : sem_unf _ _ _ ?H, HU' : sem_unf _ _ _ ?H',
                    Hm : member_type _ _ _ ?H nil (mr_mod ?T), Hv : tele_view ?T = Some (?B, _),
                    Hm' : member_type _ _ _ ?H' nil (mr_mod ?T'), Hv' : tele_view ?T' = Some (?B', _),
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

(** ** 3. Closed judgments *)

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

(** ** Globals from the validity of their types and bodies

    The δ-rule evaluates the generalized body in the empty environment, and a
    global or parameter is a neutral annotated with its type evaluated there.
    [nil] is reached by [sb_zero], which evaluates to [nil] in any environment (a
    list environment reads [zeroᵈ] past its end), so instantiating a [⋅] judgment
    at [sb_zero] relates the value at [nil] to the value anywhere. *)

(** δ: a closed term [G] that evaluates anywhere to what [N] evaluates to at
    [nil] is equal to [N]. *)
Lemma rel_exp_delta_nil : forall {GC : GCtx} T N G,
    ⋅ ⊨ N : T ->
    (forall σ, T[σ] = T) -> (forall σ, N[σ] = N) -> (forall σ, G[σ] = G) ->
    (forall ρ m, eval_exp gc_deps gc_stack N nil m -> eval_exp gc_deps gc_stack G ρ m) ->
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
    (forall ρ a, eval_exp gc_deps gc_stack T nil a -> eval_exp gc_deps gc_stack G ρ (⇑ a d)) ->
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

(** ** 4. The PER model's notion of a valid entry *)

Definition sem_entry (Θ : gdeps) (Ξ : gstack) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B =>
      (exists i, @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (Type@i) A A) /\
      (forall M, B = Some M -> @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ A M M)
  | ge_mod _ _ => True
  end.

Section Raw.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢g Θ ⍮ Ξ.

  Lemma glob_sem_of_raw : forall mp x b pv A B,
      gc_resolve Θ Ξ (qname_app mp (x :: nil)) = Some (ge_def b pv A B) ->
      sem_entry Θ Ξ (ge_def b pv A B) ->
      @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ A (a_mem (qname_mod mp) x) (a_mem (qname_mod mp) x) /\
      (forall M, b = true -> B = Some M ->
         @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ A (a_mem (qname_mod mp) x) M).
  Proof.
    intros mp x b pv A B Hr HRp.
    assert (Hb : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    destruct (wf_gc_resolve_closed _ _ _ _ _ _ _ _ Hb Hr) as [HsT HsB].
    destruct HRp as [[i HT] HM].
    assert (Hc : forall σ, (a_mem (qname_mod mp) x)[σ] = a_mem (qname_mod mp) x)
      by (intros; cbn; rewrite (mod_qname_sub _ _ _ (qname_mod_qname mp)); reflexivity).
    assert (Hp : forall ρ, eval_modexp Θ Ξ (qname_mod mp) ρ (dm_global mp nil))
      by (intros; apply eval_path_mod, (gc_chain_no_alias _ _ Hg); right; right; eauto).
    assert (Hdelta : forall M, b = true -> B = Some M ->
               @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ A (a_mem (qname_mod mp) x) M).
    { intros M -> ->; cbn in HsB.
      eapply rel_exp_delta_nil; [ apply HM; reflexivity | | | exact Hc |].
      - intros; eapply exp_closed_sub; eassumption.
      - intros; eapply exp_closed_sub; eassumption.
      - intros * Hev; eapply eval_mem_of_sel; [ apply Hp | eapply eval_sel_global; [ exact Hr | exact Hev | constructor ] ]. }
    split; [| exact Hdelta ].
    destruct b; [ destruct B as [M |] |].
    - pose proof (Hdelta M eq_refl eq_refl) as H.
      eapply rel_exp_under_ctx_trans; [ exact H | apply rel_exp_under_ctx_sym; exact H ].
    - eapply rel_exp_neut_nil with (d := d_glob (qname_app mp (x :: nil))); [ exact HT | | exact Hc | |].
      + intros; eapply exp_closed_sub; eassumption.
      + intros s; eexists; split; constructor.
      + intros * Hev; eapply eval_mem_of_sel; [ apply Hp | eapply eval_sel_global_neut; [ exact Hr | right; reflexivity | exact Hev | constructor ] ].
    - eapply rel_exp_neut_nil with (d := d_glob (qname_app mp (x :: nil))); [ exact HT | | exact Hc | |].
      + intros; eapply exp_closed_sub; eassumption.
      + intros s; eexists; split; constructor.
      + intros * Hev; eapply eval_mem_of_sel; [ apply Hp | eapply eval_sel_global_neut; [ exact Hr | left; reflexivity | exact Hev | constructor ] ].
  Qed.
End Raw.

(** ** 5. Valid global contexts *)

(** What an entry other than a body module is worth at [Θ2 ⍮ Ξ2]: a
    definition, checked over [T], is valid at [⋅] and its type over [T]; an
    alias is a valid closed unit. *)
Definition sem_V (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B =>
      (exists i, @rel_exp_under_ctx (gc_mk Θ2 Ξ2) ⋅ (Type@i) A A) /\
      (forall M, B = Some M -> @rel_exp_under_ctx (gc_mk Θ2 Ξ2) ⋅ A M M) /\
      (exists A0 i, A = ctx_pi T A0 /\ @rel_exp_under_ctx (gc_mk Θ2 Ξ2) T (Type@i) A0 A0)
  | ge_mod _ U =>
      @sem_unit (gc_mk Θ2 Ξ2) ⋅ U /\ @unit_mt (gc_mk Θ2 Ξ2) Θ2 Ξ2 ⋅ U /\
      @rel_modexp_under_ctx (gc_mk Θ2 Ξ2) ⋅ (me_lit U) (me_lit U)
  end.

(** The telescope of a module. *)
Definition sem_F (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) : Prop :=
  @sem_ctx (gc_mk Θ2 Ξ2) T /\ tele_ass T.

Lemma sgood_tele : forall Θ Ξ Θ2 Ξ2, GoodV sem_V sem_F Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 -> tele_ass (gs_tele Ξ).
Proof.
  intros * HG He; destruct (HG _ _ He) as [_ HΞ].
  destruct Ξ as [| [mp U] Ξ]; [ constructor | exact (proj2 (proj1 HΞ)) ].
Qed.

(** A sound embedding, from the validity of what the source files and has
    open. *)
Theorem sem_emb_of : forall Θ Ξ Θ2 Ξ2,
    ⊢g Θ ⍮ Ξ -> GoodV sem_V sem_F Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 -> sem_emb Θ Ξ Θ2 Ξ2.
Proof.
  intros * Hg HG He; pose proof He as [Hg2 Hs].
  assert (Hglob : forall mp x b pv A B, gc_resolve Θ Ξ (qname_app mp (x :: nil)) = Some (ge_def b pv A B) ->
             @rel_exp_under_ctx (gc_mk Θ2 Ξ2) ⋅ A (a_mem (qname_mod mp) x) (a_mem (qname_mod mp) x) /\
             (forall M, b = true -> B = Some M -> @rel_exp_under_ctx (gc_mk Θ2 Ξ2) ⋅ A (a_mem (qname_mod mp) x) M)).
  { intros * Hr.
    destruct (good_resolve _ _ _ _ _ _ _ _ HG He Hr) as (T & HA & HM & _).
    exact (glob_sem_of_raw _ _ Hg2 _ _ _ _ _ _ (gc_sub_resolve _ _ _ _ _ _ Hs Hr) (conj HA HM)). }
  constructor; [ exact He | | |].
  - intros * Hpm Hr HΓ.
    rewrite (mod_qname_inv _ _ Hpm).
    eapply closed_weaken_sem; [ eassumption | | apply exp_wk_id | apply exp_wk_id | apply exp_wk_id ].
    exact (proj1 (Hglob _ _ _ _ _ _ Hr)).
  - intros * Hpm Hr HΓ.
    rewrite (mod_qname_inv _ _ Hpm).
    eapply closed_weaken_sem; [ eassumption | | apply exp_wk_id | apply exp_wk_id | apply exp_wk_id ].
    exact (proj2 (Hglob _ _ _ _ _ _ Hr) _ eq_refl eq_refl).
  - intros p r Hr.
    apply (@gpath_ok (gc_mk Θ2 Ξ2) Θ Ξ Θ2 Ξ2 Hg Hs Hg2 (gc_sub_refl _ _) (gmod_ok_self _ _ Hg2) Hg2) with (r := r);
      [| | exact Hr ].
    + intros qp T Φ Hb.
      destruct (good_body _ _ _ _ _ _ _ _ _ HG He Hb) as [[HT HU] Hv].
      split; [ exact HT |]; split; [ exact HU |].
      intros * Hz.
      destruct (gm_valid_def _ _ _ _ _ _ _ _ _ _ _ Hv Hz) as (_ & _ & HA0).
      split; [ exact HA0 |].
      assert (Hne : z :: nil <> nil) by discriminate.
      refine (proj1 (Hglob _ _ b pv _ B _)).
      rewrite (proj2 (proj2 (closed_read _ _ Hg _ _ _ Hb (z :: nil))) Hne); exact Hz.
    + intros qp y U Hy.
      destruct (good_alias _ _ _ _ _ _ _ _ _ HG He Hy) as (T & pvT & HV); exact HV.
Qed.

(** A judgment read at a target its source embeds soundly into. *)
Lemma kread : forall Θ Ξ Θ2 Ξ2 Γ A M,
    sem_emb Θ Ξ Θ2 Ξ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A M M.
Proof.
  intros * Hμ HM; destruct kripke_fundamental as (_ & Ke & _).
  destruct (Ke _ _ _ _ _ HM _ _ Hμ) as (_ & _ & H); exact H.
Qed.

Lemma sem_V_def : forall Θ Ξ A M b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A -> GoodV sem_V sem_F Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    sem_V Θ2 Ξ2 (gs_tele Ξ) (ge_def b pv (ctx_pi (gs_tele Ξ) A) (Some (ctx_fn (gs_tele Ξ) M))).
Proof.
  intros * HM HG He.
  pose proof (sem_emb_of _ _ _ _ (ctx_wf_gctx _ _ _ (presup_exp_ctx HM)) HG He) as Hμ.
  destruct (presup_exp_typ HM) as [i HA].
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  split; [ exists j; exact (kread _ _ _ _ _ _ _ Hμ HT) |].
  split; [ intros ? [= <-]; exact (kread _ _ _ _ _ _ _ Hμ (ctx_fn_wf0 _ _ _ _ _ _ HA HM)) |].
  exists A, i; split; [ reflexivity | exact (kread _ _ _ _ _ _ _ Hμ HA) ].
Qed.

Lemma sem_V_ax : forall Θ Ξ A i b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Type@i -> GoodV sem_V sem_F Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    sem_V Θ2 Ξ2 (gs_tele Ξ) (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
Proof.
  intros * HA HG He.
  pose proof (sem_emb_of _ _ _ _ (ctx_wf_gctx _ _ _ (presup_exp_ctx HA)) HG He) as Hμ.
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  split; [ exists j; exact (kread _ _ _ _ _ _ _ Hμ HT) |].
  split; [ discriminate |].
  exists A, i; split; [ reflexivity | exact (kread _ _ _ _ _ _ _ Hμ HA) ].
Qed.

Lemma sem_V_alias : forall Θ Ξ pv Δ E Θ2 Ξ2,
    tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    GoodV sem_V sem_F Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    sem_V Θ2 Ξ2 (gs_tele Ξ) (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))).
Proof.
  intros * HΔ _ HE HG He.
  pose proof (sem_emb_of _ _ _ _ (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HE)) HG He) as Hμ.
  destruct kripke_fundamental as (_ & _ & _ & _ & _ & _ & Km).
  destruct (Km _ _ _ _ _ HE _ _ Hμ) as (HEv & HS & _ & _ & _ & HC & _).
  assert (Ht : tele_ass (Δ ++ gs_tele Ξ)) by (apply Forall_app; split; [ exact HΔ | exact (sgood_tele _ _ _ _ HG He) ]).
  rewrite <- (app_nil_r (Δ ++ gs_tele Ξ)) in HEv, HS, HC.
  assert (Hx : @rel_ext_under_ctx (gc_mk Θ2 Ξ2) ⋅ (Δ ++ gs_tele Ξ) (Δ ++ gs_tele Ξ))
    by (split; [| split ]; [ exact HC | exact HC | exact (sem_ctx_per_ctx HC) ]).
  destruct (rel_unit_alias Hx Ht Ht HEv HEv) as (HU & HsU & _).
  split; [ exact HsU |]; split; [ constructor; exact HS | exact HU ].
Qed.

Lemma sem_F_nil : forall Θ Ξ Δ Θ2 Ξ2,
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ -> GoodV sem_V sem_F Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    sem_F Θ2 Ξ2 (Δ ++ gs_tele Ξ).
Proof.
  intros * HΔ HC HG He.
  pose proof (sem_emb_of _ _ _ _ (ctx_wf_gctx _ _ _ HC) HG He) as Hμ.
  destruct kripke_fundamental as (Kc & _).
  split; [ exact (proj1 (Kc _ _ _ HC _ _ Hμ)) |].
  apply Forall_app; split; [ exact HΔ | exact (sgood_tele _ _ _ _ HG He) ].
Qed.

(** Every well-formed global context is semantically sound: the identity is a
    sound embedding. *)
Theorem gctx_sem : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> sem_emb Θ Ξ Θ Ξ.
Proof.
  intros * Hg; apply sem_emb_of; [ exact Hg | | apply Emb_refl; exact Hg ].
  exact (global_valid sem_V sem_F sem_V_def sem_V_ax sem_V_alias sem_F_nil _ _ Hg).
Qed.
