(** * The Global Rules in the Gluing Model

    The soundness counterpart of [Core/Completeness/ModuleCases.v]: a judgment
    of [Θ1 ⍮ Ξ1] glues at every [Θ2 ⍮ Ξ2] it embeds into, provided what
    [Θ1 ⍮ Ξ1] stores glues there ([glu_emb]): the declarations of its
    inductive types, and the members of its stored bodies that have no
    δ-reduct, its axioms and abstract definitions read bare, as neutrals.
    An embedding moves nothing, so the fundamental theorem holds in this
    form for contexts and typing ([kglu_fundamental]), each case being the
    fixed-context one at the target.  Module values are not glued: a member
    with a δ-reduct glues as the reduct, which [wf_mem] premises typed, and
    one without is the filed member its module expression is equal to
    ([mem_alias_filed]).  The subtyping premise of subsumption is moved
    syntactically ([emb_preserves_wf]).  Every well-formed global context
    glues ([gctx_glu]): the validity of each entry where it is checked
    ([global_valid]) is that the type of a definition glues. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import MemberLemmas GlobalModules GlobalPaths DescTyping LookupSound.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases ModuleSem ModuleCases GlobalSem.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Soundness Require Import LevelCases.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases TermStructureCases MemberCases
  SubtypingCases UniverseCases FunctionCases LetCases TrueFalseCases IndCases.
From Mctt.Core.Completeness Require IndCases.
Require Import Mctt.Core.Soundness.IndElimCases.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. Sound embeddings *)

(** [Θ1 ⍮ Ξ1] embeds soundly into [Θ2 ⍮ Ξ2]: it grows into it, its
    declarations glue there, and so does a member of one of its stored
    bodies that is an axiom or an abstract definition, at its stored type. *)
Record glu_emb (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  { gme_emb : Emb Θ1 Ξ1 Θ2 Ξ2
  ; gme_ind : forall p D, ind_lookup Θ1 Ξ1 p = Some D -> @glu_core (gc_mk Θ2 Ξ2) D
  ; gme_glob : forall p T Φ x Φ0 b pv A oM Γ,
      loc Θ1 Ξ1 p T Φ ->
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x (ge_def b pv A oM)) ->
      (if b then oM else None) = None ->
      @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ ->
      @glu_rel_exp (gc_mk Θ2 Ξ2) Γ (a_mem (qname_mod p) x) A
  }.

(** ** 2. Kripke gluing *)

Definition kglu_ctx Θ1 Ξ1 Γ : Prop :=
  forall Θ2 Ξ2, glu_emb Θ1 Ξ1 Θ2 Ξ2 -> @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ.

Definition kglu_exp Θ1 Ξ1 Γ M A : Prop :=
  forall Θ2 Ξ2, glu_emb Θ1 Ξ1 Θ2 Ξ2 -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ M A.

(** A universe, as its two cases: large, or small at a level that glues. *)
Definition kglu_univ Θ1 Ξ1 Γ U : Prop :=
  forall Θ2 Ξ2, glu_emb Θ1 Ξ1 Θ2 Ξ2 ->
    @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ /\
    ((exists i, U = Typeω@i) \/ (exists L n, U = Type⟨L⟩ /\ @glu_rel_exp (gc_mk Θ2 Ξ2) Γ L (Level@n))).

(** ** 3. Closed gluing at [⋅] weakens to every glued context

    Simpler than [closed_weaken_sem]: [nil_glu_sub_pred] does not constrain
    the environment, and the terms are the same, so no closedness is needed. *)

Section Weaken.
  Context {GC : GCtx}.
  Import Fixed_Notations.

  Lemma wf_sub_nil : forall Δ σ, ⊢ Δ -> Δ ⊢ˢ σ : ⋅.
  Proof.
    intros * HΔ; constructor; [ exact HΔ | apply wf_ctx_empty; eapply ctx_wf_gctx; exact HΔ | | |];
      intros * Hx; inversion Hx.
  Qed.

  Lemma glu_rel_exp_nil_weaken : forall Γ N T, ⊩ Γ -> ⋅ ⊩ N : T -> Γ ⊩ N : T.
  Proof.
    intros * [SbΓ HΓ] [Sb0 [H0 [i Hi]]].
    exists SbΓ; split; [ exact HΓ |]; exists i; intros Δ σ ρ Hσ.
    apply Hi.
    inversion H0 as [Sb' Heq Hg | | |]; subst.
    apply (Heq Δ σ ρ); cbn.
    apply wf_sub_nil, (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape HΓ _ _ _ Hσ)).
  Qed.

  (** A type a glued context ends with is glued. *)
  Lemma glu_rel_typ_of_ctx_ext : forall Γ A, ⊩ Γ ▹ A -> exists i : nat, Γ ⊩ A : Typeω@i.
  Proof.
    intros * [Sb HS].
    assert (HΓ : exists TSb, EG Γ ∈ glu_ctx_env ↘ TSb) by (inversion HS; subst; eexists; eassumption).
    destruct HΓ as [TSb HΓ].
    destruct (glu_ctx_env_cons_clean_inversion HΓ HS) as (i & _ & HAs & _).
    exists i, TSb; split; [ exact HΓ |]; exists (S i); intros Δ σ ρ Hσ.
    exact (glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub (glu_ctx_env_sub_escape HΓ _ _ _ Hσ) (HAs _ _ _ Hσ)).
  Qed.
End Weaken.


(** ** 4. The cases of the inductive types, at the target *)

Lemma k_decl : forall Θ Ξ Θ2 Ξ2 Γ p D, glu_emb Θ Ξ Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D ->
    ind_lookup Θ2 Ξ2 p = Some D /\ @glu_core (gc_mk Θ2 Ξ2) D /\ decl_closed D /\ ind_sort_univ (ind_sort D) /\
    decl_typed Θ2 Ξ2 D.
Proof.
  intros * He HΓ Hl.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [Hdt Hc].
  pose proof (decl_typed_emb _ _ _ _ _ (gme_emb _ _ _ _ He) Hdt) as Hdt2.
  pose proof Hdt as (_ & _ & _ & _ & Hsu & _).
  pose proof (ind_lookup_gc_sub _ _ _ _ _ _ (em_res _ _ _ _ (gme_emb _ _ _ _ He)) Hl) as Hl2.
  split; [ exact Hl2 | split; [ exact (gme_ind _ _ _ _ He _ _ Hl) | split; [ exact Hc | split; [ exact Hsu | exact Hdt2 ] ] ] ].
Qed.

Lemma k_ind : forall Θ Ξ Θ2 Ξ2 Γ p D, glu_emb Θ Ξ Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D ->
    @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ (a_ind p) (ind_ty D).
Proof.
  intros * He HΓ Hl HΓ2.
  destruct (k_decl _ _ _ _ _ _ _ He HΓ Hl) as (Hl2 & HG & Hc & Hsu & Hdt2).
  apply (@glu_rel_exp_nil_weaken (gc_mk Θ2 Ξ2)); [ exact HΓ2 |].
  eapply (@glu_rel_exp_ind0 (gc_mk Θ2 Ξ2)); eassumption.
Qed.

Lemma k_con : forall Θ Ξ Θ2 Ξ2 Γ p D c gs (i : nat), glu_emb Θ Ξ Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs ->
    @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ -> @glu_rel_ctx (gc_mk Θ2 Ξ2) (cargs_ctx p D gs ++ ind_params D) ->
    (forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
       forall Θ0 Ξ0, glu_emb Θ Ξ Θ0 Ξ0 ->
       @glu_rel_ctx (gc_mk Θ0 Ξ0) ((sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D)
                                    ▹ ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t))) ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ con_ty p D gs : Typeω@i -> @glu_rel_exp (gc_mk Θ2 Ξ2) ⋅ (con_ty p D gs) (Typeω@i) ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) Γ (a_con p c) (con_ty p D gs).
Proof.
  intros * He HΓ Hl Hcon HΓ2 HΨ2 Hsh Hty HTy.
  assert (HshV : forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
       exists j : nat, @glu_rel_exp (gc_mk Θ2 Ξ2)
         (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D)
         (ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t)) (Typeω@j))
    by (intros * Heq Hk; apply (@glu_rel_typ_of_ctx_ext (gc_mk Θ2 Ξ2)); exact (Hsh _ _ _ _ Heq Hk _ _ He)).
  destruct (k_decl _ _ _ _ _ _ _ He HΓ Hl) as (Hl2 & HG & Hc & Hsu & Hdt2).
  pose proof (sme_ind _ _ _ _ (gctx_sem _ _ (em_wf _ _ _ _ (gme_emb _ _ _ _ He))) p D Hl2) as HDc.
  apply (@glu_rel_exp_nil_weaken (gc_mk Θ2 Ξ2)); [ exact HΓ2 |].
  eapply (@glu_rel_exp_con0 (gc_mk Θ2 Ξ2)); eassumption.
Qed.

Lemma k_elim : forall Θ Ξ Θ2 Ξ2 Γ p D Ps M nm A (i : nat) Bs,
    glu_emb Θ Ξ Θ2 Ξ2 -> ind_lookup Θ Ξ p = Some D -> List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       forall Θ0 Ξ0, glu_emb Θ Ξ Θ0 Ξ0 -> @glu_rel_exp (gc_mk Θ0 Ξ0) Γ P T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : apps (a_ind p) Ps -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ M (apps (a_ind p) Ps) ->
    nm = S (ind_nn D) ->
    Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊢ A : Typeω@i ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) (elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ) A (Typeω@i) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D (List.firstn (ind_nu D) Ps) ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
       Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> forall Θ0 Ξ0, glu_emb Θ Ξ Θ0 Ξ0 ->
       @glu_rel_exp (gc_mk Θ0 Ξ0) (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) B (elim_bty p D c gs A (List.firstn (ind_nu D) Ps))) ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) Γ (a_elim nm A Bs M) (A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)]).
Proof.
  intros * He Hl HPl HPt HPg HMt HMg Hnm HAt HAg HMx Hn HBx Hk HBt HBg.
  destruct (presup_exp HMt) as [HΓ _].
  destruct (k_decl _ _ _ _ _ _ _ He HΓ Hl) as (Hl2 & HG & Hc & Hsu & Hdt2).
  pose proof (sme_ind _ _ _ _ (gctx_sem _ _ (em_wf _ _ _ _ (gme_emb _ _ _ _ He))) p D Hl2) as HDc.
  destruct (emb_preserves_wf _ _ _ _ (gme_emb _ _ _ _ He)) as (_ & Hwe & _ & _ & Hwx & _).
  eapply (@glu_rel_exp_elim (gc_mk Θ2 Ξ2)); try eassumption; eauto.
Qed.

(** A term equal to one that glues glues, the equation moved to the target. *)
Lemma k_of_eq : forall Θ Ξ Θ2 Ξ2 Γ M N A,
    glu_emb Θ Ξ Θ2 Ξ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ N : A -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ N A -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ M A.
Proof.
  intros * He Heq Hg.
  destruct (emb_preserves_wf _ _ _ _ (gme_emb _ _ _ _ He)) as (_ & _ & Hwq & _).
  eapply (@glu_rel_exp_of_eq (gc_mk Θ2 Ξ2)); [ exact Hg | exact (Hwq _ _ _ _ Heq) ].
Qed.

(** ** 5. Members *)

Lemma ds_ats_term_none : forall Ns A R, ds_ats (ds_term A None) Ns = Some R -> exists A', R = ds_term A' None.
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha; [ injection Ha as <-; eauto |].
  destruct (pi_view A) as [[? ?] |]; [ exact (IH _ _ Ha) | discriminate ].
Qed.

(** A member looked up as a term of no δ-reduct is an axiom or an abstract
    definition of a stored body, read bare: the module expression's module
    part is the body's path at no argument and no outside parameter. *)
Lemma mem_no_red : forall Θ Ξ Γ H x R A,
    mdenote Θ Ξ Γ (me_mem H x) R -> ds_ty Θ Ξ R = Some A -> ds_red R = None ->
    exists R0 p T Φ Φ0 b pv oM,
      mdenote Θ Ξ Γ H R0 /\ ds_mod Θ Ξ R0 = Some (ds_closed nil p T Φ nil) /\
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x (ge_def b pv A oM)) /\ (if b then oM else None) = None.
Proof.
  intros * Hm Ht Hr.
  assert (HR : R = ds_term A None)
    by (destruct R as [A' om | | | ]; cbn in Ht, Hr; try discriminate; subst; congruence).
  subst R.
  inversion Hm as [| | | | ? ? ? R0 R0m Γy E rd Re ? Hm0 Hmd He Hed Hrd]; subst.
  destruct R0m as [| Δ Φw Φx | Θ' p T Φ Ns |]; cbn in He; try discriminate.
  - (* an open body reads only transparent definitions and modules *)
    destruct (gm_prefix_upto Φx x) as [[| Φ' y E0 | ? ? ?] |]; try discriminate.
    destruct E0 as [[] pv A' [M |] | pv U | | ]; try discriminate; injection He as <- <- <-.
    + inversion Hed; subst; cbn in Hrd.
      destruct (gm_fill Φ'); cbn in Hrd; discriminate.
    + inversion Hed; subst.
      match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hmm end.
      cbn in Hrd; destruct (gm_fill Φ'); cbn in Hrd; [| discriminate ].
      injection Hrd as Heq; destruct Re; cbn in Hmm, Heq; try contradiction; discriminate.
  - destruct (gm_prefix_upto Φ x) as [[| Φ0 y E0 | ? ? ?] |] eqn:Hp; try discriminate.
    injection He as <- <- <-.
    pose proof (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & _).
    cbn [ds_read] in Hrd; destruct (ds_ats Re Ns) as [R1 |] eqn:Hats; cbn [option_map] in Hrd; [| discriminate ].
    injection Hrd as Heq.
    destruct E0 as [b pv A' oM | pv [Δ [sm Φy | E'] ] | pv pq D ΦD | pv Δa pq Nsa ].
    + (* a definition: one of no body, read bare *)
      cbn [ge_read] in Hed; inversion Hed; subst.
      destruct (if b then oM else None) as [M |] eqn:Ho.
      * exfalso; destruct (ds_ats_some_red _ _ _ _ Hats) as (A1 & M1 & ->).
        rewrite ds_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
      * destruct (ds_ats_term_none _ _ _ Hats) as (A1 & ->).
        destruct (ds_named_term_none Θ' Ns (apps (a_mem (qname_mod p) x) Ns) A1) as [(Hn & -> & ->) | Hn];
          rewrite Hn in Heq; cbn in Heq; [| discriminate ].
        cbn in Hats; injection Hats as ->; injection Heq as ->.
        exists R0, p, T, Φ, Φ0, b, pv, oM; repeat split; assumption.
    + exfalso; assert (Hmm : ds_is_mod Re) by (destruct sm; cbn [ge_read] in Hed; inversion Hed; subst; eapply udenote_is_mod; eassumption).
      pose proof (ds_ats_is_mod _ _ _ Hmm Hats) as Hm1.
      destruct R1; cbn in Hm1; try contradiction; rewrite ds_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + exfalso; assert (Hmm : ds_is_mod Re) by (cbn [ge_read] in Hed; inversion Hed; subst; eapply udenote_is_mod; eassumption).
      pose proof (ds_ats_is_mod _ _ _ Hmm Hats) as Hm1.
      destruct R1; cbn in Hm1; try contradiction; rewrite ds_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + exfalso; cbn [ge_read] in Hed; inversion Hed; subst.
      destruct (ds_ats_ind _ _ _ _ _ Hats) as (? & ? & ->).
      rewrite ds_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + exfalso; cbn [ge_read] in Hed; inversion Hed; subst.
      destruct (ds_ats_ind _ _ _ _ _ Hats) as (? & ? & ->).
      rewrite ds_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
Qed.

(** A member glues: as its δ-reduct, which glues by the premise of [wf_mem];
    without one, as the filed member it is equal to. *)
Lemma k_mem : forall Θ Ξ Θ2 Ξ2 Γ H x R A,
    glu_emb Θ Ξ Θ2 Ξ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ (me_mem H x) R -> ds_ty Θ Ξ R = Some A ->
    (forall M, ds_red R = Some M -> forall Θ0 Ξ0, glu_emb Θ Ξ Θ0 Ξ0 -> @glu_rel_exp (gc_mk Θ0 Ξ0) Γ M A) ->
    @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) Γ (a_mem H x) A.
Proof.
  intros * He HH Hm Ht HM HΓ.
  destruct (ds_red R) as [M |] eqn:Hr.
  - eapply k_of_eq; [ exact He | eapply wf_exp_eq_mem_delta; eassumption | exact (HM _ eq_refl _ _ He) ].
  - pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
    destruct (mem_no_red _ _ _ _ _ _ _ Hm Ht Hr) as (R0 & p & T & Φ & Φ0 & b & pv & oM & Hm0 & Hmd & Hp & Hn).
    pose proof (ds_canon_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hg Hm0) Hmd) as Hl; cbn in Hl.
    eapply k_of_eq; [ exact He | eapply mem_alias_filed; eassumption |].
    eapply gme_glob; eassumption.
Qed.

(** ** 6. The fundamental theorem, Kripke form *)

(** The other judgments glue their context, which is what a module slot,
    whose premise is a unit judgment, needs.  This is the whole block, the
    universes included; [kglu_fundamental] below is the statement without
    them. *)
Theorem kglu_fundamental_all :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> kglu_ctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> kglu_exp Θ Ξ Γ M A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> kglu_ctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> kglu_ctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> kglu_univ Θ Ξ Γ U) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> kglu_ctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> kglu_ctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> kglu_ctx Θ Ξ Γ).
Proof.
  apply syntactic_wf_mut_ind; unfold kglu_ctx, kglu_exp, kglu_univ; intros;
    repeat match goal with IH : forall _ _, glu_emb _ _ _ _ -> _ |- _ =>
      specialize (IH _ _ ltac:(eassumption)) end.
  all: try solve [ apply (@glu_rel_ctx_empty (gc_mk Θ2 Ξ2)); eapply em_wf, gme_emb; eassumption ].
  (** Universes: large, or small at a level that glues. *)
  all: try solve [ split; [ assumption | left; eexists; reflexivity ] ].
  all: try solve [ split; [ eapply presup_ctx_glu_rel_exp; eassumption | right; do 2 eexists; split; [ reflexivity | eassumption ] ] ].
  (** [Π]: the case of a large universe and that of a small one. *)
  all: try match goal with HU : _ /\ ((exists i, ?U = Typeω@i) \/ _) |- _ =>
         destruct HU as [_ [[? ->] | (? & ? & -> & ?)]] end.
  all: try solve [ apply glu_rel_exp_typ; assumption
    (** A small universe at a level term. *)
    | eapply glu_rel_exp_univ_lvl; eassumption
    (** Levels: the type, the literals and the two operations. *)
    | apply glu_rel_exp_level; assumption | apply glu_rel_exp_level_small; assumption
    | apply glu_rel_exp_llit; assumption
    | eapply glu_rel_exp_succl; eassumption
    | eapply glu_rel_exp_maxl; eassumption
    | apply glu_rel_exp_nat_small; assumption
    | apply glu_rel_exp_True_small; assumption | apply glu_rel_exp_False_small; assumption
    | eapply glu_rel_exp_pi_small_tm; eassumption
    | apply glu_rel_exp_nat; assumption
    | apply glu_rel_exp_zero; assumption | apply glu_rel_exp_succ; assumption
    | eapply glu_rel_exp_natrec; eassumption
    | apply glu_rel_exp_True; assumption | apply glu_rel_exp_False; assumption
    | apply glu_rel_exp_true; assumption
    | eapply glu_rel_exp_exfalso; eassumption
    | eapply glu_rel_exp_pi; eassumption | eapply glu_rel_exp_fn; eassumption
    | eapply glu_rel_exp_app; eassumption ].
  all: try solve [ eapply glu_rel_exp_vlookup; eassumption ].
  all: try solve [ eapply k_ind; eassumption | eapply k_con; eassumption | eapply k_elim; eassumption ].
  all: try solve [ eapply glu_rel_ctx_extend; [ eapply presup_ctx_glu_rel_exp |]; eassumption ].
  all: try solve [ eapply glu_rel_ctx_extend_def; [ eapply presup_ctx_glu_rel_exp | |]; eassumption ].
  all: try solve [ eapply glu_rel_exp_let; eassumption ].
  (** A member. *)
  all: try solve [ eapply k_mem; eassumption ].
  (** The context of the other judgments. *)
  all: try solve [ assumption | eapply presup_ctx_glu_rel_exp; eassumption
                 | eapply glu_rel_ctx_tail; eassumption
                 | eapply glu_rel_ctx_tail, presup_ctx_glu_rel_exp; eassumption ].
  (** Module slots and module [let]s, their premises moved syntactically. *)
  all: try solve [
    match goal with Hμ : glu_emb _ _ _ _ |- _ =>
      pose proof (gme_emb _ _ _ _ Hμ) as Hem;
      destruct (emb_preserves_wf _ _ _ _ Hem) as (Ec & Ee & Eq & Est & Ex & Eu & Em) end;
    first
      [ eapply (@glu_rel_ctx_extend_mod (gc_mk _ _)); [ eassumption | apply Eu; eassumption ]
      | eapply (@glu_rel_exp_let_mod (gc_mk _ _)); [ apply Eu; eassumption | apply Ee; eassumption | eassumption ] ] ].
  (* subsumption: the subtyping premise is moved syntactically *)
  match goal with Hμ : glu_emb _ _ _ _ |- _ =>
    destruct (emb_preserves_wf _ _ _ _ (gme_emb _ _ _ _ Hμ)) as (_ & _ & _ & Hsub & _) end.
  match goal with Hs : wf_subtyp _ _ _ _ _ |- _ => pose proof (Hsub _ _ _ Hs) end.
  eapply glu_rel_exp_subtyp; eassumption.
Qed.

Theorem kglu_fundamental :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> kglu_ctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> kglu_exp Θ Ξ Γ M A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> kglu_ctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> kglu_ctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> kglu_ctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> kglu_ctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> kglu_ctx Θ Ξ Γ).
Proof.
  destruct kglu_fundamental_all as (H1 & H2 & H3 & H4 & _ & H5).
  exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
Qed.

Lemma kglu_read : forall Θ1 Ξ1 Θ2 Ξ2 A M,
    glu_emb Θ1 Ξ1 Θ2 Ξ2 ->
    Θ1 ⍮ Ξ1 ⍮ ⋅ ⊢ M : A ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) ⋅ M A.
Proof. intros * Hμ HM; exact (proj1 (proj2 kglu_fundamental) _ _ _ _ _ HM _ _ Hμ). Qed.


(** ** 7. A stored axiom or abstract definition is a neutral

    A global is a neutral annotated with its type evaluated at [nil]. Since
    [nil_glu_sub_pred] leaves the environment free, the [⋅]-judgment can be
    instantiated at [nil]. The only semantic fact needed is that the values
    of a closed type at two environments are related ([typ_nil_rel], from
    completeness at [⋅]), which [glu_univ_elem_resp_per_univ] consumes. *)

Section Cook.
  Context {GC : GCtx}.
  Import Fixed_Notations.

  Lemma typ_nil_rel : forall T i ρ ρ',
      ⋅ ⊢ T : Typeω@i ->
      exists a a', ⟦ T ⟧ ρ ↘ a /\ ⟦ T ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i.
  Proof.
    intros * HT%completeness_fundamental_exp.
    destruct (rel_exp_of_typ_inversion_simple HT) as [env_rel [Hnil H]].
    apply H.
    inversion Hnil as [? Heq | | |]; subst.
    apply Heq; exact I.
  Qed.

  (** A neutral: a closed [G] that evaluates anywhere to [⇑ a d], [a] the value
      of its type at [nil], and reads back to itself. *)
  Lemma glu_neut_nil : forall T G i d,
      ⋅ ⊩ T : Typeω@i ->
      (forall σ, T[σ] = T) -> (forall σ, G[σ] = G) ->
      (forall φ, T[φ]ʷ = T) -> (forall φ, G[φ]ʷ = G) ->
      (forall Δ, ⊢ Δ -> Δ ⊢ G : T) ->
      Dom d ≈ d ∈ per_bot ->
      (forall s (M' : ne), Rne d in s ↘ M' -> (M' : exp) = G) ->
      (forall ρ a, ⟦ T ⟧ nil ↘ a -> ⟦ G ⟧ ρ ↘ ⇑ a d) ->
      ⋅ ⊩ G : T.
  Proof.
    intros * HT HTs HGs HTw HGw HGty Hd Hrb Hev.
    pose proof (glu_rel_exp_to_wf_exp HT) as HTwf.
    pose proof HT as [Sb0 [H0 _]].
    pose proof (glu_rel_exp_clean_inversion2' H0 HT) as HTi.
    exists Sb0; split; [ exact H0 |]; exists i; intros Δ σ ρ Hσ.
    destruct (HTi _ _ _ Hσ) as [? ? ? ? Hevu HevT Hu HTσ].
    inversion Hevu; subst.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
    apply_predicate_equivalence.
    unfold univ_glu_exp_pred' in *; destruct_conjs.
    rename H2 into Pa, H3 into Ela, H4 into HPa, H5 into HTPa.
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape H0 _ _ _ Hσ)).
    destruct (typ_nil_rel _ _ ρ nil HTwf) as (a1 & a0 & Ha1 & Ha0 & Hrel).
    functional_eval_rewrite_clear.
    assert (HPa0 : glu_univ_elem i Pa Ela a0) by (eapply glu_univ_elem_resp_per_univ; eassumption).
    rewrite HTs in HTPa.
    econstructor; [ exact HevT | apply Hev; exact Ha0 | exact HPa |].
    rewrite HGs, HTs.
    eapply realize_glu_elem_bot; [ exact HPa0 |].
    econstructor; [ apply HGty; exact HΔ | exact HPa0 | exact HTPa | exact Hd |].
    intros * Hk Hr; rewrite (Hrb _ _ Hr), HGw, HTw.
    pose proof (HGty _ (kripke_dom _ _ _ Hk)); mauto 3.
  Qed.
End Cook.

Section Raw.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  (** An axiom or an abstract definition of a stored body whose type glues
      at [⋅] glues there: it is the neutral of its path. *)
  Lemma glob_glu : forall p T Φ x Φ0 b pv A oM i,
      loc Θ Ξ p T Φ ->
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x (ge_def b pv A oM)) ->
      (if b then oM else None) = None ->
      @glu_rel_exp (gc_mk Θ Ξ) ⋅ A (Typeω@i) ->
      @glu_rel_exp (gc_mk Θ Ξ) ⋅ (a_mem (qname_mod p) x) A.
  Proof.
    intros * Hl Hp Hn HA.
    pose proof (loc_closed _ _ Hg _ _ _ Hl) as [_ HcΦ].
    pose proof (body_closed_prefix _ _ _ _ HcΦ Hp) as HcE; cbn in HcE; destruct HcE as [_ [HsA _]].
    pose proof (qname_mod_qname p) as Hpm.
    destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- <-] & Hent).
    pose proof (proj2 (loc_entry _ _ Hg _ _ _ Hl x _) Hent) as HeE.
    apply gc_entry_def in HeE; rewrite qname_in_app in HeE.
    pose proof (@glu_rel_exp_to_wf_exp (gc_mk Θ Ξ) _ _ _ HA) as HAw.
    eapply (@glu_neut_nil (gc_mk Θ Ξ)) with (d := d_glob (qname_app p (x :: nil))); [ exact HA | | | | | | | |].
    - intros; apply exp_closed_sub; exact HsA.
    - intros; cbn; rewrite (mod_qname_sub _ _ _ Hpm); reflexivity.
    - intros; apply exp_closed_wk; exact HsA.
    - intros; cbn; rewrite (mod_qname_wk _ _ _ Hpm); reflexivity.
    - intros Δ HΔ.
      eapply (filed_def_wf _ _ Hg _ _ _ _ _ _ _ _ _ _ i HΔ Hl Hp Hn).
      exact (closed_weaken_exp _ _ _ _ _ HΔ HAw HsA ltac:(cbn; exact I)).
    - intros s; eexists; split; constructor.
    - intros * Hrb; inversion Hrb; subst; cbn [ne_to_exp]; apply qname_term_snoc.
    - intros * Hev.
      eapply (@eval_mem_of_sel (gc_mk Θ Ξ));
        [ apply (gc_loc_path _ _ Hg _ _ ρ (gc_loc_of_loc _ _ Hg _ _ _ Hl))
        | eapply eval_sel_global_neut; [ exact HeE | | exact Hev | constructor ] ].
      destruct b; [ right; exact Hn | left; reflexivity ].
  Qed.
End Raw.


(** ** 8. Every well-formed global context glues *)

(** What an entry is worth at [Θ2 ⍮ Ξ2]: a definition's type glues, in the
    empty context.  Bodies need nothing: a member with a δ-reduct glues as
    the reduct, which [wf_mem] premises typed. *)
Definition glu_V (_ : gdeps) (_ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (_ : ctx) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A _ => exists i, @glu_rel_exp (gc_mk Θ2 Ξ2) ⋅ A (Typeω@i)
  | _ => True
  end.

Definition glu_F (_ : gdeps) (_ : gstack) (_ : ctx) : Prop := True.

Definition glu_VD (Θ2 : gdeps) (Ξ2 : gstack) (D : ind_decl) : Prop := @glu_core (gc_mk Θ2 Ξ2) D.

(** A stored body of the source, valid. *)
Lemma glu_loc_valid : forall Θ Ξ Θs Ξs Θ2 Ξ2 p T Φ,
    gds_valid glu_V glu_F glu_VD Θs Ξs Θ2 Ξ2 Θ -> gs_valid glu_V glu_F glu_VD Θs Ξs Θ2 Ξ2 Ξ -> loc Θ Ξ p T Φ ->
    gm_valid glu_V glu_F glu_VD Θs Ξs Θ2 Ξ2 T Φ.
Proof.
  intros * HΘ HΞ [Hl | Hl].
  - unfold gc_frame in Hl.
    destruct (gs_find_tele Ξ p) as [[[[Δ [[|] Φ1 | E]] [| ? ?]] T0] |] eqn:Ef; try discriminate.
    injection Hl as <- <-; exact (proj2 (gs_valid_find _ _ _ _ _ _ _ _ _ _ _ _ HΞ Ef)).
  - exact (proj2 (good_body _ _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hl)).
Qed.

(** A sound embedding, from the validity at the target of what the source
    files and has open. *)
Theorem glu_emb_of : forall Θ Ξ Θ2 Ξ2, ⊢ᵍ Θ ⍮ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    gds_valid glu_V glu_F glu_VD Θ Ξ Θ2 Ξ2 Θ -> gs_valid glu_V glu_F glu_VD Θ Ξ Θ2 Ξ2 Ξ -> glu_emb Θ Ξ Θ2 Ξ2.
Proof.
  intros * Hg He HΘ HΞ; pose proof He as [Hg2 Hs].
  constructor; [ exact He | intros p D Hl; exact (good_ind _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hl) |].
  intros * Hl Hp Hn HΓ.
  apply glu_rel_exp_nil_weaken; [ exact HΓ |].
  (* the type glues, by the entry's validity *)
  pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ (glu_loc_valid _ _ _ _ _ _ _ _ _ HΘ HΞ Hl) Hp) as [i HA].
  (* the entry, stored at the target where it is at the source *)
  destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- <-] & Hent).
  pose proof (proj2 (loc_entry _ _ Hg _ _ _ Hl x _) Hent) as HeE.
  destruct (gc_sub_entry _ _ _ _ _ _ Hs HeE) as (E2 & HeE2 & Hgr); cbn in Hgr; subst E2.
  destruct (loc_grow _ _ _ _ Hs _ _ _ Hl) as (Φ2 & Hl2).
  pose proof (proj1 (loc_entry _ _ Hg2 _ _ _ Hl2 x _) HeE2) as Hent2.
  pose proof (loc_closed _ _ Hg2 _ _ _ Hl2) as [_ HcΦ2].
  destruct (gm_entry_prefix _ _ _ (body_closed_noopen _ _ HcΦ2) Hent2) as (Φ0' & Hp2).
  exact (glob_glu _ _ Hg2 _ _ _ _ _ _ _ _ _ _ Hl2 Hp2 Hn HA).
Qed.

Corollary glu_emb_good : forall Θ Ξ Θ2 Ξ2, ⊢ᵍ Θ ⍮ Ξ -> GoodV glu_V glu_F glu_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    glu_emb Θ Ξ Θ2 Ξ2.
Proof.
  intros * Hg HG He; destruct (HG _ _ He _ _ (gc_sub_refl _ _)) as [HΘ HΞ].
  exact (glu_emb_of _ _ _ _ Hg (Embx_emb _ _ _ _ He) HΘ HΞ).
Qed.

(** *** Each entry is valid where it is checked *)

Lemma glu_V_def : forall Θ Ξ T A M b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ T ⊢ M : A -> GoodV glu_V glu_F glu_VD Θ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    gds_valid glu_V glu_F glu_VD Θ Ξ Θ2 Ξ2 Θ -> gs_valid glu_V glu_F glu_VD Θ Ξ Θ2 Ξ2 Ξ ->
    forall Θs Ξs, glu_V Θs Ξs Θ2 Ξ2 T (ge_def b pv (ctx_pi T A) (Some (ctx_fn T M))).
Proof.
  intros * HM _ He HΘ HΞ Θs Ξs.
  pose proof (glu_emb_of _ _ _ _ (ctx_wf_gctx _ _ _ (presup_exp_ctx HM)) He HΘ HΞ) as Hμ.
  destruct (presup_exp_typ HM) as [i HA].
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  exists j; exact (kglu_read _ _ _ _ _ _ Hμ HT).
Qed.

Lemma glu_V_ax : forall Θ Ξ A i b pv Θ2 Ξ2 Θs Ξs,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i -> GoodV glu_V glu_F glu_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    glu_V Θs Ξs Θ2 Ξ2 (gs_tele Ξ) (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
Proof.
  intros * HA HG He _.
  pose proof (glu_emb_good _ _ _ _ (ctx_wf_gctx _ _ _ (presup_exp_ctx HA)) HG He) as Hμ.
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  exists j; exact (kglu_read _ _ _ _ _ _ Hμ HT).
Qed.

Lemma glu_V_alias : forall Θ Ξ pv Δ E Θ2 Ξ2 Θs Ξs,
    tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    GoodV glu_V glu_F glu_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    glu_V Θs Ξs Θ2 Ξ2 (gs_tele Ξ) (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))).
Proof. intros; exact I. Qed.

Lemma glu_V_indalias : forall Θ Ξ pv Δ p Ns D Θ2 Ξ2 Θs Ξs,
    tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> ind_lookup Θ Ξ p = Some D -> List.length Ns <= ind_nu D ->
    Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ apps (a_ind p) Ns : ind_ty_at D Ns ->
    Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns ->
    GoodV glu_V glu_F glu_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    glu_V Θs Ξs Θ2 Ξ2 (gs_tele Ξ) (ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns).
Proof. intros; exact I. Qed.

Lemma glu_F_nil : forall Θ Ξ Δ Θ2 Ξ2,
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ -> GoodV glu_V glu_F glu_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    glu_F Θ2 Ξ2 (Δ ++ gs_tele Ξ).
Proof. intros; exact I. Qed.

(** A declaration typed at the source glues at the target: its judgments,
    glued. *)
Lemma glu_V_ind : forall Θ Ξ D Θ2 Ξ2,
    decl_typed Θ Ξ D -> GoodV glu_V glu_F glu_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    glu_VD Θ2 Ξ2 D /\ glu_F Θ2 Ξ2 (ind_uparams D).
Proof.
  intros * Hdt HG He; split; [| exact I ]; unfold glu_VD.
  pose proof Hdt as (Hass & _ & Hle & HΔ & Hsu & [i HS] & [n Hn] & HA & HPl & HP & HN & Hnd & Hsh).
  pose proof (glu_emb_good _ _ _ _ (ctx_wf_gctx _ _ _ HΔ) HG He) as Hμ.
  destruct kglu_fundamental as (Kc & Ke & _).
  constructor.
  - exact (Kc _ _ _ HΔ _ _ Hμ).
  - exists n; exact (Ke _ _ _ _ _ Hn _ _ Hμ).
  - exists n.
    assert (Hn' : Θ ⍮ Ξ ⍮ ind_params D ⊢ (ind_sort_lvl (ind_sort D))[wk_shiftn (ind_nn D)]ʷ : Level@n).
    { pose proof HΔ as HΔ'; rewrite params_split in HΔ'.
      pose proof (wf_wk_shiftn_app' _ _ _ _ HΔ') as Hw.
      rewrite length_nparams in Hw; rewrite params_split.
      exact (wk_preserves_exp _ _ _ _ _ _ _ Hn Hw). }
    exact (Ke _ _ _ _ _ Hn' _ _ Hμ).
  - intros k A HA0.
    destruct (Completeness.IndCases.nparams_nth_split _ _ _ HA0) as [Δ1 HΔ1].
    assert (Hk : k < ind_nn D)
      by (rewrite <- (length_nparams D), <- List.length_rev; apply List.nth_error_Some; congruence).
    pose proof (HN _ _ _ HΔ1) as HT; rewrite Completeness.IndCases.length_npre in HT by lia.
    exact (Ke _ _ _ _ _ HT _ _ Hμ).
  - intros * Hcon HA0.
    destruct (Completeness.IndCases.nonrec_nth_split _ _ _ HA0) as (gs1 & gs2 & Heq & Hk).
    pose proof (HA _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq) as HT.
    assert (Hls : List.length (cargs_strat gs1) = k)
      by (rewrite Completeness.IndCases.cargs_strat_nonrec, List.length_rev, List.length_map; exact Hk).
    rewrite Hls, (Completeness.IndCases.astrat_prefix gs1 (ca_arg A :: gs2)), Hk, <- Heq in HT.
    exact (Ke _ _ _ _ _ HT _ _ Hμ).
  - intros * Hcon Heq HPk HT.
    assert (Hls : List.length (cargs_nonrec gs1) = List.length (cargs_strat gs1))
      by (rewrite Completeness.IndCases.cargs_strat_nonrec, List.length_rev, List.length_map; reflexivity).
    rewrite Hls in HT.
    pose proof (HP _ _ _ _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq HPk HT) as H.
    rewrite (Completeness.IndCases.astrat_prefix gs1 (ca_rec t :: gs2)), <- Heq in H.
    exact (Ke _ _ _ _ _ H _ _ Hμ).
  - intros * Hcon Heq HB.
    destruct (Hsh _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq) as [_ Hs2].
    destruct (doms_split_nth _ _ _ HB) as [Hsplit _].
    pose proof (Hs2 _ _ _ Hsplit) as HT.
    assert (Hk : List.length (List.firstn k (ptyp_doms t)) = k)
      by (rewrite List.length_firstn; assert (k < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence); lia).
    assert (Hls : List.length (cargs_strat gs1) = List.length (cargs_nonrec gs1))
      by (rewrite Completeness.IndCases.cargs_strat_nonrec, List.length_rev, List.length_map; reflexivity).
    rewrite Hk, Hls, (Completeness.IndCases.astrat_prefix gs1 (ca_rec t :: gs2)), <- Heq in HT.
    exact (Ke _ _ _ _ _ HT _ _ Hμ).
  - intros * Hcon Heq Hk.
    pose proof (doms_prefix_wf _ _ _ _ _ Hdt (cons_lookup_in _ _ _ Hcon) _ _ _ Heq _ Hk) as H.
    rewrite (Completeness.IndCases.astrat_prefix gs1 (ca_rec t :: gs2)), <- Heq in H.
    exact (Kc _ _ _ H _ _ Hμ).
Qed.

(** Every well-formed global context glues: the identity is a sound
    embedding. *)
Theorem gctx_glu : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> glu_emb Θ Ξ Θ Ξ.
Proof.
  intros * Hg; apply glu_emb_good; [ exact Hg | | apply Embx_refl; exact Hg ].
  exact (global_valid glu_V glu_F glu_VD glu_V_def glu_V_ax glu_V_alias glu_V_indalias glu_F_nil glu_V_ind _ _ Hg).
Qed.
