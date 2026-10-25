(** * The Global Rules in the Gluing Model, at the Target

    The soundness counterpart of [Core/Completeness/ModuleCases.v]: the
    members, at the target of a sound embedding ([glu_emb]), where the
    members of the stored bodies that have no δ-reduct, the axioms and
    abstract definitions read bare, glue as neutrals.  Module values are
    not glued: a member with a δ-reduct glues as the reduct, which
    [wf_mem] premises typed, and one without is the filed member its module
    expression is equal to ([mem_alias_filed]).  The rules of the members,
    the extensions, the units and the module expressions are stated after
    them, as the cases of the gluing judgments. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Modules Paths DescTyping LookupSound.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.Modules Require Import Values.
From Mctt.Core.Completeness Require Import ModuleCases.
From Mctt.Core.Completeness.Global Require Import Embedding.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Soundness Require Import LevelCases.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases VariableCases UnitCases
  SubtypingCases UniverseCases FunctionCases LetCases TrueFalseCases.
From Mctt.Core.Soundness.Inductives Require Import Con.
From Mctt.Core.Soundness Require Import IndCases.
From Mctt.Core.Completeness.Inductives Require Con.
Require Import Mctt.Core.Soundness.Inductives.Elim.
Require Import Mctt.Core.Soundness.ElimCases.
Require Import Mctt.Core.Soundness.IotaCases.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. Equations, at the target *)

(** A term equal to one that glues glues, the equation moved to the target. *)
Lemma glu_rel_exp_of_eq_of_emb : forall Θ Ξ Θ2 Ξ2 Γ M N A,
    glu_emb Θ Ξ Θ2 Ξ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ N : A -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ N A -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ M A.
Proof.
  intros * He Heq Hg.
  destruct (emb_preserves_wf _ _ _ _ (glu_emb_emb _ _ _ _ He)) as (_ & _ & Hwq & _).
  eapply (@glu_rel_exp_of_eq (gc_mk Θ2 Ξ2)); [ exact Hg | exact (Hwq _ _ _ _ Heq) ].
Qed.

(** ** 2. Members *)

Lemma ds_ats_term_none : forall Ns A R, ds_ats (ds_term A None) Ns = Some R -> exists A', R = ds_term A' None.
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha; [ injection Ha as <-; eauto |].
  destruct (pi_view A) as [[? ?] |]; [ exact (IH _ _ Ha) | discriminate ].
Qed.

(** A member looked up as a term of no δ-reduct is an axiom or an abstract
    definition of a stored body, read bare: the module expression's module
    part is the body's path at no argument and no outside parameter. *)
Lemma mem_no_red : forall Θ Ξ Γ H x R A,
    mdenote Θ Ξ Γ (me_mem H x) R -> ds_ty R = Some A -> ds_red R = None ->
    exists R0 p T Φ Φ0 b pv oM,
      mdenote Θ Ξ Γ H R0 /\ ds_mod R0 = Some (ds_closed nil p T Φ nil) /\
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x (ge_def b pv A oM)) /\ (if b then oM else None) = None.
Proof.
  intros * Hm Ht Hr.
  assert (HR : R = ds_term A None)
    by (destruct R as [A' om | | | ]; cbn in Ht, Hr; try discriminate; subst; congruence).
  subst R.
  inversion Hm as [| | | | | ? ? ? R0 R0m Γy E rd Re ? Hm0 Hmd He Hed Hrd |]; subst.
  destruct R0m as [| Δ Φw Φx | Θ' p T Φ Ns |]; cbn in He; try discriminate.
  - (* an open body reads only transparent definitions and modules *)
    destruct (gm_prefix_upto Φx x) as [[| Φ' y E0 | ? ? ?] |]; try discriminate.
    destruct E0 as [[] pv A' [M |] | pv U | | |]; try discriminate; injection He as <- <- <-.
    + inversion Hed; subst; cbn in Hrd.
      destruct (gm_fill Φ'); cbn in Hrd; discriminate.
    + inversion Hed; subst.
      match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hmm end.
      cbn in Hrd; destruct (gm_fill Φ'); cbn in Hrd; [| discriminate ].
      injection Hrd as Heq; destruct Re; cbn in Hmm, Heq; try contradiction; discriminate.
    + (* a definition with a module part reads as one, with both parts *)
      inversion Hed; subst; cbn in Hrd.
      destruct (gm_fill Φ'); cbn in Hrd; discriminate.
  - destruct (gm_prefix_upto Φ x) as [[| Φ0 y E0 | ? ? ?] |] eqn:Hp; try discriminate.
    injection He as <- <- <-.
    pose proof (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & _).
    cbn [ds_read] in Hrd; destruct (ds_ats_read Re Ns) as [R1 |] eqn:Hats; cbn [option_map] in Hrd; [| discriminate ].
    injection Hrd as Heq.
    destruct E0 as [b pv A' oM | pv [Δ [sm Φy | E'] ] | pv pq D ΦD | pv Ad Md Ud | pv Rr ΦR ].
    + (* a definition: one of no body, read bare *)
      cbn [ge_read] in Hed; inversion Hed; subst; cbn [ds_ats_read] in Hats.
      destruct (if b then oM else None) as [M |] eqn:Ho.
      * exfalso; destruct (ds_ats_some_red _ _ _ _ Hats) as (A1 & M1 & ->).
        rewrite ds_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
      * destruct (ds_ats_term_none _ _ _ Hats) as (A1 & ->).
        destruct (ds_named_term_none Θ' Ns (apps (a_mem (qname_mod p) x) Ns) A1) as [(Hn & -> & ->) | Hn];
          rewrite Hn in Heq; cbn in Heq; [| discriminate ].
        cbn in Hats; injection Hats as ->; injection Heq as ->.
        exists R0, p, T, Φ, Φ0, b, pv, oM; repeat split; assumption.
    + exfalso; assert (Hmm : ds_is_mod Re) by (destruct sm; cbn [ge_read] in Hed; inversion Hed; subst; eapply udenote_is_mod; eassumption).
      rewrite (ds_ats_read_mod _ _ Hmm) in Hats.
      pose proof (ds_ats_is_mod _ _ _ Hmm Hats) as Hm1.
      destruct R1; cbn in Hm1; try contradiction; rewrite ds_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + exfalso; assert (Hmm : ds_is_mod Re) by (cbn [ge_read] in Hed; inversion Hed; subst; eapply udenote_is_mod; eassumption).
      rewrite (ds_ats_read_mod _ _ Hmm) in Hats.
      pose proof (ds_ats_is_mod _ _ _ Hmm Hats) as Hm1.
      destruct R1; cbn in Hm1; try contradiction; rewrite ds_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + (* a member of a group: its type former, a reduct *)
      exfalso; cbn [ge_read] in Hed; inversion Hed; subst; cbn [ds_ats_read ind_former_desc] in Hats.
      ds_dm_read_shape Hats.
      rewrite ds_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + (* a definition with a module part: read with its module part, no term *)
      exfalso; cbn [ge_read] in Hed; inversion Hed; subst; cbn [ds_ats_read] in Hats.
      ds_dm_read_shape Hats.
      rewrite ds_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
    + (* a record type: its type former, a reduct *)
      exfalso; cbn [ge_read] in Hed; inversion Hed; subst; cbn [ds_ats_read record_former_desc] in Hats.
      ds_dm_read_shape Hats.
      rewrite ds_named_fix in Heq by reflexivity; cbn in Heq; discriminate.
Qed.

(** A member glues: as its δ-reduct, which glues by the premise of [wf_mem];
    without one, as the filed member it is equal to. *)
Lemma glu_rel_exp_mem_of_emb : forall Θ Ξ Θ2 Ξ2 Γ H x R A,
    glu_emb Θ Ξ Θ2 Ξ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ (me_mem H x) R -> ds_ty R = Some A ->
    (forall M, ds_red R = Some M -> forall Θ0 Ξ0, glu_emb Θ Ξ Θ0 Ξ0 -> @glu_rel_exp (gc_mk Θ0 Ξ0) Γ M A) ->
    @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) Γ (a_mem H x) A.
Proof.
  intros * He HH Hm Ht HM HΓ.
  destruct (ds_red R) as [M |] eqn:Hr.
  - eapply glu_rel_exp_of_eq_of_emb; [ exact He | eapply wf_exp_eq_mem_delta; eassumption | exact (HM _ eq_refl _ _ He) ].
  - pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
    destruct (mem_no_red _ _ _ _ _ _ _ Hm Ht Hr) as (R0 & p & T & Φ & Φ0 & b & pv & oM & Hm0 & Hmd & Hp & Hn).
    pose proof (ds_canon_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hg Hm0) Hmd) as Hl; cbn in Hl.
    eapply glu_rel_exp_of_eq_of_emb; [ exact He | eapply mem_alias_filed; eassumption |].
    eapply glu_emb_glob; eassumption.
Qed.

(** ** 3. The rules

    The members read syntactic premises of their rules: the premises the
    case needs at the target are the syntactic ones moved along the
    embedding. *)

#[local] Generalizable All Variables.

(** *** Members *)

Lemma glu_mem :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     ds_ty R = Some A ->
     (forall M, ds_red R = Some M -> Θ ⍮ Ξ ⍮ Γ ⊩ M : A) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_mem H x : A ).
Proof. glu_intro; eapply glu_rel_exp_mem_of_emb; eassumption. Qed.

Lemma glu_exp_eq_mem_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     ds_ty R = Some A ->
     mdenote Θ Ξ Γ (me_mem H' x) R' ->
     ds_ty R' = Some A' ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_mem H' x : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_mem_delta :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     ds_ty R = Some A ->
     ds_red R = Some M ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

(** *** Extensions *)

Lemma glu_ext_eq_nil :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_ext_eq_ass :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊩ A : Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Ψ ++ Γ ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊩ A' : Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_ext_eq_def :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊩ A : Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Ψ ++ Γ ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊩ M : A ->
     ⊩ Θ ⍮ Ξ ⍮ Ψ ++ Γ ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊩ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊩ M' : A' ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_ext_eq_mod :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Ψ ++ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Ψ' ++ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

(** A definition with a module part: as a definition and as a module slot. *)
Lemma glu_ext_eq_dm :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊩ A : Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Ψ ++ Γ ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊩ M : A ->
     ⊩ Θ ⍮ Ξ ⍮ Ψ ++ Γ ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊩ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊩ M' : A' ->
     ⊩ Θ ⍮ Ξ ⍮ Ψ ++ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Ψ' ++ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

(** *** Units *)

Lemma glu_unit_eq_body :
  `( body_xp Θ Ξ (Δ ++ Γ) Φ Φx ->
     body_xp Θ Ξ (Δ' ++ Γ) Φ' Φx' ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊩ A[σ] : Typeω@(lv y)) ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        ⊩ Θ ⍮ Ξ ⍮ Δ ++ Γ) ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊩ M[σ] : A[σ]) ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        ⊩ Θ ⍮ Ξ ⍮ Δ ++ Γ) ->
     (forall y Φ0 E U Φ0' E' U' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        ⊩ Θ ⍮ Ξ ⍮ Δ ++ Γ) ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊩ A'[σ'] : Typeω@(lv y)) ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊩ M'[σ'] : A'[σ']) ->
     (forall y Φ0 E U Φ0' E' U' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        ⊩ Θ ⍮ Ξ ⍮ Δ' ++ Γ) ->
     (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> ⊩ Θ ⍮ Ξ ⍮ Ψ ++ Δ ++ Γ) ->
     (forall k Ψ' H', nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> ⊩ Θ ⍮ Ξ ⍮ Ψ' ++ Δ' ++ Γ) ->
     (forall k Φ0 H Φ0' H' σ σ',
        nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) ->
        nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        ⊩ Θ ⍮ Ξ ⍮ Δ ++ Γ) ->
     (forall k Φ0 H Φ0' H' σ σ',
        nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) ->
        nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        ⊩ Θ ⍮ Ξ ⍮ Δ' ++ Γ) ->
     tele_ass Δ ->
     tele_ass Δ' ->
     List.length Δ = List.length Δ' ->
     body_shape Φ Φ' ->
     body_shape Φx Φx' ->
     List.NoDup (gm_names Φ) ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_unit_eq_alias :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     tele_ass Δ ->
     tele_ass Δ' ->
     ⊩ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Δ' ++ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_unit_eq_flatten :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     tele_ass Δ ->
     ⊩ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_unit_eq_sym :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_unit_eq_trans :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

(** *** Module expressions *)

Lemma glu_me_unit :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     gc_unit Θ Ξ (me_unit fp) = Some TΦ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_var :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ₘ U ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_lit :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_mem :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     mdenote Θ Ξ Γ (me_mem H y) R ->
     ds_mtele R = Some T ->
     mdenote Θ Ξ Γ (me_mem H' y) R' ->
     ds_mtele R' = Some T' ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_app :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     mdenote Θ Ξ Γ H R ->
     ds_mtele R = Some T ->
     tele_view T = Some (B, T1) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : B ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     mdenote Θ Ξ Γ H' R' ->
     ds_mtele R' = Some T' ->
     tele_view T' = Some (B', T1') ->
     Θ ⍮ Ξ ⍮ Γ ⊩ B' : Typeω@j ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N' : B' ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_delta_slot :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ₘ U ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_delta_sel :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     mdenote Θ Ξ Γ (me_mem H y) R ->
     ds_mod R = Some Rm ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_beta_body :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : X ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_beta_alias :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : X ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_beta_alias0 :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_sym :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_me_trans :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
