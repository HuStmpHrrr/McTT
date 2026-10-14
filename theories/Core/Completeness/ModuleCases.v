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
  ContextCases FunctionCases LetCases LevelCases NatCases SubstitutionCases SubtypingCases
  TrueFalseCases UniverseCases VariableCases LogicalRelation UnitCases InstanceCases
  MemberCases MemberTyping MemberReps MemberSem ModexpCases PathCases GlobalSem IndCases TeleSem ElimCases ElimIota.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. Sound embeddings *)

Record sem_emb (Θ1 : gdeps) (Ξ1 : gstack) (Θm : gdeps) (Ξm : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  { sme_emb : Emb Θ1 Ξ1 Θ2 Ξ2
  ; sme_rd : gc_sub Θ1 Ξ1 Θm Ξm
  ; sme_rdwf : ⊢g Θm ⍮ Ξm
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
  ; sme_path : forall p r, gc_module Θ1 Ξ1 p = Some r -> @gpath_at (gc_mk Θ2 Ξ2) Θm Ξm p
  ; sme_ind : forall p D, ind_lookup Θ1 Ξ1 p = Some D -> @sem_core (gc_mk Θ2 Ξ2) D
  }.

(** ** 2. The fundamental theorem along an embedding *)

Definition kctx Θ1 Ξ1 Γ : Prop :=
  forall Θm Ξm Θ2 Ξ2, sem_emb Θ1 Ξ1 Θm Ξm Θ2 Ξ2 -> @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm Γ.

Definition kexp_eq Θ1 Ξ1 Γ A M M' : Prop :=
  forall Θm Ξm Θ2 Ξ2, sem_emb Θ1 Ξ1 Θm Ξm Θ2 Ξ2 ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm Γ /\ @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A M M'.

Definition ksubtyp Θ1 Ξ1 Γ A A' : Prop :=
  forall Θm Ξm Θ2 Ξ2, sem_emb Θ1 Ξ1 Θm Ξm Θ2 Ξ2 ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm Γ /\ @subtyp_under_ctx (gc_mk Θ2 Ξ2) Γ A A'.

Definition kext Θ1 Ξ1 Γ Ψ Ψ' : Prop :=
  forall Θm Ξm Θ2 Ξ2, sem_emb Θ1 Ξ1 Θm Ξm Θ2 Ξ2 ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ Ψ Ψ' /\
    @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm (Ψ ++ Γ) /\ @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm (Ψ' ++ Γ) /\
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm Γ.

Definition kunit Θ1 Ξ1 Γ U U' : Prop :=
  forall Θm Ξm Θ2 Ξ2, sem_emb Θ1 Ξ1 Θm Ξm Θ2 Ξ2 ->
    @rel_unit_under_ctx (gc_mk Θ2 Ξ2) Γ U U' /\
    @unit_mt (gc_mk Θ2 Ξ2) Θm Ξm Γ U /\ @unit_mt (gc_mk Θ2 Ξ2) Θm Ξm Γ U' /\
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm Γ.

Definition kmod Θ1 Ξ1 Γ H H' : Prop :=
  forall Θm Ξm Θ2 Ξ2, sem_emb Θ1 Ξ1 Θm Ξm Θ2 Ξ2 ->
    @rel_modexp_under_ctx (gc_mk Θ2 Ξ2) Γ H H' /\
    @sem_mt (gc_mk Θ2 Ξ2) Θm Ξm Γ H /\ @sem_mt (gc_mk Θ2 Ξ2) Θm Ξm Γ H' /\
    @sem_unf (gc_mk Θ2 Ξ2) Θm Ξm Γ H /\ @sem_unf (gc_mk Θ2 Ξ2) Θm Ξm Γ H' /\
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm Γ.

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
  repeat match goal with IH : forall _ _ _ _, sem_emb _ _ _ _ _ _ -> _, He : sem_emb _ _ _ _ _ _ |- _ =>
    specialize (IH _ _ _ _ He) end;
  destruct_conjs.

(** ** The cases of the inductive types, at the target *)

Lemma k_decl : forall Θ Ξ Θm Ξm Θ2 Ξ2 Γ p D, sem_emb Θ Ξ Θm Ξm Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D ->
    ind_lookup Θ2 Ξ2 p = Some D /\ @sem_decl (gc_mk Θ2 Ξ2) D /\ decl_closed D /\ ind_sort_univ (ind_sort D) /\
    decl_typed Θ2 Ξ2 D.
Proof.
  intros * He HΓ Hl.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [Hdt Hc].
  pose proof (decl_typed_emb _ _ _ _ _ (sme_emb _ _ _ _ _ _ He) Hdt) as Hdt2.
  pose proof Hdt as (_ & _ & _ & _ & Hsu & _).
  pose proof (ind_lookup_gc_sub _ _ _ _ _ _ (em_res _ _ _ _ (sme_emb _ _ _ _ _ _ He)) Hl) as Hl2.
  split; [ exact Hl2 | split; [| split; [ exact Hc | split; [ exact Hsu | exact Hdt2 ] ] ] ].
  exact (@sem_decl_of_core (gc_mk Θ2 Ξ2) D (sme_ind _ _ _ _ _ _ He _ _ Hl) Hc Hsu Hdt2).
Qed.

Lemma k_ind : forall Θ Ξ Θm Ξm Θ2 Ξ2 Γ p D, sem_emb Θ Ξ Θm Ξm Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ -> @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (ind_ty D) (a_ind p) (a_ind p).
Proof.
  intros * He HΓ Hl HΓ2.
  destruct (k_decl _ _ _ _ _ _ _ _ _ He HΓ Hl) as (Hl2 & HD & Hc & Hsu & _).
  exact (@closed_weaken_valid (gc_mk Θ2 Ξ2) Γ _ _ _ HΓ2 (@valid_exp_ind0 (gc_mk Θ2 Ξ2) D HD Hc Hsu p Hl2)).
Qed.

Lemma k_con : forall Θ Ξ Θm Ξm Θ2 Ξ2 Γ p D c gs, sem_emb Θ Ξ Θm Ξm Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D ->
    ind_con D c = Some gs ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ -> @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (con_ty p D gs) (a_con p c) (a_con p c).
Proof.
  intros * He HΓ Hl Hcon HΓ2.
  destruct (k_decl _ _ _ _ _ _ _ _ _ He HΓ Hl) as (Hl2 & HD & Hc & Hsu & _).
  destruct (@sd_conty (gc_mk Θ2 Ξ2) D HD p c gs Hl2 Hcon) as [j HT].
  pose proof (@sd_cargs (gc_mk Θ2 Ξ2) D HD p c gs Hl2 Hcon) as HΨ.
  exact (@closed_weaken_valid (gc_mk Θ2 Ξ2) Γ _ _ _ HΓ2 (@valid_exp_con0 (gc_mk Θ2 Ξ2) D HD Hc Hsu p Hl2 c gs Hcon HΨ j HT)).
Qed.

Lemma k_elim_cong : forall Θ Ξ Θm Ξm Θ2 Ξ2 Γ p D Hh Hh' Ps M M' nm A A' (i : nat) Bs Bs',
    sem_emb Θ Ξ Θm Ξm Θ2 Ξ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : apps (a_ind p) Ps -> ind_lookup Θ Ξ p = Some D ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       forall Θm Ξm Θ2 Ξ2, sem_emb Θ Ξ Θm Ξm Θ2 Ξ2 ->
         @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm Γ /\ @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ T P P) ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (apps (a_ind p) Ps) M M' ->
    nm = S (ind_nn D) ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ) (Typeω@i) A A' ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ (elim_mctx p D (List.firstn (ind_nu D) Ps)) (elim_mctx p D (List.firstn (ind_nu D) Ps)) ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs -> forall Θm Ξm Θ2 Ξ2, sem_emb Θ Ξ Θm Ξm Θ2 Ξ2 ->
       @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ (elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) (elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) /\
       @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) /\
       @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) /\
       @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm Γ) ->
    List.map fst Bs = List.map fst Bs' ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall k c gs n B B', List.nth_error Bs k = Some (c, n, B) -> List.nth_error Bs' k = Some (c, n, B') ->
       ind_con D c = Some gs -> forall Θm Ξm Θ2 Ξ2, sem_emb Θ Ξ Θm Ξm Θ2 Ξ2 ->
         @sem_ctx (gc_mk Θ2 Ξ2) (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) /\
         @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) /\
         @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ)
           (elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) B B') ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)]) (a_elim Hh nm A Bs M) (a_elim Hh' nm A' Bs' M').
Proof.
  intros * He HMs Hl HPl HPs HMM Hnm HA HMx HBn HBc HBf Hnb HB HΓ2.
  destruct (k_decl _ _ _ _ _ _ _ _ _ He (presup_exp_eq_ctx HMs) Hl) as (Hl2 & HD & Hc & Hsu & Hdt2).
  eapply (@rel_exp_elim_cong (gc_mk Θ2 Ξ2)); try eassumption.
  - intros * HP HT; exact (proj2 (proj2 (HPs _ _ _ HP HT _ _ _ _ He))).
  - exact (proj1 HMx).
  - intros c gs Hcon; exact (proj1 (proj1 (HBc _ _ Hcon _ _ _ _ He))).
  - intros * Hk Hk' Hcon; exact (proj2 (proj2 (HB _ _ _ _ _ _ Hk Hk' Hcon _ _ _ _ He))).
Qed.

Lemma k_elim : forall Θ Ξ Θm Ξm Θ2 Ξ2 Γ p D Hh Ps M nm A (i : nat) Bs,
    sem_emb Θ Ξ Θm Ξm Θ2 Ξ2 -> ind_lookup Θ Ξ p = Some D ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       forall Θm Ξm Θ2 Ξ2, sem_emb Θ Ξ Θm Ξm Θ2 Ξ2 ->
         @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm Γ /\ @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ T P P) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : apps (a_ind p) Ps ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (apps (a_ind p) Ps) M M ->
    nm = S (ind_nn D) ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ) (Typeω@i) A A ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ (elim_mctx p D (List.firstn (ind_nu D) Ps)) (elim_mctx p D (List.firstn (ind_nu D) Ps)) ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs -> forall Θm Ξm Θ2 Ξ2, sem_emb Θ Ξ Θm Ξm Θ2 Ξ2 ->
       @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ (elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) (elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) /\
       @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) /\
       @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) /\
       @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm Γ) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> forall Θm Ξm Θ2 Ξ2, sem_emb Θ Ξ Θm Ξm Θ2 Ξ2 ->
         @sem_ctx (gc_mk Θ2 Ξ2) (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) /\
         @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) /\
         @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ)
           (elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) B B) ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)]) (a_elim Hh nm A Bs M) (a_elim Hh nm A Bs M).
Proof.
  intros * He Hl HPl HPs HMs HMM Hnm HA HMx HBn HBc Hnb HB HΓ2.
  destruct (k_decl _ _ _ _ _ _ _ _ _ He (presup_exp_ctx HMs) Hl) as (Hl2 & HD & Hc & Hsu & Hdt2).
  eapply (@rel_exp_elim_cong (gc_mk Θ2 Ξ2)); try eassumption; [ | | | reflexivity |].
  - intros * HP HT; exact (proj2 (proj2 (HPs _ _ _ HP HT _ _ _ _ He))).
  - exact (proj1 HMx).
  - intros c gs Hcon; exact (proj1 (proj1 (HBc _ _ Hcon _ _ _ _ He))).
  - intros * Hk Hk' Hcon; rewrite Hk in Hk'; injection Hk' as <-.
    exact (proj2 (proj2 (HB _ _ _ _ Hcon (List.nth_error_In _ _ Hk) _ _ _ _ He))).
Qed.

Lemma k_iota : forall Θ Ξ Θm Ξm Θ2 Ξ2 Γ p D Hh c gs Ps As nm A (i : nat) Bs n B,
    sem_emb Θ Ξ Θm Ξm Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       forall Θm Ξm Θ2 Ξ2, sem_emb Θ Ξ Θm Ξm Θ2 Ξ2 ->
         @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm Γ /\ @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ T P P) ->
    List.length As = List.length gs ->
    (forall k N T, List.nth_error As k = Some N -> List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) k = Some T ->
       forall Θm Ξm Θ2 Ξ2, sem_emb Θ Ξ Θm Ξm Θ2 Ξ2 ->
         @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm Γ /\ @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ T N N) ->
    nm = S (ind_nn D) ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ) (Typeω@i) A A ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ (elim_mctx p D (List.firstn (ind_nu D) Ps)) (elim_mctx p D (List.firstn (ind_nu D) Ps)) ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs -> forall Θm Ξm Θ2 Ξ2, sem_emb Θ Ξ Θm Ξm Θ2 Ξ2 ->
       @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ (elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) (elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) /\
       @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) /\
       @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) /\
       @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm Γ) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> forall Θm Ξm Θ2 Ξ2, sem_emb Θ Ξ Θm Ξm Θ2 Ξ2 ->
         @sem_ctx (gc_mk Θ2 Ξ2) (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) /\
         @ctx_mt (gc_mk Θ2 Ξ2) Θm Ξm (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) /\
         @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ)
           (elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) B B) ->
    brs_lookup Bs c = Some (n, B) ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ apps (a_con p c) (Ps ++ As) :: nil)])
      (a_elim Hh nm A Bs (apps (a_con p c) (Ps ++ As)))
      (B[sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ elim_ihs p nm A Bs (sb_of_list Id Ps) gs As)]).
Proof.
  intros * He HΓ Hl Hcon HPl HPs HAl HAs Hnm HA HMx HBn HBc Hnb HB Hlk HΓ2.
  destruct (k_decl _ _ _ _ _ _ _ _ _ He HΓ Hl) as (Hl2 & HD & Hc & Hsu & Hdt2).
  pose proof (decl_closed_nu D Hc) as Hle.
  set (Us := List.firstn (ind_nu D) Ps) in *.
  set (Ns := List.skipn (ind_nu D) Ps) in *.
  assert (HPeq : Ps = Us ++ Ns) by (symmetry; apply List.firstn_skipn).
  assert (HPs' : forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
                   @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ T P P)
    by (intros * HP HT; exact (proj2 (proj2 (HPs _ _ _ HP HT _ _ _ _ He)))).
  destruct (@params_valid_split (gc_mk Θ2 Ξ2) D Γ Ps Hc HPl HPs') as [HUs HNs]; fold Us Ns in HUs, HNs.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; lia).
  assert (HNl : List.length Ns = ind_nn D) by (unfold Ns; rewrite List.length_skipn; unfold ind_nn; lia).
  assert (HAs' : forall k N T, List.nth_error As k = Some N ->
                   List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) k = Some T ->
                   @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ T N N)
    by (intros * HN HT; rewrite <- HPeq in HT; exact (proj2 (proj2 (HAs _ _ _ HN HT _ _ _ _ He)))).
  pose proof (@rel_exp_elim_iota_at (gc_mk Θ2 Ξ2) Γ p D Us Ns As c gs nm A i Bs HD Hc Hsu Hdt2 Hl2 HΓ2 Hcon HUl HUs HNl HAl Hnm HA
                (proj1 HMx) HBn (fun c gs Hcon => proj1 (proj1 (HBc c gs Hcon _ _ _ _ He))) Hnb
                (fun c gs n B Hcon Hin => proj2 (proj2 (HB c gs n B Hcon Hin _ _ _ _ He))) HNs HAs' Hh n B Hlk) as Hi.
  rewrite HPeq, <- List.app_assoc; exact Hi.
Qed.

(** The head of an eliminator is not evaluated. *)
Lemma eval_elim_head_iff : forall {GC : GCtx} H H' nm A Bs M ρ r,
    ⟦ a_elim H nm A Bs M ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r <-> ⟦ a_elim H' nm A Bs M ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r.
Proof. intros; split; intros He; apply eval_elim_inv in He as (m & Hm & Hel); econstructor; eassumption. Qed.

Lemma rel_exp_elim_head : forall {GC : GCtx} Γ C H H' nm A Bs M N,
    @rel_exp_under_ctx GC Γ C (a_elim H' nm A Bs M) N -> @rel_exp_under_ctx GC Γ C (a_elim H nm A Bs M) N.
Proof.
  intros * HN; eapply rel_exp_under_ctx_eval_iff_l; [ | | exact HN ]; intros; cbn [exp_sub]; apply eval_elim_head_iff.
Qed.

(** The module of an inductive type at a path, as a term, evaluates to its
    type former. *)
Lemma eval_mem_ind_iff : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall mp x D, ind_lookup Θ Ξ (qname_app mp (x :: nil)) = Some D ->
    forall ρ r, ⟦ a_mem (qname_mod mp) x ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r <-> ⟦ a_ind (qname_app mp (x :: nil)) ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r.
Proof.
  intros * Hg * Hl ρ r.
  destruct (ind_lookup_not_def _ _ _ _ Hl) as [Hr _].
  assert (Hp : eval_modexp Θ Ξ (qname_mod mp) ρ (dm_global mp nil))
    by (apply eval_path_mod, (gc_chain_no_alias _ _ Hg); right; right; right; eauto).
  rewrite (eval_mem_noargs Θ Ξ) by exact (mod_qname_noargs _ _ (qname_mod_qname mp)).
  split.
  - intros (h & Hh & Hs).
    pose proof (functional_eval_modexp _ _ _ _ Hh Hp) as ->.
    inversion Hs; subst; try congruence.
    match goal with Ha : eval_apps _ _ _ nil _ |- _ => inversion Ha; subst end; constructor.
  - intros He; inversion He; subst; exists (dm_global mp nil); split; [ exact Hp |].
    eapply eval_sel_global_ind; [ exact Hr | exact Hl | constructor ].
Qed.

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
    pose proof (sme_rd _ _ _ _ _ _ ltac:(eassumption)) as Hsub;
    pose proof (em_res _ _ _ _ (sme_emb _ _ _ _ _ _ ltac:(eassumption))) as Hsub2;
    pose proof (em_wf _ _ _ _ (sme_emb _ _ _ _ _ _ ltac:(eassumption))) as Hwf2;
    pose proof (gmod_ok_of_wf _ _ _ _ Hwf2 (wf_gctx_closed _ _ ⋅ (wf_ctx_empty _ _ (sme_rdwf _ _ _ _ _ _ ltac:(eassumption))))) as Hgm;
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
    | apply subtyp_univ; [assumption | lia]
    | apply valid_exp_univ; assumption
    | apply valid_exp_nat_small; assumption
    | apply valid_exp_True_small; assumption | apply valid_exp_False_small; assumption
    (** Levels: the type, the literals, the two operations, and the level
        equations. *)
    | apply valid_exp_level; assumption | apply valid_exp_level_small; assumption
    | apply valid_exp_llit; assumption
    | apply rel_exp_succl_cong; assumption
    | apply rel_exp_maxl_cong; assumption
    | apply valid_exp_llit_succl; assumption
    | eapply rel_exp_maxl_zero; eassumption
    | eapply rel_exp_maxl_assoc; eassumption
    | eapply rel_exp_maxl_comm; eassumption
    | eapply rel_exp_maxl_idem; eassumption
    | eapply rel_exp_succl_maxl; eassumption
    | eapply rel_exp_maxl_succl; eassumption
    | eapply rel_exp_pi_cong_small_tm; eassumption
    | apply subtyp_suniv; [assumption | lia]
    | apply subtyp_small_large; assumption ].
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
    match goal with He : sem_emb ?S1 ?S2 ?M1 ?M2 ?T1 ?T2, Hpm : mod_qname ?H = Some ?p,
                    Hm : member_type ?S1 ?S2 _ ?H nil ?R, HT : mres_tl ?R = Some _,
                    Hm2 : member_type ?M1 ?M2 _ ?H nil ?R, HΓ : sem_ctx _ |- _ =>
      rewrite (mod_qname_inv _ _ Hpm) in Hm, Hm2 |- *;
      destruct (member_type_path_module _ _ _ _ _ _ Hm HT) as [r Hr];
      pose proof (sme_path _ _ _ _ _ _ He _ _ Hr) as Hp;
      split; [ exact (rel_me_path _ _ _ _ Hp HΓ Hm2 HT) |];
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
                    HU : sem_unf _ _ _ ?H, HU' : sem_unf _ _ _ ?H', Hm : member_type _ _ _ ?H (_ :: nil) ?R,
                    HT : mres_tl ?R = Some _
                    |- rel_modexp_under_ctx _ (me_mem _ _) _ /\ _ =>
      split; [ exact (rel_me_mem Hgm _ _ _ _ _ _ HH HS Hm HT) |];
      split; [ exact (sem_mt_mem _ _ _ HS) |]; split; [ exact (sem_mt_mem _ _ _ HS') |];
      split; [ exact (sem_unf_mem _ _ _ HU) |]; split; [ exact (sem_unf_mem _ _ _ HU') | split; assumption ] end ].
  all: try solve [
    match goal with HH : rel_modexp_under_ctx _ ?H ?H', HS : sem_mt _ _ _ ?H, HS' : sem_mt _ _ _ ?H',
                    HU : sem_unf _ _ _ ?H, HU' : sem_unf _ _ _ ?H',
                    Hm : member_type _ _ _ ?H nil ?R, HT : mres_tl ?R = Some ?T, Hv : tele_view ?T = Some (?B, _),
                    Hm' : member_type _ _ _ ?H' nil ?R', HT' : mres_tl ?R' = Some ?T', Hv' : tele_view ?T' = Some (?B', _),
                    HN : rel_exp_under_ctx _ ?B ?N ?N', HN' : rel_exp_under_ctx _ ?B' ?N' ?N'
                    |- rel_modexp_under_ctx _ (me_app _ _) _ /\ _ =>
      pose proof Hm as Hm2;
      pose proof Hm' as Hm2';
      destruct (arity_pi _ _ _ _ _ _ HS Hm2 HT Hv) as (l & HB & _ & HA);
      destruct (arity_pi _ _ _ _ _ _ HS' Hm2' HT' Hv') as (l' & HB' & _ & HA');
      pose proof (rel_modexp_refl_left HH) as HHl; pose proof (rel_modexp_refl_right HH) as HHr;
      pose proof (rel_exp_under_ctx_refl_left HN) as HNl;
      split; [ exact (rel_me_app Hgm _ _ _ _ _ _ _ _ _ _ HH HS Hm2 HT HA HN) |];
      split; [ exact (sem_mt_app Hgm _ _ _ _ _ _ _ _ HS HHl Hm2 HT HA HB HNl) |];
      split; [ exact (sem_mt_app Hgm _ _ _ _ _ _ _ _ HS' HHr Hm2' HT' HA' HB' HN') |];
      split; [ exact (sem_unf_app Hgm _ _ _ _ _ _ _ _ HS HU HHl Hm2 HT HA HB HNl) |];
      split; [ exact (sem_unf_app Hgm _ _ _ _ _ _ _ _ HS' HU' HHr Hm2' HT' HA' HB' HN') | split; assumption ] end ].
  all: try solve [ split; [ apply rel_modexp_sym; assumption | repeat (split; [ assumption |]); assumption ] ].
  all: try solve [ split; [ eapply rel_modexp_trans; eassumption | repeat (split; [ assumption |]); assumption ] ].
  (** An eliminator at a resolved head evaluates as at the canonical one. *)
  all: try solve [
    match goal with HM : rel_exp_under_ctx _ _ (a_elim (me_apps (qname_mod _) _) _ _ _ _) _ |- rel_exp_under_ctx _ _ (a_elim ?H _ _ _ _) _ =>
      pose proof (rel_exp_elim_head _ _ H _ _ _ _ _ _ HM) as Hx;
      first [ exact Hx | eapply rel_exp_under_ctx_trans; [ exact Hx | apply rel_exp_under_ctx_sym; exact Hx ] ] end ].
  (** The module of an inductive type at a path, as a term: its type former. *)
  all: try solve [
    match goal with He : sem_emb ?S1 ?S2 _ _ ?T1 ?T2, Hpm : mod_qname ?H = Some ?mp,
                    Hl : ind_lookup ?S1 ?S2 (qname_app ?mp (?x :: nil)) = Some ?D,
                    HΓ0 : wf_ctx ?S1 ?S2 ?Γ, HΓ : sem_ctx ?Γ |- _ =>
      pose proof (k_ind _ _ _ _ _ _ _ _ _ He HΓ0 Hl HΓ) as Hk;
      assert (Hx : @rel_exp_under_ctx (gc_mk T1 T2) Γ (ind_ty D) (a_mem H x) (a_ind (qname_app mp (x :: nil))))
        by (rewrite (mod_qname_inv _ _ Hpm); eapply rel_exp_under_ctx_eval_iff_l; [ | | exact Hk ];
            [ intros σ ρ r; cbn [exp_sub]; rewrite (mod_qname_sub _ _ _ (qname_mod_qname mp)) | intros ρ r ];
            exact (eval_mem_ind_iff _ _ Hwf2 _ _ _ (ind_lookup_gc_sub _ _ _ _ _ _ Hsub2 Hl) ρ r));
      first [ exact Hx | eapply rel_exp_under_ctx_trans; [ exact Hx | apply rel_exp_under_ctx_sym; exact Hx ] ] end ].
  (** The inductive types. *)
  all: try solve [ eapply k_ind; eassumption | eapply k_con; eassumption
                 | eapply k_elim; eassumption | eapply k_elim_cong; eassumption | eapply k_iota; eassumption ].
  (** The small universes at a level term, and their subtyping: the cases of
      [Completeness.LevelCases], whose premises are the induction
      hypotheses. *)
  all: try solve [ mauto 2 ].
  (** The literal of a sort: the side condition of its rule is an arithmetic
      one the search does not take. *)
  all: solve [ apply valid_exp_llit; assumption
             | apply rel_exp_llit; eassumption
             | eapply valid_exp_llit_succl; assumption
             | eapply valid_exp_maxl_absorb; eassumption
             | apply subtyp_level; assumption ].
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
    ⋅ ⊨ T : Typeω@i ->
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
      (exists i, @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ (Typeω@i) A A) /\
      (forall M, B = Some M -> @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ A M M)
  | ge_mod _ _ | ge_ind _ _ _ => True
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
      by (intros; apply eval_path_mod, (gc_chain_no_alias _ _ Hg); right; right; left; eauto).
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

(** Member types read at a smaller global context: a judgment about all
    member types at the larger one holds of those at the smaller. *)
Section MtDown.
  Context {GC : GCtx}.
  Variables (Θa : gdeps) (Ξa : gstack) (Θb : gdeps) (Ξb : gstack).
  Hypothesis Hs : gc_sub Θa Ξa Θb Ξb.

  Lemma sem_mt_down : forall Γ H, sem_mt Θb Ξb Γ H -> sem_mt Θa Ξa Γ H.
  Proof.
    intros * [S1 S2]; split.
    - intros * Hm Hk; exact (S1 _ _ (proj1 (member_type_gc_sub _ _ _ _ Hs) _ _ _ _ Hm) Hk).
    - intros * Hm0 Hk0 Hm Hk.
      exact (S2 _ _ _ _ (proj1 (member_type_gc_sub _ _ _ _ Hs) _ _ _ _ Hm0) Hk0
               (proj1 (member_type_gc_sub _ _ _ _ Hs) _ _ _ _ Hm) Hk).
  Qed.

  Fixpoint ctx_mt_down (Γ : ctx) (H : ctx_mt Θb Ξb Γ) {struct H} : ctx_mt Θa Ξa Γ
  with unit_mt_down (Γ : ctx) (U : gunit) (H : unit_mt Θb Ξb Γ U) {struct H} : unit_mt Θa Ξa Γ U.
  Proof.
    - destruct H; constructor; auto.
    - destruct H; constructor; [ apply ctx_mt_down; assumption | apply sem_mt_down; assumption ].
  Qed.
End MtDown.

(** What an entry other than a body module is worth at [Θ2 ⍮ Ξ2]: a
    definition, checked over [T], is valid at [⋅] and its type over [T]; an
    alias is a valid closed unit, its members read at [Θ2 ⍮ Ξ2]. *)
Definition sem_V (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B =>
      (exists i, @rel_exp_under_ctx (gc_mk Θ2 Ξ2) ⋅ (Typeω@i) A A) /\
      (forall M, B = Some M -> @rel_exp_under_ctx (gc_mk Θ2 Ξ2) ⋅ A M M) /\
      (exists A0 i, A = ctx_pi T A0 /\ @rel_exp_under_ctx (gc_mk Θ2 Ξ2) T (Typeω@i) A0 A0)
  | ge_mod _ U =>
      @sem_unit (gc_mk Θ2 Ξ2) ⋅ U /\ @unit_mt (gc_mk Θ2 Ξ2) Θ2 Ξ2 ⋅ U /\
      @rel_modexp_under_ctx (gc_mk Θ2 Ξ2) ⋅ (me_lit U) (me_lit U)
  | ge_ind _ _ _ => True
  end.

(** The telescope of a module. *)
Definition sem_F (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) : Prop :=
  @sem_ctx (gc_mk Θ2 Ξ2) T /\ tele_ass T.

(** A declaration. *)
Definition sem_VD (Θ2 : gdeps) (Ξ2 : gstack) (D : ind_decl) : Prop := @sem_core (gc_mk Θ2 Ξ2) D.

Lemma svalid_tele : forall Θ2 Ξ2 Ξ, gs_valid sem_V sem_F sem_VD Θ2 Ξ2 Ξ -> tele_ass (gs_tele Ξ).
Proof. intros * HΞ; destruct Ξ as [| [mp U] Ξ]; [ constructor | exact (proj2 (proj1 HΞ)) ]. Qed.

(** A sound embedding, its members read at [Θm ⍮ Ξm], from the validity at
    the target of what the source files and has open.  The source's bodies
    are the ones read at [Θm ⍮ Ξm], which may only grow on to the target. *)
Theorem sem_emb_of : forall Θ Ξ Θm Ξm Θ2 Ξ2,
    ⊢g Θ ⍮ Ξ -> ⊢g Θm ⍮ Ξm -> Emb Θ Ξ Θ2 Ξ2 ->
    gc_sub Θ Ξ Θm Ξm -> gc_sub Θm Ξm Θ2 Ξ2 ->
    (forall p r, gc_body Θ Ξ p = Some r -> gc_body Θm Ξm p = Some r) ->
    gds_valid sem_V sem_F sem_VD Θ2 Ξ2 Θ -> gs_valid sem_V sem_F sem_VD Θ2 Ξ2 Ξ ->
    sem_emb Θ Ξ Θm Ξm Θ2 Ξ2.
Proof.
  intros * Hg Hgm He Hsm Hmt Hbx HΘ HΞ; pose proof He as [Hg2 Hs].
  assert (Hglob : forall mp x b pv A B, gc_resolve Θ Ξ (qname_app mp (x :: nil)) = Some (ge_def b pv A B) ->
             @rel_exp_under_ctx (gc_mk Θ2 Ξ2) ⋅ A (a_mem (qname_mod mp) x) (a_mem (qname_mod mp) x) /\
             (forall M, b = true -> B = Some M -> @rel_exp_under_ctx (gc_mk Θ2 Ξ2) ⋅ A (a_mem (qname_mod mp) x) M)).
  { intros * Hr.
    destruct (good_resolve _ _ _ _ _ _ _ _ _ HΘ HΞ Hr) as (T & HA & HM & _).
    exact (glob_sem_of_raw _ _ Hg2 _ _ _ _ _ _ (gc_sub_resolve _ _ _ _ _ _ Hs Hr) (conj HA HM)). }
  constructor; [ exact He | exact Hsm | exact Hgm | | | |].
  - intros * Hpm Hr HΓ.
    rewrite (mod_qname_inv _ _ Hpm).
    eapply closed_weaken_sem; [ eassumption | | apply exp_wk_id | apply exp_wk_id | apply exp_wk_id ].
    exact (proj1 (Hglob _ _ _ _ _ _ Hr)).
  - intros * Hpm Hr HΓ.
    rewrite (mod_qname_inv _ _ Hpm).
    eapply closed_weaken_sem; [ eassumption | | apply exp_wk_id | apply exp_wk_id | apply exp_wk_id ].
    exact (proj2 (Hglob _ _ _ _ _ _ Hr) _ eq_refl eq_refl).
  - intros p r Hr.
    apply (@gpath_ok (gc_mk Θ2 Ξ2) Θ Ξ Θm Ξm Hg Hsm Hbx Hgm Hmt
             (gmod_ok_of_wf _ _ _ _ Hg2 (wf_gctx_closed _ _ ⋅ (wf_ctx_empty _ _ Hgm))) Hg2) with (r := r);
      [| | exact Hr ].
    + intros qp T Φ Hb.
      destruct (good_body _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hb) as [[HT HU] Hv].
      split; [ exact HT |]; split; [ exact HU |].
      intros * Hz.
      destruct (gm_valid_def _ _ _ _ _ _ _ _ _ _ _ _ Hv Hz) as (_ & _ & HA0).
      split; [ exact HA0 |].
      assert (Hne : z :: nil <> nil) by discriminate.
      refine (proj1 (Hglob _ _ b pv _ B _)).
      rewrite (proj2 (proj2 (closed_read_body _ _ Hg _ _ _ Hb (z :: nil))) Hne); exact Hz.
    + intros qp y U Hy.
      destruct (good_alias _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hy) as (T & pvT & HU & HUm & HUv).
      split; [ exact HU | split; [ exact (unit_mt_down _ _ _ _ Hmt _ _ HUm) | exact HUv ] ].
  - intros p D Hl; exact (good_ind _ _ _ _ _ _ _ _ _ HΘ HΞ Hl).
Qed.

(** The two readings: at the target, along an embedding keeping bodies, and
    at the source, along any. *)
Corollary sem_emb_target : forall Θ Ξ Θ2 Ξ2,
    ⊢g Θ ⍮ Ξ -> GoodV sem_V sem_F sem_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> sem_emb Θ Ξ Θ2 Ξ2 Θ2 Ξ2.
Proof.
  intros * Hg HG He; destruct (HG _ _ He) as [HΘ HΞ].
  exact (sem_emb_of _ _ _ _ _ _ Hg (emx_wf _ _ _ _ He) (Embx_emb _ _ _ _ He) (gc_subx_sub _ _ _ _ (emx_res _ _ _ _ He))
           (gc_sub_refl _ _) (fun p r => gc_subx_body _ _ _ _ p r (emx_res _ _ _ _ He)) HΘ HΞ).
Qed.

Corollary sem_emb_source : forall Θ Ξ Θ2 Ξ2,
    ⊢g Θ ⍮ Ξ -> Emb Θ Ξ Θ2 Ξ2 ->
    gds_valid sem_V sem_F sem_VD Θ2 Ξ2 Θ -> gs_valid sem_V sem_F sem_VD Θ2 Ξ2 Ξ -> sem_emb Θ Ξ Θ Ξ Θ2 Ξ2.
Proof.
  intros * Hg He HΘ HΞ.
  exact (sem_emb_of _ _ _ _ _ _ Hg Hg He (gc_sub_refl _ _) (em_res _ _ _ _ He) (fun p r H => H) HΘ HΞ).
Qed.

(** A judgment read at a target its source embeds soundly into. *)
Lemma kread : forall Θ Ξ Θm Ξm Θ2 Ξ2 Γ A M,
    sem_emb Θ Ξ Θm Ξm Θ2 Ξ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A M M.
Proof.
  intros * Hμ HM; destruct kripke_fundamental as (_ & Ke & _).
  destruct (Ke _ _ _ _ _ HM _ _ _ _ Hμ) as (_ & _ & H); exact H.
Qed.

(** A member of a module, checked in the closed telescope [T], is valid
    wherever its context is: its members read there. *)
Lemma sem_V_def : forall Θ Ξ T A M b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ T ⊢ M : A -> Emb Θ Ξ Θ2 Ξ2 ->
    gds_valid sem_V sem_F sem_VD Θ2 Ξ2 Θ -> gs_valid sem_V sem_F sem_VD Θ2 Ξ2 Ξ ->
    sem_V Θ2 Ξ2 T (ge_def b pv (ctx_pi T A) (Some (ctx_fn T M))).
Proof.
  intros * HM He HΘ HΞ.
  pose proof (sem_emb_source _ _ _ _ (ctx_wf_gctx _ _ _ (presup_exp_ctx HM)) He HΘ HΞ) as Hμ.
  destruct (presup_exp_typ HM) as [i HA].
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  split; [ exists j; exact (kread _ _ _ _ _ _ _ _ _ Hμ HT) |].
  split; [ intros ? [= <-]; exact (kread _ _ _ _ _ _ _ _ _ Hμ (ctx_fn_wf0 _ _ _ _ _ _ HA HM)) |].
  exists A, i; split; [ reflexivity | exact (kread _ _ _ _ _ _ _ _ _ Hμ HA) ].
Qed.

Lemma sem_V_ax : forall Θ Ξ A i b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i -> GoodV sem_V sem_F sem_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    sem_V Θ2 Ξ2 (gs_tele Ξ) (ge_def b pv (ctx_pi (gs_tele Ξ) A) None).
Proof.
  intros * HA HG He.
  pose proof (sem_emb_target _ _ _ _ (ctx_wf_gctx _ _ _ (presup_exp_ctx HA)) HG He) as Hμ.
  destruct (ctx_pi_wf0 _ _ _ _ _ HA) as [j HT].
  split; [ exists j; exact (kread _ _ _ _ _ _ _ _ _ Hμ HT) |].
  split; [ discriminate |].
  exists A, i; split; [ reflexivity | exact (kread _ _ _ _ _ _ _ _ _ Hμ HA) ].
Qed.

Lemma sem_V_alias : forall Θ Ξ pv Δ E Θ2 Ξ2,
    tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    GoodV sem_V sem_F sem_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    sem_V Θ2 Ξ2 (gs_tele Ξ) (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))).
Proof.
  intros * HΔ _ HE HG He.
  pose proof (sem_emb_target _ _ _ _ (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HE)) HG He) as Hμ.
  destruct kripke_fundamental as (_ & _ & _ & _ & _ & _ & Km).
  destruct (Km _ _ _ _ _ HE _ _ _ _ Hμ) as (HEv & HS & _ & _ & _ & HC & _).
  assert (Ht : tele_ass (Δ ++ gs_tele Ξ))
    by (apply Forall_app; split; [ exact HΔ | exact (svalid_tele _ _ _ (proj2 (HG _ _ He))) ]).
  rewrite <- (app_nil_r (Δ ++ gs_tele Ξ)) in HEv, HS, HC.
  assert (Hx : @rel_ext_under_ctx (gc_mk Θ2 Ξ2) ⋅ (Δ ++ gs_tele Ξ) (Δ ++ gs_tele Ξ))
    by (split; [| split ]; [ exact HC | exact HC | exact (sem_ctx_per_ctx HC) ]).
  destruct (rel_unit_alias Hx Ht Ht HEv HEv) as (HU & HsU & _).
  split; [ exact HsU |]; split; [ constructor; exact HS | exact HU ].
Qed.

Lemma sem_F_nil : forall Θ Ξ Δ Θ2 Ξ2,
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ -> GoodV sem_V sem_F sem_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 ->
    sem_F Θ2 Ξ2 (Δ ++ gs_tele Ξ).
Proof.
  intros * HΔ HC HG He.
  pose proof (sem_emb_target _ _ _ _ (ctx_wf_gctx _ _ _ HC) HG He) as Hμ.
  destruct kripke_fundamental as (Kc & _).
  split; [ exact (proj1 (Kc _ _ _ HC _ _ _ _ Hμ)) |].
  apply Forall_app; split; [ exact HΔ | exact (svalid_tele _ _ _ (proj2 (HG _ _ He))) ].
Qed.

(** A type at a sort is a type. *)
Lemma sort_large_sem : forall {GC : GCtx} S φ Γ X, ind_sort_univ S -> Γ ⊨ X : S[φ]ʷ -> exists j : nat, Γ ⊨ X : Typeω@j.
Proof.
  intros * [[i ->] | [t ->]] H; cbn [exp_wk] in H; [ exists i; exact H | exists 0; eapply rel_exp_suniv_tm_large; exact H ].
Qed.

(** A declaration typed at the source is semantically valid at the
    target: its judgments, read in the PER model. *)
Lemma sem_V_ind : forall Θ Ξ D Θ2 Ξ2,
    decl_typed Θ Ξ D -> GoodV sem_V sem_F sem_VD Θ Ξ -> Embx Θ Ξ Θ2 Ξ2 -> sem_VD Θ2 Ξ2 D /\ sem_F Θ2 Ξ2 (ind_uparams D).
Proof.
  intros * Hdt HG He.
  split; [| destruct (decl_typed_uparams _ _ _ Hdt) as [HUw HUa]; split; [| exact HUa ] ].
  2: { pose proof (sem_emb_target _ _ _ _ (ctx_wf_gctx _ _ _ HUw) HG He) as Hμ.
       destruct kripke_fundamental as (Kc & _); exact (proj1 (Kc _ _ _ HUw _ _ _ _ Hμ)). }
  unfold sem_VD.
  pose proof Hdt as (Hass & _ & Hle & HΔ & Hsu & [i HS] & _ & HA & HPl & HP & HN & Hnd & Hsh).
  pose proof (sem_emb_target _ _ _ _ (ctx_wf_gctx _ _ _ HΔ) HG He) as Hμ.
  destruct kripke_fundamental as (Kc & _).
  assert (Harg : forall c gs k A, ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
             @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (astrat gs k ++ ind_params D) ((ind_sort D)[wk_shiftn (k + ind_nn D)]ʷ) A A /\
             exists j : nat, @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (astrat gs k ++ ind_params D) (Typeω@j) A A).
  { intros * Hcon HA0.
    destruct (nonrec_nth_split _ _ _ HA0) as (gs1 & gs2 & Heq & Hk).
    pose proof (HA _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq) as HT.
    assert (Hls : List.length (cargs_strat gs1) = k) by (rewrite cargs_strat_nonrec, List.length_rev, List.length_map; exact Hk).
    rewrite Hls, (astrat_prefix gs1 (ca_arg A :: gs2)), Hk, <- Heq in HT.
    pose proof (kread _ _ _ _ _ _ _ _ _ Hμ HT) as H.
    split; [ exact H | exact (sort_large_sem _ _ _ _ Hsu H) ]. }
  assert (Hstrat : forall c gs k, ind_con D c = Some gs -> k <= List.length (cargs_nonrec gs) ->
             @sem_ctx (gc_mk Θ2 Ξ2) (astrat gs k ++ ind_params D)).
  { intros c gs k Hcon; induction k as [| k IH]; intros Hk.
    + unfold astrat; cbn [List.firstn List.rev List.app]; exact (proj1 (Kc _ _ _ HΔ _ _ _ _ Hμ)).
    + destruct (nth_error_lt_some' (cargs_nonrec gs) k ltac:(lia)) as [A HA0].
      assert (Hst : astrat gs (S k) = ce_ass A :: astrat gs k).
      { unfold astrat; rewrite (firstn_S_snoc _ _ (ce_ass A)) by (rewrite List.nth_error_map, HA0; reflexivity).
        rewrite List.rev_app_distr; reflexivity. }
      rewrite Hst; cbn [List.app].
      destruct (Harg _ _ _ _ Hcon HA0) as (_ & j & Hj).
      exact (@sem_ctx_ext_typ (gc_mk Θ2 Ξ2) _ _ _ (IH ltac:(lia)) Hj). }
  assert (Hdom : forall c gs gs1 t gs2 k B, ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             List.nth_error (ptyp_doms t) k = Some B ->
             @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (doms_ctx (List.firstn k (ptyp_doms t)) ++ astrat gs (List.length (cargs_nonrec gs1)) ++ ind_params D)
               ((ind_sort D)[wk_shiftn (k + List.length (cargs_nonrec gs1) + ind_nn D)]ʷ) B B /\
             exists j : nat, @rel_exp_under_ctx (gc_mk Θ2 Ξ2)
               (doms_ctx (List.firstn k (ptyp_doms t)) ++ astrat gs (List.length (cargs_nonrec gs1)) ++ ind_params D) (Typeω@j) B B).
  { intros * Hcon Heq HB.
    destruct (Hsh _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq) as [_ Hs2].
    assert (Hsplit : ptyp_doms t = List.firstn k (ptyp_doms t) ++ B :: List.skipn (S k) (ptyp_doms t))
      by (rewrite <- (skipn_nth_cons' _ _ _ HB), List.firstn_skipn; reflexivity).
    pose proof (Hs2 _ _ _ Hsplit) as HT.
    assert (Hk : List.length (List.firstn k (ptyp_doms t)) = k)
      by (rewrite List.length_firstn; assert (k < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence); lia).
    assert (Hls : List.length (cargs_strat gs1) = List.length (cargs_nonrec gs1))
      by (rewrite cargs_strat_nonrec, List.length_rev, List.length_map; reflexivity).
    rewrite Hk, Hls, (astrat_prefix gs1 (ca_rec t :: gs2)), <- Heq in HT.
    pose proof (kread _ _ _ _ _ _ _ _ _ Hμ HT) as H.
    split; [ exact H | exact (sort_large_sem _ _ _ _ Hsu H) ]. }
  constructor.
  - exact (proj1 (Kc _ _ _ HΔ _ _ _ _ Hμ)).
  - exists i; exact (kread _ _ _ _ _ _ _ _ _ Hμ HS).
  - destruct (ind_ty_typed0 _ _ _ Hdt) as [j Hj]; exists j; exact (kread _ _ _ _ _ _ _ _ _ Hμ Hj).
  - intros k A HA0.
    destruct (nparams_nth_split _ _ _ HA0) as [Δ1 HΔ1].
    assert (Hk : k < ind_nn D)
      by (rewrite <- (length_nparams D), <- List.length_rev; apply List.nth_error_Some; congruence).
    pose proof (HN _ _ _ HΔ1) as HT; rewrite length_npre in HT by lia.
    pose proof (kread _ _ _ _ _ _ _ _ _ Hμ HT) as H.
    split; [ exact H | exact (sort_large_sem _ _ _ _ Hsu H) ].
  - exact Hstrat.
  - exact Harg.
  - exact Hnd.
  - intros * Hcon Heq HPk HT.
    assert (Hls : List.length (cargs_nonrec gs1) = List.length (cargs_strat gs1))
      by (rewrite cargs_strat_nonrec, List.length_rev, List.length_map; reflexivity).
    rewrite Hls in HT.
    pose proof (HP _ _ _ _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq HPk HT) as H.
    rewrite (astrat_prefix gs1 (ca_rec t :: gs2)), <- Heq in H.
    exact (kread _ _ _ _ _ _ _ _ _ Hμ H).
  - exact Hdom.
  - intros * Hcon Heq; exact (proj1 (Hsh _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq)).
  - intros * Hcon Heq; exact (HPl _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq).
  - intros c gs gs1 t gs2 k Hcon Heq; induction k as [| k IH]; intros Hk.
    + cbn [List.firstn doms_ctx List.map List.rev List.app].
      apply Hstrat with (c := c); [ exact Hcon | rewrite Heq, cargs_nonrec_app, List.length_app; lia ].
    + destruct (nth_error_lt_some' (ptyp_doms t) k ltac:(lia)) as [B HB].
      rewrite (firstn_S_snoc _ _ _ HB), doms_ctx_snoc; cbn [List.app].
      destruct (Hdom _ _ _ _ _ _ _ Hcon Heq HB) as (_ & j & Hj).
      exact (@sem_ctx_ext_typ (gc_mk Θ2 Ξ2) _ _ _ (IH ltac:(lia)) Hj).
Qed.

(** Every well-formed global context is semantically sound: the identity is a
    sound embedding. *)
Theorem gctx_sem : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> sem_emb Θ Ξ Θ Ξ Θ Ξ.
Proof.
  intros * Hg; apply sem_emb_target; [ exact Hg | | apply Embx_refl; exact Hg ].
  exact (global_valid sem_V sem_F sem_VD sem_V_def sem_V_ax sem_V_alias sem_F_nil sem_V_ind _ _ Hg).
Qed.
