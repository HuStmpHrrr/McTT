(** * Record Types: the Semantic Rules

    The semantic rules of the record type former, of tuples and of
    projections, of their congruences, of field-β and of η.  Each holds
    because the record is valid at the target of a sound embedding
    ([record_model_of_emb]): its declaration is typed where it is looked
    up, and valid at the target ([valid_emb_record]); [Records/Model.v] then
    gives the rule. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Records Require Import Syntax.
From Mctt.Core.Completeness Require Import LogicalRelation.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.Records Require Import Model.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

#[local] Generalizable All Variables.

(** ** A Record along an Embedding *)

(** What [Records/Model.v] asks of a record [R] at [p], read at [GC]. *)
#[warnings="-cannot-define-projection"]
Record record_model {GC : GCtx} (p : qname) (R : record_decl) : Prop := mk_record_model
  { (** The record is found at [p] *)
    model_lookup : record_lookup gc_deps gc_stack p = Some R
    (** Its declaration is closed *)
  ; model_closed : record_closed R
    (** Its parameters are assumptions *)
  ; model_params_ass : tele_ass (record_params R)
    (** Its field names are distinct *)
  ; model_fields_distinct : List.NoDup (List.map fst (record_fields R))
    (** Its sort is a universe *)
  ; model_sort : ind_sort_univ (record_sort R)
    (** Its declaration is valid in the PER model *)
  ; model_valid : valid_record_decl R }.

(** A record of [Θ ⍮ Ξ] is one of the target of a sound embedding of it. *)
Lemma record_model_of_emb : forall Θ Ξ Θ2 Ξ2 p R, valid_emb Θ Ξ Θ2 Ξ2 -> record_lookup Θ Ξ p = Some R ->
    @record_model (gc_mk Θ2 Ξ2) p R.
Proof.
  intros * He Hl.
  pose proof (valid_emb_wf _ _ _ _ He) as Hg.
  pose proof (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ Hl) as Ht.
  constructor.
  - exact (record_lookup_gc_sub _ _ _ _ _ _ (gctx_embedding_resolution _ _ _ _ (valid_emb_emb _ _ _ _ He)) Hl).
  - exact (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ Hg) Hl).
  - exact (typed_params_ass _ _ _ Ht).
  - exact (typed_nodup _ _ _ Ht).
  - exact (record_typed_sort_univ _ _ _ Ht).
  - exact (valid_emb_record _ _ _ _ He _ _ Hl).
Qed.

(** Put what the model asks of the record [R] at [p] in the context. *)
Ltac record_model_intro Hl :=
  match goal with He : valid_emb _ _ _ _ |- _ =>
    let Hl2 := fresh "Hl2" in let Hc := fresh "Hc" in let Hass := fresh "Hass" in let Hnd := fresh "Hnd" in
    let Hsu := fresh "Hsu" in let HPv := fresh "HPv" in let HSv := fresh "HSv" in let HFv := fresh "HFv" in
    let HTv := fresh "HTv" in
    destruct (record_model_of_emb _ _ _ _ _ _ He Hl) as [Hl2 Hc Hass Hnd Hsu [HPv HSv HFv HTv]]
  end.

(** ** The Rules *)

Lemma sem_record :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     record_lookup Θ Ξ p = Some R ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_record p : record_ty R ).
Proof.
  intros * HΓ Hl; sem_intro; [ assumption |].
  record_model_intro Hl.
  apply closed_weaken_valid; [ assumption |].
  eapply valid_exp_under_ctx_record; eassumption.
Qed.

Lemma sem_exp_eq_record_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     record_lookup Θ Ξ p = Some R ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_record p ≈ a_record p : record_ty R ).
Proof. exact @sem_record. Qed.

Lemma sem_tuple :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ T ≈ apps_exp (a_record p) Ns : Typeω@i ->
     record_lookup Θ Ξ p = Some R ->
     List.length Ns = List.length (record_params R) ->
     (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A ->
        Θ ⍮ Ξ ⍮ Γ ⊨ N : A) ->
     List.map fst fs = List.map fst (record_fields R) ->
     (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
        Θ ⍮ Ξ ⍮ Γ ⊨ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_tuple T fs : T ).
Proof.
  intros * HT Hl Hn HNs Hnames HMs; sem_intro; [ assumption |].
  match goal with He : valid_emb _ _ _ _ |- _ => rename He into Hμ end.
  record_model_intro Hl.
  eapply valid_exp_under_ctx_tuple; try eassumption.
  - intros * HN HA; exact (sem_exp_eq_at_rel (HNs _ _ _ HN HA _ _ Hμ)).
  - intros * HM HU; exact (sem_exp_eq_at_rel (HMs _ _ _ _ HM HU _ _ Hμ)).
Qed.

Lemma sem_proj :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : apps_exp (a_record p) Ns ->
     record_lookup Θ Ξ p = Some R ->
     List.length Ns = List.length (record_params R) ->
     (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A ->
        Θ ⍮ Ξ ⍮ Γ ⊨ N : A) ->
     List.nth_error (record_fields R) k = Some (f, U) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_proj f M : U[sb_of_list Id (Ns ++ record_pre R k M)] ).
Proof.
  intros * HM Hl Hn HNs Hk; sem_intro; [ assumption |].
  match goal with He : valid_emb _ _ _ _ |- _ => rename He into Hμ end.
  record_model_intro Hl.
  eapply valid_exp_under_ctx_proj; try eassumption.
  intros * HN HA; exact (sem_exp_eq_at_rel (HNs _ _ _ HN HA _ _ Hμ)).
Qed.

Lemma sem_exp_eq_tuple_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ a_tuple T fs : T ->
     Θ ⍮ Ξ ⍮ Γ ⊨ T ≈ apps_exp (a_record p) Ns : Typeω@i ->
     record_lookup Θ Ξ p = Some R ->
     List.length Ns = List.length (record_params R) ->
     (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A ->
        Θ ⍮ Ξ ⍮ Γ ⊨ N : A) ->
     List.map fst fs = List.map fst (record_fields R) ->
     List.map fst fs' = List.map fst fs ->
     (forall k f M M' U, List.nth_error fs k = Some (f, M) -> List.nth_error fs' k = Some (f, M') ->
        List.nth_error (record_fields R) k = Some (f, U) ->
        Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_tuple T' fs' : T ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_tuple T fs ≈ a_tuple T' fs' : T ).
Proof.
  intros * Ht HT Hl Hn HNs Hnames Hnames' HMs Ht'; sem_intro; [ assumption |].
  match goal with He : valid_emb _ _ _ _ |- _ => rename He into Hμ end.
  record_model_intro Hl.
  eapply rel_exp_under_ctx_tuple_cong; try eassumption.
  - intros * HN HA; exact (sem_exp_eq_at_rel (HNs _ _ _ HN HA _ _ Hμ)).
  - intros * HM HM' HU; exact (sem_exp_eq_at_rel (HMs _ _ _ _ _ HM HM' HU _ _ Hμ)).
Qed.

Lemma sem_exp_eq_proj_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : apps_exp (a_record p) Ns ->
     record_lookup Θ Ξ p = Some R ->
     List.length Ns = List.length (record_params R) ->
     (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A ->
        Θ ⍮ Ξ ⍮ Γ ⊨ N : A) ->
     List.nth_error (record_fields R) k = Some (f, U) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_proj f M ≈ a_proj f M' : U[sb_of_list Id (Ns ++ record_pre R k M)] ).
Proof.
  intros * HMM Hl Hn HNs Hk; sem_intro; [ assumption |].
  match goal with He : valid_emb _ _ _ _ |- _ => rename He into Hμ end.
  record_model_intro Hl.
  eapply rel_exp_under_ctx_proj_cong; try eassumption.
  intros * HN HA; exact (sem_exp_eq_at_rel (HNs _ _ _ HN HA _ _ Hμ)).
Qed.

Lemma sem_exp_eq_field_beta :
  `( field_lookup fs f = Some M ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_proj f (a_tuple T fs) : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_proj f (a_tuple T fs) ≈ M : A ).
Proof.
  intros * Hf Hp HM; sem_intro; [ assumption |].
  eapply rel_exp_under_ctx_field_beta; eassumption.
Qed.

Lemma sem_exp_eq_record_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : apps_exp (a_record p) Ns ->
     record_lookup Θ Ξ p = Some R ->
     List.length Ns = List.length (record_params R) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_tuple (apps_exp (a_record p) Ns) (record_eta_fields R M) : apps_exp (a_record p) Ns ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ a_tuple (apps_exp (a_record p) Ns) (record_eta_fields R M) : apps_exp (a_record p) Ns ).
Proof.
  intros * HM Hl Hn Ht; sem_intro; [ assumption |].
  record_model_intro Hl.
  eapply rel_exp_under_ctx_record_eta; eassumption.
Qed.
