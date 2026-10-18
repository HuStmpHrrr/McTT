(** * The Cases of the Fundamental Theorem of the Gluing Model

    One lemma per rule of contexts, terms and universes, about the gluing
    judgments of [Judgments.v]: the conclusion of the rule glues when its
    premises do.  Each lemma fixes a sound embedding and is the case lemma
    of the gluing relation at its target ([kglu_case]).  The model is unary,
    so of the other judgments (equality, subtyping, extensions, units and
    module expressions) only their context glues, from their premises.

    The inductive types, the module [let], the members and subsumption also
    read syntactic premises of their rules: a declaration is typed by its
    derivation, and the premises the gluing case needs at the target are
    the syntactic ones moved along the embedding ([emb_preserves_wf]).

    [soundness_fundamental] threads the cases through the induction on
    derivations. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import MemberLemmas GlobalModules GlobalPaths DescTyping LookupSound.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases ModuleSem GlobalSem.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Soundness Require Import LevelCases.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases TermStructureCases MemberCases
  SubtypingCases UniverseCases FunctionCases LetCases TrueFalseCases IndCases ModuleCases.
From Mctt.Core.Soundness Require Export Judgments.
Require Import Mctt.Core.Soundness.IndElimCases.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.
#[local] Generalizable All Variables.

(** ** The case tactic *)

(** A universe at a target from its parts. *)
Lemma kglu_univ_at_intro : forall Θ2 Ξ2 Γ U,
    @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ /\
    ((exists i : nat, U = Typeω@i) \/ (exists L (n : nat), U = Type⟨L⟩ /\ @glu_rel_exp (gc_mk Θ2 Ξ2) Γ L (Level@n))) ->
    kglu_univ_at Θ2 Ξ2 Γ U.
Proof. intros * [? ?]; constructor; assumption. Qed.

(** Fix a sound embedding and read every premise at its target. *)
Ltac kglu_intro :=
  unfold kglu_ctx, kglu_exp, kglu_univ in *; intros;
  repeat match goal with IH : forall _ _, glu_emb _ _ _ _ -> _, Hμ : glu_emb _ _ _ _ |- _ =>
    specialize (IH _ _ Hμ) end;
  repeat match goal with H : kglu_univ_at _ _ _ _ |- _ => destruct H end;
  try match goal with |- kglu_univ_at _ _ _ _ => apply kglu_univ_at_intro end.

(** The case lemmas of the gluing relation at one global context, tried in
    turn: the conclusions of the rules are distinct. *)
Ltac kglu_close :=
  (** Contexts. *)
  try solve [ eapply glu_rel_ctx_empty; eapply em_wf, gme_emb; eassumption ];
  try solve [ eapply glu_rel_ctx_extend; [ eapply presup_ctx_glu_rel_exp |]; eassumption ];
  try solve [ eapply glu_rel_ctx_extend_def; [ eapply presup_ctx_glu_rel_exp | |]; eassumption ];
  (** Universes: large, or small at a level that glues. *)
  try solve [ split; [ assumption | left; eexists; reflexivity ] ];
  try solve [ split; [ eapply presup_ctx_glu_rel_exp; eassumption | right; do 2 eexists; split; [ reflexivity | eassumption ] ] ];
  (** [Π]: the case of a large universe and that of a small one. *)
  try match goal with HU : (exists i, ?U = Typeω@i) \/ _ |- _ =>
        destruct HU as [[? ->] | (? & ? & -> & ?)] end;
  try solve [ apply glu_rel_exp_typ; assumption
    | eapply glu_rel_exp_univ_lvl; eassumption
    | apply glu_rel_exp_level; assumption | apply glu_rel_exp_level_small; assumption
    | apply glu_rel_exp_llit; assumption
    | eapply glu_rel_exp_succl; eassumption
    | eapply glu_rel_exp_maxl; eassumption
    | apply glu_rel_exp_True_small; assumption | apply glu_rel_exp_False_small; assumption
    | eapply glu_rel_exp_pi_small_tm; eassumption
    | apply glu_rel_exp_True; assumption | apply glu_rel_exp_False; assumption
    | apply glu_rel_exp_true; assumption
    | eapply glu_rel_exp_exfalso; eassumption
    | eapply glu_rel_exp_pi; eassumption | eapply glu_rel_exp_fn; eassumption
    | eapply glu_rel_exp_app; eassumption ];
  try solve [ eapply glu_rel_exp_vlookup; eassumption ];
  try solve [ eapply k_ind; eassumption | eapply k_con; eassumption | eapply k_elim; eassumption ];
  try solve [ eapply glu_rel_exp_let; eassumption ];
  try solve [ eapply k_mem; eassumption ];
  (** The context of the other judgments. *)
  try solve [ assumption | eapply presup_ctx_glu_rel_exp; eassumption
            | eapply glu_rel_ctx_tail; eassumption
            | eapply glu_rel_ctx_tail, presup_ctx_glu_rel_exp; eassumption ];
  (** Module slots, module [let]s and subsumption: their premises moved
      syntactically. *)
  try solve [
    match goal with Hμ : glu_emb _ _ _ _ |- _ =>
      let Hem := fresh "Hem" in
      pose proof (gme_emb _ _ _ _ Hμ) as Hem;
      let Ec := fresh "Ec" in let Ee := fresh "Ee" in let Eq := fresh "Eq" in let Est := fresh "Est" in
      let Ex := fresh "Ex" in let Eu := fresh "Eu" in let Em := fresh "Em" in
      destruct (emb_preserves_wf _ _ _ _ Hem) as (Ec & Ee & Eq & Est & Ex & Eu & Em);
      first
        [ eapply (@glu_rel_ctx_extend_mod (gc_mk _ _)); [ eassumption | apply Eu; eassumption ]
        | eapply (@glu_rel_exp_let_mod (gc_mk _ _)); [ apply Eu; eassumption | apply Ee; eassumption | eassumption ]
        | match goal with Hs : wf_subtyp _ _ _ _ _ |- _ =>
            eapply glu_rel_exp_subtyp; [ eassumption | eassumption | apply Est; exact Hs ] end ] end ].

Ltac kglu_case := kglu_intro; kglu_close.

(** ** The cases *)

(** *** Contexts *)

Lemma glued_ctx_empty :
  `( ⊢ᵍ Θ ⍮ Ξ ->
     ⊩ Θ ⍮ Ξ ⍮ ⋅ ).
Proof. kglu_case. Qed.

Lemma glued_ctx_extend :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▹ A ).
Proof. kglu_case. Qed.

Lemma glued_ctx_extend_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ).
Proof. kglu_case. Qed.

(** A slot glues when the context does and its unit is well formed. *)
Lemma glued_ctx_extend_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▹ₘ U ).
Proof. kglu_case. Qed.

(** *** Terms *)

Lemma glued_typ :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ Typeω@i : Typeω@(S i) ).
Proof. kglu_case. Qed.

Lemma glued_univ :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊩ Type⟨M⟩ : Type⟨succl M⟩ ).
Proof. kglu_case. Qed.

Lemma glued_level :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ Level@n : Type@0 ).
Proof. kglu_case. Qed.

Lemma glued_llit :
  `( fst o <= n ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ 𝕃ᵒ o : Level@n ).
Proof. kglu_case. Qed.

Lemma glued_succl :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊩ succl M : Level@n ).
Proof. kglu_case. Qed.

Lemma glued_maxl :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊩ maxl M N : Level@n ).
Proof. kglu_case. Qed.

Lemma glued_True :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ⊤ : Type@0 ).
Proof. kglu_case. Qed.

Lemma glued_true :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ⋆ : ⊤ ).
Proof. kglu_case. Qed.

Lemma glued_False :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ⊥ : Type@0 ).
Proof. kglu_case. Qed.

Lemma glued_exfalso :
  `( Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊩ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : ⊥ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ efq M return A : A[Id,,M] ).
Proof. kglu_case. Qed.

Lemma glued_ind :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_ind p : ind_ty D ).
Proof. kglu_case. Qed.

Lemma glued_con :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     ⊩ Θ ⍮ Ξ ⍮ cargs_ctx p D gs ++ ind_params D ->
     (forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
        ⊩ Θ ⍮ Ξ ⍮ (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D)
                  ▹ ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t)) ->
     Θ ⍮ Ξ ⍮ ⋅ ⊢ con_ty p D gs : Typeω@i ->
     Θ ⍮ Ξ ⍮ ⋅ ⊩ con_ty p D gs : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_con p c : con_ty p D gs ).
Proof. kglu_case. Qed.

Lemma glued_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     List.length Ps = ind_np D ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊩ P : T) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : apps (a_ind p) Ps ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : apps (a_ind p) Ps ->
     nm = S (ind_nn D) ->
     Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊩ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D (List.firstn (ind_nu D) Ps) ->
     brs_names (ind_cons D) Bs ->
     (forall c gs, ind_con D c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
     (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
        n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
     (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
        Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
          : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
     (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
        Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊩ B
          : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_elim nm A Bs M : A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] ).
Proof. kglu_case. Qed.

Lemma glued_pi :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ᵤ U ->
     Θ ⍮ Ξ ⍮ Γ ⊩ A : U ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊩ B : U[↑]ʷ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ Π A B : U ).
Proof. kglu_case. Qed.

Lemma glued_fn :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊩ M : B ->
     Θ ⍮ Ξ ⍮ Γ ⊩ λ A M : Π A B ).
Proof. kglu_case. Qed.

Lemma glued_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊩ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : Π A B ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : A ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M $ N : B[Id,,N] ).
Proof. kglu_case. Qed.

Lemma glued_let :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊩ B : C ->
     let_ann oA A ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_let (b_def oA M) B : C[Id,,M] ).
Proof. kglu_case. Qed.

Lemma glued_let_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊩ C : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : C ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊩ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ℓₘ U in B : C[Id ,,ₘ me_lit U] ).
Proof. kglu_case. Qed.

Lemma glued_mem :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     ds_ty Θ Ξ R = Some A ->
     (forall M, ds_red R = Some M -> Θ ⍮ Ξ ⍮ Γ ⊩ M : A) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_mem H x : A ).
Proof. kglu_case. Qed.

Lemma glued_vlookup :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊩ #x : A ).
Proof. kglu_case. Qed.

Lemma glued_exp_subtyp :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊩ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A' ).
Proof. kglu_case. Qed.

(** *** Universes *)

Lemma glued_is_univ_large :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ᵤ Typeω@i ).
Proof. kglu_case. Qed.

Lemma glued_is_univ_small :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ L : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊩ᵤ Type⟨L⟩ ).
Proof. kglu_case. Qed.

(** ** The fundamental theorem

    Contexts, terms and universes glue by their case lemmas, one per rule in
    the order of the rules; every other judgment glues its context, from its
    premises. *)
Theorem soundness_fundamental :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊩ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ ⍮ Ξ ⍮ Γ ⊩ M : A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> ⊩ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> ⊩ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> Θ ⍮ Ξ ⍮ Γ ⊩ᵤ U) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> ⊩ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> ⊩ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> ⊩ Θ ⍮ Ξ ⍮ Γ).
Proof.
  apply syntactic_wf_mut_ind; intros;
    [ (** contexts *)
      eapply glued_ctx_empty | eapply glued_ctx_extend | eapply glued_ctx_extend_def | eapply glued_ctx_extend_mod
    | (** terms *)
      eapply glued_typ | eapply glued_univ | eapply glued_level | eapply glued_llit | eapply glued_succl
    | eapply glued_maxl | eapply glued_True | eapply glued_true | eapply glued_False | eapply glued_exfalso
    | eapply glued_ind | eapply glued_con | eapply glued_elim | eapply glued_pi | eapply glued_fn | eapply glued_app
    | eapply glued_let | eapply glued_let_mod | eapply glued_mem | eapply glued_vlookup | eapply glued_exp_subtyp
    | (** term equality: the context *)
      .. ];
    try eassumption.
  (** The universes. *)
  all: try solve [ first [ eapply glued_is_univ_large | eapply glued_is_univ_small ]; eassumption ].
  (** The context of the other judgments, from their premises. *)
  all: kglu_case.
Qed.

Lemma kglu_read : forall Θ1 Ξ1 Θ2 Ξ2 A M,
    glu_emb Θ1 Ξ1 Θ2 Ξ2 ->
    Θ1 ⍮ Ξ1 ⍮ ⋅ ⊢ M : A ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) ⋅ M A.
Proof. intros * Hμ HM; exact (proj1 (proj2 soundness_fundamental) _ _ _ _ _ HM _ _ Hμ). Qed.
