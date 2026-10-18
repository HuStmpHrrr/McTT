(** * The Cases of the Fundamental Theorem

    One lemma per rule, about the semantic judgments of [Judgments.v]: the
    conclusion of the rule holds semantically when its premises do.  Each
    lemma fixes a sound embedding and is the case lemma of the relation at
    its target ([kcase]).  A few rules about modules also need a syntactic
    premise of theirs, from which a case lemma at the target reads what a
    module expression denotes; they take it beside the semantic one.

    [completeness_fundamental] threads the cases through the induction on
    derivations. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import MemberLemmas GlobalModules GlobalPaths DescTyping LookupSound IndTyping.
From Mctt.Core.Completeness Require Import
  ContextCases FunctionCases LetCases LevelCases SubstitutionCases SubtypingCases
  TrueFalseCases UniverseCases VariableCases LogicalRelation UnitCases InstanceCases
  MemberReps IndCases TeleSem ElimCases ElimIota
  ModuleVal ModuleSem UnitSub ModexpRules GlobalArgs IndSem SemK UnitBody FiledSem UnitSem MemSem CanonSem AppSem SelSem
  ModuleCases.
From Mctt.Core.Completeness Require Export Judgments.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.
#[local] Generalizable All Variables.

(** ** The inductive types at the target *)

Lemma k_decl : forall Θ Ξ Θ2 Ξ2 p D, sem_emb Θ Ξ Θ2 Ξ2 -> ind_lookup Θ Ξ p = Some D ->
    ind_lookup Θ2 Ξ2 p = Some D /\ @sem_decl (gc_mk Θ2 Ξ2) D /\ decl_closed D /\ ind_sort_univ (ind_sort D) /\
    decl_typed Θ2 Ξ2 D.
Proof.
  intros * He Hl.
  destruct (decl_of_glookup _ _ _ _ (sme_wf _ _ _ _ He) Hl) as [Hdt Hc].
  pose proof (decl_typed_emb _ _ _ _ _ (sme_emb _ _ _ _ He) Hdt) as Hdt2.
  pose proof (dt_sort_univ _ _ _ Hdt) as Hsu.
  pose proof (ind_lookup_gc_sub _ _ _ _ _ _ (em_res _ _ _ _ (sme_emb _ _ _ _ He)) Hl) as Hl2.
  split; [ exact Hl2 | split; [| split; [ exact Hc | split; [ exact Hsu | exact Hdt2 ] ] ] ].
  exact (@sem_decl_of_core (gc_mk Θ2 Ξ2) D (sme_ind _ _ _ _ He _ _ Hl) Hc Hsu Hdt2).
Qed.

Lemma k_ind : forall Θ Ξ Θ2 Ξ2 Γ p D, sem_emb Θ Ξ Θ2 Ξ2 -> ind_lookup Θ Ξ p = Some D ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ -> @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (ind_ty D) (a_ind p) (a_ind p).
Proof.
  intros * He Hl HΓ2.
  destruct (k_decl _ _ _ _ _ _ He Hl) as (Hl2 & HD & Hc & Hsu & _).
  exact (@closed_weaken_valid (gc_mk Θ2 Ξ2) Γ _ _ _ HΓ2 (@valid_exp_ind0 (gc_mk Θ2 Ξ2) D HD Hc Hsu p Hl2)).
Qed.

Lemma k_con : forall Θ Ξ Θ2 Ξ2 Γ p D c gs, sem_emb Θ Ξ Θ2 Ξ2 -> ind_lookup Θ Ξ p = Some D ->
    ind_con D c = Some gs ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ -> @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (con_ty p D gs) (a_con p c) (a_con p c).
Proof.
  intros * He Hl Hcon HΓ2.
  destruct (k_decl _ _ _ _ _ _ He Hl) as (Hl2 & HD & Hc & Hsu & _).
  destruct (@sd_conty (gc_mk Θ2 Ξ2) D HD p c gs Hl2 Hcon) as [j HT].
  pose proof (@sd_cargs (gc_mk Θ2 Ξ2) D HD p c gs Hl2 Hcon) as HΨ.
  exact (@closed_weaken_valid (gc_mk Θ2 Ξ2) Γ _ _ _ HΓ2 (@valid_exp_con0 (gc_mk Θ2 Ξ2) D HD Hc Hsu p Hl2 c gs Hcon HΨ j HT)).
Qed.

Lemma k_elim_cong : forall Θ Ξ Θ2 Ξ2 Γ p D Ps M M' nm A A' (i : nat) Bs Bs',
    sem_emb Θ Ξ Θ2 Ξ2 -> ind_lookup Θ Ξ p = Some D ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊨ P : T) ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (apps (a_ind p) Ps) M M' ->
    nm = S (ind_nn D) ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ) (Typeω@i) A A' ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ (elim_mctx p D (List.firstn (ind_nu D) Ps)) (elim_mctx p D (List.firstn (ind_nu D) Ps)) ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs ->
       Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
    List.map fst Bs = List.map fst Bs' ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall k c gs n B B', List.nth_error Bs k = Some (c, n, B) -> List.nth_error Bs' k = Some (c, n, B') ->
       ind_con D c = Some gs ->
       Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B ≈ B' : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)]) (a_elim nm A Bs M) (a_elim nm A' Bs' M').
Proof.
  intros * He Hl HPl HPs HMM Hnm HA HMx HBn HBc HBf Hnb HB HΓ2.
  destruct (k_decl _ _ _ _ _ _ He Hl) as (Hl2 & HD & Hc & Hsu & Hdt2).
  eapply (@rel_exp_elim_cong (gc_mk Θ2 Ξ2)); try eassumption.
  - intros * HP HT; exact (kea_rel (HPs _ _ _ HP HT _ _ He)).
  - exact (rxu_left _ _ _ HMx).
  - intros c gs Hcon; exact (rxu_left _ _ _ (kxa_rel (HBc _ _ Hcon _ _ He))).
  - intros * Hk Hk' Hcon; exact (kea_rel (HB _ _ _ _ _ _ Hk Hk' Hcon _ _ He)).
Qed.

Lemma k_elim : forall Θ Ξ Θ2 Ξ2 Γ p D Ps M nm A (i : nat) Bs,
    sem_emb Θ Ξ Θ2 Ξ2 -> ind_lookup Θ Ξ p = Some D ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊨ P : T) ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (apps (a_ind p) Ps) M M ->
    nm = S (ind_nn D) ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ) (Typeω@i) A A ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ (elim_mctx p D (List.firstn (ind_nu D) Ps)) (elim_mctx p D (List.firstn (ind_nu D) Ps)) ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs ->
       Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
       Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)]) (a_elim nm A Bs M) (a_elim nm A Bs M).
Proof.
  intros * He Hl HPl HPs HMM Hnm HA HMx HBn HBc Hnb HB HΓ2.
  destruct (k_decl _ _ _ _ _ _ He Hl) as (Hl2 & HD & Hc & Hsu & Hdt2).
  eapply (@rel_exp_elim_cong (gc_mk Θ2 Ξ2)); try eassumption; [ | | | reflexivity |].
  - intros * HP HT; exact (kea_rel (HPs _ _ _ HP HT _ _ He)).
  - exact (rxu_left _ _ _ HMx).
  - intros c gs Hcon; exact (rxu_left _ _ _ (kxa_rel (HBc _ _ Hcon _ _ He))).
  - intros * Hk Hk' Hcon; rewrite Hk in Hk'; injection Hk' as <-.
    exact (kea_rel (HB _ _ _ _ Hcon (List.nth_error_In _ _ Hk) _ _ He)).
Qed.

Lemma k_iota : forall Θ Ξ Θ2 Ξ2 Γ p D c gs Ps As nm A (i : nat) Bs n B,
    sem_emb Θ Ξ Θ2 Ξ2 -> ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊨ P : T) ->
    List.length As = List.length gs ->
    (forall k N T, List.nth_error As k = Some N -> List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊨ N : T) ->
    nm = S (ind_nn D) ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ) (Typeω@i) A A ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ (elim_mctx p D (List.firstn (ind_nu D) Ps)) (elim_mctx p D (List.firstn (ind_nu D) Ps)) ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs ->
       Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
       Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
    brs_lookup Bs c = Some (n, B) ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ apps (a_con p c) (Ps ++ As) :: nil)])
      (a_elim nm A Bs (apps (a_con p c) (Ps ++ As)))
      (B[sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ elim_ihs nm A Bs (sb_of_list Id Ps) gs As)]).
Proof.
  intros * He Hl Hcon HPl HPs HAl HAs Hnm HA HMx HBn HBc Hnb HB Hlk HΓ2.
  destruct (k_decl _ _ _ _ _ _ He Hl) as (Hl2 & HD & Hc & Hsu & Hdt2).
  pose proof (decl_closed_nu D Hc) as Hle.
  set (Us := List.firstn (ind_nu D) Ps) in *.
  set (Ns := List.skipn (ind_nu D) Ps) in *.
  assert (HPeq : Ps = Us ++ Ns) by (symmetry; apply List.firstn_skipn).
  assert (HPs' : forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
                   @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ T P P)
    by (intros * HP HT; exact (kea_rel (HPs _ _ _ HP HT _ _ He))).
  destruct (@params_valid_split (gc_mk Θ2 Ξ2) D Γ Ps Hc HPl HPs') as [HUs HNs]; fold Us Ns in HUs, HNs.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; lia).
  assert (HNl : List.length Ns = ind_nn D) by (unfold Ns; rewrite List.length_skipn; unfold ind_nn; lia).
  assert (HAs' : forall k N T, List.nth_error As k = Some N ->
                   List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) k = Some T ->
                   @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ T N N)
    by (intros * HN HT; rewrite <- HPeq in HT; exact (kea_rel (HAs _ _ _ HN HT _ _ He))).
  pose proof (@rel_exp_elim_iota_at (gc_mk Θ2 Ξ2) Γ p D Us Ns As c gs nm A i Bs HD Hc Hsu Hdt2 Hl2 HΓ2 Hcon HUl HUs HNl HAl Hnm HA
                (rxu_left _ _ _ HMx) HBn (fun c gs Hcon => rxu_left _ _ _ (kxa_rel (HBc c gs Hcon _ _ He))) Hnb
                (fun c gs n B Hcon Hin => kea_rel (HB c gs n B Hcon Hin _ _ He)) HNs HAs' n B Hlk) as Hi.
  rewrite HPeq, <- List.app_assoc; exact Hi.
Qed.

(** A body unit, from the semantic premises of its rule. *)
Lemma k_unit_body_k : forall Θ Ξ Θ2 Ξ2 Γ Δ Δ' Φ Φ' Φx Φx' (lv : String.string -> nat), sem_emb Θ Ξ Θ2 Ξ2 ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' ->
    body_xp Θ Ξ (Δ ++ Γ) Φ Φx -> body_xp Θ Ξ (Δ' ++ Γ) Φ' Φx' ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ Δ Δ' -> @sem_ctx (gc_mk Θ2 Ξ2) Γ ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ (body_ctx Φx ++ Δ) (body_ctx Φx ++ Δ) ->
    @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ Ξ ((body_ctx Φx ++ Δ) ++ Γ) ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ (body_ctx Φx' ++ Δ') (body_ctx Φx' ++ Δ') ->
    @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ Ξ ((body_ctx Φx' ++ Δ') ++ Γ) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ A[σ] ≈ A'[σ'] : Typeω@(lv y)) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ M[σ] ≈ M'[σ'] : A[σ]) ->
    (forall y Φ0 pv U Φ0' pv' U' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_mod pv' U')) ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ᵘ U[σ]ᵘ ≈ U'[σ']ᵘ) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δ ++ Γ ⊨ᵐ H ≈ H) ->
    (forall k Ψ' H', nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> Θ ⍮ Ξ ⍮ Ψ' ++ Δ' ++ Γ ⊨ᵐ H' ≈ H') ->
    (forall k Φ0 H Φ0' H' σ σ',
      nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ᵐ H[σ]ᵐ ≈ H'[σ']ᵐ) ->
    tele_ass Δ -> tele_ass Δ' -> List.length Δ = List.length Δ' ->
    body_shape Φ Φ' -> body_shape Φx Φx' -> List.NoDup (gm_names Φ) ->
    @rel_unit_under_ctx (gc_mk Θ2 Ξ2) Γ (gu_open Δ Φ) (gu_open Δ' Φ') /\
    @SemK.semK (gc_mk Θ2 Ξ2) Θ Ξ Γ (me_lit (gu_open Δ Φ)) /\ @SemK.semK (gc_mk Θ2 Ξ2) Θ Ξ Γ (me_lit (gu_open Δ' Φ')).
Proof.
  intros * He Hu Hx Hx' HΔ HΓ HC HokC HC' HokC' HA HM HU Ho Ho' HO Ha Ha' Hl Hs Hsxx Hnd.
  pose proof (sme_emb _ _ _ _ He) as Hemb.
  pose proof (em_res _ _ _ _ Hemb) as Hsub; pose proof (em_wf _ _ _ _ Hemb) as Hgw.
  change (⊢ᵍ @gc_deps (gc_mk Θ2 Ξ2) ⍮ @gc_stack (gc_mk Θ2 Ξ2)) in Hgw.
  change (gc_sub Θ Ξ (@gc_deps (gc_mk Θ2 Ξ2)) (@gc_stack (gc_mk Θ2 Ξ2))) in Hsub.
  apply (@k_unit_body (gc_mk Θ2 Ξ2) Hgw _ _ (sme_wf _ _ _ _ He) Hsub (sme_filed _ _ _ _ He) _ _ _ _ _ _ _ Hu Hx Hx' HΔ HΓ
           (rxu_left _ _ _ HC) HokC (rxu_left _ _ _ HC') HokC'); try assumption.
  - intros * Hp Hp' Hf Hf'; split; [ eexists; exact (kea_rel (HA _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hp' Hf Hf' _ _ He)) |].
    exact (kea_rel (HM _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hp' Hf Hf' _ _ He)).
  - intros * Hp Hp' Hf Hf'; exact (ruu_lit _ _ _ (kna_rel (HU _ _ _ _ _ _ _ _ _ Hp Hp' Hf Hf' _ _ He))).
  - intros * Hk Hk' Hf Hf'; exact (kma_rel (HO _ _ _ _ _ _ _ Hk Hk' Hf Hf' _ _ He)).
  - intros * Hk; destruct (Ho _ _ _ Hk _ _ He) as [_ HV HS _]; exact (conj HV HS).
  - intros * Hk; destruct (Ho' _ _ _ Hk _ _ He) as [_ HV HS _]; exact (conj HV HS).
Qed.

(** ** The case tactic

    [kintro] fixes the embedding and reads the premises at its target; the
    conclusion is then the case lemma of the relation there.  The lemma is
    found by trying them, as the conclusions of the rules are distinct. *)

Ltac kclose Hgw Hgm Hsub Hgf :=
  (** Contexts. *)
  try solve [ split; [ constructor | apply ctx_ok_nil ] ];
  try solve [ split; [ eapply rel_ctx_extend'; eassumption | apply ctx_ok_ass; assumption ] ];
  try solve [ split; [ eapply rel_ctx_extend_def'; eassumption | apply ctx_ok_def; assumption ] ];
  try solve [ split; [ apply rel_ctx_extend_mod'; assumption | apply ctx_ok_mod; assumption ] ];
  (** The context of a judgment about terms, from its premises. *)
  try (split; [ assumption | split; [ assumption |] ]);
  (** Terms, from the case lemmas at one global context. *)
  try solve [ apply valid_exp_typ; assumption
    | apply valid_exp_true; assumption
    | eapply rel_exp_exfalso_cong; eassumption
    | apply rel_exp_true_eta; assumption
    | eapply rel_exp_fn_cong; eassumption
    | eapply rel_exp_app_cong; eassumption
    | eapply valid_exp_let; eassumption
    | eapply rel_exp_let_cong; eassumption
    | eapply rel_exp_let_zeta; eassumption
    | eapply rel_exp_pi_beta; eassumption
    | eapply rel_exp_eq_subtyp; eassumption
    | apply rel_exp_under_ctx_sym; assumption
    | eapply rel_exp_under_ctx_trans; eassumption
    | eapply subtyp_refl; eassumption
    | eapply subtyp_trans; eassumption
    | eapply subtyp_pi; eassumption
    | apply subtyp_univ; [assumption | lia]
    | apply valid_exp_univ; assumption
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
    | apply subtyp_suniv; [assumption | lia]
    | apply subtyp_small_large; assumption ];
  try solve [ eapply valid_exp_var; eassumption | eapply rel_exp_var_delta; eassumption ];
  try solve [ eapply rel_exp_fn_eta; eassumption ];
  try solve [ apply valid_exp_True; assumption | apply valid_exp_False; assumption
            | apply valid_exp_True_small; assumption | apply valid_exp_False_small; assumption
            | eapply rel_exp_univ_cong_tm; eassumption | eapply valid_exp_univ_tm; eassumption
            | eapply valid_exp_maxl_absorb; eassumption | eapply rel_exp_maxl_absorb; eassumption
            | eapply subtyp_suniv_tm; eassumption | eapply subtyp_small_large_tm; eassumption
            | apply subtyp_level; assumption ];
  (** The universes. *)
  try solve [ left; eexists; reflexivity | right; do 2 eexists; split; [ reflexivity | eassumption ] ];
  (** [Π] at a universe. *)
  try solve [
    match goal with HU : (exists i : nat, ?U = Typeω@i) \/ _ |- _ =>
      destruct HU as [[? ->] | (? & ? & -> & ?)]; cbn [exp_wk] in *;
      [ eapply rel_exp_pi_cong; eassumption | eapply rel_exp_pi_cong_small_tm; eassumption ] end ];
  (** The inductive types. *)
  try solve [ eapply k_ind; eassumption | eapply k_con; eassumption
            | eapply k_elim; eassumption | eapply k_elim_cong; eassumption | eapply k_iota; eassumption ];
  (** Local modules. *)
  try solve [ eapply valid_exp_let_mod; eassumption | eapply rel_exp_let_mod_cong; eassumption
            | eapply rel_exp_let_mod_zeta; eassumption ];
  (** Members. *)
  try solve [
    match goal with Hs : smt _ _ _ ?H, Hm : mdenote _ _ _ (me_mem ?H ?x) ?R, Ht : ds_ty _ _ ?R = Some _,
                    HH : _ ⊨ᵐ ?H ≈ ?H' |- _ ⊨ a_mem ?H ?x ≈ a_mem ?H' ?x : _ =>
      pose proof (proj2 (semK_mem_all _ _ Hgm Hgf) _ _ Hs _ _ _ Hm Ht) as Hsm;
      apply rel_exp_under_ctx_sym;
      exact (rel_mem_of_smem _ _ _ _ _ _ (rel_modexp_sym HH) Hsm) end ];
  try solve [
    match goal with Hs : smt _ _ _ ?H, Hm : mdenote _ _ _ (me_mem ?H ?x) ?R, Ht : ds_ty _ _ ?R = Some _,
                    HH : _ ⊨ᵐ ?H ≈ ?H |- _ ⊨ a_mem ?H ?x ≈ a_mem ?H ?x : _ =>
      pose proof (proj2 (semK_mem_all _ _ Hgm Hgf) _ _ Hs _ _ _ Hm Ht) as Hsm;
      exact (rel_mem_of_smem _ _ _ _ _ _ HH Hsm) end ];
  try solve [
    match goal with Hs : smt _ _ _ ?H, Hm : mdenote _ _ _ (me_mem ?H ?x) ?R, Ht : ds_ty _ _ ?R = Some _,
                    Hr : ds_red ?R = Some ?M, HH : _ ⊨ᵐ ?H ≈ ?H |- _ ⊨ a_mem ?H ?x ≈ ?M : _ =>
      pose proof (proj2 (semK_mem_all _ _ Hgm Hgf) _ _ Hs _ _ _ Hm Ht) as Hsm; rewrite Hr in Hsm;
      exact (rel_mem_red_of_smem _ _ _ _ _ _ HH Hsm) end ];
  (** Extensions. *)
  try solve [ split; [ apply rel_ext_nil; assumption | cbn [app]; repeat (split; [ assumption |]); assumption ] ];
  try solve [ split; [ first [ eapply rel_ext_ass; eassumption | eapply rel_ext_def; eassumption | eapply rel_ext_mod; eassumption ] |];
              cbn [app]; repeat split;
              first [ assumption | apply ctx_ok_ass; assumption | apply ctx_ok_def; assumption | apply ctx_ok_mod; assumption ] ];
  (** Units. *)
  try solve [
    match goal with |- ?A /\ ?B /\ ?C /\ _ =>
      cut (A /\ B /\ C); [ intros (? & ? & ?); repeat (split; [ assumption |]); assumption |];
      first [ eapply k_unit_alias; eassumption
            | eapply (k_unit_flatten Hgw _ _ Hgm Hsub Hgf); eassumption ] end ];
  try solve [ split; [ match goal with HU : _ ⊨ᵘ _ ≈ _ |- _ =>
                         destruct HU as [? ? ?]; constructor; [ apply rel_modexp_sym; assumption | assumption .. ] end
                     | repeat (split; [ assumption |]); assumption ] ];
  try solve [ split; [ match goal with HU1 : _ ⊨ᵘ ?U1 ≈ ?U2, HU2 : _ ⊨ᵘ ?U2 ≈ ?U3 |- _ ⊨ᵘ ?U1 ≈ ?U3 =>
                         destruct HU1 as [? ? ?]; destruct HU2 as [? ? ?];
                         constructor; [ eapply rel_modexp_trans; eassumption | assumption .. ] end
                     | repeat (split; [ assumption |]); assumption ] ];
  (** Module expressions. *)
  try solve [
    match goal with |- ?A /\ ?B /\ ?B /\ _ =>
      cut (A /\ B); [ intros (? & ?); repeat (split; [ assumption |]); assumption
                    | eapply (k_unit_path _ _ Hgm Hgf); eassumption ] end ];
  try solve [
    match goal with Hl : _ ∋ # ?x ≔ₘ ?U, Hg : @gfiled_ok ?G ?T1 ?X1 |- ?Γ0 ⊨ᵐ me_var ?x ≈ ?H' /\ ?S /\ _ =>
      cut (S /\ @SemK.semK G T1 X1 Γ0 (me_lit U));
      [ intros (? & ?);
        split; [ first [ eapply rel_me_var; eassumption | eapply rel_me_delta_slot; eassumption ] |];
        split; [ assumption |]; split; [ first [ assumption | apply (smt_of_semK _ _ Hgf); assumption ] | split; assumption ]
      | eapply (k_var Hgw _ _ Hgm Hsub); [ eapply wf_me_var; eassumption | eassumption .. ] ] end ];
  try solve [ split; [ match goal with HU : _ ⊨ᵘ _ ≈ _ |- _ => exact (ruu_lit _ _ _ HU) end |];
              split; [ apply (smt_of_semK _ _ Hgf); assumption |]; split; [ apply (smt_of_semK _ _ Hgf); assumption |];
              split; assumption ];
  try solve [
    match goal with |- ?A /\ ?B /\ ?C /\ _ =>
      cut (A /\ B /\ C); [ intros (? & ? & ?); repeat (split; [ assumption |]); assumption |];
      first [ eapply (k_mem Hgw _ _ Hgm Hsub Hgf); eassumption | eapply (k_app Hgw _ _ Hgm Hsub Hgf); eassumption ] end ];
  try solve [
    match goal with Hs : smt _ _ _ (me_mem ?H ?y), Hm : mdenote _ _ _ (me_mem ?H ?y) ?R, Hmd : ds_mod _ _ ?R = Some ?Rm
                    |- _ ⊨ᵐ me_mem ?H ?y ≈ ds_unit ?Rm /\ _ =>
      let Hc := fresh "Hc" in let HK := fresh "HK" in
      destruct (smt_canon _ _ Hgm Hgf _ _ _ _ Hs Hm Hmd) as [Hc HK];
      split; [ exact Hc |]; split; [ exact Hs |]; split; [ exact (smt_of_semK _ _ Hgf _ _ HK) | split; assumption ] end ];
  try solve [ split; [ apply rel_modexp_sym; assumption | repeat (split; [ assumption |]); assumption ] ];
  try solve [ split; [ eapply rel_modexp_trans; eassumption | repeat (split; [ assumption |]); assumption ] ];
  (** [β]. *)
  try solve [
    match goal with |- ?A /\ ?B /\ _ =>
      cut (A /\ B); [ intros (? & ?); repeat (split; [ assumption |]); assumption |];
      eapply k_alias0; eassumption end ];
  try solve [
    match goal with |- ?A /\ ?B /\ ?C /\ _ =>
      cut (A /\ B /\ C); [ intros (? & ? & ?); repeat (split; [ assumption |]); assumption |];
      first [ eapply (k_beta_body Hgw _ _ Hgm Hsub Hgf); eassumption
            | eapply (k_beta_alias Hgw _ _ Hgm Hsub Hgf); eassumption ] end ];
  (** A body unit. *)
  try solve [
    match goal with |- ?A /\ ?B /\ ?C /\ _ =>
      cut (A /\ B /\ C); [ intros (? & ? & ?); repeat (split; [ assumption |]); assumption |];
      eapply k_unit_body_k; eassumption end ].

Ltac kcase :=
  kintro;
  match goal with
  | Hgw : ⊢ᵍ @gc_deps (gc_mk _ _) ⍮ _, Hsub : gc_sub ?T1 ?X1 _ _, Hgm : ⊢ᵍ ?T1 ⍮ ?X1,
    Hgf : @gfiled_ok _ ?T1 ?X1 |- _ => kclose Hgw Hgm Hsub Hgf
  end.

(** ** The cases *)

(** *** Contexts *)

Lemma sem_ctx_empty :
  `( ⊢ᵍ Θ ⍮ Ξ ->
     ⊨ Θ ⍮ Ξ ⍮ ⋅ ).
Proof. kcase. Qed.

Lemma sem_ctx_extend :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ▹ A ).
Proof. kcase. Qed.

Lemma sem_ctx_extend_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ).
Proof. kcase. Qed.

Lemma sem_ctx_extend_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ▹ₘ U ).
Proof. kcase. Qed.

(** *** Terms *)

Lemma sem_typ :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Typeω@i : Typeω@(S i) ).
Proof. kcase. Qed.

Lemma sem_univ :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Type⟨M⟩ : Type⟨succl M⟩ ).
Proof. kcase. Qed.

Lemma sem_level :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Level@n : Type@0 ).
Proof. kcase. Qed.

Lemma sem_llit :
  `( fst o <= n ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ 𝕃ᵒ o : Level@n ).
Proof. kcase. Qed.

Lemma sem_succl :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ succl M : Level@n ).
Proof. kcase. Qed.

Lemma sem_maxl :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl M N : Level@n ).
Proof. kcase. Qed.

Lemma sem_True :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ⊤ : Type@0 ).
Proof. kcase. Qed.

Lemma sem_true :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ⋆ : ⊤ ).
Proof. kcase. Qed.

Lemma sem_False :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ⊥ : Type@0 ).
Proof. kcase. Qed.

Lemma sem_exfalso :
  `( Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : ⊥ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ efq M return A : A[Id,,M] ).
Proof. kcase. Qed.

Lemma sem_ind :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_ind p : ind_ty D ).
Proof. kcase. Qed.

Lemma sem_con :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     ⊨ Θ ⍮ Ξ ⍮ cargs_ctx p D gs ++ ind_params D ->
     (forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
        ⊨ Θ ⍮ Ξ ⍮ (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D)
                  ▹ ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t)) ->
     Θ ⍮ Ξ ⍮ ⋅ ⊨ con_ty p D gs : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_con p c : con_ty p D gs ).
Proof. kcase. Qed.

Lemma sem_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     List.length Ps = ind_np D ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊨ P : T) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : apps (a_ind p) Ps ->
     nm = S (ind_nn D) ->
     Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_mctx p D (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D (List.firstn (ind_nu D) Ps) ->
     brs_names (ind_cons D) Bs ->
     (forall c gs, ind_con D c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
     (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
        n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
     (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
        Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B
          : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_elim nm A Bs M : A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] ).
Proof. kcase. Qed.

Lemma sem_pi :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵤ U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A : U ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B : U[↑]ʷ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Π A B : U ).
Proof. kcase. Qed.

Lemma sem_fn :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ M : B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ λ A M : Π A B ).
Proof. kcase. Qed.

Lemma sem_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : Π A B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M $ N : B[Id,,N] ).
Proof. kcase. Qed.

Lemma sem_let :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊨ B : C ->
     let_ann oA A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_let (b_def oA M) B : C[Id,,M] ).
Proof. kcase. Qed.

Lemma sem_let_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ C : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓₘ U in B : C[Id ,,ₘ me_lit U] ).
Proof. kcase. Qed.

Lemma sem_mem :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     ds_ty Θ Ξ R = Some A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     (forall M, ds_red R = Some M -> Θ ⍮ Ξ ⍮ Γ ⊨ M : A) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_mem H x : A ).
Proof. kcase. Qed.

Lemma sem_vlookup :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ #x : A ).
Proof. kcase. Qed.

Lemma sem_exp_subtyp :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A ⊆ A' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A' ).
Proof. kcase. Qed.

(** *** Term equality: congruence *)

Lemma sem_exp_eq_typ_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Typeω@i ≈ Typeω@i : Typeω@(S i) ).
Proof. kcase. Qed.

Lemma sem_exp_eq_univ_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Type⟨M⟩ ≈ Type⟨M'⟩ : Type⟨succl M⟩ ).
Proof. kcase. Qed.

Lemma sem_exp_eq_level_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Level@n ≈ Level@n : Type@0 ).
Proof. kcase. Qed.

Lemma sem_exp_eq_llit_cong :
  `( fst o <= n ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ 𝕃ᵒ o ≈ 𝕃ᵒ o : Level@n ).
Proof. kcase. Qed.

Lemma sem_exp_eq_succl_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ succl M ≈ succl M' : Level@n ).
Proof. kcase. Qed.

Lemma sem_exp_eq_maxl_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N ≈ N' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl M N ≈ maxl M' N' : Level@n ).
Proof. kcase. Qed.

(** *** Term equality: the level equations *)

Lemma sem_exp_eq_llit_succl :
  `( a <= n ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ 𝕃ᵒ(a, S b) ≈ succl (𝕃ᵒ(a, b)) : Level@n ).
Proof. kcase. Qed.

Lemma sem_exp_eq_maxl_absorb :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl M (𝕃ᵒ(S n, 0)) ≈ 𝕃ᵒ(S n, 0) : Level@(S n) ).
Proof. kcase. Qed.

Lemma sem_exp_eq_maxl_zero :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl (𝕃@0) M ≈ M : Level@n ).
Proof. kcase. Qed.

Lemma sem_exp_eq_maxl_assoc :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ P : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl (maxl M N) P ≈ maxl M (maxl N P) : Level@n ).
Proof. kcase. Qed.

Lemma sem_exp_eq_maxl_comm :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl M N ≈ maxl N M : Level@n ).
Proof. kcase. Qed.

Lemma sem_exp_eq_maxl_idem :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl M M ≈ M : Level@n ).
Proof. kcase. Qed.

Lemma sem_exp_eq_succl_maxl :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ succl (maxl M N) ≈ maxl (succl M) (succl N) : Level@n ).
Proof. kcase. Qed.

Lemma sem_exp_eq_maxl_succl :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl M (succl M) ≈ succl M : Level@n ).
Proof. kcase. Qed.

(** *** Term equality: congruence, continued *)

Lemma sem_exp_eq_True_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ⊤ ≈ ⊤ : Type@0 ).
Proof. kcase. Qed.

Lemma sem_exp_eq_true_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ⋆ ≈ ⋆ : ⊤ ).
Proof. kcase. Qed.

Lemma sem_exp_eq_False_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ⊥ ≈ ⊥ : Type@0 ).
Proof. kcase. Qed.

Lemma sem_exp_eq_exfalso_cong :
  `( Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊨ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : ⊥ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ efq M return A ≈ efq M' return A' : A[Id,,M] ).
Proof. kcase. Qed.

Lemma sem_exp_eq_ind_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_ind p ≈ a_ind p : ind_ty D ).
Proof. kcase. Qed.

Lemma sem_exp_eq_con_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     ⊨ Θ ⍮ Ξ ⍮ cargs_ctx p D gs ++ ind_params D ->
     Θ ⍮ Ξ ⍮ ⋅ ⊨ con_ty p D gs : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_con p c ≈ a_con p c : con_ty p D gs ).
Proof. kcase. Qed.

Lemma sem_exp_eq_elim_cong :
  `( ind_lookup Θ Ξ p = Some D ->
     List.length Ps = ind_np D ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊨ P : T) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : apps (a_ind p) Ps ->
     nm = S (ind_nn D) ->
     Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_mctx p D (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D (List.firstn (ind_nu D) Ps) ->
     Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊨ A ≈ A' : Typeω@i ->
     brs_names (ind_cons D) Bs ->
     (forall c gs, ind_con D c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
     List.map fst Bs = List.map fst Bs' ->
     (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
        n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
     (forall k c gs n B B', nth_error Bs k = Some (c, n, B) -> nth_error Bs' k = Some (c, n, B') ->
        ind_con D c = Some gs ->
        Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B ≈ B'
          : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_elim nm A Bs M ≈ a_elim nm A' Bs' M' : A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] ).
Proof. kcase. Qed.

Lemma sem_exp_eq_pi_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵤ U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A : U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A ≈ A' : U ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B ≈ B' : U[↑]ʷ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Π A B ≈ Π A' B' : U ).
Proof. kcase. Qed.

Lemma sem_exp_eq_fn_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ M ≈ M' : B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ λ A M ≈ λ A' M' : Π A B ).
Proof. kcase. Qed.

Lemma sem_exp_eq_app_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : Π A B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N ≈ N' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M $ N ≈ M' $ N' : B[Id,,N] ).
Proof. kcase. Qed.

Lemma sem_exp_eq_let_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊨ B ≈ B' : C ->
     let_ann oA A ->
     let_ann oA' A' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_let (b_def oA M) B ≈ a_let (b_def oA' M') B' : C[Id,,M] ).
Proof. kcase. Qed.

Lemma sem_exp_eq_let_mod_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ B ≈ B' : C ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓₘ U' in B' : C[Id ,,ₘ me_lit U] ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓₘ U in B ≈ ℓₘ U' in B' : C[Id ,,ₘ me_lit U] ).
Proof. kcase. Qed.

Lemma sem_exp_eq_mem_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H' ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     ds_ty Θ Ξ R = Some A ->
     mdenote Θ Ξ Γ (me_mem H' x) R' ->
     ds_ty Θ Ξ R' = Some A' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_mem H' x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_mem H x ≈ a_mem H' x : A ).
Proof. kcase. Qed.

Lemma sem_exp_eq_var :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ #x ≈ #x : A ).
Proof. kcase. Qed.

(** *** Term equality: computation *)

Lemma sem_exp_eq_pi_beta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ M : B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ (λ A M) $ N ≈ M[Id,,N] : B[Id,,N] ).
Proof. kcase. Qed.

Lemma sem_exp_eq_elim_iota :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     List.length Ps = ind_np D ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊨ P : T) ->
     List.length As = List.length gs ->
     (forall k N T, nth_error As k = Some N -> nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊨ N : T) ->
     nm = S (ind_nn D) ->
     Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_mctx p D (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D (List.firstn (ind_nu D) Ps) ->
     brs_names (ind_cons D) Bs ->
     (forall c gs, ind_con D c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
     (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
        n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
     (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
        Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B
          : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
     brs_lookup Bs c = Some (n, B) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_elim nm A Bs (apps (a_con p c) (Ps ++ As))
       ≈ B[sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ elim_ihs nm A Bs (sb_of_list Id Ps) gs As)]
       : A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ apps (a_con p c) (Ps ++ As) :: nil)] ).
Proof. kcase. Qed.

Lemma sem_exp_eq_let_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊨ B : C ->
     let_ann oA A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_let (b_def oA M) B ≈ B[Id,,M] : C[Id,,M] ).
Proof. kcase. Qed.

Lemma sem_exp_eq_let_mod_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ C : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : C[Id ,,ₘ me_lit U] ).
Proof. kcase. Qed.

Lemma sem_exp_eq_mem_delta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     ds_ty Θ Ξ R = Some A ->
     ds_red R = Some M ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_mem H x ≈ M : A ).
Proof. kcase. Qed.

Lemma sem_exp_eq_var_delta :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ #x ≈ M : A ).
Proof. kcase. Qed.

(** *** Term equality: uniqueness, subsumption, and the PER rules *)

Lemma sem_exp_eq_fn_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : Π A B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ λ A M[↑]ʷ $ #0 : Π A B ).
Proof. kcase. Qed.

Lemma sem_exp_eq_true_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : ⊤ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ ⋆ : ⊤ ).
Proof. kcase. Qed.

Lemma sem_exp_eq_subtyp :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A ⊆ A' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : A' ).
Proof. kcase. Qed.

Lemma sem_exp_eq_sym :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M' ≈ M : A ).
Proof. kcase. Qed.

Lemma sem_exp_eq_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M' ≈ M'' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M'' : A ).
Proof. kcase. Qed.

(** *** Subtyping *)

Lemma sem_subtyp_refl :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ⊆ M' ).
Proof. kcase. Qed.

Lemma sem_subtyp_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M ⊆ M' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M' ⊆ M'' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ⊆ M'' ).
Proof. kcase. Qed.

Lemma sem_subtyp_univ :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     i < j ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Typeω@i ⊆ Typeω@j ).
Proof. kcase. Qed.

Lemma sem_subtyp_suniv :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl M M' ≈ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Type⟨M⟩ ⊆ Type⟨M'⟩ ).
Proof. kcase. Qed.

Lemma sem_subtyp_level :
  `( m <= n ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Level@m ⊆ Level@n ).
Proof. kcase. Qed.

Lemma sem_subtyp_small_large :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Type⟨M⟩ ⊆ Typeω@i ).
Proof. kcase. Qed.

Lemma sem_subtyp_pi :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊨ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A' ⊨ B' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A' ⊨ B ⊆ B' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Π A B ⊆ Π A' B' ).
Proof. kcase. Qed.

(** *** Universes *)

Lemma sem_is_univ_large :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵤ Typeω@i ).
Proof. kcase. Qed.

Lemma sem_is_univ_small :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ L : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵤ Type⟨L⟩ ).
Proof. kcase. Qed.

(** *** Extensions *)

Lemma sem_ext_eq_nil :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ ⋅ ≈ ⋅ ).
Proof. kcase. Qed.

Lemma sem_ext_eq_ass :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ▹ A ≈ Ψ' ▹ A' ).
Proof. kcase. Qed.

Lemma sem_ext_eq_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ M' : A' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ▸ A ≔ M ≈ Ψ' ▸ A' ≔ M' ).
Proof. kcase. Qed.

Lemma sem_ext_eq_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊨ᵘ U' ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ▹ₘ U ≈ Ψ' ▹ₘ U' ).
Proof. kcase. Qed.

(** *** Units

    A body unit is valid in its parts as the rule checks them; the case
    reads the module the literal denotes off the derivation of the rule,
    as an alias's does. *)

Lemma sem_unit_eq_body :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' ->
     body_xp Θ Ξ (Δ ++ Γ) Φ Φx ->
     body_xp Θ Ξ (Δ' ++ Γ) Φ' Φx' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Δ ≈ Δ' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ body_ctx Φx ++ Δ ≈ body_ctx Φx ++ Δ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ body_ctx Φx' ++ Δ' ≈ body_ctx Φx' ++ Δ' ->
     (forall y Φ0 b pv A M Φ0' b' pv' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ A[σ] ≈ A'[σ'] : Typeω@(lv y)) ->
     (forall y Φ0 b pv A M Φ0' b' pv' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ M[σ] ≈ M'[σ'] : A[σ]) ->
     (forall y Φ0 pv U Φ0' pv' U' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_mod pv' U')) ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ᵘ U[σ]ᵘ ≈ U'[σ']ᵘ) ->
     (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δ ++ Γ ⊨ᵐ H ≈ H) ->
     (forall k Ψ' H', nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> Θ ⍮ Ξ ⍮ Ψ' ++ Δ' ++ Γ ⊨ᵐ H' ≈ H') ->
     (forall k Φ0 H Φ0' H' σ σ',
        nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) ->
        nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ᵐ H[σ]ᵐ ≈ H'[σ']ᵐ) ->
     tele_ass Δ ->
     tele_ass Δ' ->
     List.length Δ = List.length Δ' ->
     body_shape Φ Φ' ->
     body_shape Φx Φx' ->
     List.NoDup (gm_names Φ) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' ).
Proof. kcase. Qed.

Lemma sem_unit_eq_alias :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E') ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Δ ≈ Δ' ->
     tele_ass Δ ->
     tele_ass Δ' ->
     Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ᵐ E ≈ E' ->
     Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊨ᵐ E' ≈ E' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E') ).
Proof. kcase. Qed.

Lemma sem_unit_eq_flatten :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ≈ gu_mk (Δ' ++ Δ) D ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Δ ≈ Δ ->
     tele_ass Δ ->
     Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ᵘ gu_mk Δ' D ≈ gu_mk Δ' D ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ≈ gu_mk (Δ' ++ Δ) D ).
Proof. kcase. Qed.

Lemma sem_unit_eq_sym :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U' ≈ U ).
Proof. kcase. Qed.

Lemma sem_unit_eq_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U' ≈ U'' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U'' ).
Proof. kcase. Qed.

(** *** Module expressions

    A unit path, a slot and an application read what they denote off the
    syntactic premises of their rules. *)

Lemma sem_me_unit :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ->
     gc_unit Θ Ξ (me_unit fp) = Some TΦ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_unit fp ≈ me_unit fp ).
Proof. kcase. Qed.

Lemma sem_me_var :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ₘ U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_var x ≈ me_var x ).
Proof. kcase. Qed.

Lemma sem_me_lit :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_lit U ≈ me_lit U' ).
Proof. kcase. Qed.

Lemma sem_me_mem :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H' ->
     mdenote Θ Ξ Γ (me_mem H y) R ->
     ds_mtele Θ Ξ R = Some T ->
     mdenote Θ Ξ Γ (me_mem H' y) R' ->
     ds_mtele Θ Ξ R' = Some T' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_mem H y ≈ me_mem H' y ).
Proof. kcase. Qed.

Lemma sem_me_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H' ->
     mdenote Θ Ξ Γ H R ->
     ds_mtele Θ Ξ R = Some T ->
     tele_view T = Some (B, T1) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N ≈ N' : B ->
     mdenote Θ Ξ Γ H' R' ->
     ds_mtele Θ Ξ R' = Some T' ->
     tele_view T' = Some (B', T1') ->
     Θ ⍮ Ξ ⍮ Γ ⊢ B' : Typeω@j ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N' : B' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N' : B' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_app H N ≈ me_app H' N' ).
Proof. kcase. Qed.

Lemma sem_me_delta_slot :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ₘ U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_var x ≈ me_lit U ).
Proof. kcase. Qed.

Lemma sem_me_delta_sel :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_mem H y ≈ me_mem H y ->
     mdenote Θ Ξ Γ (me_mem H y) R ->
     ds_mod Θ Ξ R = Some Rm ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_mem H y ≈ ds_unit Rm ).
Proof. kcase. Qed.

Lemma sem_me_beta_body :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass X :: nil) (md_body sm_open Φ) ≈ gu_mk (Δ ++ ce_ass X :: nil) (md_body sm_open Φ) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_mk (Δ ++ ce_ass X :: nil) (md_body sm_open Φ) ≈ gu_mk (Δ ++ ce_ass X :: nil) (md_body sm_open Φ) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : X ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) (md_body sm_open Φ))) N
       ≈ me_lit (gu_mk (tele_sub Δ (Id,,N)) (md_body sm_open (gmod_sub Φ (sb_qn (length Δ) (Id,,N))))) ).
Proof. kcase. Qed.

Lemma sem_me_beta_alias :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass X :: nil) (md_alias E) ≈ gu_mk (Δ ++ ce_ass X :: nil) (md_alias E) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_mk (Δ ++ ce_ass X :: nil) (md_alias E) ≈ gu_mk (Δ ++ ce_ass X :: nil) (md_alias E) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : X ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) (md_alias E))) N
       ≈ me_lit (gu_mk (tele_sub Δ (Id,,N)) (md_alias E[sb_qn (length Δ) (Id,,N)]ᵐ)) ).
Proof. kcase. Qed.

Lemma sem_me_beta_alias0 :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ E ≈ E ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_lit (gu_mk nil (md_alias E)) ≈ E ).
Proof. kcase. Qed.

Lemma sem_me_sym :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H' ≈ H ).
Proof. kcase. Qed.

Lemma sem_me_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H' ≈ H'' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H'' ).
Proof. kcase. Qed.

(** ** The fundamental theorem

    Every syntactic judgment holds semantically, by its case lemma, one per
    rule in the order of the rules. *)
Theorem completeness_fundamental :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊨ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ ⍮ Ξ ⍮ Γ ⊨ M : A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : A) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ ⍮ Ξ ⍮ Γ ⊨ A ⊆ A') /\
  (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> Θ ⍮ Ξ ⍮ Γ ⊨ᵤ U) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ≈ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U') /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H').
Proof.
  apply syntactic_wf_mut_ind; intros;
    [ (** contexts *)
      eapply sem_ctx_empty | eapply sem_ctx_extend | eapply sem_ctx_extend_def | eapply sem_ctx_extend_mod
    | (** terms *)
      eapply sem_typ | eapply sem_univ | eapply sem_level | eapply sem_llit | eapply sem_succl | eapply sem_maxl
    | eapply sem_True | eapply sem_true | eapply sem_False | eapply sem_exfalso | eapply sem_ind | eapply sem_con
    | eapply sem_elim | eapply sem_pi | eapply sem_fn | eapply sem_app | eapply sem_let | eapply sem_let_mod
    | eapply sem_mem | eapply sem_vlookup | eapply sem_exp_subtyp
    | (** term equality *)
      eapply sem_exp_eq_typ_cong | eapply sem_exp_eq_univ_cong | eapply sem_exp_eq_level_cong
    | eapply sem_exp_eq_llit_cong | eapply sem_exp_eq_succl_cong | eapply sem_exp_eq_maxl_cong
    | eapply sem_exp_eq_llit_succl | eapply sem_exp_eq_maxl_absorb | eapply sem_exp_eq_maxl_zero
    | eapply sem_exp_eq_maxl_assoc | eapply sem_exp_eq_maxl_comm | eapply sem_exp_eq_maxl_idem
    | eapply sem_exp_eq_succl_maxl | eapply sem_exp_eq_maxl_succl
    | eapply sem_exp_eq_True_cong | eapply sem_exp_eq_true_cong | eapply sem_exp_eq_False_cong
    | eapply sem_exp_eq_exfalso_cong | eapply sem_exp_eq_ind_cong | eapply sem_exp_eq_con_cong
    | eapply sem_exp_eq_elim_cong | eapply sem_exp_eq_pi_cong | eapply sem_exp_eq_fn_cong
    | eapply sem_exp_eq_app_cong | eapply sem_exp_eq_let_cong | eapply sem_exp_eq_let_mod_cong
    | eapply sem_exp_eq_mem_cong | eapply sem_exp_eq_var | eapply sem_exp_eq_pi_beta
    | eapply sem_exp_eq_elim_iota | eapply sem_exp_eq_let_zeta | eapply sem_exp_eq_let_mod_zeta
    | eapply sem_exp_eq_mem_delta | eapply sem_exp_eq_var_delta | eapply sem_exp_eq_fn_eta
    | eapply sem_exp_eq_true_eta | eapply sem_exp_eq_subtyp | eapply sem_exp_eq_sym | eapply sem_exp_eq_trans
    | (** subtyping *)
      eapply sem_subtyp_refl | eapply sem_subtyp_trans | eapply sem_subtyp_univ | eapply sem_subtyp_suniv
    | eapply sem_subtyp_level | eapply sem_subtyp_small_large | eapply sem_subtyp_pi
    | (** universes *)
      eapply sem_is_univ_large | eapply sem_is_univ_small
    | (** extensions *)
      eapply sem_ext_eq_nil | eapply sem_ext_eq_ass | eapply sem_ext_eq_def | eapply sem_ext_eq_mod
    | (** units: the first premise is the conclusion of the rule *)
      eapply sem_unit_eq_body; [ eapply wf_unit_eq_body; eassumption | .. ]
    | eapply sem_unit_eq_alias; [ eapply wf_unit_eq_alias; eassumption | .. ]
    | eapply sem_unit_eq_flatten; [ eapply wf_unit_eq_flatten; eassumption | .. ]
    | eapply sem_unit_eq_sym | eapply sem_unit_eq_trans
    | (** module expressions *)
      eapply sem_me_unit | eapply sem_me_var | eapply sem_me_lit | eapply sem_me_mem | eapply sem_me_app
    | eapply sem_me_delta_slot | eapply sem_me_delta_sel | eapply sem_me_beta_body | eapply sem_me_beta_alias
    | eapply sem_me_beta_alias0 | eapply sem_me_sym | eapply sem_me_trans ];
    eassumption.
Qed.
