(** * The Module Rules at One Global Context

    The cases of the rules about units and module expressions, at a global
    context [GC] that a global context [Θm ⍮ Ξm] embeds into: the units and
    module expressions are moreover valid in what they denote, read at
    [Θm ⍮ Ξm] ([semK], [smt]), and the slots of a valid context hold valid
    units ([ctx_ok]).  [KripkeCases.v] states them as the cases of the
    semantic judgments. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import MemberLemmas GlobalModules GlobalPaths DescTyping LookupSound.
From Mctt.Core.Completeness Require Import
  ContextCases FunctionCases LetCases LevelCases SubstitutionCases SubtypingCases
  TrueFalseCases UniverseCases VariableCases LogicalRelation UnitCases InstanceCases
  MemberReps IndCases TeleSem ElimCases ElimIota
  ModuleVal ModuleSem UnitSub ModexpRules GlobalArgs IndSem SemK UnitBody FiledSem UnitSem MemSem CanonSem AppSem SelSem.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** 1. Valid contexts' slots *)

Section Slots.
  Context {GC : GCtx}.
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  Variables (Θm : gdeps) (Ξm : gstack).
  Hypothesis Hgm : ⊢ᵍ Θm ⍮ Ξm.
  Hypothesis Hsub : gc_sub Θm Ξm gc_deps gc_stack.

  #[local] Abbreviation semK := (semK Θm Ξm).
  #[local] Abbreviation ctx_ok := (SemK.ctx_ok Θm Ξm).

Lemma ctx_ok_nil : ctx_ok nil.
Proof. unfold SemK.ctx_ok; intros Γ1 U Γ0 H; destruct Γ1; discriminate. Qed.

Lemma ctx_ok_tail : forall e Γ, ctx_ok (e :: Γ) -> ctx_ok Γ.
Proof. unfold SemK.ctx_ok; intros * H Γ1 U Γ0 ->; exact (H (e :: Γ1) U Γ0 eq_refl). Qed.

Lemma ctx_ok_app_r : forall Ψ Γ, ctx_ok (Ψ ++ Γ) -> ctx_ok Γ.
Proof. unfold SemK.ctx_ok; intros * H Γ1 U Γ0 ->; apply (H (Ψ ++ Γ1)); rewrite app_assoc; reflexivity. Qed.

Lemma ctx_ok_cons : forall e Γ, ctx_ok Γ -> (forall U, e = ce_mod U -> semK Γ (me_lit U)) -> ctx_ok (e :: Γ).
Proof.
  unfold SemK.ctx_ok; intros * H He [| e1 Γ1] U Γ0 Heq; cbn in Heq; injection Heq as -> Heq; [ subst; exact (He _ eq_refl) |].
  exact (H _ _ _ Heq).
Qed.

Lemma ctx_ok_ass : forall Γ A, ctx_ok Γ -> ctx_ok (Γ ▹ A).
Proof. intros * H; apply ctx_ok_cons; [ exact H | discriminate ]. Qed.

Lemma ctx_ok_def : forall Γ A M, ctx_ok Γ -> ctx_ok (Γ ▸ A ≔ M).
Proof. intros * H; apply ctx_ok_cons; [ exact H | discriminate ]. Qed.

Lemma ctx_ok_mod : forall Γ U, ctx_ok Γ -> semK Γ (me_lit U) -> ctx_ok (Γ ▹ₘ U).
Proof. intros * H HU; apply ctx_ok_cons; [ exact H | intros U0 [= <-]; exact HU ]. Qed.

(** A valid unit stays valid one entry further in. *)
Lemma semK_shift : forall e Γ K, semK Γ K -> ⊨ e :: Γ -> wf_ctx Θm Ξm (e :: Γ) -> semK (e :: Γ) K[sb_of_wk ↑]ᵐ.
Proof.
  intros * HK HC Hw.
  eapply (semK_gsub Hgw _ _ Hgm Hsub); [ exact HK | exact (gsub_wk _ _ _ (rel_wk_under_ctx_shift HC) HC (sem_ctx_tail HC)) |].
  apply wf_sub_of_wk, wf_wk_shift; exact Hw.
Qed.

(** The unit of a slot of a valid context is valid there. *)
Lemma slot_semK : forall Γ x U, Γ ∋ #x ≔ₘ U -> ⊨ Γ -> wf_ctx Θm Ξm Γ -> ctx_ok Γ -> semK Γ (me_lit U).
Proof.
  induction 1 as [U0 Γ0 | n U1 Γ0 e Hl IH]; intros HC Hw Hok.
  - pose proof (semK_shift _ _ _ (Hok nil U0 Γ0 eq_refl : semK Γ0 (me_lit U0)) HC Hw) as H.
    cbn [modexp_sub] in H; rewrite gunit_sub_of_wk in H; exact H.
  - pose proof (semK_shift _ _ _ (IH (sem_ctx_tail HC) (ctx_decomp_tail Hw) (ctx_ok_tail _ _ Hok)) HC Hw) as H.
    cbn [modexp_sub] in H; rewrite gunit_sub_of_wk in H; exact H.
Qed.

End Slots.

(** ** 2. The cases of the module rules *)

Section Cases.
  Context {GC : GCtx}.
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  Variables (Θm : gdeps) (Ξm : gstack).
  Hypothesis Hgm : ⊢ᵍ Θm ⍮ Ξm.
  Hypothesis Hsub : gc_sub Θm Ξm gc_deps gc_stack.
  Hypothesis Hgf : gfiled_ok Θm Ξm.

  #[local] Abbreviation semK := (semK Θm Ξm).
  #[local] Abbreviation smt := (smt Θm Ξm).
  #[local] Abbreviation ctx_ok := (SemK.ctx_ok Θm Ξm).

(** A slot is valid in what it denotes, as its unit is. *)
Lemma k_var : forall Γ x U, Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_var x ≈ me_var x -> ⊨ Γ -> ctx_ok Γ -> Γ ∋ #x ≔ₘ U ->
    smt Γ (me_var x) /\ semK Γ (me_lit U).
Proof.
  intros * Hw HΓ Hok Hl.
  pose proof (slot_semK Hgw _ _ Hgm Hsub _ _ _ Hl HΓ (presup_modexp_eq_ctx Hw) Hok) as HK.
  split; [| exact HK ].
  destruct (me_denotes _ _ _ _ _ Hw) as (R & Rm & Hm & Hmd).
  inversion Hm as [? ? ? ? ? Hq _ | ? ? ? ? Hl' Hu | | |]; subst; [ cbn in Hq; discriminate |].
  pose proof (ctx_lookup_mod_functional _ _ _ _ Hl Hl') as <-.
  exact (smt_intro _ _ _ _ _ _ _ _ Hw Hm Hmd (rel_me_delta_slot _ _ _ HΓ Hl) HK (dn_lit _ _ _ _ _ Hu) Hmd).
Qed.

(** Submodules of equal module expressions valid in what they denote. *)
Lemma k_mem : forall Γ H H' y R T R' T', Γ ⊨ᵐ H ≈ H' -> smt Γ H -> smt Γ H' ->
    mdenote Θm Ξm Γ (me_mem H y) R -> ds_mtele Θm Ξm R = Some T ->
    mdenote Θm Ξm Γ (me_mem H' y) R' -> ds_mtele Θm Ξm R' = Some T' ->
    Γ ⊨ᵐ me_mem H y ≈ me_mem H' y /\ smt Γ (me_mem H y) /\ smt Γ (me_mem H' y).
Proof.
  intros * HH Hs Hs' Hm Ht Hm' Ht'.
  unfold ds_mtele in Ht, Ht'.
  destruct (ds_mod Θm Ξm R) as [Rm |] eqn:Hmd; [| discriminate ].
  destruct (ds_mod Θm Ξm R') as [Rm' |] eqn:Hmd'; [| discriminate ].
  destruct (smt_sel Hgw _ _ Hgm Hsub Hgf _ _ _ _ _ Hs Hm Hmd) as (Hy & Hsy & HK).
  destruct (smt_sel Hgw _ _ Hgm Hsub Hgf _ _ _ _ _ Hs' Hm' Hmd') as (_ & Hsy' & _).
  destruct (proj2 (semK_sel_all Hgw _ _ Hgm Hsub Hgf) _ _ Hs _ _ _ Hm Hmd) as [HS _].
  pose proof (smod_resp_l _ _ _ _ _ (rel_modexp_sym HH) HS) as HS'.
  pose proof (rel_sel_of_smod _ _ _ _ _ (rel_modexp_refl_right HH) HS' (semK_valid _ _ Hgf _ _ HK)) as Hy'.
  split; [ exact (rel_modexp_trans Hy (rel_modexp_sym Hy')) | split; assumption ].
Qed.

(** Applications of equal module expressions valid in what they denote. *)
Lemma k_app : forall Γ H H' N N' R T B T1 i R' T' B' T1' j,
    Γ ⊨ᵐ H ≈ H' -> smt Γ H -> smt Γ H' ->
    mdenote Θm Ξm Γ H R -> ds_mtele Θm Ξm R = Some T -> tele_view T = Some (B, T1) ->
    Θm ⍮ Ξm ⍮ Γ ⊢ B : Typeω@i -> Θm ⍮ Ξm ⍮ Γ ⊢ N : B -> Γ ⊨ N ≈ N' : B ->
    mdenote Θm Ξm Γ H' R' -> ds_mtele Θm Ξm R' = Some T' -> tele_view T' = Some (B', T1') ->
    Θm ⍮ Ξm ⍮ Γ ⊢ B' : Typeω@j -> Θm ⍮ Ξm ⍮ Γ ⊢ N' : B' -> Γ ⊨ N' : B' ->
    Γ ⊨ᵐ me_app H N ≈ me_app H' N' /\ smt Γ (me_app H N) /\ smt Γ (me_app H' N').
Proof.
  intros * HH Hs Hs' Hm Ht Hv HB HN HNN Hm' Ht' Hv' HB' HN' HNs'.
  destruct (proj2 (semK_app_all Hgw _ _ Hgm Hsub Hgf) _ _ Hs _ _ _ _ _ _ Hm Ht Hv HB HN (rel_exp_under_ctx_refl_left HNN))
    as [Hl HsN].
  destruct (proj2 (semK_app_all Hgw _ _ Hgm Hsub Hgf) _ _ Hs' _ _ _ _ _ _ Hm' Ht' Hv' HB' HN' HNs') as [_ HsN'].
  split; [ exact (rel_me_app _ _ _ _ _ _ HH HNN Hl) | split; assumption ].
Qed.

(** [β] for a literal, valid in what it denotes on both sides. *)
Lemma k_beta : forall Γ Δ X D N,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_lit (gu_mk (Δ ++ ce_ass X :: nil) D) ≈ me_lit (gu_mk (Δ ++ ce_ass X :: nil) D) ->
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) N ≈ me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) N ->
    semK Γ (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) -> Θm ⍮ Ξm ⍮ Γ ⊢ N : X -> Γ ⊨ N : X ->
    Γ ⊨ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) N ≈ me_lit (gu_mk Δ D)[Id,,N]ᵘ /\
    smt Γ (me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) N) /\ smt Γ (me_lit (gu_mk Δ D)[Id,,N]ᵘ).
Proof.
  intros * Hw Hwa HK HNw HN.
  pose proof (presup_exp_ctx HNw) as HwΓ.
  destruct (presup_exp_typ HNw) as [i HXw].
  destruct (me_denotes _ _ _ _ _ Hw) as (R & Rm & Hm & _).
  pose proof (mdenote_lit_inv _ _ _ _ _ Hm) as Hu.
  destruct (semK_lit_app Hgw _ _ Hgm Hsub Hgf _ _ _ _ _ _ _ HK Hu HXw HNw HN) as (_ & R' & Ha & HKN & HK' & Hm' & Hmd').
  split; [ exact HKN |]; split; [| exact (smt_of_semK _ _ Hgf _ _ HK') ].
  exact (smt_intro _ _ _ _ _ _ _ _ Hwa (dn_app _ _ _ _ _ _ _ Hm Ha) Hmd' HKN HK' Hm' Hmd').
Qed.

Lemma k_beta_body : forall Γ Δ X Φ N,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵘ gu_open (Δ ++ ce_ass X :: nil) Φ ≈ gu_open (Δ ++ ce_ass X :: nil) Φ ->
    semK Γ (me_lit (gu_open (Δ ++ ce_ass X :: nil) Φ)) -> Θm ⍮ Ξm ⍮ Γ ⊢ N : X -> Γ ⊨ N : X ->
    Γ ⊨ᵐ me_app (me_lit (gu_open (Δ ++ ce_ass X :: nil) Φ)) N
      ≈ me_lit (gu_open (tele_sub Δ (Id,,N)) (gmod_sub Φ (sb_qn (List.length Δ) (Id,,N)))) /\
    smt Γ (me_app (me_lit (gu_open (Δ ++ ce_ass X :: nil) Φ)) N) /\
    smt Γ (me_lit (gu_open (tele_sub Δ (Id,,N)) (gmod_sub Φ (sb_qn (List.length Δ) (Id,,N))))).
Proof.
  intros * HU HK HNw HN.
  pose proof (wf_me_beta_body _ _ _ _ _ _ _ HU HNw) as Hb.
  destruct (k_beta _ _ _ _ _ (wf_me_lit _ _ _ _ _ HU) (wf_me_trans _ _ _ _ _ _ Hb (wf_me_sym _ _ _ _ _ Hb)) HK HNw HN) as (H1 & H2 & H3).
  rewrite gunit_sub_mk in H1, H3; cbn [moddef_sub] in H1, H3.
  split; [ exact H1 | split; assumption ].
Qed.

Lemma k_beta_alias : forall Γ Δ X E N,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass X :: nil) (md_alias E) ≈ gu_mk (Δ ++ ce_ass X :: nil) (md_alias E) ->
    semK Γ (me_lit (gu_mk (Δ ++ ce_ass X :: nil) (md_alias E))) -> Θm ⍮ Ξm ⍮ Γ ⊢ N : X -> Γ ⊨ N : X ->
    Γ ⊨ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) (md_alias E))) N
      ≈ me_lit (gu_mk (tele_sub Δ (Id,,N)) (md_alias E[sb_qn (List.length Δ) (Id,,N)]ᵐ)) /\
    smt Γ (me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) (md_alias E))) N) /\
    smt Γ (me_lit (gu_mk (tele_sub Δ (Id,,N)) (md_alias E[sb_qn (List.length Δ) (Id,,N)]ᵐ))).
Proof.
  intros * HU HK HNw HN.
  pose proof (wf_me_beta_alias _ _ _ _ _ _ _ HU HNw) as Hb.
  destruct (k_beta _ _ _ _ _ (wf_me_lit _ _ _ _ _ HU) (wf_me_trans _ _ _ _ _ _ Hb (wf_me_sym _ _ _ _ _ Hb)) HK HNw HN) as (H1 & H2 & H3).
  rewrite gunit_sub_mk in H1, H3; cbn [moddef_sub] in H1, H3.
  split; [ exact H1 | split; assumption ].
Qed.

(** [β] for an alias with no parameter. *)
Lemma k_alias0 : forall Γ E, Θm ⍮ Ξm ⍮ Γ ⊢ᵐ E ≈ E -> ⊨ Γ -> Γ ⊨ᵐ E ≈ E -> smt Γ E ->
    Γ ⊨ᵐ me_lit (gu_mk nil (md_alias E)) ≈ E /\ smt Γ (me_lit (gu_mk nil (md_alias E))).
Proof.
  intros * Hw HΓ HE Hs.
  pose proof (wf_me_beta_alias0 _ _ _ _ Hw) as Hb.
  pose proof (wf_me_trans _ _ _ _ _ _ Hb (wf_me_sym _ _ _ _ _ Hb)) as Hw'.
  assert (HL : Γ ⊨ᵐ me_lit (gu_mk nil (md_alias E)) ≈ me_lit (gu_mk nil (md_alias E))).
  { apply rel_lit_alias; [ constructor; [ exact HΓ | exact HΓ | exact (sem_ctx_per_ctx HΓ) ] | constructor | constructor
                         | reflexivity | exact HE | exact HE ]. }
  split; [ exact (rel_me_beta_alias0 _ _ HE) |].
  apply (smt_of_semK _ _ Hgf).
  eapply sk_alias; [ exact Hw' | constructor | exact HΓ | exact HΓ | exact HL | exact HE | exact Hs ].
Qed.

(** A loaded unit or an open frame, by its path. *)
Lemma k_unit_path : forall Γ fp TΦ, wf_ctx Θm Ξm Γ -> gc_unit Θm Ξm (me_unit fp) = Some TΦ -> ⊨ Γ ->
    Γ ⊨ᵐ me_unit fp ≈ me_unit fp /\ smt Γ (me_unit fp).
Proof.
  intros * HwΓ Hu HΓ.
  pose proof (wf_me_unit _ _ _ _ _ HwΓ Hu) as Hw.
  destruct TΦ as [T Φ].
  destruct (gc_unit_loc _ _ _ _ _ Hu) as (mp & Hq & Hl).
  pose proof (mod_qname_inv _ _ Hq) as Heq.
  pose proof (gc_loc_of_loc _ _ Hgm _ _ _ Hl) as Hgl.
  assert (Hs : sargs Γ T nil).
  { apply (mk_sargs _ _ _ T nil); [ rewrite app_nil_r; reflexivity | reflexivity | constructor | cbn; auto
                                  | intros [|k] ? ? Hk; discriminate ]. }
  rewrite Heq in Hw |- *.
  pose proof (sk_filed _ _ _ _ _ _ nil Hw Hgl HΓ Hs) as HK.
  split; [ exact (filed_valid _ _ Hgf _ _ _ _ nil Hgl HΓ Hs) | exact (smt_of_semK _ _ Hgf _ _ HK) ].
Qed.

(** An alias unit. *)
Lemma k_unit_alias : forall Γ Δ Δ' E E',
    Θm ⍮ Ξm ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E') -> Θm ⍮ Ξm ⍮ Γ ⊢ˣ Δ ≈ Δ' ->
    Γ ⊨ˣ Δ ≈ Δ' -> tele_ass Δ -> tele_ass Δ' -> ⊨ Γ ->
    Δ ++ Γ ⊨ᵐ E ≈ E' -> Δ' ++ Γ ⊨ᵐ E' ≈ E' -> smt (Δ ++ Γ) E -> smt (Δ' ++ Γ) E' ->
    Γ ⊨ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E') /\
    semK Γ (me_lit (gu_mk Δ (md_alias E))) /\ semK Γ (me_lit (gu_mk Δ' (md_alias E'))).
Proof.
  intros * Hu HΔw HΔ Ha Ha' HΓ HE HE' Hs Hs'.
  pose proof (ext_eq_length _ _ _ _ _ HΔw) as Hl.
  pose proof HΔ as [HΔΓ HΔ'Γ _].
  pose proof (rel_lit_alias _ _ _ _ _ HΔ Ha Ha' Hl HE HE') as HR.
  pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_trans _ _ _ _ _ _ Hu (wf_unit_eq_sym _ _ _ _ _ Hu))) as Hw.
  pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_trans _ _ _ _ _ _ (wf_unit_eq_sym _ _ _ _ _ Hu) Hu)) as Hw'.
  split; [ constructor; [ exact HR | .. ]; apply sem_unit_alias; first [ assumption | exact (rel_modexp_refl_left HE) ] |].
  split; [ eapply sk_alias; [ exact Hw | exact Ha | exact HΓ | exact HΔΓ | exact (rel_modexp_refl_left HR)
                            | exact (rel_modexp_refl_left HE) | exact Hs ] |].
  eapply sk_alias; [ exact Hw' | exact Ha' | exact HΓ | exact HΔ'Γ | exact (rel_modexp_refl_right HR) | exact HE' | exact Hs' ].
Qed.

(** An alias of a literal, flattened. *)
Lemma k_unit_flatten : forall Γ Δ Δ' D,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ≈ gu_mk (Δ' ++ Δ) D ->
    tele_ass Δ -> ⊨ Γ -> ⊨ Δ ++ Γ -> semK (Δ ++ Γ) (me_lit (gu_mk Δ' D)) ->
    Γ ⊨ᵘ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ≈ gu_mk (Δ' ++ Δ) D /\
    semK Γ (me_lit (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))) /\ semK Γ (me_lit (gu_mk (Δ' ++ Δ) D)).
Proof.
  intros * Hu Ha HΓ HΔΓ HK.
  pose proof (rel_lit_flatten _ _ Hgm Hgf _ _ _ _ Ha HK) as HR.
  pose proof (semK_valid _ _ Hgf _ _ HK) as HV.
  pose proof (semK_abs _ _ Hgm Hgf _ _ _ HK Ha) as HK'; cbn [gunit_abs] in HK'.
  pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_trans _ _ _ _ _ _ Hu (wf_unit_eq_sym _ _ _ _ _ Hu))) as Hw.
  split; [ constructor; [ exact HR | apply sem_unit_alias; assumption | exact (ruu_right _ _ _ (semK_lit_unit Hgw _ _ Hgm Hsub _ _ HK')) ] |].
  split; [| exact HK' ].
  eapply sk_alias; [ exact Hw | exact Ha | exact HΓ | exact HΔΓ | exact (rel_modexp_refl_left HR) | exact HV
                   | exact (smt_of_semK _ _ Hgf _ _ HK) ].
Qed.

(** A body unit. *)
Lemma k_unit_body : forall Γ Δ Δ' Φ Φ' Φx Φx',
    Θm ⍮ Ξm ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' ->
    body_xp Θm Ξm (Δ ++ Γ) Φ Φx -> body_xp Θm Ξm (Δ' ++ Γ) Φ' Φx' ->
    Γ ⊨ˣ Δ ≈ Δ' -> ⊨ Γ ->
    ⊨ (body_ctx Φx ++ Δ) ++ Γ -> ctx_ok ((body_ctx Φx ++ Δ) ++ Γ) ->
    ⊨ (body_ctx Φx' ++ Δ') ++ Γ -> ctx_ok ((body_ctx Φx' ++ Δ') ++ Γ) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
      (exists i, Δ ++ Γ ⊨ A[σ] ≈ A'[σ'] : Typeω@i) /\ Δ ++ Γ ⊨ M[σ] ≈ M'[σ'] : A[σ]) ->
    (forall y Φ0 pv U Φ0' pv' U' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_mod pv' U')) ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
      Δ ++ Γ ⊨ᵐ me_lit U[σ]ᵘ ≈ me_lit U'[σ']ᵘ) ->
    (forall k Φ0 H Φ0' H' σ σ',
      nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Δ ++ Γ ⊨ᵐ H[σ]ᵐ ≈ H'[σ']ᵐ) ->
    (forall k Ψo H, nth_error (body_opens Φ Φx) k = Some (Ψo, H) -> Ψo ++ Δ ++ Γ ⊨ᵐ H ≈ H /\ smt (Ψo ++ Δ ++ Γ) H) ->
    (forall k Ψo H, nth_error (body_opens Φ' Φx') k = Some (Ψo, H) -> Ψo ++ Δ' ++ Γ ⊨ᵐ H ≈ H /\ smt (Ψo ++ Δ' ++ Γ) H) ->
    tele_ass Δ -> tele_ass Δ' -> List.length Δ = List.length Δ' ->
    body_shape Φ Φ' -> body_shape Φx Φx' -> List.NoDup (gm_names Φ) ->
    Γ ⊨ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' /\ semK Γ (me_lit (gu_open Δ Φ)) /\ semK Γ (me_lit (gu_open Δ' Φ')).
Proof.
  intros * Hu Hx Hx' HΔ HΓ HC HokC HC' HokC' HD HU HO Ho Ho' Ha Ha' Hl Hs Hsxx Hnd.
  rewrite <- app_assoc in HC, HokC, HC', HokC'.
  pose proof (body_shape_l _ _ Hsxx) as Hsx; pose proof (body_shape_r _ _ Hsxx) as Hsx'.
  pose proof (body_shape_l _ _ Hs) as Hsw; pose proof (body_shape_r _ _ Hs) as Hsw'.
  assert (HndX : List.NoDup (gm_names Φx)) by (rewrite (body_xp_names _ _ _ _ _ Hx); exact Hnd).
  assert (HndX' : List.NoDup (gm_names Φx'))
    by (rewrite (body_xp_names _ _ _ _ _ Hx'), <- (body_shape_names _ _ Hs); exact Hnd).
  assert (Hk : forall k Ψo H, nth_error (body_opens Φ Φx) k = Some (Ψo, H) ->
             Ψo ++ Δ ++ Γ ⊨ᵐ H ≈ H /\ kinds_ok Θm Ξm (Ψo ++ Δ ++ Γ) H)
    by (intros * Hn; destruct (Ho _ _ _ Hn) as [HV HS]; exact (conj HV (smt_kinds _ _ Hgm Hgf _ _ HS))).
  assert (Hk' : forall k Ψo H, nth_error (body_opens Φ' Φx') k = Some (Ψo, H) ->
             Ψo ++ Δ' ++ Γ ⊨ᵐ H ≈ H /\ kinds_ok Θm Ξm (Ψo ++ Δ' ++ Γ) H)
    by (intros * Hn; destruct (Ho' _ _ _ Hn) as [HV HS]; exact (conj HV (smt_kinds _ _ Hgm Hgf _ _ HS))).
  pose proof (rel_lit_body _ _ _ _ _ _ _ _ _ HΔ Ha Ha' Hl Hx Hx' Hs Hsx Hsx' Hsw Hsw' HndX HndX' HC HC' HD HU HO Hk Hk') as HR.
  pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_trans _ _ _ _ _ _ Hu (wf_unit_eq_sym _ _ _ _ _ Hu))) as Hw.
  pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_trans _ _ _ _ _ _ (wf_unit_eq_sym _ _ _ _ _ Hu) Hu)) as Hw'.
  assert (Hslots : forall Φx0 Δ0, ctx_ok (body_ctx Φx0 ++ Δ0 ++ Γ) -> gm_nopens Φx0 = 0 ->
             forall y Φ0 pv U, gm_prefix_upto Φx0 y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
             semK (body_ctx Φ0 ++ Δ0 ++ Γ) (me_lit U)).
  { intros * Hok Hn * Hp.
    destruct (prefix_body_ctx _ _ _ Hn Hp) as [X HX]; cbn [body_ctx] in HX.
    apply (Hok X U); rewrite HX, <- app_assoc; reflexivity. }
  split; [ constructor; [ exact HR | | ] |].
  - eapply sem_unit_body; [ exact Ha | exact (body_xp_target Hgw _ _ Hgm Hsub _ _ _ Hx) | exact Hsw | exact Hsx | exact HC |].
    intros * Hn; exact (proj1 (Ho _ _ _ Hn)).
  - eapply sem_unit_body; [ exact Ha' | exact (body_xp_target Hgw _ _ Hgm Hsub _ _ _ Hx') | exact Hsw' | exact Hsx' | exact HC' |].
    intros * Hn; exact (proj1 (Ho' _ _ _ Hn)).
  - split.
    + eapply sk_body; [ exact Hw | exact Hx | exact Ha | exact HΓ | exact HC
                      | exact (Hslots _ _ HokC (body_xp_nopens _ _ _ _ _ Hx)) | exact Hsw | exact Hsx
                      | exact (rel_modexp_refl_left HR) | intros * Hn; exact (proj1 (Ho _ _ _ Hn))
                      | intros * Hn; exact (proj2 (Ho _ _ _ Hn)) ].
    + eapply sk_body; [ exact Hw' | exact Hx' | exact Ha' | exact HΓ | exact HC'
                      | exact (Hslots _ _ HokC' (body_xp_nopens _ _ _ _ _ Hx')) | exact Hsw' | exact Hsx'
                      | exact (rel_modexp_refl_right HR) | intros * Hn; exact (proj1 (Ho' _ _ _ Hn))
                      | intros * Hn; exact (proj2 (Ho' _ _ _ Hn)) ].
Qed.

End Cases.

