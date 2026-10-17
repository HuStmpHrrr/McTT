(** * The Global Rules: Validity along an Embedding

    A judgment of the global context [Θ1 ⍮ Ξ1] is valid at every [Θ2 ⍮ Ξ2] it
    embeds into, provided the modules [Θ1 ⍮ Ξ1] files and has open are valid
    at [Θ2 ⍮ Ξ2] ([sem_emb]): the fundamental theorem holds in this form for
    every rule ([kripke_fundamental]), each case being the fixed-context case
    lemma at the target, the units and module expressions being moreover
    valid in what they denote, read at [Θ1 ⍮ Ξ1] ([semK], [smt]).  At the
    identity it is the fixed-context theorem. *)

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
  { apply rel_lit_alias; [ split; [ exact HΓ | split; [ exact HΓ | exact (sem_ctx_per_ctx HΓ) ] ] | constructor | constructor
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
  { exists T, nil; rewrite app_nil_r; split; [ reflexivity |]; split; [ reflexivity |]; split; [ constructor |].
    split; [ cbn; auto | intros [|k] ? ? Hk; discriminate ]. }
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
  pose proof HΔ as (HΔΓ & HΔ'Γ & _).
  pose proof (rel_lit_alias _ _ _ _ _ HΔ Ha Ha' Hl HE HE') as HR.
  pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_trans _ _ _ _ _ _ Hu (wf_unit_eq_sym _ _ _ _ _ Hu))) as Hw.
  pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_trans _ _ _ _ _ _ (wf_unit_eq_sym _ _ _ _ _ Hu) Hu)) as Hw'.
  split; [ split; [ exact HR | split; apply sem_unit_alias; first [ assumption | exact (rel_modexp_refl_left HE) ] ] |].
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
  split; [ split; [ exact HR | split; [ apply sem_unit_alias; assumption | exact (proj2 (proj2 (semK_lit_unit Hgw _ _ Hgm Hsub _ _ HK'))) ] ] |].
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
  split; [ split; [ exact HR | split ] |].
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

(** ** 3. Sound embeddings *)

(** [Θ1 ⍮ Ξ1] embeds soundly into [Θ2 ⍮ Ξ2]: it grows into it, and what it
    files and has open is valid there, its declarations too. *)
Record sem_emb (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  { sme_emb : Emb Θ1 Ξ1 Θ2 Ξ2
  ; sme_wf : ⊢ᵍ Θ1 ⍮ Ξ1
  ; sme_filed : @gfiled_ok (gc_mk Θ2 Ξ2) Θ1 Ξ1
  ; sme_ind : forall p D, ind_lookup Θ1 Ξ1 p = Some D -> @sem_core (gc_mk Θ2 Ξ2) D
  }.

(** ** 3. The fundamental theorem along an embedding *)

Definition kctx Θ1 Ξ1 Γ : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 -> @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ1 Ξ1 Γ.

Definition kexp_eq Θ1 Ξ1 Γ A M M' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ1 Ξ1 Γ /\ @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A M M'.

Definition ksubtyp Θ1 Ξ1 Γ A A' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ1 Ξ1 Γ /\ @subtyp_under_ctx (gc_mk Θ2 Ξ2) Γ A A'.

Definition kuniv Θ1 Ξ1 Γ U : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ1 Ξ1 Γ /\
    ((exists i : nat, U = Typeω@i) \/ (exists L (n : nat), U = Type⟨L⟩ /\ @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (Level@n) L L)).

Definition kext Θ1 Ξ1 Γ Ψ Ψ' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ Ψ Ψ' /\
    @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ1 Ξ1 (Ψ ++ Γ) /\ @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ1 Ξ1 (Ψ' ++ Γ) /\
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ1 Ξ1 Γ.

Definition kunit Θ1 Ξ1 Γ U U' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 ->
    @rel_unit_under_ctx (gc_mk Θ2 Ξ2) Γ U U' /\
    @SemK.semK (gc_mk Θ2 Ξ2) Θ1 Ξ1 Γ (me_lit U) /\ @SemK.semK (gc_mk Θ2 Ξ2) Θ1 Ξ1 Γ (me_lit U') /\
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ1 Ξ1 Γ.

Definition kmod Θ1 Ξ1 Γ H H' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ1 Ξ1 Θ2 Ξ2 ->
    @rel_modexp_under_ctx (gc_mk Θ2 Ξ2) Γ H H' /\
    @SemK.smt (gc_mk Θ2 Ξ2) Θ1 Ξ1 Γ H /\ @SemK.smt (gc_mk Θ2 Ξ2) Θ1 Ξ1 Γ H' /\
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ1 Ξ1 Γ.

Ltac kcase :=
  repeat match goal with IH : forall _ _, sem_emb _ _ _ _ -> _, He : sem_emb _ _ _ _ |- _ =>
    specialize (IH _ _ He) end;
  destruct_conjs.

(** ** The cases of the inductive types, at the target *)

Lemma k_decl : forall Θ Ξ Θ2 Ξ2 Γ p D, sem_emb Θ Ξ Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D ->
    ind_lookup Θ2 Ξ2 p = Some D /\ @sem_decl (gc_mk Θ2 Ξ2) D /\ decl_closed D /\ ind_sort_univ (ind_sort D) /\
    decl_typed Θ2 Ξ2 D.
Proof.
  intros * He HΓ Hl.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [Hdt Hc].
  pose proof (decl_typed_emb _ _ _ _ _ (sme_emb _ _ _ _ He) Hdt) as Hdt2.
  pose proof Hdt as (_ & _ & _ & _ & Hsu & _).
  pose proof (ind_lookup_gc_sub _ _ _ _ _ _ (em_res _ _ _ _ (sme_emb _ _ _ _ He)) Hl) as Hl2.
  split; [ exact Hl2 | split; [| split; [ exact Hc | split; [ exact Hsu | exact Hdt2 ] ] ] ].
  exact (@sem_decl_of_core (gc_mk Θ2 Ξ2) D (sme_ind _ _ _ _ He _ _ Hl) Hc Hsu Hdt2).
Qed.

Lemma k_ind : forall Θ Ξ Θ2 Ξ2 Γ p D, sem_emb Θ Ξ Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ -> @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (ind_ty D) (a_ind p) (a_ind p).
Proof.
  intros * He HΓ Hl HΓ2.
  destruct (k_decl _ _ _ _ _ _ _ He HΓ Hl) as (Hl2 & HD & Hc & Hsu & _).
  exact (@closed_weaken_valid (gc_mk Θ2 Ξ2) Γ _ _ _ HΓ2 (@valid_exp_ind0 (gc_mk Θ2 Ξ2) D HD Hc Hsu p Hl2)).
Qed.

Lemma k_con : forall Θ Ξ Θ2 Ξ2 Γ p D c gs, sem_emb Θ Ξ Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D ->
    ind_con D c = Some gs ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ -> @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (con_ty p D gs) (a_con p c) (a_con p c).
Proof.
  intros * He HΓ Hl Hcon HΓ2.
  destruct (k_decl _ _ _ _ _ _ _ He HΓ Hl) as (Hl2 & HD & Hc & Hsu & _).
  destruct (@sd_conty (gc_mk Θ2 Ξ2) D HD p c gs Hl2 Hcon) as [j HT].
  pose proof (@sd_cargs (gc_mk Θ2 Ξ2) D HD p c gs Hl2 Hcon) as HΨ.
  exact (@closed_weaken_valid (gc_mk Θ2 Ξ2) Γ _ _ _ HΓ2 (@valid_exp_con0 (gc_mk Θ2 Ξ2) D HD Hc Hsu p Hl2 c gs Hcon HΨ j HT)).
Qed.

Lemma k_elim_cong : forall Θ Ξ Θ2 Ξ2 Γ p D Ps M M' nm A A' (i : nat) Bs Bs',
    sem_emb Θ Ξ Θ2 Ξ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : apps (a_ind p) Ps -> ind_lookup Θ Ξ p = Some D ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       kexp_eq Θ Ξ Γ T P P) ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (apps (a_ind p) Ps) M M' ->
    nm = S (ind_nn D) ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ) (Typeω@i) A A' ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ (elim_mctx p D (List.firstn (ind_nu D) Ps)) (elim_mctx p D (List.firstn (ind_nu D) Ps)) ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs ->
       kext Θ Ξ Γ (elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) (elim_bctx p D gs A (List.firstn (ind_nu D) Ps))) ->
    List.map fst Bs = List.map fst Bs' ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall k c gs n B B', List.nth_error Bs k = Some (c, n, B) -> List.nth_error Bs' k = Some (c, n, B') ->
       ind_con D c = Some gs ->
       kexp_eq Θ Ξ (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) (elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) B B') ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)]) (a_elim nm A Bs M) (a_elim nm A' Bs' M').
Proof.
  intros * He HMs Hl HPl HPs HMM Hnm HA HMx HBn HBc HBf Hnb HB HΓ2.
  destruct (k_decl _ _ _ _ _ _ _ He (presup_exp_eq_ctx HMs) Hl) as (Hl2 & HD & Hc & Hsu & Hdt2).
  eapply (@rel_exp_elim_cong (gc_mk Θ2 Ξ2)); try eassumption.
  - intros * HP HT; exact (proj2 (proj2 (HPs _ _ _ HP HT _ _ He))).
  - exact (proj1 HMx).
  - intros c gs Hcon; exact (proj1 (proj1 (HBc _ _ Hcon _ _ He))).
  - intros * Hk Hk' Hcon; exact (proj2 (proj2 (HB _ _ _ _ _ _ Hk Hk' Hcon _ _ He))).
Qed.

Lemma k_elim : forall Θ Ξ Θ2 Ξ2 Γ p D Ps M nm A (i : nat) Bs,
    sem_emb Θ Ξ Θ2 Ξ2 -> ind_lookup Θ Ξ p = Some D ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       kexp_eq Θ Ξ Γ T P P) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : apps (a_ind p) Ps ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (apps (a_ind p) Ps) M M ->
    nm = S (ind_nn D) ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ) (Typeω@i) A A ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ (elim_mctx p D (List.firstn (ind_nu D) Ps)) (elim_mctx p D (List.firstn (ind_nu D) Ps)) ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs ->
       kext Θ Ξ Γ (elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) (elim_bctx p D gs A (List.firstn (ind_nu D) Ps))) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
       kexp_eq Θ Ξ (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) (elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) B B) ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)]) (a_elim nm A Bs M) (a_elim nm A Bs M).
Proof.
  intros * He Hl HPl HPs HMs HMM Hnm HA HMx HBn HBc Hnb HB HΓ2.
  destruct (k_decl _ _ _ _ _ _ _ He (presup_exp_ctx HMs) Hl) as (Hl2 & HD & Hc & Hsu & Hdt2).
  eapply (@rel_exp_elim_cong (gc_mk Θ2 Ξ2)); try eassumption; [ | | | reflexivity |].
  - intros * HP HT; exact (proj2 (proj2 (HPs _ _ _ HP HT _ _ He))).
  - exact (proj1 HMx).
  - intros c gs Hcon; exact (proj1 (proj1 (HBc _ _ Hcon _ _ He))).
  - intros * Hk Hk' Hcon; rewrite Hk in Hk'; injection Hk' as <-.
    exact (proj2 (proj2 (HB _ _ _ _ Hcon (List.nth_error_In _ _ Hk) _ _ He))).
Qed.

Lemma k_iota : forall Θ Ξ Θ2 Ξ2 Γ p D c gs Ps As nm A (i : nat) Bs n B,
    sem_emb Θ Ξ Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       kexp_eq Θ Ξ Γ T P P) ->
    List.length As = List.length gs ->
    (forall k N T, List.nth_error As k = Some N -> List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) k = Some T ->
       kexp_eq Θ Ξ Γ T N N) ->
    nm = S (ind_nn D) ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ) (Typeω@i) A A ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ (elim_mctx p D (List.firstn (ind_nu D) Ps)) (elim_mctx p D (List.firstn (ind_nu D) Ps)) ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs ->
       kext Θ Ξ Γ (elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) (elim_bctx p D gs A (List.firstn (ind_nu D) Ps))) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
       kexp_eq Θ Ξ (elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) (elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) B B) ->
    brs_lookup Bs c = Some (n, B) ->
    @sem_ctx (gc_mk Θ2 Ξ2) Γ ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ apps (a_con p c) (Ps ++ As) :: nil)])
      (a_elim nm A Bs (apps (a_con p c) (Ps ++ As)))
      (B[sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ elim_ihs nm A Bs (sb_of_list Id Ps) gs As)]).
Proof.
  intros * He HΓ Hl Hcon HPl HPs HAl HAs Hnm HA HMx HBn HBc Hnb HB Hlk HΓ2.
  destruct (k_decl _ _ _ _ _ _ _ He HΓ Hl) as (Hl2 & HD & Hc & Hsu & Hdt2).
  pose proof (decl_closed_nu D Hc) as Hle.
  set (Us := List.firstn (ind_nu D) Ps) in *.
  set (Ns := List.skipn (ind_nu D) Ps) in *.
  assert (HPeq : Ps = Us ++ Ns) by (symmetry; apply List.firstn_skipn).
  assert (HPs' : forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
                   @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ T P P)
    by (intros * HP HT; exact (proj2 (proj2 (HPs _ _ _ HP HT _ _ He)))).
  destruct (@params_valid_split (gc_mk Θ2 Ξ2) D Γ Ps Hc HPl HPs') as [HUs HNs]; fold Us Ns in HUs, HNs.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; lia).
  assert (HNl : List.length Ns = ind_nn D) by (unfold Ns; rewrite List.length_skipn; unfold ind_nn; lia).
  assert (HAs' : forall k N T, List.nth_error As k = Some N ->
                   List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) k = Some T ->
                   @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ T N N)
    by (intros * HN HT; rewrite <- HPeq in HT; exact (proj2 (proj2 (HAs _ _ _ HN HT _ _ He)))).
  pose proof (@rel_exp_elim_iota_at (gc_mk Θ2 Ξ2) Γ p D Us Ns As c gs nm A i Bs HD Hc Hsu Hdt2 Hl2 HΓ2 Hcon HUl HUs HNl HAl Hnm HA
                (proj1 HMx) HBn (fun c gs Hcon => proj1 (proj1 (HBc c gs Hcon _ _ He))) Hnb
                (fun c gs n B Hcon Hin => proj2 (proj2 (HB c gs n B Hcon Hin _ _ He))) HNs HAs' n B Hlk) as Hi.
  rewrite HPeq, <- List.app_assoc; exact Hi.
Qed.

(** A body unit, from the induction hypotheses of its rule. *)
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
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> kexp_eq Θ Ξ (Δ ++ Γ) (Typeω@(lv y)) A[σ] A'[σ']) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> kexp_eq Θ Ξ (Δ ++ Γ) A[σ] M[σ] M'[σ']) ->
    (forall y Φ0 pv U Φ0' pv' U' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_mod pv' U')) ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> kunit Θ Ξ (Δ ++ Γ) U[σ]ᵘ U'[σ']ᵘ) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> kmod Θ Ξ (Ψ ++ Δ ++ Γ) H H) ->
    (forall k Ψ' H', nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> kmod Θ Ξ (Ψ' ++ Δ' ++ Γ) H' H') ->
    (forall k Φ0 H Φ0' H' σ σ',
      nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> kmod Θ Ξ (Δ ++ Γ) H[σ]ᵐ H'[σ']ᵐ) ->
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
           (proj1 HC) HokC (proj1 HC') HokC'); try assumption.
  - intros * Hp Hp' Hf Hf'; split; [ eexists; exact (proj2 (proj2 (HA _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hp' Hf Hf' _ _ He))) |].
    exact (proj2 (proj2 (HM _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hp' Hf Hf' _ _ He))).
  - intros * Hp Hp' Hf Hf'; exact (proj1 (proj1 (HU _ _ _ _ _ _ _ _ _ Hp Hp' Hf Hf' _ _ He))).
  - intros * Hk Hk' Hf Hf'; exact (proj1 (HO _ _ _ _ _ _ _ Hk Hk' Hf Hf' _ _ He)).
  - intros * Hk; destruct (Ho _ _ _ Hk _ _ He) as (HV & HS & _); exact (conj HV HS).
  - intros * Hk; destruct (Ho' _ _ _ Hk _ _ He) as (HV & HS & _); exact (conj HV HS).
Qed.

Theorem kripke_fundamental :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> kctx Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> kexp_eq Θ Ξ Γ A M M) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> kexp_eq Θ Ξ Γ A M M') /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> ksubtyp Θ Ξ Γ A A') /\
  (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> kuniv Θ Ξ Γ U) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> kext Θ Ξ Γ Ψ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> kunit Θ Ξ Γ U U') /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> kmod Θ Ξ Γ H H').
Proof.
  apply syntactic_wf_mut_ind; unfold kctx, kexp_eq, ksubtyp, kuniv, kext, kunit, kmod; intros;
    match goal with He : sem_emb _ _ _ _ |- _ =>
      pose proof (sme_emb _ _ _ _ He) as Hemb; pose proof (sme_wf _ _ _ _ He) as Hgm;
      pose proof (sme_filed _ _ _ _ He) as Hgf end;
    pose proof (em_res _ _ _ _ Hemb) as Hsub; pose proof (em_wf _ _ _ _ Hemb) as Hgw;
    match goal with He : sem_emb _ _ ?T2 ?X2 |- _ =>
      change (⊢ᵍ @gc_deps (gc_mk T2 X2) ⍮ @gc_stack (gc_mk T2 X2)) in Hgw;
      match type of Hsub with gc_sub ?T1 ?X1 _ _ =>
        change (gc_sub T1 X1 (@gc_deps (gc_mk T2 X2)) (@gc_stack (gc_mk T2 X2))) in Hsub end end;
    kcase.
  (** Contexts. *)
  all: try solve [ split; [ constructor | apply ctx_ok_nil ] ].
  all: try solve [ split; [ eapply rel_ctx_extend'; eassumption | apply ctx_ok_ass; assumption ] ].
  all: try solve [ split; [ eapply rel_ctx_extend_def'; eassumption | apply ctx_ok_def; assumption ] ].
  (** Terms whose case lemma predates modules. *)
  all: try (split; [ assumption | split; [ assumption |] ]).
  all: try solve [ apply valid_exp_typ; assumption
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
    | apply subtyp_small_large; assumption ].
  all: try solve [ eapply valid_exp_var; eassumption | eapply rel_exp_var_delta; eassumption ].
  all: try solve [ eapply rel_exp_fn_eta; eassumption ].
  all: try solve [ apply valid_exp_True; assumption | apply valid_exp_False; assumption
                 | apply valid_exp_True_small; assumption | apply valid_exp_False_small; assumption
                 | eapply rel_exp_univ_cong_tm; eassumption | eapply valid_exp_univ_tm; eassumption
                 | eapply valid_exp_maxl_absorb; eassumption | eapply rel_exp_maxl_absorb; eassumption
                 | eapply subtyp_suniv_tm; eassumption | eapply subtyp_small_large_tm; eassumption
                 | apply subtyp_level; assumption ].
  (** The universes. *)
  all: try solve [ left; eexists; reflexivity | right; do 2 eexists; split; [ reflexivity | eassumption ] ].
  (** [Π] at a universe. *)
  all: try solve [
    match goal with HU : (exists i : nat, ?U = Typeω@i) \/ _ |- _ =>
      destruct HU as [[? ->] | (? & ? & -> & ?)]; cbn [exp_wk] in *;
      [ eapply rel_exp_pi_cong; eassumption | eapply rel_exp_pi_cong_small_tm; eassumption ] end ].
  (** The inductive types. *)
  all: try solve [ eapply k_ind; eassumption | eapply k_con; eassumption
                 | eapply k_elim; eassumption | eapply k_elim_cong; eassumption | eapply k_iota; eassumption ].
  (** Module slots and local modules. *)
  all: try solve [ split; [ apply rel_ctx_extend_mod'; assumption | apply ctx_ok_mod; assumption ] ].
  all: try solve [ eapply valid_exp_let_mod; eassumption | eapply rel_exp_let_mod_cong; eassumption
                 | eapply rel_exp_let_mod_zeta; eassumption ].
  (** Members. *)
  all: try solve [
    match goal with Hs : smt _ _ _ ?H, Hm : mdenote _ _ _ (me_mem ?H ?x) ?R, Ht : ds_ty _ _ ?R = Some _,
                    HH : _ ⊨ᵐ ?H ≈ ?H' |- _ ⊨ a_mem ?H ?x ≈ a_mem ?H' ?x : _ =>
      pose proof (proj2 (semK_mem_all _ _ Hgm Hgf) _ _ Hs _ _ _ Hm Ht) as Hsm;
      apply rel_exp_under_ctx_sym;
      exact (rel_mem_of_smem _ _ _ _ _ _ (rel_modexp_sym HH) Hsm) end ].
  all: try solve [
    match goal with Hs : smt _ _ _ ?H, Hm : mdenote _ _ _ (me_mem ?H ?x) ?R, Ht : ds_ty _ _ ?R = Some _,
                    HH : _ ⊨ᵐ ?H ≈ ?H |- _ ⊨ a_mem ?H ?x ≈ a_mem ?H ?x : _ =>
      pose proof (proj2 (semK_mem_all _ _ Hgm Hgf) _ _ Hs _ _ _ Hm Ht) as Hsm;
      exact (rel_mem_of_smem _ _ _ _ _ _ HH Hsm) end ].
  all: try solve [
    match goal with Hs : smt _ _ _ ?H, Hm : mdenote _ _ _ (me_mem ?H ?x) ?R, Ht : ds_ty _ _ ?R = Some _,
                    Hr : ds_red ?R = Some ?M, HH : _ ⊨ᵐ ?H ≈ ?H |- _ ⊨ a_mem ?H ?x ≈ ?M : _ =>
      pose proof (proj2 (semK_mem_all _ _ Hgm Hgf) _ _ Hs _ _ _ Hm Ht) as Hsm; rewrite Hr in Hsm;
      exact (rel_mem_red_of_smem _ _ _ _ _ _ HH Hsm) end ].
  (** Extensions. *)
  all: try solve [ split; [ apply rel_ext_nil; assumption | cbn [app]; repeat (split; [ assumption |]); assumption ] ].
  all: try solve [ split; [ first [ eapply rel_ext_ass; eassumption | eapply rel_ext_def; eassumption | eapply rel_ext_mod; eassumption ] |];
                   cbn [app]; repeat split;
                   first [ assumption | apply ctx_ok_ass; assumption | apply ctx_ok_def; assumption | apply ctx_ok_mod; assumption ] ].
  (** Units. *)
  all: try solve [
    match goal with |- ?A /\ ?B /\ ?C /\ _ =>
      cut (A /\ B /\ C); [ intros (? & ? & ?); repeat (split; [ assumption |]); assumption |];
      first [ eapply k_unit_alias; [ eapply wf_unit_eq_alias; eassumption | eassumption .. ]
            | eapply (k_unit_flatten Hgw _ _ Hgm Hsub Hgf); [ eapply wf_unit_eq_flatten; eassumption | eassumption .. ] ] end ].
  all: try solve [ split; [ match goal with HU : _ ⊨ᵘ _ ≈ _ |- _ =>
                              destruct HU as (? & ? & ?); split; [ apply rel_modexp_sym; assumption | split; assumption ] end
                          | repeat (split; [ assumption |]); assumption ] ].
  all: try solve [ split; [ match goal with HU1 : _ ⊨ᵘ ?U1 ≈ ?U2, HU2 : _ ⊨ᵘ ?U2 ≈ ?U3 |- _ ⊨ᵘ ?U1 ≈ ?U3 =>
                              destruct HU1 as (? & ? & ?); destruct HU2 as (? & ? & ?);
                              split; [ eapply rel_modexp_trans; eassumption | split; assumption ] end
                          | repeat (split; [ assumption |]); assumption ] ].
  (** Module expressions. *)
  all: try solve [
    match goal with |- ?A /\ ?B /\ ?B /\ _ =>
      cut (A /\ B); [ intros (? & ?); repeat (split; [ assumption |]); assumption | eapply (k_unit_path _ _ Hgm Hgf); eassumption ] end ].
  all: try solve [
    match goal with Hl : _ ∋ # ?x ≔ₘ ?U, Hg : @gfiled_ok ?G ?T1 ?X1 |- ?Γ0 ⊨ᵐ me_var ?x ≈ ?H' /\ ?S /\ _ =>
      cut (S /\ @SemK.semK G T1 X1 Γ0 (me_lit U));
      [ intros (? & ?);
        split; [ first [ eapply rel_me_var; eassumption | eapply rel_me_delta_slot; eassumption ] |];
        split; [ assumption |]; split; [ first [ assumption | apply (smt_of_semK _ _ Hgf); assumption ] | split; assumption ]
      | eapply (k_var Hgw _ _ Hgm Hsub); [ eapply wf_me_var; eassumption | eassumption .. ] ] end ].
  all: try solve [ split; [ match goal with HU : _ ⊨ᵘ _ ≈ _ |- _ => exact (proj1 HU) end |];
                   split; [ apply (smt_of_semK _ _ Hgf); assumption |]; split; [ apply (smt_of_semK _ _ Hgf); assumption |];
                   split; assumption ].
  all: try solve [
    match goal with |- ?A /\ ?B /\ ?C /\ _ =>
      cut (A /\ B /\ C); [ intros (? & ? & ?); repeat (split; [ assumption |]); assumption |];
      first [ eapply (k_mem Hgw _ _ Hgm Hsub Hgf); eassumption | eapply (k_app Hgw _ _ Hgm Hsub Hgf); eassumption ] end ].
  all: try solve [
    match goal with Hs : smt _ _ _ (me_mem ?H ?y), Hm : mdenote _ _ _ (me_mem ?H ?y) ?R, Hmd : ds_mod _ _ ?R = Some ?Rm
                    |- _ ⊨ᵐ me_mem ?H ?y ≈ ds_unit ?Rm /\ _ =>
      destruct (smt_canon _ _ Hgm Hgf _ _ _ _ Hs Hm Hmd) as [Hc HK];
      split; [ exact Hc |]; split; [ exact Hs |]; split; [ exact (smt_of_semK _ _ Hgf _ _ HK) | split; assumption ] end ].
  all: try solve [ split; [ apply rel_modexp_sym; assumption | repeat (split; [ assumption |]); assumption ] ].
  all: try solve [ split; [ eapply rel_modexp_trans; eassumption | repeat (split; [ assumption |]); assumption ] ].
  (** [β]. *)
  all: try solve [
    match goal with |- ?A /\ ?B /\ _ =>
      cut (A /\ B); [ intros (? & ?); repeat (split; [ assumption |]); assumption |];
      eapply k_alias0; eassumption end ].
  all: try solve [
    match goal with |- ?A /\ ?B /\ ?C /\ _ =>
      cut (A /\ B /\ C); [ intros (? & ? & ?); repeat (split; [ assumption |]); assumption |];
      first [ eapply (k_beta_body Hgw _ _ Hgm Hsub Hgf); eassumption
            | eapply (k_beta_alias Hgw _ _ Hgm Hsub Hgf); eassumption ] end ].
  (** A body unit. *)
  all: match goal with |- ?A /\ ?B /\ ?C /\ _ =>
         cut (A /\ B /\ C); [ intros (? & ? & ?); repeat (split; [ assumption |]); assumption |];
         eapply k_unit_body_k; [ eassumption | eapply wf_unit_eq_body; eassumption | eassumption .. ] end.
Qed.
