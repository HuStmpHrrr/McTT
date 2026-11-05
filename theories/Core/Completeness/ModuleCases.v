(** * The Module Rules

    First the rules about units and module expressions at one global context
    [GC] that a global context [Θm ⍮ Ξm] embeds into: the units and module
    expressions are moreover valid in what they denote, read at [Θm ⍮ Ξm]
    ([valid_unit], [valid_modexp]), and the slots of a context with valid
    slots hold valid units ([valid_slots]).  Then the rules themselves, about
    the semantic judgments: each reads its premises at the target of a sound
    embedding and concludes there by the lemma at one global context. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Modules Paths DescTyping LookupSound.
From Mctt.Core.Completeness Require Import ContextCases FunctionCases LetCases LevelCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import
  SubtypingCases PropCases UniverseCases VariableCases LogicalRelation UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness.Inductives Require Import Con.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.Inductives Require Import Elim.
From Mctt.Core.Completeness Require Import IndCases ElimCases.
From Mctt.Core.Completeness.Inductives Require Import Iota.
From Mctt.Core.Completeness Require Import IotaCases.
From Mctt.Core.Completeness.Modules Require Import ModuleVal Values UnitSubst ModexpRel.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Inductives Require Import Decl.
From Mctt.Core.Completeness.Modules Require Import ValidUnit Body Filed Unit Mem Canon App Sel.
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

  #[local] Abbreviation valid_unit := (valid_unit Θm Ξm).
  #[local] Abbreviation valid_slots := (ValidUnit.valid_slots Θm Ξm).

Lemma valid_slots_nil : valid_slots nil.
Proof. unfold ValidUnit.valid_slots; intros Γ1 e U Γ0 H; destruct Γ1; discriminate. Qed.

Lemma valid_slots_tail : forall e Γ, valid_slots (e :: Γ) -> valid_slots Γ.
Proof. unfold ValidUnit.valid_slots; intros * H Γ1 e0 U Γ0 ->; exact (H (e :: Γ1) e0 U Γ0 eq_refl). Qed.

Lemma valid_slots_app_r : forall Ψ Γ, valid_slots (Ψ ++ Γ) -> valid_slots Γ.
Proof. unfold ValidUnit.valid_slots; intros * H Γ1 e0 U Γ0 ->; apply (H (Ψ ++ Γ1)); rewrite app_assoc; reflexivity. Qed.

Lemma valid_slots_cons : forall e Γ, valid_slots Γ -> (forall U, centry_unit e = Some U -> valid_unit Γ (me_lit U)) ->
    valid_slots (e :: Γ).
Proof.
  unfold ValidUnit.valid_slots; intros * H He [| e1 Γ1] e0 U Γ0 Heq Hu; cbn in Heq; injection Heq as -> Heq;
    [ subst; exact (He _ Hu) |].
  exact (H _ _ _ _ Heq Hu).
Qed.

Lemma valid_slots_ass : forall Γ κ A, valid_slots Γ -> valid_slots (Γ ▹{κ} A).
Proof. intros * H; apply valid_slots_cons; [ exact H | discriminate ]. Qed.

Lemma valid_slots_def : forall Γ A M, valid_slots Γ -> valid_slots (Γ ▸ A ≔ M).
Proof. intros * H; apply valid_slots_cons; [ exact H | discriminate ]. Qed.

Lemma valid_slots_mod : forall Γ U, valid_slots Γ -> valid_unit Γ (me_lit U) -> valid_slots (Γ ▹ₘ U).
Proof. intros * H HU; apply valid_slots_cons; [ exact H | intros U0 [= <-]; exact HU ]. Qed.

Lemma valid_slots_dm : forall Γ A M U, valid_slots Γ -> valid_unit Γ (me_lit U) -> valid_slots (Γ ▸ₘ A ≔ M ‖ U).
Proof. intros * H HU; apply valid_slots_cons; [ exact H | intros U0 [= <-]; exact HU ]. Qed.

(** A valid unit stays valid one entry further in. *)
Lemma valid_unit_shift : forall e Γ K, valid_unit Γ K -> ⊨ e :: Γ -> ⊢ Θm ⍮ Ξm ⍮ e :: Γ -> valid_unit (e :: Γ) K[sb_of_wk ↑]ᵐ.
Proof.
  intros * HK HC Hw.
  eapply (valid_unit_gsub Hgw _ _ Hgm Hsub); [ exact HK | exact (gsub_wk _ _ _ (rel_wk_under_ctx_shift HC) HC (rel_ctx_wf_tail HC)) |].
  apply wf_sub_of_wk, wf_wk_shift; exact Hw.
Qed.

(** The unit of a slot of a valid context is valid there. *)
Lemma slot_valid_unit : forall Γ x U, Γ ∋ #x ≔ₘ U -> ⊨ Γ -> ⊢ Θm ⍮ Ξm ⍮ Γ -> valid_slots Γ -> valid_unit Γ (me_lit U).
Proof.
  induction 1 as [U0 Γ0 | U0 A M Γ0 | n U1 Γ0 e Hl IH]; intros HC Hw Hok.
  - pose proof (valid_unit_shift _ _ _ (Hok nil _ U0 Γ0 eq_refl eq_refl : valid_unit Γ0 (me_lit U0)) HC Hw) as H.
    cbn [modexp_sub] in H; rewrite gunit_sub_of_wk in H; exact H.
  - pose proof (valid_unit_shift _ _ _ (Hok nil _ U0 Γ0 eq_refl eq_refl : valid_unit Γ0 (me_lit U0)) HC Hw) as H.
    cbn [modexp_sub] in H; rewrite gunit_sub_of_wk in H; exact H.
  - pose proof (valid_unit_shift _ _ _ (IH (rel_ctx_wf_tail HC) (ctx_decomp_tail Hw) (valid_slots_tail _ _ Hok)) HC Hw) as H.
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
  Hypothesis Hgf : valid_filed_mods Θm Ξm.

  #[local] Abbreviation valid_unit := (valid_unit Θm Ξm).
  #[local] Abbreviation valid_modexp := (valid_modexp Θm Ξm).
  #[local] Abbreviation valid_slots := (ValidUnit.valid_slots Θm Ξm).

(** A slot is valid in what it denotes, as its unit is. *)
Lemma valid_modexp_var : forall Γ x U, Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_var x ≈ me_var x -> ⊨ Γ -> valid_slots Γ -> Γ ∋ #x ≔ₘ U ->
    valid_modexp Γ (me_var x) /\ valid_unit Γ (me_lit U).
Proof.
  intros * Hw HΓ Hok Hl.
  pose proof (slot_valid_unit Hgw _ _ Hgm Hsub _ _ _ Hl HΓ (presup_modexp_eq_ctx Hw) Hok) as HK.
  split; [| exact HK ].
  destruct (me_denotes _ _ _ _ _ Hw) as (R & Rm & Hm & Hmd).
  inversion Hm as [? ? ? ? ? Hq _ | ? ? ? ? ? ? ? ? ? Hq _ | ? ? ? ? Hl' Hu | | | | ? ? ? ? ? ? Hq _]; subst;
    [ cbn in Hq; discriminate | cbn in Hq; discriminate | | cbn in Hq; discriminate ].
  pose proof (ctx_lookup_mod_functional _ _ _ _ Hl Hl') as <-.
  exact (valid_modexp_intro _ _ _ _ _ _ _ _ Hw Hm Hmd (rel_modexp_under_ctx_delta_slot _ _ _ HΓ Hl) HK (mdenote_lit _ _ _ _ _ Hu) Hmd).
Qed.

(** Submodules of equal module expressions valid in what they denote. *)
Lemma valid_modexp_mem : forall Γ H H' y R T R' T', Γ ⊨ᵐ H ≈ H' -> valid_modexp Γ H -> valid_modexp Γ H' ->
    mdenote Θm Ξm Γ (me_mem H y) R -> mdesc_mod_tele R = Some T ->
    mdenote Θm Ξm Γ (me_mem H' y) R' -> mdesc_mod_tele R' = Some T' ->
    Γ ⊨ᵐ me_mem H y ≈ me_mem H' y /\ valid_modexp Γ (me_mem H y) /\ valid_modexp Γ (me_mem H' y).
Proof.
  intros * HH Hs Hs' Hm Ht Hm' Ht'.
  unfold mdesc_mod_tele in Ht, Ht'.
  destruct (mdesc_mod R) as [Rm |] eqn:Hmd; [| discriminate ].
  destruct (mdesc_mod R') as [Rm' |] eqn:Hmd'; [| discriminate ].
  destruct (valid_modexp_sel Hgw _ _ Hgm Hsub Hgf _ _ _ _ _ Hs Hm Hmd) as (Hy & Hsy & HK).
  destruct (valid_modexp_sel Hgw _ _ Hgm Hsub Hgf _ _ _ _ _ Hs' Hm' Hmd') as (_ & Hsy' & _).
  destruct (proj2 (valid_unit_sel_all Hgw _ _ Hgm Hsub Hgf) _ _ Hs _ _ _ Hm Hmd) as [HS _].
  pose proof (valid_sel_resp_l _ _ _ _ _ (rel_modexp_under_ctx_sym HH) HS) as HS'.
  pose proof (rel_sel_of_valid_sel _ _ _ _ _ (rel_modexp_refl_right HH) HS' (valid_unit_rel _ _ Hgf _ _ HK)) as Hy'.
  split; [ exact (rel_modexp_under_ctx_trans Hy (rel_modexp_under_ctx_sym Hy')) | split; assumption ].
Qed.

(** Applications of equal module expressions valid in what they denote. *)
Lemma valid_modexp_app : forall Γ H H' N N' R T B T1 Srt R' T' B' T1' Srt',
    Γ ⊨ᵐ H ≈ H' -> valid_modexp Γ H -> valid_modexp Γ H' ->
    mdenote Θm Ξm Γ H R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) ->
    Θm ⍮ Ξm ⍮ Γ ⊢ B : Srt -> evaluated_sort Srt -> Γ ⊨ B : Srt -> Θm ⍮ Ξm ⍮ Γ ⊢ N : B -> Γ ⊨ N ≈ N' : B ->
    mdenote Θm Ξm Γ H' R' -> mdesc_mod_tele R' = Some T' -> tele_view T' = Some (B', T1') ->
    Θm ⍮ Ξm ⍮ Γ ⊢ B' : Srt' -> evaluated_sort Srt' -> Γ ⊨ B' : Srt' -> Θm ⍮ Ξm ⍮ Γ ⊢ N' : B' -> Γ ⊨ N' : B' ->
    Γ ⊨ᵐ me_app H N ≈ me_app H' N' /\ valid_modexp Γ (me_app H N) /\ valid_modexp Γ (me_app H' N').
Proof.
  intros * HH Hs Hs' Hm Ht Hv HB HS HBs HN HNN Hm' Ht' Hv' HB' HS' HBs' HN' HNs'.
  destruct (rel_param_typed_of_sort _ _ _ HS HBs) as [i HBp].
  destruct (rel_param_typed_of_sort _ _ _ HS' HBs') as [j HBp'].
  destruct (proj2 (valid_unit_app_all Hgw _ _ Hgm Hsub Hgf) _ _ Hs _ _ _ _ _ _ _ Hm Ht Hv HS HB HBp HN (rel_exp_under_ctx_refl_left HNN))
    as [Hl HsN].
  destruct (proj2 (valid_unit_app_all Hgw _ _ Hgm Hsub Hgf) _ _ Hs' _ _ _ _ _ _ _ Hm' Ht' Hv' HS' HB' HBp' HN' HNs') as [_ HsN'].
  split; [ exact (rel_modexp_under_ctx_app _ _ _ _ _ _ HH (rel_type_evaluated_of_evaluated_sort HS HBs) HNN Hl) | split; assumption ].
Qed.

(** [β] for a literal, valid in what it denotes on both sides. *)
Lemma valid_modexp_beta : forall Γ Δ κ X D N,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D) ≈ me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D) ->
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) N ≈ me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) N ->
    valid_unit Γ (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) -> Θm ⍮ Ξm ⍮ Γ ⊢ N : X -> Γ ⊨ N : X ->
    Γ ⊨ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) N ≈ me_lit (gu_mk Δ D)[Id,,N]ᵘ /\
    valid_modexp Γ (me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) N) /\ valid_modexp Γ (me_lit (gu_mk Δ D)[Id,,N]ᵘ).
Proof.
  intros * Hw Hwa HK HNw HN.
  (* the parameter is relevant in the PER model *)
  destruct (valid_unit_lit_params_evaluated _ _ _ _ HK) as (i & _ & HX); cbn [gu_params] in HX.
  pose proof (HX _ _ _ _ eq_refl) as HX0; cbn [List.app] in HX0.
  destruct (me_denotes _ _ _ _ _ Hw) as (R & Rm & Hm & _).
  pose proof (mdenote_lit_inv _ _ _ _ _ Hm) as Hu.
  destruct (valid_unit_lit_app Hgw _ _ Hgm Hsub Hgf _ _ _ _ _ _ _ _ HK Hu HX0 HNw HN) as (_ & R' & Ha & HKN & HK' & Hm' & Hmd').
  split; [ exact HKN |]; split; [| exact (valid_modexp_of_valid_unit _ _ Hgf _ _ HK') ].
  exact (valid_modexp_intro _ _ _ _ _ _ _ _ Hwa (mdenote_app _ _ _ _ _ _ _ Hm Ha) Hmd' HKN HK' Hm' Hmd').
Qed.

Lemma valid_modexp_beta_body : forall Γ Δ κ X Φ N,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵘ gu_open (Δ ++ ce_ass κ X :: nil) Φ ≈ gu_open (Δ ++ ce_ass κ X :: nil) Φ ->
    valid_unit Γ (me_lit (gu_open (Δ ++ ce_ass κ X :: nil) Φ)) -> Θm ⍮ Ξm ⍮ Γ ⊢ N : X -> Γ ⊨ N : X ->
    Γ ⊨ᵐ me_app (me_lit (gu_open (Δ ++ ce_ass κ X :: nil) Φ)) N
      ≈ me_lit (gu_open (tele_sub Δ (Id,,N)) (gmod_sub Φ (sb_qn (List.length Δ) (Id,,N)))) /\
    valid_modexp Γ (me_app (me_lit (gu_open (Δ ++ ce_ass κ X :: nil) Φ)) N) /\
    valid_modexp Γ (me_lit (gu_open (tele_sub Δ (Id,,N)) (gmod_sub Φ (sb_qn (List.length Δ) (Id,,N))))).
Proof.
  intros * HU HK HNw HN.
  pose proof (wf_me_beta_body _ _ _ _ _ _ _ _ HU HNw) as Hb.
  destruct (valid_modexp_beta _ _ _ _ _ _ (wf_me_lit _ _ _ _ _ HU) (wf_me_trans _ _ _ _ _ _ Hb (wf_me_sym _ _ _ _ _ Hb)) HK HNw HN) as (H1 & H2 & H3).
  rewrite gunit_sub_mk in H1, H3; cbn [moddef_sub] in H1, H3.
  split; [ exact H1 | split; assumption ].
Qed.

Lemma valid_modexp_beta_alias : forall Γ Δ κ X E N,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E) ≈ gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E) ->
    valid_unit Γ (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E))) -> Θm ⍮ Ξm ⍮ Γ ⊢ N : X -> Γ ⊨ N : X ->
    Γ ⊨ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E))) N
      ≈ me_lit (gu_mk (tele_sub Δ (Id,,N)) (md_alias E[sb_qn (List.length Δ) (Id,,N)]ᵐ)) /\
    valid_modexp Γ (me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E))) N) /\
    valid_modexp Γ (me_lit (gu_mk (tele_sub Δ (Id,,N)) (md_alias E[sb_qn (List.length Δ) (Id,,N)]ᵐ))).
Proof.
  intros * HU HK HNw HN.
  pose proof (wf_me_beta_alias _ _ _ _ _ _ _ _ HU HNw) as Hb.
  destruct (valid_modexp_beta _ _ _ _ _ _ (wf_me_lit _ _ _ _ _ HU) (wf_me_trans _ _ _ _ _ _ Hb (wf_me_sym _ _ _ _ _ Hb)) HK HNw HN) as (H1 & H2 & H3).
  rewrite gunit_sub_mk in H1, H3; cbn [moddef_sub] in H1, H3.
  split; [ exact H1 | split; assumption ].
Qed.

(** [β] for an alias with no parameter. *)
Lemma valid_modexp_beta_alias0 : forall Γ E, Θm ⍮ Ξm ⍮ Γ ⊢ᵐ E ≈ E -> ⊨ Γ -> Γ ⊨ᵐ E ≈ E -> valid_modexp Γ E ->
    Γ ⊨ᵐ me_lit (gu_mk nil (md_alias E)) ≈ E /\ valid_modexp Γ (me_lit (gu_mk nil (md_alias E))).
Proof.
  intros * Hw HΓ HE Hs.
  pose proof (wf_me_beta_alias0 _ _ _ _ Hw) as Hb.
  pose proof (wf_me_trans _ _ _ _ _ _ Hb (wf_me_sym _ _ _ _ _ Hb)) as Hw'.
  assert (HL : Γ ⊨ᵐ me_lit (gu_mk nil (md_alias E)) ≈ me_lit (gu_mk nil (md_alias E))).
  { apply rel_lit_alias; [ constructor; [ exact HΓ | exact HΓ | exact (rel_ctx_wf_per_ctx HΓ) ] | constructor | constructor
                         | reflexivity | exact HE | exact HE ]. }
  split; [ exact (rel_modexp_under_ctx_beta_alias0 _ _ HE) |].
  apply (valid_modexp_of_valid_unit _ _ Hgf).
  eapply valid_unit_alias; [ exact Hw' | constructor | exists 0; apply rel_params_evaluated_nil | exact HΓ | exact HΓ | exact HL | exact HE | exact Hs ].
Qed.

(** A loaded unit or an open frame, by its path. *)
Lemma valid_modexp_unit : forall Γ fp TΦ, ⊢ Θm ⍮ Ξm ⍮ Γ -> gc_unit Θm Ξm (me_unit fp) = Some TΦ -> ⊨ Γ ->
    Γ ⊨ᵐ me_unit fp ≈ me_unit fp /\ valid_modexp Γ (me_unit fp).
Proof.
  intros * HwΓ Hu HΓ.
  pose proof (wf_me_unit _ _ _ _ _ HwΓ Hu) as Hw.
  destruct TΦ as [T Φ].
  destruct (gc_unit_loc _ _ _ _ _ Hu) as (mp & Hq & Hl).
  pose proof (mod_qname_inv _ _ Hq) as Heq.
  pose proof (gc_loc_of_loc _ _ Hgm _ _ _ Hl) as Hgl.
  assert (Hs : valid_args Γ T nil).
  { apply (mk_valid_args _ _ _ T nil); [ rewrite app_nil_r; reflexivity | reflexivity | constructor | cbn; auto
                                  | intros [|k] ? ? Hk; discriminate | intros [|k] ? Hk; discriminate ]. }
  rewrite Heq in Hw |- *.
  pose proof (valid_unit_filed _ _ _ _ _ _ nil Hw Hgl HΓ Hs) as HK.
  split; [ exact (filed_valid _ _ Hgf _ _ _ _ nil Hgl HΓ Hs (List.Forall_nil _)) | exact (valid_modexp_of_valid_unit _ _ Hgf _ _ HK) ].
Qed.

(** An alias unit. *)
Lemma rel_unit_under_ctx_alias : forall Γ Δ Δ' E E' l,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E') -> Θm ⍮ Ξm ⍮ Γ ⊢ˣ Δ ≈ Δ' ->
    Γ ⊨ˣ Δ ≈ Δ' -> all_assumptions Δ -> all_assumptions Δ' -> rel_params_evaluated Γ Δ l -> rel_params_evaluated Γ Δ' l -> ⊨ Γ ->
    Δ ++ Γ ⊨ᵐ E ≈ E' -> Δ' ++ Γ ⊨ᵐ E' ≈ E' -> valid_modexp (Δ ++ Γ) E -> valid_modexp (Δ' ++ Γ) E' ->
    Γ ⊨ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E') /\
    valid_unit Γ (me_lit (gu_mk Δ (md_alias E))) /\ valid_unit Γ (me_lit (gu_mk Δ' (md_alias E'))).
Proof.
  intros * Hu HΔw HΔ Ha Ha' HΔr HΔr' HΓ HE HE' Hs Hs'.
  pose proof (ext_eq_length _ _ _ _ _ HΔw) as Hl.
  pose proof HΔ as [HΔΓ HΔ'Γ _].
  pose proof (rel_lit_alias _ _ _ _ _ HΔ Ha Ha' Hl HE HE') as HR.
  pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_trans _ _ _ _ _ _ Hu (wf_unit_eq_sym _ _ _ _ _ Hu))) as Hw.
  pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_trans _ _ _ _ _ _ (wf_unit_eq_sym _ _ _ _ _ Hu) Hu)) as Hw'.
  split; [ constructor; [ exact HR | .. ]; apply rel_unit_wf_alias; first [ assumption | exact (rel_modexp_refl_left HE) ] |].
  split; [ eapply valid_unit_alias; [ exact Hw | exact Ha | exists l; exact HΔr | exact HΓ | exact HΔΓ | exact (rel_modexp_refl_left HR)
                            | exact (rel_modexp_refl_left HE) | exact Hs ] |].
  eapply valid_unit_alias; [ exact Hw' | exact Ha' | exists l; exact HΔr' | exact HΓ | exact HΔ'Γ | exact (rel_modexp_refl_right HR)
                           | exact HE' | exact Hs' ].
Qed.

(** An alias of a literal, flattened. *)
Lemma rel_unit_under_ctx_flatten : forall Γ Δ Δ' D l,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ≈ gu_mk (Δ' ++ Δ) D ->
    all_assumptions Δ -> params_evaluated Θm Ξm Γ Δ l -> rel_params_evaluated Γ Δ l ->
    ⊨ Γ -> ⊨ Δ ++ Γ -> valid_unit (Δ ++ Γ) (me_lit (gu_mk Δ' D)) ->
    Γ ⊨ᵘ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ≈ gu_mk (Δ' ++ Δ) D /\
    valid_unit Γ (me_lit (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))) /\ valid_unit Γ (me_lit (gu_mk (Δ' ++ Δ) D)).
Proof.
  intros * Hu Ha HΔw HΔr HΓ HΔΓ HK.
  pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_trans _ _ _ _ _ _ Hu (wf_unit_eq_sym _ _ _ _ _ Hu))) as Hw.
  (* the alias's flag: what the literal denotes can be abstracted over [Δ] *)
  assert (HΔa : forall R, mdenote Θm Ξm (Δ ++ Γ) (me_lit (gu_mk Δ' D)) R -> desc_levels_abstractable Θm Ξm Γ Δ R).
  { pose proof (proj1 (modexp_gen _ _ _ _ _ Hw)) as Hf; cbn [gen_m unit_full] in Hf.
    destruct Hf as [_ _ _ _ _ _ _ lv Rt [Hs1 Hd1 Hn1]].
    intros R HR; destruct lv; [ left; exact (Hs1 eq_refl) | right ].
    rewrite (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ HR _ (Hd1 eq_refl)); exact (Hn1 eq_refl). }
  pose proof (rel_lit_flatten _ _ Hgm Hgf _ _ _ _ _ Ha HΔw HΔr HΔa HK) as HR.
  pose proof (valid_unit_rel _ _ Hgf _ _ HK) as HV.
  pose proof (valid_unit_abs _ _ Hgm Hgf _ _ _ _ HK Ha HΔw HΔr (fun R HR => HΔa R (mdenote_lit _ _ _ _ _ HR))) as HK';
    cbn [gunit_abs] in HK'.
  split; [ constructor; [ exact HR | apply rel_unit_wf_alias; assumption | exact (rel_unit_under_ctx_right _ _ _ (valid_unit_lit_unit Hgw _ _ Hgm Hsub _ _ HK')) ] |].
  split; [| exact HK' ].
  eapply valid_unit_alias; [ exact Hw | exact Ha | exists l; exact HΔr | exact HΓ | exact HΔΓ | exact (rel_modexp_refl_left HR) | exact HV
                   | exact (valid_modexp_of_valid_unit _ _ Hgf _ _ HK) ].
Qed.

(** A body unit. *)
Lemma rel_unit_under_ctx_body : forall Γ Δ Δ' Φ Φ' Φx Φx' l,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' ->
    body_xp Θm Ξm (Δ ++ Γ) Φ Φx -> body_xp Θm Ξm (Δ' ++ Γ) Φ' Φx' ->
    Γ ⊨ˣ Δ ≈ Δ' -> ⊨ Γ ->
    ⊨ (body_ctx Φx ++ Δ) ++ Γ -> valid_slots ((body_ctx Φx ++ Δ) ++ Γ) ->
    ⊨ (body_ctx Φx' ++ Δ') ++ Γ -> valid_slots ((body_ctx Φx' ++ Δ') ++ Γ) ->
    body_sorts_valid Φx (Δ ++ Γ) -> body_sorts_valid Φx' (Δ' ++ Γ) ->
    rel_params_evaluated Γ Δ l -> rel_params_evaluated Γ Δ' l ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
      (exists i, Δ ++ Γ ⊨ A[σ] ≈ A'[σ'] : abs_kind_sort (entry_kind E) Typeω@i) /\
      Δ ++ Γ ⊨ M[σ] ≈ M'[σ'] : A[σ]) ->
    (forall y Φ0 E U Φ0' E' U' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
      Δ ++ Γ ⊨ᵐ me_lit U[σ]ᵘ ≈ me_lit U'[σ']ᵘ) ->
    (forall k Ψo H, nth_error (body_opens Φ Φx) k = Some (Ψo, H) -> Ψo ++ Δ ++ Γ ⊨ᵐ H ≈ H /\ valid_modexp (Ψo ++ Δ ++ Γ) H) ->
    (forall k Ψo H, nth_error (body_opens Φ' Φx') k = Some (Ψo, H) -> Ψo ++ Δ' ++ Γ ⊨ᵐ H ≈ H /\ valid_modexp (Ψo ++ Δ' ++ Γ) H) ->
    all_assumptions Δ -> all_assumptions Δ' -> List.length Δ = List.length Δ' ->
    body_shape Φ Φ' -> body_shape Φx Φx' -> List.NoDup (gm_names Φ) ->
    Γ ⊨ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' /\ valid_unit Γ (me_lit (gu_open Δ Φ)) /\ valid_unit Γ (me_lit (gu_open Δ' Φ')).
Proof.
  intros * Hu Hx Hx' HΔ HΓ HC HokC HC' HokC' Hsv Hsv' HΔr HΔr' HD HU Ho Ho' Ha Ha' Hl Hs Hsxx Hnd.
  rewrite <- app_assoc in HC, HokC, HC', HokC'.
  pose proof (body_shape_l _ _ Hsxx) as Hsx; pose proof (body_shape_r _ _ Hsxx) as Hsx'.
  pose proof (body_shape_l _ _ Hs) as Hsw; pose proof (body_shape_r _ _ Hs) as Hsw'.
  assert (HndX : List.NoDup (gm_names Φx)) by (rewrite (body_xp_names _ _ _ _ _ Hx); exact Hnd).
  assert (HndX' : List.NoDup (gm_names Φx'))
    by (rewrite (body_xp_names _ _ _ _ _ Hx'), <- (body_shape_names _ _ Hs); exact Hnd).
  pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_trans _ _ _ _ _ _ Hu (wf_unit_eq_sym _ _ _ _ _ Hu))) as Hw.
  pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_trans _ _ _ _ _ _ (wf_unit_eq_sym _ _ _ _ _ Hu) Hu)) as Hw'.
  pose proof (body_xp_scoped_of_wf _ _ _ _ _ _ Hw Hx) as Hsc.
  pose proof (body_xp_scoped_of_wf _ _ _ _ _ _ Hw' Hx') as Hsc'.
  pose proof (rel_lit_body _ _ _ _ _ _ _ _ _ HΔ Ha Ha' Hl Hx Hx' Hsxx Hsx Hsx' HndX HndX' HC HC' Hsv Hsv' Hsc Hsc' HD HU) as HR.
  assert (Hslots : forall Φx0 Δ0, valid_slots (body_ctx Φx0 ++ Δ0 ++ Γ) -> gm_nopens Φx0 = 0 ->
             forall y Φ0 E U, gm_prefix_upto Φx0 y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
             valid_unit (body_ctx Φ0 ++ Δ0 ++ Γ) (me_lit U)).
  { intros * Hok Hn * Hp HEu.
    destruct (prefix_body_ctx _ _ _ Hn Hp) as [X HX].
    destruct (body_ctx_unit Φ0 y _ _ HEu) as (e & He & Heu); rewrite He in HX.
    apply (Hok X e U); [ rewrite HX, <- app_assoc; reflexivity | exact Heu ]. }
  split; [ constructor; [ exact HR | | ] |].
  - eapply rel_unit_wf_body; [ exact Ha | exact (body_xp_target Hgw _ _ Hgm Hsub _ _ _ Hx) | exact Hsw | exact Hsx | exact HC | exact Hsv |].
    intros * Hn; exact (proj1 (Ho _ _ _ Hn)).
  - eapply rel_unit_wf_body; [ exact Ha' | exact (body_xp_target Hgw _ _ Hgm Hsub _ _ _ Hx') | exact Hsw' | exact Hsx' | exact HC' | exact Hsv' |].
    intros * Hn; exact (proj1 (Ho' _ _ _ Hn)).
  - split.
    + eapply valid_unit_body; [ exact Hw | exact Hx | exact Ha | exists l; exact HΔr | exact HΓ | exact HC | exact Hsv
                      | exact (Hslots _ _ HokC (body_xp_nopens _ _ _ _ _ Hx)) | exact Hsw | exact Hsx
                      | exact (rel_modexp_refl_left HR) | intros * Hn; exact (proj1 (Ho _ _ _ Hn))
                      | intros * Hn; exact (proj2 (Ho _ _ _ Hn)) ].
    + eapply valid_unit_body; [ exact Hw' | exact Hx' | exact Ha' | exists l; exact HΔr' | exact HΓ | exact HC' | exact Hsv'
                      | exact (Hslots _ _ HokC' (body_xp_nopens _ _ _ _ _ Hx')) | exact Hsw' | exact Hsx'
                      | exact (rel_modexp_refl_right HR) | intros * Hn; exact (proj1 (Ho' _ _ _ Hn))
                      | intros * Hn; exact (proj2 (Ho' _ _ _ Hn)) ].
Qed.

(** A literal and the literal of its expansion evaluate alike: a closure
    stores the expansion ([eval_close_expand_iff]). *)
Lemma eval_me_lit_expand_iff : forall U ρ h,
    ⟦ me_lit (gunit_expand U) ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h <-> ⟦ me_lit U ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h.
Proof. intros [Δ D] ρ h; rewrite gunit_expand_mk, !eval_me_lit_iff; apply eval_close_expand_iff. Qed.

(** A module expression related to a literal is related to the literal of
    its expansion. *)
Lemma rel_modexp_lit_expand : forall Γ H U, Γ ⊨ᵐ H ≈ me_lit U -> Γ ⊨ᵐ H ≈ me_lit (gunit_expand U).
Proof.
  intros * [R HR Hb]; econstructor; [ exact HR |].
  intros * HΓ' * Hσ * Hρ Hev Hev'.
  destruct (Hb _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [h1 h2 h3 h4 E1 E2 E3 E4 Hc].
  apply (mk_rel_modexp h1 h2 h3 h4 E1 E2); [ apply eval_me_lit_expand_iff; exact E3 | | exact Hc ].
  cbn [modexp_sub]; rewrite <- gunit_expand_sub; apply eval_me_lit_expand_iff; exact E4.
Qed.

(** A body unit and its expansion ([wf_unit_eq_expand]): related, and the
    expansion a valid unit, of no open, its own expansion. *)
Lemma rel_unit_under_ctx_expand : forall Γ Δ Φ,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ Φ ->
    Γ ⊨ᵘ gu_open Δ Φ ≈ gu_open Δ Φ -> valid_unit Γ (me_lit (gu_open Δ Φ)) ->
    Γ ⊨ᵘ gu_open Δ Φ ≈ gu_open Δ (gm_expand Φ) /\ valid_unit Γ (me_lit (gu_open Δ Φ)) /\
    valid_unit Γ (me_lit (gu_open Δ (gm_expand Φ))).
Proof.
  intros * Hw [HL Hl _] HK.
  pose proof (wf_unit_eq_expand _ _ _ _ _ Hw) as Hwe.
  pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_trans _ _ _ _ _ _ (wf_unit_eq_sym _ _ _ _ _ Hwe) Hwe)) as Hwx.
  pose proof (rel_modexp_lit_expand _ _ (gu_open Δ Φ) HL) as HLx.
  pose proof (gm_noopen_expand Φ) as Hn.
  assert (Hnone : forall k Ψ H, nth_error (body_opens (gm_expand Φ) (gm_expand Φ)) k = Some (Ψ, H) -> False)
    by (intros k Ψ H Hk; rewrite (body_opens_noopen _ Hn) in Hk; destruct k; discriminate).
  inversion Hl; subst.
  match goal with Hxp : body_xp _ _ _ Φ ?Φx |- _ => pose proof (body_xp_expand _ _ _ _ _ Hxp) as -> end.
  split; [ constructor; [ exact HLx | exact Hl |] |].
  { eapply rel_unit_wf_body; [ eassumption | exact (body_xp_noopen _ _ _ _ Hn) | eassumption | eassumption
                             | eassumption | eassumption |].
    intros * Hk; exfalso; exact (Hnone _ _ _ Hk). }
  split; [ exact HK |].
  inversion HK; subst; [ exfalso; eapply me_apps_qname_not_lit; eassumption |].
  match goal with Hxp : body_xp Θm Ξm _ Φ ?Φx |- _ => pose proof (body_xp_expand _ _ _ _ _ Hxp) as -> end.
  eapply valid_unit_body; [ exact Hwx | exact (body_xp_noopen _ _ _ _ Hn) | eassumption | eassumption | eassumption
                          | eassumption | eassumption | eassumption | eassumption | eassumption
                          | exact (rel_modexp_refl_right HLx) | intros * Hk; exfalso; exact (Hnone _ _ _ Hk)
                          | intros * Hk; exfalso; exact (Hnone _ _ _ Hk) ].
Qed.

End Cases.

(** ** 3. The rules

    Each rule reads its premises at the target of a sound embedding
    ([sem_intro]) and concludes there by its lemma of part 2. *)

#[local] Generalizable All Variables.

(** The slots of each context with valid slots in scope, as [valid_slots]. *)
Ltac add_valid_slots :=
  repeat match goal with
    | H : @valid_ctx ?gc ?T ?X ?G |- _ =>
        lazymatch goal with
        | _ : @valid_slots gc T X G |- _ => fail
        | _ => let Hs := fresh "Hok" in pose proof (proj2 (proj1 (@valid_ctx_iff gc T X G) H)) as Hs
        end
    end.

(** Conclude a judgment about units, or about module expressions, at the
    target from a lemma of part 2 giving the relation and the validity of
    both sides (of the left one only, for a module expression whose right
    side is a part of it). *)
Ltac close_unit lem :=
  lazymatch goal with |- sem_unit_eq_at ?T ?X ?T2 ?X2 ?G ?U ?U' =>
    let Hc := fresh "Hc" in
    assert (Hc : @rel_unit_under_ctx (gc_mk T2 X2) G U U' /\ @valid_unit (gc_mk T2 X2) T X G (me_lit U) /\
                 @valid_unit (gc_mk T2 X2) T X G (me_lit U'))
      by (eapply lem; eassumption);
    destruct Hc as (? & ? & ?); constructor; assumption
  end.

Ltac close_modexp lem :=
  lazymatch goal with |- sem_modexp_eq_at ?T ?X ?T2 ?X2 ?G ?H ?H' =>
    let Hc := fresh "Hc" in
    assert (Hc : @rel_modexp_under_ctx (gc_mk T2 X2) G H H' /\ @valid_modexp (gc_mk T2 X2) T X G H /\
                 @valid_modexp (gc_mk T2 X2) T X G H')
      by (eapply lem; eassumption);
    destruct Hc as (? & ? & ?); constructor; assumption
  end.

Ltac close_modexp_left lem :=
  lazymatch goal with |- sem_modexp_eq_at ?T ?X ?T2 ?X2 ?G ?H ?H' =>
    let Hc := fresh "Hc" in
    assert (Hc : @rel_modexp_under_ctx (gc_mk T2 X2) G H H' /\ @valid_modexp (gc_mk T2 X2) T X G H)
      by (eapply lem; eassumption);
    destruct Hc as (? & ?); constructor; assumption
  end.

(** *** Units *)

(** A parameter of the sort a rule gives it ([parameter_sort]) is a
    parameter type in the PER model ([rel_param_typed]). *)
Lemma rel_param_typed_of_parameter_sort : forall {GC : GCtx} Γ T l S, parameter_sort l S -> Γ ⊨ T : S -> rel_param_typed Γ T l.
Proof. intros * [] H; [ left | right ]; exact H. Qed.

(** A body unit at the target of a sound embedding, from the semantic
    premises of its rule. *)
Lemma rel_unit_under_ctx_body_of_embedding : forall Θ Ξ Θ2 Ξ2 Γ Δ Δ' Φ Φ' Φx Φx' (sort_of : String.string -> typ) l
    (ps : nat -> typ),
    valid_gctx_embedding Θ Ξ Θ2 Ξ2 ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' ->
    body_xp Θ Ξ (Δ ++ Γ) Φ Φx -> body_xp Θ Ξ (Δ' ++ Γ) Φ' Φx' ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ Δ Δ' -> @rel_ctx_wf (gc_mk Θ2 Ξ2) Γ ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ (body_ctx Φx ++ Δ) (body_ctx Φx ++ Δ) ->
    @valid_slots (gc_mk Θ2 Ξ2) Θ Ξ ((body_ctx Φx ++ Δ) ++ Γ) ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ (body_ctx Φx' ++ Δ') (body_ctx Φx' ++ Δ') ->
    @valid_slots (gc_mk Θ2 Ξ2) Θ Ξ ((body_ctx Φx' ++ Δ') ++ Γ) ->
    (forall y Φ0 E A M, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       sort_kind (sort_of y) (entry_kind E)) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ A[σ] ≈ A'[σ'] : sort_of y) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊨ A'[σ'] : sort_of y) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ M[σ] ≈ M'[σ'] : A[σ]) ->
    (forall y Φ0 E U Φ0' E' U' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ᵘ U[σ]ᵘ ≈ U'[σ']ᵘ) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δ ++ Γ ⊨ᵐ H ≈ H) ->
    (forall k Ψ' H', nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> Θ ⍮ Ξ ⍮ Ψ' ++ Δ' ++ Γ ⊨ᵐ H' ≈ H') ->
    all_assumptions Δ -> all_assumptions Δ' -> List.length Δ = List.length Δ' ->
    body_shape Φ Φ' -> body_shape Φx Φx' -> List.NoDup (gm_names Φ) ->
    (forall k, parameter_sort l (ps k)) ->
    (forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊨ T : ps (List.length Δ2)) ->
    (forall Δ1 κ T Δ2, Δ' = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊨ T : ps (List.length Δ2)) ->
    @rel_unit_under_ctx (gc_mk Θ2 Ξ2) Γ (gu_open Δ Φ) (gu_open Δ' Φ') /\
    @valid_unit (gc_mk Θ2 Ξ2) Θ Ξ Γ (me_lit (gu_open Δ Φ)) /\ @valid_unit (gc_mk Θ2 Ξ2) Θ Ξ Γ (me_lit (gu_open Δ' Φ')).
Proof.
  intros * He Hu Hx Hx' HΔ HΓ HC HokC HC' HokC' Htag HA HA' HM HU Ho Ho' Ha Ha' Hl Hs Hsxx Hnd Hps HP HP'.
  pose proof (valid_gctx_embedding_embedding _ _ _ _ He) as Hemb.
  pose proof (gctx_embedding_resolution _ _ _ _ Hemb) as Hsub; pose proof (gctx_embedding_wf _ _ _ _ Hemb) as Hgw.
  change (⊢ᵍ @gc_deps (gc_mk Θ2 Ξ2) ⍮ @gc_stack (gc_mk Θ2 Ξ2)) in Hgw.
  change (gc_sub Θ Ξ (@gc_deps (gc_mk Θ2 Ξ2)) (@gc_stack (gc_mk Θ2 Ξ2))) in Hsub.
  set (GC := gc_mk Θ2 Ξ2) in *.
  pose proof (body_xp_nopens _ _ _ _ _ Hx) as Hn; pose proof (body_xp_nopens _ _ _ _ _ Hx') as Hn'.
  pose proof (body_shape_l _ _ Hsxx) as Hsx; pose proof (body_shape_r _ _ Hsxx) as Hsx'.
  assert (HndX : List.NoDup (gm_names Φx)) by (rewrite (body_xp_names _ _ _ _ _ Hx); exact Hnd).
  assert (HndX' : List.NoDup (gm_names Φx'))
    by (rewrite (body_xp_names _ _ _ _ _ Hx'), <- (body_shape_names _ _ Hs); exact Hnd).
  pose proof (rel_ext_under_ctx_left _ _ _ HC) as HCl; rewrite <- app_assoc in HCl.
  pose proof (rel_ext_under_ctx_left _ _ _ HC') as HCl'; rewrite <- app_assoc in HCl'.
  (* the partner of an entry on the other side, with its term part and its filling *)
  assert (Hpart : forall Φa Φb y Φ0 E A M, body_shape Φa Φb -> gm_nopens Φb = 0 ->
            gm_prefix_upto Φa y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
            exists Φ0' E' A' M' σ', gm_prefix_upto Φb y = Some (gm_ext Φ0' y E') /\ entry_tm E' = Some (A', M') /\
              gm_fill Φ0' = Some σ' /\ entry_kind E' = entry_kind E).
  { intros * Hab Hnb Hp HE.
    destruct (shape_prefix _ _ _ _ _ Hab Hp) as (Φ0' & E' & Hp' & Hsh0 & HsE).
    destruct (entry_shape_tm _ _ _ _ HsE HE) as (A' & M' & HE').
    pose proof (prefix_nopens _ _ _ Hnb Hp') as Hn0'; cbn in Hn0'.
    destruct (gm_fill Φ0') as [σ' |] eqn:Hf'; [| exfalso; exact (proj1 (body_shape_fill _ _ Hn0' (body_shape_r _ _ Hsh0)) Hf') ].
    exists Φ0', E', A', M', σ'; repeat split; try assumption.
    symmetry; exact (entry_shape_kind _ _ HsE). }
  (* the types of the entries, filled in, at their tagged sorts *)
  assert (HD : forall y Φ0 E A M Φ0' E' A' M' σ σ',
             gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
             gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
             gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
             exists i, Δ ++ Γ ⊨ A[σ] ≈ A'[σ'] : abs_kind_sort (entry_kind E) Typeω@i).
  { intros * Hp HE Hp' HE' Hf Hf'.
    destruct (sort_kind_abs_kind_sort_inv _ _ (Htag _ _ _ _ _ Hp HE)) as [i Hi]; exists i; rewrite <- Hi.
    exact (sem_exp_eq_at_rel (HA _ _ _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hf Hf' _ _ He)). }
  assert (Hsv : body_sorts_valid Φx (Δ ++ Γ)).
  { apply (body_sorts_valid_of_fill _ _ Hn Hsx HndX HCl (body_xp_scoped_of_wf _ _ _ _ _ _
             (wf_me_lit _ _ _ _ _ (wf_unit_eq_trans _ _ _ _ _ _ Hu (wf_unit_eq_sym _ _ _ _ _ Hu))) Hx)).
    intros * Hp HE Hf.
    destruct (Hpart _ _ _ _ _ _ _ Hsxx Hn' Hp HE) as (Φ0' & E' & A' & M' & σ' & Hp' & HE' & Hf' & _).
    destruct (HD _ _ _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hf Hf') as (i & Hi); exists i; exact (rel_exp_under_ctx_refl_left Hi). }
  assert (Hsv' : body_sorts_valid Φx' (Δ' ++ Γ)).
  { apply (body_sorts_valid_of_fill _ _ Hn' Hsx' HndX' HCl' (body_xp_scoped_of_wf _ _ _ _ _ _
             (wf_me_lit _ _ _ _ _ (wf_unit_eq_trans _ _ _ _ _ _ (wf_unit_eq_sym _ _ _ _ _ Hu) Hu)) Hx')).
    intros * Hp' HE' Hf'.
    destruct (Hpart _ _ _ _ _ _ _ (body_shape_sym _ _ Hsxx) Hn Hp' HE') as (Φl & El & Al & Ml & σl & Hp & HE & Hf & Hr).
    destruct (sort_kind_abs_kind_sort_inv _ _ (Htag _ _ _ _ _ Hp HE)) as [i Hi]; exists i; rewrite <- Hr, <- Hi.
    exact (sem_exp_eq_at_rel (HA' _ _ _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hf Hf' _ _ He)). }
  apply (@rel_unit_under_ctx_body GC Hgw _ _ (valid_gctx_embedding_wf _ _ _ _ He) Hsub
           _ _ _ _ _ _ _ l Hu Hx Hx' HΔ HΓ (rel_ext_under_ctx_left _ _ _ HC) HokC (rel_ext_under_ctx_left _ _ _ HC') HokC'
           Hsv Hsv'); try assumption.
  - intros Δ1 κ T Δ2 HE0; exact (rel_param_typed_of_parameter_sort _ _ _ _ (Hps _) (sem_exp_eq_at_rel (HP _ _ _ _ HE0 _ _ He))).
  - intros Δ1 κ T Δ2 HE0; exact (rel_param_typed_of_parameter_sort _ _ _ _ (Hps _) (sem_exp_eq_at_rel (HP' _ _ _ _ HE0 _ _ He))).
  - intros * Hp HE Hp' HE' Hf Hf'; split; [ exact (HD _ _ _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hf Hf') |].
    exact (sem_exp_eq_at_rel (HM _ _ _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hf Hf' _ _ He)).
  - intros * Hp HE Hp' HE' Hf Hf'; exact (rel_unit_under_ctx_lit _ _ _ (sem_unit_eq_at_rel (HU _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hf Hf' _ _ He))).
  - intros * Hk; destruct (Ho _ _ _ Hk _ _ He) as [_ HV HS _]; exact (conj HV HS).
  - intros * Hk; destruct (Ho' _ _ _ Hk _ _ He) as [_ HV HS _]; exact (conj HV HS).
Qed.

Lemma sem_unit_eq_body :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' ->
     body_xp Θ Ξ (Δ ++ Γ) Φ Φx ->
     body_xp Θ Ξ (Δ' ++ Γ) Φ' Φx' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Δ ≈ Δ' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ body_ctx Φx ++ Δ ≈ body_ctx Φx ++ Δ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ body_ctx Φx' ++ Δ' ≈ body_ctx Φx' ++ Δ' ->
     (forall y Φ0 E A M, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        sort_kind (entry_sort y) (entry_kind E)) ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ A[σ] ≈ A'[σ'] : entry_sort y) ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊨ A'[σ'] : entry_sort y) ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ M[σ] ≈ M'[σ'] : A[σ]) ->
     (forall y Φ0 E U Φ0' E' U' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ᵘ U[σ]ᵘ ≈ U'[σ']ᵘ) ->
     (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δ ++ Γ ⊨ᵐ H ≈ H) ->
     (forall k Ψ' H', nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> Θ ⍮ Ξ ⍮ Ψ' ++ Δ' ++ Γ ⊨ᵐ H' ≈ H') ->
     all_assumptions Δ ->
     all_assumptions Δ' ->
     List.length Δ = List.length Δ' ->
     body_shape Φ Φ' ->
     body_shape Φx Φx' ->
     List.NoDup (gm_names Φ) ->
     (forall k, parameter_sort param_level (param_sorts k)) ->
     (forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊨ T : param_sorts (List.length Δ2)) ->
     (forall Δ1 κ T Δ2, Δ' = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊨ T : param_sorts (List.length Δ2)) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' ).
Proof.
  intros * Hu Hx Hx' HΔ HC HC' Htag HA HA' HM HU Ho Ho' Ha Ha' Hl Hs Hsxx Hnd Hps HP HP' Θ2 Ξ2 He.
  destruct (HΔ _ _ He) as [HKctx HΔr _ _].
  destruct (HC _ _ He) as [_ HCr HKC _].
  destruct (HC' _ _ He) as [_ HCr' HKC' _].
  destruct (rel_unit_under_ctx_body_of_embedding _ _ _ _ _ _ _ _ _ _ _ _ _ _ He Hu Hx Hx' HΔr (valid_ctx_rel_ctx_wf HKctx)
              HCr (proj2 (proj1 (valid_ctx_iff _ _ _) HKC)) HCr' (proj2 (proj1 (valid_ctx_iff _ _ _) HKC'))
              Htag HA HA' HM HU Ho Ho' Ha Ha' Hl Hs Hsxx Hnd Hps HP HP') as (HR & HV & HV').
  constructor; assumption.
Qed.

Lemma sem_unit_eq_alias :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E') ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Δ ≈ Δ' ->
     all_assumptions Δ ->
     all_assumptions Δ' ->
     Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ᵐ E ≈ E' ->
     Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊨ᵐ E' ≈ E' ->
     (forall k, parameter_sort param_level (param_sorts k)) ->
     (forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊨ T : param_sorts (List.length Δ2)) ->
     (forall Δ1 κ T Δ2, Δ' = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊨ T : param_sorts (List.length Δ2)) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E') ).
Proof.
  intros * Hu HΔw HΔ Ha Ha' HE HE' Hps HP HP'; sem_intro0.
  match goal with He : valid_gctx_embedding _ _ _ _ |- _ =>
    assert (HPr : rel_params_evaluated Γ Δ param_level)
      by (intros ? ? ? ? HE0; exact (rel_param_typed_of_parameter_sort _ _ _ _ (Hps _) (sem_exp_eq_at_rel (HP _ _ _ _ HE0 _ _ He))));
    assert (HPr' : rel_params_evaluated Γ Δ' param_level)
      by (intros ? ? ? ? HE0; exact (rel_param_typed_of_parameter_sort _ _ _ _ (Hps _) (sem_exp_eq_at_rel (HP' _ _ _ _ HE0 _ _ He))))
  end.
  close_unit rel_unit_under_ctx_alias.
Qed.

Lemma sem_unit_eq_flatten :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ≈ gu_mk (Δ' ++ Δ) D ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ Δ ≈ Δ ->
     all_assumptions Δ ->
     Θ ⍮ Ξ ⍮ Δ ++ Γ ⊨ᵘ gu_mk Δ' D ≈ gu_mk Δ' D ->
     (forall k, parameter_sort param_level (param_sorts k)) ->
     (forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ T : param_sorts (List.length Δ2)) ->
     (forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊨ T : param_sorts (List.length Δ2)) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ≈ gu_mk (Δ' ++ Δ) D ).
Proof.
  intros * Hu HΔ Ha HU Hps HPw HP; sem_intro0.
  pose proof (params_evaluated_of_sorts _ _ _ _ _ _ Hps HPw) as HPw'.
  match goal with He : valid_gctx_embedding _ _ _ _ |- _ =>
    assert (HPr : rel_params_evaluated Γ Δ param_level)
      by (intros ? ? ? ? HE0; exact (rel_param_typed_of_parameter_sort _ _ _ _ (Hps _) (sem_exp_eq_at_rel (HP _ _ _ _ HE0 _ _ He))))
  end.
  close_unit rel_unit_under_ctx_flatten.
Qed.

(** A body unit is equivalent to its expansion ([wf_unit_eq_expand]). *)
Lemma sem_unit_eq_expand :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ Φ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_open Δ Φ ≈ gu_open Δ Φ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_open Δ Φ ≈ gu_open Δ (gm_expand Φ) ).
Proof.
  intros * Hw HU; sem_intro0.
  close_unit rel_unit_under_ctx_expand.
Qed.

Lemma sem_unit_eq_sym :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U' ≈ U ).
Proof.
  intros * HU; sem_intro; try assumption.
  destruct HU as [HL Hl Hr]; constructor; [ apply rel_modexp_under_ctx_sym; exact HL | assumption .. ].
Qed.

Lemma sem_unit_eq_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U' ≈ U'' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U'' ).
Proof.
  intros * HU HU'; sem_intro; try assumption.
  destruct HU as [HL Hl _]; destruct HU' as [HL' _ Hr'].
  constructor; [ eapply rel_modexp_under_ctx_trans; eassumption | assumption .. ].
Qed.

(** *** Module expressions *)

Lemma sem_me_unit :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ->
     gc_unit Θ Ξ (me_unit fp) = Some TΦ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_unit fp ≈ me_unit fp ).
Proof. intros; sem_intro0; close_modexp_left valid_modexp_unit. Qed.

Lemma sem_me_var :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ₘ U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_var x ≈ me_var x ).
Proof.
  intros * Hw HΓ Hl; sem_intro; add_valid_slots;
    pose proof (valid_modexp_var Hgw _ _ Hgm Hsub _ _ _ ltac:(eapply wf_me_var; eassumption) HΓ Hok Hl) as [Hs HK];
    [ assumption | eapply rel_modexp_under_ctx_var; eassumption | exact Hs | exact Hs ].
Qed.

Lemma sem_me_lit :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_lit U ≈ me_lit U' ).
Proof.
  intros * HU; sem_intro; [ assumption | exact (rel_unit_under_ctx_lit _ _ _ HU) | apply (valid_modexp_of_valid_unit _ _ Hgf); assumption .. ].
Qed.

Lemma sem_me_mem :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H' ->
     mdenote Θ Ξ Γ (me_mem H y) R ->
     mdesc_mod_tele R = Some T ->
     mdenote Θ Ξ Γ (me_mem H' y) R' ->
     mdesc_mod_tele R' = Some T' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_mem H y ≈ me_mem H' y ).
Proof. intros; sem_intro0; close_modexp valid_modexp_mem. Qed.

Lemma sem_me_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H' ->
     mdenote Θ Ξ Γ H R ->
     mdesc_mod_tele R = Some T ->
     tele_view T = Some (B, T1) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ B : Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ B : Srt ->
     evaluated_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N ≈ N' : B ->
     mdenote Θ Ξ Γ H' R' ->
     mdesc_mod_tele R' = Some T' ->
     tele_view T' = Some (B', T1') ->
     Θ ⍮ Ξ ⍮ Γ ⊢ B' : Srt' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ B' : Srt' ->
     evaluated_sort Srt' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N' : B' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N' : B' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_app H N ≈ me_app H' N' ).
Proof. intros; sem_intro0; close_modexp valid_modexp_app. Qed.

Lemma sem_me_delta_slot :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ₘ U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_var x ≈ me_lit U ).
Proof.
  intros * Hw HΓ Hl; sem_intro; add_valid_slots;
    pose proof (valid_modexp_var Hgw _ _ Hgm Hsub _ _ _ ltac:(eapply wf_me_var; eassumption) HΓ Hok Hl) as [Hs HK];
    [ assumption | eapply rel_modexp_under_ctx_delta_slot; eassumption | exact Hs
    | exact (valid_modexp_of_valid_unit _ _ Hgf _ _ HK) ].
Qed.

Lemma sem_me_delta_sel :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_mem H y ≈ me_mem H y ->
     mdenote Θ Ξ Γ (me_mem H y) R ->
     mdesc_mod R = Some Rm ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_mem H y ≈ mdesc_unit Rm ).
Proof.
  intros * HH Hm Hmd; sem_intro; try assumption;
    assert (Hc : Γ ⊨ᵐ me_mem H y ≈ mdesc_unit Rm /\ valid_unit Θ Ξ Γ (mdesc_unit Rm))
      by (eapply valid_modexp_canon; eassumption).
  - exact (proj1 Hc).
  - exact (valid_modexp_of_valid_unit _ _ Hgf _ _ (proj2 Hc)).
Qed.

Lemma sem_me_beta_body :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass κ X :: nil) (md_body sm_open Φ) ≈ gu_mk (Δ ++ ce_ass κ X :: nil) (md_body sm_open Φ) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_mk (Δ ++ ce_ass κ X :: nil) (md_body sm_open Φ) ≈ gu_mk (Δ ++ ce_ass κ X :: nil) (md_body sm_open Φ) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : X ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) (md_body sm_open Φ))) N
       ≈ me_lit (gu_mk (tele_sub Δ (Id,,N)) (md_body sm_open (gmod_sub Φ (sb_qn (length Δ) (Id,,N))))) ).
Proof. intros; sem_intro0; close_modexp valid_modexp_beta_body. Qed.

Lemma sem_me_beta_alias :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E) ≈ gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E) ≈ gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : X ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E))) N
       ≈ me_lit (gu_mk (tele_sub Δ (Id,,N)) (md_alias E[sb_qn (length Δ) (Id,,N)]ᵐ)) ).
Proof. intros; sem_intro0; close_modexp valid_modexp_beta_alias. Qed.

Lemma sem_me_beta_alias0 :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ E ≈ E ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵐ me_lit (gu_mk nil (md_alias E)) ≈ E ).
Proof. intros; sem_intro0; close_modexp_left valid_modexp_beta_alias0. Qed.

(** *** Members *)

Lemma sem_mem :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     mdesc_type R = Some A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     (forall M, mdesc_reduct R = Some M -> Θ ⍮ Ξ ⍮ Γ ⊨ M : A) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_mem H x : A ).
Proof.
  intros * HH Hm Ht _ _ _; sem_intro; [ assumption |].
  assert (Hsm : valid_mem Γ H x A (mdesc_reduct R)) by (eapply (proj2 (valid_unit_mem_all _ _ Hgm Hgf)); eassumption).
  exact (rel_mem_of_valid_mem _ _ _ _ _ _ HH Hsm).
Qed.

Lemma sem_exp_eq_mem_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H' ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     mdesc_type R = Some A ->
     mdenote Θ Ξ Γ (me_mem H' x) R' ->
     mdesc_type R' = Some A' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_mem H' x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_mem H x ≈ a_mem H' x : A ).
Proof.
  intros * HH Hm Ht Hm' Ht' _; sem_intro; [ assumption |].
  assert (Hsm : valid_mem Γ H x A (mdesc_reduct R)) by (eapply (proj2 (valid_unit_mem_all _ _ Hgm Hgf)); eassumption).
  apply rel_exp_under_ctx_sym.
  exact (rel_mem_of_valid_mem _ _ _ _ _ _ (rel_modexp_under_ctx_sym HH) Hsm).
Qed.

Lemma sem_exp_eq_mem_delta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     mdesc_type R = Some A ->
     mdesc_reduct R = Some M ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_mem H x ≈ M : A ).
Proof.
  intros * HH Hm Ht Hr; sem_intro; [ assumption |].
  assert (Hsm : valid_mem Γ H x A (mdesc_reduct R)) by (eapply (proj2 (valid_unit_mem_all _ _ Hgm Hgf)); eassumption).
  rewrite Hr in Hsm.
  exact (rel_mem_red_of_valid_mem _ _ _ _ _ _ HH Hsm).
Qed.

