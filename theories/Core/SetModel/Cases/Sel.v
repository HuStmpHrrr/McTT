(** * Submodules of Valid Units

    A submodule a valid unit, or a module expression valid in what it
    denotes, has by lookup is the unit its module part stands for, which is
    valid, of the same modules and proofness ([set_valid_unit_sel_all]): a
    body's submodule is its entry's unit, filled in and abstracted over the
    parameters; a filed module's, the filed submodule or the alias stored,
    at the arguments. *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Respects Substitution JudgmentSubstitution.
From Mctt.Core.SetModel.Interpretation.Global Require Import Model.
From Mctt.Core.SetModel.Cases Require Import ValidUnit MemberTypes ModuleCases Unit Canon App.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas DescTyping LookupSound Presup.
From Mctt.Core.Completeness.Modules Require Import ValidUnit Mem.
From Mctt.Core.Completeness.Modules Require Sel.
Import ListNotations.

Section Sel.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.
  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).
  (** The global context is well formed *)
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  (** The valuation models the global context *)
  Hypothesis Hok : set_gctx_ok T γ.

(** ** The Proofness of a Body's Submodules *)

(** The slots a body of definitions and modules gives are those its
    filling reads. *)
Lemma body_slot_proofs_fill : forall Φ σ κs, gm_fill Φ = Some σ ->
    slot_proofs_eq (body_slot_proofs γ κs Φ) (fun s => modexp_member_proofs γ κs (sentry_modexp (σ s))).
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its Φg _]; intros σ κs Hf; cbn in Hf.
  - injection Hf as <-. intros s ys x. reflexivity.
  - destruct E as [b pv r A [M |] | pv U | | pv A M U |]; try discriminate;
      destruct (gm_fill Φ) as [σ0 |] eqn:Hf0; cbn in Hf; try discriminate; injection Hf as <-;
      pose proof (IH _ κs eq_refl) as IHσ; intros [| s] ys x; cbn [body_slot_proofs push_slot_proofs sb_extend];
      try exact (IHσ s ys x).
    + reflexivity.
    + cbn [gentry_slot_proofs sentry_modexp modexp_member_proofs]. symmetry.
      apply (proj2 (unit_member_proofs_sub_all γ)). exact IHσ.
    + cbn [gentry_slot_proofs sentry_modexp modexp_member_proofs]. symmetry.
      apply (proj2 (unit_member_proofs_sub_all γ)). exact IHσ.
  - discriminate.
Qed.

(** Whether a member of a body's submodule is a proof is read at the last
    entry so named. *)
Lemma body_member_lookup_chain_prefix : forall κs Φ y Φ' E ys x, gm_noopen Φ -> gm_prefix_upto Φ y = Some (gm_ext Φ' y E) ->
    body_member_lookup γ κs Φ (y :: ys) x = Some (gentry_slot_proofs γ (body_slot_proofs γ κs Φ') E ys x).
Proof.
  intros κs Φ. revert κs. induction Φ as [| Φ IH z E0 | Φ IH H its Φg _]; intros κs y Φ' E ys x Hn Hp;
    cbn [gm_prefix_upto gm_noopen body_member_lookup chain_key] in Hp, Hn |- *; [discriminate | | contradiction].
  destruct (String.eqb_spec y z) as [-> | _]; [injection Hp as <- <-; reflexivity | exact (IH _ _ _ _ _ _ Hn Hp)].
Qed.

(** The filling of a body gives coherent slots of its context. *)
Lemma set_sub_slots_coherent_fill : forall Φ D σ, gm_fill Φ = Some σ -> set_sub_slots_coherent γ (body_ctx Φ ++ D) D σ.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its Φg _]; intros D σ Hf κs Hκ; cbn in Hf.
  - injection Hf as <-. cbn [body_ctx List.app].
    eapply set_slots_coherent_resp with (κs := κs); [intros s ys x; reflexivity | exact Hκ].
  - destruct E as [b pv r A [M |] | pv U | | pv A M U |]; try discriminate;
      destruct (gm_fill Φ) as [σ0 |] eqn:Hf0; cbn in Hf; try discriminate; injection Hf as <-;
      cbn [body_ctx List.app set_slots_coherent]; (split; [exact (IH _ _ eq_refl _ Hκ) |]);
      intros U0 HU0 ys x; cbn in HU0; try discriminate; injection HU0 as <-;
      cbn [sb_extend sentry_modexp modexp_member_proofs];
      apply (proj2 (unit_member_proofs_sub_all γ)); intros s ys' x'; reflexivity.
  - discriminate.
Qed.

(** ** Selection Over Parameters *)

(** Over assumptions read from an environment, a submodule of one unit's
    value is another's value, when it is so of what is left at every
    environment past them. *)
Lemma set_unit_params_sel : forall L Γ ρ P1 P2 D1 D2 m1 m2 y, all_assumptions L -> set_env_in T γ Γ ρ ->
    set_interp_unit_params T γ Γ ρ P1 L D1 m1 -> set_interp_unit_params T γ Γ ρ P2 L D2 m2 ->
    (forall ys x, P1 (y :: ys) x = P2 ys x) ->
    (forall ρ' n1 n2, set_env_in T γ (List.rev L ++ Γ) ρ' ->
       set_interp_moddef T γ (List.rev L ++ Γ) ρ' D1 n1 -> set_interp_moddef T γ (List.rev L ++ Γ) ρ' D2 n2 ->
       set_module_eq γ (select_module γ n1 y) n2) ->
    set_module_eq γ (select_module γ m1 y) m2.
Proof.
  induction L as [| e L IH]; intros Γ ρ P1 P2 D1 D2 m1 m2 y HL Hρ H1 H2 EP Hbase.
  - inversion H1; subst. inversion H2; subst. apply (Hbase ρ); assumption.
  - inversion HL as [| ? ? (κ & A & ->) HL']; subst.
    inversion H1 as [| ? ? ? ? ? ? ? a1 f1 Hc HA1 Hf1 | | |]; subst.
    inversion H2 as [| ? ? ? ? ? ? ? a2 f2 _ HA2 Hf2 | | |]; subst.
    pose proof (set_env_rel_eq T γ _ _ _ Hρ) as Eρ.
    pose proof (set_interp_functional T γ Hfn Hmods _ _ _ _ HA1 _ _ Eρ HA2) as Ea.
    cbn [select_module]. apply set_module_eq_params; [exact (code_carrier_resp _ _ Ea) | exact EP |]. intros x x' Hx Exx'.
    assert (Hx2 : forall z, set_eq x z -> set_mem z (code_carrier a2))
      by (intros z Ez; eapply set_mem_eq_l; [exact Ez |]; eapply set_mem_eq_r; [apply code_carrier_resp; exact Ea | exact Hx]).
    pose proof (set_env_in_extend_ass T γ _ _ κ _ _ _ Hρ HA1 Hx) as Hρx.
    assert (E1 : set_module_eq γ (select_module γ (f1 x) y) (f2 x)).
    { apply (IH _ _ _ _ _ _ _ _ _ HL' Hρx (Hf1 _ Hx) (Hf2 _ (Hx2 _ (set_eq_refl x))) EP).
      intros ρ' n1 n2 Hρ' Hn1 Hn2. cbn [List.rev] in Hbase. rewrite <- List.app_assoc in Hbase. exact (Hbase ρ' n1 n2 Hρ' Hn1 Hn2). }
    eapply set_module_eq_trans; [exact E1 |].
    assert (Eρx : set_env_eq γ (set_env_extend ρ (set_entry_term κ x)) (set_env_extend ρ (set_entry_term κ x')))
      by (intros [| s]; [constructor; exact Exx' | apply Eρ]).
    exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (set_interp_functional_all T γ Hfn Hmods)))))) _ _ _ _ _ _
             (Hf2 _ (Hx2 _ (set_eq_refl x))) _ P2 _ Eρx ltac:(intros; reflexivity) (Hf2 _ (Hx2 _ Exx'))).
Qed.

(** ** Canonical Units Moved *)

(** A module expression of a canonical unit, moved along a substitution
    sending environments and coherent slots, has the canonical unit moved. *)
Lemma set_canon_moved : forall Δ Γ σ Fσ K Rm, set_canon_with T γ Δ K Rm -> set_moves_with T γ nil Δ Γ σ Fσ ->
    set_sub_slots_coherent γ Δ Γ σ -> set_canon_with T γ Γ (modexp_sub K σ) (mdesc_sub Rm σ).
Proof.
  intros * [Hr Hv Hp] Hs Hκ. constructor; rewrite mdesc_unit_sub.
  - pose proof (set_modexp_rel_moved T γ Hfn Hmods _ _ _ _ _ _ _ Hs Hr) as H. cbn [tele_sub List.app List.length sb_qn] in H. exact H.
  - exact (proj1 (set_valid_unit_modexp_moved T γ Hfn Hmods Hgw) _ _ Hv _ _ _ Hs Hκ).
  - intros κs Hκs ys x.
    rewrite !(proj1 (unit_member_proofs_sub_all γ) _ κs σ (fun s => modexp_member_proofs γ κs (sentry_modexp (σ s))))
      by (intros s ys' x'; reflexivity).
    exact (Hp _ (Hκ _ Hκs) ys x).
Qed.

(** ** A Body's Submodules *)

(** The submodule of a body's value at an environment is the module of its
    entry's unit, filled in, which is its canonical unit's. *)
Lemma set_body_sel_base : forall D Φ y Φ' E U σ RU ρ n m, gm_nopens (gm_expand Φ) = 0 ->
    set_ctx T γ D -> set_ctx T γ (body_ctx (gm_expand Φ) ++ D) ->
    gm_prefix_upto (gm_expand Φ) y = Some (gm_ext Φ' y E) -> entry_unit E = Some U -> gm_fill Φ' = Some σ ->
    set_canon_with T γ (body_ctx Φ' ++ D) (me_lit U) RU ->
    set_env_in T γ D ρ -> set_interp_moddef T γ D ρ (md_body sm_open Φ) n ->
    set_interp_modexp T γ D ρ (mdesc_unit (mdesc_sub RU σ)) m -> set_module_eq γ (select_module γ n y) m.
Proof.
  intros * Hn HD HC Hp HEu Hf HU Hρ Hm Hm'.
  inversion Hm as [? ? ? ? ms ρo HΦ |]; subst.
  destruct (set_interp_gmod_prefix T γ _ _ _ _ _ HΦ _ _ _ Hp) as (ms' & ρ0 & e & Hc0 & Hm0 & He & Hl).
  cbn [select_module]. rewrite Hl.
  destruct (prefix_body_ctx _ _ _ Hn Hp) as (X & HX). rewrite HX, <- List.app_assoc in HC.
  pose proof (set_ctx_app_r T γ _ _ HC) as HC1.
  assert (HC0 : set_ctx T γ (body_ctx Φ' ++ D))
    by (destruct E as [? ? ? ? [] | | | |]; cbn [body_ctx List.app set_ctx] in HC1; exact (proj1 HC1)).
  destruct (set_gsub_fill T γ Hfn Hmods _ _ _ Hf HD HC0 Hc0) as (Fσ & Hs).
  destruct (set_canon_moved _ _ _ _ _ _ HU Hs (set_sub_slots_coherent_fill _ _ _ Hf)) as [(F1 & F2 & [HF1 HF2 E12]) _ _].
  assert (Hsub : sub_setting T γ (body_ctx Φ' ++ D) ρ0 nil (body_ctx Φ' ++ D) D σ ρ ρ).
  { constructor; [reflexivity | exact (wf_gm_fill _ _ _ _ _ Hc0 Hf) | intros k Hk; cbn in Hk; lia
                 | intros; reflexivity | intros k; exact (set_interp_gmod_fill T γ _ _ _ _ _ Hm0 _ Hf k)]. }
  assert (Hmu : forall mu, set_interp_gunit T γ (body_ctx Φ' ++ D) ρ0 U mu -> set_module_eq γ mu m).
  { intros mu Hmu.
    pose proof (proj1 (proj2 (proj2 (proj2 (set_interp_sub_all T γ)))) _ _ (me_lit U) _ ltac:(constructor; exact Hmu) nil _ _ _ _ _
                  Hc0 Hsub) as HUσ.
    eapply set_module_eq_trans; [exact (set_modexp_denotes_unique _ _ _ _ _ HF1 _ _ _ Hρ HUσ) |].
    eapply set_module_eq_trans; [exact (E12 _ Hρ) |].
    exact (set_module_eq_sym _ _ (set_modexp_denotes_unique _ _ _ _ _ HF2 _ _ _ Hρ Hm')). }
  destruct E as [b pv r A om | pv U0 | | pv A M U0 |]; cbn in HEu; try discriminate; injection HEu as <-;
    inversion He; subst; cbn [set_entry_module_part]; apply Hmu; assumption.
Qed.

(** [set_sel_valid_with Γ H y Rm]: the submodule [y] of [H], of the module
    part [Rm], is the unit [Rm] stands for: equal modules, the unit valid,
    and the same proofness. *)
Record set_sel_valid_with (Γ : ctx) (H : modexp) (y : string) (Rm : mdesc) : Prop :=
  { (** Its modules are the unit's *)
    set_sel_rel : set_modexp_rel T γ Γ (me_mem H y) (mdesc_unit Rm)
    (** The unit is valid *)
  ; set_sel_unit_valid : set_valid_unit T γ Γ (mdesc_unit Rm)
    (** Its proofness is the unit's *)
  ; set_sel_proofs : forall κs, set_slots_coherent γ Γ κs -> forall ys x,
      modexp_member_proofs γ κs H (y :: ys) x = modexp_member_proofs γ κs (mdesc_unit Rm) ys x }.

(** The proofness of a body's submodule is its entry's unit's, filled in,
    at the slots past the parameters. *)
Lemma body_sel_proofs : forall κs Δ Φ y Φ' E U σ ys x, gm_noopen (gm_expand Φ) ->
    gm_prefix_upto (gm_expand Φ) y = Some (gm_ext Φ' y E) -> entry_unit E = Some U -> gm_fill Φ' = Some σ ->
    unit_member_proofs γ κs (gu_open Δ Φ) (y :: ys) x =
    modexp_member_proofs γ (tele_out_proofs γ κs (List.rev Δ)) (me_lit (gunit_sub U σ)) ys x.
Proof.
  intros * Hno Hp HEu Hf. rewrite unit_member_proofs_tele_out. cbn [moddef_member_proofs modexp_member_proofs].
  rewrite <- (proj2 (body_member_proofs_expand γ Φ _)), (body_member_lookup_chain_prefix _ _ _ _ _ _ _ Hno Hp).
  rewrite (proj2 (unit_member_proofs_sub_all γ) U _ σ _ (fun s ys' x' => eq_refl)).
  destruct E as [b pv r A om | pv U0 | | pv A M U0 |]; cbn in HEu; try discriminate; injection HEu as <-;
    cbn [gentry_slot_proofs]; apply (proj1 (proj2 (unit_member_proofs_resp_all γ))); exact (body_slot_proofs_fill _ _ _ Hf).
Qed.

(** A submodule of a valid body: its entry's unit, filled in, abstracted
    over the parameters. *)
Lemma set_body_sel : forall Γ Δ Φ Φx y R Rm, set_body_ok T γ Γ Δ Φ Φx ->
    (forall y0 Φ0 E U, gm_prefix_upto Φx y0 = Some (gm_ext Φ0 y0 E) -> entry_unit E = Some U ->
       set_valid_unit T γ (body_ctx Φ0 ++ Δ ++ Γ) (me_lit U)) ->
    mdenote gc_deps gc_stack Γ (me_mem (me_lit (gu_open Δ Φ)) y) R -> mdesc_mod R = Some Rm ->
    set_sel_valid_with Γ (me_lit (gu_open Δ Φ)) y Rm.
Proof.
  intros * Hb Hsub Hm Hmd. pose proof Hb as [Hw Hx HΔ [l Hl] HΓ HC _ _ _ (FH & _ & [HFH _ _]) _].
  destruct (Sel.body_mod_desc _ _ Hgw _ _ _ _ _ _ _ Hx Hm Hmd) as (Φ' & E & U & σ & RU & Hp & HEu & Hf & Hu & ->).
  pose proof (body_xp_result_noopen _ _ _ _ _ Hx) as Hno. pose proof (gm_noopen_nopens _ Hno) as Hn.
  pose proof (body_xp_expand _ _ _ _ _ Hx) as Hxe. subst Φx.
  pose proof (Hsub _ _ _ _ Hp HEu) as HKU.
  pose proof (proj1 (set_valid_unit_canon_all T γ Hfn Hmods Hgw Hok) _ _ HKU _ _ (mdenote_lit _ _ _ _ _ Hu)
                (mdesc_is_mod_mod _ (udenote_is_mod _ _ _ _ _ _ Hu))) as HcanU.
  pose proof (set_valid_unit_ctx T γ _ _ HKU) as HC0. pose proof (presup_modexp_eq_ctx (set_valid_unit_wf T γ _ _ HKU)) as Hc0.
  pose proof (set_ctx_app_r T γ _ _ HC0) as HD. pose proof (ctx_app_wf_tail _ _ _ _ Hc0) as HcD.
  destruct (set_gsub_fill T γ Hfn Hmods _ _ _ Hf HD HC0 Hc0) as (Fσ & Hs).
  pose proof (set_canon_moved _ _ _ _ _ _ HcanU Hs (set_sub_slots_coherent_fill _ _ _ Hf)) as [HrX HKX HpX].
  destruct (Sel.mem_unit_wf _ _ Hgw _ _ _ _ _ Hw Hm Hmd) as (HwHy & HwU & _).
  assert (HG : set_modexp_denotes T γ Γ (me_mem (me_lit (gu_open Δ Φ)) y) (fun ρ => select_module γ (FH ρ) y)).
  { apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
    econstructor; [ exact (set_modexp_denotes_exists _ _ _ _ _ HFH _ Hρ) | exact HwHy ]. }
  (* the submodule's value at an environment past the parameters *)
  assert (Hbase : forall ρ' n m, set_env_in T γ (Δ ++ Γ) ρ' -> set_interp_moddef T γ (Δ ++ Γ) ρ' (md_body sm_open Φ) n ->
            set_interp_modexp T γ (Δ ++ Γ) ρ' (mdesc_unit (mdesc_sub RU σ)) m -> set_module_eq γ (select_module γ n y) m)
    by (intros; eapply set_body_sel_base; eassumption).
  destruct Δ as [| e Δ0].
  - (* no parameter: the unit filled in *)
    rewrite mdesc_up_nil. cbn [List.app] in *. destruct HrX as (F1 & F2 & [HF1 HF2 E12]).
    constructor; [| exact HKX |].
    + exists (fun ρ => select_module γ (FH ρ) y), F2. constructor; [exact HG | exact HF2 |]. intros ρ Hρ.
      pose proof (set_modexp_denotes_exists _ _ _ _ _ HFH _ Hρ) as Hm1. apply set_interp_me_lit_iff in Hm1.
      inversion Hm1 as [? ? ? ? P1 m1 HP1 HL1]; subst. inversion HL1; subst.
      exact (Hbase _ _ _ Hρ ltac:(eassumption) (set_modexp_denotes_exists _ _ _ _ _ HF2 _ Hρ)).
    + intros κs Hκ ys x. cbn [modexp_member_proofs]. rewrite (body_sel_proofs _ _ _ _ _ _ _ _ _ _ Hno Hp HEu Hf).
      exact (HpX κs Hκ ys x).
  - (* over the parameters: the alias of it, flattened *)
    set (Δ := e :: Δ0) in *.
    pose proof (set_alias_unit_up T γ Hfn Hmods Hok Γ Δ _ l ltac:(discriminate) HΔ Hl HΓ HD HcD
                  (mdesc_is_mod_sub _ σ (udenote_is_mod _ _ _ _ _ _ Hu)) HKX HwU) as [Hrup HKup Hpup].
    pose proof (set_modexp_rel_refl_left T γ _ _ _ Hrup) as (F2 & _ & [HF2 _ _]).
    assert (Hpa : forall κs, set_slots_coherent γ Γ κs -> forall ys x,
               modexp_member_proofs γ κs (me_lit (gu_open Δ Φ)) (y :: ys) x =
               modexp_member_proofs γ κs (me_lit (gu_mk Δ (md_alias (mdesc_unit (mdesc_sub RU σ))))) ys x).
    { intros κs Hκ ys x. cbn [modexp_member_proofs]. rewrite (body_sel_proofs _ _ _ _ _ _ _ _ _ _ Hno Hp HEu Hf).
      rewrite unit_member_proofs_tele_out. cbn [moddef_member_proofs].
      exact (HpX _ (set_slots_coherent_tele_out γ _ _ _ HΔ Hκ) ys x). }
    constructor; [| exact HKup | intros κs Hκ ys x; exact (eq_trans (Hpa κs Hκ ys x) (Hpup κs Hκ ys x))].
    eapply set_modexp_rel_trans; [| exact Hrup].
    exists (fun ρ => select_module γ (FH ρ) y), F2. constructor; [exact HG | exact HF2 |]. intros ρ Hρ.
    pose proof (set_modexp_denotes_exists _ _ _ _ _ HFH _ Hρ) as Hm1. apply set_interp_me_lit_iff in Hm1.
    pose proof (set_modexp_denotes_exists _ _ _ _ _ HF2 _ Hρ) as Hm2. apply set_interp_me_lit_iff in Hm2.
    inversion Hm1 as [? ? ? ? P1 m1 HP1 HL1]; subst. inversion Hm2 as [? ? ? ? P2 m2 HP2 HL2]; subst.
    apply (set_unit_params_sel (List.rev Δ) Γ ρ P1 P2 _ _ _ _ y (List.Forall_rev HΔ) Hρ HL1 HL2).
    + intros ys x. rewrite HP1, HP2. exact (Hpa _ (set_slots_coherent_env T γ _ _ Hρ) ys x).
    + intros ρ' n1 n2 Hρ' Hn1 Hn2. rewrite List.rev_involutive in Hρ', Hn1, Hn2.
      inversion Hn2; subst. apply (Hbase _ _ _ Hρ' Hn1). assumption.
Qed.

(** ** Closed Units Read Anywhere *)

Lemma double_even_div2 : forall x, (Nat.even (x + x) = true /\ Nat.div2 (x + x) = x) /\
    (Nat.even (S (x + x)) = false /\ Nat.div2 (S (x + x)) = x).
Proof.
  induction x as [| x [[IHe IHd] [IHe' IHd']]]; [repeat split; reflexivity |].
  rewrite Nat.add_succ_r. cbn [Nat.add].
  change (Nat.even (S (S (x + x)))) with (Nat.even (x + x)).
  change (Nat.div2 (S (S (x + x)))) with (S (Nat.div2 (x + x))).
  change (Nat.even (S (S (S (x + x))))) with (Nat.even (S (x + x))).
  change (Nat.div2 (S (S (S (x + x))))) with (S (Nat.div2 (S (x + x)))).
  rewrite IHe, IHd, IHe', IHd'. repeat split; reflexivity.
Qed.

(** Two environments read side by side: one at the even positions, the
    other at the odd ones. *)
Definition set_env_merge (ρ1 ρ2 : set_env) : set_env :=
  fun x => if Nat.even x then ρ1 (Nat.div2 x) else ρ2 (Nat.div2 x).

Lemma set_env_merge_even : forall ρ1 ρ2 x, set_env_merge ρ1 ρ2 (x + x) = ρ1 x.
Proof. intros. unfold set_env_merge. destruct (double_even_div2 x) as [[-> ->] _]. reflexivity. Qed.

Lemma set_env_merge_odd : forall ρ1 ρ2 x, set_env_merge ρ1 ρ2 (S (x + x)) = ρ2 x.
Proof. intros. unfold set_env_merge. destruct (double_even_div2 x) as [_ [-> ->]]. reflexivity. Qed.

(** A closed unit of the empty context has one module at every
    environment: both are read at the environment holding both. *)
Lemma set_interp_closed_unit : forall U ρ1 ρ2 m1 m2, gunit_scoped 0 U -> ⊢ gc_deps ⍮ gc_stack ⍮ nil ->
    set_env_eq γ ρ1 ρ1 -> set_env_eq γ ρ2 ρ2 ->
    set_interp_gunit T γ nil ρ1 U m1 -> set_interp_gunit T γ nil ρ2 U m2 -> set_module_eq γ m1 m2.
Proof.
  intros * HU Hc E1 E2 Hm1 Hm2.
  assert (Hwk : forall φ, gc_deps ⍮ gc_stack ⍮ nil ⊢ʷ φ : nil)
    by (intros φ; constructor; [exact Hc | exact Hc | intros ? ? Hl; inversion Hl | intros ? ? ? Hl; inversion Hl
                               | intros ? ? Hl; inversion Hl]).
  set (ρ3 := set_env_merge ρ1 ρ2).
  assert (Hm : forall ρ φ m, set_interp_gunit T γ nil ρ U m -> (forall x, ρ x = ρ3 (φ x)) -> set_interp_gunit T γ nil ρ3 U m).
  { intros ρ φ m H Hag.
    assert (Hs : wk_setting nil ρ nil nil nil φ ρ3) by (constructor; [reflexivity | exact (Hwk φ) | exact Hag]).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (set_interp_wk_all T γ))))) _ _ _ _ H nil nil nil φ ρ3 Hs) as H'.
    cbn [tele_wk List.app List.length wk_qn] in H'.
    rewrite (proj1 (proj2 (proj2 (proj2 syn_scoped_wk_id))) U 0 _ HU ltac:(intros x Hx; lia)) in H'. exact H'. }
  assert (A1 : forall x, ρ1 x = ρ3 (x + x)) by (intros x; unfold ρ3; rewrite set_env_merge_even; reflexivity).
  assert (A2 : forall x, ρ2 x = ρ3 (S (x + x))) by (intros x; unfold ρ3; rewrite set_env_merge_odd; reflexivity).
  assert (E3 : set_env_eq γ ρ3 ρ3) by (intros x; unfold ρ3, set_env_merge; destruct (Nat.even x); [apply E1 | apply E2]).
  exact (proj1 (proj2 (proj2 (proj2 (proj2 (set_interp_functional_all T γ Hfn Hmods))))) _ _ _ _
           (Hm _ (fun x => x + x) _ Hm1 A1) ρ3 _ E3 (Hm _ (fun x => S (x + x)) _ Hm2 A2)).
Qed.

(** A closed unit has one proofness at every slots. *)
Lemma closed_unit_member_proofs : forall U κs1 κs2 ys x, gunit_scoped 0 U ->
    unit_member_proofs γ κs1 U ys x = unit_member_proofs γ κs2 U ys x.
Proof.
  intros * HU.
  set (κs3 := fun s => if Nat.even s then κs1 (Nat.div2 s) else κs2 (Nat.div2 s)).
  assert (Hid : forall φ, gunit_wk U φ = U)
    by (intros φ; exact (proj1 (proj2 (proj2 (proj2 syn_scoped_wk_id))) U 0 _ HU ltac:(intros x' Hx'; lia))).
  rewrite <- (proj2 (unit_member_proofs_wk_all γ) U κs3 (fun s => s + s) κs1), Hid
    by (intros s ys' x'; unfold κs3; destruct (double_even_div2 s) as [[-> ->] _]; reflexivity).
  rewrite <- (proj2 (unit_member_proofs_wk_all γ) U κs3 (fun s => S (s + s)) κs2), Hid
    by (intros s ys' x'; unfold κs3; destruct (double_even_div2 s) as [_ [-> ->]]; reflexivity).
  reflexivity.
Qed.

(** A closed unit read in any context is its module at the empty
    environment: read below the context, by weakening, then anywhere. *)
Lemma set_closed_unit_value : forall Γ U ρ m FU0, gunit_scoped 0 U -> ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> set_env_in T γ Γ ρ ->
    set_modexp_denotes T γ nil (me_lit U) FU0 -> set_interp_gunit T γ Γ ρ U m -> set_module_eq γ m (FU0 empty_set_env).
Proof.
  intros * HU Hc Hρ HFU Hm.
  assert (Hρ0 : set_env_in T γ nil (set_env_drop (List.length Γ) ρ))
    by (rewrite <- (List.app_nil_r Γ) in Hρ; exact (set_env_rel_drop T γ _ _ _ _ Hρ)).
  assert (He : set_env_in T γ nil empty_set_env) by (intros x; constructor; apply set_eq_refl).
  pose proof (set_modexp_denotes_exists _ _ _ _ _ HFU _ Hρ0) as Hm0. apply set_interp_me_lit_iff in Hm0.
  pose proof (set_modexp_denotes_exists _ _ _ _ _ HFU _ He) as Hme. apply set_interp_me_lit_iff in Hme.
  assert (Hs : wk_setting nil (set_env_drop (List.length Γ) ρ) nil nil Γ (fun x => List.length Γ + x) ρ).
  { constructor; [reflexivity | | intros x; reflexivity].
    constructor; [exact Hc | exact (wf_ctx_empty _ _ Hgw) | intros ? ? Hl; inversion Hl | intros ? ? ? Hl; inversion Hl
                 | intros ? ? Hl; inversion Hl]. }
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (set_interp_wk_all T γ))))) _ _ _ _ Hm0 nil nil Γ _ ρ Hs) as Hmw.
  cbn [tele_wk List.app List.length wk_qn] in Hmw.
  rewrite (proj1 (proj2 (proj2 (proj2 syn_scoped_wk_id))) U 0 _ HU ltac:(intros x Hx; lia)) in Hmw.
  eapply set_module_eq_trans;
    [exact (proj1 (proj2 (proj2 (proj2 (proj2 (set_interp_functional_all T γ Hfn Hmods))))) _ _ _ _ Hm _ _
              (set_env_rel_eq T γ _ _ _ Hρ) Hmw) |].
  exact (set_interp_closed_unit _ _ _ _ _ HU (wf_ctx_empty _ _ Hgw) Hρ0 He Hm0 Hme).
Qed.

(** ** Submodules of Filed Modules *)

(** A filed module at arguments is the global module at their values. *)
Lemma set_filed_value : forall Γ p T0 Φ ρ Ns m, gc_loc gc_deps gc_stack p = Some (T0, Φ) -> set_env_in T γ Γ ρ ->
    set_interp_modexp T γ Γ ρ (me_apps (qname_mod p) Ns) m ->
    exists ns, set_interp_list T γ Γ ρ Ns ns /\ set_module_eq γ m (set_module_global p ns).
Proof.
  intros * Hgl Hρ Hm. destruct (set_interp_me_apps_inv T γ _ _ _ _ _ Hm) as (m0 & ns & Hm0 & Hns & ->).
  exists ns. split; [exact Hns |].
  pose proof (set_filed_mod_path _ _ _ _ _ (set_gctx_ok_filed _ _ Hok _ _ _ Hgl) Γ ρ) as Hpath.
  pose proof (set_interp_modexp_functional T γ Hfn Hmods _ _ _ _ Hm0 _ _ (set_env_rel_eq T γ _ _ _ Hρ) Hpath) as E.
  rewrite <- (List.app_nil_l ns), <- apply_module_args_global.
  apply apply_module_args_resp; [exact E | apply list_set_eq_refl].
Qed.

(** Its proofness is the global module's, at any slots. *)
Lemma filed_member_proofs : forall p T0 Φ Ns κs ys x, gc_loc gc_deps gc_stack p = Some (T0, Φ) ->
    modexp_member_proofs γ κs (me_apps (qname_mod p) Ns) ys x = module_member_proofs γ (set_module_global p nil) ys x.
Proof.
  intros * Hgl. rewrite me_apps_member_proofs, (mod_qname_member_proofs γ _ _ (mod_qname_qname_mod p) κs (env_slot_proofs γ empty_set_env)).
  rewrite <- (set_interp_modexp_member_proofs T γ _ _ _ _ (set_filed_mod_path _ _ _ _ _ (set_gctx_ok_filed _ _ Hok _ _ _ Hgl) nil empty_set_env)).
  reflexivity.
Qed.

(** A body submodule of a filed module at arguments: filed at its path, at
    the arguments. *)
Lemma set_filed_body_sel : forall Γ p T0 Φ Tr Tf Ns y Tq Φq,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns ->
    gc_loc gc_deps gc_stack p = Some (T0, Φ) -> set_ctx T γ Γ -> set_args_valid T γ Γ T0 Tr Tf Ns ->
    gc_loc gc_deps gc_stack (qname_in p y) = Some (Tq, Φq) ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_apps (qname_mod (qname_in p y)) Ns ≈ me_apps (qname_mod (qname_in p y)) Ns ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_mem (me_apps (qname_mod p) Ns) y ≈ me_mem (me_apps (qname_mod p) Ns) y ->
    set_sel_valid_with Γ (me_apps (qname_mod p) Ns) y (mdesc_closed nil (qname_in p y) Tq Φq Ns).
Proof.
  intros * Hw Hgl HΓ Ha Hglq Hwq HwY. cbn [mdesc_unit].
  destruct (loc_child_tele _ _ Hgw _ _ _ _ _ _ Hgl Hglq) as (Δ' & -> & HΔ').
  pose proof Ha as [-> Hlen HTfa HTfs HNs HNr].
  assert (Ha' : set_args_valid T γ Γ (Δ' ++ Tr ++ Tf) (Δ' ++ Tr) Tf Ns)
    by (constructor; [rewrite List.app_assoc; reflexivity | exact Hlen | exact HTfa | exact HTfs | exact HNs | exact HNr]).
  pose proof (set_valid_unit_filed T γ _ _ _ _ _ _ _ Hw Hgl HΓ Ha) as HK.
  pose proof (set_valid_unit_filed T γ _ _ _ _ _ _ _ Hwq Hglq HΓ Ha') as HKq.
  constructor; [| exact HKq |].
  - destruct (set_valid_unit_rel T γ Hfn Hmods Hok _ _ HK) as (FK & _ & [HFK _ _]).
    destruct (set_valid_unit_rel T γ Hfn Hmods Hok _ _ HKq) as (Fq & _ & [HFq _ _]).
    exists (fun ρ => select_module γ (FK ρ) y), Fq. constructor; [| exact HFq |].
    + apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
      econstructor; [ exact (set_modexp_denotes_exists _ _ _ _ _ HFK _ Hρ) | exact HwY ].
    + intros ρ Hρ.
      destruct (set_filed_value _ _ _ _ _ _ _ Hgl Hρ (set_modexp_denotes_exists _ _ _ _ _ HFK _ Hρ)) as (ns & Hns & E1).
      destruct (set_filed_value _ _ _ _ _ _ _ Hglq Hρ (set_modexp_denotes_exists _ _ _ _ _ HFq _ Hρ)) as (ns' & Hns' & E2).
      eapply set_module_eq_trans; [exact (select_module_resp γ Hmods _ _ E1 y) |].
      cbn [select_module]. rewrite (set_gctx_ok_bodies _ _ Hok _ _ Hglq), apply_module_args_global. cbn [List.app].
      eapply set_module_eq_trans; [| exact (set_module_eq_sym _ _ E2)].
      apply set_module_eq_global.
      exact (proj1 (proj2 (set_interp_functional_all T γ Hfn Hmods)) _ _ _ _ Hns _ _ (set_env_rel_eq T γ _ _ _ Hρ) Hns').
  - intros κs _ ys x. cbn [mdesc_unit]. rewrite (filed_member_proofs _ _ _ _ _ _ _ Hgl), (filed_member_proofs _ _ _ _ _ _ _ Hglq).
    cbn [module_member_proofs]. rewrite (set_gctx_ok_bodies _ _ Hok _ _ Hglq). reflexivity.
Qed.

(** An alias submodule of a filed module at arguments: the stored unit at
    the arguments, which is the module the valuation stores. *)
Lemma set_filed_alias_sel : forall Γ p T0 Φ Tr Tf Ns y Φ0 E Ua RU Rm,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns ->
    gc_loc gc_deps gc_stack p = Some (T0, Φ) -> set_ctx T γ Γ -> set_args_valid T γ Γ T0 Tr Tf Ns ->
    gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_alias_unit E = Some Ua ->
    mdenote gc_deps gc_stack Γ (me_apps (me_lit Ua) Ns) RU -> mdesc_mod RU = Some Rm ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_mem (me_apps (qname_mod p) Ns) y ≈ me_mem (me_apps (qname_mod p) Ns) y ->
    set_sel_valid_with Γ (me_apps (qname_mod p) Ns) y Rm.
Proof.
  intros * Hw Hgl HΓ Ha Hp HUa HmU HmdU HwY.
  pose proof (set_gctx_ok_filed _ _ Hok _ _ _ Hgl) as HFm.
  destruct (set_filed_mod_aliases _ _ _ _ _ HFm _ _ _ _ Hp HUa) as [HmUa HvUa].
  pose proof (presup_modexp_eq_ctx Hw) as HcΓ.
  pose proof (HvUa _ HΓ HcΓ) as HKUa.
  pose proof (HvUa nil I (wf_ctx_empty _ _ Hgw)) as HKUa0.
  pose proof (proj1 (proj2 (wf_modexp_eq_scoped _ _ _ _ _ (set_valid_unit_wf T γ _ _ HKUa0)))) as HUs. cbn in HUs.
  destruct (set_valid_unit_rel T γ Hfn Hmods Hok _ _ HKUa0) as (FU0 & _ & [HFU0 _ _]).
  pose proof (set_gctx_ok_aliases _ _ Hok _ _ _ HmUa HFU0) as EqA.
  pose proof (set_valid_unit_filed T γ _ _ _ _ _ _ _ Hw Hgl HΓ Ha) as HK.
  (* the stored unit at the arguments is valid in what it denotes *)
  assert (HsV : set_valid_modexp T γ Γ (me_apps (me_lit Ua) Ns)).
  { assert (HUa' : exists Ta Ea, Ua = gu_mk Ta (md_alias Ea))
      by (destruct E as [| pv [Ta [| Ea]] | | pv Ad Md [Ta [| Ea]] |]; cbn in HUa; try discriminate; injection HUa as <-; eauto).
    destruct HUa' as (Ta & Ea & ->).
    destruct (loc_alias_params _ _ Hgw _ _ _ _ _ Hgl HmUa) as (Δ0 & HTa' & HaΔ0); cbn [gu_params] in HTa'; subst Ta.
    pose proof Ha as [-> Hlen HTfa HTfs HNs HNr].
    inversion HKUa as [| | ? ? ? Hal0 HE0]; subst;
      try (exfalso; match goal with Hq : me_apps _ _ = me_lit _ |- _ => exact (me_apps_qname_not_lit _ _ _ Hq) end).
    inversion HE0 as [? ? KE RE RmE RKE [HwE HmE HmodE _ _ _ _] _]; subst.
    pose proof (proj1 (modexp_gen _ _ _ _ _ (set_valid_unit_wf T γ _ _ HKUa))) as HfUa; cbn [gen_m unit_full] in HfUa.
    destruct HfUa as [lp ps Hps HΔΓ HaTa HE'w HTp lv Rt HF].
    pose proof (udenote_alias _ _ _ None _ _ _ _ HmE HmodE) as Hu.
    pose proof (desc_ok_mod _ _ Hgw _ _ _ (me_desc_ok _ _ _ _ _ _ HE'w HmE) HmodE) as HokR.
    destruct (filed_denote _ _ Hgw _ _ _ Γ Ns Hgl) as (RF & HmF & HmodF).
    destruct (desc_ok_filed_args _ _ _ _ _ _ (me_desc_ok _ _ _ _ _ _ Hw HmF) HmodF) as [_ Hargs].
    destruct Hargs as [rest filled Hspl Hl2 _ _ Hwf Hsyn].
    destruct (MemberTypes.app_split_length _ _ _ _ Hspl ltac:(rewrite Hl2; exact Hlen)) as [_ <-].
    assert (Hti : tele_insts (Δ0 ++ Tr ++ Tf) sb_id Ns = tele_insts Tf sb_id Ns)
      by (rewrite List.app_assoc; exact (Sel.tele_insts_app_full (Δ0 ++ Tr) Tf sb_id Ns HTfa (eq_sym Hlen))).
    apply (set_valid_modexp_apps_up T γ Hfn Hmods Hgw Hok Ns Γ _ RmE _ lp
             (set_valid_modexp_of_unit T γ Hfn Hmods Hok _ _ HKUa) (mdenote_lit _ _ _ _ _ Hu) (mdesc_mod_is_mod _ _ HmodE)
             HΔΓ HaTa).
    - rewrite !List.length_app. lia.
    - intros k N A HN HA. rewrite Hti in HA. exact (Hsyn _ _ _ HN HA).
    - intros k N A HN HA. rewrite Hti in HA. exact (HNs _ _ _ HN HA).
    - intros k A HA. rewrite Hti in HA. exact (HNr _ _ HA).
    - exact (params_evaluated_of_sorts _ _ _ _ _ _ Hps HTp).
    - exact HokR. }
  destruct (set_valid_modexp_canon T γ Hfn Hmods Hgw Hok _ _ _ _ HsV HmU HmdU) as [HrK HKK HpK].
  pose proof HrK as (FK' & _ & [HFK' _ _]).
  destruct (set_valid_unit_rel T γ Hfn Hmods Hok _ _ HK) as (FK & _ & [HFK _ _]).
  assert (He : set_env_in T γ nil empty_set_env) by (intros x; constructor; apply set_eq_refl).
  constructor; [| exact HKK |].
  - eapply set_modexp_rel_trans; [| exact HrK].
    exists (fun ρ => select_module γ (FK ρ) y), FK'. constructor; [| exact HFK' |].
    + apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
      econstructor; [ exact (set_modexp_denotes_exists _ _ _ _ _ HFK _ Hρ) | exact HwY ].
    + intros ρ Hρ.
      destruct (set_filed_value _ _ _ _ _ _ _ Hgl Hρ (set_modexp_denotes_exists _ _ _ _ _ HFK _ Hρ)) as (ns & Hns & E1).
      destruct (set_interp_me_apps_inv T γ _ _ _ _ _ (set_modexp_denotes_exists _ _ _ _ _ HFK' _ Hρ)) as (m0 & ns' & Hm0 & Hns' & ->).
      apply set_interp_me_lit_iff in Hm0.
      eapply set_module_eq_trans; [exact (select_module_resp γ Hmods _ _ E1 y) |]. cbn [select_module].
      apply apply_module_args_resp.
      * eapply set_module_eq_trans; [exact EqA |].
        exact (set_module_eq_sym _ _ (set_closed_unit_value _ _ _ _ _ HUs HcΓ Hρ HFU0 Hm0)).
      * exact (proj1 (proj2 (set_interp_functional_all T γ Hfn Hmods)) _ _ _ _ Hns _ _ (set_env_rel_eq T γ _ _ _ Hρ) Hns').
  - intros κs Hκ ys x. rewrite (filed_member_proofs _ _ _ _ _ _ _ Hgl). cbn [module_member_proofs].
    rewrite (module_member_proofs_resp γ ys _ _ EqA x).
    rewrite (proj1 (proj2 (proj2 (proj2 (set_interp_member_proofs_all T γ)))) _ _ _ _
               (set_modexp_denotes_exists _ _ _ _ _ HFU0 _ He) ys x).
    cbn [modexp_member_proofs]. rewrite (closed_unit_member_proofs _ _ κs _ _ HUs).
    rewrite <- (HpK κs Hκ ys x), me_apps_member_proofs. reflexivity.
Qed.

(** ** The Submodules of Valid Units *)

(** Related module expressions have related submodules. *)
Lemma set_modexp_rel_mem : forall Γ H H' y, set_ctx T γ Γ -> set_modexp_rel T γ Γ H H' ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_mem H y ≈ me_mem H y -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_mem H' y ≈ me_mem H' y ->
    set_modexp_rel T γ Γ (me_mem H y) (me_mem H' y).
Proof.
  intros * HΓ (F & F' & [HF HF' E]) HwY HwY'.
  exists (fun ρ => select_module γ (F ρ) y), (fun ρ => select_module γ (F' ρ) y). constructor.
  - apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
    econstructor; [ exact (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ) | exact HwY ].
  - apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
    econstructor; [ exact (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ) | exact HwY' ].
  - intros ρ Hρ. exact (select_module_resp γ Hmods _ _ (E _ Hρ) y).
Qed.

(** A submodule of an alias over parameters: its target's, abstracted. *)
Lemma set_alias_sel : forall Γ Δ E y R' Rm', set_alias_ok T γ Γ Δ E -> set_valid_modexp T γ (Δ ++ Γ) E ->
    mdenote gc_deps gc_stack Γ (me_mem (me_lit (gu_mk Δ (md_alias E))) y) (mdesc_up Δ R') -> mdesc_mod R' = Some Rm' ->
    mdenote gc_deps gc_stack (Δ ++ Γ) (me_mem E y) R' ->
    set_sel_valid_with (Δ ++ Γ) E y Rm' -> set_sel_valid_with Γ (me_lit (gu_mk Δ (md_alias E))) y (mdesc_up Δ Rm').
Proof.
  intros * Hal HE Hm Hmd' Hm' [HrE HKE HpE]. pose proof Hal as [Hw HΔ [l Hl] HΓ HΔΓ (FA & _ & [HFA _ _]) HEE].
  pose proof (presup_modexp_eq_ctx (set_valid_modexp_wf T γ _ _ HE)) as HcΔΓ.
  destruct (Sel.mem_unit_wf _ _ Hgw _ _ _ _ _ (set_valid_modexp_wf T γ _ _ HE) Hm' Hmd') as (HwEy & _ & _).
  destruct (Sel.mem_unit_wf _ _ Hgw _ _ _ _ _ Hw Hm ltac:(rewrite mdesc_mod_up, Hmd'; reflexivity)) as (HwLy & HwU & _).
  destruct Δ as [| e Δ0].
  - (* no parameter: the target's submodule *)
    rewrite mdesc_up_nil. cbn [List.app] in *.
    constructor; [| exact HKE | intros κs Hκ ys x; exact (HpE κs Hκ ys x)].
    eapply set_modexp_rel_trans; [| exact HrE].
    exact (set_modexp_rel_mem _ _ _ _ HΓ (set_alias0_rel T γ Hfn Hmods _ _ HΓ HEE) HwLy HwEy).
  - (* over the parameters: the alias of the target's, abstracted *)
    set (Δ := e :: Δ0) in *.
    pose proof (set_alias_unit_up T γ Hfn Hmods Hok Γ Δ _ l ltac:(discriminate) HΔ Hl HΓ HΔΓ HcΔΓ
                  (mdesc_mod_is_mod _ _ Hmd') HKE HwU) as [Hrup HKup Hpup].
    pose proof (set_modexp_rel_refl_left T γ _ _ _ Hrup) as (F2 & _ & [HF2 _ _]).
    destruct HrE as (G1 & G2 & [HG1 HG2 EG]).
    assert (Hpa : forall κs, set_slots_coherent γ Γ κs -> forall ys x,
               modexp_member_proofs γ κs (me_lit (gu_mk Δ (md_alias E))) (y :: ys) x =
               modexp_member_proofs γ κs (me_lit (gu_mk Δ (md_alias (mdesc_unit Rm')))) ys x).
    { intros κs Hκ ys x. cbn [modexp_member_proofs]. rewrite !unit_member_proofs_tele_out. cbn [moddef_member_proofs].
      exact (HpE _ (set_slots_coherent_tele_out γ _ _ _ HΔ Hκ) ys x). }
    constructor; [| exact HKup | intros κs Hκ ys x; exact (eq_trans (Hpa κs Hκ ys x) (Hpup κs Hκ ys x))].
    eapply set_modexp_rel_trans; [| exact Hrup].
    exists (fun ρ => select_module γ (FA ρ) y), F2. constructor; [| exact HF2 |].
    + apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
      econstructor; [ exact (set_modexp_denotes_exists _ _ _ _ _ HFA _ Hρ) | exact HwLy ].
    + intros ρ Hρ.
      pose proof (set_modexp_denotes_exists _ _ _ _ _ HFA _ Hρ) as Hm1. apply set_interp_me_lit_iff in Hm1.
      pose proof (set_modexp_denotes_exists _ _ _ _ _ HF2 _ Hρ) as Hm2. apply set_interp_me_lit_iff in Hm2.
      inversion Hm1 as [? ? ? ? P1 m1 HP1 HL1]; subst. inversion Hm2 as [? ? ? ? P2 m2 HP2 HL2]; subst.
      apply (set_unit_params_sel (List.rev Δ) Γ ρ P1 P2 _ _ _ _ y (List.Forall_rev HΔ) Hρ HL1 HL2).
      * intros ys x. rewrite HP1, HP2. exact (Hpa _ (set_slots_coherent_env T γ _ _ Hρ) ys x).
      * intros ρ' n1 n2 Hρ' Hn1 Hn2. rewrite List.rev_involutive in Hρ', Hn1, Hn2.
        inversion Hn1; subst. inversion Hn2; subst.
        match goal with H1 : set_interp_modexp _ _ _ _ E n1, H2 : set_interp_modexp _ _ _ _ (mdesc_unit Rm') n2 |- _ =>
          eapply set_module_eq_trans; [exact (set_modexp_denotes_unique _ _ _ _ _ HG1 _ _ _ Hρ' (set_interp_me_mem T γ _ _ _ _ _ H1 HwEy)) |];
          eapply set_module_eq_trans; [exact (EG _ Hρ') |];
          exact (set_module_eq_sym _ _ (set_modexp_denotes_unique _ _ _ _ _ HG2 _ _ _ Hρ' H2)) end.
Qed.

Theorem set_valid_unit_sel_all :
  (forall Γ K, set_valid_unit T γ Γ K -> forall y R Rm, mdenote gc_deps gc_stack Γ (me_mem K y) R -> mdesc_mod R = Some Rm ->
     set_sel_valid_with Γ K y Rm) /\
  (forall Γ H, set_valid_modexp T γ Γ H -> forall y R Rm, mdenote gc_deps gc_stack Γ (me_mem H y) R -> mdesc_mod R = Some Rm ->
     set_sel_valid_with Γ H y Rm).
Proof.
  apply (set_valid_unit_modexp_ind T γ).
  - (* a filed module at arguments: the filed submodule or the stored alias *)
    intros Γ p T0 Φ Tr Tf Ns Hw Hgl HΓ Ha y R Rm Hm Hmd.
    destruct (Sel.mem_unit_wf _ _ Hgw _ _ _ _ _ Hw Hm Hmd) as (HwY & HwU & _).
    destruct (Sel.filed_mod_desc _ _ Hgw _ _ _ _ _ _ _ _ Hgl Hm Hmd)
      as [(Tq & Φq & Hglq & ->) | (Φ0 & E & Ua & RU & Hp & HUa & HmU & HmdU)].
    + cbn [mdesc_unit] in HwU. exact (set_filed_body_sel _ _ _ _ _ _ _ _ _ _ Hw Hgl HΓ Ha Hglq HwU HwY).
    + exact (set_filed_alias_sel _ _ _ _ _ _ _ _ _ _ _ _ _ Hw Hgl HΓ Ha Hp HUa HmU HmdU HwY).
  - (* a body: its entry's unit, filled in, over the parameters *)
    intros Γ Δ Φ Φx Hb Hsub _ _ _ y R Rm Hm Hmd. exact (set_body_sel _ _ _ _ _ _ _ Hb Hsub Hm Hmd).
  - (* an alias: its target's, over the parameters *)
    intros Γ Δ E Hal HE IHE y R Rm Hm Hmd.
    pose proof Hal as [Hw _ _ _ _ _ _].
    pose proof (proj1 (modexp_gen _ _ _ _ _ Hw)) as Hf; cbn [gen_m unit_full] in Hf.
    destruct Hf as [_ _ _ HwΔΓ _ _ _ _ _ _].
    destruct (Sel.alias_mod_desc _ _ Hgw _ _ _ _ _ _ HwΔΓ Hm Hmd) as (R' & Hm' & ->).
    rewrite mdesc_mod_up in Hmd. destruct (mdesc_mod R') as [Rm' |] eqn:Hmd'; cbn in Hmd; [injection Hmd as <- | discriminate].
    exact (set_alias_sel _ _ _ _ _ _ Hal HE Hm Hmd' Hm' (IHE _ _ _ Hm' Hmd')).
  - (* a module expression equal to a valid unit: as the unit's, or a frame *)
    intros Γ H K R0 Rm0 RK [HwH HmH HmodH HHK HmK HmodK Hpr] HK IHK y R Rm Hm Hmd.
    pose proof (set_valid_unit_ctx T γ _ _ HK) as HΓ.
    (* a path naming an open frame, of either kind: filed at it *)
    assert (Hframe : forall p Tq Φq, mod_qname (me_mem H y) = Some p -> gc_frame gc_stack p = Some (Tq, Φq) ->
              Rm = mdesc_closed nil p Tq Φq nil -> set_sel_valid_with Γ H y Rm).
    { intros p Tq Φq Hq Hf ->.
      destruct (Sel.mem_unit_wf _ _ Hgw _ _ _ _ _ HwH Hm Hmd) as (HwY & HwU & _).
      cbn in Hq; destruct (mod_qname H) as [p0 |] eqn:Hq0; [| discriminate]; injection Hq as <-.
      change (q_abs (q_unit p0) (q_chain p0 ++ y :: nil)) with (qname_in p0 y) in *.
      assert (Ht : exists U T1, gs_find_tele gc_stack (qname_in p0 y) = Some (U, nil, T1)).
      { unfold gc_frame in Hf; destruct (gs_find_tele gc_stack (qname_in p0 y)) as [[[U [| ? ?]] T1] |];
          try (destruct U as [? [[|] ? | ?]]); try discriminate; eauto. }
      destruct Ht as (U & T1 & Ht).
      destruct (frame_parent _ _ Hgw _ _ _ _ Ht) as (T0 & Φ0 & Hf0 & _).
      pose proof (mod_qname_inv _ _ Hq0) as ->.
      cbn [mdesc_unit] in HwU.
      assert (Hs0 : set_args_valid T γ Γ T0 T0 nil nil).
      { constructor; [rewrite List.app_nil_r; reflexivity | reflexivity | constructor | exact I
                     | intros [| k] N A HN; discriminate | intros [| k] A HA; discriminate]. }
      exact (set_filed_body_sel Γ p0 T0 Φ0 T0 nil nil y Tq Φq HwH ltac:(unfold gc_loc; rewrite Hf0; reflexivity) HΓ Hs0
               ltac:(unfold gc_loc; rewrite Hf; reflexivity) HwU HwY). }
    inversion Hm as [? ? pu Tq Φq Hq Hu | ? ? pu pq k D Mk Tm Φm Hq Hk HMk Hl | | | | ? ? ? R1 R1m Γy E rd R2 ? Hm1 Hmd1 He Hed Hr
                    | ? ? pu Rr Tm Φm Hq Hk Hl]; subst.
    + (* a unit: an open frame *)
      cbn in Hmd; injection Hmd as <-.
      destruct (gc_unit_cases _ _ _ _ _ Hu) as (p & Hq' & [Hf | (_ & Hc & _)]); rewrite Hq in Hq'; injection Hq' as <-.
      * exact (Hframe _ _ _ Hq Hf eq_refl).
      * exfalso; cbn in Hq; destruct (mod_qname H) as [p0 |]; [| discriminate]; injection Hq as <-.
        cbn in Hc; destruct (q_chain p0); discriminate.
    + (* the open frame of a member's module *)
      destruct (frame_ind_loc _ _ Hgw _ _ _ _ Hk) as (? & ? & Tq & Φq & ? & _ & Hf & Hl' & _).
      rewrite Hl in Hl'; injection Hl' as <- <-; cbn in Hmd; injection Hmd as <-.
      exact (Hframe _ _ _ Hq Hf eq_refl).
    + pose proof (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ Hm1 _ HmH) as ->.
      rewrite HmodH in Hmd1; injection Hmd1 as <-.
      assert (HmKy : mdenote gc_deps gc_stack Γ (me_mem K y) R) by (eapply mdenote_mem; [exact HmK | exact HmodK | exact He | exact Hed | exact Hr]).
      destruct (IHK _ _ _ HmKy Hmd) as [HrK HKu HpK].
      constructor; [| exact HKu |].
      * destruct (Sel.mem_unit_wf _ _ Hgw _ _ _ _ _ HwH Hm Hmd) as (HwHy & _ & _).
        destruct (Sel.mem_unit_wf _ _ Hgw _ _ _ _ _ (set_valid_unit_wf T γ _ _ HK) HmKy Hmd) as (HwKy & _ & _).
        exact (set_modexp_rel_trans T γ _ _ _ _ (set_modexp_rel_mem _ _ _ _ HΓ HHK HwHy HwKy) HrK).
      * intros κs Hκ ys x. exact (eq_trans (Hpr κs Hκ (y :: ys) x) (HpK κs Hκ ys x)).
    + (* the open frame of a record type's module *)
      destruct (frame_record_loc _ _ Hgw _ _ Hk) as (? & ? & Tq & Φq & _ & Hf & Hl').
      rewrite Hl in Hl'; injection Hl' as <- <-; cbn in Hmd; injection Hmd as <-.
      exact (Hframe _ _ _ Hq Hf eq_refl).
Qed.

(** A submodule of a module expression valid in what it denotes is valid,
    as the unit of its module part. *)
Corollary set_valid_modexp_sel : forall Γ H y R Rm, set_valid_modexp T γ Γ H ->
    mdenote gc_deps gc_stack Γ (me_mem H y) R -> mdesc_mod R = Some Rm ->
    set_sel_valid_with Γ H y Rm /\ set_valid_modexp T γ Γ (me_mem H y).
Proof.
  intros * HH Hm Hmd. pose proof (proj2 set_valid_unit_sel_all _ _ HH _ _ _ Hm Hmd) as HS. split; [exact HS |].
  destruct HS as [Hr HK Hp].
  destruct (Sel.mem_unit_wf _ _ Hgw _ _ _ _ _ (set_valid_modexp_wf T γ _ _ HH) Hm Hmd) as (HwHy & _ & RK & HmK & HmdK).
  apply (set_valid_modexp_intro T γ _ _ (mdesc_unit Rm) R Rm RK); [| exact HK].
  constructor; [exact HwHy | exact Hm | exact Hmd | exact Hr | exact HmK | exact HmdK |].
  intros κs Hκ ys x. exact (Hp κs Hκ ys x).
Qed.

(** ** The Rules *)

Lemma mdesc_mod_tele_mod : forall R Tl, mdesc_mod_tele R = Some Tl -> exists Rm, mdesc_mod R = Some Rm.
Proof. intros * H. unfold mdesc_mod_tele in H. destruct (mdesc_mod R) as [Rm |]; [exists Rm; reflexivity | discriminate]. Qed.

(** Submodules of equal module expressions are equal. *)
Lemma set_rule_me_mem : forall Γ H H' y R Tl R' Tl', set_ctx T γ Γ -> set_modexp_eq T γ Γ H H' ->
    mdenote gc_deps gc_stack Γ (me_mem H y) R -> mdesc_mod_tele R = Some Tl ->
    mdenote gc_deps gc_stack Γ (me_mem H' y) R' -> mdesc_mod_tele R' = Some Tl' ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_mem H y ≈ me_mem H y -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_mem H' y ≈ me_mem H' y ->
    set_modexp_eq T γ Γ (me_mem H y) (me_mem H' y).
Proof.
  intros * HΓ (F & F' & [HF HF' E Hv Hv' Hpr]) Hm Ht Hm' Ht' HwY HwY'.
  destruct (mdesc_mod_tele_mod _ _ Ht) as (Rm & Hmd). destruct (mdesc_mod_tele_mod _ _ Ht') as (Rm' & Hmd').
  apply set_modexp_eq_of_rel; [| exact (proj2 (set_valid_modexp_sel _ _ _ _ _ Hv Hm Hmd))
                              | exact (proj2 (set_valid_modexp_sel _ _ _ _ _ Hv' Hm' Hmd'))
                              | intros κs Hκ ys x; exact (Hpr κs Hκ (y :: ys) x)].
  apply set_modexp_rel_mem; [exact HΓ | | exact HwY | exact HwY']. exists F, F'. constructor; assumption.
Qed.

(** [δ] for submodules: a submodule is the unit its module part stands
    for. *)
Lemma set_rule_me_delta_sel : forall Γ H y R Rm, set_modexp_eq T γ Γ (me_mem H y) (me_mem H y) ->
    mdenote gc_deps gc_stack Γ (me_mem H y) R -> mdesc_mod R = Some Rm ->
    set_modexp_eq T γ Γ (me_mem H y) (mdesc_unit Rm).
Proof.
  intros * (F & F' & [_ _ _ Hv _]) Hm Hmd. destruct (set_valid_modexp_canon T γ Hfn Hmods Hgw Hok _ _ _ _ Hv Hm Hmd) as [Hr HK Hpr].
  exact (set_modexp_eq_of_rel T γ _ _ _ Hr Hv (set_valid_modexp_of_unit T γ Hfn Hmods Hok _ _ HK) Hpr).
Qed.

End Sel.
