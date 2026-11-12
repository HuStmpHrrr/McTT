(** * The Set Rules of Module Expressions

    Equal module expressions denote equal modules and are valid
    ([set_modexp_eq]).  A valid unit is valid as a module expression, of
    its own module ([set_valid_modexp_of_unit]); a slot is its unit; a
    loaded unit is filed at no argument; a literal is its unit; [β]
    instantiates a literal's outermost parameter.  Selections and
    applications are valid by the units their module parts stand for
    ([set_valid_unit_sel_all], [set_valid_modexp_app]). *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Respects Substitution JudgmentSubstitution.
From Mctt.Core.SetModel.Interpretation.Global Require Import Model.
From Mctt.Core.SetModel.Cases Require Import ValidUnit MemberTypes.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas MemberWf DescTyping LookupSound Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax.
From Mctt.Core.Completeness.Modules Require Import App.
Import ListNotations.

Section ModuleCases.
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

(** ** Valid Units Are Valid Module Expressions *)

(** An application's module: its head's at its arguments' values. *)
Lemma set_interp_me_apps : forall Ns Γ ρ H m ns, set_interp_modexp T γ Γ ρ H m -> set_interp_list T γ Γ ρ Ns ns ->
    set_interp_modexp T γ Γ ρ (me_apps H Ns) (apply_module_args m ns).
Proof.
  induction Ns as [| N Ns IH]; intros Γ ρ H m ns Hm Hns; inversion Hns; subst; [exact Hm |].
  cbn [me_apps]. match goal with HN : set_interp _ _ _ _ N ?v, HNs : set_interp_list _ _ _ _ Ns ?vs |- _ =>
    exact (IH _ _ _ (apply_module m v) vs (set_interp_me_app T γ _ _ _ _ _ _ Hm HN) HNs) end.
Qed.

(** A valid unit denotes, alike on both sides. *)
Lemma set_valid_unit_rel : forall Γ K, set_valid_unit T γ Γ K -> set_modexp_rel T γ Γ K K.
Proof.
  intros * HK. destruct HK as [Γ p T0 Φ Tr Tf Ns _ Hgl HΓ Ha | Γ Δ Φ Φx Hb _ _ | Γ Δ E Hal _].
  - pose proof (set_filed_mod_path _ _ _ _ _ (set_gctx_ok_filed _ _ Hok _ _ _ Hgl)) as Hpath.
    destruct Ha as [_ Hlen HTfa _ HNr _].
    assert (HN : forall k N, List.nth_error Ns k = Some N -> exists FN, set_denotes T γ Γ N FN).
    { intros k N HN.
      destruct (List.nth_error (tele_insts Tf sb_id Ns) k) as [A |] eqn:EA.
      - destruct (HNr _ _ _ HN EA) as (FA & FN & FN' & [_ HFN _ _ _]). exists FN. exact HFN.
      - exfalso. apply List.nth_error_None in EA. rewrite length_tele_insts in EA by exact HTfa.
        assert (Hk : k < List.length Ns) by (apply List.nth_error_Some; congruence). lia. }
    destruct (set_denotes_list T γ _ _ HN) as (Fs & HFs).
    set (F := fun ρ => apply_module_args (set_module_global p nil) (Fs ρ)).
    assert (HF : set_modexp_denotes T γ Γ (me_apps (qname_mod p) Ns) F).
    { apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
      exact (set_interp_me_apps _ _ _ _ _ _ (Hpath Γ ρ) (HFs _ Hρ)). }
    exists F, F. constructor; [exact HF | exact HF |].
    intros ρ Hρ. apply set_modexp_denotes_unique with (1 := HF) (2 := Hρ). exact (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ).
  - exact (set_body_ok_rel _ _ _ _ _ _ Hb).
  - exact (set_alias_ok_rel _ _ _ _ _ Hal).
Qed.

(** A valid unit is valid in what it denotes, as itself. *)
Lemma set_valid_modexp_of_unit : forall Γ K, set_valid_unit T γ Γ K -> set_valid_modexp T γ Γ K.
Proof.
  intros * HK. pose proof (set_valid_unit_wf T γ _ _ HK) as Hw.
  destruct (me_denotes _ _ _ _ _ Hw) as (R & Rm & Hm & Hmd).
  apply (set_valid_modexp_intro T γ _ _ K R Rm R); [| exact HK].
  constructor; [exact Hw | exact Hm | exact Hmd | exact (set_valid_unit_rel _ _ HK) | exact Hm | exact Hmd |].
  intros; reflexivity.
Qed.

(** Equal module expressions, both valid. *)
Lemma set_modexp_eq_of_rel : forall Γ H H', set_modexp_rel T γ Γ H H' -> set_valid_modexp T γ Γ H -> set_valid_modexp T γ Γ H' ->
    set_modexp_eq T γ Γ H H'.
Proof. intros * (F & F' & [HF HF' E]) HH HH'. exists F, F'. constructor; assumption. Qed.

(** A denotation on the left relates to itself. *)
Lemma set_modexp_rel_refl_left : forall Γ H H', set_modexp_rel T γ Γ H H' -> set_modexp_rel T γ Γ H H.
Proof.
  intros * (F & F' & [HF _ _]). exists F, F. constructor; [exact HF | exact HF |].
  intros ρ Hρ. exact (set_modexp_denotes_unique _ _ _ _ _ HF _ _ _ Hρ (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ)).
Qed.

Lemma set_modexp_rel_sym : forall Γ H H', set_modexp_rel T γ Γ H H' -> set_modexp_rel T γ Γ H' H.
Proof. intros * (F & F' & [HF HF' E]). exists F', F. constructor; [exact HF' | exact HF |]. intros ρ Hρ. apply set_module_eq_sym. exact (E _ Hρ). Qed.

(** ** Slots *)

(** A slot's proofness is its unit's, at coherent slots. *)
Lemma set_slots_coherent_lookup : forall Γ x U, Γ ∋ #x ≔ₘ U -> forall κs, set_slots_coherent γ Γ κs ->
    forall ys z, κs x ys z = unit_member_proofs γ κs U ys z.
Proof.
  induction 1 as [U0 Γ0 | U0 A M Γ0 | n U1 Γ0 e Hl IH]; intros κs [Hc Hu] ys z;
    rewrite (proj2 (unit_member_proofs_wk_all γ) _ κs wk_shift (fun s => κs (S s))) by (intros s ys' z'; reflexivity).
  - exact (Hu _ eq_refl ys z).
  - exact (Hu _ eq_refl ys z).
  - exact (IH _ Hc ys z).
Qed.

(** A slot denotes the module its entry holds, equal to its unit's. *)
Lemma set_slot_rel : forall Γ x U, Γ ∋ #x ≔ₘ U -> set_ctx T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ Γ ->
    set_modexp_rel T γ Γ (me_var x) (me_lit U).
Proof.
  induction 1 as [U0 Γ0 | U0 A M Γ0 | n U1 Γ0 e Hl IH]; intros HC Hc;
    (assert (Hs : set_moves_with T γ nil _ _ (sb_of_wk wk_shift) set_env_tail)
       by (constructor; [exact (set_gsub_shift T γ _ _ Hc) | exact HC | exact (proj1 HC) | exact HC | exact (ctx_decomp_tail Hc)])).
  all: change (me_lit (gunit_wk ?U wk_shift)) with (modexp_wk (me_lit U) wk_shift); rewrite <- modexp_sub_of_wk.
  - destruct HC as [HC0 (FU & FU' & [HFU _ _])].
    pose proof (set_modexp_denotes_moved T γ Hfn Hmods _ _ _ _ _ _ _ Hs HFU) as HFUm.
    exists (fun ρ => set_entry_module_part (ρ 0)), (fun ρ => FU (set_env_moved 0 set_env_tail ρ)).
    constructor; [constructor | exact HFUm |].
    + intros ρ Hρ. exact (set_interp_me_var T γ _ ρ 0).
    + intros ρ ρ' m Hr Hm. inversion Hm; subst. destruct Hr as [_ He]. cbn [set_entry_rel] in He.
      destruct He as (m1 & m1' & n & [Hl Hr' _ E1 E2]). rewrite Hl, Hr'. cbn [set_entry_module_part].
      exact (set_module_eq_trans _ _ _ E2 (set_module_eq_sym _ _ E1)).
    + intros ρ [Ht He]. cbn [set_entry_rel] in He. destruct He as (m1 & m1' & n & [Hl _ Hn E1 _]). rewrite Hl. cbn [set_entry_module_part].
      eapply set_module_eq_trans; [exact E1 |].
      exact (set_modexp_denotes_unique _ _ _ _ _ HFU _ _ _ Ht (set_interp_me_lit T γ _ _ _ _ Hn)).
  - destruct HC as [HC0 [_ (FU & FU' & [HFU _ _])]].
    pose proof (set_modexp_denotes_moved T γ Hfn Hmods _ _ _ _ _ _ _ Hs HFU) as HFUm.
    exists (fun ρ => set_entry_module_part (ρ 0)), (fun ρ => FU (set_env_moved 0 set_env_tail ρ)).
    constructor; [constructor | exact HFUm |].
    + intros ρ Hρ. exact (set_interp_me_var T γ _ ρ 0).
    + intros ρ ρ' m Hr Hm. inversion Hm; subst. destruct Hr as [_ He]. cbn [set_entry_rel] in He.
      destruct He as (v & v' & w & m1 & m1' & n & [Hl Hr' _ _ _ _ E1 E2]). rewrite Hl, Hr'. cbn [set_entry_module_part].
      exact (set_module_eq_trans _ _ _ E2 (set_module_eq_sym _ _ E1)).
    + intros ρ [Ht He]. cbn [set_entry_rel] in He. destruct He as (v & v' & w & m1 & m1' & n & [Hl _ _ Hn _ _ E1 _]).
      rewrite Hl. cbn [set_entry_module_part].
      eapply set_module_eq_trans; [exact E1 |].
      exact (set_modexp_denotes_unique _ _ _ _ _ HFU _ _ _ Ht (set_interp_me_lit T γ _ _ _ _ Hn)).
  - exact (set_modexp_rel_moved T γ Hfn Hmods _ _ _ _ _ _ _ Hs (IH (proj1 HC) (ctx_decomp_tail Hc))).
Qed.

(** A slot is valid as its unit. *)
Lemma set_valid_modexp_var : forall Γ x U, Γ ∋ #x ≔ₘ U -> set_ctx T γ Γ -> set_valid_slots T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ Γ ->
    set_valid_modexp T γ Γ (me_var x) /\ set_valid_unit T γ Γ (me_lit U).
Proof.
  intros * Hl HC Hsl Hc. pose proof (set_slot_valid_unit T γ Hfn Hmods Hgw _ _ _ Hl HC Hsl Hc) as HK. split; [| exact HK].
  pose proof (wf_me_var _ _ _ _ _ Hc Hl) as Hw.
  destruct (me_denotes _ _ _ _ _ Hw) as (R & Rm & Hm & Hmd).
  inversion Hm as [? ? ? ? ? Hq _ | ? ? ? ? ? ? ? ? ? Hq _ | ? ? ? ? Hl' Hu | | | | ? ? ? ? ? ? Hq _]; subst;
    try (cbn in Hq; discriminate).
  pose proof (ctx_lookup_mod_functional _ _ _ _ Hl Hl') as <-.
  apply (set_valid_modexp_intro T γ _ _ (me_lit U) R Rm R); [| exact HK].
  constructor; [exact Hw | exact Hm | exact Hmd | exact (set_slot_rel _ _ _ Hl HC Hc) | exact (mdenote_lit _ _ _ _ _ Hu) | exact Hmd |].
  intros κs Hκ ys z. cbn [modexp_member_proofs]. exact (set_slots_coherent_lookup _ _ _ Hl _ Hκ ys z).
Qed.

(** ** The Rules: Slots, Loaded Units, [δ] at a Slot, Symmetry and Transitivity *)

Lemma set_rule_me_var : forall Γ x U, Γ ∋ #x ≔ₘ U -> set_ctx T γ Γ -> set_valid_slots T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ Γ ->
    set_modexp_eq T γ Γ (me_var x) (me_var x).
Proof.
  intros * Hl HC Hsl Hc. destruct (set_valid_modexp_var _ _ _ Hl HC Hsl Hc) as [Hv _].
  exact (set_modexp_eq_of_rel _ _ _ (set_modexp_rel_refl_left _ _ _ (set_slot_rel _ _ _ Hl HC Hc)) Hv Hv).
Qed.

Lemma set_rule_me_delta_slot : forall Γ x U, Γ ∋ #x ≔ₘ U -> set_ctx T γ Γ -> set_valid_slots T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ Γ ->
    set_modexp_eq T γ Γ (me_var x) (me_lit U).
Proof.
  intros * Hl HC Hsl Hc. destruct (set_valid_modexp_var _ _ _ Hl HC Hsl Hc) as [Hv HK].
  exact (set_modexp_eq_of_rel _ _ _ (set_slot_rel _ _ _ Hl HC Hc) Hv (set_valid_modexp_of_unit _ _ HK)).
Qed.

Lemma set_rule_me_unit : forall Γ fp TΦ, ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> set_ctx T γ Γ -> gc_unit gc_deps gc_stack (me_unit fp) = Some TΦ ->
    set_modexp_eq T γ Γ (me_unit fp) (me_unit fp).
Proof.
  intros * Hc HC Hu. destruct TΦ as [T0 Φ0]. destruct (gc_unit_loc _ _ _ _ _ Hu) as (mp & Hq & Hl).
  pose proof (mod_qname_inv _ _ Hq) as Heq. rewrite Heq.
  assert (HK : set_valid_unit T γ Γ (me_apps (qname_mod mp) nil)).
  { apply (set_valid_unit_filed T γ Γ mp T0 Φ0 T0 nil nil); [exact (loc_modexp_wf _ _ _ Hc _ _ _ Hl) | exact (gc_loc_of_loc _ _ Hgw _ _ _ Hl)
                                                            | exact HC |].
    constructor; [rewrite List.app_nil_r; reflexivity | reflexivity | constructor | exact I
                 | intros [| k] N A HN; discriminate | intros [| k] A HA; discriminate]. }
  pose proof (set_valid_modexp_of_unit _ _ HK) as Hv.
  exact (set_modexp_eq_of_rel _ _ _ (set_valid_unit_rel _ _ HK) Hv Hv).
Qed.

Lemma set_rule_me_sym : forall Γ H H', set_modexp_eq T γ Γ H H' -> set_modexp_eq T γ Γ H' H.
Proof.
  intros * (F & F' & [HF HF' E Hv Hv']). exists F', F. constructor; [exact HF' | exact HF | | exact Hv' | exact Hv].
  intros ρ Hρ. apply set_module_eq_sym. exact (E _ Hρ).
Qed.

Lemma set_rule_me_trans : forall Γ H H' H'', set_modexp_eq T γ Γ H H' -> set_modexp_eq T γ Γ H' H'' -> set_modexp_eq T γ Γ H H''.
Proof.
  intros * (F & F' & [HF HF' E Hv _]) (G & G' & [HG HG' E' _ Hv'']). exists F, G'. constructor; [exact HF | exact HG' | | exact Hv | exact Hv''].
  intros ρ Hρ. eapply set_module_eq_trans; [exact (E _ Hρ) |]. eapply set_module_eq_trans; [| exact (E' _ Hρ)].
  exact (set_modexp_denotes_unique _ _ _ _ _ HG _ _ _ Hρ (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ)).
Qed.

(** ** Literals *)

Lemma set_rule_me_lit : forall Γ U U', set_unit_eq T γ Γ U U' -> set_modexp_eq T γ Γ (me_lit U) (me_lit U').
Proof.
  intros * (F & F' & [HF HF' E HU HU']). exists F, F'.
  constructor; [exact HF | exact HF' | exact E | exact (set_valid_modexp_of_unit _ _ HU) | exact (set_valid_modexp_of_unit _ _ HU')].
Qed.

(** An alias of no parameter denotes its target's module. *)
Lemma set_alias0_rel : forall Γ E, set_ctx T γ Γ -> set_modexp_rel T γ Γ E E ->
    set_modexp_rel T γ Γ (me_lit (gu_mk nil (md_alias E))) E.
Proof.
  intros * HΓ (FE & _ & [HFE _ _]).
  assert (HF : set_modexp_denotes T γ Γ (me_lit (gu_mk nil (md_alias E))) FE).
  { apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ. constructor.
    apply (set_interp_gunit_mk T γ _ _ _ _ (unit_member_proofs γ (env_slot_proofs γ ρ) (gu_mk nil (md_alias E)))); [intros; reflexivity |].
    cbn [List.rev]. constructor. constructor. exact (set_modexp_denotes_exists _ _ _ _ _ HFE _ Hρ). }
  exists FE, FE. constructor; [exact HF | exact HFE |].
  intros ρ Hρ. exact (set_modexp_denotes_unique _ _ _ _ _ HFE _ _ _ Hρ (set_modexp_denotes_exists _ _ _ _ _ HFE _ Hρ)).
Qed.

(** An alias of no parameter is its target. *)
Lemma set_rule_me_beta_alias0 : forall Γ E, set_ctx T γ Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_lit (gu_mk nil (md_alias E)) ≈ me_lit (gu_mk nil (md_alias E)) ->
    set_modexp_eq T γ Γ E E -> set_modexp_eq T γ Γ (me_lit (gu_mk nil (md_alias E))) E.
Proof.
  intros * HΓ Hw (FE & FE' & [HFE HFE' EE HvE _]).
  assert (HEE : set_modexp_rel T γ Γ E E).
  { exists FE, FE. constructor; [exact HFE | exact HFE |].
    intros ρ Hρ. exact (set_modexp_denotes_unique _ _ _ _ _ HFE _ _ _ Hρ (set_modexp_denotes_exists _ _ _ _ _ HFE _ Hρ)). }
  pose proof (set_alias0_rel _ _ HΓ HEE) as HrelE.
  pose proof (set_modexp_rel_refl_left _ _ _ HrelE) as Hrel.
  assert (HK : set_valid_unit T γ Γ (me_lit (gu_mk nil (md_alias E)))).
  { apply set_valid_unit_alias; [constructor | exact HvE].
    - exact Hw.
    - constructor.
    - exists 0. apply set_params_evaluated_nil.
    - exact HΓ.
    - exact HΓ.
    - exact Hrel.
    - exact HEE. }
  exact (set_modexp_eq_of_rel _ _ _ HrelE (set_valid_modexp_of_unit _ _ HK) HvE).
Qed.

(** ** Members *)

(** A term member of a valid module expression is of its type. *)
Lemma set_rule_mem : forall Γ H x R A, set_ctx T γ Γ -> set_modexp_eq T γ Γ H H ->
    mdenote gc_deps gc_stack Γ (me_mem H x) R -> mdesc_type R = Some A ->
    set_exp_eq T γ Γ A (a_mem H x) (a_mem H x).
Proof.
  intros * HΓ (F & F' & [HF _ _ Hv _]) Hm Ht.
  destruct (proj1 (set_valid_modexp_members_denote T γ Hfn Hmods Hgw Hok _ _ Hv _ _ _ Hm Ht)) as (FA & HA).
  assert (HM : set_denotes T γ Γ (a_mem H x) (fun ρ => select_term γ (F ρ) x)).
  { apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ. constructor. exact (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ). }
  exists FA, (fun ρ => select_term γ (F ρ) x), (fun ρ => select_term γ (F ρ) x).
  constructor; [exact HA | exact HM | exact HM | intros; apply set_eq_refl |].
  intros ρ Hρ. exact (proj1 (set_valid_modexp_members T γ Hfn Hmods Hgw Hok _ _ _ Hv HF _ _ _ _ Hm Ht HA _ Hρ)).
Qed.

(** Members of equal module expressions are equal. *)
Lemma set_rule_mem_cong : forall Γ H H' x R A, set_ctx T γ Γ -> set_modexp_eq T γ Γ H H' ->
    mdenote gc_deps gc_stack Γ (me_mem H x) R -> mdesc_type R = Some A -> set_exp_eq T γ Γ A (a_mem H x) (a_mem H' x).
Proof.
  intros * HΓ (F & F' & [HF HF' E Hv _]) Hm Ht.
  destruct (proj1 (set_valid_modexp_members_denote T γ Hfn Hmods Hgw Hok _ _ Hv _ _ _ Hm Ht)) as (FA & HA).
  assert (HM : set_denotes T γ Γ (a_mem H x) (fun ρ => select_term γ (F ρ) x)).
  { apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ. constructor. exact (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ). }
  assert (HM' : set_denotes T γ Γ (a_mem H' x) (fun ρ => select_term γ (F' ρ) x)).
  { apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ. constructor. exact (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ). }
  exists FA, (fun ρ => select_term γ (F ρ) x), (fun ρ => select_term γ (F' ρ) x).
  constructor; [exact HA | exact HM | exact HM' | |].
  - intros ρ Hρ. exact (select_term_resp γ _ _ (E _ Hρ) x).
  - intros ρ Hρ. exact (proj1 (set_valid_modexp_members T γ Hfn Hmods Hgw Hok _ _ _ Hv HF _ _ _ _ Hm Ht HA _ Hρ)).
Qed.

(** [δ] for members: a term member of a valid module expression is its
    reduct. *)
Lemma set_rule_mem_delta : forall Γ H x R A M, set_ctx T γ Γ -> set_modexp_eq T γ Γ H H ->
    mdenote gc_deps gc_stack Γ (me_mem H x) R -> mdesc_type R = Some A -> mdesc_reduct R = Some M ->
    set_exp_eq T γ Γ A (a_mem H x) M.
Proof.
  intros * HΓ (F & F' & [HF _ _ Hv _]) Hm Ht HM.
  destruct (set_valid_modexp_members_denote T γ Hfn Hmods Hgw Hok _ _ Hv _ _ _ Hm Ht) as [(FA & HA) HMd].
  destruct (HMd _ HM) as (FM & HFM).
  assert (HMem : set_denotes T γ Γ (a_mem H x) (fun ρ => select_term γ (F ρ) x)).
  { apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ. constructor. exact (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ). }
  exists FA, (fun ρ => select_term γ (F ρ) x), FM.
  constructor; [exact HA | exact HMem | exact HFM | |].
  - intros ρ Hρ. exact (proj2 (set_valid_modexp_members T γ Hfn Hmods Hgw Hok _ _ _ Hv HF _ _ _ _ Hm Ht HA _ Hρ) _ _ HM HFM).
  - intros ρ Hρ. exact (proj1 (set_valid_modexp_members T γ Hfn Hmods Hgw Hok _ _ _ Hv HF _ _ _ _ Hm Ht HA _ Hρ)).
Qed.

(** ** A Unit's Outermost Parameter Moved Into the Context *)

(** A unit's value read at an environment equal pointwise. *)
Lemma set_interp_gunit_env_ext : forall Γ ρ ρ' U m, ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> (forall x, ρ x = ρ' x) ->
    set_interp_gunit T γ Γ ρ U m -> set_interp_gunit T γ Γ ρ' U m.
Proof.
  intros * Hc E Hm.
  assert (Hs : wk_setting Γ ρ nil Γ Γ wk_id ρ') by (constructor; [reflexivity | exact (wf_wk_id _ _ _ Hc) | intros x; exact (E x)]).
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (set_interp_wk_all T γ))))) _ _ _ _ Hm nil Γ Γ wk_id ρ' Hs) as H.
  cbn [tele_wk List.app List.length wk_qn] in H.
  rewrite (proj1 (proj2 (proj2 (proj2 syn_wk_id_ext))) U wk_id ltac:(intros x; reflexivity)) in H. exact H.
Qed.

(** A unit's proofness, its outermost parameter no slot. *)
Lemma unit_member_proofs_unbind : forall κs κ X Δ D ys x,
    unit_member_proofs γ κs (gu_mk (Δ ++ [ce_ass κ X]) D) ys x =
    unit_member_proofs γ (push_slot_proofs κs (no_slot_proofs γ)) (gu_mk Δ D) ys x.
Proof. intros. rewrite !unit_member_proofs_tele_out, List.rev_app_distr. reflexivity. Qed.

Lemma env_slot_proofs_extend_term : forall ρ κ v,
    slot_proofs_eq (env_slot_proofs γ (set_env_extend ρ (set_entry_term κ v))) (push_slot_proofs (env_slot_proofs γ ρ) (no_slot_proofs γ)).
Proof. intros ρ κ v [| s] ys x; reflexivity. Qed.

(** [set_unit_params_with Γ ρ Δ κ X D m a P f]: the module [m] the unit
    [gu_mk (Δ ++ [ce_ass κ X]) D] has at [ρ] is the function [f] over the
    value [a] of its outermost parameter's type, of the proofness [P]; at
    each value of [a], [f] is the unit without the parameter, over the
    context extended by it. *)
Record set_unit_params_with (Γ : ctx) (ρ : set_env) (Δ : ctx) (κ : abs_kind) (X : exp) (D : moddef) (m : set_module)
    (a : aczel_set) (P : member_proofness) (f : aczel_set -> set_module) : Prop :=
  { (** [m] is the function [f] over [a], of the proofness [P] *)
    set_unit_params_module : m = set_module_params a P f
    (** [a] is the parameter's type's value *)
  ; set_unit_params_type : set_interp T γ Γ ρ X a
    (** [P] is the unit's proofness, read off its syntax *)
  ; set_unit_params_proofs : forall ys x, P ys x = unit_member_proofs γ (env_slot_proofs γ ρ) (gu_mk (Δ ++ [ce_ass κ X]) D) ys x
    (** At each value of [a], [f] is the unit without the parameter *)
  ; set_unit_params_body : forall v, set_mem v (code_carrier a) ->
      set_interp_gunit T γ (ce_ass κ X :: Γ) (set_env_extend ρ (set_entry_term κ v)) (gu_mk Δ D) (f v) }.

(** The function a unit over one more parameter denotes, at the
    parameter's value, is the unit without it over the context extended. *)
Lemma set_unit_params_unbind : forall Γ ρ Δ κ X D m, ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κ X :: Γ ->
    set_interp_gunit T γ Γ ρ (gu_mk (Δ ++ [ce_ass κ X]) D) m ->
    exists a P f, set_unit_params_with Γ ρ Δ κ X D m a P f.
Proof.
  intros * Hc Hm. inversion Hm as [? ? ? ? P m' HP HL]; subst.
  rewrite List.rev_app_distr in HL. cbn [List.rev List.app] in HL.
  inversion HL as [| ? ? ? ? ? ? ? a f _ HA Hf | | |]; subst.
  exists a, P, f. constructor; [reflexivity | exact HA | exact HP |].
  intros v Hv. apply (set_interp_gunit_mk T γ _ _ _ _ P); [| exact (Hf _ Hv)].
  intros ys x. rewrite HP, unit_member_proofs_unbind.
  apply (proj1 (proj2 (unit_member_proofs_resp_all γ))). intros s ys' x'. symmetry. apply env_slot_proofs_extend_term.
Qed.

(** The module a unit over one more parameter denotes at the parameter's
    value, read at an environment of the context extended by it. *)
Definition set_module_at_param (F : set_env -> set_module) (ρ : set_env) : set_module :=
  match F (set_env_tail ρ) with set_module_params _ _ f => f (set_entry_value (ρ 0)) | m => m end.

(** A unit over one more parameter, denoting, denotes without it over the
    context extended. *)
Lemma set_unit_denotes_unbind : forall Γ Δ κ X D F, set_ctx T γ (ce_ass κ X :: Γ) -> ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κ X :: Γ ->
    set_modexp_denotes T γ Γ (me_lit (gu_mk (Δ ++ [ce_ass κ X]) D)) F ->
    set_modexp_denotes T γ (ce_ass κ X :: Γ) (me_lit (gu_mk Δ D)) (set_module_at_param F).
Proof.
  intros * HC Hc HF. apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HC). intros ρ' [Ht He].
  cbn [set_entry_rel] in He. destruct He as (x & x' & a' & [Hl _ Ha' Hx _]).
  pose proof (set_modexp_denotes_exists _ _ _ _ _ HF _ Ht) as Hm.
  inversion Hm; subst.
  match goal with Hn : set_interp_gunit _ _ _ _ _ _ |- _ =>
    destruct (set_unit_params_unbind _ _ _ _ _ _ _ Hc Hn) as (a & P & f & [Heq Ha _ Hf]) end.
  unfold set_module_at_param. rewrite Heq, Hl. cbn [set_entry_value]. constructor.
  apply (set_interp_gunit_env_ext _ (set_env_extend (set_env_tail ρ') (set_entry_term κ x))); [exact Hc | intros [| s]; [exact (eq_sym Hl) | reflexivity] |].
  apply Hf. eapply set_mem_eq_r; [| exact Hx]. apply code_carrier_resp.
  exact (set_interp_functional T γ Hfn Hmods _ _ _ _ Ha' _ _ (set_env_rel_eq T γ _ _ _ Ht) Ha).
Qed.

(** Hence it relates to itself there. *)
Lemma set_unit_rel_unbind : forall Γ Δ κ X D, set_ctx T γ (ce_ass κ X :: Γ) -> ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κ X :: Γ ->
    set_modexp_rel T γ Γ (me_lit (gu_mk (Δ ++ [ce_ass κ X]) D)) (me_lit (gu_mk (Δ ++ [ce_ass κ X]) D)) ->
    set_modexp_rel T γ (ce_ass κ X :: Γ) (me_lit (gu_mk Δ D)) (me_lit (gu_mk Δ D)).
Proof.
  intros * HC Hc (F & _ & [HF _ _]). pose proof (set_unit_denotes_unbind _ _ _ _ _ _ HC Hc HF) as HG.
  exists (set_module_at_param F), (set_module_at_param F). constructor; [exact HG | exact HG |].
  intros ρ Hρ. exact (set_modexp_denotes_unique _ _ _ _ _ HG _ _ _ Hρ (set_modexp_denotes_exists _ _ _ _ _ HG _ Hρ)).
Qed.

Lemma set_params_evaluated_unbind : forall Γ Δ e l, set_params_evaluated T γ Γ (Δ ++ [e]) l -> set_params_evaluated T γ (e :: Γ) Δ l.
Proof.
  intros * H Δ1 κ A Δ2 ->. specialize (H Δ1 κ A (Δ2 ++ [e]) ltac:(rewrite <- List.app_assoc; reflexivity)).
  rewrite <- List.app_assoc in H. exact H.
Qed.

(** A valid literal over one more parameter is valid without it over the
    context extended. *)
Lemma set_valid_unit_unbind : forall Γ Δ κ X D, set_valid_unit T γ Γ (me_lit (gu_mk (Δ ++ [ce_ass κ X]) D)) ->
    set_valid_unit T γ (ce_ass κ X :: Γ) (me_lit (gu_mk Δ D)).
Proof.
  intros * HK. pose proof (set_valid_unit_wf T γ _ _ HK) as Hw.
  pose proof (proj1 (modexp_gen _ _ _ _ _ Hw)) as Hf; cbn [gen_m] in Hf.
  pose proof (unit_full_unabs _ _ _ _ _ _ Hf) as Hf1; cbn [List.app] in Hf1.
  pose proof (wf_me_lit _ _ _ _ _ (unit_eq_of_full _ _ _ _ Hf1)) as Hw1.
  pose proof (ctx_app_wf_tail _ _ _ _ (proj1 (unit_full_ctx _ _ _ _ _ Hf1))) as Hc.
  inversion HK as [| ? Δ0 Φ Φx Hb Hsub Hop | ? Δ0 E Hal HE]; subst;
    [exfalso; match goal with Hq : me_apps _ _ = me_lit _ |- _ => exact (me_apps_qname_not_lit _ _ _ Hq) end | |].
  - (* a body *)
    destruct Hb as [_ Hx HΔ [l Hl] HΓ HC Hs Hsh Hshx Hr Hro].
    rewrite <- !List.app_assoc in Hx, HC, Hs, Hro, Hsub, Hop; cbn [List.app] in Hx, HC, Hs, Hro, Hsub, Hop.
    pose proof (set_ctx_app_r T γ _ _ (set_ctx_app_r T γ _ _ HC)) as HC1.
    apply set_valid_unit_body with (Φx := Φx); [| exact Hsub | exact Hop].
    constructor; [exact Hw1 | exact Hx | exact (proj1 (proj1 (List.Forall_app _ _ _) HΔ)) | exists l; exact (set_params_evaluated_unbind _ _ _ _ Hl)
                 | exact HC1 | exact HC | exact Hs | exact Hsh | exact Hshx | exact (set_unit_rel_unbind _ _ _ _ _ HC1 Hc Hr) | exact Hro].
  - (* an alias *)
    destruct Hal as [_ HΔ [l Hl] HΓ HCΔ Hr Ht].
    rewrite <- List.app_assoc in HCΔ, Ht, HE; cbn [List.app] in HCΔ, Ht, HE.
    pose proof (set_ctx_app_r T γ _ _ HCΔ) as HC1.
    apply set_valid_unit_alias; [| exact HE].
    constructor; [exact Hw1 | exact (proj1 (proj1 (List.Forall_app _ _ _) HΔ)) | exists l; exact (set_params_evaluated_unbind _ _ _ _ Hl)
                 | exact HC1 | exact HCΔ | exact (set_unit_rel_unbind _ _ _ _ _ HC1 Hc Hr) | exact Ht].
Qed.

(** ** [β] *)

(** A literal given its outermost parameter has the proofness of the
    literal instantiated: an argument holds no slot. *)
Lemma unit_member_proofs_beta : forall κs Δ κ X D N ys x,
    unit_member_proofs γ κs (gu_mk (Δ ++ [ce_ass κ X]) D) ys x = unit_member_proofs γ κs (gunit_sub (gu_mk Δ D) (sb_extend sb_id (se_exp N))) ys x.
Proof.
  intros. rewrite unit_member_proofs_unbind. symmetry.
  apply (proj2 (unit_member_proofs_sub_all γ)). intros [| s] ys' x'; reflexivity.
Qed.

(** [set_app_reduct_with Γ K N Rm K' RK' Rm']: the unit [K], of the module
    part [Rm], given the argument [N], is the valid unit [K'], which
    denotes [RK'] of the module part [Rm'] that [Rm] at [N] is. *)
Record set_app_reduct_with (Γ : ctx) (K : modexp) (N : exp) (Rm : mdesc) (K' : modexp) (RK' Rm' : mdesc) : Prop :=
  { (** The module part given the argument *)
    set_app_reduct_at : mdesc_at Rm N = Some Rm'
    (** The application denotes [K']'s module *)
  ; set_app_reduct_rel : set_modexp_rel T γ Γ (me_app K N) K'
    (** [K'] is a valid unit *)
  ; set_app_reduct_valid : set_valid_unit T γ Γ K'
    (** It denotes [RK'] *)
  ; set_app_reduct_desc : mdenote gc_deps gc_stack Γ K' RK'
    (** Of the module part [Rm'] *)
  ; set_app_reduct_mod : mdesc_mod RK' = Some Rm'
    (** It has [K]'s proofness, which is the application's *)
  ; set_app_reduct_proofs : forall κs, set_slots_coherent γ Γ κs -> forall ys x,
      modexp_member_proofs γ κs K ys x = modexp_member_proofs γ κs K' ys x }.

(** A valid literal with an outermost parameter given an argument is the
    literal instantiated. *)
Lemma set_unit_beta_reduct : forall Γ Δ κ X D N R0, set_valid_unit T γ Γ (me_lit (gu_mk (Δ ++ [ce_ass κ X]) D)) ->
    mdenote gc_deps gc_stack Γ (me_lit (gu_mk (Δ ++ [ce_ass κ X]) D)) R0 ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ N : X -> set_exp_eq T γ Γ X N N ->
    exists R', set_app_reduct_with Γ (me_lit (gu_mk (Δ ++ [ce_ass κ X]) D)) N R0
                 (me_lit (gunit_sub (gu_mk Δ D) (sb_extend sb_id (se_exp N)))) R' R'.
Proof.
  intros * HKU HR0 HNw (FX & FN & _ & [HFX HFN _ _ HNm]).
  pose proof (set_valid_unit_ctx T γ _ _ HKU) as HΓ.
  destruct (set_valid_unit_rel _ _ HKU) as (FU & _ & [HFU _ _]).
  pose proof (set_valid_unit_unbind _ _ _ _ _ HKU) as HKI.
  pose proof (presup_modexp_eq_ctx (set_valid_unit_wf T γ _ _ HKI)) as Hc.
  pose proof (set_valid_unit_ctx T γ _ _ HKI) as HCe.
  (* the argument instantiates the parameter *)
  destruct (ctx_decomp_kind Hc) as (Srt & HS & HX).
  pose proof (set_gsub_single T γ _ _ _ _ _ _ HΓ (wf_sub_single _ _ _ _ _ _ _ HX HS HNw) HFX HFN HNm) as Hg.
  assert (Hs : set_moves_with T γ nil (ce_ass κ X :: Γ) Γ (sb_extend sb_id (se_exp N)) (fun ρ => set_env_extend ρ (set_entry_term κ (FN ρ))))
    by (constructor; [exact Hg | exact HΓ | exact HCe | exact HΓ | exact Hc]).
  assert (Hκ : set_sub_slots_coherent γ (ce_ass κ X :: Γ) Γ (sb_extend sb_id (se_exp N))).
  { intros κs Hκs. split; [| intros U0 HU0; discriminate].
    eapply set_slots_coherent_resp with (κs := κs); [intros s ys x; reflexivity | exact Hκs]. }
  pose proof (proj1 (set_valid_unit_modexp_moved T γ Hfn Hmods Hgw) _ _ HKI _ _ _ Hs Hκ) as HK'.
  change (set_valid_unit T γ Γ (me_lit (gunit_sub (gu_mk Δ D) (sb_extend sb_id (se_exp N))))) in HK'.
  (* the denotations *)
  pose proof (set_unit_denotes_unbind _ _ _ _ _ _ HCe Hc HFU) as HG.
  pose proof (set_modexp_denotes_moved T γ Hfn Hmods _ _ _ _ _ _ _ Hs HG) as HGm.
  change (set_modexp_denotes T γ Γ (me_lit (gunit_sub (gu_mk Δ D) (sb_extend sb_id (se_exp N))))
            (fun ρ => set_module_at_param FU (set_env_extend ρ (set_entry_term κ (FN ρ))))) in HGm.
  assert (HFL : set_modexp_denotes T γ Γ (me_app (me_lit (gu_mk (Δ ++ [ce_ass κ X]) D)) N) (fun ρ => apply_module (FU ρ) (FN ρ))).
  { apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
    exact (set_interp_me_app T γ _ _ _ _ _ _ (set_modexp_denotes_exists _ _ _ _ _ HFU _ Hρ) (set_denotes_exists _ _ _ _ _ HFN _ Hρ)). }
  assert (Hrel : set_modexp_rel T γ Γ (me_app (me_lit (gu_mk (Δ ++ [ce_ass κ X]) D)) N) (me_lit (gunit_sub (gu_mk Δ D) (sb_extend sb_id (se_exp N))))).
  { exists (fun ρ => apply_module (FU ρ) (FN ρ)), (fun ρ => set_module_at_param FU (set_env_extend ρ (set_entry_term κ (FN ρ)))).
    constructor; [exact HFL | exact HGm |]. intros ρ Hρ.
    pose proof (set_modexp_denotes_exists _ _ _ _ _ HFU _ Hρ) as Hm. inversion Hm; subst.
    match goal with Hn : set_interp_gunit _ _ _ _ _ _ |- _ =>
      destruct (set_unit_params_unbind _ _ _ _ _ _ _ Hc Hn) as (a & P & f & [Heq Ha HP Hf]) end.
    pose proof (set_denotes_exists _ _ _ _ _ HFX _ Hρ) as HXa.
    assert (Hv : set_mem (FN ρ) (code_carrier a)).
    { eapply set_mem_eq_r; [| exact (HNm _ Hρ)]. apply code_carrier_resp.
      exact (set_interp_functional T γ Hfn Hmods _ _ _ _ HXa _ _ (set_env_rel_eq T γ _ _ _ Hρ) Ha). }
    pose proof (Hf _ Hv) as Hfv.
    assert (Hρe : set_env_in T γ (ce_ass κ X :: Γ) (set_env_extend ρ (set_entry_term κ (FN ρ))))
      by exact (set_env_in_extend_ass T γ _ _ _ _ _ _ Hρ HXa (HNm _ Hρ)).
    pose proof (set_modexp_denotes_unique _ _ _ _ _ HG _ _ _ Hρe (set_interp_me_lit T γ _ _ _ _ Hfv)) as HGf.
    unfold set_module_at_param in HGf |- *. change (set_env_tail (set_env_extend ρ (set_entry_term κ (FN ρ)))) with ρ in HGf |- *.
    rewrite Heq in HGf |- *. cbn [apply_module set_env_extend set_entry_value] in HGf |- *.
    apply set_module_eq_cond_l; [exact Hv | |].
    - exact HGf.
    - intros ys x. rewrite HP.
      rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (set_interp_member_proofs_all T γ))))) _ _ _ _ Hfv ys x).
      rewrite unit_member_proofs_unbind.
      apply (proj1 (proj2 (unit_member_proofs_resp_all γ))). intros s ys' x'. symmetry. apply env_slot_proofs_extend_term. }
  (* the syntactic descriptions *)
  pose proof (set_valid_unit_wf T γ _ _ HKU) as HwU.
  pose proof (unit_eq_of_full _ _ _ _ (proj1 (modexp_gen _ _ _ _ _ HwU))) as HUU.
  destruct (mdenote_beta _ _ _ _ _ _ _ N HUU _ (mdenote_lit_inv _ _ _ _ _ HR0)) as (R' & HmL & HmK & HR').
  exists R'. constructor; [| exact Hrel | exact HK' | exact HmK | exact HR' |].
  - inversion HmL; subst; try match goal with Hq : mod_qname _ = Some _ |- _ => cbn in Hq; discriminate end.
    match goal with Hm1 : mdenote _ _ _ (me_lit _) ?R1, Ha : mdesc_at ?R1 N = Some _ |- _ =>
      rewrite (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ HR0 _ Hm1); exact Ha end.
  - intros κs _ ys x. cbn [modexp_member_proofs]. apply unit_member_proofs_beta.
Qed.

(** A literal body or alias given its outermost parameter is the literal
    instantiated. *)
Lemma set_rule_me_beta : forall Γ Δ κ X D N, set_ctx T γ Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_app (me_lit (gu_mk (Δ ++ [ce_ass κ X]) D)) N ≈ me_lit (gunit_sub (gu_mk Δ D) (sb_extend sb_id (se_exp N))) ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ N : X ->
    set_unit_eq T γ Γ (gu_mk (Δ ++ [ce_ass κ X]) D) (gu_mk (Δ ++ [ce_ass κ X]) D) -> set_exp_eq T γ Γ X N N ->
    set_modexp_eq T γ Γ (me_app (me_lit (gu_mk (Δ ++ [ce_ass κ X]) D)) N) (me_lit (gunit_sub (gu_mk Δ D) (sb_extend sb_id (se_exp N)))).
Proof.
  intros * _ Hβ HNw (FU & _ & [_ _ _ HKU _]) HN.
  destruct (me_denotes _ _ _ _ _ (set_valid_unit_wf T γ _ _ HKU)) as (R0 & _ & HR0 & _).
  destruct (set_unit_beta_reduct _ _ _ _ _ _ _ HKU HR0 HNw HN) as (R' & [Hat Hrel HK' HmK HR' Hpr]).
  apply set_modexp_eq_of_rel; [exact Hrel | | exact (set_valid_modexp_of_unit _ _ HK')].
  apply (set_valid_modexp_intro T γ _ _ (me_lit (gunit_sub (gu_mk Δ D) (sb_extend sb_id (se_exp N)))) R' R' R'); [| exact HK'].
  constructor; [exact (wf_modexp_eq_refl_left Hβ) | eapply mdenote_app; [exact HR0 | exact Hat] | exact HR' | exact Hrel | exact HmK | exact HR' |].
  exact Hpr.
Qed.

(** ** Applications *)

Lemma set_modexp_rel_trans : forall Γ H H' H'', set_modexp_rel T γ Γ H H' -> set_modexp_rel T γ Γ H' H'' ->
    set_modexp_rel T γ Γ H H''.
Proof.
  intros * (F & F' & [HF HF' E]) (G & G' & [HG HG' E']). exists F, G'. constructor; [exact HF | exact HG' |].
  intros ρ Hρ. eapply set_module_eq_trans; [exact (E _ Hρ) |]. eapply set_module_eq_trans; [| exact (E' _ Hρ)].
  exact (set_modexp_denotes_unique _ _ _ _ _ HG _ _ _ Hρ (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ)).
Qed.

(** Related module expressions given one argument are related. *)
Lemma set_modexp_rel_app : forall Γ H H' N FN, set_ctx T γ Γ -> set_modexp_rel T γ Γ H H' -> set_denotes T γ Γ N FN ->
    set_modexp_rel T γ Γ (me_app H N) (me_app H' N).
Proof.
  intros * HΓ (F & F' & [HF HF' E]) HN.
  exists (fun ρ => apply_module (F ρ) (FN ρ)), (fun ρ => apply_module (F' ρ) (FN ρ)). constructor.
  - apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
    exact (set_interp_me_app T γ _ _ _ _ _ _ (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ) (set_denotes_exists _ _ _ _ _ HN _ Hρ)).
  - apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
    exact (set_interp_me_app T γ _ _ _ _ _ _ (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ) (set_denotes_exists _ _ _ _ _ HN _ Hρ)).
  - intros ρ Hρ. apply apply_module_resp; [exact (E _ Hρ) | apply set_eq_refl].
Qed.

(** A valid unit given an argument of the outermost parameter its module
    part takes is a valid unit: a filed module records the argument, a
    literal is instantiated, an alias with no parameter is its target
    given the argument.  A valid module expression given one is valid. *)
Theorem set_valid_unit_app_all :
  (forall Γ K, set_valid_unit T γ Γ K -> forall RK Rm Tl B T1 Srt N, mdenote gc_deps gc_stack Γ K RK -> mdesc_mod RK = Some Rm ->
     mdesc_tele Rm = Some Tl -> tele_view Tl = Some (B, T1) -> evaluated_sort Srt -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ B : Srt ->
     (exists Srt', evaluated_sort Srt' /\ set_exp_eq T γ Γ Srt' B B) -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ N : B -> set_exp_eq T γ Γ B N N ->
     exists K' RK' Rm', set_app_reduct_with Γ K N Rm K' RK' Rm') /\
  (forall Γ H, set_valid_modexp T γ Γ H -> forall R Tl B T1 Srt N, mdenote gc_deps gc_stack Γ H R -> mdesc_mod_tele R = Some Tl ->
     tele_view Tl = Some (B, T1) -> evaluated_sort Srt -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ B : Srt ->
     (exists Srt', evaluated_sort Srt' /\ set_exp_eq T γ Γ Srt' B B) -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ N : B -> set_exp_eq T γ Γ B N N ->
     set_valid_modexp T γ Γ (me_app H N)).
Proof.
  apply (set_valid_unit_modexp_ind T γ).
  - (* a filed module at arguments: the argument recorded *)
    intros Γ p T0 Φ Tr Tf Ns Hw Hgl HΓ Hs RK Rm Tl B T1 Srt N Hm Hmod Ht Hv HSrt HBw HBs HNw HN.
    destruct (filed_denote _ _ Hgw _ _ _ Γ Ns Hgl) as (R1 & Hm1 & Hmod1).
    rewrite (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ Hm _ Hm1), Hmod1 in Hmod; injection Hmod as <-.
    assert (HmtK : mdesc_mod_tele R1 = Some Tl) by (unfold mdesc_mod_tele; rewrite Hmod1; exact Ht).
    assert (HwN : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_app (me_apps (qname_mod p) Ns) N ≈ me_app (me_apps (qname_mod p) Ns) N)
      by (eapply app_wf; [exact Hw | exact Hm1 | exact HmtK | exact Hv | exact HSrt | exact HBw | exact HNw]).
    pose proof Hs as [-> Hlen HTa2 HTs2 HNs HNr].
    cbn [mdesc_tele] in Ht. rewrite length_app in Ht.
    destruct (Nat.leb_spec (List.length Ns) (List.length Tr + List.length Tf)) as [_ | Hgt]; [| lia].
    injection Ht as <-.
    replace (List.length Tr + List.length Tf - List.length Ns) with (List.length Tr) in Hv by lia.
    rewrite List.firstn_app, List.firstn_all, Nat.sub_diag in Hv; cbn [List.firstn] in Hv; rewrite !List.app_nil_r in Hv.
    pose proof (set_filed_mod_tele_assumptions T γ _ _ _ (set_gctx_ok_filed T γ Hok _ _ _ Hgl)) as HTa.
    pose proof (set_filed_mod_tele_scoped T γ _ _ _ (set_gctx_ok_filed T γ Hok _ _ _ Hgl)) as HTs.
    apply List.Forall_app in HTa as [HTa1 _].
    destruct (List.exists_last (l := Tr)) as (L & e & ->); [intros ->; cbn in Hv; discriminate |].
    apply List.Forall_app in HTa1 as [_ He]; inversion He as [| ? ? (κ & A & ->) _]; subst.
    rewrite tele_sub_app in Hv; cbn [tele_sub List.length sb_qn centry_sub] in Hv.
    rewrite tele_view_last in Hv; injection Hv as <- <-.
    rewrite <- List.app_assoc in Hgl, HTs |- *. cbn [List.app] in Hgl, HTs |- *.
    (* the argument fills the next parameter *)
    assert (Hti : tele_insts (ce_ass κ A :: Tf) sb_id (Ns ++ [N]) = tele_insts Tf sb_id Ns ++ [exp_sub A (sb_of_list sb_id Ns)])
      by (change (ce_ass κ A :: Tf) with ([ce_ass κ A] ++ Tf); rewrite tele_insts_app by (try exact HTa2; lia); reflexivity).
    assert (HlT : List.length (tele_insts Tf sb_id Ns) = List.length Ns) by (rewrite length_tele_insts by exact HTa2; lia).
    assert (Hs' : set_args_valid T γ Γ (L ++ ce_ass κ A :: Tf) L (ce_ass κ A :: Tf) (Ns ++ [N])).
    { constructor; [reflexivity | cbn; rewrite List.length_app; cbn; lia | constructor; [eexists; eexists; reflexivity | exact HTa2]
                   | exact (proj2 (proj1 (ctx_scoped_app_iff _ _) HTs)) | |].
      - intros k N0 B0 HN0 HB0. rewrite Hti in HB0.
        destruct (Nat.lt_ge_cases k (List.length Ns)) as [Hk | Hk].
        + rewrite List.nth_error_app1 in HN0, HB0 by lia. exact (HNs _ _ _ HN0 HB0).
        + rewrite List.nth_error_app2 in HN0, HB0 by lia. rewrite HlT in HB0.
          destruct (k - List.length Ns) as [| k']; cbn in HN0, HB0; [injection HN0 as <-; injection HB0 as <-; exact HN |].
          destruct k'; discriminate.
      - intros k B0 HB0. rewrite Hti in HB0.
        destruct (Nat.lt_ge_cases k (List.length Ns)) as [Hk | Hk].
        + rewrite List.nth_error_app1 in HB0 by lia. exact (HNr _ _ HB0).
        + rewrite List.nth_error_app2 in HB0 by lia. rewrite HlT in HB0.
          destruct (k - List.length Ns) as [| k']; cbn in HB0; [injection HB0 as <-; exact HBs |].
          destruct k'; discriminate. }
    destruct (filed_denote _ _ Hgw _ _ _ Γ (Ns ++ [N]) Hgl) as (R2 & Hm2 & Hmod2).
    assert (HK' : set_valid_unit T γ Γ (me_apps (qname_mod p) (Ns ++ [N]))).
    { apply (set_valid_unit_filed T γ Γ p (L ++ ce_ass κ A :: Tf) Φ L (ce_ass κ A :: Tf));
        [rewrite me_apps_snoc; exact HwN | exact Hgl | exact HΓ | exact Hs']. }
    exists (me_apps (qname_mod p) (Ns ++ [N])), R2, (mdesc_closed nil p (L ++ ce_ass κ A :: Tf) Φ (Ns ++ [N])).
    constructor; [| | exact HK' | exact Hm2 | exact Hmod2 |].
    + cbn. rewrite (List.map_ext _ (fun M => M) exp_sub_id), List.map_id. reflexivity.
    + pose proof (set_valid_unit_rel _ _ HK') as Hr. rewrite me_apps_snoc in Hr |- *. exact Hr.
    + intros κs _ ys x. rewrite me_apps_snoc. reflexivity.
  - (* a body: β *)
    intros Γ Δ Φ Φx Hb Hsub _ Hop _ RK Rm Tl B T1 Srt N Hm Hmod Ht Hv HSrt HBw HBs HNw HN.
    pose proof (set_valid_unit_body T γ _ _ _ _ Hb Hsub Hop) as HK0.
    pose proof Hm as Hm0. apply mdenote_lit_inv in Hm.
    rewrite (mdesc_is_mod_mod _ (udenote_is_mod _ _ _ _ _ _ Hm)) in Hmod; injection Hmod as <-.
    inversion Hm; subst.
    match goal with Hb0 : mdesc_body _ _ _ _ _ = Some _ |- _ => cbn in Hb0; injection Hb0 as <- end.
    cbn in Ht; injection Ht as <-.
    destruct (tele_view_ass _ _ _ (set_body_ok_params T γ _ _ _ _ Hb) Hv) as [κ ->].
    destruct (set_unit_beta_reduct _ _ _ _ _ _ _ HK0 Hm0 HNw HN) as (R' & HR').
    exact (ex_intro _ _ (ex_intro _ R' (ex_intro _ R' HR'))).
  - (* an alias *)
    intros Γ Δ E Hal HE IHE RK Rm Tl B T1 Srt N Hm Hmod Ht Hv HSrt HBw HBs HNw HN.
    pose proof (set_valid_unit_alias T γ _ _ _ Hal HE) as HK0.
    pose proof Hm as Hm0. apply mdenote_lit_inv in Hm.
    rewrite (mdesc_is_mod_mod _ (udenote_is_mod _ _ _ _ _ _ Hm)) in Hmod; injection Hmod as <-.
    inversion Hm as [| ? ? ? E0 RE Rem HmE HmodE]; subst.
    destruct (mdesc_tele_up_tele _ _ _ (mdesc_mod_is_mod _ _ HmodE) Ht) as (T0 & Ht0 & ->).
    destruct Δ as [| e Δ'] using List.rev_ind.
    + (* with no parameter: its target given the argument *)
      cbn [List.app] in *. rewrite List.app_nil_r in Hv. rewrite mdesc_up_nil in *.
      assert (HmtE : mdesc_mod_tele RE = Some T0) by (unfold mdesc_mod_tele; rewrite HmodE; exact Ht0).
      pose proof (IHE _ _ _ _ _ _ HmE HmtE Hv HSrt HBw HBs HNw HN) as HsN.
      inversion HsN as [? ? KN RN RNm RKN [HwN HmN HmodN HNK HmKN HmodKN HprN] HKNv]; subst.
      inversion HmN; subst; try (match goal with Hq : mod_qname (me_app _ _) = Some _ |- _ => cbn in Hq; discriminate end).
      match goal with Hm1 : mdenote _ _ _ E ?R1, Ha1 : mdesc_at ?R1 N = Some RN |- _ =>
        pose proof (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ Hm1 _ HmE) as ->; rename Ha1 into HaN end.
      destruct (mdesc_mod_at _ _ _ _ HmodE HaN) as (Rm' & HaRm & HmodRN).
      rewrite HmodRN in HmodN; injection HmodN as <-.
      destruct Hal as [_ _ _ HΓ _ _ HEE]. cbn [List.app] in HEE.
      destruct HN as (FB & FN & FN' & HNw').
      exists KN, RKN, Rm'. constructor; [exact HaRm | | exact HKNv | exact HmKN | exact HmodKN |].
      * eapply set_modexp_rel_trans; [| exact HNK].
        exact (set_modexp_rel_app _ _ _ _ _ HΓ (set_alias0_rel _ _ HΓ HEE) (set_exp_eq_left _ _ _ _ _ _ _ _ _ HNw')).
      * intros κs Hκ ys x. exact (HprN κs Hκ ys x).
    + (* β *)
      clear IHΔ'. pose proof (set_alias_ok_params T γ _ _ _ Hal) as HΔ.
      apply List.Forall_app in HΔ as [_ He]. inversion He as [| ? ? (κ & X & ->) _]; subst.
      rewrite List.app_assoc, tele_view_last in Hv. injection Hv as <- <-.
      destruct (set_unit_beta_reduct _ _ _ _ _ _ _ HK0 Hm0 HNw HN) as (R' & HR').
      exact (ex_intro _ _ (ex_intro _ R' (ex_intro _ R' HR'))).
  - (* a module expression equal to a valid unit: as the unit does *)
    intros Γ H K R Rm RK [HwH HmH HmodH HHK HmK HmodK Hpr] HK IHK R0 Tl B T1 Srt N Hm Ht Hv HSrt HBw HBs HNw HN.
    pose proof (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ Hm _ HmH) as ->.
    pose proof Ht as HmtR. unfold mdesc_mod_tele in Ht; rewrite HmodH in Ht.
    destruct (IHK _ _ _ _ _ _ _ HmK HmodK Ht Hv HSrt HBw HBs HNw HN) as (K' & RK' & Rm' & [Ha HKN HK' HmK' HmodK' Hpr']).
    destruct (mdesc_mod_at_inv _ _ _ _ HmodH Ha) as (R' & HaR & HmodR').
    destruct HN as (FB & FN & FN' & HNw').
    apply (set_valid_modexp_intro T γ _ _ K' R' Rm' RK'); [| exact HK'].
    constructor; [| eapply mdenote_app; [exact Hm | exact HaR] | exact HmodR' | | exact HmK' | exact HmodK' |].
    + eapply app_wf; [exact HwH | exact Hm | exact HmtR | exact Hv | exact HSrt | exact HBw | exact HNw].
    + eapply set_modexp_rel_trans; [| exact HKN].
      exact (set_modexp_rel_app _ _ _ _ _ (set_valid_unit_ctx T γ _ _ HK) HHK (set_exp_eq_left _ _ _ _ _ _ _ _ _ HNw')).
    + intros κs Hκ ys x. exact (eq_trans (Hpr κs Hκ ys x) (Hpr' κs Hκ ys x)).
Qed.

(** Equal module expressions given equal arguments are equal. *)
Lemma set_rule_me_app : forall Γ H H' N N' R Tl B T1 Srt R' Tl' B' T1' Srt', set_ctx T γ Γ ->
    set_modexp_eq T γ Γ H H' ->
    mdenote gc_deps gc_stack Γ H R -> mdesc_mod_tele R = Some Tl -> tele_view Tl = Some (B, T1) ->
    evaluated_sort Srt -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ B : Srt -> set_exp_eq T γ Γ Srt B B ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ N : B -> set_exp_eq T γ Γ B N N -> set_exp_eq T γ Γ B N N' ->
    mdenote gc_deps gc_stack Γ H' R' -> mdesc_mod_tele R' = Some Tl' -> tele_view Tl' = Some (B', T1') ->
    evaluated_sort Srt' -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ B' : Srt' -> set_exp_eq T γ Γ Srt' B' B' ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ N' : B' -> set_exp_eq T γ Γ B' N' N' ->
    set_modexp_eq T γ Γ (me_app H N) (me_app H' N').
Proof.
  intros * HΓ (F & F' & [HF HF' E Hv Hv']) Hm Ht HV HS HBw HB HNw HN (FB & FN & FN' & [_ HFN HFN' EN _])
    Hm' Ht' HV' HS' HBw' HB' HNw' HN'.
  exists (fun ρ => apply_module (F ρ) (FN ρ)), (fun ρ => apply_module (F' ρ) (FN' ρ)). constructor.
  - apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
    exact (set_interp_me_app T γ _ _ _ _ _ _ (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ) (set_denotes_exists _ _ _ _ _ HFN _ Hρ)).
  - apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
    exact (set_interp_me_app T γ _ _ _ _ _ _ (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ) (set_denotes_exists _ _ _ _ _ HFN' _ Hρ)).
  - intros ρ Hρ. exact (apply_module_resp _ _ (E _ Hρ) _ _ (EN _ Hρ)).
  - exact (proj2 set_valid_unit_app_all _ _ Hv _ _ _ _ _ _ Hm Ht HV HS HBw (ex_intro _ _ (conj HS HB)) HNw HN).
  - exact (proj2 set_valid_unit_app_all _ _ Hv' _ _ _ _ _ _ Hm' Ht' HV' HS' HBw' (ex_intro _ _ (conj HS' HB')) HNw' HN').
Qed.

End ModuleCases.
