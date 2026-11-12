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
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas DescTyping LookupSound Presup.
Import ListNotations.

Section ModuleCases.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.
  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq (global_module γ q) (global_module γ q).
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

(** Terms each of which denotes have their values as a function of the
    environment. *)
Lemma set_denotes_list : forall Γ Ns, (forall k N, List.nth_error Ns k = Some N -> exists FN, set_denotes T γ Γ N FN) ->
    exists Fs, forall ρ, set_env_in T γ Γ ρ -> set_interp_list T γ Γ ρ Ns (Fs ρ).
Proof.
  intros Γ Ns. induction Ns as [| N Ns IH]; intros HN; [exists (fun _ => nil); intros; constructor |].
  destruct (HN 0 N eq_refl) as (FN & HFN).
  destruct (IH (fun k N' HN' => HN (S k) N' HN')) as (Fs & HFs).
  exists (fun ρ => FN ρ :: Fs ρ). intros ρ Hρ. constructor; [exact (set_denotes_exists _ _ _ _ _ HFN _ Hρ) | exact (HFs _ Hρ)].
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
    destruct (set_denotes_list _ _ HN) as (Fs & HFs).
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
Lemma set_modexp_rel_left : forall Γ H H', set_modexp_rel T γ Γ H H' -> set_modexp_rel T γ Γ H H.
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
  exact (set_modexp_eq_of_rel _ _ _ (set_modexp_rel_left _ _ _ (set_slot_rel _ _ _ Hl HC Hc)) Hv Hv).
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

End ModuleCases.
