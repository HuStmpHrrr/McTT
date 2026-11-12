(** * The Set Rules of Extensions and Units

    Equal extensions relate the same environments.  Each side's entries
    are read in its own context, and a term has the same value read in two
    contexts extending one context by equal extensions
    ([set_interp_functional_ext]): so an entry of one side relates the
    entries the other's relates. *)

From Stdlib Require Import String List Lia.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Respects ContextRelation JudgmentSubstitution.
From Mctt.Core.SetModel.Interpretation.Global Require Import Model.
From Mctt.Core.SetModel.Cases Require Import ValidUnit MemberTypes ModuleCases Unit.
From Mctt.Core.Syntactic Require Import Syntax Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural.
From Mctt.Core.Syntactic.System.Global Require Import Presup DescTyping MemberLemmas.
From Mctt.Core.SetModel.Interpretation Require Import Substitution.
From Mctt.Core.Syntactic.System Require Import Scoping.
From Mctt.Core.Completeness.Modules Require Import ValidUnit Body.
Import ListNotations.

Section Units.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.
  Hypothesis Hfn : fn_kinds_unique_ext.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).
  (** The valuation models the global context *)
  Hypothesis Hok : set_gctx_ok T γ.

(** ** Values Read in Equal Extensions *)

Lemma ctx_ext_equal_of_ext_eq : forall Γ Ψ Ψ', gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> ctx_ext_equal (Ψ ++ Γ) (Ψ' ++ Γ).
Proof. intros * H. exists Γ, Ψ, Ψ'. constructor; [reflexivity | reflexivity | exact H]. Qed.

(** A term denotes the same in the two contexts. *)
Lemma set_denotes_across : forall Γ Ψ Ψ' M F F' ρ, gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    set_denotes T γ (Ψ ++ Γ) M F -> set_denotes T γ (Ψ' ++ Γ) M F' ->
    set_env_in T γ (Ψ ++ Γ) ρ -> set_env_in T γ (Ψ' ++ Γ) ρ -> set_eq (F ρ) (F' ρ).
Proof.
  intros * HΨ HF HF' Hρ Hρ'.
  exact (set_interp_functional_ext T γ Hfn Hmods _ _ _ _ (set_denotes_exists _ _ _ _ _ HF _ Hρ) _ _ _
           (ctx_ext_equal_of_ext_eq _ _ _ HΨ) (set_env_rel_eq _ _ _ _ _ Hρ) (set_denotes_exists _ _ _ _ _ HF' _ Hρ')).
Qed.

(** A module expression the same. *)
Lemma set_modexp_denotes_across : forall Γ Ψ Ψ' H F F' ρ, gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    set_modexp_denotes T γ (Ψ ++ Γ) H F -> set_modexp_denotes T γ (Ψ' ++ Γ) H F' ->
    set_env_in T γ (Ψ ++ Γ) ρ -> set_env_in T γ (Ψ' ++ Γ) ρ -> set_module_eq γ (F ρ) (F' ρ).
Proof.
  intros * HΨ HF HF' Hρ Hρ'.
  exact (set_interp_modexp_functional_ext T γ Hfn Hmods _ _ _ _ (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ) _ _ _
           (ctx_ext_equal_of_ext_eq _ _ _ HΨ) (set_env_rel_eq _ _ _ _ _ Hρ) (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ')).
Qed.

(** ** Extending Equal Extensions *)

(** Equal extensions extended by entries that relate the same entries are
    equal. *)
Lemma set_ext_eq_extend : forall Γ Ψ Ψ' ce ce', set_ext_eq_with T γ Γ Ψ Ψ' ->
    set_entry_valid T γ (Ψ ++ Γ) ce -> set_entry_valid T γ (Ψ' ++ Γ) ce' ->
    (forall ρ e e', set_env_in T γ (Ψ ++ Γ) ρ -> set_env_in T γ (Ψ' ++ Γ) ρ ->
       set_entry_rel T γ (Ψ ++ Γ) ρ ce e e' <-> set_entry_rel T γ (Ψ' ++ Γ) ρ ce' e e') ->
    set_ext_eq_with T γ Γ (ce :: Ψ) (ce' :: Ψ').
Proof.
  intros * [HL HR Hrel] Hv Hv' Hiff. constructor; [split; assumption | split; assumption |].
  destruct (set_env_rel_per _ _ _ HL) as [Hsym Htrans].
  assert (Hin : forall ρ1 ρ2, set_env_rel T γ (Ψ ++ Γ) ρ1 ρ2 -> set_env_in T γ (Ψ ++ Γ) ρ1 /\ set_env_in T γ (Ψ' ++ Γ) ρ1).
  { intros ρ1 ρ2 H. assert (H1 : set_env_in T γ (Ψ ++ Γ) ρ1) by (eapply Htrans; [exact H | apply Hsym; exact H]).
    split; [exact H1 | apply Hrel; exact H1]. }
  intros ρ ρ'. cbn [List.app set_env_rel]. split; intros [Ht He].
  - destruct (Hin _ _ Ht) as [H1 H2]. split; [apply Hrel; exact Ht | apply (Hiff _ _ _ H1 H2); exact He].
  - assert (Ht' : set_env_rel T γ (Ψ ++ Γ) (set_env_tail ρ) (set_env_tail ρ')) by (apply Hrel; exact Ht).
    destruct (Hin _ _ Ht') as [H1 H2]. split; [exact Ht' | apply (Hiff _ _ _ H1 H2); exact He].
Qed.

(** An assumption below a supertype and above a subtype relates the same
    entries as one of the other type. *)
Lemma set_entry_rel_ass_iff : forall Γ Ψ Ψ' κ A A' FA FA' FX FX' FY FY' ρ e e', gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    set_denotes T γ (Ψ ++ Γ) A FA -> set_denotes T γ (Ψ' ++ Γ) A' FA' ->
    set_subtyp_with T γ (Ψ ++ Γ) A A' FX FX' -> set_subtyp_with T γ (Ψ ++ Γ) A' A FY FY' ->
    set_env_in T γ (Ψ ++ Γ) ρ -> set_env_in T γ (Ψ' ++ Γ) ρ ->
    set_entry_rel T γ (Ψ ++ Γ) ρ (ce_ass κ A) e e' <-> set_entry_rel T γ (Ψ' ++ Γ) ρ (ce_ass κ A') e e'.
Proof.
  intros * HΨ HA HA' [HX HX' Hs] [HY HY' Hs'] Hρ Hρ'. cbn [set_entry_rel]. split.
  - intros (x & x' & a & [E1 E2 Ha Hx Ex]). exists x, x', (FA' ρ).
    constructor; [exact E1 | exact E2 | exact (set_denotes_exists _ _ _ _ _ HA' _ Hρ') | | exact Ex].
    eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_across _ _ _ _ _ _ _ HΨ HX' HA' Hρ Hρ') |].
    apply Hs; [exact Hρ |].
    eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_unique _ _ _ _ _ HX _ _ _ Hρ Ha) | exact Hx].
  - intros (x & x' & a & [E1 E2 Ha Hx Ex]). exists x, x', (FA ρ).
    constructor; [exact E1 | exact E2 | exact (set_denotes_exists _ _ _ _ _ HA _ Hρ) | | exact Ex].
    eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HY' HA Hρ) |].
    apply Hs'; [exact Hρ |]. eapply set_mem_eq_r; [apply code_carrier_resp | exact Hx].
    eapply set_eq_trans; [exact (set_denotes_unique _ _ _ _ _ HA' _ _ _ Hρ' Ha) |].
    apply set_eq_sym. exact (set_denotes_across _ _ _ _ _ _ _ HΨ HY HA' Hρ Hρ').
Qed.

(** A definition relates the same entries as one of an equal body. *)
Lemma set_entry_rel_def_iff : forall Γ Ψ Ψ' A A' M M' FA FM FM' FM2 ρ e e', gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    set_exp_eq_with T γ (Ψ ++ Γ) A M M' FA FM FM' -> set_denotes T γ (Ψ' ++ Γ) M' FM2 ->
    set_env_in T γ (Ψ ++ Γ) ρ -> set_env_in T γ (Ψ' ++ Γ) ρ ->
    set_entry_rel T γ (Ψ ++ Γ) ρ (ce_def A M) e e' <-> set_entry_rel T γ (Ψ' ++ Γ) ρ (ce_def A' M') e e'.
Proof.
  intros * HΨ [_ HM HM' EM _] HM2 Hρ Hρ'.
  assert (E : set_eq (FM ρ) (FM2 ρ))
    by (eapply set_eq_trans; [apply EM; exact Hρ | exact (set_denotes_across _ _ _ _ _ _ _ HΨ HM' HM2 Hρ Hρ')]).
  cbn [set_entry_rel]. split.
  - intros (r & v & v' & w & [E1 E2 Hw Ev Ev']). pose proof (set_denotes_unique _ _ _ _ _ HM _ _ _ Hρ Hw) as Ew.
    exists r, v, v', (FM2 ρ). constructor; [exact E1 | exact E2 | exact (set_denotes_exists _ _ _ _ _ HM2 _ Hρ') | |].
    + eapply set_eq_trans; [exact Ev | eapply set_eq_trans; [exact Ew | exact E]].
    + eapply set_eq_trans; [exact Ev' | eapply set_eq_trans; [exact Ew | exact E]].
  - intros (r & v & v' & w & [E1 E2 Hw Ev Ev']). pose proof (set_denotes_unique _ _ _ _ _ HM2 _ _ _ Hρ' Hw) as Ew.
    exists r, v, v', (FM ρ). constructor; [exact E1 | exact E2 | exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) | |].
    + eapply set_eq_trans; [exact Ev | eapply set_eq_trans; [exact Ew | apply set_eq_sym; exact E]].
    + eapply set_eq_trans; [exact Ev' | eapply set_eq_trans; [exact Ew | apply set_eq_sym; exact E]].
Qed.

(** The unit's module, read in a context and in an equal extension *)
Lemma set_unit_module_across : forall Γ Ψ Ψ' U U' FU FU' FU2 FU2' ρ, gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    set_unit_eq_with T γ (Ψ ++ Γ) U U' FU FU' ->
    set_unit_eq_with T γ (Ψ' ++ Γ) U' U' FU2 FU2' ->
    set_env_in T γ (Ψ ++ Γ) ρ -> set_env_in T γ (Ψ' ++ Γ) ρ -> set_module_eq γ (FU ρ) (FU2 ρ).
Proof.
  intros * HΨ [_ HU' EU _ _] [HU2 _ _ _ _] Hρ Hρ'.
  eapply set_module_eq_trans; [apply EU; exact Hρ | exact (set_modexp_denotes_across _ _ _ _ _ _ _ HΨ HU' HU2 Hρ Hρ')].
Qed.

(** A module slot relates the same entries as one of an equal unit. *)
Lemma set_entry_rel_mod_iff : forall Γ Ψ Ψ' U U' FU FU' FU2 FU2' ρ e e', gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    set_unit_eq_with T γ (Ψ ++ Γ) U U' FU FU' ->
    set_unit_eq_with T γ (Ψ' ++ Γ) U' U' FU2 FU2' ->
    set_env_in T γ (Ψ ++ Γ) ρ -> set_env_in T γ (Ψ' ++ Γ) ρ ->
    set_entry_rel T γ (Ψ ++ Γ) ρ (ce_mod U) e e' <-> set_entry_rel T γ (Ψ' ++ Γ) ρ (ce_mod U') e e'.
Proof.
  intros * HΨ HUe HU2e Hρ Hρ'. pose proof (set_unit_module_across _ _ _ _ _ _ _ _ _ _ HΨ HUe HU2e Hρ Hρ') as E.
  destruct HUe as [HU _ _ _ _]. destruct HU2e as [HU2 _ _ _ _]. cbn [set_entry_rel]. split.
  - intros (m & m' & n & [E1 E2 Hn Em Em']).
    pose proof (set_modexp_denotes_unique _ _ _ _ _ HU _ _ _ Hρ (proj2 (set_interp_me_lit_iff _ _ _ _ _ _) Hn)) as En.
    exists m, m', (FU2 ρ). constructor; [exact E1 | exact E2 | apply set_interp_me_lit_iff; exact (set_modexp_denotes_exists _ _ _ _ _ HU2 _ Hρ') | |].
    + eapply set_module_eq_trans; [exact Em | eapply set_module_eq_trans; [exact En | exact E]].
    + eapply set_module_eq_trans; [exact Em' | eapply set_module_eq_trans; [exact En | exact E]].
  - intros (m & m' & n & [E1 E2 Hn Em Em']).
    pose proof (set_modexp_denotes_unique _ _ _ _ _ HU2 _ _ _ Hρ' (proj2 (set_interp_me_lit_iff _ _ _ _ _ _) Hn)) as En.
    exists m, m', (FU ρ). constructor; [exact E1 | exact E2 | apply set_interp_me_lit_iff; exact (set_modexp_denotes_exists _ _ _ _ _ HU _ Hρ) | |].
    + eapply set_module_eq_trans; [exact Em | eapply set_module_eq_trans; [exact En | apply set_module_eq_sym; exact E]].
    + eapply set_module_eq_trans; [exact Em' | eapply set_module_eq_trans; [exact En | apply set_module_eq_sym; exact E]].
Qed.

(** A definition with a module part, as both. *)
Lemma set_entry_rel_dm_iff : forall Γ Ψ Ψ' A A' M M' U U' FA FM FM' FM2 FU FU' FU2 FU2' ρ e e',
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    set_exp_eq_with T γ (Ψ ++ Γ) A M M' FA FM FM' -> set_denotes T γ (Ψ' ++ Γ) M' FM2 ->
    set_unit_eq_with T γ (Ψ ++ Γ) U U' FU FU' ->
    set_unit_eq_with T γ (Ψ' ++ Γ) U' U' FU2 FU2' ->
    set_env_in T γ (Ψ ++ Γ) ρ -> set_env_in T γ (Ψ' ++ Γ) ρ ->
    set_entry_rel T γ (Ψ ++ Γ) ρ (ce_dm A M U) e e' <-> set_entry_rel T γ (Ψ' ++ Γ) ρ (ce_dm A' M' U') e e'.
Proof.
  intros * HΨ HMe HM2 HUe HU2e Hρ Hρ'. pose proof (set_unit_module_across _ _ _ _ _ _ _ _ _ _ HΨ HUe HU2e Hρ Hρ') as EU.
  destruct HUe as [HU _ _ _ _]. destruct HU2e as [HU2 _ _ _ _]. destruct HMe as [_ HM HM' EM _].
  assert (E : set_eq (FM ρ) (FM2 ρ))
    by (eapply set_eq_trans; [apply EM; exact Hρ | exact (set_denotes_across _ _ _ _ _ _ _ HΨ HM' HM2 Hρ Hρ')]).
  cbn [set_entry_rel]. split.
  - intros (v & v' & w & m & m' & n & [E1 E2 Hw Hn Ev Ev' Em Em']).
    pose proof (set_denotes_unique _ _ _ _ _ HM _ _ _ Hρ Hw) as Ew.
    pose proof (set_modexp_denotes_unique _ _ _ _ _ HU _ _ _ Hρ (proj2 (set_interp_me_lit_iff _ _ _ _ _ _) Hn)) as En.
    exists v, v', (FM2 ρ), m, m', (FU2 ρ).
    constructor; [exact E1 | exact E2 | exact (set_denotes_exists _ _ _ _ _ HM2 _ Hρ')
                 | apply set_interp_me_lit_iff; exact (set_modexp_denotes_exists _ _ _ _ _ HU2 _ Hρ') | | | |].
    + eapply set_eq_trans; [exact Ev | eapply set_eq_trans; [exact Ew | exact E]].
    + eapply set_eq_trans; [exact Ev' | eapply set_eq_trans; [exact Ew | exact E]].
    + eapply set_module_eq_trans; [exact Em | eapply set_module_eq_trans; [exact En | exact EU]].
    + eapply set_module_eq_trans; [exact Em' | eapply set_module_eq_trans; [exact En | exact EU]].
  - intros (v & v' & w & m & m' & n & [E1 E2 Hw Hn Ev Ev' Em Em']).
    pose proof (set_denotes_unique _ _ _ _ _ HM2 _ _ _ Hρ' Hw) as Ew.
    pose proof (set_modexp_denotes_unique _ _ _ _ _ HU2 _ _ _ Hρ' (proj2 (set_interp_me_lit_iff _ _ _ _ _ _) Hn)) as En.
    exists v, v', (FM ρ), m, m', (FU ρ).
    constructor; [exact E1 | exact E2 | exact (set_denotes_exists _ _ _ _ _ HM _ Hρ)
                 | apply set_interp_me_lit_iff; exact (set_modexp_denotes_exists _ _ _ _ _ HU _ Hρ) | | | |].
    + eapply set_eq_trans; [exact Ev | eapply set_eq_trans; [exact Ew | apply set_eq_sym; exact E]].
    + eapply set_eq_trans; [exact Ev' | eapply set_eq_trans; [exact Ew | apply set_eq_sym; exact E]].
    + eapply set_module_eq_trans; [exact Em | eapply set_module_eq_trans; [exact En | apply set_module_eq_sym; exact EU]].
    + eapply set_module_eq_trans; [exact Em' | eapply set_module_eq_trans; [exact En | apply set_module_eq_sym; exact EU]].
Qed.

(** A term equal to another is equal to itself. *)
Lemma set_exp_eq_with_left : forall Γ A M M' FA FM FM', set_exp_eq_with T γ Γ A M M' FA FM FM' ->
    set_exp_eq_with T γ Γ A M M FA FM FM.
Proof. intros * [HA HM _ _ Hm]. constructor; [exact HA | exact HM | exact HM | intros; apply set_eq_refl | exact Hm]. Qed.

(** A unit equal to another denotes, as a slot's must. *)
Lemma set_modexp_rel_of_unit_eq_with : forall Γ U U' F F', set_unit_eq_with T γ Γ U U' F F' ->
    set_modexp_rel T γ Γ (me_lit U) (me_lit U).
Proof.
  intros * [HF _ _ _ _]. exists F, F. constructor; [exact HF | exact HF |].
  intros ρ Hρ. exact (set_modexp_denotes_refl _ _ _ _ _ _ HF Hρ).
Qed.

(** ** The Rules of Extensions *)

Lemma set_rule_ext_eq_nil : forall Γ, set_ctx T γ Γ -> set_ext_eq_with T γ Γ nil nil.
Proof. intros Γ HΓ. constructor; [exact HΓ | exact HΓ | intros; reflexivity]. Qed.

Lemma set_rule_ext_eq_ass : forall Γ Ψ Ψ' κ A A' S FS FA FA2 S' FS' FA' FA'2, gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    set_ext_eq_with T γ Γ Ψ Ψ' ->
    set_exp_eq_with T γ (Ψ ++ Γ) S A A FS FA FA2 -> set_exp_eq_with T γ (Ψ' ++ Γ) S' A' A' FS' FA' FA'2 ->
    set_subtyp T γ (Ψ ++ Γ) A A' -> set_subtyp T γ (Ψ ++ Γ) A' A ->
    set_ext_eq_with T γ Γ (ce_ass κ A :: Ψ) (ce_ass κ A' :: Ψ').
Proof.
  intros * HΨ Hext [_ HA _ _ _] [_ HA' _ _ _] (FX & FX' & Hs) (FY & FY' & Hs').
  apply set_ext_eq_extend; [exact Hext | exists FA; exact HA | exists FA'; exact HA' |].
  intros. eapply set_entry_rel_ass_iff; eassumption.
Qed.

Lemma set_rule_ext_eq_def : forall Γ Ψ Ψ' A A' M M' FA FM FM' FA' FM2 FM2', gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    set_ext_eq_with T γ Γ Ψ Ψ' ->
    set_exp_eq_with T γ (Ψ ++ Γ) A M M' FA FM FM' -> set_exp_eq_with T γ (Ψ' ++ Γ) A' M' M' FA' FM2 FM2' ->
    set_ext_eq_with T γ Γ (ce_def A M :: Ψ) (ce_def A' M' :: Ψ').
Proof.
  intros * HΨ Hext HMe HM2e.
  apply set_ext_eq_extend; [exact Hext | do 3 eexists; exact (set_exp_eq_with_left _ _ _ _ _ _ _ HMe) | do 3 eexists; exact HM2e |].
  intros. destruct HM2e as [_ HM2 _ _ _]. eapply set_entry_rel_def_iff; eassumption.
Qed.

Lemma set_rule_ext_eq_mod : forall Γ Ψ Ψ' U U' FU FU' FU2 FU2', gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    set_ext_eq_with T γ Γ Ψ Ψ' ->
    set_unit_eq_with T γ (Ψ ++ Γ) U U' FU FU' ->
    set_unit_eq_with T γ (Ψ' ++ Γ) U' U' FU2 FU2' ->
    set_ext_eq_with T γ Γ (ce_mod U :: Ψ) (ce_mod U' :: Ψ').
Proof.
  intros * HΨ Hext HUe HU2e.
  apply set_ext_eq_extend; [exact Hext | exact (set_modexp_rel_of_unit_eq_with _ _ _ _ _ HUe)
                           | exact (set_modexp_rel_of_unit_eq_with _ _ _ _ _ HU2e) |].
  intros. eapply set_entry_rel_mod_iff; eassumption.
Qed.

Lemma set_rule_ext_eq_dm : forall Γ Ψ Ψ' A A' M M' E E' FA FM FM' FA' FM2 FM2' FU FU' FU2 FU2',
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> set_ext_eq_with T γ Γ Ψ Ψ' ->
    set_exp_eq_with T γ (Ψ ++ Γ) A M M' FA FM FM' -> set_exp_eq_with T γ (Ψ' ++ Γ) A' M' M' FA' FM2 FM2' ->
    set_unit_eq_with T γ (Ψ ++ Γ) (gu_mk nil (md_alias E)) (gu_mk nil (md_alias E')) FU FU' ->
    set_unit_eq_with T γ (Ψ' ++ Γ) (gu_mk nil (md_alias E')) (gu_mk nil (md_alias E')) FU2 FU2' ->
    set_ext_eq_with T γ Γ (ce_dm A M (gu_mk nil (md_alias E)) :: Ψ) (ce_dm A' M' (gu_mk nil (md_alias E')) :: Ψ').
Proof.
  intros * HΨ Hext HMe HM2e HUe HU2e.
  apply set_ext_eq_extend; [exact Hext | split | split |].
  - do 3 eexists; exact (set_exp_eq_with_left _ _ _ _ _ _ _ HMe).
  - exact (set_modexp_rel_of_unit_eq_with _ _ _ _ _ HUe).
  - do 3 eexists; exact HM2e.
  - exact (set_modexp_rel_of_unit_eq_with _ _ _ _ _ HU2e).
  - intros. destruct HM2e as [_ HM2 _ _ _]. eapply set_entry_rel_dm_iff; eassumption.
Qed.

(** ** Units over Equal Telescopes *)

(** Telescopes of assumptions of one length push the same slots. *)
Lemma tele_out_proofs_assumptions : forall L L' κs, all_assumptions L -> all_assumptions L' -> List.length L = List.length L' ->
    tele_out_proofs γ κs L = tele_out_proofs γ κs L'.
Proof.
  induction L as [| e L IH]; intros [| e' L'] κs HL HL' Hlen; try discriminate; [reflexivity |].
  inversion HL as [| ? ? (κ & A & ->) HL0]; subst. inversion HL' as [| ? ? (κ' & A' & ->) HL0']; subst.
  cbn [tele_out_proofs]. apply IH; [exact HL0 | exact HL0' | injection Hlen as Hlen; exact Hlen].
Qed.

(** The suffixes of equal lengths of telescopes of one length, read
    outermost first. *)
Lemma rev_firstn_rev_suffix : forall (Δ : ctx) k, Δ = List.firstn (List.length Δ - k) Δ ++ List.rev (List.firstn k (List.rev Δ)).
Proof. intros. rewrite List.firstn_rev, List.rev_involutive. symmetry. apply List.firstn_skipn. Qed.

(** An alias over assumptions of evaluated sorts of a valid target is a
    valid unit. *)
Lemma set_valid_unit_alias_of : forall Γ Δ E l,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_lit (gu_mk Δ (md_alias E)) ≈ me_lit (gu_mk Δ (md_alias E)) ->
    all_assumptions Δ -> set_params_evaluated T γ Γ Δ l -> set_valid_modexp T γ (Δ ++ Γ) E ->
    set_valid_unit T γ Γ (me_lit (gu_mk Δ (md_alias E))).
Proof.
  intros * Hw HΔ Hl HvE. pose proof (fn_kinds_unique_of_ext Hfn) as Hfn0.
  inversion HvE as [? ? K R Rm RK [HwE _ _ HrE _ _ _] HK]; subst.
  pose proof (set_valid_unit_ctx T γ _ _ HK) as HΔΓ. pose proof (presup_modexp_eq_ctx HwE) as HcΔΓ.
  pose proof (set_modexp_rel_refl_left T γ _ _ _ HrE) as HEE.
  apply set_valid_unit_alias; [| exact HvE].
  constructor; [exact Hw | exact HΔ | exists l; exact Hl | exact (set_ctx_app_r T γ _ _ HΔΓ) | exact HΔΓ | | exact HEE].
  exact (set_unit_rel_abs T γ Hfn0 Hmods Δ Γ nil _ HΔ HΔΓ HcΔΓ
           (set_modexp_rel_refl_left T γ _ _ _ (set_alias0_rel T γ Hfn0 Hmods _ _ HΔΓ HEE))).
Qed.

Lemma set_rule_unit_eq_alias : forall Γ Δ Δ' E E' l,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E') ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Δ ≈ Δ' ->
    (forall X Ψ X' Ψ', Δ = X ++ Ψ -> Δ' = X' ++ Ψ' -> List.length Ψ = List.length Ψ' -> set_ext_eq_with T γ Γ Ψ Ψ') ->
    all_assumptions Δ -> all_assumptions Δ' ->
    set_params_evaluated T γ Γ Δ l -> set_params_evaluated T γ Γ Δ' l ->
    set_modexp_eq T γ (Δ ++ Γ) E E' -> set_modexp_eq T γ (Δ' ++ Γ) E' E' ->
    set_unit_eq T γ Γ (gu_mk Δ (md_alias E)) (gu_mk Δ' (md_alias E')).
Proof.
  intros * HUU HΔw Hext HΔ HΔ' Hl Hl' (G & G' & [HG HG' EG HvE _ HprE]) (G2 & _ & [HG2 _ _ HvE2 _ _]).
  pose proof (fn_kinds_unique_of_ext Hfn) as Hfn0. pose proof (ext_eq_length _ _ _ _ _ HΔw) as Hlen.
  pose proof (set_valid_unit_alias_of _ _ _ _ (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_left HUU)) HΔ Hl HvE) as HK.
  pose proof (set_valid_unit_alias_of _ _ _ _ (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_right HUU)) HΔ' Hl' HvE2) as HK'.
  destruct (set_valid_unit_rel T γ Hfn0 Hmods Hok _ _ HK) as (F & _ & [HF _ _]).
  destruct (set_valid_unit_rel T γ Hfn0 Hmods Hok _ _ HK') as (F' & _ & [HF' _ _]).
  assert (Hpr : forall κs, set_slots_coherent γ Γ κs -> forall ys x,
             unit_member_proofs γ κs (gu_mk Δ (md_alias E)) ys x = unit_member_proofs γ κs (gu_mk Δ' (md_alias E')) ys x).
  { intros κs Hκ ys x. rewrite !unit_member_proofs_tele_out. cbn [moddef_member_proofs].
    rewrite (HprE _ (set_slots_coherent_tele_out γ _ _ _ HΔ Hκ)).
    rewrite (tele_out_proofs_assumptions (List.rev Δ) (List.rev Δ') κs (List.Forall_rev HΔ) (List.Forall_rev HΔ')
               ltac:(rewrite !List.length_rev; exact Hlen)).
    reflexivity. }
  exists F, F'. constructor; [exact HF | exact HF' | | exact HK | exact HK' | exact Hpr].
  intros ρ Hρ.
  pose proof (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ) as Hm1. apply set_interp_me_lit_iff in Hm1.
  pose proof (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ) as Hm2. apply set_interp_me_lit_iff in Hm2.
  inversion Hm1 as [? ? ? ? P1 m1 HP1 HL1]; subst. inversion Hm2 as [? ? ? ? P2 m2 HP2 HL2]; subst.
  apply (set_unit_params_eq_ext T γ Hfn0 Hmods (List.rev Δ) (List.rev Δ') nil nil Γ ρ P1 P2 (md_alias E) (md_alias E') (F ρ) (F' ρ)
           (List.Forall_rev HΔ) (List.Forall_rev HΔ') ltac:(rewrite !List.length_rev; exact Hlen)); [| exact Hρ | exact Hρ | exact HL1 | exact HL2 | |].
  - intros k. rewrite !List.app_nil_r.
    apply (Hext (List.firstn (List.length Δ - k) Δ) _ (List.firstn (List.length Δ' - k) Δ') _
             (rev_firstn_rev_suffix Δ k) (rev_firstn_rev_suffix Δ' k)).
    rewrite !List.length_rev, !List.length_firstn, !List.length_rev. lia.
  - intros ys x. rewrite HP1, HP2. exact (Hpr _ (set_slots_coherent_env T γ _ _ Hρ) ys x).
  - intros ρ' n1 n2 Hρ1 Hρ2 Hn1 Hn2. cbn [List.app] in Hρ1, Hρ2, Hn1, Hn2. rewrite List.rev_involutive in Hρ1, Hρ2, Hn1, Hn2.
    inversion Hn1 as [| ? ? ? ? H1]; subst. inversion Hn2 as [| ? ? ? ? H2]; subst.
    eapply set_module_eq_trans; [exact (set_modexp_denotes_unique _ _ _ _ _ HG _ _ _ Hρ1 H1) |].
    eapply set_module_eq_trans; [exact (EG _ Hρ1) |].
    eapply set_module_eq_trans; [exact (set_modexp_denotes_across _ _ _ _ _ _ _ HΔw HG' HG2 Hρ1 Hρ2) |].
    exact (set_module_eq_sym _ _ (set_modexp_denotes_unique _ _ _ _ _ HG2 _ _ _ Hρ2 H2)).
Qed.

(** ** Bodies over Equal Telescopes *)

(** An entry of a body read in the environment the entries before it make
    is read as the entry filled in at the body's base environment. *)
Lemma set_interp_gmod_sub_setting : forall D ρ Φ ms ρo σ, ⊢ gc_deps ⍮ gc_stack ⍮ body_ctx Φ ++ D ->
    set_interp_gmod T γ D ρ Φ ms ρo -> gm_fill Φ = Some σ ->
    sub_setting T γ (body_ctx Φ ++ D) ρo nil (body_ctx Φ ++ D) D σ ρ ρ.
Proof.
  intros * Hc Hm Hf.
  constructor; [reflexivity | exact (wf_gm_fill _ _ _ _ _ Hc Hf) | intros k Hk; cbn in Hk; lia
               | intros; reflexivity | intros k; exact (set_interp_gmod_fill T γ _ _ _ _ _ Hm _ Hf k)].
Qed.

(** Two bodies of one shape read at one environment of their bases have
    equal tables, when their definitions and submodules filled in agree
    there entry by entry. *)
Lemma set_interp_gmod_eq_filled : forall Φ Φ' D D' ρ ms ms' ρo ρo',
    body_shape Φ Φ' -> gm_nopens Φ = 0 -> List.NoDup (gm_names Φ) ->
    set_interp_gmod T γ D ρ Φ ms ρo -> set_interp_gmod T γ D' ρ Φ' ms' ρo' ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ' v v',
       gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φ' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       set_interp T γ D ρ (exp_sub M σ) v -> set_interp T γ D' ρ (exp_sub M' σ') v' -> set_eq v v') ->
    (forall y Φ0 E U Φ0' E' U' σ σ' m m',
       gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_prefix_upto Φ' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       set_interp_modexp T γ D ρ (me_lit (gunit_sub U σ)) m -> set_interp_modexp T γ D' ρ (me_lit (gunit_sub U' σ')) m' ->
       set_module_eq γ m m') ->
    set_members_eq γ ms ms'.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its Φg _];
    intros [| Φ' y' E' | Φ' H' its' Φg'] D D' ρ ms ms' ρo ρo' Hs Hn Hnd Hm Hm' Hdef Hmod; cbn [body_shape gm_nopens] in Hs, Hn;
    try contradiction; [| | discriminate].
  - inversion Hm; subst. inversion Hm'; subst. constructor.
  - destruct Hs as (Hs0 & <- & HsE).
    assert (Hnd' : List.NoDup (gm_names (gm_ext Φ' y E'))) by (rewrite <- (body_shape_names (gm_ext Φ y E) (gm_ext Φ' y E')); [exact Hnd |];
                                                              cbn [body_shape]; auto).
    inversion Hm as [| ? ? ? ? ? ms0 ρo0 e Hc HΦ HE]; subst. inversion Hm' as [| ? ? ? ? ? ms0' ρo0' e' Hc' HΦ' HE']; subst.
    destruct (body_shape_fill _ _ Hn Hs0) as [Hf0 Hf0'].
    destruct (gm_fill Φ) as [σ |] eqn:Hf; [| exfalso; exact (Hf0 eq_refl)].
    destruct (gm_fill Φ') as [σ' |] eqn:Hf'; [| exfalso; exact (Hf0' eq_refl)].
    pose proof (set_interp_gmod_sub_setting _ _ _ _ _ _ Hc HΦ Hf) as Hsub.
    pose proof (set_interp_gmod_sub_setting _ _ _ _ _ _ Hc' HΦ' Hf') as Hsub'.
    assert (Hp : gm_prefix_upto (gm_ext Φ y E) y = Some (gm_ext Φ y E)) by (cbn [gm_prefix_upto]; rewrite String.eqb_refl; reflexivity).
    assert (Hp' : gm_prefix_upto (gm_ext Φ' y E') y = Some (gm_ext Φ' y E')) by (cbn [gm_prefix_upto]; rewrite String.eqb_refl; reflexivity).
    apply set_members_eq_app.
    + apply (IH Φ' D D' ρ ms0 ms0' ρo0 ρo0' Hs0 Hn ltac:(cbn [gm_names] in Hnd; inversion Hnd; assumption) HΦ HΦ').
      * intros * Hq HEq Hq' HEq'. exact (Hdef _ _ _ _ _ _ _ _ _ _ _ _ _ (prefix_ext_keep _ _ _ _ _ Hnd Hq) HEq
                                             (prefix_ext_keep _ _ _ _ _ Hnd' Hq') HEq').
      * intros * Hq HEq Hq' HEq'. exact (Hmod _ _ _ _ _ _ _ _ _ _ _(prefix_ext_keep _ _ _ _ _ Hnd Hq) HEq
                                             (prefix_ext_keep _ _ _ _ _ Hnd' Hq') HEq').
    + assert (HvM : forall M v, set_interp T γ (body_ctx Φ ++ D) ρo0 M v -> set_interp T γ D ρ (exp_sub M σ) v)
        by (intros M v HM; exact (set_interp_sub T γ _ _ _ _ HM Hc _ _ _ _ _ _ Hsub)).
      assert (HvM' : forall M v, set_interp T γ (body_ctx Φ' ++ D') ρo0' M v -> set_interp T γ D' ρ (exp_sub M σ') v)
        by (intros M v HM; exact (set_interp_sub T γ _ _ _ _ HM Hc' _ _ _ _ _ _ Hsub')).
      assert (HvU : forall U m, set_interp_gunit T γ (body_ctx Φ ++ D) ρo0 U m ->
                 set_interp_modexp T γ D ρ (me_lit (gunit_sub U σ)) m)
        by (intros U m HU; exact (proj1 (proj2 (proj2 (proj2 (set_interp_sub_all T γ)))) _ _ (me_lit U) _
                                    ltac:(constructor; exact HU) nil _ _ _ _ _ Hc Hsub)).
      assert (HvU' : forall U m, set_interp_gunit T γ (body_ctx Φ' ++ D') ρo0' U m ->
                  set_interp_modexp T γ D' ρ (me_lit (gunit_sub U σ')) m)
        by (intros U m HU; exact (proj1 (proj2 (proj2 (proj2 (set_interp_sub_all T γ)))) _ _ (me_lit U) _
                                    ltac:(constructor; exact HU) nil _ _ _ _ _ Hc' Hsub')).
      constructor; [| constructor].
      destruct E as [b pv r A [M |] | pv U | | pv A M U |]; destruct E' as [b' pv' r' A' [M' |] | pv' U' | | pv' A' M' U' |];
        cbn [entry_shape] in HsE; try contradiction.
      * destruct HsE as (_ & _ & _ & <-). inversion HE; subst. inversion HE'; subst. constructor.
        exact (Hdef _ _ _ _ _ _ _ _ _ _ _ _ _ Hp eq_refl Hp' eq_refl Hf Hf' (HvM _ _ ltac:(eassumption)) (HvM' _ _ ltac:(eassumption))).
      * inversion HE; subst. inversion HE'; subst. constructor.
        exact (Hmod _ _ _ _ _ _ _ _ _ _ _ Hp eq_refl Hp' eq_refl Hf Hf' (HvU _ _ ltac:(eassumption)) (HvU' _ _ ltac:(eassumption))).
      * inversion HE; subst. inversion HE'; subst. constructor.
        -- exact (Hdef _ _ _ _ _ _ _ _ _ _ _ _ _ Hp eq_refl Hp' eq_refl Hf Hf' (HvM _ _ ltac:(eassumption)) (HvM' _ _ ltac:(eassumption))).
        -- exact (Hmod _ _ _ _ _ _ _ _ _ _ _ Hp eq_refl Hp' eq_refl Hf Hf' (HvU _ _ ltac:(eassumption)) (HvU' _ _ ltac:(eassumption))).
Qed.

End Units.
