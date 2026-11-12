(** * The Set Rules of Extensions and Units

    Equal extensions relate the same environments.  Each side's entries
    are read in its own context, and a term has the same value read in two
    contexts extending one context by equal extensions
    ([set_interp_functional_ext]): so an entry of one side relates the
    entries the other's relates. *)

From Stdlib Require Import List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.SetModel.Interpretation Require Import ContextRelation.
From Mctt.Core.Syntactic Require Import Syntax.
From Mctt.Core.Syntactic.System Require Import Definitions.
Import ListNotations.

Section Units.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.
  Hypothesis Hfn : fn_kinds_unique_ext.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).

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

End Units.
