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
From Mctt.Core.SetModel Require Import Judgments.
From Mctt.Core.SetModel.Cases Require Import ValidUnit MemberTypes ModuleCases Unit Sel ContextCases.
From Mctt.Core.Syntactic Require Import Syntax Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural.
From Mctt.Core.Syntactic.System.Global Require Import Presup DescTyping MemberLemmas.
From Mctt.Core.SetModel.Interpretation Require Import Substitution.
From Mctt.Core.Syntactic.System Require Import Scoping.
From Mctt.Core.Completeness.Modules Require Import ValidUnit Body.
Import ListNotations.

Section Units.
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

Section UnitSteps.
  Context {GC : GCtx}.
  Hypothesis Hfn : fn_kinds_unique_ext.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).
  (** The context the derivations were checked at *)
  Variable Θs : gdeps.
  Variable Ξs : gstack.
  (** The valuation models, here, everything that context resolves *)
  Hypothesis Hemb : set_gctx_embedding Θs Ξs gc_deps gc_stack T γ.

(** This context is well formed, as one the smaller context grows into. *)
Lemma set_here_wf : ⊢ᵍ gc_deps ⍮ gc_stack.
Proof. exact (gctx_embedding_wf _ _ _ _ (set_gctx_embedding_embedding _ _ _ _ _ _ Hemb)). Qed.

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

(** ** Equal Extensions, Entry by Entry *)

Lemma set_ext_eq_with_nil : forall Γ, set_ctx T γ Γ -> set_ext_eq_with T γ Γ nil nil.
Proof. intros Γ HΓ. constructor; [exact HΓ | exact HΓ | intros; reflexivity]. Qed.

(** The suffixes of extensions by one more entry each: the whole ones, or
    suffixes of the extensions before. *)
Lemma set_ext_eq_suffixes_eq_cons : forall Γ Ψ Ψ' e e',
    (forall X Ψ0 X' Ψ0', Ψ = X ++ Ψ0 -> Ψ' = X' ++ Ψ0' -> List.length Ψ0 = List.length Ψ0' -> set_ext_eq_with T γ Γ Ψ0 Ψ0') ->
    List.length Ψ = List.length Ψ' -> set_ext_eq_with T γ Γ (e :: Ψ) (e' :: Ψ') ->
    forall X Ψ0 X' Ψ0', e :: Ψ = X ++ Ψ0 -> e' :: Ψ' = X' ++ Ψ0' -> List.length Ψ0 = List.length Ψ0' ->
    set_ext_eq_with T γ Γ Ψ0 Ψ0'.
Proof.
  intros * Hsuf Hlen Hwhole [| x X] Ψ0 [| x' X'] Ψ0' E E' Hl.
  - cbn in E, E'. subst. exact Hwhole.
  - exfalso. apply (f_equal (@List.length centry)) in E, E'. cbn in E, E'. rewrite List.length_app in E'. lia.
  - exfalso. apply (f_equal (@List.length centry)) in E, E'. cbn in E, E'. rewrite List.length_app in E. lia.
  - injection E as _ E. injection E' as _ E'. exact (Hsuf _ _ _ _ E E' Hl).
Qed.

Lemma set_ext_eq_with_ass : forall Γ Ψ Ψ' κ A A' S FS FA FA2 S' FS' FA' FA'2, gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    set_ext_eq_with T γ Γ Ψ Ψ' ->
    set_exp_eq_with T γ (Ψ ++ Γ) S A A FS FA FA2 -> set_exp_eq_with T γ (Ψ' ++ Γ) S' A' A' FS' FA' FA'2 ->
    set_rel_subtyp T γ (Ψ ++ Γ) A A' -> set_rel_subtyp T γ (Ψ ++ Γ) A' A ->
    set_ext_eq_with T γ Γ (ce_ass κ A :: Ψ) (ce_ass κ A' :: Ψ').
Proof.
  intros * HΨ Hext [_ HA _ _ _] [_ HA' _ _ _] (FX & FX' & Hs) (FY & FY' & Hs').
  apply set_ext_eq_extend; [exact Hext | exists FA; exact HA | exists FA'; exact HA' |].
  intros. eapply set_entry_rel_ass_iff; eassumption.
Qed.

Lemma set_ext_eq_with_def : forall Γ Ψ Ψ' A A' M M' FA FM FM' FA' FM2 FM2', gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    set_ext_eq_with T γ Γ Ψ Ψ' ->
    set_exp_eq_with T γ (Ψ ++ Γ) A M M' FA FM FM' -> set_exp_eq_with T γ (Ψ' ++ Γ) A' M' M' FA' FM2 FM2' ->
    set_ext_eq_with T γ Γ (ce_def A M :: Ψ) (ce_def A' M' :: Ψ').
Proof.
  intros * HΨ Hext HMe HM2e.
  apply set_ext_eq_extend; [exact Hext | do 3 eexists; exact (set_exp_eq_with_left _ _ _ _ _ _ _ HMe) | do 3 eexists; exact HM2e |].
  intros. destruct HM2e as [_ HM2 _ _ _]. eapply set_entry_rel_def_iff; eassumption.
Qed.

Lemma set_ext_eq_with_mod : forall Γ Ψ Ψ' U U' FU FU' FU2 FU2', gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
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

Lemma set_ext_eq_with_dm : forall Γ Ψ Ψ' A A' M M' E E' FA FM FM' FA' FM2 FM2' FU FU' FU2 FU2',
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

(** Aliases over telescopes of one length of equal targets push the same
    proofs. *)
Lemma set_unit_alias_eq_proofs : forall Γ Δ Δ' E E', gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Δ ≈ Δ' ->
    all_assumptions Δ -> all_assumptions Δ' -> set_rel_modexp_eq T γ (Δ ++ Γ) E E' ->
    forall κs, set_slots_coherent γ Γ κs -> forall ys x,
      unit_member_proofs γ κs (gu_mk Δ (md_alias E)) ys x = unit_member_proofs γ κs (gu_mk Δ' (md_alias E')) ys x.
Proof.
  intros * HΔw HΔ HΔ' (G & G' & [_ _ _ _ _ HprE]) κs Hκ ys x. pose proof (ext_eq_length _ _ _ _ _ HΔw) as Hlen.
  rewrite !unit_member_proofs_tele_out. cbn [moddef_member_proofs].
  rewrite (HprE _ (set_slots_coherent_tele_out γ _ _ _ HΔ Hκ)).
  rewrite (tele_out_proofs_assumptions (List.rev Δ) (List.rev Δ') κs (List.Forall_rev HΔ) (List.Forall_rev HΔ')
             ltac:(rewrite !List.length_rev; exact Hlen)).
  reflexivity.
Qed.

(** Aliases over equal telescopes of equal targets have equal values. *)
Lemma set_unit_alias_eq_values : forall Γ Δ Δ' E E' F F', gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Δ ≈ Δ' ->
    (forall X Ψ X' Ψ', Δ = X ++ Ψ -> Δ' = X' ++ Ψ' -> List.length Ψ = List.length Ψ' -> set_ext_eq_with T γ Γ Ψ Ψ') ->
    all_assumptions Δ -> all_assumptions Δ' ->
    set_rel_modexp_eq T γ (Δ ++ Γ) E E' -> set_rel_modexp_eq T γ (Δ' ++ Γ) E' E' ->
    set_modexp_denotes T γ Γ (me_lit (gu_mk Δ (md_alias E))) F -> set_modexp_denotes T γ Γ (me_lit (gu_mk Δ' (md_alias E'))) F' ->
    forall ρ, set_env_in T γ Γ ρ -> set_module_eq γ (F ρ) (F' ρ).
Proof.
  intros * HΔw Hext HΔ HΔ' HEe (G2 & _ & [HG2 _ _ HvE2 _ _]) HF HF'.
  pose proof (set_unit_alias_eq_proofs _ _ _ _ _ HΔw HΔ HΔ' HEe) as Hpr.
  destruct HEe as (G & G' & [HG HG' EG HvE _ HprE]).
  pose proof (fn_kinds_unique_of_ext Hfn) as Hfn0. pose proof (ext_eq_length _ _ _ _ _ HΔw) as Hlen.
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

(** A term equal to another is equal to itself. *)
Lemma set_rel_exp_eq_refl_left : forall Γ A M M', set_rel_exp_eq T γ Γ A M M' -> set_rel_exp_eq T γ Γ A M M.
Proof. intros * (FA & FM & FM' & H). exists FA, FM, FM. exact (set_exp_eq_with_left _ _ _ _ _ _ _ H). Qed.

(** The slots of a context's tail are valid. *)
Lemma set_valid_slots_app_r : forall Ψ Γ, set_valid_slots T γ (Ψ ++ Γ) -> set_valid_slots T γ Γ.
Proof. induction Ψ as [| e Ψ IH]; intros Γ H; [exact H | exact (IH _ (proj1 H))]. Qed.

(** A submodule of a body whose context has valid slots is valid in the
    context the entries before it make. *)
Lemma set_valid_slots_body_unit : forall Φ X y Φ0 E U, gm_nopens Φ = 0 -> set_valid_slots T γ (body_ctx Φ ++ X) ->
    gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U -> set_valid_unit T γ (body_ctx Φ0 ++ X) (me_lit U).
Proof.
  intros * Hn Hsl Hp HEu. destruct (prefix_body_ctx _ _ _ Hn Hp) as (Y & HY). rewrite HY, <- List.app_assoc in Hsl.
  apply set_valid_slots_app_r in Hsl.
  destruct E as [b pv r A om | pv U0 | | pv A M U0 |]; cbn in HEu; try discriminate; injection HEu as <-;
    cbn [body_ctx List.app set_valid_slots] in Hsl; destruct Hsl as [_ Hu]; apply Hu; reflexivity.
Qed.

(** The partner of a definition of a body in a body of its shape, with its
    term part and its filling. *)
Lemma body_partner_tm : forall Φa Φb y Φ0 E A M, body_shape Φa Φb -> gm_nopens Φb = 0 ->
    gm_prefix_upto Φa y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
    exists Φ0' E' A' M' σ', gm_prefix_upto Φb y = Some (gm_ext Φ0' y E') /\ entry_tm E' = Some (A', M') /\
      gm_fill Φ0' = Some σ' /\ entry_kind E' = entry_kind E.
Proof.
  intros * Hab Hnb Hp HE.
  destruct (shape_prefix _ _ _ _ _ Hab Hp) as (Φ0' & E' & Hp' & Hsh0 & HsE).
  destruct (entry_shape_tm _ _ _ _ HsE HE) as (A' & M' & HE').
  pose proof (prefix_nopens _ _ _ Hnb Hp') as Hn0'. cbn in Hn0'.
  destruct (gm_fill Φ0') as [σ' |] eqn:Hf'; [| exfalso; exact (proj1 (body_shape_fill _ _ Hn0' (body_shape_r _ _ Hsh0)) Hf')].
  exists Φ0', E', A', M', σ'. repeat split; try assumption. symmetry. exact (entry_shape_kind _ _ HsE).
Qed.

(** A body's definitions, filled in, each of its tag's sort make the body's
    sorts valid. *)
Lemma set_body_sorts_valid_of_filled : forall Φ D, gm_nopens Φ = 0 -> List.NoDup (gm_names Φ) ->
    (forall y Φ0 E A M σ, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) -> gm_fill Φ0 = Some σ ->
       exists i, set_rel_exp_eq T γ D (abs_kind_sort (entry_kind E) (a_typ i)) (exp_sub A σ) (exp_sub A σ)) ->
    set_body_sorts_valid T γ Φ D.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its Φg _]; intros D Hn Hnd Hf; cbn [set_body_sorts_valid gm_nopens] in *;
    [exact I | | discriminate].
  split.
  - apply IH; [exact Hn | cbn [gm_names] in Hnd; inversion Hnd; assumption |].
    intros * Hp HE Hf0. exact (Hf _ _ _ _ _ _ (prefix_ext_keep _ _ _ _ _ Hnd Hp) HE Hf0).
  - intros A M σ HE Hf0. apply (Hf y Φ E A M σ); [cbn [gm_prefix_upto]; rewrite String.eqb_refl; reflexivity | exact HE | exact Hf0].
Qed.

(** A body of definitions and modules whose context denotes has a value,
    as a function of the base environment. *)
Lemma set_interp_gmod_function : forall Φ D, gm_fill Φ <> None -> set_ctx T γ (body_ctx Φ ++ D) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ body_ctx Φ ++ D ->
    exists G : set_env -> list (string * set_entry) * set_env,
      forall ρ, set_env_in T γ D ρ -> set_interp_gmod T γ D ρ Φ (fst (G ρ)) (snd (G ρ)).
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros D Hf HC Hc.
  - exists (fun ρ => (nil, ρ)). intros ρ _. constructor.
  - assert (Hf0 : gm_fill Φ <> None)
      by (intros E0; apply Hf; cbn [gm_fill]; destruct E as [? ? ? ? [] | | | |]; rewrite ?E0; reflexivity).
    destruct E as [b pv r A [M |] | pv U | | pv A M U |]; try (exfalso; apply Hf; reflexivity);
      cbn [body_ctx List.app set_ctx] in HC, Hc; destruct HC as [HC0 Hce];
      destruct (IH D Hf0 HC0 (ctx_decomp_tail Hc)) as (G0 & HG0);
      pose proof (fun ρ Hρ => set_interp_gmod_env_in T γ _ _ _ _ _ (HG0 ρ Hρ) Hf0 Hρ HC0) as Hin.
    + destruct Hce as (FA & FM & FM' & [_ HM _ _ _]).
      exists (fun ρ => (fst (G0 ρ) ++ [(y, set_entry_term r (FM (snd (G0 ρ))))],
                       set_env_extend (snd (G0 ρ)) (set_entry_term r (FM (snd (G0 ρ)))))).
      intros ρ Hρ. cbn [fst snd]. apply set_interp_gm_ext; [exact (ctx_decomp_tail Hc) | exact (HG0 ρ Hρ) |].
      constructor. exact (set_denotes_exists _ _ _ _ _ HM _ (Hin ρ Hρ)).
    + destruct Hce as (FU & _ & [HU _ _]).
      exists (fun ρ => (fst (G0 ρ) ++ [(y, set_entry_module (FU (snd (G0 ρ))))],
                       set_env_extend (snd (G0 ρ)) (set_entry_module (FU (snd (G0 ρ)))))).
      intros ρ Hρ. cbn [fst snd]. apply set_interp_gm_ext; [exact (ctx_decomp_tail Hc) | exact (HG0 ρ Hρ) |].
      constructor. apply set_interp_me_lit_iff. exact (set_modexp_denotes_exists _ _ _ _ _ HU _ (Hin ρ Hρ)).
    + destruct Hce as [(FA & FM & FM' & [_ HM _ _ _]) (FU & _ & [HU _ _])].
      exists (fun ρ => (fst (G0 ρ) ++ [(y, set_entry_both (FM (snd (G0 ρ))) (FU (snd (G0 ρ))))],
                       set_env_extend (snd (G0 ρ)) (set_entry_both (FM (snd (G0 ρ))) (FU (snd (G0 ρ)))))).
      intros ρ Hρ. cbn [fst snd]. apply set_interp_gm_ext; [exact (ctx_decomp_tail Hc) | exact (HG0 ρ Hρ) |].
      constructor; [exact (set_denotes_exists _ _ _ _ _ HM _ (Hin ρ Hρ)) |].
      apply set_interp_me_lit_iff. exact (set_modexp_denotes_exists _ _ _ _ _ HU _ (Hin ρ Hρ)).
  - exfalso. apply Hf. reflexivity.
Qed.

(** A body unit over assumptions whose context denotes denotes. *)
Lemma set_body_unit_rel : forall Γ Δ Φ Φx, body_xp gc_deps gc_stack (Δ ++ Γ) Φ Φx -> gm_fill Φx <> None -> all_assumptions Δ ->
    set_ctx T γ (body_ctx Φx ++ Δ ++ Γ) -> ⊢ gc_deps ⍮ gc_stack ⍮ body_ctx Φx ++ Δ ++ Γ ->
    set_modexp_rel T γ Γ (me_lit (gu_open Δ Φ)) (me_lit (gu_open Δ Φ)).
Proof.
  intros * Hx Hf HΔ HC Hcx. pose proof (fn_kinds_unique_of_ext Hfn) as Hfn0.
  pose proof (body_xp_expand _ _ _ _ _ Hx) as Hxe.
  pose proof (set_ctx_app_r T γ _ _ HC) as HΔΓ. pose proof (ctx_app_wf_tail _ _ _ _ Hcx) as Hc0.
  destruct (set_interp_gmod_function _ _ Hf HC Hcx) as (G & HG).
  set (F := fun ρ => set_module_members (fst (G ρ))).
  assert (HF : set_modexp_denotes T γ (Δ ++ Γ) (me_lit (gu_mk nil (md_body sm_open Φ))) F).
  { apply (set_modexp_denotes_of_exists T γ Hfn0 Hmods _ _ _ HΔΓ). intros ρ Hρ. apply set_interp_me_lit.
    apply (set_interp_gunit_mk T γ _ _ _ _ (unit_member_proofs γ (env_slot_proofs γ ρ) (gu_mk nil (md_body sm_open Φ))));
      [intros; reflexivity |].
    cbn [List.rev]. constructor. apply set_interp_md_body with (ρ' := snd (G ρ)). rewrite <- Hxe. exact (HG ρ Hρ). }
  apply (set_unit_rel_abs T γ Hfn0 Hmods Δ Γ nil _ HΔ HΔΓ Hc0).
  exists F, F. constructor; [exact HF | exact HF |].
  intros ρ Hρ. exact (set_modexp_denotes_unique _ _ _ _ _ HF _ _ _ Hρ (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ)).
Qed.

(** A body unit over assumptions of evaluated sorts, its context
    denoting with valid slots, its definitions filled in of their sorts and
    its opens' targets valid, is a valid unit. *)
Lemma set_valid_unit_body_of : forall Γ Δ Φ Φx l,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_lit (gu_open Δ Φ) ≈ me_lit (gu_open Δ Φ) ->
    body_xp gc_deps gc_stack (Δ ++ Γ) Φ Φx -> ⊢ gc_deps ⍮ gc_stack ⍮ body_ctx Φx ++ Δ ++ Γ ->
    all_assumptions Δ -> set_params_evaluated T γ Γ Δ l ->
    set_ctx T γ (body_ctx Φx ++ Δ ++ Γ) -> set_valid_slots T γ (body_ctx Φx ++ Δ ++ Γ) ->
    set_body_sorts_valid T γ Φx (Δ ++ Γ) -> body_shape Φ Φ -> body_shape Φx Φx ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> set_valid_modexp T γ (Ψ ++ Δ ++ Γ) H) ->
    set_valid_unit T γ Γ (me_lit (gu_open Δ Φ)).
Proof.
  intros * Hw Hx Hcx HΔ Hl HC Hsl Hsv Hs Hsx Hop.
  pose proof (body_xp_nopens _ _ _ _ _ Hx) as Hn.
  pose proof (set_ctx_app_r T γ _ _ (set_ctx_app_r T γ _ _ HC)) as HΓ.
  pose proof (set_body_unit_rel _ _ _ _ Hx (proj1 (body_shape_fill _ _ Hn Hsx)) HΔ HC Hcx) as Hrel.
  apply set_valid_unit_body with (Φx := Φx); [constructor | | exact Hop].
  - exact Hw.
  - exact Hx.
  - exact HΔ.
  - exists l. exact Hl.
  - exact HΓ.
  - exact HC.
  - exact Hsv.
  - exact Hs.
  - exact Hsx.
  - exact Hrel.
  - intros k Ψ H Hk. pose proof (Hop _ _ _ Hk) as HvH.
    inversion HvH as [? ? K R Rm RK [_ _ _ Hr _ _ _] _]; subst. exact (set_modexp_rel_refl_left T γ _ _ _ Hr).
  - intros y Φ0 E U Hp HEu. exact (set_valid_slots_body_unit _ _ _ _ _ _ Hn Hsl Hp HEu).
Qed.

(** A submodule's proofness at the slots a body before it gives is its
    unit's, filled in. *)
Lemma gentry_slot_proofs_fill : forall κs Φ E U σ ys x, gm_fill Φ = Some σ -> entry_unit E = Some U ->
    gentry_slot_proofs γ (body_slot_proofs γ κs Φ) E ys x = unit_member_proofs γ κs (gunit_sub U σ) ys x.
Proof.
  intros * Hf HEu. rewrite (proj2 (unit_member_proofs_sub_all γ) U _ σ _ (fun s ys' x' => eq_refl)).
  destruct E as [b pv r A om | pv U0 | | pv A M U0 |]; cbn in HEu; try discriminate; injection HEu as <-;
    cbn [gentry_slot_proofs]; apply (proj1 (proj2 (unit_member_proofs_resp_all γ))); exact (body_slot_proofs_fill γ _ _ _ Hf).
Qed.

(** Two bodies of one shape whose submodules, filled in, have the same
    proofness have the same proofness. *)
Lemma body_member_lookup_eq_filled : forall Φ Φ' κs, body_shape Φ Φ' -> gm_nopens Φ = 0 -> List.NoDup (gm_names Φ) ->
    (forall y Φ0 E U Φ0' E' U' σ σ',
       gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_prefix_upto Φ' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       forall ys x, unit_member_proofs γ κs (gunit_sub U σ) ys x = unit_member_proofs γ κs (gunit_sub U' σ') ys x) ->
    forall ys x, body_member_lookup γ κs Φ ys x = body_member_lookup γ κs Φ' ys x.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its Φg _]; intros [| Φ' y' E' | Φ' H' its' Φg'] κs Hs Hn Hnd Hu ys x;
    cbn [body_shape gm_nopens] in Hs, Hn; try contradiction; [reflexivity | | discriminate].
  destruct Hs as (Hs0 & <- & HsE).
  assert (Hnd' : List.NoDup (gm_names (gm_ext Φ' y E'))) by (rewrite <- (body_shape_names (gm_ext Φ y E) (gm_ext Φ' y E')); [exact Hnd |];
                                                            cbn [body_shape]; auto).
  assert (Hp : gm_prefix_upto (gm_ext Φ y E) y = Some (gm_ext Φ y E)) by (cbn [gm_prefix_upto]; rewrite String.eqb_refl; reflexivity).
  assert (Hp' : gm_prefix_upto (gm_ext Φ' y E') y = Some (gm_ext Φ' y E')) by (cbn [gm_prefix_upto]; rewrite String.eqb_refl; reflexivity).
  cbn [body_member_lookup]. destruct (String.eqb (chain_key ys x) y) eqn:Ek.
  - f_equal. destruct (body_shape_fill _ _ Hn Hs0) as [Hf0 Hf0'].
    destruct (gm_fill Φ) as [σ |] eqn:Hf; [| exfalso; exact (Hf0 eq_refl)].
    destruct (gm_fill Φ') as [σ' |] eqn:Hf'; [| exfalso; exact (Hf0' eq_refl)].
    destruct E as [b pv r A [M |] | pv U | | pv A M U |]; destruct E' as [b' pv' r' A' [M' |] | pv' U' | | pv' A' M' U' |];
      cbn [entry_shape] in HsE; try contradiction; destruct ys as [| y0 ys']; try reflexivity.
    + destruct HsE as (_ & _ & _ & <-). reflexivity.
    + rewrite (gentry_slot_proofs_fill κs Φ (ge_mod pv U) U σ ys' x Hf eq_refl),
        (gentry_slot_proofs_fill κs Φ' (ge_mod pv' U') U' σ' ys' x Hf' eq_refl).
      exact (Hu _ _ _ _ _ _ _ _ _ Hp eq_refl Hp' eq_refl Hf Hf' ys' x).
    + rewrite (gentry_slot_proofs_fill κs Φ (ge_def_mod pv A M U) U σ ys' x Hf eq_refl),
        (gentry_slot_proofs_fill κs Φ' (ge_def_mod pv' A' M' U') U' σ' ys' x Hf' eq_refl).
      exact (Hu _ _ _ _ _ _ _ _ _ Hp eq_refl Hp' eq_refl Hf Hf' ys' x).
  - apply (IH Φ' κs Hs0 Hn ltac:(cbn [gm_names] in Hnd; inversion Hnd; assumption)).
    intros * Hq HEq Hq' HEq'. exact (Hu _ _ _ _ _ _ _ _ _ (prefix_ext_keep _ _ _ _ _ Hnd Hq) HEq (prefix_ext_keep _ _ _ _ _ Hnd' Hq') HEq').
Qed.

(** The facts at one context the equation of two bodies over equal
    telescopes rests on: the derivation's premises read there. *)
Record set_body_eq_setting (Γ Δ Δ' : ctx) (Φ Φ' Φx Φx' : gmod) (l : nat) (entry_sort : string -> exp) : Prop :=
  { (** The two units are equal *)
    set_body_eq_wf : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ'
    (** The left body's expansion *)
  ; set_body_eq_xp : body_xp gc_deps gc_stack (Δ ++ Γ) Φ Φx
    (** The right body's expansion *)
  ; set_body_eq_xp' : body_xp gc_deps gc_stack (Δ' ++ Γ) Φ' Φx'
    (** The telescopes are equal extensions *)
  ; set_body_eq_tele_wf : gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Δ ≈ Δ'
    (** The left body's context is well formed *)
  ; set_body_eq_ctx_wf : ⊢ gc_deps ⍮ gc_stack ⍮ body_ctx Φx ++ Δ ++ Γ
    (** The right body's context is well formed *)
  ; set_body_eq_ctx_wf' : ⊢ gc_deps ⍮ gc_stack ⍮ body_ctx Φx' ++ Δ' ++ Γ
    (** The telescopes' suffixes are equal *)
  ; set_body_eq_tele : forall X Ψ X' Ψ', Δ = X ++ Ψ -> Δ' = X' ++ Ψ' -> List.length Ψ = List.length Ψ' -> set_ext_eq_with T γ Γ Ψ Ψ'
    (** The left body's context denotes *)
  ; set_body_eq_ctx : set_ctx T γ (body_ctx Φx ++ Δ ++ Γ)
    (** The right body's context denotes *)
  ; set_body_eq_ctx' : set_ctx T γ (body_ctx Φx' ++ Δ' ++ Γ)
    (** The left body's context has valid slots *)
  ; set_body_eq_slots : set_valid_slots T γ (body_ctx Φx ++ Δ ++ Γ)
    (** The right body's context has valid slots *)
  ; set_body_eq_slots' : set_valid_slots T γ (body_ctx Φx' ++ Δ' ++ Γ)
    (** A left definition's sort is a universe of its kind *)
  ; set_body_eq_sorts : forall y Φ0 E A M, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
      exists i, entry_sort y = abs_kind_sort (entry_kind E) (a_typ i)
    (** So is a right one's *)
  ; set_body_eq_sorts' : forall y Φ0' E' A' M', gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
      exists i, entry_sort y = abs_kind_sort (entry_kind E') (a_typ i)
    (** Partner definitions' types, filled in, are equal *)
  ; set_body_eq_types : forall y Φ0 E A M Φ0' E' A' M' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
      set_rel_exp_eq T γ (Δ ++ Γ) (entry_sort y) (exp_sub A σ) (exp_sub A' σ')
    (** A right definition's type, filled in, is of its sort *)
  ; set_body_eq_types' : forall y Φ0 E A M Φ0' E' A' M' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
      set_rel_exp_eq T γ (Δ' ++ Γ) (entry_sort y) (exp_sub A' σ') (exp_sub A' σ')
    (** Partner definitions' bodies, filled in, are equal *)
  ; set_body_eq_terms : forall y Φ0 E A M Φ0' E' A' M' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
      set_rel_exp_eq T γ (Δ ++ Γ) (exp_sub A σ) (exp_sub M σ) (exp_sub M' σ')
    (** A right definition's body, filled in, is of its type *)
  ; set_body_eq_terms' : forall y Φ0 E A M Φ0' E' A' M' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
      set_rel_exp_eq T γ (Δ' ++ Γ) (exp_sub A' σ') (exp_sub M' σ') (exp_sub M' σ')
    (** Partner modules, filled in, are equal units *)
  ; set_body_eq_units : forall y Φ0 E U Φ0' E' U' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
      set_rel_unit_eq T γ (Δ ++ Γ) (gunit_sub U σ) (gunit_sub U' σ')
    (** A right module, filled in, is a unit equal to itself *)
  ; set_body_eq_units' : forall y Φ0 E U Φ0' E' U' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
      set_rel_unit_eq T γ (Δ' ++ Γ) (gunit_sub U' σ') (gunit_sub U' σ')
    (** The left body's opens are valid *)
  ; set_body_eq_opens : forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> set_rel_modexp_eq T γ (Ψ ++ Δ ++ Γ) H H
    (** So are the right one's *)
  ; set_body_eq_opens' : forall k Ψ' H', nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> set_rel_modexp_eq T γ (Ψ' ++ Δ' ++ Γ) H' H'
    (** The left telescope is of assumptions *)
  ; set_body_eq_assumptions : all_assumptions Δ
    (** So is the right one *)
  ; set_body_eq_assumptions' : all_assumptions Δ'
    (** The left telescope's parameters are of evaluated sorts *)
  ; set_body_eq_params : set_params_evaluated T γ Γ Δ l
    (** So are the right one's *)
  ; set_body_eq_params' : set_params_evaluated T γ Γ Δ' l
    (** The bodies have one shape *)
  ; set_body_eq_shape : body_shape Φ Φ'
    (** So do their expansions *)
  ; set_body_eq_shape_xp : body_shape Φx Φx'
    (** The left body's names are distinct *)
  ; set_body_eq_names : List.NoDup (gm_names Φ) }.

(** The two bodies' units are valid. *)
Lemma set_body_eq_valid : forall Γ Δ Δ' Φ Φ' Φx Φx' l entry_sort, set_body_eq_setting Γ Δ Δ' Φ Φ' Φx Φx' l entry_sort ->
    set_valid_unit T γ Γ (me_lit (gu_open Δ Φ)) /\ set_valid_unit T γ Γ (me_lit (gu_open Δ' Φ')).
Proof.
  intros * [HUU Hx Hx' HΔw Hcx Hcx' Hext HC HC' Hsl Hsl' Htag Htag' HA HA' HM HM' HU HU' Ho Ho' HΔ HΔ' Hl Hl' Hs Hsxx Hnd].
  pose proof (fn_kinds_unique_of_ext Hfn) as Hfn0. pose proof (ext_eq_length _ _ _ _ _ HΔw) as Hlen.
  pose proof (body_xp_nopens _ _ _ _ _ Hx) as Hn. pose proof (body_xp_nopens _ _ _ _ _ Hx') as Hn'.
  pose proof (body_xp_expand _ _ _ _ _ Hx) as Hxe. pose proof (body_xp_expand _ _ _ _ _ Hx') as Hxe'.
  assert (HndX : List.NoDup (gm_names Φx)) by (rewrite (body_xp_names _ _ _ _ _ Hx); exact Hnd).
  assert (HndX' : List.NoDup (gm_names Φx'))
    by (rewrite (body_xp_names _ _ _ _ _ Hx'), <- (body_shape_names _ _ Hs); exact Hnd).
  (* the definitions of each side, filled in, are of their sorts *)
  assert (Hsv : set_body_sorts_valid T γ Φx (Δ ++ Γ)).
  { apply (set_body_sorts_valid_of_filled _ _ Hn HndX). intros * Hp HE Hf.
    destruct (body_partner_tm _ _ _ _ _ _ _ Hsxx Hn' Hp HE) as (Φ0' & E' & A' & M' & σ' & Hp' & HE' & Hf' & _).
    destruct (Htag _ _ _ _ _ Hp HE) as [i Hi]. exists i. rewrite <- Hi.
    exact (set_rel_exp_eq_refl_left _ _ _ _ (HA _ _ _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hf Hf')). }
  assert (Hsv' : set_body_sorts_valid T γ Φx' (Δ' ++ Γ)).
  { apply (set_body_sorts_valid_of_filled _ _ Hn' HndX'). intros y Φ0' E' A' M' σ' Hp' HE' Hf'.
    destruct (body_partner_tm _ _ _ _ _ _ _ (body_shape_sym _ _ Hsxx) Hn Hp' HE') as (Φ0 & E & A0 & M0 & σ0 & Hp & HE & Hf & _).
    destruct (Htag' _ _ _ _ _ Hp' HE') as [i Hi]. exists i. rewrite <- Hi.
    exact (HA' _ _ _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hf Hf'). }
  (* both sides are valid units *)
  assert (HK : set_valid_unit T γ Γ (me_lit (gu_open Δ Φ))).
  { apply (set_valid_unit_body_of _ _ _ _ l (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_left HUU)) Hx Hcx HΔ Hl HC Hsl Hsv
             (body_shape_l _ _ Hs) (body_shape_l _ _ Hsxx)).
    intros k Ψ H Hk. destruct (Ho _ _ _ Hk) as (G & G' & [_ _ _ Hv _ _]). exact Hv. }
  assert (HK' : set_valid_unit T γ Γ (me_lit (gu_open Δ' Φ'))).
  { apply (set_valid_unit_body_of _ _ _ _ l (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_right HUU)) Hx' Hcx' HΔ' Hl' HC' Hsl' Hsv'
             (body_shape_r _ _ Hs) (body_shape_r _ _ Hsxx)).
    intros k Ψ H Hk. destruct (Ho' _ _ _ Hk) as (G & G' & [_ _ _ Hv _ _]). exact Hv. }
  split; assumption.
Qed.

(** The two bodies push the same proofs. *)
Lemma set_body_eq_proofs : forall Γ Δ Δ' Φ Φ' Φx Φx' l entry_sort, set_body_eq_setting Γ Δ Δ' Φ Φ' Φx Φx' l entry_sort ->
    forall κs, set_slots_coherent γ Γ κs -> forall ys x,
      unit_member_proofs γ κs (gu_open Δ Φ) ys x = unit_member_proofs γ κs (gu_open Δ' Φ') ys x.
Proof.
  intros * [HUU Hx Hx' HΔw Hcx Hcx' Hext HC HC' Hsl Hsl' Htag Htag' HA HA' HM HM' HU HU' Ho Ho' HΔ HΔ' Hl Hl' Hs Hsxx Hnd]
    κs Hκ ys x.
  pose proof (ext_eq_length _ _ _ _ _ HΔw) as Hlen.
  pose proof (body_xp_nopens _ _ _ _ _ Hx) as Hn.
  pose proof (body_xp_expand _ _ _ _ _ Hx) as Hxe. pose proof (body_xp_expand _ _ _ _ _ Hx') as Hxe'.
  assert (HndX : List.NoDup (gm_names Φx)) by (rewrite (body_xp_names _ _ _ _ _ Hx); exact Hnd).
  rewrite !unit_member_proofs_tele_out. cbn [moddef_member_proofs].
  rewrite (tele_out_proofs_assumptions (List.rev Δ') (List.rev Δ) κs (List.Forall_rev HΔ') (List.Forall_rev HΔ)
             ltac:(rewrite !List.length_rev; symmetry; exact Hlen)).
  rewrite <- (proj2 (body_member_proofs_expand γ Φ (tele_out_proofs γ κs (List.rev Δ)))),
    <- (proj2 (body_member_proofs_expand γ Φ' (tele_out_proofs γ κs (List.rev Δ)))), <- Hxe, <- Hxe'.
  rewrite (body_member_lookup_eq_filled Φx Φx' _ Hsxx Hn HndX); [reflexivity |].
  intros * Hp HEu Hp' HEu' Hf Hf' ys0 x0.
  destruct (HU _ _ _ _ _ _ _ _ _ Hp HEu Hp' HEu' Hf Hf') as (G1 & G2 & [_ _ _ _ _ HprU]).
  exact (HprU _ (set_slots_coherent_tele_out γ _ _ _ HΔ Hκ) ys0 x0).
Qed.

(** The two bodies have equal values. *)
Lemma set_body_eq_values : forall Γ Δ Δ' Φ Φ' Φx Φx' l entry_sort F F', set_body_eq_setting Γ Δ Δ' Φ Φ' Φx Φx' l entry_sort ->
    set_modexp_denotes T γ Γ (me_lit (gu_open Δ Φ)) F -> set_modexp_denotes T γ Γ (me_lit (gu_open Δ' Φ')) F' ->
    forall ρ, set_env_in T γ Γ ρ -> set_module_eq γ (F ρ) (F' ρ).
Proof.
  intros * Hset HF HF' ρ Hρ. pose proof (set_body_eq_proofs _ _ _ _ _ _ _ _ _ Hset) as Hpr.
  destruct Hset as [HUU Hx Hx' HΔw Hcx Hcx' Hext HC HC' Hsl Hsl' Htag Htag' HA HA' HM HM' HU HU' Ho Ho' HΔ HΔ' Hl Hl' Hs Hsxx Hnd].
  pose proof (fn_kinds_unique_of_ext Hfn) as Hfn0. pose proof (ext_eq_length _ _ _ _ _ HΔw) as Hlen.
  pose proof (body_xp_nopens _ _ _ _ _ Hx) as Hn. pose proof (body_xp_nopens _ _ _ _ _ Hx') as Hn'.
  pose proof (body_xp_expand _ _ _ _ _ Hx) as Hxe. pose proof (body_xp_expand _ _ _ _ _ Hx') as Hxe'.
  assert (HndX : List.NoDup (gm_names Φx)) by (rewrite (body_xp_names _ _ _ _ _ Hx); exact Hnd).
  pose proof (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ) as Hm1. apply set_interp_me_lit_iff in Hm1.
  pose proof (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ) as Hm2. apply set_interp_me_lit_iff in Hm2.
  inversion Hm1 as [? ? ? ? P1 m1 HP1 HL1]; subst. inversion Hm2 as [? ? ? ? P2 m2 HP2 HL2]; subst.
  apply (set_unit_params_eq_ext T γ Hfn0 Hmods (List.rev Δ) (List.rev Δ') nil nil Γ ρ P1 P2 (md_body sm_open Φ) (md_body sm_open Φ')
           (F ρ) (F' ρ) (List.Forall_rev HΔ) (List.Forall_rev HΔ') ltac:(rewrite !List.length_rev; exact Hlen));
    [| exact Hρ | exact Hρ | exact HL1 | exact HL2 | |].
  - intros k. rewrite !List.app_nil_r.
    apply (Hext (List.firstn (List.length Δ - k) Δ) _ (List.firstn (List.length Δ' - k) Δ') _
             (rev_firstn_rev_suffix Δ k) (rev_firstn_rev_suffix Δ' k)).
    rewrite !List.length_rev, !List.length_firstn, !List.length_rev. lia.
  - intros ys x. rewrite HP1, HP2. exact (Hpr _ (set_slots_coherent_env T γ _ _ Hρ) ys x).
  - intros ρ' n1 n2 Hρ1 Hρ2 Hn1 Hn2. cbn [List.app] in Hρ1, Hρ2, Hn1, Hn2. rewrite List.rev_involutive in Hρ1, Hρ2, Hn1, Hn2.
    inversion Hn1 as [? ? ? ? ms1 ρo1 Hg1 |]; subst. inversion Hn2 as [? ? ? ? ms2 ρo2 Hg2 |]; subst.
    apply set_module_eq_members.
    apply (set_interp_gmod_eq_filled _ _ (Δ ++ Γ) (Δ' ++ Γ) ρ' _ _ _ _ Hsxx Hn HndX Hg1 Hg2).
    + intros * Hp HE Hp' HE' Hf Hf' Hv Hv'.
      destruct (HM _ _ _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hf Hf') as (FA & FM & FM' & [_ HFM HFM' EM _]).
      destruct (HM' _ _ _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hf Hf') as (FA2 & FM2 & _ & [_ HFM2 _ _ _]).
      eapply set_eq_trans; [exact (set_denotes_unique _ _ _ _ _ HFM _ _ _ Hρ1 Hv) |].
      eapply set_eq_trans; [exact (EM _ Hρ1) |].
      eapply set_eq_trans; [exact (set_denotes_across _ _ _ _ _ _ _ HΔw HFM' HFM2 Hρ1 Hρ2) |].
      exact (set_eq_sym _ _ (set_denotes_unique _ _ _ _ _ HFM2 _ _ _ Hρ2 Hv')).
    + intros * Hp HEu Hp' HEu' Hf Hf' Hm Hm'.
      destruct (HU _ _ _ _ _ _ _ _ _ Hp HEu Hp' HEu' Hf Hf') as (G1 & G2 & [HG1 HG2 EG _ _ _]).
      destruct (HU' _ _ _ _ _ _ _ _ _ Hp HEu Hp' HEu' Hf Hf') as (G3 & _ & [HG3 _ _ _ _ _]).
      eapply set_module_eq_trans; [exact (set_modexp_denotes_unique _ _ _ _ _ HG1 _ _ _ Hρ1 Hm) |].
      eapply set_module_eq_trans; [exact (EG _ Hρ1) |].
      eapply set_module_eq_trans; [exact (set_modexp_denotes_across _ _ _ _ _ _ _ HΔw HG2 HG3 Hρ1 Hρ2) |].
      exact (set_module_eq_sym _ _ (set_modexp_denotes_unique _ _ _ _ _ HG3 _ _ _ Hρ2 Hm')).
Qed.

(** The whole extensions of equal extensions denote. *)
Lemma set_ext_eq_suffixes_whole : forall Γ Δ Δ', set_rel_ext_eq_suffixes T γ Γ Δ Δ' -> List.length Δ = List.length Δ' ->
    set_ctx T γ (Δ ++ Γ) /\ set_ctx T γ (Δ' ++ Γ).
Proof. intros * [Hsuf _ _] Hlen. destruct (Hsuf nil Δ nil Δ' eq_refl eq_refl Hlen) as [HL HR _]. split; assumption. Qed.

End UnitSteps.

(** ** The Rules of Extensions *)

Lemma set_rule_ext_eq_nil : forall Γ, set_ctx_slots Θ Ξ T γ Γ -> set_ext_eq_suffixes Θ Ξ T γ Γ nil nil.
Proof.
  intros Γ HΓ. set_open. destruct HΓ as [HΓ Hsl]. constructor; [| exact Hsl | exact Hsl].
  intros [| ? ?] Ψ [| ? ?] Ψ' E E' _; try discriminate. cbn in E, E'. subst. exact (set_ext_eq_with_nil _ HΓ).
Qed.

Lemma set_rule_ext_eq_ass : forall Γ Ψ Ψ' κ A A' S S', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> set_ext_eq_suffixes Θ Ξ T γ Γ Ψ Ψ' ->
    set_exp_eq Θ Ξ T γ (Ψ ++ Γ) S A A -> set_exp_eq Θ Ξ T γ (Ψ' ++ Γ) S' A' A' ->
    set_subtyp Θ Ξ T γ (Ψ ++ Γ) A A' -> set_subtyp Θ Ξ T γ (Ψ ++ Γ) A' A ->
    set_ext_eq_suffixes Θ Ξ T γ Γ (ce_ass κ A :: Ψ) (ce_ass κ A' :: Ψ').
Proof.
  intros * HΨw HΨ HAe HA'e Hs Hs'. set_open. pose proof (ext_eq_length _ _ _ _ _ HΨw) as Hlen.
  destruct HΨ as [Hsuf Hsl Hsl']. destruct HAe as (FS & FA & FA2 & HA). destruct HA'e as (FS' & FA' & FA'2 & HA').
  constructor.
  - apply (set_ext_eq_suffixes_eq_cons _ _ _ _ _ Hsuf Hlen).
    pose proof (Hsuf nil Ψ nil Ψ' eq_refl eq_refl Hlen) as Hwh. eapply set_ext_eq_with_ass; eassumption.
  - exact (set_valid_slots_extend_plain T γ _ (ce_ass κ A) Hsl eq_refl).
  - exact (set_valid_slots_extend_plain T γ _ (ce_ass κ A') Hsl' eq_refl).
Qed.

Lemma set_rule_ext_eq_def : forall Γ Ψ Ψ' A A' M M', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> set_ext_eq_suffixes Θ Ξ T γ Γ Ψ Ψ' ->
    set_exp_eq Θ Ξ T γ (Ψ ++ Γ) A M M' -> set_exp_eq Θ Ξ T γ (Ψ' ++ Γ) A' M' M' ->
    set_ext_eq_suffixes Θ Ξ T γ Γ (ce_def A M :: Ψ) (ce_def A' M' :: Ψ').
Proof.
  intros * HΨw HΨ HMe HM'e. set_open. pose proof (ext_eq_length _ _ _ _ _ HΨw) as Hlen.
  destruct HΨ as [Hsuf Hsl Hsl']. destruct HMe as (FA & FM & FM' & HM). destruct HM'e as (FA' & FM2 & FM2' & HM').
  constructor.
  - apply (set_ext_eq_suffixes_eq_cons _ _ _ _ _ Hsuf Hlen).
    pose proof (Hsuf nil Ψ nil Ψ' eq_refl eq_refl Hlen) as Hwh. eapply set_ext_eq_with_def; eassumption.
  - exact (set_valid_slots_extend_plain T γ _ (ce_def A M) Hsl eq_refl).
  - exact (set_valid_slots_extend_plain T γ _ (ce_def A' M') Hsl' eq_refl).
Qed.

Lemma set_rule_ext_eq_mod : forall Γ Ψ Ψ' U U', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> set_ext_eq_suffixes Θ Ξ T γ Γ Ψ Ψ' ->
    set_unit_eq Θ Ξ T γ (Ψ ++ Γ) U U' -> set_unit_eq Θ Ξ T γ (Ψ' ++ Γ) U' U' ->
    set_ext_eq_suffixes Θ Ξ T γ Γ (ce_mod U :: Ψ) (ce_mod U' :: Ψ').
Proof.
  intros * HΨw HΨ HUe HU'e. set_open. pose proof (ext_eq_length _ _ _ _ _ HΨw) as Hlen.
  destruct HΨ as [Hsuf Hsl Hsl']. destruct HUe as (FU & FU' & HU). destruct HU'e as (FU2 & FU2' & HU').
  constructor.
  - apply (set_ext_eq_suffixes_eq_cons _ _ _ _ _ Hsuf Hlen).
    pose proof (Hsuf nil Ψ nil Ψ' eq_refl eq_refl Hlen) as Hwh. eapply set_ext_eq_with_mod; eassumption.
  - split; [exact Hsl | intros U0 HU0; injection HU0 as <-; destruct HU as [_ _ _ Hv _ _]; exact Hv].
  - split; [exact Hsl' | intros U0 HU0; injection HU0 as <-; destruct HU' as [_ _ _ Hv _ _]; exact Hv].
Qed.

Lemma set_rule_ext_eq_dm : forall Γ Ψ Ψ' A A' M M' E E', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> set_ext_eq_suffixes Θ Ξ T γ Γ Ψ Ψ' ->
    set_exp_eq Θ Ξ T γ (Ψ ++ Γ) A M M' -> set_exp_eq Θ Ξ T γ (Ψ' ++ Γ) A' M' M' ->
    set_unit_eq Θ Ξ T γ (Ψ ++ Γ) (gu_mk nil (md_alias E)) (gu_mk nil (md_alias E')) ->
    set_unit_eq Θ Ξ T γ (Ψ' ++ Γ) (gu_mk nil (md_alias E')) (gu_mk nil (md_alias E')) ->
    set_ext_eq_suffixes Θ Ξ T γ Γ (ce_dm A M (gu_mk nil (md_alias E)) :: Ψ) (ce_dm A' M' (gu_mk nil (md_alias E')) :: Ψ').
Proof.
  intros * HΨw HΨ HMe HM'e HUe HU'e. set_open. pose proof (ext_eq_length _ _ _ _ _ HΨw) as Hlen.
  destruct HΨ as [Hsuf Hsl Hsl']. destruct HMe as (FA & FM & FM' & HM). destruct HM'e as (FA' & FM2 & FM2' & HM').
  destruct HUe as (FU & FU' & HU). destruct HU'e as (FU2 & FU2' & HU').
  constructor.
  - apply (set_ext_eq_suffixes_eq_cons _ _ _ _ _ Hsuf Hlen).
    pose proof (Hsuf nil Ψ nil Ψ' eq_refl eq_refl Hlen) as Hwh. eapply set_ext_eq_with_dm; eassumption.
  - split; [exact Hsl | intros U0 HU0; injection HU0 as <-; destruct HU as [_ _ _ Hv _ _]; exact Hv].
  - split; [exact Hsl' | intros U0 HU0; injection HU0 as <-; destruct HU' as [_ _ _ Hv _ _]; exact Hv].
Qed.

(** ** The Rules of Units over Equal Telescopes *)

Lemma set_rule_unit_eq_alias : forall Γ Δ Δ' E E' l ps,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E') ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' -> set_ext_eq_suffixes Θ Ξ T γ Γ Δ Δ' ->
    all_assumptions Δ -> all_assumptions Δ' -> (forall k, parameter_sort l (ps k)) ->
    (forall Δ1 κ A Δ2, Δ = Δ1 ++ ce_ass κ A :: Δ2 -> set_exp_eq Θ Ξ T γ (Δ2 ++ Γ) (ps (List.length Δ2)) A A) ->
    (forall Δ1 κ A Δ2, Δ' = Δ1 ++ ce_ass κ A :: Δ2 -> set_exp_eq Θ Ξ T γ (Δ2 ++ Γ) (ps (List.length Δ2)) A A) ->
    set_modexp_eq Θ Ξ T γ (Δ ++ Γ) E E' -> set_modexp_eq Θ Ξ T γ (Δ' ++ Γ) E' E' ->
    set_unit_eq Θ Ξ T γ Γ (gu_mk Δ (md_alias E)) (gu_mk Δ' (md_alias E')).
Proof.
  intros * HUU HΔw HΔs HΔ HΔ' Hps HAs HAs' HEe HE'e. set_open.
  pose proof (set_params_evaluated_of_sorts T γ _ _ _ _ Hps (fun Δ1 κ A Δ2 E0 => HAs Δ1 κ A Δ2 E0 _ _ Hμ)) as Hl.
  pose proof (set_params_evaluated_of_sorts T γ _ _ _ _ Hps (fun Δ1 κ A Δ2 E0 => HAs' Δ1 κ A Δ2 E0 _ _ Hμ)) as Hl'.
  pose proof (set_ext_eq_suffixes_eq T γ _ _ _ HΔs) as Hext.
  pose proof HEe as (G & G' & [_ _ _ HvE _ _]). pose proof HE'e as (G2 & _ & [_ _ _ HvE2 _ _]).
  pose proof (set_valid_unit_alias_of Hfnx Hmods _ _ _ _ (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_left HUU)) HΔ Hl HvE) as HK.
  pose proof (set_valid_unit_alias_of Hfnx Hmods _ _ _ _ (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_right HUU)) HΔ' Hl' HvE2) as HK'.
  destruct (set_valid_unit_rel T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HK) as (F & _ & [HF _ _]).
  destruct (set_valid_unit_rel T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HK') as (F' & _ & [HF' _ _]).
  exists F, F'. constructor; [exact HF | exact HF' | | exact HK | exact HK' |].
  - exact (set_unit_alias_eq_values Hfnx Hmods _ _ _ _ _ _ _ HΔw Hext HΔ HΔ' HEe HE'e HF HF').
  - exact (set_unit_alias_eq_proofs _ _ _ _ _ HΔw HΔ HΔ' HEe).
Qed.

Lemma set_rule_unit_eq_body : forall Γ Δ Δ' Φ Φ' Φx Φx' l ps (entry_sort : string -> exp),
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' ->
    body_xp Θ Ξ (Δ ++ Γ) Φ Φx -> body_xp Θ Ξ (Δ' ++ Γ) Φ' Φx' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' -> set_ext_eq_suffixes Θ Ξ T γ Γ Δ Δ' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx ++ Δ ≈ body_ctx Φx ++ Δ -> set_ext_eq_suffixes Θ Ξ T γ Γ (body_ctx Φx ++ Δ) (body_ctx Φx ++ Δ) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx' ++ Δ' ≈ body_ctx Φx' ++ Δ' -> set_ext_eq_suffixes Θ Ξ T γ Γ (body_ctx Φx' ++ Δ') (body_ctx Φx' ++ Δ') ->
    (forall y Φ0 E A M, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       exists i, entry_sort y = abs_kind_sort (entry_kind E) (a_typ i)) ->
    (forall y Φ0' E' A' M', gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       exists i, entry_sort y = abs_kind_sort (entry_kind E') (a_typ i)) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       set_exp_eq Θ Ξ T γ (Δ ++ Γ) (entry_sort y) (exp_sub A σ) (exp_sub A' σ')) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       set_exp_eq Θ Ξ T γ (Δ' ++ Γ) (entry_sort y) (exp_sub A' σ') (exp_sub A' σ')) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       set_exp_eq Θ Ξ T γ (Δ ++ Γ) (exp_sub A σ) (exp_sub M σ) (exp_sub M' σ')) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       set_exp_eq Θ Ξ T γ (Δ' ++ Γ) (exp_sub A' σ') (exp_sub M' σ') (exp_sub M' σ')) ->
    (forall y Φ0 E U Φ0' E' U' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       set_unit_eq Θ Ξ T γ (Δ ++ Γ) (gunit_sub U σ) (gunit_sub U' σ')) ->
    (forall y Φ0 E U Φ0' E' U' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       set_unit_eq Θ Ξ T γ (Δ' ++ Γ) (gunit_sub U' σ') (gunit_sub U' σ')) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> set_modexp_eq Θ Ξ T γ (Ψ ++ Δ ++ Γ) H H) ->
    (forall k Ψ' H', nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> set_modexp_eq Θ Ξ T γ (Ψ' ++ Δ' ++ Γ) H' H') ->
    all_assumptions Δ -> all_assumptions Δ' -> (forall k, parameter_sort l (ps k)) ->
    (forall Δ1 κ A Δ2, Δ = Δ1 ++ ce_ass κ A :: Δ2 -> set_exp_eq Θ Ξ T γ (Δ2 ++ Γ) (ps (List.length Δ2)) A A) ->
    (forall Δ1 κ A Δ2, Δ' = Δ1 ++ ce_ass κ A :: Δ2 -> set_exp_eq Θ Ξ T γ (Δ2 ++ Γ) (ps (List.length Δ2)) A A) ->
    body_shape Φ Φ' -> body_shape Φx Φx' -> List.NoDup (gm_names Φ) ->
    set_unit_eq Θ Ξ T γ Γ (gu_open Δ Φ) (gu_open Δ' Φ').
Proof.
  intros * HUU Hx Hx' HΔw HΔs Hxb Hb Hxb' Hb' Htag Htag' HA0 HA0' HM0 HM0' HU0 HU0' Ho0 Ho0' HΔ HΔ' Hps HAs HAs' Hs Hsxx Hnd.
  set_open.
  pose proof (proj1 (set_ext_eq_suffixes_whole _ _ _ Hb eq_refl)) as HC.
  pose proof (proj1 (set_ext_eq_suffixes_whole _ _ _ Hb' eq_refl)) as HC'.
  pose proof (set_ext_eq_suffixes_slots T γ _ _ _ Hb) as Hsl. pose proof (set_ext_eq_suffixes_slots T γ _ _ _ Hb') as Hsl'.
  pose proof (ext_eq_ctx_left _ _ _ _ _ Hxb) as Hcx. pose proof (ext_eq_ctx_left _ _ _ _ _ Hxb') as Hcx'.
  rewrite <- List.app_assoc in HC, HC', Hsl, Hsl', Hcx, Hcx'.
  assert (Hset : set_body_eq_setting Γ Δ Δ' Φ Φ' Φx Φx' l entry_sort).
  { refine {| set_body_eq_wf := HUU; set_body_eq_xp := Hx; set_body_eq_xp' := Hx'; set_body_eq_tele_wf := HΔw;
              set_body_eq_ctx_wf := Hcx; set_body_eq_ctx_wf' := Hcx'; set_body_eq_tele := set_ext_eq_suffixes_eq T γ _ _ _ HΔs;
              set_body_eq_ctx := HC; set_body_eq_ctx' := HC'; set_body_eq_slots := Hsl; set_body_eq_slots' := Hsl';
              set_body_eq_sorts := Htag; set_body_eq_sorts' := Htag';
              set_body_eq_assumptions := HΔ; set_body_eq_assumptions' := HΔ';
              set_body_eq_params := set_params_evaluated_of_sorts T γ _ _ _ _ Hps (fun Δ1 κ A Δ2 E0 => HAs Δ1 κ A Δ2 E0 _ _ Hμ);
              set_body_eq_params' := set_params_evaluated_of_sorts T γ _ _ _ _ Hps (fun Δ1 κ A Δ2 E0 => HAs' Δ1 κ A Δ2 E0 _ _ Hμ);
              set_body_eq_shape := Hs; set_body_eq_shape_xp := Hsxx; set_body_eq_names := Hnd |}.
    - intros; eapply HA0; eassumption. - intros; eapply HA0'; eassumption.
    - intros; eapply HM0; eassumption. - intros; eapply HM0'; eassumption.
    - intros; eapply HU0; eassumption. - intros; eapply HU0'; eassumption.
    - intros; eapply Ho0; eassumption. - intros; eapply Ho0'; eassumption. }
  destruct (set_body_eq_valid Hfnx Hmods _ _ _ _ _ _ _ _ _ Hset) as [HK HK'].
  destruct (set_valid_unit_rel T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HK) as (F & _ & [HF _ _]).
  destruct (set_valid_unit_rel T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HK') as (F' & _ & [HF' _ _]).
  exists F, F'. constructor; [exact HF | exact HF' | | exact HK | exact HK' |].
  - exact (set_body_eq_values Hfnx Hmods _ _ _ _ _ _ _ _ _ _ _ Hset HF HF').
  - exact (set_body_eq_proofs _ _ _ _ _ _ _ _ _ Hset).
Qed.

End Units.
