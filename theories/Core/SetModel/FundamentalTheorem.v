(** * The Fundamental Theorem of the Set Model

    Every judgment of a well-formed global context holds in the set model
    at a valuation modelling the global context ([set_fundamental]): by
    induction on the derivation, each rule is its set rule, stated and
    proved in the file of its construct. *)

From Stdlib Require Import String List Lia.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Respects ContextRelation JudgmentSubstitution.
From Mctt.Core.SetModel Require Import Judgments.
From Mctt.Core.SetModel.Cases Require Import UniverseCases PropCases FunctionCases LevelCases VariableCases LetCases
  SubtypingCases ContextCases ValidUnit MemberTypes ModuleCases Unit Canon App Sel UnitCases IndCases RecordCases ElimCases
  ElimViewCases.
From Mctt.Core.Syntactic.System.Records Require Import Typing.
From Mctt.Core.Syntactic Require Import Syntax Members Presup.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
Import ListNotations.

Section FundamentalTheorem.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.
  (** The global context is well formed *)
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  (** The valuation models the global context *)
  Hypothesis Hok : set_gctx_ok T γ.
  (** A λ's kinds are unique across equal extensions *)
  Hypothesis Hfn : fn_kinds_unique_ext.

(** An assumption of a type equal to another reads the other's. *)
Lemma wf_sub_id_conv_ass : forall Γ κ A A' Srt, gc_deps ⍮ gc_stack ⍮ Γ ⊢ A : Srt -> sort_kind Srt κ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ A ≈ A' : Srt -> gc_deps ⍮ gc_stack ⍮ ce_ass κ A' :: Γ ⊢ˢ sb_id : ce_ass κ A :: Γ.
Proof.
  intros * HA Hk HAA'. pose proof (presup_exp_eq_right HAA') as HA'.
  eapply wf_sub_id_extend; [apply wf_sub_id; exact (presup_exp_ctx HA) | exact HA | exact Hk | exact HA' | exact Hk |].
  eapply wf_subtyp_refl; [exact HA | destruct Hk; constructor |]. mauto 3.
Qed.

(** The same for types of the kind [κ] next to a universe. *)
Lemma wf_sub_id_conv_univ : forall Γ U κ A A', gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵤ U ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ A ≈ A' : abs_kind_sort κ U -> gc_deps ⍮ gc_stack ⍮ ce_ass κ A' :: Γ ⊢ˢ sb_id : ce_ass κ A :: Γ.
Proof.
  intros * HU HAA'. destruct κ; cbn [abs_kind_sort] in HAA'.
  - destruct (wf_exp_eq_is_univ_large HU HAA') as [i Hi].
    exact (wf_sub_id_conv_ass _ _ _ _ _ (presup_exp_eq_left Hi) (sort_kind_universe i) Hi).
  - exact (wf_sub_id_conv_ass _ _ _ _ _ (presup_exp_eq_left HAA') sort_kind_prop HAA').
  - exact (wf_sub_id_conv_ass _ _ _ _ _ (presup_exp_eq_left HAA') sort_kind_level HAA').
Qed.

(** A context extended by a type of the kind [κ] next to a universe,
    equal to another, by the other. *)
Lemma wf_ctx_conv_univ : forall Γ U κ A A', gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵤ U ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ A ≈ A' : abs_kind_sort κ U -> ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κ A' :: Γ.
Proof. intros * HU HAA'. exact (wf_ctx_extend_univ_kind _ _ _ _ _ _ HU (presup_exp_eq_right HAA')). Qed.

(** A definition of equal type and body reads the other's. *)
Lemma wf_conv_def : forall Γ A A' M M' Srt, gc_deps ⍮ gc_stack ⍮ Γ ⊢ A : Srt -> type_sort Srt ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ A ≈ A' : Srt -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ M ≈ M' : A ->
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_def A' M' :: Γ /\ gc_deps ⍮ gc_stack ⍮ ce_def A' M' :: Γ ⊢ˢ sb_id : ce_def A M :: Γ.
Proof.
  intros * HA HS HAA' HMM'. pose proof (presup_exp_eq_right HAA') as HA'.
  pose proof (presup_exp_eq_left HMM') as HM. pose proof (presup_exp_eq_right HMM') as HM'.
  assert (Hsub : gc_deps ⍮ gc_stack ⍮ Γ ⊢ A ⊆ A') by (eapply wf_subtyp_refl; eassumption).
  assert (Hsub' : gc_deps ⍮ gc_stack ⍮ Γ ⊢ A' ⊆ A) by (eapply wf_subtyp_refl; [exact HA | exact HS | mauto 3]).
  assert (HM'A' : gc_deps ⍮ gc_stack ⍮ Γ ⊢ M' : A') by (eapply wf_exp_subtyp; [exact HM' | exact HA' | exact HS | exact Hsub]).
  split; [eapply wf_ctx_extend_def; eassumption |].
  eapply wf_sub_id_extend_def; [apply wf_sub_id; exact (presup_exp_ctx HA) | exact HA | exact HS | exact HA' | exact HS
                               | exact Hsub' | exact HM | exact HM'A' | mauto 3].
Qed.

(** Module slots of equal units are equal one-entry extensions. *)
Lemma wf_ext_eq_one_mod : forall Γ U U', gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U' ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ ce_mod U :: nil ≈ ce_mod U' :: nil.
Proof.
  intros * HU. eapply wf_ext_eq_mod; [constructor; exact (presup_unit_eq_ctx HU) | exact HU | exact (wf_unit_eq_refl_right HU)].
Qed.

(** So are definitions with module parts of equal types, bodies and units. *)
Lemma wf_ext_eq_one_dm : forall Γ A A' M M' E E' i, gc_deps ⍮ gc_stack ⍮ Γ ⊢ A : a_typ i ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ A ≈ A' : a_typ i -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ M : A -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ M ≈ M' : A ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E') ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ ce_dm A M (gu_mk nil (md_alias E)) :: nil ≈ ce_dm A' M' (gu_mk nil (md_alias E')) :: nil.
Proof.
  intros * HA HAA' HM HMM' HU. pose proof (presup_exp_eq_right HAA') as HA'.
  assert (HM'A' : gc_deps ⍮ gc_stack ⍮ Γ ⊢ M' : A')
    by (eapply wf_exp_subtyp; [exact (presup_exp_eq_right HMM') | exact HA' | constructor
                              | eapply wf_subtyp_refl; [exact HA' | constructor | exact HAA']]).
  eapply wf_ext_eq_dm; [constructor; exact (presup_exp_ctx HA) | exact HA | exact HAA' | exact HM | exact HMM' | exact HA' | exact HM'A'
                       | exact HU | exact (wf_unit_eq_refl_right HU)].
Qed.

(** A context extended by an assumption of a type equal to another is
    well formed. *)
Lemma wf_ctx_conv_ass : forall Γ κ A A' Srt, sort_kind Srt κ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ A ≈ A' : Srt ->
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κ A' :: Γ.
Proof. intros * Hk HAA'. eapply wf_ctx_extend; [exact (presup_exp_eq_right HAA') | exact Hk]. Qed.

(** The judgments the theorem concludes are in [Judgments.v]. *)

(** The induction hypotheses taken apart: contexts into their two parts,
    judgments into their denotations. *)
Ltac ft_ihs :=
  repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : set_rel_ctx_slots T γ _ |- _ => destruct H
    | H : set_rel_exp_eq _ _ _ _ _ _ |- _ => destruct H as (? & ? & ? & ?)
    | H : set_rel_universe T γ _ _ |- _ => destruct H as (? & [? ? ?])
    | H : set_rel_subtyp _ _ _ _ _ |- _ => destruct H as (? & ? & ?)
    | H : set_rel_unit_eq _ _ _ _ _ |- _ => destruct H as (? & ? & ?)
    | H : set_rel_modexp_eq _ _ _ _ _ |- _ => destruct H as (? & ? & ?)
    end.

(** A context below one an induction hypothesis gives. *)
Ltac ft_ctx :=
  first [ assumption
        | match goal with H : set_ctx _ _ (_ :: ?Γ) |- set_ctx _ _ ?Γ => exact (proj1 H) end
        | match goal with H : set_ctx _ _ (?Ψ ++ ?Γ) |- set_ctx _ _ ?Γ => exact (set_ctx_app_r _ _ _ _ H) end ].
Ltac ft_slots :=
  first [ assumption
        | match goal with H : set_valid_slots _ _ (_ :: ?Γ) |- set_valid_slots _ _ ?Γ => exact (proj1 H) end
        | match goal with H : set_valid_slots _ _ (?Ψ ++ ?Γ) |- set_valid_slots _ _ ?Γ => exact (set_valid_slots_app_r _ _ _ _ H) end ].
Ltac ft_cs := split; [ft_ctx | ft_slots].

(** A syntactic side condition from a premise. *)
Ltac ft_syn :=
  first [ eassumption
        | match goal with H : _ ⍮ _ ⍮ ?Δ ⊢ _ : _ |- ⊢ _ ⍮ _ ⍮ ?Δ => exact (presup_exp_ctx H) end
        | match goal with H : _ ⍮ _ ⍮ ?Δ ⊢ _ ≈ _ : _ |- ⊢ _ ⍮ _ ⍮ ?Δ => exact (presup_exp_eq_ctx H) end
        | (eapply wf_sub_single; [eassumption | first [eassumption | constructor] | first [eassumption | econstructor; eassumption]])
        | (eapply wf_sub_single_def; eassumption)
        | (eapply wf_sub_single_mod; eassumption)
        | (eapply wf_sub_single_mod; eapply wf_unit_eq_refl_left; eassumption)
        | (eapply wf_sub_single_dm; eassumption)
        | (eapply wf_sub_single_dm; [eassumption | eassumption | eapply wf_unit_eq_refl_left; eassumption])
        | (eapply wf_sub_id_conv_ass; [eassumption | first [eassumption | constructor | apply sort_kind_abs_kind_sort] | eassumption])
        | (eapply wf_ctx_conv_ass; [first [eassumption | constructor] | eassumption])
        | (eapply wf_sub_id_conv_univ; eassumption)
        | (eapply wf_ctx_conv_univ; eassumption) ].

(** A premise of a set rule from the hypotheses. *)
Ltac ft_prem := first [ eassumption | ft_ctx | ft_syn | (do 3 eexists; eassumption) | (do 2 eexists; eassumption) | reflexivity
                      | match goal with H : set_rel_ext_eq_suffixes T γ ?Γ ?Ψ ?Ψ', Hx : _ ⍮ _ ⍮ ?Γ ⊢ˣ ?Ψ ≈ ?Ψ' |- set_ext_eq_with _ _ ?Γ ?Ψ ?Ψ' =>
                          exact (set_ext_eq_suffixes_eq T γ _ _ _ H nil Ψ nil Ψ' eq_refl eq_refl (ext_eq_length _ _ _ _ _ Hx)) end
                      | (eapply set_exp_eq_left; eassumption) | (eapply set_exp_eq_with_left; eassumption)
                      | (econstructor; eassumption) ].

(** A case by its set rule. *)
Ltac ft_by lemma := split; [ft_cs | eapply lemma; ft_prem].

(** No extensions. *)
Lemma set_ext_eq_suffixes_nil : forall Γ, set_ctx T γ Γ -> set_valid_slots T γ Γ -> set_rel_ext_eq_suffixes T γ Γ nil nil.
Proof.
  intros Γ HΓ Hsl. constructor; [| exact Hsl | exact Hsl].
  intros [| ? ?] Ψ [| ? ?] Ψ' E E' _; try discriminate. cbn in E, E'. subst. exact (set_rule_ext_eq_nil T γ _ HΓ).
Qed.

(** Extensions by one more entry each: their suffixes are the whole ones
    or suffixes of the extensions before. *)
Lemma set_ext_eq_suffixes_cons : forall Γ Ψ Ψ' e e', set_rel_ext_eq_suffixes T γ Γ Ψ Ψ' -> List.length Ψ = List.length Ψ' ->
    set_ext_eq_with T γ Γ (e :: Ψ) (e' :: Ψ') ->
    set_valid_slots T γ (e :: Ψ ++ Γ) -> set_valid_slots T γ (e' :: Ψ' ++ Γ) -> set_rel_ext_eq_suffixes T γ Γ (e :: Ψ) (e' :: Ψ').
Proof.
  intros * [Hsuf _ _] Hlen Hwhole Hsl Hsl'. constructor; [| exact Hsl | exact Hsl'].
  intros [| x X] Ψ0 [| x' X'] Ψ0' E E' Hl.
  - cbn in E, E'. subst. exact Hwhole.
  - exfalso. apply (f_equal (@List.length centry)) in E, E'. cbn in E, E'. rewrite List.length_app in E'. lia.
  - exfalso. apply (f_equal (@List.length centry)) in E, E'. cbn in E, E'. rewrite List.length_app in E. lia.
  - injection E as _ E. injection E' as _ E'. exact (Hsuf _ _ _ _ E E' Hl).
Qed.

(** Equal extensions of a context give it. *)
Lemma set_ext_eq_suffixes_ctx_slots : forall Γ Δ Δ', set_rel_ext_eq_suffixes T γ Γ Δ Δ' -> set_rel_ctx_slots T γ Γ.
Proof.
  intros * [Hsuf Hsl _]. split; [| exact (set_valid_slots_app_r T γ _ _ Hsl)].
  exact (set_ext_eq_left _ _ _ _ _ (Hsuf Δ nil Δ' nil (eq_sym (List.app_nil_r Δ)) (eq_sym (List.app_nil_r Δ')) eq_refl)).
Qed.

(** A large universe is a universe. *)
Lemma set_rule_is_univ_large : forall Γ i, set_ctx T γ Γ -> set_rel_universe T γ Γ (a_typ i).
Proof.
  intros Γ i HΓ. exists (fun _ => large_universe_code T i). constructor; [exact HΓ | apply set_denotes_typ |].
  intros ρ _. exists (tower T (ul i)). split; [apply tower_grothendieck |]. exists (large_ordinal_set i). apply set_eq_refl.
Qed.

(** A universe at a level is a universe. *)
Lemma set_rule_is_univ_small : forall Γ n L FL FM FM', set_ctx T γ Γ -> set_exp_eq_with T γ Γ (a_level n) L L FL FM FM' ->
    set_rel_universe T γ Γ (a_univ L).
Proof.
  intros * HΓ HL. pose proof HL as [_ HM _ _ _].
  exists (fun ρ => level_universe_code T (FM ρ)). constructor; [exact HΓ | exact (set_denotes_univ T γ _ _ _ HM) |].
  intros ρ Hρ. destruct (level_value T γ _ _ _ _ _ _ _ HL Hρ) as (o & _ & Eo).
  exists (tower T (us o)). split; [apply tower_grothendieck |]. exists (FM ρ).
  unfold level_universe_code, universe_code. apply type_code_resp; [apply set_eq_refl |].
  apply separation_set_resp; [exact is_relevant_code_resp | exact is_relevant_code_resp | apply small_universe_set_eq; exact Eo | tauto].
Qed.

(** A family at an argument of its domain denotes the family's value at
    the argument's. *)
Lemma set_denotes_single_sub_with : forall Γ κ A N B S FA FAN FN FN2 FS FB FB2, fn_kinds_unique -> set_ctx T γ Γ ->
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κ A :: Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˢ sb_extend sb_id (se_exp N) : ce_ass κ A :: Γ ->
    set_denotes T γ Γ A FA -> set_exp_eq_with T γ Γ A N N FAN FN FN2 -> set_exp_eq_with T γ (ce_ass κ A :: Γ) S B B FS FB FB2 ->
    set_denotes T γ Γ (exp_sub B (sb_extend sb_id (se_exp N))) (fun ρ => body_function κ FB ρ (FN ρ)).
Proof.
  intros * Hfn0 HΓ Hc Hσ HA [HAN HN _ _ HNm] [_ HB _ _ _].
  apply (set_denotes_single_sub T γ _ _ _ _ _ _ _ _ Hfn0 (set_gctx_ok_modules _ _ Hok) HΓ Hc Hσ HA HN); [| exact HB].
  intros ρ Hρ. eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HAN HA Hρ) |].
  exact (HNm _ Hρ).
Qed.

(** An extension by one more entry each. *)
(** A premise under binders from its induction hypothesis. *)
Ltac ft_from_ih :=
  intros; match goal with IH : context [gc_deps = gc_deps -> gc_stack = gc_stack -> _] |- _ =>
    eapply proj2; eapply IH; solve [eauto] end.

(** The whole extensions of equal extensions denote, with valid slots. *)
Lemma set_ext_eq_suffixes_whole : forall Γ Δ Δ', set_rel_ext_eq_suffixes T γ Γ Δ Δ' -> List.length Δ = List.length Δ' ->
    set_ctx T γ (Δ ++ Γ) /\ set_ctx T γ (Δ' ++ Γ).
Proof. intros * [Hsuf _ _] Hlen. destruct (Hsuf nil Δ nil Δ' eq_refl eq_refl Hlen) as [HL HR _]. split; assumption. Qed.

Ltac ft_cs' :=
  first [ ft_cs | match goal with H : set_rel_ext_eq_suffixes T γ ?Γ _ _ |- set_rel_ctx_slots T γ ?Γ => exact (set_ext_eq_suffixes_ctx_slots _ _ _ H) end ].

Ltac ft_ext_cons :=
  match goal with Hx : _ ⍮ _ ⍮ ?Γ ⊢ˣ ?Ψ ≈ ?Ψ' |- set_rel_ext_eq_suffixes T γ ?Γ (_ :: ?Ψ) (_ :: ?Ψ') =>
    apply set_ext_eq_suffixes_cons; [assumption | exact (ext_eq_length _ _ _ _ _ Hx) | | |] end.

Theorem set_fundamental :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ = gc_deps -> Ξ = gc_stack -> set_rel_ctx_slots T γ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = gc_deps -> Ξ = gc_stack -> set_rel_ctx_slots T γ Γ /\ set_rel_exp_eq T γ Γ A M M) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Θ = gc_deps -> Ξ = gc_stack -> set_rel_ctx_slots T γ Γ /\ set_rel_exp_eq T γ Γ A M M') /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ = gc_deps -> Ξ = gc_stack -> set_rel_ctx_slots T γ Γ /\ set_rel_subtyp T γ Γ A A') /\
  (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> Θ = gc_deps -> Ξ = gc_stack -> set_rel_ctx_slots T γ Γ /\ set_rel_universe T γ Γ U) /\
  (forall Θ Ξ Γ Δ Δ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' -> Θ = gc_deps -> Ξ = gc_stack -> set_rel_ext_eq_suffixes T γ Γ Δ Δ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ = gc_deps -> Ξ = gc_stack -> set_rel_ctx_slots T γ Γ /\ set_rel_unit_eq T γ Γ U U') /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ = gc_deps -> Ξ = gc_stack -> set_rel_ctx_slots T γ Γ /\ set_rel_modexp_eq T γ Γ H H').
Proof.
  pose proof (fn_kinds_unique_of_ext Hfn) as Hfn0. pose proof (set_gctx_ok_modules _ _ Hok) as Hmods.
  apply syntactic_wf_mut_ind; intros; subst;
    repeat match goal with H : gc_deps = gc_deps -> gc_stack = gc_stack -> _ |- _ => specialize (H eq_refl eq_refl) end;
    ft_ihs.
  (* contexts *)
  - split; exact I.
  - split; [eapply set_rule_ctx_extend; eassumption | eapply set_rule_slots_extend_plain; [eassumption | reflexivity]].
  - split; [eapply set_rule_ctx_extend_def; [eassumption | do 3 eexists; eassumption] | eapply set_rule_slots_extend_plain; [eassumption | reflexivity]].
  - split; [eapply set_rule_ctx_extend_mod; ft_prem | eapply set_rule_slots_extend_mod; ft_prem].
  - split; [eapply set_rule_ctx_extend_dm; ft_prem | eapply set_rule_slots_extend_dm; ft_prem].
  (* terms *)
  - split; [ft_cs | apply set_rule_typ].
  - split; [ft_cs | eapply set_rule_univ; eassumption].
  - split; [ft_cs | apply set_rule_level].
  - split; [ft_cs | apply set_rule_llit; assumption].
  - split; [ft_cs | eapply set_rule_succl; eassumption].
  - split; [ft_cs | eapply set_rule_maxl; eassumption].
  - split; [ft_cs | apply set_rule_prop].
  - split; [ft_cs | apply set_rule_True].
  - split; [ft_cs | apply set_rule_tt].
  - split; [ft_cs | apply set_rule_False].
  - split; [ft_cs | eapply set_rule_absurd; eassumption].
  - ft_by set_rule_and.
  - ft_by set_rule_conj.
  - ft_by set_rule_left.
  - split; [ft_cs | eapply (set_rule_right T γ Hfn0 Hmods Γ P Q M); ft_prem].
  - ft_by set_rule_proof_tag.
  - ft_by set_rule_ind.
  - ft_by set_rule_con.
  - split; [ft_cs |].
    eapply (set_rule_elim T γ Hfn0 Hmods Hgw Hok); try eassumption; try reflexivity; try (do 3 eexists; eassumption);
      try ft_from_ih;
      intros; match goal with IH : context [set_rel_ext_eq_suffixes T γ _ _ _] |- set_ctx _ _ _ =>
        solve [eapply proj1; eapply set_ext_eq_suffixes_whole; [eapply IH; eauto | reflexivity]] end.
  - ft_by set_rule_pi.
  - split; [ft_cs | do 3 eexists; eapply set_rule_fn_with; ft_prem].
  - split; [ft_cs |]. eapply (set_rule_app T γ Γ κd κc i A B M N);
      [ft_ctx | ft_syn | eapply set_exp_eq_left; eassumption | eassumption | eassumption
      | eassumption | eapply (set_denotes_single_sub_with Γ κd A N B); ft_prem | intros; apply set_eq_refl].
  - split; [ft_cs | eapply set_exp_eq_refl_left; eapply set_rule_let_def_zeta; ft_prem].
  - split; [ft_cs | eapply set_exp_eq_refl_left; eapply set_rule_let_mod_zeta; ft_prem].
  - split; [ft_cs | eapply set_exp_eq_refl_left; eapply set_rule_let_dm_zeta; ft_prem].
  - match goal with |- _ /\ set_rel_exp_eq _ _ ?G ?A ?L _ => assert (HTm : gc_deps ⍮ gc_stack ⍮ G ⊢ L : A) by (eapply wf_mem; eassumption) end.
    ft_by set_rule_mem.
  - ft_by set_rule_var.
  - ft_by set_rule_record.
  - split; [ft_cs |]. eapply (set_rule_tuple T γ Hfn0 Hmods Hgw Hok); [ft_syn | ft_ctx | eassumption | eassumption | eassumption | eassumption | ft_from_ih
                                           | eassumption | eassumption | ft_from_ih | do 3 eexists; eassumption].
  - split; [ft_cs |]. eapply (set_rule_proj T γ Hfn0 Hmods Hgw Hok); [ft_syn | ft_ctx | eassumption | eassumption | eassumption | eassumption | ft_from_ih
                                          | eassumption | do 3 eexists; eassumption | eassumption].
  - split; [ft_cs | eapply set_rule_exp_eq_subtyp; eassumption].
  (* term equality *)
  - split; [ft_cs | apply set_rule_typ].
  - ft_by set_rule_univ.
  - split; [ft_cs | apply set_rule_level].
  - split; [ft_cs | apply set_rule_llit; assumption].
  - ft_by set_rule_succl.
  - ft_by set_rule_maxl.
  - ft_by set_rule_llit_succl.
  - ft_by set_rule_maxl_absorb.
  - ft_by set_rule_maxl_zero.
  - ft_by set_rule_maxl_assoc.
  - ft_by set_rule_maxl_comm.
  - ft_by set_rule_maxl_idem.
  - ft_by set_rule_succl_maxl.
  - ft_by set_rule_maxl_succl.
  - split; [ft_cs | apply set_rule_prop].
  - split; [ft_cs | apply set_rule_True].
  - split; [ft_cs | apply set_rule_False].
  - ft_by set_rule_absurd_cong.
  - ft_by set_rule_and_cong.
  - ft_by set_rule_ind.
  - ft_by set_rule_con.
  - split; [ft_cs |].
    eapply (set_rule_elim_cong T γ Hfn0 Hmods Hgw Hok); try eassumption; try reflexivity; try (do 3 eexists; eassumption);
      try ft_from_ih;
      intros; match goal with IH : context [set_rel_ext_eq_suffixes T γ _ _ _] |- set_ctx _ _ _ =>
        solve [eapply proj1; eapply set_ext_eq_suffixes_whole; [eapply IH; eauto | reflexivity]] end.
  - ft_by set_rule_pi_cong.
  - split; [ft_cs |].
    assert (Hc : gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_fn A M ≈ a_fn A' M' : a_pi κd κc A B) by (eapply wf_exp_eq_fn_cong; eassumption).
    pose proof (presup_exp_eq_left Hc). pose proof (presup_exp_eq_right Hc).
    eapply set_rule_fn_cong; ft_prem.
  - split; [ft_cs |].
    match goal with H : _ ⍮ _ ⍮ _ ⊢ N ≈ N' : _ |- _ => pose proof (presup_exp_eq_left H) end.
    eapply (set_rule_app_cong T γ Γ κd κc i A B M M' N N');
      [ft_ctx | ft_syn | eapply set_exp_eq_left; eassumption | eassumption | eassumption
      | eassumption | eapply (set_denotes_single_sub_with Γ κd A N B); ft_prem | intros; apply set_eq_refl].
  - split; [ft_cs |].
    destruct (wf_conv_def Γ A A' M M' Srt ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    eapply set_rule_let_def_cong; ft_prem.
  - split; [ft_cs |]. pose proof (wf_ext_eq_one_mod Γ U U' ltac:(eassumption)).
    eapply set_rule_let_mod_cong; ft_prem.
  - split; [ft_cs |]. pose proof (wf_ext_eq_one_dm Γ A A' M M' E E' i ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
                                     ltac:(eassumption) ltac:(eassumption)).
    eapply set_rule_let_dm_cong; ft_prem.
  - match goal with |- _ /\ set_rel_exp_eq _ _ ?G ?A ?L ?Rt =>
      assert (Hc : gc_deps ⍮ gc_stack ⍮ G ⊢ L ≈ Rt : A) by (eapply wf_exp_eq_mem_cong; eassumption) end.
    pose proof (presup_exp_eq_left Hc). ft_by set_rule_mem_cong.
  - ft_by set_rule_var.
  - ft_by set_rule_pi_beta.
  - split; [ft_cs |].
    eapply (set_rule_elim_iota T γ Hfn0 Hmods Hgw Hok); try eassumption; try reflexivity; try (do 3 eexists; eassumption);
      try ft_from_ih;
      intros; match goal with IH : context [set_rel_ext_eq_suffixes T γ _ _ _] |- set_ctx _ _ _ =>
        solve [eapply proj1; eapply set_ext_eq_suffixes_whole; [eapply IH; eauto | reflexivity]] end.
  - split; [ft_cs |].
    match goal with |- set_rel_exp_eq _ _ ?G ?A ?L ?R => assert (Hc : gc_deps ⍮ gc_stack ⍮ G ⊢ L ≈ R : A) end;
      [ eapply wf_exp_eq_elim_view; first [eassumption | reflexivity] |].
    pose proof (presup_exp_eq_right Hc).
    eapply (set_rule_elim_view T γ Hfn0 Hmods Hgw Hok); try eassumption; try reflexivity; try (do 3 eexists; eassumption);
      try ft_from_ih;
      intros; match goal with IH : context [set_rel_ext_eq_suffixes T γ _ _ _] |- set_ctx _ _ _ =>
        solve [eapply proj1; eapply set_ext_eq_suffixes_whole; [eapply IH; eauto | reflexivity]] end.
  - split; [ft_cs |].
    eapply (set_rule_con_view T γ Hfn0 Hmods Hok); try eassumption; try (do 3 eexists; eassumption); try ft_from_ih.
  - split; [ft_cs |].
    eapply (set_rule_con_rview T γ Hfn0 Hmods Hgw Hok); try eassumption; try (do 3 eexists; eassumption); try ft_from_ih.
  - ft_by set_rule_let_def_zeta.
  - ft_by set_rule_let_mod_zeta.
  - ft_by set_rule_let_dm_zeta.
  - match goal with |- _ /\ set_rel_exp_eq _ _ ?G ?A ?L ?Rt =>
      assert (Hc : gc_deps ⍮ gc_stack ⍮ G ⊢ L ≈ Rt : A) by (eapply wf_exp_eq_mem_delta; eassumption) end.
    pose proof (presup_exp_eq_left Hc). ft_by set_rule_mem_delta.
  - match goal with H : _ ∋ #_ ≔ _ : _ |- _ => pose proof (ctx_lookup_def_lookup _ _ _ _ H) end.
    ft_by set_rule_var_delta.
  - assert (Hc : gc_deps ⍮ gc_stack ⍮ Γ ⊢ M ≈ a_fn A (a_app (exp_wk M wk_shift) (a_var 0)) : a_pi κd κc A B)
      by (eapply wf_exp_eq_fn_eta; eassumption).
    pose proof (presup_exp_eq_right Hc). ft_by set_rule_fn_eta.
  - ft_by set_rule_irrelevant.
  - ft_by set_rule_record_cong.
  - split; [ft_cs |]. eapply (set_rule_tuple_cong T γ); [eassumption | eassumption | eassumption | eassumption |].
    intros. eexists. ft_from_ih.
  - split; [ft_cs |].
    match goal with H : _ ⍮ _ ⍮ _ ⊢ M ≈ M' : _ |- _ => pose proof (presup_exp_eq_left H) as HMl end.
    edestruct (set_rule_proj T γ Hfn0 Hmods Hgw Hok Γ M p R Ns k f U) as (FP & FPa & FPb & HPl);
      [ft_syn | ft_ctx | eassumption | eassumption | eassumption | eassumption | ft_from_ih | exact HMl
      | apply set_exp_eq_refl_left with (M' := M'); do 3 eexists; eassumption | eassumption |].
    eapply (set_rule_proj_cong T γ); [eassumption | exact HPl | eassumption].
  - split; [ft_cs |].
    match goal with H : _ ⍮ _ ⍮ _ ⊢ a_tuple T0 fs : T0 |- _ =>
      destruct (wf_tuple_inversion H) as [p0 R0 Ns0 i0 _ _ Hr0 Hl0 _ _ Hn0 _ _];
      destruct (wf_record_inversion Hr0) as [R1 Hl1 Hnd1 _ _ _ _ _ _ _ _ _] end.
    rewrite Hl0 in Hl1. injection Hl1 as <-. rewrite <- Hn0 in Hnd1.
    eapply (set_rule_field_beta T γ); [exact Hnd1 | eassumption | eassumption | eassumption | eassumption].
  - split; [ft_cs |].
    match goal with H : _ ⍮ _ ⍮ _ ⊢ a_tuple _ (record_eta_fields R M) : _, HR : record_lookup _ _ p = Some R |- _ =>
      destruct (wf_tuple_inversion H) as [p0 R0 Ns0 i0 _ _ Hr0 Hl0 _ _ Hn0 _ _];
      destruct (wf_record_inversion Hr0) as [R1 Hl1 Hnd1 _ _ _ _ _ _ _ _ _];
      rewrite Hl0 in Hl1; injection Hl1 as <- end.
    assert (Hnd : NoDup (List.map fst (record_fields R))).
    { match goal with Hn0 : List.map fst (record_eta_fields R M) = List.map fst (record_fields ?R0), Hnd1 : NoDup _ |- _ =>
        rewrite <- Hn0 in Hnd1; unfold record_eta_fields in Hnd1; rewrite List.map_map in Hnd1; exact Hnd1 end. }
    eapply (set_rule_record_eta T γ Hok); [ft_ctx | eassumption | eassumption | exact Hnd | eassumption | eassumption].
  - split; [ft_cs | eapply set_rule_exp_eq_subtyp; eassumption].
  - split; [ft_cs | apply set_rule_exp_eq_sym; do 3 eexists; eassumption].
  - split; [ft_cs | eapply set_rule_exp_eq_trans; do 3 eexists; eassumption].
  (* subtyping *)
  - ft_by set_rule_subtyp_refl.
  - split; [ft_cs | eapply set_rule_subtyp_trans; do 2 eexists; eassumption].
  - ft_by set_rule_subtyp_univ.
  - ft_by set_rule_subtyp_suniv.
  - ft_by set_rule_subtyp_level.
  - ft_by set_rule_subtyp_small_large.
  - assert (κc <> ak_propositional) by (match goal with H : evaluated_kind κc |- _ => destruct H end; discriminate).
    ft_by set_rule_subtyp_pi.
  (* universes *)
  - split; [ft_cs | apply set_rule_is_univ_large; ft_ctx].
  - ft_by set_rule_is_univ_small.
  (* extensions *)
  - apply set_ext_eq_suffixes_nil; assumption.
  - ft_ext_cons; [eapply set_rule_ext_eq_ass; ft_prem | apply set_rule_slots_extend_plain; [assumption | reflexivity]
                 | apply set_rule_slots_extend_plain; [assumption | reflexivity]].
  - ft_ext_cons; [eapply set_rule_ext_eq_def; ft_prem | apply set_rule_slots_extend_plain; [assumption | reflexivity]
                 | apply set_rule_slots_extend_plain; [assumption | reflexivity]].
  - ft_ext_cons; [eapply set_rule_ext_eq_mod; ft_prem
                 | split; [assumption | intros U0 [= <-]; eapply set_unit_eq_valid; eassumption]
                 | split; [assumption | intros U0 [= <-]; eapply set_unit_eq_valid; eassumption]].
  - ft_ext_cons; [eapply set_rule_ext_eq_dm; ft_prem
                 | split; [assumption | intros U0 [= <-]; eapply set_unit_eq_valid; eassumption]
                 | split; [assumption | intros U0 [= <-]; eapply set_unit_eq_valid; eassumption]].
  (* units *)
  - split; [ft_cs' |].
    match goal with
    | Hb : set_rel_ext_eq_suffixes T γ Γ (body_ctx Φx ++ Δ) (body_ctx Φx ++ Δ),
      Hb' : set_rel_ext_eq_suffixes T γ Γ (body_ctx Φx' ++ Δ') (body_ctx Φx' ++ Δ'),
      Hxb : _ ⍮ _ ⍮ Γ ⊢ˣ body_ctx Φx ++ Δ ≈ _, Hxb' : _ ⍮ _ ⍮ Γ ⊢ˣ body_ctx Φx' ++ Δ' ≈ _ |- _ =>
        pose proof (proj1 (set_ext_eq_suffixes_whole _ _ _ Hb eq_refl)) as HC;
        pose proof (proj1 (set_ext_eq_suffixes_whole _ _ _ Hb' eq_refl)) as HC';
        pose proof (set_ext_eq_suffixes_slots T γ _ _ _ Hb) as Hsl; pose proof (set_ext_eq_suffixes_slots T γ _ _ _ Hb') as Hsl';
        pose proof (ext_eq_ctx_left _ _ _ _ _ Hxb) as Hcx; pose proof (ext_eq_ctx_left _ _ _ _ _ Hxb') as Hcx'
    end.
    rewrite <- List.app_assoc in HC, HC', Hsl, Hsl', Hcx, Hcx'.
    eapply (set_rule_unit_eq_body T γ Hfn Hmods Hok) with (l := param_level) (entry_sort := entry_sort);
      [eapply wf_unit_eq_body; eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
      | match goal with H : set_rel_ext_eq_suffixes T γ Γ Δ Δ' |- _ => exact (set_ext_eq_suffixes_eq T γ _ _ _ H) end
      | eassumption | eassumption | eassumption | eassumption
      | intros; eapply sort_kind_abs_kind_sort_inv; eauto | intros; eapply sort_kind_abs_kind_sort_inv; eauto
      | ft_from_ih | ft_from_ih | ft_from_ih | ft_from_ih | ft_from_ih | ft_from_ih | ft_from_ih | ft_from_ih
      | eassumption | eassumption
      | apply (set_params_evaluated_of_sorts T γ Γ Δ param_level param_sorts); [assumption | ft_from_ih]
      | apply (set_params_evaluated_of_sorts T γ Γ Δ' param_level param_sorts); [assumption | ft_from_ih]
      | eassumption | eassumption | eassumption].
  - split; [ft_cs' |].
    eapply (set_rule_unit_eq_alias T γ Hfn Hmods Hok) with (l := param_level);
      [eapply wf_unit_eq_alias; eassumption | eassumption
      | match goal with H : set_rel_ext_eq_suffixes T γ Γ Δ Δ' |- _ => exact (set_ext_eq_suffixes_eq T γ _ _ _ H) end
      | eassumption | eassumption
      | apply (set_params_evaluated_of_sorts T γ Γ Δ param_level param_sorts); [assumption | ft_from_ih]
      | apply (set_params_evaluated_of_sorts T γ Γ Δ' param_level param_sorts); [assumption | ft_from_ih]
      | do 2 eexists; eassumption | do 2 eexists; eassumption].
  - split; [ft_cs' |].
    eapply (set_rule_unit_eq_flatten T γ Hfn0 Hmods Hok) with (l := param_level);
      [eassumption | apply (set_params_evaluated_of_sorts T γ Γ Δ param_level param_sorts); [assumption | ft_from_ih]
      | do 2 eexists; eassumption | eapply wf_unit_eq_flatten; eassumption].
  - split; [ft_cs | eapply (set_rule_unit_eq_expand T γ Hfn0 Hmods); [do 2 eexists; eassumption | eapply wf_unit_eq_expand; eassumption]].
  - split; [ft_cs | eapply set_rule_unit_eq_sym; do 2 eexists; eassumption].
  - split; [ft_cs | eapply set_rule_unit_eq_trans; do 2 eexists; eassumption].
  (* module expressions *)
  - ft_by set_rule_me_unit.
  - ft_by set_rule_me_var.
  - ft_by set_rule_me_lit.
  - match goal with |- _ /\ set_rel_modexp_eq _ _ ?G ?L ?Rt =>
      assert (Hc : gc_deps ⍮ gc_stack ⍮ G ⊢ᵐ L ≈ Rt) by (eapply wf_me_mem; eassumption) end.
    pose proof (wf_modexp_eq_refl_left Hc). pose proof (wf_modexp_eq_refl_right Hc).
    ft_by set_rule_me_mem.
  - split; [ft_cs | eapply (set_rule_me_app T γ Hfn0 Hmods Hgw Hok Γ H H' N N' R _ B _ Srt R' _ B' _ Srt'); ft_prem].
  - ft_by set_rule_me_delta_slot.
  - ft_by set_rule_me_delta_sel.
  - split; [ft_cs |].
    match goal with |- context [me_lit (gu_open (tele_sub ?Δ ?σ) (gmod_sub ?Φ _))] =>
      replace (gu_open (tele_sub Δ σ) _) with (gunit_sub (gu_open Δ Φ) σ) by (rewrite gunit_sub_mk; reflexivity) end.
    eapply set_rule_me_beta; [ft_prem | ft_prem | ft_prem | ft_prem | ft_prem | | ft_prem ..].
    rewrite gunit_sub_mk. eapply wf_me_beta_body; eassumption.
  - split; [ft_cs |].
    match goal with |- context [me_lit (gu_mk (tele_sub ?Δ ?σ) (md_alias (modexp_sub ?E _)))] =>
      replace (gu_mk (tele_sub Δ σ) _) with (gunit_sub (gu_mk Δ (md_alias E)) σ) by (rewrite gunit_sub_mk; reflexivity) end.
    eapply set_rule_me_beta; [ft_prem | ft_prem | ft_prem | ft_prem | ft_prem | | ft_prem ..].
    rewrite gunit_sub_mk. eapply wf_me_beta_alias; eassumption.
  - split; [ft_cs | eapply set_rule_me_beta_alias0; [ft_prem | ft_prem | ft_prem | ft_prem
                                                   | eapply wf_modexp_eq_refl_left; eapply wf_me_beta_alias0; eassumption | ft_prem]].
  - ft_by set_rule_me_sym.
  - ft_by set_rule_me_trans.
Qed.

End FundamentalTheorem.
