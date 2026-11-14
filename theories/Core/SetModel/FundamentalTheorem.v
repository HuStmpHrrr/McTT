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

(** A universe stays one where its context grows. *)
Lemma wf_is_univ_embedding : forall Θ1 Ξ1 Θ2 Ξ2, gctx_embedding Θ1 Ξ1 Θ2 Ξ2 ->
    forall Γ U, Θ1 ⍮ Ξ1 ⍮ Γ ⊢ᵤ U -> Θ2 ⍮ Ξ2 ⍮ Γ ⊢ᵤ U.
Proof.
  intros * He * HU. pose proof (gctx_embedding_preserves_wf _ _ _ _ He) as (Hc & Hx & _).
  destruct HU; [apply wf_is_univ_large; exact (Hc _ H) | eapply wf_is_univ_small; exact (Hx _ _ _ H)].
Qed.

(** The theorem is proved at a context its derivations' context grows
    into: the section's, with the valuation modelling there what the
    derivations' context resolves.  Its judgments are those of
    [Judgments.v] at that one context; [set_fundamental] below reads them
    at every such context. *)
Section FundamentalTheorem.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** An assumption of a type equal to another reads the other's. *)
Lemma wf_sub_id_conv_ass {Θ : gdeps} {Ξ : gstack} : forall Γ κ A A' Srt, Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt -> sort_kind Srt κ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Srt -> Θ ⍮ Ξ ⍮ ce_ass κ A' :: Γ ⊢ˢ sb_id : ce_ass κ A :: Γ.
Proof.
  intros * HA Hk HAA'. pose proof (presup_exp_eq_right HAA') as HA'.
  eapply wf_sub_id_extend; [apply wf_sub_id; exact (presup_exp_ctx HA) | exact HA | exact Hk | exact HA' | exact Hk |].
  eapply wf_subtyp_refl; [exact HA | destruct Hk; constructor |]. mauto 3.
Qed.

(** The same for types of the kind [κ] next to a universe. *)
Lemma wf_sub_id_conv_univ {Θ : gdeps} {Ξ : gstack} : forall Γ U κ A A', Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : abs_kind_sort κ U -> Θ ⍮ Ξ ⍮ ce_ass κ A' :: Γ ⊢ˢ sb_id : ce_ass κ A :: Γ.
Proof.
  intros * HU HAA'. destruct κ; cbn [abs_kind_sort] in HAA'.
  - destruct (wf_exp_eq_is_univ_large HU HAA') as [i Hi].
    exact (wf_sub_id_conv_ass _ _ _ _ _ (presup_exp_eq_left Hi) (sort_kind_universe i) Hi).
  - exact (wf_sub_id_conv_ass _ _ _ _ _ (presup_exp_eq_left HAA') sort_kind_prop HAA').
  - exact (wf_sub_id_conv_ass _ _ _ _ _ (presup_exp_eq_left HAA') sort_kind_level HAA').
Qed.

(** A context extended by a type of the kind [κ] next to a universe,
    equal to another, by the other. *)
Lemma wf_ctx_conv_univ {Θ : gdeps} {Ξ : gstack} : forall Γ U κ A A', Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : abs_kind_sort κ U -> ⊢ Θ ⍮ Ξ ⍮ ce_ass κ A' :: Γ.
Proof. intros * HU HAA'. exact (wf_ctx_extend_univ_kind _ _ _ _ _ _ HU (presup_exp_eq_right HAA')). Qed.

(** A definition of equal type and body reads the other's. *)
Lemma wf_conv_def {Θ : gdeps} {Ξ : gstack} : forall Γ A A' M M' Srt, Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt -> type_sort Srt ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Srt -> Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    ⊢ Θ ⍮ Ξ ⍮ ce_def A' M' :: Γ /\ Θ ⍮ Ξ ⍮ ce_def A' M' :: Γ ⊢ˢ sb_id : ce_def A M :: Γ.
Proof.
  intros * HA HS HAA' HMM'. pose proof (presup_exp_eq_right HAA') as HA'.
  pose proof (presup_exp_eq_left HMM') as HM. pose proof (presup_exp_eq_right HMM') as HM'.
  assert (Hsub : Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A') by (eapply wf_subtyp_refl; eassumption).
  assert (Hsub' : Θ ⍮ Ξ ⍮ Γ ⊢ A' ⊆ A) by (eapply wf_subtyp_refl; [exact HA | exact HS | mauto 3]).
  assert (HM'A' : Θ ⍮ Ξ ⍮ Γ ⊢ M' : A') by (eapply wf_exp_subtyp; [exact HM' | exact HA' | exact HS | exact Hsub]).
  split; [eapply wf_ctx_extend_def; eassumption |].
  eapply wf_sub_id_extend_def; [apply wf_sub_id; exact (presup_exp_ctx HA) | exact HA | exact HS | exact HA' | exact HS
                               | exact Hsub' | exact HM | exact HM'A' | mauto 3].
Qed.

(** Module slots of equal units are equal one-entry extensions. *)
Lemma wf_ext_eq_one_mod {Θ : gdeps} {Ξ : gstack} : forall Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ ce_mod U :: nil ≈ ce_mod U' :: nil.
Proof.
  intros * HU. eapply wf_ext_eq_mod; [constructor; exact (presup_unit_eq_ctx HU) | exact HU | exact (wf_unit_eq_refl_right HU)].
Qed.

(** So are definitions with module parts of equal types, bodies and units. *)
Lemma wf_ext_eq_one_dm {Θ : gdeps} {Ξ : gstack} : forall Γ A A' M M' E E' i, Θ ⍮ Ξ ⍮ Γ ⊢ A : a_typ i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : a_typ i -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E') ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ ce_dm A M (gu_mk nil (md_alias E)) :: nil ≈ ce_dm A' M' (gu_mk nil (md_alias E')) :: nil.
Proof.
  intros * HA HAA' HM HMM' HU. pose proof (presup_exp_eq_right HAA') as HA'.
  assert (HM'A' : Θ ⍮ Ξ ⍮ Γ ⊢ M' : A')
    by (eapply wf_exp_subtyp; [exact (presup_exp_eq_right HMM') | exact HA' | constructor
                              | eapply wf_subtyp_refl; [exact HA' | constructor | exact HAA']]).
  eapply wf_ext_eq_dm; [constructor; exact (presup_exp_ctx HA) | exact HA | exact HAA' | exact HM | exact HMM' | exact HA' | exact HM'A'
                       | exact HU | exact (wf_unit_eq_refl_right HU)].
Qed.

(** A context extended by an assumption of a type equal to another is
    well formed. *)
Lemma wf_ctx_conv_ass {Θ : gdeps} {Ξ : gstack} : forall Γ κ A A' Srt, sort_kind Srt κ -> Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Srt ->
    ⊢ Θ ⍮ Ξ ⍮ ce_ass κ A' :: Γ.
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
Lemma set_ext_eq_suffixes_nil {GC : GCtx} : forall Γ, set_ctx T γ Γ -> set_valid_slots T γ Γ -> set_rel_ext_eq_suffixes T γ Γ nil nil.
Proof.
  intros Γ HΓ Hsl. constructor; [| exact Hsl | exact Hsl].
  intros [| ? ?] Ψ [| ? ?] Ψ' E E' _; try discriminate. cbn in E, E'. subst. exact (set_rule_ext_eq_nil T γ _ HΓ).
Qed.

(** Extensions by one more entry each: their suffixes are the whole ones
    or suffixes of the extensions before. *)
Lemma set_ext_eq_suffixes_cons {GC : GCtx} : forall Γ Ψ Ψ' e e', set_rel_ext_eq_suffixes T γ Γ Ψ Ψ' -> List.length Ψ = List.length Ψ' ->
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
Lemma set_ext_eq_suffixes_ctx_slots {GC : GCtx} : forall Γ Δ Δ', set_rel_ext_eq_suffixes T γ Γ Δ Δ' -> set_rel_ctx_slots T γ Γ.
Proof.
  intros * [Hsuf Hsl _]. split; [| exact (set_valid_slots_app_r T γ _ _ Hsl)].
  exact (set_ext_eq_left _ _ _ _ _ (Hsuf Δ nil Δ' nil (eq_sym (List.app_nil_r Δ)) (eq_sym (List.app_nil_r Δ')) eq_refl)).
Qed.

(** A judgment at this context, as the reading here ([Hμ]) of the same
    judgment at every context the derivation's context grows into. *)
Ltac ft_kripke :=
  match goal with Hμ : set_gctx_embedding ?Θs ?Ξs _ _ T γ |- _ =>
    lazymatch goal with
    | |- set_rel_ctx_slots T γ ?Γ => apply (fun K : set_ctx_slots Θs Ξs T γ Γ => K _ _ Hμ)
    | |- set_rel_exp_eq T γ ?Γ ?A ?M ?M' => apply (fun K : set_exp_eq Θs Ξs T γ Γ A M M' => K _ _ Hμ)
    | |- set_rel_subtyp T γ ?Γ ?A ?A' => apply (fun K : set_subtyp Θs Ξs T γ Γ A A' => K _ _ Hμ)
    | |- set_rel_universe T γ ?Γ ?U => apply (fun K : set_universe Θs Ξs T γ Γ U => K _ _ Hμ)
    | |- set_rel_ext_eq_suffixes T γ ?Γ ?Δ ?Δ' => apply (fun K : set_ext_eq_suffixes Θs Ξs T γ Γ Δ Δ' => K _ _ Hμ)
    | |- set_rel_unit_eq T γ ?Γ ?U ?U' => apply (fun K : set_unit_eq Θs Ξs T γ Γ U U' => K _ _ Hμ)
    | |- set_rel_modexp_eq T γ ?Γ ?H ?H' => apply (fun K : set_modexp_eq Θs Ξs T γ Γ H H' => K _ _ Hμ)
    end
  end.

(** A case by its set rule over the judgments at every context, from the
    induction hypotheses as they are. *)
Ltac ft_by_kripke lemma := split; [ft_cs | ft_kripke; eapply lemma; ft_prem].

(** A premise under binders: an induction hypothesis read here, or a
    syntactic premise of the derivation's context moved here along the
    moves [ft_move] names. *)
Ltac ft_from_ih :=
  intros; first [ match goal with IH : forall _, _ |- _ =>
                    solve [eapply proj2; eapply IH; eauto | eapply IH; eauto] end
                | ft_kripke; match goal with IH : forall _, _ |- _ =>
                    solve [eapply proj2; eapply IH; eauto | eapply IH; eauto] end
                | match goal with Hμ : set_gctx_embedding _ _ ?Θt ?Ξt T γ |- _ =>
                  match goal with
                  | Mv : forall _ _ _, wf_exp _ _ _ _ _ -> wf_exp Θt Ξt _ _ _ |- wf_exp _ _ _ _ _ =>
                      apply Mv; solve [eauto]
                  | Mv : forall _ _ _ _, wf_exp_eq _ _ _ _ _ _ -> wf_exp_eq Θt Ξt _ _ _ _ |- wf_exp_eq _ _ _ _ _ _ =>
                      apply Mv; solve [eauto]
                  | Mv : forall _ _ _, wf_subtyp _ _ _ _ _ -> wf_subtyp Θt Ξt _ _ _ |- wf_subtyp _ _ _ _ _ =>
                      apply Mv; solve [eauto]
                  | Mv : forall _ _ _, wf_ext_eq _ _ _ _ _ -> wf_ext_eq Θt Ξt _ _ _ |- wf_ext_eq _ _ _ _ _ =>
                      apply Mv; solve [eauto]
                  | Mv : forall _, wf_ctx _ _ _ -> wf_ctx Θt Ξt _ |- wf_ctx _ _ _ =>
                      apply Mv; solve [eauto]
                  end end ].

(** The whole extensions of equal extensions denote, with valid slots. *)
Lemma set_ext_eq_suffixes_whole {GC : GCtx} : forall Γ Δ Δ', set_rel_ext_eq_suffixes T γ Γ Δ Δ' -> List.length Δ = List.length Δ' ->
    set_ctx T γ (Δ ++ Γ) /\ set_ctx T γ (Δ' ++ Γ).
Proof. intros * [Hsuf _ _] Hlen. destruct (Hsuf nil Δ nil Δ' eq_refl eq_refl Hlen) as [HL HR _]. split; assumption. Qed.

Ltac ft_cs' :=
  first [ ft_cs | match goal with H : set_rel_ext_eq_suffixes T γ ?Γ _ _ |- set_rel_ctx_slots T γ ?Γ => exact (set_ext_eq_suffixes_ctx_slots _ _ _ H) end ].

Ltac ft_ext_cons :=
  match goal with Hx : _ ⍮ _ ⍮ ?Γ ⊢ˣ ?Ψ ≈ ?Ψ' |- set_rel_ext_eq_suffixes T γ ?Γ (_ :: ?Ψ) (_ :: ?Ψ') =>
    apply set_ext_eq_suffixes_cons; [assumption | exact (ext_eq_length _ _ _ _ _ Hx) | | |] end.

(** A case's syntactic hypotheses, read at the derivation's context
    [Θs ⍮ Ξs], copied to this one beside their own: its judgments and
    expansions along the embedding ([Mv_*], kept for the premises under
    binders), its declarations' lookups (they do not grow, and the rules
    read the model of each at [Θs ⍮ Ξs]). *)
Ltac ft_move :=
  match goal with Hμ : set_gctx_embedding ?Θs ?Ξs ?Θt ?Ξt T γ |- _ =>
    let He := fresh "He" in pose proof (set_gctx_embedding_embedding _ _ _ _ _ _ Hμ) as He;
    let Hsub := fresh "Hsub" in pose proof (gctx_embedding_resolution _ _ _ _ He) as Hsub;
    destruct (gctx_embedding_preserves_wf _ _ _ _ He) as (Mv_ctx & Mv_exp & Mv_eq & Mv_sub & Mv_ext & Mv_unit & Mv_me & Mv_nl);
    pose proof (wf_is_univ_embedding _ _ _ _ He) as Mv_univ;
    pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_grow_all _ _ _ _ (set_gctx_embedding_source_wf _ _ _ _ _ _ Hμ)
                  (gctx_embedding_wf _ _ _ _ He) Hsub))))) as Mv_body;
    repeat match goal with
      | H : body_xp Θs Ξs ?a ?b ?c |- _ =>
          lazymatch goal with _ : body_xp Θt Ξt a b c |- _ => fail | _ => pose proof (Mv_body _ _ _ H) end
      end;
    (* the source judgments stay: a rule's source premises are read off them *)
    repeat match goal with
      | H : wf_ctx Θs Ξs ?a |- _ =>
          lazymatch goal with _ : wf_ctx Θt Ξt a |- _ => fail | _ => pose proof (Mv_ctx _ H) end
      | H : wf_exp Θs Ξs ?a ?b ?c |- _ =>
          lazymatch goal with _ : wf_exp Θt Ξt a b c |- _ => fail | _ => pose proof (Mv_exp _ _ _ H) end
      | H : wf_exp_eq Θs Ξs ?a ?b ?c ?d |- _ =>
          lazymatch goal with _ : wf_exp_eq Θt Ξt a b c d |- _ => fail | _ => pose proof (Mv_eq _ _ _ _ H) end
      | H : wf_subtyp Θs Ξs ?a ?b ?c |- _ =>
          lazymatch goal with _ : wf_subtyp Θt Ξt a b c |- _ => fail | _ => pose proof (Mv_sub _ _ _ H) end
      | H : wf_ext_eq Θs Ξs ?a ?b ?c |- _ =>
          lazymatch goal with _ : wf_ext_eq Θt Ξt a b c |- _ => fail | _ => pose proof (Mv_ext _ _ _ H) end
      | H : wf_unit_eq Θs Ξs ?a ?b ?c |- _ =>
          lazymatch goal with _ : wf_unit_eq Θt Ξt a b c |- _ => fail | _ => pose proof (Mv_unit _ _ _ H) end
      | H : wf_modexp_eq Θs Ξs ?a ?b ?c |- _ =>
          lazymatch goal with _ : wf_modexp_eq Θt Ξt a b c |- _ => fail | _ => pose proof (Mv_me _ _ _ H) end
      | H : wf_no_level_members Θs Ξs ?a ?b |- _ =>
          lazymatch goal with _ : wf_no_level_members Θt Ξt a b |- _ => fail | _ => pose proof (Mv_nl _ _ H) end
      | H : wf_is_univ Θs Ξs ?a ?b |- _ =>
          lazymatch goal with _ : wf_is_univ Θt Ξt a b |- _ => fail | _ => pose proof (Mv_univ _ _ H) end
      end;
    repeat match goal with
      | H : ind_lookup Θs Ξs ?q = ?r |- _ =>
          lazymatch goal with _ : ind_lookup Θt Ξt q = r |- _ => fail | _ =>
            pose proof (ind_lookup_gc_sub _ _ _ _ _ _ Hsub H) end
      | H : record_lookup Θs Ξs ?q = ?r |- _ =>
          lazymatch goal with _ : record_lookup Θt Ξt q = r |- _ => fail | _ =>
            pose proof (record_lookup_gc_sub _ _ _ _ _ _ Hsub H) end
      end
  end.

(** Two judgments at every context a context grows into are both
    judgments at each. *)
Lemma set_kripke_conj : forall Θ Ξ (P Q : gdeps -> gstack -> Prop),
    (forall Θ2 Ξ2, set_gctx_embedding Θ Ξ Θ2 Ξ2 T γ -> P Θ2 Ξ2 /\ Q Θ2 Ξ2) ->
    (forall Θ2 Ξ2, set_gctx_embedding Θ Ξ Θ2 Ξ2 T γ -> P Θ2 Ξ2) /\
    (forall Θ2 Ξ2, set_gctx_embedding Θ Ξ Θ2 Ξ2 T γ -> Q Θ2 Ξ2).
Proof. intros * H. split; intros * Hμ; apply (H _ _ Hμ). Qed.

(** A case read at one context [GC] its derivation's context grows into
    ([Hμ]): its conclusion there, and its induction hypotheses read there
    beside their own (which a rule over the judgments at every such
    context takes as they are). *)
Ltac ft_open :=
  unfold set_ctx_slots, set_exp_eq, set_subtyp, set_universe, set_ext_eq_suffixes, set_unit_eq, set_modexp_eq;
  first [apply set_kripke_conj | idtac]; intros Θ2 Ξ2 Hμ; cbv beta;
  match type of Hμ with set_gctx_embedding ?Θs ?Ξs _ _ _ _ =>
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with
      | H : set_ctx_slots Θs Ξs T γ ?a |- _ =>
          lazymatch goal with _ : set_rel_ctx_slots T γ a |- _ => fail | _ => pose proof (H _ _ Hμ) end
      | H : set_exp_eq Θs Ξs T γ ?a ?b ?c ?d |- _ =>
          lazymatch goal with _ : set_rel_exp_eq T γ a b c d |- _ => fail | _ => pose proof (H _ _ Hμ) end
      | H : set_subtyp Θs Ξs T γ ?a ?b ?c |- _ =>
          lazymatch goal with _ : set_rel_subtyp T γ a b c |- _ => fail | _ => pose proof (H _ _ Hμ) end
      | H : set_universe Θs Ξs T γ ?a ?b |- _ =>
          lazymatch goal with _ : set_rel_universe T γ a b |- _ => fail | _ => pose proof (H _ _ Hμ) end
      | H : set_ext_eq_suffixes Θs Ξs T γ ?a ?b ?c |- _ =>
          lazymatch goal with _ : set_rel_ext_eq_suffixes T γ a b c |- _ => fail | _ => pose proof (H _ _ Hμ) end
      | H : set_unit_eq Θs Ξs T γ ?a ?b ?c |- _ =>
          lazymatch goal with _ : set_rel_unit_eq T γ a b c |- _ => fail | _ => pose proof (H _ _ Hμ) end
      | H : set_modexp_eq Θs Ξs T γ ?a ?b ?c |- _ =>
          lazymatch goal with _ : set_rel_modexp_eq T γ a b c |- _ => fail | _ => pose proof (H _ _ Hμ) end
      end;
    change (set_gctx_embedding Θs Ξs (@gc_deps (gc_mk Θ2 Ξ2)) (@gc_stack (gc_mk Θ2 Ξ2)) T γ) in Hμ
  end;
  set (GC := gc_mk Θ2 Ξ2) in *.

(** The fundamental theorem: every judgment of a global context holds in
    the set model, at every context it is modelled at
    ([set_gctx_embedding]), each read as in [Judgments.v]. *)
Theorem set_fundamental :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> set_ctx_slots Θ Ξ T γ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> set_ctx_slots Θ Ξ T γ Γ /\ set_exp_eq Θ Ξ T γ Γ A M M) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> set_ctx_slots Θ Ξ T γ Γ /\ set_exp_eq Θ Ξ T γ Γ A M M') /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> set_ctx_slots Θ Ξ T γ Γ /\ set_subtyp Θ Ξ T γ Γ A A') /\
  (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> set_ctx_slots Θ Ξ T γ Γ /\ set_universe Θ Ξ T γ Γ U) /\
  (forall Θ Ξ Γ Δ Δ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' -> set_ext_eq_suffixes Θ Ξ T γ Γ Δ Δ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> set_ctx_slots Θ Ξ T γ Γ /\ set_unit_eq Θ Ξ T γ Γ U U') /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> set_ctx_slots Θ Ξ T γ Γ /\ set_modexp_eq Θ Ξ T γ Γ H H').
Proof.
  apply syntactic_wf_mut_ind; intros; ft_open;
    (* what the valuation gives here *)
    pose proof (gctx_embedding_wf _ _ _ _ (set_gctx_embedding_embedding _ _ _ _ _ _ Hμ)) as Hgw;
    pose proof (set_gctx_embedding_fn_kinds _ _ _ _ _ _ Hμ) as Hfn; rewrite <- gc_mk_eta in Hfn;
    pose proof (fn_kinds_unique_of_ext Hfn) as Hfn0;
    pose proof (set_gctx_embedding_modules _ _ _ _ _ _ Hμ) as Hmods;
    ft_move; ft_ihs.
  (* contexts *)
  - ft_kripke; apply set_rule_ctx_empty.
  - ft_kripke; eapply set_rule_ctx_extend; eassumption.
  - ft_kripke; eapply set_rule_ctx_extend_def; eassumption.
  - ft_kripke; eapply set_rule_ctx_extend_mod; eassumption.
  - ft_kripke; eapply set_rule_ctx_extend_dm; eassumption.
  (* terms *)
  - split; [ft_cs | ft_kripke; apply set_rule_typ].
  - ft_by_kripke set_rule_univ.
  - ft_by_kripke set_rule_level.
  - ft_by_kripke set_rule_llit.
  - ft_by_kripke set_rule_succl.
  - ft_by_kripke set_rule_maxl.
  - ft_by_kripke set_rule_prop.
  - ft_by_kripke set_rule_True.
  - ft_by_kripke set_rule_tt.
  - ft_by_kripke set_rule_False.
  - ft_by_kripke set_rule_absurd.
  - ft_by_kripke set_rule_and.
  - ft_by_kripke set_rule_conj.
  - ft_by_kripke set_rule_left.
  - split; [ft_cs | ft_kripke; eapply (set_rule_right _ _ T γ Γ P Q M); ft_prem].
  - ft_by_kripke set_rule_proof_tag.
  - ft_by_kripke set_rule_ind.
  - ft_by_kripke set_rule_con.
  - split; [ft_cs |].
    eapply (set_rule_elim T γ Hfn0 Hmods Hgw _ _ Hμ); try eassumption; try reflexivity; try (do 3 eexists; eassumption);
      try ft_from_ih;
      intros; match goal with |- set_ctx _ _ _ =>
        solve [eapply proj1; eapply set_ext_eq_suffixes_whole; [ft_from_ih | reflexivity]] end.
  - ft_by_kripke set_rule_pi.
  - assert (Θ ⍮ Ξ ⍮ Γ ⊢ a_fn A M : a_pi κd κc A B) by (eapply wf_fn; eassumption).
    ft_by_kripke (set_rule_fn Θ Ξ T γ Γ κd κc i Srt A M B).
  - ft_by_kripke (set_rule_app Θ Ξ T γ Γ κd κc i Srt A B M N).
  - split; [ft_cs | eapply set_rel_exp_eq_refl_left; ft_kripke; eapply set_rule_let_def_zeta; ft_prem].
  - split; [ft_cs | eapply set_rel_exp_eq_refl_left; ft_kripke; eapply set_rule_let_mod_zeta; ft_prem].
  - split; [ft_cs | eapply set_rel_exp_eq_refl_left; ft_kripke; eapply set_rule_let_dm_zeta; ft_prem].
  - match goal with |- _ /\ set_rel_exp_eq _ _ ?G ?A ?L _ => assert (HTm : Θ ⍮ Ξ ⍮ G ⊢ L : A) by (eapply wf_mem; eassumption) end.
    ft_by_kripke set_rule_mem.
  - ft_by_kripke set_rule_var.
  - ft_by_kripke set_rule_record.
  - split; [ft_cs |]. ft_kripke. eapply set_rule_tuple; first [eassumption | ft_syn | ft_from_ih].
  - split; [ft_cs |]. ft_kripke. eapply set_rule_proj; first [eassumption | ft_syn | ft_from_ih].
  - ft_by_kripke set_rule_exp_eq_subtyp.
  (* term equality *)
  - split; [ft_cs | ft_kripke; apply set_rule_typ].
  - ft_by_kripke set_rule_univ.
  - ft_by_kripke set_rule_level.
  - ft_by_kripke set_rule_llit.
  - ft_by_kripke set_rule_succl.
  - ft_by_kripke set_rule_maxl.
  - ft_by_kripke set_rule_llit_succl.
  - ft_by_kripke set_rule_maxl_absorb.
  - ft_by_kripke set_rule_maxl_zero.
  - ft_by_kripke set_rule_maxl_assoc.
  - ft_by_kripke set_rule_maxl_comm.
  - ft_by_kripke set_rule_maxl_idem.
  - ft_by_kripke set_rule_succl_maxl.
  - ft_by_kripke set_rule_maxl_succl.
  - ft_by_kripke set_rule_prop.
  - ft_by_kripke set_rule_True.
  - ft_by_kripke set_rule_False.
  - ft_by_kripke set_rule_absurd_cong.
  - ft_by_kripke set_rule_and_cong.
  - ft_by_kripke set_rule_ind.
  - ft_by_kripke set_rule_con.
  - split; [ft_cs |].
    eapply (set_rule_elim_cong T γ Hfn0 Hmods Hgw _ _ Hμ); try eassumption; try reflexivity; try (do 3 eexists; eassumption);
      try ft_from_ih;
      intros; match goal with |- set_ctx _ _ _ =>
        solve [eapply proj1; eapply set_ext_eq_suffixes_whole; [ft_from_ih | reflexivity]] end.
  - ft_by_kripke set_rule_pi_cong.
  - assert (Hc : Θ ⍮ Ξ ⍮ Γ ⊢ a_fn A M ≈ a_fn A' M' : a_pi κd κc A B) by (eapply wf_exp_eq_fn_cong; eassumption).
    pose proof (presup_exp_eq_left Hc). pose proof (presup_exp_eq_right Hc).
    ft_by_kripke set_rule_fn_cong.
  - match goal with H : Θ ⍮ Ξ ⍮ _ ⊢ N ≈ N' : _ |- _ => pose proof (presup_exp_eq_left H) end.
    ft_by_kripke (set_rule_app_cong Θ Ξ T γ Γ κd κc i Srt A B M M' N N').
  - split; [ft_cs |].
    destruct (@wf_conv_def Θ Ξ Γ A A' M M' Srt ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    ft_kripke; eapply set_rule_let_def_cong; ft_prem.
  - split; [ft_cs |]. pose proof (@wf_ext_eq_one_mod Θ Ξ Γ U U' ltac:(eassumption)).
    ft_kripke; eapply set_rule_let_mod_cong; ft_prem.
  - split; [ft_cs |]. pose proof (@wf_ext_eq_one_dm Θ Ξ Γ A A' M M' E E' i ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
                                     ltac:(eassumption) ltac:(eassumption)).
    ft_kripke; eapply set_rule_let_dm_cong; ft_prem.
  - match goal with |- _ /\ set_rel_exp_eq _ _ ?G ?A ?L ?Rt =>
      assert (Hc : Θ ⍮ Ξ ⍮ G ⊢ L ≈ Rt : A) by (eapply wf_exp_eq_mem_cong; eassumption) end.
    pose proof (presup_exp_eq_left Hc). pose proof (presup_exp_eq_right Hc). ft_by_kripke set_rule_mem_cong.
  - ft_by_kripke set_rule_var.
  - assert (Θ ⍮ Ξ ⍮ Γ ⊢ a_fn A M : a_pi κd κc A B) by (eapply wf_fn; eassumption).
    ft_by_kripke (set_rule_pi_beta Θ Ξ T γ Γ κd κc i Srt A M B N).
  - split; [ft_cs |].
    eapply (set_rule_elim_iota T γ Hfn0 Hmods Hgw _ _ Hμ); try eassumption; try reflexivity; try (do 3 eexists; eassumption);
      try ft_from_ih;
      intros; match goal with |- set_ctx _ _ _ =>
        solve [eapply proj1; eapply set_ext_eq_suffixes_whole; [ft_from_ih | reflexivity]] end.
  - split; [ft_cs |].
    match goal with |- set_rel_exp_eq _ _ ?G ?A ?L ?R => assert (Hc : gc_deps ⍮ gc_stack ⍮ G ⊢ L ≈ R : A) end;
      [ apply Mv_eq; eapply wf_exp_eq_elim_view; first [eassumption | reflexivity] |].
    pose proof (presup_exp_eq_right Hc).
    eapply (set_rule_elim_view T γ Hfn0 Hmods Hgw _ _ Hμ); try eassumption; try reflexivity; try (do 3 eexists; eassumption);
      try ft_from_ih;
      intros; match goal with |- set_ctx _ _ _ =>
        solve [eapply proj1; eapply set_ext_eq_suffixes_whole; [ft_from_ih | reflexivity]] end.
  - split; [ft_cs |].
    eapply (set_rule_con_view T γ Hfn0 Hmods _ _ Hμ); try eassumption; try (do 3 eexists; eassumption); try ft_from_ih.
  - split; [ft_cs |].
    eapply (set_rule_con_rview T γ Hfn0 Hmods Hgw _ _ Hμ); try eassumption; try (do 3 eexists; eassumption); try ft_from_ih.
  - ft_by_kripke set_rule_let_def_zeta.
  - ft_by_kripke set_rule_let_mod_zeta.
  - ft_by_kripke set_rule_let_dm_zeta.
  - match goal with |- _ /\ set_rel_exp_eq _ _ ?G ?A ?L ?Rt =>
      assert (Hc : Θ ⍮ Ξ ⍮ G ⊢ L ≈ Rt : A) by (eapply wf_exp_eq_mem_delta; eassumption) end.
    pose proof (presup_exp_eq_left Hc). ft_by_kripke set_rule_mem_delta.
  - match goal with H : _ ∋ #_ ≔ _ : _ |- _ => pose proof (ctx_lookup_def_lookup _ _ _ _ H) end.
    ft_by_kripke set_rule_var_delta.
  - assert (Hc : Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ a_fn A (a_app (exp_wk M wk_shift) (a_var 0)) : a_pi κd κc A B)
      by (eapply wf_exp_eq_fn_eta; eassumption).
    pose proof (presup_exp_eq_right Hc). ft_by_kripke (set_rule_fn_eta Θ Ξ T γ Γ κd κc i Srt A B M).
  - ft_by_kripke set_rule_irrelevant.
  - ft_by_kripke set_rule_record_cong.
  - split; [ft_cs |]. ft_kripke. eapply set_rule_tuple_cong; [eassumption | eassumption | eassumption | eassumption |].
    intros. eexists. ft_from_ih.
  - split; [ft_cs |].
    match goal with H : Θ ⍮ Ξ ⍮ _ ⊢ M ≈ M' : _ |- _ => pose proof (presup_exp_eq_left H) as HMl end.
    ft_kripke. eapply set_rule_proj_cong; [eassumption | | eassumption].
    eapply (set_rule_proj Θ Ξ T γ Γ M p R Ns k f U);
      [ft_syn | eassumption | eassumption | eassumption | eassumption | ft_from_ih | ft_from_ih | exact HMl
      | eapply set_exp_eq_left_refl; eassumption | eassumption].
  - split; [ft_cs |].
    match goal with H : _ ⍮ _ ⍮ _ ⊢ a_tuple T0 fs : T0 |- _ =>
      destruct (wf_tuple_inversion H) as [p0 R0 Ns0 i0 _ _ Hr0 Hl0 _ _ Hn0 _ _];
      destruct (wf_record_inversion Hr0) as [R1 Hl1 Hnd1 _ _ _ _ _ _ _ _ _] end.
    rewrite Hl0 in Hl1. injection Hl1 as <-. rewrite <- Hn0 in Hnd1.
    ft_kripke. eapply set_rule_field_beta; [exact Hnd1 | eassumption | eassumption | eassumption | eassumption].
  - split; [ft_cs |].
    match goal with H : _ ⍮ _ ⍮ _ ⊢ a_tuple _ (record_eta_fields R M) : _, HR : record_lookup _ _ p = Some R |- _ =>
      destruct (wf_tuple_inversion H) as [p0 R0 Ns0 i0 _ _ Hr0 Hl0 _ _ Hn0 _ _];
      destruct (wf_record_inversion Hr0) as [R1 Hl1 Hnd1 _ _ _ _ _ _ _ _ _];
      rewrite Hl0 in Hl1; injection Hl1 as <- end.
    assert (Hnd : NoDup (List.map fst (record_fields R))).
    { match goal with Hn0 : List.map fst (record_eta_fields R M) = List.map fst (record_fields ?R0), Hnd1 : NoDup _ |- _ =>
        rewrite <- Hn0 in Hnd1; unfold record_eta_fields in Hnd1; rewrite List.map_map in Hnd1; exact Hnd1 end. }
    ft_kripke. eapply set_rule_record_eta; [eassumption | eassumption | eassumption | exact Hnd | eassumption | eassumption].
  - ft_by_kripke set_rule_exp_eq_subtyp.
  - ft_by_kripke set_rule_exp_eq_sym.
  - ft_by_kripke set_rule_exp_eq_trans.
  (* subtyping *)
  - ft_by_kripke set_rule_subtyp_refl.
  - ft_by_kripke set_rule_subtyp_trans.
  - ft_by_kripke set_rule_subtyp_univ.
  - ft_by_kripke set_rule_subtyp_suniv.
  - ft_by_kripke set_rule_subtyp_level.
  - ft_by_kripke set_rule_subtyp_small_large.
  - assert (κc <> ak_propositional) by (match goal with H : evaluated_kind κc |- _ => destruct H end; discriminate).
    ft_by_kripke set_rule_subtyp_pi.
  (* universes *)
  - ft_by_kripke set_rule_is_univ_large.
  - ft_by_kripke set_rule_is_univ_small.
  (* extensions *)
  - apply set_ext_eq_suffixes_nil; assumption.
  - ft_ext_cons; [eapply set_rule_ext_eq_ass; ft_prem | apply set_valid_slots_extend_plain; [assumption | reflexivity]
                 | apply set_valid_slots_extend_plain; [assumption | reflexivity]].
  - ft_ext_cons; [eapply set_rule_ext_eq_def; ft_prem | apply set_valid_slots_extend_plain; [assumption | reflexivity]
                 | apply set_valid_slots_extend_plain; [assumption | reflexivity]].
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
    eapply (set_rule_unit_eq_body T γ Hfn Hmods _ _ Hμ) with (l := param_level) (entry_sort := entry_sort);
      [apply Mv_unit; eapply wf_unit_eq_body; eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
      | match goal with H : set_rel_ext_eq_suffixes T γ Γ Δ Δ' |- _ => exact (set_ext_eq_suffixes_eq T γ _ _ _ H) end
      | eassumption | eassumption | eassumption | eassumption
      | intros; eapply sort_kind_abs_kind_sort_inv; eauto | intros; eapply sort_kind_abs_kind_sort_inv; eauto
      | ft_from_ih | ft_from_ih | ft_from_ih | ft_from_ih | ft_from_ih | ft_from_ih | ft_from_ih | ft_from_ih
      | eassumption | eassumption
      | apply (set_params_evaluated_of_sorts T γ Γ Δ param_level param_sorts); [assumption | ft_from_ih]
      | apply (set_params_evaluated_of_sorts T γ Γ Δ' param_level param_sorts); [assumption | ft_from_ih]
      | eassumption | eassumption | eassumption].
  - split; [ft_cs' |].
    eapply (set_rule_unit_eq_alias T γ Hfn Hmods _ _ Hμ) with (l := param_level);
      [apply Mv_unit; eapply wf_unit_eq_alias; eassumption | eassumption
      | match goal with H : set_rel_ext_eq_suffixes T γ Γ Δ Δ' |- _ => exact (set_ext_eq_suffixes_eq T γ _ _ _ H) end
      | eassumption | eassumption
      | apply (set_params_evaluated_of_sorts T γ Γ Δ param_level param_sorts); [assumption | ft_from_ih]
      | apply (set_params_evaluated_of_sorts T γ Γ Δ' param_level param_sorts); [assumption | ft_from_ih]
      | do 2 eexists; eassumption | do 2 eexists; eassumption].
  - split; [ft_cs' |].
    eapply (set_rule_unit_eq_flatten T γ Hfn0 Hmods Hgw _ _ Hμ) with (l := param_level);
      [eassumption | apply (set_params_evaluated_of_sorts T γ Γ Δ param_level param_sorts); [assumption | ft_from_ih]
      | do 2 eexists; eassumption | apply Mv_unit; eapply wf_unit_eq_flatten; eassumption].
  - split; [ft_cs | eapply (set_rule_unit_eq_expand T γ Hfn0 Hmods); [do 2 eexists; eassumption | apply Mv_unit; eapply wf_unit_eq_expand; eassumption]].
  - split; [ft_cs | eapply set_rule_unit_eq_sym; do 2 eexists; eassumption].
  - split; [ft_cs | eapply set_rule_unit_eq_trans; do 2 eexists; eassumption].
  (* module expressions *)
  - ft_by_kripke set_rule_me_unit.
  - ft_by_kripke set_rule_me_var.
  - ft_by_kripke set_rule_me_lit.
  - match goal with |- _ /\ set_rel_modexp_eq _ _ ?G ?L ?Rt =>
      assert (Hc : gc_deps ⍮ gc_stack ⍮ G ⊢ᵐ L ≈ Rt) by (apply Mv_me; eapply wf_me_mem; eassumption) end.
    pose proof (wf_modexp_eq_refl_left Hc). pose proof (wf_modexp_eq_refl_right Hc).
    ft_by set_rule_me_mem.
  - split; [ft_cs | ft_kripke; eapply (set_rule_me_app Θ Ξ T γ Γ H H' N N' R _ B _ Srt R' _ B' _ Srt'); ft_prem].
  - ft_by_kripke set_rule_me_delta_slot.
  - ft_by set_rule_me_delta_sel.
  - split; [ft_cs |].
    match goal with |- context [me_lit (gu_open (tele_sub ?Δ ?σ) (gmod_sub ?Φ _))] =>
      replace (gu_open (tele_sub Δ σ) _) with (gunit_sub (gu_open Δ Φ) σ) by (rewrite gunit_sub_mk; reflexivity) end.
    ft_kripke. eapply set_rule_me_beta; [ft_prem | | ft_prem ..].
    rewrite gunit_sub_mk. eapply wf_me_beta_body; eassumption.
  - split; [ft_cs |].
    match goal with |- context [me_lit (gu_mk (tele_sub ?Δ ?σ) (md_alias (modexp_sub ?E _)))] =>
      replace (gu_mk (tele_sub Δ σ) _) with (gunit_sub (gu_mk Δ (md_alias E)) σ) by (rewrite gunit_sub_mk; reflexivity) end.
    ft_kripke. eapply set_rule_me_beta; [ft_prem | | ft_prem ..].
    rewrite gunit_sub_mk. eapply wf_me_beta_alias; eassumption.
  - split; [ft_cs | ft_kripke; eapply set_rule_me_beta_alias0;
                    [ft_prem | eapply wf_modexp_eq_refl_left; eapply wf_me_beta_alias0; eassumption | ft_prem]].
  - ft_by_kripke set_rule_me_sym.
  - ft_by_kripke set_rule_me_trans.
Qed.

End FundamentalTheorem.
