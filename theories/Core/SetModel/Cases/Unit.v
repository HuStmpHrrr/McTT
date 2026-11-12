(** * Valid Units Abstracted over Parameters

    A unit valid in a context extended by assumptions is valid abstracted
    over them, in the context below ([set_valid_unit_abs]).  Its value at an
    environment is a function of each parameter's value
    ([set_unit_denotes_bind]); the members' proofness every function node
    carries is the abstracted unit's, read at that environment, so the
    inner unit's value has its nodes' proofness replaced
    ([params_with_proofs]). *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Respects Substitution JudgmentSubstitution.
From Mctt.Core.SetModel.Interpretation.Global Require Import Model.
From Mctt.Core.SetModel.Cases Require Import SubtypingCases ValidUnit MemberTypes ModuleCases.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas DescTyping LookupSound Presup.
Import ListNotations.

Section Unit.
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

(** ** The Proofness of Function Nodes *)

(** [params_with_proofs L P m]: the module [m] over the parameters [L],
    outermost first, its function nodes of the parameters given the
    proofness [P].  A unit bound over one more parameter stores the outer
    proofness in every node; the inner unit's value at each value of the
    parameter comes from a derivation storing the inner proofness, equal
    to the outer only pointwise, and picking a derivation per value would
    need choice: so the inner value's nodes are rebuilt explicitly. *)
Fixpoint params_with_proofs (L : list centry) (P : member_proofness) (m : set_module) : set_module :=
  match L with
  | nil => m
  | ce_ass _ _ :: L' =>
      match m with
      | set_module_params a _ f => set_module_params a P (fun v => params_with_proofs L' P (f v))
      | _ => m
      end
  | _ :: L' => params_with_proofs L' P m
  end.

(** A unit's parameters denote at any proofness, the function nodes
    replaced. *)
Lemma set_interp_unit_params_with_proofs : forall Γ ρ P L D m, set_interp_unit_params T γ Γ ρ P L D m ->
    forall P', set_interp_unit_params T γ Γ ρ P' L D (params_with_proofs L P' m).
Proof.
  induction 1 as [Γ ρ P D m Hm | Γ ρ P κ A L D a f Hc HA Hf IH | Γ ρ P A M L D v m Hc HM Hm IH
                 | Γ ρ P U L D mu m Hc HU Hm IH | Γ ρ P A M U L D v mu m Hc HM HU Hm IH]; intros P'; cbn [params_with_proofs].
  - constructor. exact Hm.
  - constructor; [exact Hc | exact HA |]. intros x Hx. exact (IH x Hx P').
  - econstructor; [exact Hc | exact HM | exact (IH P')].
  - econstructor; [exact Hc | exact HU | exact (IH P')].
  - econstructor; [exact Hc | exact HM | exact HU | exact (IH P')].
Qed.

(** ** One Parameter Abstracted *)

(** The unit over one more parameter: the function of the parameter's
    value, at the outer unit's proofness. *)
Lemma set_unit_denotes_bind : forall Γ Δ κ X D G, set_ctx T γ (ce_ass κ X :: Γ) -> ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κ X :: Γ ->
    set_modexp_denotes T γ (ce_ass κ X :: Γ) (me_lit (gu_mk Δ D)) G ->
    exists F, set_modexp_denotes T γ Γ (me_lit (gu_mk (Δ ++ [ce_ass κ X]) D)) F.
Proof.
  intros * HC Hc HG. pose proof HC as [HΓ (FX & HX)].
  set (P := fun ρ => unit_member_proofs γ (env_slot_proofs γ ρ) (gu_mk (Δ ++ [ce_ass κ X]) D)).
  exists (fun ρ => set_module_params (FX ρ) (P ρ)
                     (fun v => params_with_proofs (List.rev Δ) (P ρ) (G (set_env_extend ρ (set_entry_term κ v))))).
  apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ. constructor.
  apply (set_interp_gunit_mk T γ _ _ _ _ (P ρ)); [intros; reflexivity |].
  rewrite List.rev_app_distr. cbn [List.rev List.app].
  constructor; [exact Hc | exact (set_denotes_exists _ _ _ _ _ HX _ Hρ) |]. intros v Hv.
  pose proof (set_modexp_denotes_exists _ _ _ _ _ HG _
                (set_env_in_extend_ass T γ _ _ _ _ _ _ Hρ (set_denotes_exists _ _ _ _ _ HX _ Hρ) Hv)) as Hm.
  apply set_interp_me_lit_iff in Hm. inversion Hm; subst.
  match goal with Hp : set_interp_unit_params _ _ _ _ _ _ _ _ |- _ => exact (set_interp_unit_params_with_proofs _ _ _ _ _ _ Hp _) end.
Qed.

Lemma set_unit_rel_bind : forall Γ Δ κ X D, set_ctx T γ (ce_ass κ X :: Γ) -> ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κ X :: Γ ->
    set_modexp_rel T γ (ce_ass κ X :: Γ) (me_lit (gu_mk Δ D)) (me_lit (gu_mk Δ D)) ->
    set_modexp_rel T γ Γ (me_lit (gu_mk (Δ ++ [ce_ass κ X]) D)) (me_lit (gu_mk (Δ ++ [ce_ass κ X]) D)).
Proof.
  intros * HC Hc (G & _ & [HG _ _]). destruct (set_unit_denotes_bind _ _ _ _ _ _ HC Hc HG) as (F & HF).
  exists F, F. constructor; [exact HF | exact HF |].
  intros ρ Hρ. exact (set_modexp_denotes_unique _ _ _ _ _ HF _ _ _ Hρ (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ)).
Qed.

(** ** Parameters of Evaluated Sorts *)

(** A type of a universe is one of every universe above. *)
Lemma set_exp_eq_typ_le : forall Γ A l l', set_exp_eq T γ Γ (a_typ l) A A -> l <= l' -> set_exp_eq T γ Γ (a_typ l') A A.
Proof.
  intros * HA Hle. destruct (Nat.eq_dec l l') as [<- | Hne]; [exact HA |].
  destruct HA as (FS & FA & FA' & HA).
  destruct (set_rule_subtyp_univ T γ Γ l l' ltac:(lia)) as (FS0 & FS' & HS).
  exact (set_rule_exp_eq_subtyp T γ _ _ _ _ _ _ _ _ _ _ HA HS).
Qed.

Lemma set_params_evaluated_le : forall Γ Δ l l', set_params_evaluated T γ Γ Δ l -> l <= l' -> set_params_evaluated T γ Γ Δ l'.
Proof.
  intros * H Hle Δ1 κ A Δ2 E. destruct (H _ _ _ _ E) as [HA | HA]; [left | right; exact HA].
  exact (set_exp_eq_typ_le _ _ _ _ HA Hle).
Qed.

(** The parameters of a unit over one more parameter, of the context
    extended by it. *)
Lemma set_params_evaluated_snoc : forall Γ Δ e l, set_params_evaluated T γ (e :: Γ) Δ l ->
    (forall κ A, e = ce_ass κ A -> set_exp_eq T γ Γ (a_typ l) A A \/ set_exp_eq T γ Γ a_level_sort A A) ->
    set_params_evaluated T γ Γ (Δ ++ [e]) l.
Proof.
  intros * H He Δ1 κ A Δ2 E. destruct Δ2 as [| d Δ2 _] using List.rev_ind.
  - apply List.app_inj_tail in E as [-> ->]. exact (He _ _ eq_refl).
  - rewrite List.app_comm_cons, List.app_assoc in E. apply List.app_inj_tail in E as [-> ->].
    rewrite <- List.app_assoc. exact (H _ _ _ _ eq_refl).
Qed.

(** A valid unit over the context extended by an assumption is valid
    over one more parameter, when it is well formed so. *)
Lemma set_valid_unit_bind : forall Γ Δ κ X D l, set_valid_unit T γ (ce_ass κ X :: Γ) (me_lit (gu_mk Δ D)) ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_lit (gu_mk (Δ ++ [ce_ass κ X]) D) ≈ me_lit (gu_mk (Δ ++ [ce_ass κ X]) D) ->
    (set_exp_eq T γ Γ (a_typ l) X X \/ set_exp_eq T γ Γ a_level_sort X X) ->
    set_valid_unit T γ Γ (me_lit (gu_mk (Δ ++ [ce_ass κ X]) D)).
Proof.
  intros * HK Hw HX. pose proof (set_valid_unit_ctx T γ _ _ HK) as HC.
  pose proof (presup_modexp_eq_ctx (set_valid_unit_wf T γ _ _ HK)) as Hc.
  assert (Hev : forall l1, set_params_evaluated T γ (ce_ass κ X :: Γ) Δ l1 -> exists l', set_params_evaluated T γ Γ (Δ ++ [ce_ass κ X]) l').
  { intros l1 Hl1. exists (max l1 l). apply set_params_evaluated_snoc.
    - apply (set_params_evaluated_le _ _ l1); [exact Hl1 | lia].
    - intros κ' A E. injection E as <- <-. destruct HX as [HX | HX]; [left | right; exact HX].
      apply (set_exp_eq_typ_le _ _ l); [exact HX | lia]. }
  inversion HK as [| ? Δ0 Φ Φx Hb Hsub Hop | ? Δ0 E Hal HE]; subst;
    [exfalso; match goal with Hq : me_apps _ _ = me_lit _ |- _ => exact (me_apps_qname_not_lit _ _ _ Hq) end | |].
  - (* a body *)
    destruct Hb as [_ Hx HΔ [l1 Hl1] HΓ HCx Hs Hsh Hshx Hr Hro].
    apply set_valid_unit_body with (Φx := Φx).
    + constructor; [exact Hw | rewrite <- List.app_assoc; exact Hx | apply List.Forall_app; split; [exact HΔ | repeat constructor; eauto]
                   | exact (Hev _ Hl1) | exact (proj1 HC) | rewrite <- List.app_assoc; exact HCx | rewrite <- List.app_assoc; exact Hs
                   | exact Hsh | exact Hshx | exact (set_unit_rel_bind _ _ _ _ _ HC Hc Hr)
                   | intros * Hk; rewrite <- List.app_assoc; exact (Hro _ _ _ Hk)].
    + intros * Hp HU. rewrite <- List.app_assoc. exact (Hsub _ _ _ _ Hp HU).
    + intros * Hk. rewrite <- List.app_assoc. exact (Hop _ _ _ Hk).
  - (* an alias *)
    destruct Hal as [_ HΔ [l1 Hl1] HΓ HCΔ Hr Ht].
    apply set_valid_unit_alias; [| rewrite <- List.app_assoc; exact HE].
    constructor; [exact Hw | apply List.Forall_app; split; [exact HΔ | repeat constructor; eauto] | exact (Hev _ Hl1)
                 | exact (proj1 HC) | rewrite <- List.app_assoc; exact HCΔ | exact (set_unit_rel_bind _ _ _ _ _ HC Hc Hr)
                 | rewrite <- List.app_assoc; exact Ht].
Qed.

(** A literal relating to itself over the context extended by assumptions
    relates to itself abstracted over them. *)
Lemma set_unit_rel_abs : forall Δ Γ Δy D, all_assumptions Δ -> set_ctx T γ (Δ ++ Γ) -> ⊢ gc_deps ⍮ gc_stack ⍮ Δ ++ Γ ->
    set_modexp_rel T γ (Δ ++ Γ) (me_lit (gu_mk Δy D)) (me_lit (gu_mk Δy D)) ->
    set_modexp_rel T γ Γ (me_lit (gu_mk (Δy ++ Δ) D)) (me_lit (gu_mk (Δy ++ Δ) D)).
Proof.
  intros Δ. induction Δ as [| e Δ IH] using List.rev_ind; intros Γ Δy D HΔ HC Hc Hr.
  - rewrite List.app_nil_r. exact Hr.
  - apply List.Forall_app in HΔ as [HΔ He]. inversion He as [| ? ? (κ & X & ->) _]; subst.
    rewrite <- List.app_assoc in HC, Hc, Hr. cbn [List.app] in HC, Hc, Hr.
    rewrite List.app_assoc. apply (set_unit_rel_bind _ _ _ _ _ (set_ctx_app_r T γ _ _ HC) (ctx_app_wf_tail _ _ _ _ Hc)).
    exact (IH _ _ _ HΔ HC Hc Hr).
Qed.

(** ** Values Over Parameters Compared *)

(** Over assumptions read from an environment, the values of two units
    agree, the second over more parameters, when what is left of each
    agrees at every environment past them, at the slots the assumptions
    push. *)
Lemma set_unit_params_eq_app : forall L Γ ρ P1 P2 D1 L2 D2 m1 m2, all_assumptions L -> set_env_in T γ Γ ρ ->
    set_interp_unit_params T γ Γ ρ P1 L D1 m1 -> set_interp_unit_params T γ Γ ρ P2 (L ++ L2) D2 m2 ->
    (forall ys x, P1 ys x = P2 ys x) ->
    (forall ρ' n1 n2, set_env_in T γ (List.rev L ++ Γ) ρ' ->
       slot_proofs_eq (env_slot_proofs γ ρ') (tele_out_proofs γ (env_slot_proofs γ ρ) L) ->
       set_interp_moddef T γ (List.rev L ++ Γ) ρ' D1 n1 -> set_interp_unit_params T γ (List.rev L ++ Γ) ρ' P2 L2 D2 n2 ->
       set_module_eq γ n1 n2) ->
    set_module_eq γ m1 m2.
Proof.
  induction L as [| e L IH]; intros Γ ρ P1 P2 D1 L2 D2 m1 m2 HL Hρ H1 H2 EP Hbase.
  - inversion H1; subst. cbn [List.app] in H2. apply (Hbase ρ); [exact Hρ | intros s ys x; reflexivity | assumption | exact H2].
  - inversion HL as [| ? ? (κ & A & ->) HL']; subst. cbn [List.app] in H2.
    inversion H1 as [| ? ? ? ? ? ? ? a1 f1 Hc HA1 Hf1 | | |]; subst.
    inversion H2 as [| ? ? ? ? ? ? ? a2 f2 _ HA2 Hf2 | | |]; subst.
    pose proof (set_env_rel_eq T γ _ _ _ Hρ) as Eρ.
    pose proof (set_interp_functional T γ Hfn Hmods _ _ _ _ HA1 _ _ Eρ HA2) as Ea.
    apply set_module_eq_params; [exact Ea | exact EP |]. intros x x' Hx Exx'.
    assert (Hx2 : forall z, set_eq x z -> set_mem z (code_carrier a2))
      by (intros z Ez; eapply set_mem_eq_l; [exact Ez |]; eapply set_mem_eq_r; [apply code_carrier_resp; exact Ea | exact Hx]).
    pose proof (set_env_in_extend_ass T γ _ _ κ _ _ _ Hρ HA1 Hx) as Hρx.
    assert (E1 : set_module_eq γ (f1 x) (f2 x)).
    { apply (IH _ _ _ _ _ _ _ _ _ HL' Hρx (Hf1 _ Hx) (Hf2 _ (Hx2 _ (set_eq_refl x))) EP).
      intros ρ' n1 n2 Hρ' Eκ Hn1 Hn2. cbn [List.rev] in Hbase. rewrite <- List.app_assoc in Hbase.
      apply (Hbase ρ' n1 n2 Hρ'); [| exact Hn1 | exact Hn2].
      intros s ys z. rewrite (Eκ s ys z). cbn [tele_out_proofs].
      apply (tele_out_proofs_resp γ L). intros s' ys' z'. apply env_slot_proofs_extend_term. }
    eapply set_module_eq_trans; [exact E1 |].
    assert (Eρx : set_env_eq γ (set_env_extend ρ (set_entry_term κ x)) (set_env_extend ρ (set_entry_term κ x')))
      by (intros [| s]; [constructor; exact Exx' | apply Eρ]).
    exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (set_interp_functional_all T γ Hfn Hmods)))))) _ _ _ _ _ _
             (Hf2 _ (Hx2 _ (set_eq_refl x))) _ P2 _ Eρx ltac:(intros; reflexivity) (Hf2 _ (Hx2 _ Exx'))).
Qed.

(** ** Aliases of Literals Flattened *)

(** An alias over assumptions of a literal is the literal over both
    telescopes. *)
Lemma set_unit_rel_flatten : forall Γ Δ Δ' D, all_assumptions Δ ->
    set_modexp_rel T γ Γ (me_lit (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))) (me_lit (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))) ->
    set_modexp_rel T γ Γ (me_lit (gu_mk (Δ' ++ Δ) D)) (me_lit (gu_mk (Δ' ++ Δ) D)) ->
    set_modexp_rel T γ Γ (me_lit (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))) (me_lit (gu_mk (Δ' ++ Δ) D)).
Proof.
  intros * HΔ (FA & _ & [HFA _ _]) (FF & _ & [HFF _ _]). exists FA, FF. constructor; [exact HFA | exact HFF |].
  intros ρ Hρ.
  pose proof (set_modexp_denotes_exists _ _ _ _ _ HFA _ Hρ) as HmA. apply set_interp_me_lit_iff in HmA.
  pose proof (set_modexp_denotes_exists _ _ _ _ _ HFF _ Hρ) as HmF. apply set_interp_me_lit_iff in HmF.
  inversion HmA as [? ? ? ? PA mA HPA HLA]; subst. inversion HmF as [? ? ? ? PF mF HPF HLF]; subst.
  rewrite List.rev_app_distr in HLF.
  apply (set_unit_params_eq_app (List.rev Δ) Γ ρ PA PF _ (List.rev Δ') D _ _ (List.Forall_rev HΔ) Hρ HLA HLF).
  - intros ys x. rewrite HPA, HPF, !unit_member_proofs_tele_out. cbn [moddef_member_proofs modexp_member_proofs].
    rewrite unit_member_proofs_tele_out, List.rev_app_distr, tele_out_proofs_app. reflexivity.
  - intros ρ' n1 n2 Hρ' Eκ Hn1 Hn2. rewrite List.rev_involutive in Hρ', Hn1, Hn2.
    inversion Hn1; subst. match goal with Hm : set_interp_modexp _ _ _ _ (me_lit _) _ |- _ => apply set_interp_me_lit_iff in Hm; inversion Hm; subst end.
    match goal with Hp : set_interp_unit_params _ _ _ _ ?P1 _ D n1 |- _ =>
      apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (set_interp_functional_all T γ Hfn Hmods)))))) _ _ _ _ _ _ Hp _ PF _
               (set_env_rel_eq T γ _ _ _ Hρ')) end.
    + intros ys x. match goal with HP : forall ys x, _ ys x = unit_member_proofs _ _ _ ys x |- _ => rewrite HP end.
      rewrite HPF, (proj1 (proj2 (unit_member_proofs_resp_all γ)) _ _ _ Eκ), !unit_member_proofs_tele_out.
      rewrite List.rev_app_distr, tele_out_proofs_app. reflexivity.
    + exact Hn2.
Qed.

(** Aliases over assumptions of related targets of one proofness are
    related. *)
Lemma set_alias_rel_cong : forall Γ Δ E1 E2, all_assumptions Δ ->
    set_modexp_rel T γ Γ (me_lit (gu_mk Δ (md_alias E1))) (me_lit (gu_mk Δ (md_alias E1))) ->
    set_modexp_rel T γ Γ (me_lit (gu_mk Δ (md_alias E2))) (me_lit (gu_mk Δ (md_alias E2))) ->
    set_modexp_rel T γ (Δ ++ Γ) E1 E2 ->
    (forall κs, set_slots_coherent γ (Δ ++ Γ) κs -> forall ys x, modexp_member_proofs γ κs E1 ys x = modexp_member_proofs γ κs E2 ys x) ->
    set_modexp_rel T γ Γ (me_lit (gu_mk Δ (md_alias E1))) (me_lit (gu_mk Δ (md_alias E2))).
Proof.
  intros * HΔ (F1 & _ & [HF1 _ _]) (F2 & _ & [HF2 _ _]) (G1 & G2 & [HG1 HG2 EG]) Hpr.
  exists F1, F2. constructor; [exact HF1 | exact HF2 |]. intros ρ Hρ.
  pose proof (set_modexp_denotes_exists _ _ _ _ _ HF1 _ Hρ) as Hm1. apply set_interp_me_lit_iff in Hm1.
  pose proof (set_modexp_denotes_exists _ _ _ _ _ HF2 _ Hρ) as Hm2. apply set_interp_me_lit_iff in Hm2.
  inversion Hm1 as [? ? ? ? P1 m1 HP1 HL1]; subst. inversion Hm2 as [? ? ? ? P2 m2 HP2 HL2]; subst.
  rewrite <- (List.app_nil_r (List.rev Δ)) in HL2.
  apply (set_unit_params_eq_app (List.rev Δ) Γ ρ P1 P2 _ nil _ _ _ (List.Forall_rev HΔ) Hρ HL1 HL2).
  - intros ys x. rewrite HP1, HP2, !unit_member_proofs_tele_out. cbn [moddef_member_proofs].
    apply Hpr. exact (set_slots_coherent_tele_out γ _ _ _ HΔ (set_slots_coherent_env T γ _ _ Hρ)).
  - intros ρ' n1 n2 Hρ' _ Hn1 Hn2. rewrite List.rev_involutive in Hρ', Hn1, Hn2.
    inversion Hn1; subst. inversion Hn2; subst. match goal with Hd : set_interp_moddef _ _ _ _ (md_alias E2) _ |- _ => inversion Hd; subst end.
    match goal with H1 : set_interp_modexp _ _ _ _ E1 ?a, H2 : set_interp_modexp _ _ _ _ E2 ?b |- set_module_eq _ ?a ?b =>
      eapply set_module_eq_trans; [exact (set_modexp_denotes_unique _ _ _ _ _ HG1 _ _ _ Hρ' H1) |];
      eapply set_module_eq_trans; [exact (EG _ Hρ') |]; exact (set_module_eq_sym _ _ (set_modexp_denotes_unique _ _ _ _ _ HG2 _ _ _ Hρ' H2)) end.
Qed.

(** ** A Telescope of Assumptions Abstracted *)

(** A valid literal over the context extended by assumptions is valid
    abstracted over them, when it is well formed so. *)
Lemma set_valid_unit_abs : forall Δ Γ Δy D l, set_valid_unit T γ (Δ ++ Γ) (me_lit (gu_mk Δy D)) -> all_assumptions Δ ->
    set_params_evaluated T γ Γ Δ l ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_lit (gu_mk (Δy ++ Δ) D) ≈ me_lit (gu_mk (Δy ++ Δ) D) ->
    set_valid_unit T γ Γ (me_lit (gu_mk (Δy ++ Δ) D)).
Proof.
  intros Δ. induction Δ as [| e Δ IH] using List.rev_ind; intros Γ Δy D l HK HΔ Hl Hw.
  - rewrite List.app_nil_r. exact HK.
  - apply List.Forall_app in HΔ as [HΔ He]. inversion He as [| ? ? (κ & X & ->) _]; subst.
    rewrite <- List.app_assoc in HK. cbn [List.app] in HK.
    pose proof (proj1 (modexp_gen _ _ _ _ _ Hw)) as Hf; cbn [gen_m] in Hf. rewrite List.app_assoc in Hf.
    pose proof (wf_me_lit _ _ _ _ _ (unit_eq_of_full _ _ _ _ (unit_full_unabs _ _ _ _ _ _ Hf))) as Hw'; cbn [List.app] in Hw'.
    assert (Hl' : set_params_evaluated T γ (ce_ass κ X :: Γ) Δ l).
    { intros Δ1 κ' A Δ2 E. rewrite E in Hl. pose proof (Hl Δ1 κ' A (Δ2 ++ [ce_ass κ X]) ltac:(rewrite <- List.app_assoc; reflexivity)) as H.
      rewrite <- List.app_assoc in H. exact H. }
    rewrite List.app_assoc in Hw |- *.
    apply (set_valid_unit_bind _ _ _ _ _ l); [exact (IH _ _ _ _ HK HΔ Hl' Hw') | exact Hw |].
    exact (Hl Δ κ X nil eq_refl).
Qed.

(** ** The Rules of Units *)

(** Parameters each of a sort a universe at [l] or the type of levels,
    semantically. *)
Lemma set_params_evaluated_of_sorts : forall Γ Δ l ps, (forall k, parameter_sort l (ps k)) ->
    (forall Δ1 κ A Δ2, Δ = Δ1 ++ ce_ass κ A :: Δ2 -> set_exp_eq T γ (Δ2 ++ Γ) (ps (List.length Δ2)) A A) ->
    set_params_evaluated T γ Γ Δ l.
Proof.
  intros * Hps HA Δ1 κ A Δ2 E. pose proof (HA _ _ _ _ E) as H.
  destruct (Hps (List.length Δ2)); [left | right]; exact H.
Qed.

Lemma set_rule_unit_eq_sym : forall Γ U U', set_unit_eq T γ Γ U U' -> set_unit_eq T γ Γ U' U.
Proof.
  intros * (F & F' & [HF HF' E HU HU']). exists F', F. constructor; [exact HF' | exact HF | | exact HU' | exact HU].
  intros ρ Hρ. apply set_module_eq_sym. exact (E _ Hρ).
Qed.

Lemma set_rule_unit_eq_trans : forall Γ U U' U'', set_unit_eq T γ Γ U U' -> set_unit_eq T γ Γ U' U'' -> set_unit_eq T γ Γ U U''.
Proof.
  intros * (F & F' & [HF HF' E HU _]) (G & G' & [HG HG' E' _ HU'']). exists F, G'. constructor; [exact HF | exact HG' | | exact HU | exact HU''].
  intros ρ Hρ. eapply set_module_eq_trans; [exact (E _ Hρ) |]. eapply set_module_eq_trans; [| exact (E' _ Hρ)].
  exact (set_modexp_denotes_unique _ _ _ _ _ HG _ _ _ Hρ (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ)).
Qed.

(** An alias over assumptions of a literal is the literal over both
    telescopes. *)
Lemma set_rule_unit_eq_flatten : forall Γ Δ Δ' D l, all_assumptions Δ -> set_params_evaluated T γ Γ Δ l ->
    set_unit_eq T γ (Δ ++ Γ) (gu_mk Δ' D) (gu_mk Δ' D) ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ≈ gu_mk (Δ' ++ Δ) D ->
    set_unit_eq T γ Γ (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D)))) (gu_mk (Δ' ++ Δ) D).
Proof.
  intros * HΔ Hl (FU & _ & [HFU _ _ HK _]) HUU.
  pose proof (set_valid_unit_ctx T γ _ _ HK) as HΔΓ. pose proof (set_ctx_app_r T γ _ _ HΔΓ) as HΓ.
  pose proof (presup_modexp_eq_ctx (set_valid_unit_wf T γ _ _ HK)) as HcΔΓ.
  pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_left HUU)) as HwA. pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_right HUU)) as HwF.
  pose proof (set_valid_unit_rel T γ Hfn Hmods Hok _ _ HK) as HrU.
  assert (HrA : set_modexp_rel T γ Γ (me_lit (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))) (me_lit (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D)))))).
  { exact (set_unit_rel_abs Δ Γ nil _ HΔ HΔΓ HcΔΓ
             (set_modexp_rel_refl_left T γ _ _ _ (set_alias0_rel T γ Hfn Hmods _ _ HΔΓ HrU))). }
  assert (HKA : set_valid_unit T γ Γ (me_lit (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D)))))).
  { apply set_valid_unit_alias; [| exact (set_valid_modexp_of_unit T γ Hfn Hmods Hok _ _ HK)].
    constructor; [exact HwA | exact HΔ | exists l; exact Hl | exact HΓ | exact HΔΓ | exact HrA | exact HrU]. }
  pose proof (set_valid_unit_abs _ _ _ _ _ HK HΔ Hl HwF) as HKF.
  destruct (set_unit_rel_flatten _ _ _ _ HΔ HrA (set_valid_unit_rel T γ Hfn Hmods Hok _ _ HKF)) as (F1 & F2 & [HF1 HF2 E12]).
  exists F1, F2. constructor; [exact HF1 | exact HF2 | exact E12 | exact HKA | exact HKF].
Qed.

(** A unit's parameters denote over a definition reading as another. *)
Lemma set_interp_unit_params_moddef : forall Γ ρ P L D m, set_interp_unit_params T γ Γ ρ P L D m ->
    forall D', (forall Γ' ρ' n, set_interp_moddef T γ Γ' ρ' D n -> set_interp_moddef T γ Γ' ρ' D' n) ->
    set_interp_unit_params T γ Γ ρ P L D' m.
Proof.
  induction 1 as [Γ ρ P D m Hm | Γ ρ P κ A L D a f Hc HA Hf IH | Γ ρ P A M L D v m Hc HM Hm IH
                 | Γ ρ P U L D mu m Hc HU Hm IH | Γ ρ P A M U L D v mu m Hc HM HU Hm IH]; intros D' HD.
  - constructor. exact (HD _ _ _ Hm).
  - constructor; [exact Hc | exact HA |]. intros x Hx. exact (IH x Hx _ HD).
  - econstructor; [exact Hc | exact HM | exact (IH _ HD)].
  - econstructor; [exact Hc | exact HU | exact (IH _ HD)].
  - econstructor; [exact Hc | exact HM | exact HU | exact (IH _ HD)].
Qed.

(** A body unit is its expansion. *)
Lemma set_rule_unit_eq_expand : forall Γ Δ Φ, set_unit_eq T γ Γ (gu_open Δ Φ) (gu_open Δ Φ) ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ (gm_expand Φ) ->
    set_unit_eq T γ Γ (gu_open Δ Φ) (gu_open Δ (gm_expand Φ)).
Proof.
  intros * (F & _ & [HF _ _ HK _]) HUU.
  pose proof (gm_noopen_expand Φ) as Hno. pose proof (gm_expand_noopen _ Hno) as Hee.
  assert (HD : forall Γ' ρ' n, set_interp_moddef T γ Γ' ρ' (md_body sm_open Φ) n -> set_interp_moddef T γ Γ' ρ' (md_body sm_open (gm_expand Φ)) n)
    by (intros * Hn; inversion Hn; subst; eapply set_interp_md_body; rewrite Hee; eassumption).
  assert (HP : forall ρ ys x, unit_member_proofs γ (env_slot_proofs γ ρ) (gu_open Δ Φ) ys x =
                             unit_member_proofs γ (env_slot_proofs γ ρ) (gu_open Δ (gm_expand Φ)) ys x).
  { intros ρ ys x. rewrite !unit_member_proofs_tele_out. cbn [moddef_member_proofs].
    rewrite (proj2 (body_member_proofs_expand γ Φ _)). reflexivity. }
  pose proof (set_valid_unit_ctx T γ _ _ HK) as HΓ.
  set (F' := fun ρ => params_with_proofs (List.rev Δ) (unit_member_proofs γ (env_slot_proofs γ ρ) (gu_open Δ (gm_expand Φ))) (F ρ)).
  assert (HF' : set_modexp_denotes T γ Γ (me_lit (gu_open Δ (gm_expand Φ))) F').
  { apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ. constructor.
    pose proof (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ) as Hm. apply set_interp_me_lit_iff in Hm.
    inversion Hm as [? ? ? ? P m HPm HL]; subst.
    apply (set_interp_gunit_mk T γ _ _ _ _ (unit_member_proofs γ (env_slot_proofs γ ρ) (gu_open Δ (gm_expand Φ)))); [intros; reflexivity |].
    exact (set_interp_unit_params_moddef _ _ _ _ _ _ (set_interp_unit_params_with_proofs _ _ _ _ _ _ HL _) _ HD). }
  assert (E : forall ρ, set_env_in T γ Γ ρ -> set_module_eq γ (F ρ) (F' ρ)).
  { intros ρ Hρ.
    pose proof (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ) as Hm1. apply set_interp_me_lit_iff in Hm1.
    pose proof (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ) as Hm2. apply set_interp_me_lit_iff in Hm2.
    inversion Hm1 as [? ? ? ? P1 m1 HP1 HL1]; subst. inversion Hm2 as [? ? ? ? P2 m2 HP2 HL2]; subst.
    pose proof HK as HK0. inversion HK0 as [| ? ? ? Φx [_ _ HΔ _ _ _ _ _ _ _ _] _ _ |]; subst;
      try (exfalso; match goal with Hq : me_apps _ _ = me_lit _ |- _ => exact (me_apps_qname_not_lit _ _ _ Hq) end).
    rewrite <- (List.app_nil_r (List.rev Δ)) in HL2.
    apply (set_unit_params_eq_app (List.rev Δ) Γ ρ P1 P2 _ nil _ _ _ (List.Forall_rev HΔ) Hρ HL1 HL2).
    - intros ys x. rewrite HP1, HP2. apply HP.
    - intros ρ' n1 n2 Hρ' _ Hn1 Hn2. inversion Hn2; subst.
      match goal with Hd : set_interp_moddef _ _ _ _ _ n2 |- _ => inversion Hd; subst end. inversion Hn1; subst.
      rewrite Hee in *. constructor.
      match goal with Ha : set_interp_gmod _ _ _ _ (gm_expand Φ) ?ms1 _, Hb : set_interp_gmod _ _ _ _ (gm_expand Φ) ?ms2 _ |-
                      set_members_eq _ ?ms1 ?ms2 =>
        exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (set_interp_functional_all T γ Hfn Hmods))))))))
                _ _ _ _ _ Ha _ _ _ (set_env_rel_eq T γ _ _ _ Hρ') Hb)) end. }
  (* the expansion is a valid body *)
  assert (HK' : set_valid_unit T γ Γ (me_lit (gu_open Δ (gm_expand Φ)))).
  { inversion HK as [| ? ? ? Φx Hb Hsub Hop |]; subst;
      try (exfalso; match goal with Hq : me_apps _ _ = me_lit _ |- _ => exact (me_apps_qname_not_lit _ _ _ Hq) end).
    destruct Hb as [_ Hx HΔ Hl HΓ' HC Hs Hsh Hshx _ _].
    pose proof (body_xp_expand _ _ _ _ _ Hx) as Hxe. subst Φx.
    apply set_valid_unit_body with (Φx := gm_expand Φ); [| exact Hsub |].
    - constructor; [exact (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_right HUU)) | exact (body_xp_noopen _ _ _ _ Hno) | exact HΔ | exact Hl
                   | exact HΓ' | exact HC | exact Hs | exact Hshx | exact Hshx | | ].
      + exists F', F'. constructor; [exact HF' | exact HF' |].
        intros ρ Hρ. exact (set_modexp_denotes_unique _ _ _ _ _ HF' _ _ _ Hρ (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ)).
      + intros k Ψ H Hk. rewrite (body_opens_noopen _ Hno) in Hk. destruct k; discriminate.
    - intros k Ψ H Hk. rewrite (body_opens_noopen _ Hno) in Hk. destruct k; discriminate. }
  exists F, F'. constructor; [exact HF | exact HF' | exact E | exact HK | exact HK'].
Qed.

End Unit.
