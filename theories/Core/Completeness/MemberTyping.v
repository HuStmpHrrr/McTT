(** * Typed Members up to the Module PER

    Typing the members of a module value is a property of its class in the
    module PER ([mtyped_per]) and of the class of its type value
    ([mtyped_resp]).  A typed value still lacking an argument applies to an
    argument of its next parameter's type, and related such values give
    related results. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases UniverseCases SubstitutionCases LetCases UnitCases InstanceCases MemberCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Related Values Agree on Saturation and on the Next Parameter *)

Lemma per_ltele_next : forall ts ρ D ts' ρ' D' args args' A,
    per_ltele ts ρ D ts' ρ' D' args args' ->
    nth_error ts (List.length args) = Some (ce_ass A) ->
    exists A' i R, nth_error ts' (List.length args') = Some (ce_ass A') /\
      PER.Definitions.rel_typ i A (env_args ρ args) A' (env_args ρ' args') R.
Proof.
  intros * H; revert A; induction H; intros A0 Hn; cbn in Hn |- *.
  - exact (IHper_ltele _ Hn).
  - injection Hn as ->; do 3 eexists; split; [ reflexivity | eassumption ].
  - discriminate.
Qed.

Lemma msat_rel : forall w, msat w -> forall w', per_dmod w w' -> msat w'.
Proof.
  induction 1 as [ρ Δ Φ args Hl | ρ Δ E args h Hl HE Hs IH]; intros w' Hw.
  - destruct (per_dmod_body_sat _ _ _ _ _ Hw Hl) as (ρ' & Δ' & Φ' & args' & -> & Hl' & _).
    constructor; exact Hl'.
  - destruct (per_dmod_alias_sat _ _ _ _ _ Hw Hl) as (ρ' & Δ' & E' & args' & h0 & h' & -> & Hl' & HE0 & HE' & Hhh).
    pose proof (functional_eval_modexp _ _ _ _ HE HE0) as <-.
    econstructor; [ exact Hl' | exact HE' | exact (IH _ Hhh) ].
Qed.

Lemma nextparam_rel : forall w a, nextparam w a -> forall w', per_dmod w w' ->
    exists a' i R, nextparam w' a' /\ per_univ_elem i R a a'.
Proof.
  assert (Hloc : forall ρ U args A a w', nth_error (rev (gu_params U)) (List.length args) = Some (ce_ass A) ->
             ⟦ A ⟧ env_args ρ args ↘ a -> per_dmod (dm_local ρ U args) w' ->
             exists a' i R, nextparam w' a' /\ per_univ_elem i R a a').
  { intros * Hn Ha Hw.
    destruct (per_dmod_local_inv _ _ _ _ Hw) as (ρ' & U' & args' & -> & Hlt & L1 & L2).
    destruct (per_ltele_next _ _ _ _ _ _ _ _ _ Hlt Hn) as (A' & i & R & Hn' & [a1 a2 Ha1 Ha2 HR]).
    functional_eval_rewrite_clear.
    exists a2, i, R; split; [ eapply np_local; eassumption | exact HR ]. }
  induction 1 as [ρ Δ Φ args A a Hn Ha | ρ Δ E args A a Hn Ha | ρ Δ E args h a Hl HE Hnp IH];
    intros w' Hw.
  - exact (Hloc ρ (gu_mk Δ (md_body Φ)) args A a w' Hn Ha Hw).
  - exact (Hloc ρ (gu_mk Δ (md_alias E)) args A a w' Hn Ha Hw).
  - destruct (per_dmod_alias_sat _ _ _ _ _ Hw Hl) as (ρ' & Δ' & E' & args' & h0 & h' & -> & Hl' & HE0 & HE' & Hhh).
    pose proof (functional_eval_modexp _ _ _ _ HE HE0) as <-.
    destruct (IH _ Hhh) as (a' & i & R & Hnp' & HR).
    exists a', i, R; split; [ eapply np_alias; [ exact Hl' | exact HE' | exact Hnp' ] | exact HR ].
Qed.

Lemma nextparam_functional : forall w a, nextparam w a -> forall a', nextparam w a' -> a = a'.
Proof.
  induction 1 as [ρ Δ Φ args A a Hn Ha | ρ Δ E args A a Hn Ha | ρ Δ E args h a Hl HE Hnp IH];
    intros a' H'; inversion H'; subst;
    try match goal with Hn' : nth_error _ _ = Some _ |- _ => pose proof (nth_error_rev_lt _ _ _ Hn'); lia end.
  - match goal with Hn' : nth_error _ _ = Some _ |- _ => rewrite Hn in Hn'; injection Hn' as <- end.
    eapply functional_eval_exp; eassumption.
  - match goal with Hn' : nth_error _ _ = Some _ |- _ => rewrite Hn in Hn'; injection Hn' as <- end.
    eapply functional_eval_exp; eassumption.
  - match goal with H1 : eval_modexp _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
    apply IH; assumption.
Qed.

Lemma functional_eval_appm : forall h n r1 r2,
    $ᵐ| h & n | gc_ctx ↘ r1 -> $ᵐ| h & n | gc_ctx ↘ r2 -> r1 = r2.
Proof. intros; pose proof (@functional_eval gc_ctx) as Hf; destruct_all; eauto. Qed.

Lemma functional_eval_selmc : forall h ch r1 r2,
    h ·ₘ* ch gc_ctx ↘ r1 -> h ·ₘ* ch gc_ctx ↘ r2 -> r1 = r2.
Proof. intros; pose proof (@functional_eval gc_ctx) as Hf; destruct_all; eauto. Qed.

Lemma functional_eval_selc : forall h ch r1 r2,
    h ·ₜ* ch gc_ctx ↘ r1 -> h ·ₜ* ch gc_ctx ↘ r2 -> r1 = r2.
Proof. intros; pose proof (@functional_eval gc_ctx) as Hf; destruct_all; eauto. Qed.

(** ** Typing Is a Property of the Class of a Module Value *)

Lemma mtyped_per :
    forall w ch k a, mtyped w ch k a -> forall w', per_dmod w w' -> mtyped w' ch k a.
Proof.
  induction 1 as [ w ch k a0 a ρB B i in_rel Hgl Hnp Ha Hty IH
                 | w a i R Hs Ha
                 | ρ Δ Φ args x Φ' pv A M a a0 i R Hl Hx HA Ha
                 | ρ Δ Φ args y Φ' pm Uy ch k a Hl Hy Hm IH
                 | ρ Δ E args h ch k a Hl HE Hm IH
                 | ρ U args ch0 ch k a a1 Hl Hnp1 Hch0 Hk Hty IH ];
    intros w' Hw.
  - destruct (nextparam_rel _ _ Hnp _ Hw) as (a0' & i' & R' & Hnp' & Ha0').
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ Ha Ha0') as (R'' & Ha' & ER).
    eapply mty_pi; [ | exact Hnp' | exact Ha' | ].
    + destruct Hgl as (ρ & U & args & -> & Hlt).
      destruct (per_dmod_local_inv _ _ _ _ Hw) as (ρ' & U' & args' & -> & _ & L1 & L2).
      do 3 eexists; split; [ reflexivity | lia ].
    + intros c w1' b Hc Hw1' Hb.
      assert (Hc' : in_rel c c) by (apply ER, Hc).
      destruct (appm_ex _ _ Hnp c) as [w1 Hw1].
      destruct (appm_rel _ _ _ Hw Hnp _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ Ha)) Hc' Hw1)
        as (w1'' & Hw1'' & Hww).
      pose proof (functional_eval_appm _ _ _ _ Hw1' Hw1'') as <-.
      exact (IH _ _ _ Hc' Hw1 Hb _ Hww).
  - eapply mty_top; [ exact (msat_rel _ Hs _ Hw) | exact Ha ].
  - destruct (per_dmod_body_sat _ _ _ _ _ Hw Hl) as (ρ' & Δ' & Φ'' & args' & -> & Hl' & Hbd).
    destruct (per_body_lookup_def _ _ _ _ _ _ _ _ _ Hbd Hx)
      as (Φ1' & pv' & A' & M' & i0 & R0 & Hx' & [a1 a2 Ha1 Ha2 HR0] & _).
    functional_eval_rewrite_clear.
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ Ha HR0) as (R'' & Ha' & _).
    eapply mty_def; [ exact Hl' | exact Hx' | exact Ha2 | exact Ha' ].
  - destruct (per_dmod_body_sat _ _ _ _ _ Hw Hl) as (ρ' & Δ' & Φ'' & args' & -> & Hl' & Hbd).
    destruct (per_body_lookup_mod _ _ _ _ _ _ _ _ Hbd Hy) as (Φ1' & pm' & Uy' & Hy' & HU).
    eapply mty_sub; [ exact Hl' | exact Hy' | exact (IH _ HU) ].
  - destruct (per_dmod_alias_sat _ _ _ _ _ Hw Hl) as (ρ' & Δ' & E' & args' & h0 & h' & -> & Hl' & HE0 & HE' & Hhh).
    pose proof (functional_eval_modexp _ _ _ _ HE HE0) as <-.
    eapply mty_alias; [ exact Hl' | exact HE' | exact (IH _ Hhh) ].
  - inversion Hw; subst.
    match goal with Hh0 : per_dmod (dm_local ρ U args) ?h' |- _ => rename Hh0 into Hh end.
    destruct (nextparam_rel _ _ Hnp1 _ Hh) as (a1' & _ & _ & Hnp1' & _).
    destruct (per_dmod_local_inv _ _ _ _ Hh) as (ρ' & U' & args' & -> & _ & L1 & L2).
    eapply mty_member; [ lia | exact Hnp1' | exact Hch0 | exact Hk | exact (IH _ Hh) ].
Qed.

(** ** Typing Is a Property of the Class of a Type Value *)

Lemma per_univ_elem_pi_left : forall i E a ρ B a',
    per_univ_elem i E (Πᵈ a ρ B) a' -> exists a1 ρ1 B1, a' = Πᵈ a1 ρ1 B1.
Proof. intros * H; basic_invert_per_univ_elem H; eauto. Qed.

Lemma per_univ_elem_top_left : forall i E a', per_univ_elem i E ⊤ᵈ a' -> a' = ⊤ᵈ.
Proof. intros * H; basic_invert_per_univ_elem H; reflexivity. Qed.

Lemma mtyped_resp : forall w ch k a, mtyped w ch k a -> forall i R a', per_univ_elem i R a a' -> mtyped w ch k a'.
Proof.
  induction 1 as [ w ch k a0 a ρB B i in_rel Hgl Hnp Ha Hty IH
                 | w a i R Hs Ha
                 | ρ Δ Φ args x Φ' pv A M a a0 i R Hl Hx HA Ha
                 | ρ Δ Φ args y Φ' pm Uy ch k a Hl Hy Hm IH
                 | ρ Δ E args h ch k a Hl HE Hm IH
                 | ρ U args ch0 ch k a a1 Hl Hnp1 Hch0 Hk Hty IH ];
    intros i' R' a'' HR.
  - destruct (per_univ_elem_pi_left _ _ _ _ _ _ HR) as (a2 & ρ2 & B2 & ->).
    destruct (per_univ_elem_pi_inv HR) as (in' & out' & Hin' & Hout' & _).
    pose proof (proj1 (per_univ_elem_sym _ _ _ _ Hin')) as Hin2.
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ Hin2 Ha) as (R2 & Ha2 & ER2).
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hin' Ha) as ER1.
    eapply mty_pi; [ exact Hgl | exact Hnp | exact Ha2 |].
    intros c w1 b2 Hc Hw1 Hb2.
    assert (Hc' : in' c c) by (apply ER2, Hc).
    destruct (Hout' _ _ Hc') as [b b2' Hb Hb2' Hbb].
    functional_eval_rewrite_clear.
    eapply IH; [ apply ER1, Hc' | exact Hw1 | exact Hb | exact Hbb ].
  - destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ HR)) Ha) as (R2 & Ha2 & _).
    eapply mty_top; [ exact Hs | exact Ha2 ].
  - destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ HR)) Ha) as (R2 & Ha2 & _).
    eapply mty_def; eassumption.
  - eapply mty_sub; [ eassumption | eassumption | eapply IH; exact HR ].
  - eapply mty_alias; [ eassumption | eassumption | eapply IH; exact HR ].
  - eapply mty_member; [ eassumption | eassumption | eassumption | eassumption | eapply IH; exact HR ].
Qed.

(** ** Selecting Submodules of Related Typed Values *)

Lemma mtyped_selmc_rel :
    forall w chain k a, mtyped w chain k a ->
    forall pre ch, chain = pre ++ ch -> (k = mk_term -> ch <> nil) ->
    forall w', per_dmod w w' ->
    forall v, w ·ₘ* pre gc_ctx ↘ v ->
    exists v', w' ·ₘ* pre gc_ctx ↘ v' /\ per_dmod v v'.
Proof.
  induction 1 as [ w chain k a0 a ρB B i in_rel Hgl Hnp Ha Hty IH
                 | w a i R Hs Ha
                 | ρ Δ Φ args x Φ' pv A M a a0 i R Hl Hx HA Ha
                 | ρ Δ Φ args y Φ' pm Uy chain k a Hl Hy Hm IH
                 | ρ Δ E args h chain k a Hl HE Hm IH
                 | ρ U args ch0 chain k a a1 Hl Hnp1 Hch0 Hk Hty IH ];
    intros pre ch Heq Hch w' Hw v Hv;
    (destruct pre as [| z pre]; [ inversion Hv; subst; exists w'; split; [ constructor | exact Hw ] |]);
    cbn in Heq.
  - destruct Hgl as (ρ & U & args & -> & Hlt).
    destruct (per_dmod_local_inv _ _ _ _ Hw) as (ρ' & U' & args' & -> & _ & L1 & L2).
    rewrite (selmc_unsat _ _ _ _ _ Hlt (cons_neq_nil _ _) Hv).
    eexists; split; [ apply selmc_unsat_ex; [ lia | discriminate ] | constructor; exact Hw ].
  - discriminate.
  - injection Heq as -> Heq; destruct pre; [| discriminate ]; cbn in Heq; subst.
    exfalso; apply Hch; reflexivity.
  - injection Heq as -> Heq.
    inversion Hv; subst.
    match goal with Hs : eval_selm _ _ _ _ |- _ => inversion Hs; subst end; cbn in *; try lia.
    match goal with Hp : gm_prefix_upto Φ _ = Some (gm_ext _ _ (ge_mod _ ?Uy')) |- _ =>
      rewrite Hy in Hp; injection Hp as <- <-; subst end.
    destruct (per_dmod_body_sat _ _ _ _ _ Hw Hl) as (ρ' & Δ' & Φ'' & args' & -> & Hl' & Hbd).
    destruct (per_body_lookup_mod _ _ _ _ _ _ _ _ Hbd Hy) as (Φ1' & pm' & Uy' & Hy' & HU).
    match goal with Hr : eval_selmc _ (dm_of _ _) pre v |- _ =>
      destruct (IH _ _ eq_refl Hch _ HU _ Hr) as (v' & Hv' & Hvv) end.
    exists v'; split; [ econstructor; [ eapply eval_selm_body; [ exact Hl' | exact Hy' ] | exact Hv' ] | exact Hvv ].
  - subst.
    destruct (per_dmod_alias_sat _ _ _ _ _ Hw Hl) as (ρ' & Δ' & E' & args' & h0 & h' & -> & Hl' & HE0 & HE' & Hhh).
    pose proof (functional_eval_modexp _ _ _ _ HE HE0) as <-.
    apply (selmc_alias _ _ _ _ _ _ _ Hl (cons_neq_nil _ _) HE) in Hv.
    destruct (IH (z :: pre) ch eq_refl Hch _ Hhh _ Hv) as (v' & Hv' & Hvv).
    exists v'; split; [ apply (selmc_alias ρ' Δ' E' args' h' (z :: pre) v' Hl' (cons_neq_nil _ _) HE'); exact Hv' | exact Hvv ].
  - rewrite (selmc_member _ _ _ _ Hv).
    inversion Hw; subst.
    eexists; split; [ apply selmc_member_ex | constructor; assumption ].
Qed.

Lemma mtyped_selmc_ex : forall w chain k a, mtyped w chain k a ->
    forall pre ch, chain = pre ++ ch -> (k = mk_term -> ch <> nil) ->
    exists v, w ·ₘ* pre gc_ctx ↘ v.
Proof.
  induction 1 as [ w chain k a0 a ρB B i in_rel Hgl Hnp Ha Hty IH
                 | w a i R Hs Ha
                 | ρ Δ Φ args x Φ' pv A M a a0 i R Hl Hx HA Ha
                 | ρ Δ Φ args y Φ' pm Uy chain k a Hl Hy Hm IH
                 | ρ Δ E args h chain k a Hl HE Hm IH
                 | ρ U args ch0 chain k a a1 Hl Hnp1 Hch0 Hk Hty IH ];
    intros pre ch Heq Hch;
    (destruct pre as [| z pre]; [ eexists; constructor |]); cbn in Heq.
  - destruct Hgl as (ρ & U & args & -> & Hlt).
    eexists; apply selmc_unsat_ex; [ exact Hlt | discriminate ].
  - discriminate.
  - injection Heq as -> Heq; destruct pre; [| discriminate ]; cbn in Heq; subst.
    exfalso; apply Hch; reflexivity.
  - injection Heq as -> Heq.
    destruct (IH _ _ Heq Hch) as [v Hv].
    eexists; econstructor; [ eapply eval_selm_body; eassumption | exact Hv ].
  - destruct (IH (z :: pre) ch Heq Hch) as [v Hv].
    exists v; apply (selmc_alias _ _ _ _ _ _ _ Hl (cons_neq_nil _ _) HE); exact Hv.
  - eexists; apply selmc_member_ex.
Qed.

(** ** The Next Argument, through Members and Saturated Aliases *)

Inductive nextdom : dmod -> domain -> Prop :=
| nd_param : forall w a, nextparam w a -> nextdom w a
| nd_member : forall h ch a, nextdom h a -> nextdom (dm_member h ch) a
| nd_alias : forall ρ Δ E args h a,
    List.length args = List.length Δ ->
    eval_modexp gc_ctx E (env_args ρ args) h -> nextdom h a ->
    nextdom (dm_alias ρ Δ E args) a.

Lemma nextparam_body_sat : forall ρ Δ Φ args a,
    List.length args = List.length Δ -> ~ nextparam (dm_body ρ Δ Φ args) a.
Proof.
  intros * Hl Hn; inversion Hn; subst.
  match goal with Hn' : nth_error _ _ = Some _ |- _ => pose proof (nth_error_rev_lt _ _ _ Hn'); lia end.
Qed.

Lemma nextdom_body_sat : forall ρ Δ Φ args a,
    List.length args = List.length Δ -> ~ nextdom (dm_body ρ Δ Φ args) a.
Proof. intros * Hl Hn; inversion Hn; subst; eapply nextparam_body_sat; eassumption. Qed.

Lemma per_univ_elem_pi_top : forall i R ρ a B, ~ per_univ_elem i R (Πᵈ a ρ B) ⊤ᵈ.
Proof. intros * H; destruct (per_univ_elem_pi_left _ _ _ _ _ _ H) as (? & ? & ? & ?); discriminate. Qed.

(** A typed value at a [Π] that still takes an argument takes it at the
    [Π]'s domain. *)
Lemma mtyped_pi_dom :
    forall w ch k a, mtyped w ch k a ->
    forall a1 ρB B, a = Πᵈ a1 ρB B ->
    forall a0, nextdom w a0 -> exists i R, per_univ_elem i R a1 a0.
Proof.
  induction 1 as [ w ch k a0 a ρB B i in_rel Hgl Hnp Ha Hty IH
                 | w a i R Hs Ha
                 | ρ Δ Φ args x Φ' pv A M a a0 i R Hl Hx HA Ha
                 | ρ Δ Φ args y Φ' pm Uy ch k a Hl Hy Hm IH
                 | ρ Δ E args h ch k a Hl HE Hm IH
                 | ρ U args ch0 ch k a a1 Hl Hnp1 Hch0 Hk Hty IH ];
    intros a1' ρB' B' Heq a0' Hnd.
  - injection Heq as <- <- <-.
    destruct Hgl as (ρ & [Δ [Φ | E]] & args & -> & Hlt); cbn in *;
      inversion Hnd; subst; try lia;
      pose proof (nextparam_functional _ _ Hnp _ ltac:(eassumption)) as <-; eauto.
  - subst; exfalso; eapply per_univ_elem_pi_top; exact Ha.
  - exfalso; eapply nextdom_body_sat; eassumption.
  - exfalso; eapply nextdom_body_sat; eassumption.
  - inversion Hnd; subst.
    + match goal with Hn : nextparam _ _ |- _ => inversion Hn; subst end.
      * match goal with Hn' : nth_error _ _ = Some _ |- _ => pose proof (nth_error_rev_lt _ _ _ Hn'); lia end.
      * match goal with H1 : eval_modexp _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
        eapply IH; [ reflexivity | apply nd_param; eassumption ].
    + match goal with H1 : eval_modexp _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
      eapply IH; [ reflexivity | eassumption ].
  - inversion Hnd; subst;
      [ match goal with Hn : nextparam _ _ |- _ => inversion Hn end | eapply IH; [ reflexivity | eassumption ] ].
Qed.

Lemma mtyped_nil_mod : forall w ch k a, mtyped w ch k a -> ch = nil -> k = mk_mod ->
    (msat w /\ exists i R, per_univ_elem i R a ⊤ᵈ) \/ (exists a0, nextdom w a0).
Proof.
  induction 1 as [ w ch k a0 a ρB B i in_rel Hgl Hnp Ha Hty IH
                 | w a i R Hs Ha
                 | ρ Δ Φ args x Φ' pv A M a a0 i R Hl Hx HA Ha
                 | ρ Δ Φ args y Φ' pm Uy ch k a Hl Hy Hm IH
                 | ρ Δ E args h ch k a Hl HE Hm IH
                 | ρ U args ch0 ch k a a1 Hl Hnp1 Hch0 Hk Hty IH ];
    intros Hc Hk'; try discriminate.
  - right; exists a0; apply nd_param; exact Hnp.
  - left; split; [ exact Hs | eauto ].
  - destruct (IH Hc Hk') as [[Hs Ht] | [a0 Hn]].
    + left; split; [ econstructor; eassumption | exact Ht ].
    + right; exists a0; econstructor; eassumption.
  - right; exists a1; apply nd_member, nd_param; exact Hnp1.
Qed.

(** An arity at a [Π] belongs to a value that takes an argument at its domain. *)
Lemma mtyped_arity_pi :
    forall w a, mtyped w nil mk_mod a ->
    forall i R b ρ C, per_univ_elem i R a (Πᵈ b ρ C) ->
    exists a0 j R0, nextdom w a0 /\ per_univ_elem j R0 b a0.
Proof.
  intros * Hm * HR.
  destruct (mtyped_nil_mod _ _ _ _ Hm eq_refl eq_refl) as [[_ (i' & R' & Ht)] | [a0 Hn]].
  - exfalso.
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ Ht)) HR) as (R2 & H2 & _).
    pose proof (per_univ_elem_top_left _ _ _ H2); discriminate.
  - pose proof (mtyped_resp _ _ _ _ Hm _ _ _ HR) as Hm'.
    destruct (mtyped_pi_dom _ _ _ _ Hm' _ _ _ eq_refl _ Hn) as (j & R0 & H0).
    exists a0, j, R0; split; assumption.
Qed.

Lemma mtyped_member_inv : forall h ch0 ch k a, mtyped (dm_member h ch0) ch k a ->
    exists ρ U args a1, h = dm_local ρ U args /\ List.length args < List.length (gu_params U) /\
      nextparam h a1 /\ ch0 <> nil /\ (k = mk_term -> ch <> nil) /\ mtyped h (ch0 ++ ch) k a.
Proof.
  intros * H; inversion H; subst.
  - match goal with Hg : exists _ _ _, _ |- _ => destruct Hg as (ρ & [? []] & ? & ? & _); discriminate end.
  - match goal with Hs : msat _ |- _ => inversion Hs end.
  - do 4 eexists; repeat split; eauto.
Qed.

Lemma mtyped_alias_sat_inv : forall ρ Δ E args ch k a h,
    mtyped (dm_alias ρ Δ E args) ch k a ->
    List.length args = List.length Δ -> ⟦ E ⟧ᵐ gc_ctx ⍮ env_args ρ args ↘ h ->
    mtyped h ch k a.
Proof.
  intros * H Hl HE; inversion H; subst.
  - match goal with Hg : exists _ _ _, _ |- _ => destruct Hg as (ρ0 & [Δ0 [Φ0 | E0]] & args0 & Heq & Hlt) end;
      cbn in Heq; [ discriminate |].
    injection Heq as <- <- <- <-; cbn in Hlt; lia.
  - match goal with Hs : msat _ |- _ => inversion Hs; subst end.
    match goal with H1 : eval_modexp _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
    match goal with Hs : msat h |- _ => eapply mty_top; eassumption end.
  - match goal with H1 : eval_modexp _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
    assumption.
Qed.

Lemma mtyped_app_nd :
    forall w a0, nextdom w a0 ->
    forall ch k a1 ρB B, mtyped w ch k (Πᵈ a1 ρB B) ->
    forall i' Ein c w1 b, per_univ_elem i' Ein a1 a1 -> Ein c c ->
    $ᵐ| w & c | gc_ctx ↘ w1 -> ⟦ B ⟧ ρB ↦ c ↘ b -> mtyped w1 ch k b.
Proof.
  induction 1 as [w a Hn | h ch0 a Hn IH | ρ Δ E args h a Hl HE Hn IH];
    intros * Hm * Ha Hc Hw1 Hb.
  - eapply mtyped_app; [ exact Hm | reflexivity | left; eauto | eassumption .. ].
  - eapply mtyped_app; [ exact Hm | reflexivity | right; eauto | eassumption .. ].
  - pose proof (mtyped_alias_sat_inv _ _ _ _ _ _ _ _ Hm Hl HE) as Hm'.
    inversion Hw1; subst; try lia.
    match goal with H1 : eval_modexp _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
    eapply IH; eassumption.
Qed.

(** Related typed values, applied to related arguments of their next
    parameter, give related results. *)
Lemma appm_rel_typed :
    forall w a0, nextdom w a0 ->
    forall ch k a1 ρB B, mtyped w ch k (Πᵈ a1 ρB B) ->
    forall i Ein, per_univ_elem i Ein a1 a1 ->
    (forall c, Ein c c -> exists b, ⟦ B ⟧ ρB ↦ c ↘ b) ->
    forall w', per_dmod w w' -> forall c c', Ein c c' ->
    exists w1 w1', $ᵐ| w & c | gc_ctx ↘ w1 /\ $ᵐ| w' & c' | gc_ctx ↘ w1' /\ per_dmod w1 w1'.
Proof.
  induction 1 as [w a Hn | h ch0 a Hn IH | ρ Δ E args h a Hl HE Hn IH];
    intros * Hm * Ha HB w' Hw c c' Hc.
  - destruct (mtyped_pi_dom _ _ _ _ Hm _ _ _ eq_refl _ (nd_param _ _ Hn)) as (j & R0 & H0).
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ H0 Ha) as E0.
    destruct (appm_ex _ _ Hn c) as [w1 Hw1].
    destruct (appm_rel _ _ _ Hw Hn _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ H0)) (proj2 (E0 _ _) Hc) Hw1)
      as (w1' & Hw1' & Hww).
    exists w1, w1'; auto.
  - destruct (mtyped_member_inv _ _ _ _ _ Hm) as (ρ & U & args & a2 & -> & Hlt & Hnp & Hch0 & Hk & Hm').
    inversion Hw; subst.
    match goal with Hh : per_dmod (dm_local ρ U args) ?h' |- _ => rename Hh into Hhh end.
    destruct (IH _ _ _ _ _ Hm' _ _ Ha HB _ Hhh _ _ Hc) as (h1 & h1' & Hh1 & Hh1' & Hh11).
    assert (HPE : PER Ein) by (eapply per_elem_PER; exact Ha).
    assert (Hcc : Ein c c) by (etransitivity; [ exact Hc | symmetry; exact Hc ]).
    destruct (HB _ Hcc) as [b Hb].
    pose proof (mtyped_app_nd _ _ Hn _ _ _ _ _ Hm' _ _ _ _ _ Ha Hcc Hh1 Hb) as Hm1.
    destruct (mtyped_selmc_ex _ _ _ _ Hm1 ch0 _ eq_refl Hk) as [r Hr].
    destruct (mtyped_selmc_rel _ _ _ _ Hm1 ch0 _ eq_refl Hk _ Hh11 _ Hr) as (r' & Hr' & Hrr).
    exists r, r'; split; [ econstructor; eassumption |]; split; [ econstructor; eassumption | exact Hrr ].
  - pose proof (mtyped_alias_sat_inv _ _ _ _ _ _ _ _ Hm Hl HE) as Hm'.
    destruct (per_dmod_alias_sat _ _ _ _ _ Hw Hl) as (ρ' & Δ' & E' & args' & h0 & h' & -> & Hl' & HE0 & HE' & Hhh).
    pose proof (functional_eval_modexp _ _ _ _ HE HE0) as <-.
    destruct (IH _ _ _ _ _ Hm' _ _ Ha HB _ Hhh _ _ Hc) as (h1 & h1' & Hh1 & Hh1' & Hh11).
    exists h1, h1'; split; [ eapply eval_appm_alias; eassumption |]; split; [ eapply eval_appm_alias; eassumption | exact Hh11 ].
Qed.

End Fixed_GCtx.
