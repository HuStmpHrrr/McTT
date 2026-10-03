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
Import Domain_Notations Fixed_Notations.
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

Lemma per_dmod_local_inv : forall ρ U args w',
    per_dmod (dm_local ρ U args) w' ->
    exists ρ' U' args', w' = dm_local ρ' U' args' /\
      per_ltele (rev (gu_params U)) ρ (gu_def U) (rev (gu_params U')) ρ' (gu_def U') args args' /\
      List.length (gu_params U) = List.length (gu_params U') /\ List.length args = List.length args'.
Proof.
  intros * H; inversion H; subst.
  match goal with Hl : per_ltele _ _ _ _ _ _ _ _ |- _ =>
    destruct (per_ltele_lengths _ _ _ _ _ _ _ _ Hl) as [H1 H2]; rewrite !length_rev in H1 end.
  do 3 eexists; split; [ reflexivity |]; eauto.
Qed.

Lemma msat_rel : forall w, msat w -> forall w', per_dmod w w' -> msat w'.
Proof.
  induction 1 as [ρ Δ Φ args Hl | ρ Δ E args h Hl HE Hs IH | p T args Hm Hl]; intros w' Hw.
  - destruct (per_dmod_local_inv _ _ _ _ Hw) as (ρ' & [Δ' D'] & args' & -> & Hlt & L1 & L2).
    cbn [gu_params gu_def] in *.
    pose proof (per_ltele_full _ _ _ _ _ _ _ _ Hlt ltac:(rewrite length_rev; exact Hl)) as Hd.
    inversion Hd; subst; constructor; lia.
  - destruct (per_dmod_local_inv _ _ _ _ Hw) as (ρ' & [Δ' D'] & args' & -> & Hlt & L1 & L2).
    cbn [gu_params gu_def] in *.
    pose proof (per_ltele_full _ _ _ _ _ _ _ _ Hlt ltac:(rewrite length_rev; exact Hl)) as Hd.
    inversion Hd; subst.
    match goal with H1' : eval_modexp _ _ E _ ?h1, H3 : eval_modexp _ _ ?E' _ ?h', H5 : per_dmod ?h1 ?h' |- _ =>
      pose proof (functional_eval_modexp _ _ _ _ HE H1') as <-;
      econstructor; [ lia | exact H3 | exact (IH _ H5) ] end.
  - inversion Hw; subst.
    match goal with Hg : per_gargs _ _ _ args _ |- _ => destruct (per_gargs_lengths _ _ _ _ _ Hg) as [? _] end.
    econstructor; [ exact Hm | lia ].
Qed.

Lemma nextparam_rel : gparam_ok -> forall w a, nextparam w a -> forall w', per_dmod w w' ->
    exists a' i R, nextparam w' a' /\ per_univ_elem i R a a'.
Proof.
  intros HGp; induction 1 as [ρ U args A a Hn Ha | ρ Δ E args h a Hl HE Hnp IH | p T args A a Hm Hn Ha];
    intros w' Hw.
  - destruct (per_dmod_local_inv _ _ _ _ Hw) as (ρ' & U' & args' & -> & Hlt & L1 & L2).
    destruct (per_ltele_next _ _ _ _ _ _ _ _ _ Hlt Hn) as (A' & i & R & Hn' & [a1 a2 Ha1 Ha2 HR]).
    functional_eval_rewrite_clear.
    exists a2, i, R; split; [ econstructor; eassumption | exact HR ].
  - destruct (per_dmod_local_inv _ _ _ _ Hw) as (ρ' & [Δ' D'] & args' & -> & Hlt & L1 & L2).
    cbn [gu_params gu_def] in *.
    pose proof (per_ltele_full _ _ _ _ _ _ _ _ Hlt ltac:(rewrite length_rev; exact Hl)) as Hd.
    inversion Hd; subst.
    match goal with H1' : eval_modexp _ _ E _ ?h1, H3 : eval_modexp _ _ ?E' _ ?h', H5 : per_dmod ?h1 ?h' |- _ =>
      pose proof (functional_eval_modexp _ _ _ _ HE H1') as <-;
      destruct (IH _ H5) as (a' & i & R & Hnp' & HR);
      exists a', i, R; split; [ eapply np_alias; [ lia | exact H3 | exact Hnp' ] | exact HR ] end.
  - inversion Hw; subst.
    match goal with Hm' : gc_module _ _ p = Some (mr_body ?T') |- _ => rewrite Hm in Hm'; injection Hm' as <- end.
    match goal with Hg : per_gargs _ _ _ args _ |- _ => rename Hg into Hga end.
    destruct (HGp _ _ _ _ _ Hm Hga Hn) as (i & R & [a1 a2 Ha1 Ha2 HR]).
    destruct (per_gargs_lengths _ _ _ _ _ Hga) as [Hl _].
    functional_eval_rewrite_clear.
    exists a2, i, R; split; [ econstructor; [ exact Hm | rewrite <- Hl; exact Hn | exact Ha2 ] | exact HR ].
Qed.

Lemma nextparam_functional : forall w a, nextparam w a -> forall a', nextparam w a' -> a = a'.
Proof.
  induction 1 as [ρ U args A a Hn Ha | ρ Δ E args h a Hl HE Hnp IH | p T args A a Hm Hn Ha];
    intros a' H'; inversion H'; subst.
  - match goal with Hn' : nth_error _ _ = Some _ |- _ => rewrite Hn in Hn'; injection Hn' as <- end.
    eapply functional_eval_exp; eassumption.
  - cbn in Hn. assert (Hn' : nth_error (rev Δ) (List.length args) <> None) by congruence.
    apply nth_error_Some in Hn'; rewrite length_rev in Hn'; lia.
  - match goal with Hn' : nth_error _ _ = Some _ |- _ => cbn in Hn';
      assert (Hn'' : nth_error (rev Δ) (List.length args) <> None) by congruence end.
    apply nth_error_Some in Hn''; rewrite length_rev in Hn''; lia.
  - match goal with H1 : eval_modexp _ _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
    apply IH; assumption.
  - match goal with Hm' : gc_module _ _ p = Some (mr_body ?T') |- _ => rewrite Hm in Hm'; injection Hm' as <- end.
    match goal with Hn' : nth_error _ _ = Some _ |- _ => rewrite Hn in Hn'; injection Hn' as <- end.
    eapply functional_eval_exp; eassumption.
Qed.

Lemma functional_eval_appm : forall h n r1 r2,
    eval_appm gc_deps gc_stack h n r1 -> eval_appm gc_deps gc_stack h n r2 -> r1 = r2.
Proof. intros; pose proof (@functional_eval gc_deps gc_stack) as Hf; destruct_all; eauto. Qed.

Lemma functional_eval_selmc : forall h ch r1 r2,
    eval_selmc gc_deps gc_stack h ch r1 -> eval_selmc gc_deps gc_stack h ch r2 -> r1 = r2.
Proof. intros; pose proof (@functional_eval gc_deps gc_stack) as Hf; destruct_all; eauto. Qed.

Lemma functional_eval_selc : forall h ch r1 r2,
    eval_selc gc_deps gc_stack h ch r1 -> eval_selc gc_deps gc_stack h ch r2 -> r1 = r2.
Proof. intros; pose proof (@functional_eval gc_deps gc_stack) as Hf; destruct_all; eauto. Qed.

(** ** Typing Is a Property of the Class of a Module Value *)

Lemma mtyped_per : gparam_ok -> gchild_ok -> galias_ok ->
    forall w ch k a, mtyped w ch k a -> forall w', per_dmod w w' -> mtyped w' ch k a.
Proof.
  intros HGp HGc HGa.
  induction 1 as [ w ch k a0 a ρB B i in_rel Hgl Hnp Ha Hty IH
                 | w a i R Hs Ha
                 | ρ Δ Φ args x Φ' b pv A M ρ1 a a0 i R Hl Hx Hb HA Ha
                 | ρ Δ Φ args y Φ' Uy ρ1 ch k a Hl Hy Hb Hm IH
                 | ρ Δ E args h ch k a Hl HE Hm IH
                 | p T args x b A0 B f aA j E a a0 i R Hm Hl Hr Hf HaA HE Hff Ha0 Ha
                 | p args y T ch k a Hm Hty IH
                 | p args y U ch ch' k a Hm Hk Hty IH
                 | ρ U args ch0 ch k a a1 Hl Hnp1 Hch0 Hk Hty IH ];
    intros w' Hw.
  - destruct (nextparam_rel HGp _ _ Hnp _ Hw) as (a0' & i' & R' & Hnp' & Ha0').
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ Ha Ha0') as (R'' & Ha' & ER).
    eapply mty_pi; [ | exact Hnp' | exact Ha' | ].
    + destruct Hgl as [(ρ & U & args & -> & Hlt) | (p & args & -> & -> & ->)].
      * destruct (per_dmod_local_inv _ _ _ _ Hw) as (ρ' & U' & args' & -> & _ & L1 & L2).
        left; do 3 eexists; split; [ reflexivity | lia ].
      * inversion Hw; subst; right; do 2 eexists; split; [ reflexivity | auto ].
    + intros c w1' b Hc Hw1' Hb.
      assert (Hc' : in_rel c c) by (apply ER, Hc).
      destruct (appm_ex _ _ Hnp c) as [w1 Hw1].
      destruct (appm_rel HGp _ _ _ Hw Hnp _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ Ha)) Hc' Hw1)
        as (w1'' & Hw1'' & Hww).
      pose proof (functional_eval_appm _ _ _ _ Hw1' Hw1'') as <-.
      exact (IH _ _ _ Hc' Hw1 Hb _ Hww).
  - eapply mty_top; [ exact (msat_rel _ Hs _ Hw) | exact Ha ].
  - destruct (per_dmod_local_inv _ _ _ _ Hw) as (ρ' & [Δ' D'] & args' & -> & Hlt & L1 & L2).
    cbn [gu_params gu_def] in *.
    pose proof (per_ltele_full _ _ _ _ _ _ _ _ Hlt ltac:(rewrite length_rev; exact Hl)) as Hd.
    inversion Hd; subst.
    match goal with Hb0 : per_body _ _ _ _ |- _ => rename Hb0 into Hbd end.
    destruct (per_body_lookup_def _ _ _ _ _ _ _ _ _ _ Hbd Hx)
      as (Φ1' & b' & pv' & A' & M' & ρ1x & ρ1' & i0 & R0 & Hx' & Hb1 & Hb1' & [a1 a2 Ha1 Ha2 HR0] & _).
    pose proof (functional_eval_benv _ _ _ _ Hb Hb1) as <-.
    functional_eval_rewrite_clear.
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ Ha HR0) as (R'' & Ha' & _).
    eapply mty_def; [ lia | exact Hx' | exact Hb1' | exact Ha2 | exact Ha' ].
  - destruct (per_dmod_local_inv _ _ _ _ Hw) as (ρ' & [Δ' D'] & args' & -> & Hlt & L1 & L2).
    cbn [gu_params gu_def] in *.
    pose proof (per_ltele_full _ _ _ _ _ _ _ _ Hlt ltac:(rewrite length_rev; exact Hl)) as Hd.
    inversion Hd; subst.
    match goal with Hb0 : per_body _ _ _ _ |- _ => rename Hb0 into Hbd end.
    destruct (per_body_lookup_mod _ _ _ _ _ _ _ Hbd Hy) as (Φ1' & Uy' & ρ1x & ρ1' & Hy' & Hb1 & Hb1' & HU).
    pose proof (functional_eval_benv _ _ _ _ Hb Hb1) as <-.
    eapply mty_sub; [ lia | exact Hy' | exact Hb1' | exact (IH _ HU) ].
  - destruct (per_dmod_local_inv _ _ _ _ Hw) as (ρ' & [Δ' D'] & args' & -> & Hlt & L1 & L2).
    cbn [gu_params gu_def] in *.
    pose proof (per_ltele_full _ _ _ _ _ _ _ _ Hlt ltac:(rewrite length_rev; exact Hl)) as Hd.
    inversion Hd; subst.
    match goal with H1' : eval_modexp _ _ E _ ?h1, H3 : eval_modexp _ _ ?E' _ ?h', H5 : per_dmod ?h1 ?h' |- _ =>
      pose proof (functional_eval_modexp _ _ _ _ HE H1') as <-;
      eapply mty_alias; [ lia | exact H3 | exact (IH _ H5) ] end.
  - inversion Hw; subst.
    match goal with Hm' : gc_module _ _ p = Some (mr_body ?T') |- _ => rewrite Hm in Hm'; injection Hm' as <- end.
    match goal with Hg0 : per_gargs _ _ _ args _ |- _ => rename Hg0 into Hg end.
    pose proof HaA as HaA'; rewrite <- (rev_involutive T) in HaA'.
    destruct (apps_rel_gargs _ _ _ _ _ _ _ _ _ _ _ _ Hg HaA' HaA' HE Hff)
      as (v & v' & b1 & b1' & R1 & _ & _ & Hb1 & Hb1' & HR1 & _).
    destruct (per_gargs_lengths _ _ _ _ _ Hg) as [Hla Hlt]; rewrite length_rev in Hlt.
    rewrite skipn_rev, rev_involutive in Hb1, Hb1'.
    rewrite Hla in Hb1'.
    functional_eval_rewrite_clear.
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ Ha HR1) as (R'' & Ha' & _).
    eapply mty_gdef; [ exact Hm | lia | exact Hr | exact Hf | exact HaA | exact HE | exact Hff | exact Hb1' | exact Ha' ].
  - inversion Hw; subst.
    match goal with Hm0 : gc_module _ _ p = Some (mr_body ?Tp) |- _ => rename Hm0 into Hmp end.
    match goal with Hg0 : per_gargs _ _ _ args _ |- _ => rename Hg0 into Hg end.
    destruct (HGc _ _ _ _ Hmp Hm) as [Δ ->].
    assert (Hw2 : per_dmod (dm_global (path_app p (y :: nil)) args) (dm_global (path_app p (y :: nil)) args'))
      by (econstructor; [ exact Hm | rewrite rev_app_distr; apply per_gargs_app; exact Hg ]).
    eapply mty_gsub; [ exact Hm | exact (IH _ Hw2) ].
  - inversion Hw; subst.
    match goal with Hm0 : gc_module _ _ p = Some (mr_body ?Tp) |- _ => rename Hm0 into Hmp end.
    match goal with Hg0 : per_gargs _ _ _ args _ |- _ => rename Hg0 into Hg end.
    pose proof (HGa _ _ _ _ _ _ _ Hmp Hm Hg) as Hw2.
    eapply mty_galias; [ exact Hm | exact Hk | exact (IH _ Hw2) ].
  - inversion Hw; subst.
    match goal with Hh0 : per_dmod (dm_local ρ U args) ?h' |- _ => rename Hh0 into Hh end.
    destruct (nextparam_rel HGp _ _ Hnp1 _ Hh) as (a1' & _ & _ & Hnp1' & _).
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
                 | ρ Δ Φ args x Φ' b pv A M ρ1 a a0 i R Hl Hx Hb HA Ha
                 | ρ Δ Φ args y Φ' Uy ρ1 ch k a Hl Hy Hb Hm IH
                 | ρ Δ E args h ch k a Hl HE Hm IH
                 | p T args x b A0 B f aA j E a a0 i R Hm Hl Hr Hf HaA HE Hff Ha0 Ha
                 | p args y T ch k a Hm Hty IH
                 | p args y U ch ch' k a Hm Hk Hty IH
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
  - eapply mty_sub; [ eassumption | eassumption | eassumption | eapply IH; exact HR ].
  - eapply mty_alias; [ eassumption | eassumption | eapply IH; exact HR ].
  - destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ HR)) Ha) as (R2 & Ha2 & _).
    eapply mty_gdef; eassumption.
  - eapply mty_gsub; [ eassumption | eapply IH; exact HR ].
  - eapply mty_galias; [ eassumption | eassumption | eapply IH; exact HR ].
  - eapply mty_member; [ eassumption | eassumption | eassumption | eassumption | eapply IH; exact HR ].
Qed.

(** ** Selecting Submodules of Related Typed Values *)

Lemma mtyped_selmc_rel : gchild_ok -> galias_ok ->
    forall w chain k a, mtyped w chain k a ->
    forall pre ch, chain = pre ++ ch -> (k = mk_term -> ch <> nil) ->
    forall w', per_dmod w w' ->
    forall v, eval_selmc gc_deps gc_stack w pre v ->
    exists v', eval_selmc gc_deps gc_stack w' pre v' /\ per_dmod v v'.
Proof.
  intros HGc HGa.
  induction 1 as [ w chain k a0 a ρB B i in_rel Hgl Hnp Ha Hty IH
                 | w a i R Hs Ha
                 | ρ Δ Φ args x Φ' b pv A M ρ1 a a0 i R Hl Hx Hb HA Ha
                 | ρ Δ Φ args y Φ' Uy ρ1 chain k a Hl Hy Hb Hm IH
                 | ρ Δ E args h chain k a Hl HE Hm IH
                 | p T args x b A0 B f aA j E a a0 i R Hm Hl Hr Hf HaA HE Hff Ha0 Ha
                 | p args y T chain k a Hm Hty IH
                 | p args y U ch0 ch' k a Hm Hk Hty IH
                 | ρ U args ch0 chain k a a1 Hl Hnp1 Hch0 Hk Hty IH ];
    intros pre ch Heq Hch w' Hw v Hv;
    (destruct pre as [| z pre]; [ inversion Hv; subst; exists w'; split; [ constructor | exact Hw ] |]);
    cbn in Heq.
  - destruct Hgl as [(ρ & U & args & -> & Hlt) | (p & args & -> & Hc & ->)]; [| subst; discriminate ].
    destruct (per_dmod_local_inv _ _ _ _ Hw) as (ρ' & U' & args' & -> & _ & L1 & L2).
    rewrite (selmc_unsat _ _ _ _ _ Hlt (cons_neq_nil _ _) Hv).
    eexists; split; [ apply selmc_unsat_ex; [ lia | discriminate ] | constructor; exact Hw ].
  - discriminate.
  - injection Heq as -> Heq; destruct pre; [| discriminate ]; cbn in Heq; subst.
    exfalso; apply Hch; reflexivity.
  - injection Heq as -> Heq.
    inversion Hv; subst.
    match goal with Hs : eval_selm _ _ _ _ _ |- _ => inversion Hs; subst end; cbn in *; try lia.
    match goal with Hp : gm_prefix_upto Φ _ = Some (gm_ext _ _ (ge_mod ?Uy')) |- _ =>
      rewrite Hy in Hp; injection Hp as <- <- end.
    match goal with Hb' : eval_benv _ _ _ Φ' ?ρ1' |- _ => pose proof (functional_eval_benv _ _ _ _ Hb Hb') as <- end.
    destruct (per_dmod_local_inv _ _ _ _ Hw) as (ρ' & [Δ' D'] & args' & -> & Hlt & L1 & L2).
    cbn [gu_params gu_def] in *.
    pose proof (per_ltele_full _ _ _ _ _ _ _ _ Hlt ltac:(rewrite length_rev; exact Hl)) as Hd.
    inversion Hd; subst.
    match goal with Hb0 : per_body _ _ _ _ |- _ => rename Hb0 into Hbd end.
    destruct (per_body_lookup_mod _ _ _ _ _ _ _ Hbd Hy) as (Φ1' & Uy' & ρ1x & ρ1' & Hy' & Hb1 & Hb1' & HU).
    pose proof (functional_eval_benv _ _ _ _ Hb Hb1) as <-.
    match goal with Hr : eval_selmc _ _ (dm_local ρ1 Uy nil) pre v |- _ =>
      destruct (IH _ _ eq_refl Hch _ HU _ Hr) as (v' & Hv' & Hvv) end.
    exists v'; split; [ econstructor; [ eapply eval_selm_body; [ lia | exact Hy' | exact Hb1' ] | exact Hv' ] | exact Hvv ].
  - subst.
    destruct (per_dmod_local_inv _ _ _ _ Hw) as (ρ' & [Δ' D'] & args' & -> & Hlt & L1 & L2).
    cbn [gu_params gu_def] in *.
    pose proof (per_ltele_full _ _ _ _ _ _ _ _ Hlt ltac:(rewrite length_rev; exact Hl)) as Hd.
    inversion Hd; subst.
    match goal with H1' : eval_modexp _ _ E _ ?h1, H3 : eval_modexp _ _ ?E' _ ?h', H5 : per_dmod ?h1 ?h' |- _ =>
      pose proof (functional_eval_modexp _ _ _ _ HE H1') as <-; rename H3 into HE', H5 into Hhh end.
    apply (selmc_alias _ _ _ _ _ _ _ Hl (cons_neq_nil _ _) HE) in Hv.
    destruct (IH (z :: pre) ch eq_refl Hch _ Hhh _ Hv) as (v' & Hv' & Hvv).
    exists v'; split; [ apply (selmc_alias ρ' Δ' E' args' h' (z :: pre) v' ltac:(lia) (cons_neq_nil _ _) HE'); exact Hv' | exact Hvv ].
  - injection Heq as -> Heq; destruct pre; [| discriminate ]; cbn in Heq; subst.
    exfalso; apply Hch; reflexivity.
  - injection Heq as -> Heq.
    inversion Hv; subst.
    match goal with Hs : eval_selm _ _ _ _ _ |- _ => inversion Hs; subst end;
      [| match goal with Hm' : gc_module _ _ _ = Some (mr_alias _ _) |- _ => rewrite Hm in Hm'; discriminate end ].
    inversion Hw; subst.
    match goal with Hm0 : gc_module _ _ p = Some (mr_body ?Tp) |- _ => rename Hm0 into Hmp end.
    match goal with Hg0 : per_gargs _ _ _ args _ |- _ => rename Hg0 into Hg end.
    destruct (HGc _ _ _ _ Hmp Hm) as [Δ ->].
    assert (Hw2 : per_dmod (dm_global (path_app p (z :: nil)) args) (dm_global (path_app p (z :: nil)) args'))
      by (econstructor; [ exact Hm | rewrite rev_app_distr; apply per_gargs_app; exact Hg ]).
    match goal with Hr : eval_selmc _ _ (dm_global _ args) pre v |- _ =>
      destruct (IH _ _ eq_refl Hch _ Hw2 _ Hr) as (v' & Hv' & Hvv) end.
    exists v'; split; [ econstructor; [ apply eval_selm_global; intros; rewrite Hm; discriminate | exact Hv' ] | exact Hvv ].
  - injection Heq as -> Heq.
    inversion Hv; subst.
    match goal with Hs : eval_selm _ _ _ _ _ |- _ => inversion Hs; subst end;
      [ match goal with Hm' : forall U r, gc_module _ _ _ <> Some (mr_alias U r) |- _ => exfalso; eapply Hm'; exact Hm end |].
    match goal with Hm' : gc_module _ _ _ = Some (mr_alias ?U' ?ch1) |- _ => rewrite Hm in Hm'; injection Hm' as <- <- end.
    inversion Hw; subst.
    match goal with Hm0 : gc_module _ _ p = Some (mr_body ?Tp) |- _ => rename Hm0 into Hmp end.
    match goal with Hg0 : per_gargs _ _ _ args _ |- _ => rename Hg0 into Hg end.
    pose proof (HGa _ _ _ _ _ _ _ Hmp Hm Hg) as Hw2.
    match goal with H1 : eval_selmc _ _ (dm_local nil U args) ch0 ?h1, H2 : eval_selmc _ _ ?h1 pre v |- _ =>
      assert (Hv2 : eval_selmc gc_deps gc_stack (dm_local nil U args) (ch0 ++ pre) v)
        by (apply eval_selmc_app; eexists; split; eassumption) end.
    destruct (IH (ch0 ++ pre) ch ltac:(rewrite app_assoc; reflexivity) Hch _ Hw2 _ Hv2) as (v' & Hv' & Hvv).
    apply eval_selmc_app in Hv' as (h1' & Hh1' & Hv').
    exists v'; split; [ econstructor; [ eapply eval_selm_global_alias; eassumption | exact Hv' ] | exact Hvv ].
  - rewrite (selmc_member _ _ _ _ Hv).
    inversion Hw; subst.
    eexists; split; [ apply selmc_member_ex | constructor; assumption ].
Qed.

Lemma mtyped_selmc_ex : forall w chain k a, mtyped w chain k a ->
    forall pre ch, chain = pre ++ ch -> (k = mk_term -> ch <> nil) ->
    exists v, eval_selmc gc_deps gc_stack w pre v.
Proof.
  induction 1 as [ w chain k a0 a ρB B i in_rel Hgl Hnp Ha Hty IH
                 | w a i R Hs Ha
                 | ρ Δ Φ args x Φ' b pv A M ρ1 a a0 i R Hl Hx Hb HA Ha
                 | ρ Δ Φ args y Φ' Uy ρ1 chain k a Hl Hy Hb Hm IH
                 | ρ Δ E args h chain k a Hl HE Hm IH
                 | p T args x b A0 B f aA j E a a0 i R Hm Hl Hr Hf HaA HE Hff Ha0 Ha
                 | p args y T chain k a Hm Hty IH
                 | p args y U ch0 ch' k a Hm Hk Hty IH
                 | ρ U args ch0 chain k a a1 Hl Hnp1 Hch0 Hk Hty IH ];
    intros pre ch Heq Hch;
    (destruct pre as [| z pre]; [ eexists; constructor |]); cbn in Heq.
  - destruct Hgl as [(ρ & U & args & -> & Hlt) | (p & args & -> & Hc & ->)]; [| subst; discriminate ].
    eexists; apply selmc_unsat_ex; [ exact Hlt | discriminate ].
  - discriminate.
  - injection Heq as -> Heq; destruct pre; [| discriminate ]; cbn in Heq; subst.
    exfalso; apply Hch; reflexivity.
  - injection Heq as -> Heq.
    destruct (IH _ _ Heq Hch) as [v Hv].
    eexists; econstructor; [ eapply eval_selm_body; eassumption | exact Hv ].
  - destruct (IH (z :: pre) ch Heq Hch) as [v Hv].
    exists v; apply (selmc_alias _ _ _ _ _ _ _ Hl (cons_neq_nil _ _) HE); exact Hv.
  - injection Heq as -> Heq; destruct pre; [| discriminate ]; cbn in Heq; subst.
    exfalso; apply Hch; reflexivity.
  - injection Heq as -> Heq.
    destruct (IH _ _ Heq Hch) as [v Hv].
    eexists; econstructor; [ apply eval_selm_global; intros; rewrite Hm; discriminate | exact Hv ].
  - injection Heq as -> Heq.
    destruct (IH (ch0 ++ pre) ch ltac:(rewrite Heq, app_assoc; reflexivity) Hch) as [v Hv].
    apply eval_selmc_app in Hv as (h1 & Hh1 & Hv).
    eexists; econstructor; [ eapply eval_selm_global_alias; eassumption | exact Hv ].
  - eexists; apply selmc_member_ex.
Qed.

(** ** The Next Argument, through Members and Saturated Aliases *)

Inductive nextdom : dmod -> domain -> Prop :=
| nd_param : forall w a, nextparam w a -> nextdom w a
| nd_member : forall h ch a, nextdom h a -> nextdom (dm_member h ch) a
| nd_alias : forall ρ Δ E args h a,
    List.length args = List.length Δ ->
    eval_modexp gc_deps gc_stack E (env_args ρ args) h -> nextdom h a ->
    nextdom (dm_local ρ (gu_mk Δ (md_alias E)) args) a.

Lemma nextparam_body_sat : forall ρ Δ Φ args a,
    List.length args = List.length Δ -> ~ nextparam (dm_local ρ (gu_body Δ Φ) args) a.
Proof.
  intros * Hl Hn; inversion Hn; subst; cbn in *.
  match goal with Hn' : nth_error _ _ = Some _ |- _ =>
    assert (Hn'' : nth_error (rev Δ) (List.length args) <> None) by congruence end.
  apply nth_error_Some in Hn''; rewrite length_rev in Hn''; lia.
Qed.

Lemma nextdom_body_sat : forall ρ Δ Φ args a,
    List.length args = List.length Δ -> ~ nextdom (dm_local ρ (gu_body Δ Φ) args) a.
Proof. intros * Hl Hn; inversion Hn; subst; eapply nextparam_body_sat; eassumption. Qed.

Lemma per_univ_elem_pi_top : forall i R ρ a B, ~ per_univ_elem i R (Πᵈ a ρ B) ⊤ᵈ.
Proof. intros * H; destruct (per_univ_elem_pi_left _ _ _ _ _ _ H) as (? & ? & ? & ?); discriminate. Qed.

(** A typed value at a [Π] that still takes an argument takes it at the
    [Π]'s domain. *)
Lemma mtyped_pi_dom : gchild_ok -> galias_params_ok ->
    forall w ch k a, mtyped w ch k a ->
    forall a1 ρB B, a = Πᵈ a1 ρB B ->
    forall a0, nextdom w a0 -> exists i R, per_univ_elem i R a1 a0.
Proof.
  intros HGc HGap.
  induction 1 as [ w ch k a0 a ρB B i in_rel Hgl Hnp Ha Hty IH
                 | w a i R Hs Ha
                 | ρ Δ Φ args x Φ' b pv A M ρ1 a a0 i R Hl Hx Hb HA Ha
                 | ρ Δ Φ args y Φ' Uy ρ1 ch k a Hl Hy Hb Hm IH
                 | ρ Δ E args h ch k a Hl HE Hm IH
                 | p T args x b A0 B f aA j E a a0 i R Hm Hl Hr Hf HaA HE Hff Ha0 Ha
                 | p args y T ch k a Hm Hty IH
                 | p args y U ch ch' k a Hm Hk Hty IH
                 | ρ U args ch0 ch k a a1 Hl Hnp1 Hch0 Hk Hty IH ];
    intros a1' ρB' B' Heq a0' Hnd.
  - injection Heq as <- <- <-.
    destruct Hgl as [(ρ & U & args & -> & Hlt) | (p & args & -> & -> & ->)].
    + inversion Hnd; subst.
      * pose proof (nextparam_functional _ _ Hnp _ ltac:(eassumption)) as <-; eauto.
      * cbn in Hlt; lia.
    + inversion Hnd; subst.
      pose proof (nextparam_functional _ _ Hnp _ ltac:(eassumption)) as <-; eauto.
  - subst; exfalso; eapply per_univ_elem_pi_top; exact Ha.
  - exfalso; eapply nextdom_body_sat; eassumption.
  - exfalso; eapply nextdom_body_sat; eassumption.
  - inversion Hnd; subst.
    + match goal with Hn : nextparam _ _ |- _ => inversion Hn; subst end; cbn in *.
      * match goal with Hn' : nth_error _ _ = Some _ |- _ =>
          assert (Hn'' : nth_error (rev Δ) (List.length args) <> None) by congruence end.
        apply nth_error_Some in Hn''; rewrite length_rev in Hn''; lia.
      * match goal with H1 : eval_modexp _ _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
        eapply IH; [ reflexivity | apply nd_param; eassumption ].
    + match goal with H1 : eval_modexp _ _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
      eapply IH; [ reflexivity | eassumption ].
  - subst a.
    inversion Hnd; subst.
    match goal with Hn : nextparam _ _ |- _ => inversion Hn; subst end.
    match goal with Hm' : gc_module _ _ p = Some (mr_body ?T') |- _ => rewrite Hm in Hm'; injection Hm' as <- end.
    match goal with Hn' : nth_error (rev T) _ = Some (ce_ass ?A1) |- _ => rename Hn' into HnT end.
    assert (HlT : List.length args < List.length T)
      by (assert (Hn'' : nth_error (rev T) (List.length args) <> None) by congruence;
          apply nth_error_Some in Hn''; rewrite length_rev in Hn''; exact Hn'').
    rewrite nth_error_rev in HnT.
    replace (List.length args <? List.length T) with true in HnT by (symmetry; apply Nat.ltb_lt; exact HlT).
    replace (List.length T - List.length args) with (S (List.length T - S (List.length args))) in Ha0 by lia.
    rewrite (firstn_snoc _ _ _ HnT), ctx_pi_app in Ha0; cbn in Ha0.
    inversion Ha0; subst.
    functional_eval_rewrite_clear.
    destruct (per_univ_elem_pi_inv Ha) as (in' & out' & Hin' & _ & _).
    eauto.
  - inversion Hnd; subst.
    match goal with Hn : nextparam _ _ |- _ => inversion Hn; subst end.
    match goal with Hm0 : gc_module _ _ p = Some (mr_body ?Tp) |- _ => rename Hm0 into Hmp end.
    destruct (HGc _ _ _ _ Hmp Hm) as [Δ ->].
    eapply IH; [ reflexivity |].
    apply nd_param; econstructor; [ exact Hm | rewrite rev_app_distr, nth_error_app1; [ eassumption |] | eassumption ].
    apply nth_error_Some; match goal with Hn' : nth_error (rev _) _ = Some _ |- _ => rewrite Hn' end; discriminate.
  - inversion Hnd; subst.
    match goal with Hn : nextparam _ _ |- _ => inversion Hn; subst end.
    match goal with Hm0 : gc_module _ _ p = Some (mr_body ?Tp) |- _ => rename Hm0 into Hmp end.
    destruct (HGap _ _ _ _ _ Hmp Hm) as [Δ HU].
    match goal with Hn' : nth_error (rev _) _ = Some _ |- _ => rename Hn' into HnT end.
    assert (HlT : List.length args < List.length (rev _))
      by (apply nth_error_Some; rewrite HnT; discriminate).
    rewrite length_rev in HlT.
    assert (HnU : nth_error (rev (gu_params U)) (List.length args) = Some (ce_ass A))
      by (rewrite HU, rev_app_distr, nth_error_app1; [ exact HnT | rewrite length_rev; exact HlT ]).
    eapply IH; [ reflexivity | apply nd_param; econstructor; eassumption ].
  - inversion Hnd; subst;
      [ match goal with Hn : nextparam _ _ |- _ => inversion Hn end | eapply IH; [ reflexivity | eassumption ] ].
Qed.

Lemma mtyped_nil_mod : forall w ch k a, mtyped w ch k a -> ch = nil -> k = mk_mod ->
    (msat w /\ exists i R, per_univ_elem i R a ⊤ᵈ) \/ (exists a0, nextdom w a0).
Proof.
  induction 1 as [ w ch k a0 a ρB B i in_rel Hgl Hnp Ha Hty IH
                 | w a i R Hs Ha
                 | ρ Δ Φ args x Φ' b pv A M ρ1 a a0 i R Hl Hx Hb HA Ha
                 | ρ Δ Φ args y Φ' Uy ρ1 ch k a Hl Hy Hb Hm IH
                 | ρ Δ E args h ch k a Hl HE Hm IH
                 | p T args x b A0 B f aA j E a a0 i R Hm Hl Hr Hf HaA HE Hff Ha0 Ha
                 | p args y T ch k a Hm Hty IH
                 | p args y U ch ch' k a Hm Hk Hty IH
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
Lemma mtyped_arity_pi : gchild_ok -> galias_params_ok ->
    forall w a, mtyped w nil mk_mod a ->
    forall i R b ρ C, per_univ_elem i R a (Πᵈ b ρ C) ->
    exists a0 j R0, nextdom w a0 /\ per_univ_elem j R0 b a0.
Proof.
  intros HGc HGap * Hm * HR.
  destruct (mtyped_nil_mod _ _ _ _ Hm eq_refl eq_refl) as [[_ (i' & R' & Ht)] | [a0 Hn]].
  - exfalso.
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ Ht)) HR) as (R2 & H2 & _).
    pose proof (per_univ_elem_top_left _ _ _ H2); discriminate.
  - pose proof (mtyped_resp _ _ _ _ Hm _ _ _ HR) as Hm'.
    destruct (mtyped_pi_dom HGc HGap _ _ _ _ Hm' _ _ _ eq_refl _ Hn) as (j & R0 & H0).
    exists a0, j, R0; split; assumption.
Qed.

Lemma mtyped_member_inv : forall h ch0 ch k a, mtyped (dm_member h ch0) ch k a ->
    exists ρ U args a1, h = dm_local ρ U args /\ List.length args < List.length (gu_params U) /\
      nextparam h a1 /\ ch0 <> nil /\ (k = mk_term -> ch <> nil) /\ mtyped h (ch0 ++ ch) k a.
Proof.
  intros * H; inversion H; subst.
  - match goal with Hg : _ \/ _ |- _ => destruct Hg as [(? & ? & ? & ? & _) | (? & ? & ? & _)]; discriminate end.
  - match goal with Hs : msat _ |- _ => inversion Hs end.
  - do 4 eexists; repeat split; eauto.
Qed.

Lemma mtyped_alias_sat_inv : forall ρ Δ E args ch k a h,
    mtyped (dm_local ρ (gu_mk Δ (md_alias E)) args) ch k a ->
    List.length args = List.length Δ -> eval_modexp gc_deps gc_stack E (env_args ρ args) h ->
    mtyped h ch k a.
Proof.
  intros * H Hl HE; inversion H; subst.
  - match goal with Hg : _ \/ _ |- _ => destruct Hg as [(? & ? & ? & Heq & Hlt) | (? & ? & ? & _)]; [| discriminate ] end.
    injection Heq as <- <- <-; cbn in Hlt; lia.
  - match goal with Hs : msat _ |- _ => inversion Hs; subst end.
    match goal with H1 : eval_modexp _ _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
    match goal with Hs : msat h |- _ => eapply mty_top; eassumption end.
  - match goal with H1 : eval_modexp _ _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
    assumption.
Qed.

Lemma mtyped_app_nd : gchild_ok -> galias_params_ok ->
    forall w a0, nextdom w a0 ->
    forall ch k a1 ρB B, mtyped w ch k (Πᵈ a1 ρB B) ->
    forall i' Ein c w1 b, per_univ_elem i' Ein a1 a1 -> Ein c c ->
    eval_appm gc_deps gc_stack w c w1 -> ⟦ B ⟧ ρB ↦ c ↘ b -> mtyped w1 ch k b.
Proof.
  intros HGc HGap; induction 1 as [w a Hn | h ch0 a Hn IH | ρ Δ E args h a Hl HE Hn IH];
    intros * Hm * Ha Hc Hw1 Hb.
  - eapply mtyped_app; [ exact HGc | exact HGap | exact Hm | reflexivity | left; eauto | eassumption .. ].
  - eapply mtyped_app; [ exact HGc | exact HGap | exact Hm | reflexivity | right; eauto | eassumption .. ].
  - pose proof (mtyped_alias_sat_inv _ _ _ _ _ _ _ _ Hm Hl HE) as Hm'.
    inversion Hw1; subst; try lia.
    match goal with H1 : eval_modexp _ _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
    eapply IH; eassumption.
Qed.

(** Related typed values, applied to related arguments of their next
    parameter, give related results. *)
Lemma appm_rel_typed : gparam_ok -> gchild_ok -> galias_ok -> galias_params_ok ->
    forall w a0, nextdom w a0 ->
    forall ch k a1 ρB B, mtyped w ch k (Πᵈ a1 ρB B) ->
    forall i Ein, per_univ_elem i Ein a1 a1 ->
    (forall c, Ein c c -> exists b, ⟦ B ⟧ ρB ↦ c ↘ b) ->
    forall w', per_dmod w w' -> forall c c', Ein c c' ->
    exists w1 w1', eval_appm gc_deps gc_stack w c w1 /\ eval_appm gc_deps gc_stack w' c' w1' /\ per_dmod w1 w1'.
Proof.
  intros HGp HGc HGa HGap; induction 1 as [w a Hn | h ch0 a Hn IH | ρ Δ E args h a Hl HE Hn IH];
    intros * Hm * Ha HB w' Hw c c' Hc.
  - destruct (mtyped_pi_dom HGc HGap _ _ _ _ Hm _ _ _ eq_refl _ (nd_param _ _ Hn)) as (j & R0 & H0).
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ H0 Ha) as E0.
    destruct (appm_ex _ _ Hn c) as [w1 Hw1].
    destruct (appm_rel HGp _ _ _ Hw Hn _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ H0)) (proj2 (E0 _ _) Hc) Hw1)
      as (w1' & Hw1' & Hww).
    exists w1, w1'; auto.
  - destruct (mtyped_member_inv _ _ _ _ _ Hm) as (ρ & U & args & a2 & -> & Hlt & Hnp & Hch0 & Hk & Hm').
    inversion Hw; subst.
    match goal with Hh : per_dmod (dm_local ρ U args) ?h' |- _ => rename Hh into Hhh end.
    destruct (IH _ _ _ _ _ Hm' _ _ Ha HB _ Hhh _ _ Hc) as (h1 & h1' & Hh1 & Hh1' & Hh11).
    assert (HPE : PER Ein) by (eapply per_elem_PER; exact Ha).
    assert (Hcc : Ein c c) by (etransitivity; [ exact Hc | symmetry; exact Hc ]).
    destruct (HB _ Hcc) as [b Hb].
    pose proof (mtyped_app_nd HGc HGap _ _ Hn _ _ _ _ _ Hm' _ _ _ _ _ Ha Hcc Hh1 Hb) as Hm1.
    destruct (mtyped_selmc_ex _ _ _ _ Hm1 ch0 _ eq_refl Hk) as [r Hr].
    destruct (mtyped_selmc_rel HGc HGa _ _ _ _ Hm1 ch0 _ eq_refl Hk _ Hh11 _ Hr) as (r' & Hr' & Hrr).
    exists r, r'; split; [ econstructor; eassumption |]; split; [ econstructor; eassumption | exact Hrr ].
  - pose proof (mtyped_alias_sat_inv _ _ _ _ _ _ _ _ Hm Hl HE) as Hm'.
    destruct (per_dmod_local_inv _ _ _ _ Hw) as (ρ' & [Δ' D'] & args' & -> & Hlt & L1 & L2).
    cbn [gu_params gu_def] in *.
    pose proof (per_ltele_full _ _ _ _ _ _ _ _ Hlt ltac:(rewrite length_rev; exact Hl)) as Hd.
    inversion Hd; subst.
    match goal with H1' : eval_modexp _ _ E _ ?h1, H3 : eval_modexp _ _ ?E' _ ?h', H5 : per_dmod ?h1 ?h' |- _ =>
      pose proof (functional_eval_modexp _ _ _ _ HE H1') as <-; rename H3 into HE', H5 into Hhh end.
    destruct (IH _ _ _ _ _ Hm' _ _ Ha HB _ Hhh _ _ Hc) as (h1 & h1' & Hh1 & Hh1' & Hh11).
    exists h1, h1'; split; [ eapply eval_appm_alias; eassumption |]; split; [ eapply eval_appm_alias; [ lia | eassumption .. ] | exact Hh11 ].
Qed.

End Fixed_GCtx.
