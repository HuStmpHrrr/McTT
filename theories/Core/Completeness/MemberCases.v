(** * Members of Module Values

    The members of a module value are typed at type values.  A module still
    lacking an argument types its members at [Π]-values whose domain is the
    type of that argument; a saturated local body types a definition at its
    declared type, read in the environment the body before it makes; an
    alias types its members as its target does; a global module types its
    members as the global definitions do.  Related module values have
    related members ([mtyped_rel]). *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases UniverseCases SubstitutionCases LetCases UnitCases InstanceCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** The Next Argument of a Module Value *)

Inductive nextparam : dmod -> domain -> Prop :=
| np_local : forall ρ U args A a,
    nth_error (rev (gu_params U)) (List.length args) = Some (ce_ass A) ->
    ⟦ A ⟧ env_args ρ args ↘ a ->
    nextparam (dm_local ρ U args) a
| np_alias : forall ρ Δ E args h a,
    List.length args = List.length Δ ->
    eval_modexp gc_deps gc_stack E (env_args ρ args) h ->
    nextparam h a ->
    nextparam (dm_local ρ (gu_mk Δ (md_alias E)) args) a
| np_global : forall p T args A a,
    gc_module gc_deps gc_stack p = Some (mr_body T) ->
    nth_error (rev T) (List.length args) = Some (ce_ass A) ->
    ⟦ A ⟧ env_args nil args ↘ a ->
    nextparam (dm_global p args) a.

(** Supplying the first missing argument of a walk over parameters. *)
Lemma per_ltele_supply : forall ts ρ D ts' ρ' D' args args' A,
    per_ltele ts ρ D ts' ρ' D' args args' ->
    nth_error ts (List.length args) = Some (ce_ass A) ->
    exists i R A', PER.Definitions.rel_typ i A (env_args ρ args) A' (env_args ρ' args') R /\
      forall c c', R c c' -> per_ltele ts ρ D ts' ρ' D' (args ++ c :: nil) (args' ++ c' :: nil).
Proof.
  intros * H; revert A; induction H; intros A0 Hn; cbn in Hn.
  - destruct (IHper_ltele _ Hn) as (j & R0 & A1 & HR0 & HS).
    exists j, R0, A1; split; [ exact HR0 |].
    intros c c' Hc; cbn; eapply per_ltele_supplied; [ eassumption | eassumption | apply HS, Hc ].
  - injection Hn as ->.
    exists i, R, A'; split; [ assumption |].
    intros c c' Hc; cbn; eapply per_ltele_supplied; [ eassumption | eassumption |]; auto.
  - discriminate.
Qed.

Lemma per_ltele_lengths : forall ts ρ D ts' ρ' D' args args',
    per_ltele ts ρ D ts' ρ' D' args args' ->
    List.length ts = List.length ts' /\ List.length args = List.length args'.
Proof.
  intros * H; induction H; cbn.
  - destruct IHper_ltele; split; congruence.
  - match goal with Ht : PER.Definitions.rel_typ _ _ _ _ _ _ |- _ => destruct Ht as [a0 a0' _ _ Ha] end.
    pose proof (var_per_elem 0 Ha) as Hc.
    destruct (H1 _ _ Hc); split; [ cbn; congruence | reflexivity ].
  - split; reflexivity.
Qed.

Lemma per_ltele_full : forall ts ρ D ts' ρ' D' args args',
    per_ltele ts ρ D ts' ρ' D' args args' ->
    List.length args = List.length ts ->
    per_mdef (env_args ρ args) D (env_args ρ' args') D'.
Proof.
  intros * H; induction H; cbn; intros Hl; [ apply IHper_ltele; lia | discriminate | assumption ].
Qed.

Lemma per_ltele_kind : forall ts ρ D ts' ρ' D' args args',
    per_ltele ts ρ D ts' ρ' D' args args' ->
    (exists Φ Φ', D = md_body Φ /\ D' = md_body Φ') \/ (exists E E', D = md_alias E /\ D' = md_alias E').
Proof.
  intros * H; induction H; auto.
  - match goal with Ht : PER.Definitions.rel_typ _ _ _ _ _ _ |- _ => destruct Ht as [a0 a0' _ _ Ha] end.
    exact (H1 _ _ (var_per_elem 0 Ha)).
  - inversion H; subst; eauto.
Qed.

(** The definition named [x] of two related bodies. *)
Lemma per_body_lookup_def : forall ρ Φ ρ' Φ' x Φ1 b pv A M,
    per_body ρ Φ ρ' Φ' ->
    gm_prefix_upto Φ x = Some (gm_ext Φ1 x (ge_def b pv A (Some M))) ->
    exists Φ1' b' pv' A' M' ρ1 ρ1' i R,
      gm_prefix_upto Φ' x = Some (gm_ext Φ1' x (ge_def b' pv' A' (Some M'))) /\
      eval_benv gc_deps gc_stack ρ Φ1 ρ1 /\ eval_benv gc_deps gc_stack ρ' Φ1' ρ1' /\
      PER.Definitions.rel_typ i A ρ1 A' ρ1' R /\ PER.Definitions.rel_elem M ρ1 M' ρ1' R.
Proof.
  intros * H; induction H; intros Hx; cbn in Hx |- *; try discriminate.
  - destruct (String.eqb x y) eqn:Ey; [ injection Hx as -> -> -> |].
    + apply String.eqb_eq in Ey; subst.
      do 9 eexists; split; [ reflexivity |]; eauto.
    + apply IHper_body; exact Hx.
  - destruct (String.eqb x y) eqn:Ey; [ discriminate |]; apply IHper_body; exact Hx.
  - apply IHper_body; exact Hx.
Qed.

(** The submodule named [y] of two related bodies. *)
Lemma per_body_lookup_mod : forall ρ Φ ρ' Φ' y Φ1 Uy,
    per_body ρ Φ ρ' Φ' ->
    gm_prefix_upto Φ y = Some (gm_ext Φ1 y (ge_mod Uy)) ->
    exists Φ1' Uy' ρ1 ρ1',
      gm_prefix_upto Φ' y = Some (gm_ext Φ1' y (ge_mod Uy')) /\
      eval_benv gc_deps gc_stack ρ Φ1 ρ1 /\ eval_benv gc_deps gc_stack ρ' Φ1' ρ1' /\
      per_dmod (dm_local ρ1 Uy nil) (dm_local ρ1' Uy' nil).
Proof.
  intros * H; induction H; intros Hx; cbn in Hx |- *; try discriminate.
  - destruct (String.eqb y y0) eqn:Ey; [ discriminate |]; apply IHper_body; exact Hx.
  - destruct (String.eqb y y0) eqn:Ey; [ injection Hx as -> -> |].
    + apply String.eqb_eq in Ey; subst.
      do 4 eexists; split; [ reflexivity |]; eauto.
    + apply IHper_body; exact Hx.
  - apply IHper_body; exact Hx.
Qed.

(** ** Saturated Module Values *)

Inductive msat : dmod -> Prop :=
| ms_body : forall ρ Δ Φ args,
    List.length args = List.length Δ -> msat (dm_local ρ (gu_body Δ Φ) args)
| ms_alias : forall ρ Δ E args h,
    List.length args = List.length Δ ->
    eval_modexp gc_deps gc_stack E (env_args ρ args) h -> msat h ->
    msat (dm_local ρ (gu_mk Δ (md_alias E)) args)
| ms_global : forall p T args,
    gc_module gc_deps gc_stack p = Some (mr_body T) -> List.length args = List.length T ->
    msat (dm_global p args).

(** ** Typed Members

    [mtyped w ch k a]: the chain [ch] of [w] is a member of kind [k] at the
    type value [a] (for [k = mk_mod], the arity of the submodule).  A local
    value lacking an argument types its members at a [Π] over that argument; a
    global value types its term members at the instance of the global
    definition's type, so only its own arity is a [Π] of this kind. *)

Inductive mtyped : dmod -> list String.string -> mkind -> domain -> Prop :=
| mty_pi : forall w ch k a0 a ρB B i in_rel,
    (exists ρ U args, w = dm_local ρ U args /\ List.length args < List.length (gu_params U)) \/
      (exists p args, w = dm_global p args /\ ch = nil /\ k = mk_mod) ->
    nextparam w a0 -> per_univ_elem i in_rel a a0 ->
    (forall c w1 b, in_rel c c -> eval_appm gc_deps gc_stack w c w1 -> ⟦ B ⟧ ρB ↦ c ↘ b -> mtyped w1 ch k b) ->
    mtyped w ch k (Πᵈ a ρB B)
| mty_top : forall w a i R, msat w -> per_univ_elem i R a ⊤ᵈ -> mtyped w nil mk_mod a
| mty_def : forall ρ Δ Φ args x Φ' b A M ρ1 a a0 i R,
    List.length args = List.length Δ ->
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b false A (Some M))) ->
    eval_benv gc_deps gc_stack (env_args ρ args) Φ' ρ1 ->
    ⟦ A ⟧ ρ1 ↘ a0 -> per_univ_elem i R a a0 ->
    mtyped (dm_local ρ (gu_body Δ Φ) args) (x :: nil) mk_term a
| mty_sub : forall ρ Δ Φ args y Φ' Uy ρ1 ch k a,
    List.length args = List.length Δ ->
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod Uy)) ->
    eval_benv gc_deps gc_stack (env_args ρ args) Φ' ρ1 ->
    mtyped (dm_local ρ1 Uy nil) ch k a ->
    mtyped (dm_local ρ (gu_body Δ Φ) args) (y :: ch) k a
| mty_alias : forall ρ Δ E args h ch k a,
    List.length args = List.length Δ ->
    eval_modexp gc_deps gc_stack E (env_args ρ args) h -> mtyped h ch k a ->
    mtyped (dm_local ρ (gu_mk Δ (md_alias E)) args) ch k a
| mty_gdef : forall p T args x b A0 B f aA j E a a0 i R,
    gc_module gc_deps gc_stack p = Some (mr_body T) ->
    List.length args <= List.length T ->
    gc_resolve gc_deps gc_stack (path_app p (x :: nil)) = Some (ge_def b false (ctx_pi T A0) B) ->
    ⟦ a_glob (path_app p (x :: nil)) ⟧ nil ↘ f ->
    ⟦ ctx_pi T A0 ⟧ nil ↘ aA -> per_univ_elem j E aA aA -> E f f ->
    ⟦ ctx_pi (firstn (List.length T - List.length args) T) A0 ⟧ env_args nil args ↘ a0 ->
    per_univ_elem i R a a0 ->
    mtyped (dm_global p args) (x :: nil) mk_term a
| mty_gsub : forall p args y T ch k a,
    gc_module gc_deps gc_stack (path_app p (y :: nil)) = Some (mr_body T) ->
    mtyped (dm_global (path_app p (y :: nil)) args) ch k a ->
    mtyped (dm_global p args) (y :: ch) k a
| mty_galias : forall p args y U ch ch' k a,
    gc_module gc_deps gc_stack (path_app p (y :: nil)) = Some (mr_alias U ch) ->
    (k = mk_term -> ch' <> nil) ->
    mtyped (dm_local nil U args) (ch ++ ch') k a ->
    mtyped (dm_global p args) (y :: ch') k a
| mty_member : forall ρ U args ch0 ch k a,
    List.length args < List.length (gu_params U) -> ch0 <> nil -> (k = mk_term -> ch <> nil) ->
    mtyped (dm_local ρ U args) (ch0 ++ ch) k a -> mtyped (dm_member (dm_local ρ U args) ch0) ch k a.

(** The types of the parameters of global modules are related at related
    arguments: the global telescopes are valid. *)
Definition gparam_ok : Prop :=
  forall p T args args' A,
    gc_module gc_deps gc_stack p = Some (mr_body T) ->
    per_gargs (rev T) nil nil args args' ->
    nth_error (rev T) (List.length args) = Some (ce_ass A) ->
    exists i R, PER.Definitions.rel_typ i A (env_args nil args) A (env_args nil args') R.

Lemma per_gargs_lengths : forall ts ρ ρ' args args',
    per_gargs ts ρ ρ' args args' -> List.length args = List.length args' /\ List.length args <= List.length ts.
Proof. intros * H; induction H; cbn; lia. Qed.

Lemma per_gargs_supply : forall ts ρ ρ' args args' A i R c c',
    per_gargs ts ρ ρ' args args' ->
    nth_error ts (List.length args) = Some (ce_ass A) ->
    PER.Definitions.rel_typ i A (env_args ρ args) A (env_args ρ' args') R -> R c c' ->
    per_gargs ts ρ ρ' (args ++ c :: nil) (args' ++ c' :: nil).
Proof.
  intros * H; revert A i R c c'; induction H; intros A0 i0 R0 c c' Hn HR Hc; cbn in *.
  - destruct ts as [| e ts]; cbn in Hn; [ discriminate |]; injection Hn as ->.
    econstructor; [ eassumption | eassumption | constructor ].
  - econstructor; [ eassumption | eassumption |]; eapply IHper_gargs; eassumption.
Qed.

(** ** Applying Related Module Values *)

Lemma appm_rel : gparam_ok -> forall w w' a, per_dmod w w' -> nextparam w a ->
    forall i E b c c' r, per_univ_elem i E a b -> E c c' -> eval_appm gc_deps gc_stack w c r ->
    exists r', eval_appm gc_deps gc_stack w' c' r' /\ per_dmod r r'.
Proof.
  intros HGp * Hw Hnp; revert w' Hw;
    induction Hnp as [ρ U args A a Hn Ha | ρ Δ E args h a Hl HE Hnp IH | p T args A a Hm Hn Ha];
    intros w' Hw * HR Hcc Hr.
  - inversion Hw; subst.
    match goal with Hlt : per_ltele _ _ _ _ _ _ _ _ |- _ => rename Hlt into Hl end.
    destruct (per_ltele_supply _ _ _ _ _ _ _ _ _ Hl Hn) as (i0 & R0 & A' & [a1 a2 Ha1 Ha2 HR0] & Hsup).
    pose proof (functional_eval_exp _ _ _ _ Ha Ha1) as <-.
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR HR0) as EE.
    pose proof (Hsup _ _ (proj1 (EE _ _) Hcc)) as Hl'.
    destruct (per_ltele_lengths _ _ _ _ _ _ _ _ Hl) as [Hlen1 Hlen2].
    rewrite !length_rev in Hlen1.
    assert (Hlt : List.length args < List.length (gu_params U))
      by (assert (Hn' : nth_error (rev (gu_params U)) (List.length args) <> None) by congruence;
          apply nth_error_Some in Hn'; rewrite length_rev in Hn'; exact Hn').
    destruct (per_ltele_kind _ _ _ _ _ _ _ _ Hl) as [(Φ1 & Φ1' & E1 & E1') | (E1 & E1' & HE1 & HE1')];
      destruct U as [Δ D], U' as [Δ' D']; cbn [gu_def gu_params] in *; subst D D';
      inversion Hr; subst; try lia.
    + eexists; split; [ apply eval_appm_body; lia |]; constructor; exact Hl'.
    + eexists; split; [ apply eval_appm_alias_unsat; lia |]; constructor; exact Hl'.
  - inversion Hw; subst.
    match goal with Hlt0 : per_ltele _ _ _ _ _ _ _ _ |- _ => rename Hlt0 into Hlt end.
    destruct (per_ltele_lengths _ _ _ _ _ _ _ _ Hlt) as [Hlen1 Hlen2].
    rewrite !length_rev in Hlen1. cbn [gu_params gu_def] in *.
    pose proof (per_ltele_full _ _ _ _ _ _ _ _ Hlt ltac:(rewrite length_rev; exact Hl)) as Hd.
    inversion Hd; subst.
    inversion Hr; subst; try lia.
    match goal with
    | H1 : eval_modexp _ _ E _ ?h0, H5 : per_dmod ?h0 ?h', H3 : eval_modexp _ _ ?E' _ ?h',
      H10 : eval_modexp _ _ E _ ?h1, H11 : eval_appm _ _ ?h1 c r |- _ =>
        pose proof (functional_eval_modexp _ _ _ _ HE H1) as <-;
        pose proof (functional_eval_modexp _ _ _ _ HE H10) as <-;
        destruct (IH _ H5 _ _ _ _ _ _ HR Hcc H11) as (r' & Hr' & Hrr');
        destruct U' as [Δ' D']; cbn [gu_def gu_params] in *; subst D';
        exists r'; split; [ eapply eval_appm_alias; [ lia | exact H3 | exact Hr' ] | exact Hrr' ]
    end.
  - inversion Hw; subst. inversion Hr; subst.
    match goal with Hm' : gc_module _ _ p = Some (mr_body ?T') |- _ =>
      rewrite Hm in Hm'; injection Hm' as <- end.
    match goal with Hg0 : per_gargs _ _ _ args _ |- _ => rename Hg0 into Hg end.
    destruct (HGp _ _ _ _ _ Hm Hg Hn) as (i0 & R0 & [a1 a2 Ha1 Ha2 HR0]).
    pose proof (functional_eval_exp _ _ _ _ Ha Ha1) as <-.
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR HR0) as EE.
    eexists; split; [ constructor |].
    econstructor; [ exact Hm |].
    eapply per_gargs_supply; [ exact Hg | exact Hn | econstructor; eassumption | apply EE, Hcc ].
Qed.

(** ** Selections from Module Values Still Lacking Arguments *)

Lemma selmc_member : forall w ch0 ch v,
    eval_selmc gc_deps gc_stack (dm_member w ch0) ch v -> v = dm_member w (ch0 ++ ch).
Proof.
  intros w ch0 ch; revert ch0; induction ch as [| y ch IH]; intros * H; inversion H; subst.
  - rewrite app_nil_r; reflexivity.
  - match goal with Hs : eval_selm _ _ _ _ _ |- _ => inversion Hs; subst end.
    rewrite (IH _ _ ltac:(eassumption)), <- app_assoc; reflexivity.
Qed.

Lemma selc_member : forall w ch0 ch v,
    eval_selc gc_deps gc_stack (dm_member w ch0) ch v -> v = d_member w (ch0 ++ ch).
Proof.
  intros w ch0 ch; revert ch0; induction ch as [| y ch IH]; intros * H; inversion H; subst.
  - match goal with Hs : eval_sel _ _ _ _ _ |- _ => inversion Hs; subst end; reflexivity.
  - match goal with Hs : eval_selm _ _ _ _ _ |- _ => inversion Hs; subst end.
    rewrite (IH _ _ ltac:(eassumption)), <- app_assoc; reflexivity.
Qed.

Lemma selm_unsat : forall ρ U args y h,
    List.length args < List.length (gu_params U) ->
    eval_selm gc_deps gc_stack (dm_local ρ U args) y h -> h = dm_member (dm_local ρ U args) (y :: nil).
Proof. intros * Hl H; inversion H; subst; cbn in Hl; [ reflexivity | lia | lia ]. Qed.

Lemma sel_unsat : forall ρ U args x v,
    List.length args < List.length (gu_params U) ->
    eval_sel gc_deps gc_stack (dm_local ρ U args) x v -> v = d_member (dm_local ρ U args) (x :: nil).
Proof. intros * Hl H; inversion H; subst; cbn in Hl; [ reflexivity | lia | lia ]. Qed.

Lemma selc_unsat : forall ρ U args ch v,
    List.length args < List.length (gu_params U) ->
    eval_selc gc_deps gc_stack (dm_local ρ U args) ch v -> v = d_member (dm_local ρ U args) ch.
Proof.
  intros * Hl H; inversion H; subst.
  - eapply sel_unsat; eassumption.
  - match goal with Hs : eval_selm _ _ _ _ ?h1 |- _ => pose proof (selm_unsat _ _ _ _ _ Hl Hs); subst end.
    rewrite (selc_member _ _ _ _ ltac:(eassumption)); reflexivity.
Qed.

Lemma selmc_unsat : forall ρ U args ch v,
    List.length args < List.length (gu_params U) -> ch <> nil ->
    eval_selmc gc_deps gc_stack (dm_local ρ U args) ch v -> v = dm_member (dm_local ρ U args) ch.
Proof.
  intros * Hl Hch H; inversion H; subst; [ congruence |].
  match goal with Hs : eval_selm _ _ _ _ ?h1 |- _ => pose proof (selm_unsat _ _ _ _ _ Hl Hs); subst end.
  rewrite (selmc_member _ _ _ _ ltac:(eassumption)); reflexivity.
Qed.

Lemma per_univ_elem_pi_inv : forall {j E a ρ B a' ρ' B'},
    per_univ_elem j E (Πᵈ a ρ B) (Πᵈ a' ρ' B') ->
    exists in_rel (out_rel : forall c c', in_rel c c' -> relation domain),
      per_univ_elem j in_rel a a' /\
      (forall c c' (H : in_rel c c'), rel_mod_eval (per_univ_elem j) B (ρ ↦ c) B' (ρ' ↦ c') (out_rel c c' H)) /\
      (E <~> fun f f' => forall c c' (H : in_rel c c'), rel_mod_app f c f' c' (out_rel c c' H)).
Proof.
  intros * H.
  basic_invert_per_univ_elem H.
  do 2 eexists; split; [ eassumption | split ]; [| eassumption ].
  intros c c' Hc; destruct_rel_mod_eval; econstructor; eassumption.
Qed.

(** A function at a telescope's [Π]-type, applied to arguments related at
    the telescope. *)
Lemma apps_rel_gargs : forall ts ρ ρ' args args' A0 g g' j E a a',
    per_gargs ts ρ ρ' args args' ->
    ⟦ ctx_pi (rev ts) A0 ⟧ ρ ↘ a -> ⟦ ctx_pi (rev ts) A0 ⟧ ρ' ↘ a' -> per_univ_elem j E a a' -> E g g' ->
    exists v v' b b' R,
      eval_apps gc_deps gc_stack g args v /\ eval_apps gc_deps gc_stack g' args' v' /\
      ⟦ ctx_pi (rev (skipn (List.length args) ts)) A0 ⟧ env_args ρ args ↘ b /\
      ⟦ ctx_pi (rev (skipn (List.length args) ts)) A0 ⟧ env_args ρ' args' ↘ b' /\
      per_univ_elem j R b b' /\ R v v'.
Proof.
  intros * H; revert A0 g g' j E a a'; induction H; intros * Ha Ha' HE Hg.
  - do 5 eexists; repeat split; [ constructor | constructor | exact Ha | exact Ha' | exact HE | exact Hg ].
  - cbn [rev] in Ha, Ha'; rewrite ctx_pi_app in Ha, Ha'; cbn in Ha, Ha'.
    inversion Ha; subst; inversion Ha'; subst.
    functional_eval_rewrite_clear.
    destruct (per_univ_elem_pi_inv HE) as (in_rel & out_rel & Hin & Hout & HEq).
    match goal with Ht : PER.Definitions.rel_typ _ _ _ _ _ _ |- _ => destruct Ht as [x1 x2 Hx1 Hx2 HRx] end.
    functional_eval_rewrite_clear.
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRx Hin) as ER.
    assert (Hcc : in_rel a a') by (apply ER; assumption).
    destruct (Hout _ _ Hcc) as [b1 b1' Hb1 Hb1' Hb].
    destruct (proj1 (HEq g g') Hg _ _ Hcc) as [g1 g1' Hg1 Hg1' Hgg].
    destruct (IHper_gargs _ _ _ _ _ _ _ Hb1 Hb1' Hb Hgg) as (v & v' & b & b' & R1 & Hv & Hv' & Hb2 & Hb2' & HR1 & Hvv).
    exists v, v', b, b', R1; repeat split; try assumption; econstructor; eassumption.
Qed.

Lemma per_gargs_app : forall ts ts2 ρ ρ' args args',
    per_gargs ts ρ ρ' args args' -> per_gargs (ts ++ ts2) ρ ρ' args args'.
Proof. intros * H; induction H; cbn; econstructor; eassumption. Qed.

(** A saturated alias selects as its target. *)
Lemma selc_alias : forall ρ Δ E args h ch v,
    List.length args = List.length Δ ->
    eval_modexp gc_deps gc_stack E (env_args ρ args) h ->
    eval_selc gc_deps gc_stack (dm_local ρ (gu_mk Δ (md_alias E)) args) ch v <-> eval_selc gc_deps gc_stack h ch v.
Proof.
  intros * Hl HE; split; intros H.
  - inversion H; subst.
    + match goal with Hs : eval_sel _ _ _ _ _ |- _ => inversion Hs; subst end; cbn in *; try lia.
      match goal with H1 : eval_modexp _ _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1); subst end.
      constructor; assumption.
    + match goal with Hs : eval_selm _ _ _ _ _ |- _ => inversion Hs; subst end; cbn in *; try lia.
      match goal with H1 : eval_modexp _ _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1); subst end.
      econstructor; eassumption.
  - inversion H; subst.
    + constructor; eapply eval_sel_alias; eassumption.
    + econstructor; [ eapply eval_selm_alias; eassumption | eassumption ].
Qed.

Lemma selmc_alias : forall ρ Δ E args h ch v,
    List.length args = List.length Δ -> ch <> nil ->
    eval_modexp gc_deps gc_stack E (env_args ρ args) h ->
    eval_selmc gc_deps gc_stack (dm_local ρ (gu_mk Δ (md_alias E)) args) ch v <-> eval_selmc gc_deps gc_stack h ch v.
Proof.
  intros * Hl Hch HE; split; intros H.
  - inversion H; subst; [ congruence |].
    match goal with Hs : eval_selm _ _ _ _ _ |- _ => inversion Hs; subst end; cbn in *; try lia.
    match goal with H1 : eval_modexp _ _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1); subst end.
    econstructor; eassumption.
  - inversion H; subst; [ congruence |].
    econstructor; [ eapply eval_selm_alias; eassumption | eassumption ].
Qed.

Lemma selc_member_ex : forall h ch0 ch, ch <> nil ->
    eval_selc gc_deps gc_stack (dm_member h ch0) ch (d_member h (ch0 ++ ch)).
Proof.
  intros h ch0 ch; revert ch0; induction ch as [| y ch IH]; intros ch0 Hch; [ congruence |].
  destruct ch as [| z ch].
  - constructor; constructor.
  - econstructor; [ constructor |].
    replace (ch0 ++ y :: z :: ch) with ((ch0 ++ y :: nil) ++ z :: ch) by (rewrite <- app_assoc; reflexivity).
    apply IH; discriminate.
Qed.

Lemma selmc_member_ex : forall h ch0 ch,
    eval_selmc gc_deps gc_stack (dm_member h ch0) ch (dm_member h (ch0 ++ ch)).
Proof.
  intros h ch0 ch; revert ch0; induction ch as [| y ch IH]; intros ch0.
  - rewrite app_nil_r; constructor.
  - econstructor; [ constructor |].
    replace (ch0 ++ y :: ch) with ((ch0 ++ y :: nil) ++ ch) by (rewrite <- app_assoc; reflexivity).
    apply IH.
Qed.

Lemma selc_unsat_ex : forall ρ U args ch,
    List.length args < List.length (gu_params U) -> ch <> nil ->
    eval_selc gc_deps gc_stack (dm_local ρ U args) ch (d_member (dm_local ρ U args) ch).
Proof.
  intros * Hl Hch; destruct ch as [| y ch]; [ congruence |].
  destruct ch as [| z ch].
  - constructor; constructor; exact Hl.
  - econstructor; [ apply eval_selm_unsat; exact Hl |].
    apply (selc_member_ex _ (y :: nil) (z :: ch)); discriminate.
Qed.

Lemma selmc_unsat_ex : forall ρ U args ch,
    List.length args < List.length (gu_params U) -> ch <> nil ->
    eval_selmc gc_deps gc_stack (dm_local ρ U args) ch (dm_member (dm_local ρ U args) ch).
Proof.
  intros * Hl Hch; destruct ch as [| y ch]; [ congruence |].
  econstructor; [ apply eval_selm_unsat; exact Hl |].
  apply (selmc_member_ex _ (y :: nil) ch).
Qed.

(** The submodules of global modules extend their telescopes, and global
    aliases are related at related arguments: the global context is valid. *)
Definition gchild_ok : Prop :=
  forall p T y T',
    gc_module gc_deps gc_stack p = Some (mr_body T) ->
    gc_module gc_deps gc_stack (path_app p (y :: nil)) = Some (mr_body T') ->
    exists Δ, T' = Δ ++ T.

Definition galias_ok : Prop :=
  forall p T y U ch args args',
    gc_module gc_deps gc_stack p = Some (mr_body T) ->
    gc_module gc_deps gc_stack (path_app p (y :: nil)) = Some (mr_alias U ch) ->
    per_gargs (rev T) nil nil args args' ->
    per_dmod (dm_local nil U args) (dm_local nil U args').

Lemma appm_ex : forall w a, nextparam w a -> forall c, exists w1, eval_appm gc_deps gc_stack w c w1.
Proof.
  induction 1 as [ρ U args A a Hn Ha | ρ Δ E args h a Hl HE Hnp IH | p T args A a Hm Hn Ha]; intros c.
  - assert (Hlt : List.length args < List.length (gu_params U))
      by (assert (Hn' : nth_error (rev (gu_params U)) (List.length args) <> None) by congruence;
          apply nth_error_Some in Hn'; rewrite length_rev in Hn'; exact Hn').
    destruct U as [Δ [Φ | E]]; cbn in Hlt; eexists; [ apply eval_appm_body | apply eval_appm_alias_unsat ]; exact Hlt.
  - destruct (IH c) as [w1 Hw1]; eexists; eapply eval_appm_alias; eassumption.
  - eexists; constructor.
Qed.

Lemma nextparam_local_lt : forall ρ U args a,
    nextparam (dm_local ρ U args) a -> List.length args <= List.length (gu_params U).
Proof.
  intros * H; inversion H; subst; cbn; [| lia ].
  match goal with Hn : nth_error _ _ = Some _ |- _ =>
    assert (Hn' : nth_error (rev (gu_params U)) (List.length args) <> None) by congruence;
    apply nth_error_Some in Hn'; rewrite length_rev in Hn'; lia end.
Qed.

Definition mrel (k : mkind) (E : relation domain) (w : dmod) (ch : list String.string) (w' : dmod) : Prop :=
  match k with
  | mk_term => exists v v', eval_selc gc_deps gc_stack w ch v /\ eval_selc gc_deps gc_stack w' ch v' /\ E v v'
  | mk_mod => exists v v', eval_selmc gc_deps gc_stack w ch v /\ eval_selmc gc_deps gc_stack w' ch v' /\ per_dmod v v'
  end.

(** ** Related Module Values Have Related Members *)
Lemma mtyped_rel : gparam_ok -> gchild_ok -> galias_ok ->
    forall w ch k a, mtyped w ch k a -> forall w' i E, per_dmod w w' -> per_univ_elem i E a a -> mrel k E w ch w'.
Proof.
  intros HGp HGc HGa.
  induction 1 as [ w ch k a0 a ρB B i in_rel Hgl Hnp Ha Hty IH
                 | w a i R Hs Ha
                 | ρ Δ Φ args x Φ' b A M ρ1 a a0 i R Hl Hx Hb HA Ha
                 | ρ Δ Φ args y Φ' Uy ρ1 ch k a Hl Hy Hb Hm IH
                 | ρ Δ E args h ch k a Hl HE Hm IH
                 | p T args x b A0 B f aA j E a a0 i R Hm Hl Hr Hf HaA HE Hff Ha0 Ha
                 | p args y T ch k a Hm Hty IH
                 | p args y U ch ch' k a Hm Hk Hty IH
                 | ρ U args ch0 ch k a Hl Hch0 Hk Hty IH ];
    intros w' i' E' Hw HE';
    assert (HPd : PER per_dmod) by typeclasses eauto.
  - (* still lacking an argument *)
    destruct (per_univ_elem_pi_inv HE') as (in' & out' & Hin' & Hout' & HEq).
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hin' Ha) as Ein.
    assert (HPin : PER in') by (eapply per_elem_PER; exact Hin').
    destruct Hgl as [(ρ & U & args & -> & Hlt) | (p & args & -> & -> & ->)].
    2: { exists (dm_global p args), w'; repeat split; [ constructor | constructor | exact Hw ]. }
    inversion Hw; subst.
    match goal with Hlt0 : per_ltele _ _ _ _ _ _ _ _ |- _ => rename Hlt0 into Hl end.
    destruct (per_ltele_lengths _ _ _ _ _ _ _ _ Hl) as [Hlen1 Hlen2]; rewrite !length_rev in Hlen1.
    assert (Hlt' : List.length args' < List.length (gu_params U')) by lia.
    pose proof (proj1 (per_univ_elem_sym _ _ _ _ Ha)) as Ha'.
    destruct k; cbn.
    + pose proof (var_per_elem 0 Hin') as Hc0.
      assert (Hch : ch <> nil).
      { destruct (Hout' _ _ Hc0) as [b0 b0' Hb0 _ Hbb0].
        destruct (appm_ex _ _ Hnp (⇑! a 0)) as [w1 Hw1].
        assert (Hww : per_dmod (dm_local ρ U args) (dm_local ρ U args))
          by (etransitivity; [ exact Hw | symmetry; exact Hw ]).
        assert (Hc0' : in_rel (⇑! a 0) (⇑! a 0)) by (apply Ein, Hc0).
        destruct (appm_rel HGp _ _ _ Hww Hnp _ _ _ _ _ _ Ha' Hc0' Hw1) as (w1' & Hw1' & Hw11).
        assert (Hb00 : per_univ_elem i' (out' _ _ Hc0) b0 b0)
          by (etransitivity; [ exact Hbb0 | symmetry; exact Hbb0 ]).
        destruct (IH _ _ _ Hc0' Hw1 Hb0 _ _ _ Hw11 Hb00) as (v1 & v1' & Hv1 & _ & _).
        intros ->; inversion Hv1. }
      exists (d_member (dm_local ρ U args) ch), (d_member (dm_local ρ' U' args') ch).
      split; [ apply selc_unsat_ex; assumption |]; split; [ apply selc_unsat_ex; assumption |].
      apply HEq; intros c c' Hcc.
      assert (Hcc0 : in' c c) by (etransitivity; [ exact Hcc | symmetry; exact Hcc ]).
      assert (Hcc1 : in_rel c c') by (apply Ein, Hcc).
      assert (Hcc2 : in_rel c c) by (apply Ein, Hcc0).
      destruct (appm_ex _ _ Hnp c) as [w1 Hw1].
      destruct (appm_rel HGp _ _ _ Hw Hnp _ _ _ _ _ _ Ha' Hcc1 Hw1) as (w1' & Hw1' & Hw11).
      destruct (Hout' _ _ Hcc) as [b b' Hb Hb' Hbb'].
      destruct (Hout' _ _ Hcc0) as [b1 b1' Hb1 Hb1' Hbb1].
      functional_eval_rewrite_clear.
      assert (Hbb : per_univ_elem i' (out' _ _ Hcc0) b b) by (etransitivity; [ exact Hbb1 | symmetry; exact Hbb1 ]).
      destruct (IH _ _ _ Hcc2 Hw1 Hb _ _ _ Hw11 Hbb) as (v1 & v1' & Hv1 & Hv1' & Hvv).
      econstructor; [ econstructor; eassumption | econstructor; eassumption |].
      apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hbb Hbb'); exact Hvv.
    + destruct ch as [| y ch].
      * exists (dm_local ρ U args), (dm_local ρ' U' args'); repeat split; [ constructor | constructor | exact Hw ].
      * exists (dm_member (dm_local ρ U args) (y :: ch)), (dm_member (dm_local ρ' U' args') (y :: ch)).
        repeat split; [ apply selmc_unsat_ex; [ assumption | discriminate ]
                      | apply selmc_unsat_ex; [ assumption | discriminate ] |].
        constructor; exact Hw.
  - (* saturated: the arity *)
    exists w, w'; repeat split; [ constructor | constructor | exact Hw ].
  - (* a definition *)
    inversion Hw; subst.
    match goal with Hlt0 : per_ltele _ _ _ _ _ _ _ _ |- _ => rename Hlt0 into Hlt end.
    destruct (per_ltele_lengths _ _ _ _ _ _ _ _ Hlt) as [Hlen1 Hlen2]; rewrite !length_rev in Hlen1.
    cbn [gu_params gu_def] in *.
    pose proof (per_ltele_full _ _ _ _ _ _ _ _ Hlt ltac:(rewrite length_rev; exact Hl)) as Hd.
    destruct U' as [Δ' D']; cbn [gu_params gu_def] in *.
    inversion Hd; subst.
    match goal with Hb0 : per_body _ _ _ _ |- _ => rename Hb0 into Hbd end.
    destruct (per_body_lookup_def _ _ _ _ _ _ _ _ _ _ Hbd Hx)
      as (Φ1' & b' & pv' & A' & M' & ρ1x & ρ1' & i0 & R0 & Hx' & Hb1 & Hb1' & [a1 a2 Ha1 Ha2 HR0] & [m m' Hm Hm' Hmm']).
    pose proof (functional_eval_benv _ _ _ _ Hb Hb1) as <-.
    functional_eval_rewrite_clear.
    exists m, m'; split; [ constructor; eapply eval_sel_body; eassumption |].
    split; [ constructor; eapply eval_sel_body; [ lia | eassumption | eassumption | eassumption ] |].
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HE' Ha) as E1.
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ Ha)) HR0) as E2.
    apply E1, E2, Hmm'.
  - (* a submodule *)
    inversion Hw; subst.
    match goal with Hlt0 : per_ltele _ _ _ _ _ _ _ _ |- _ => rename Hlt0 into Hlt end.
    destruct (per_ltele_lengths _ _ _ _ _ _ _ _ Hlt) as [Hlen1 Hlen2]; rewrite !length_rev in Hlen1.
    cbn [gu_params gu_def] in *.
    pose proof (per_ltele_full _ _ _ _ _ _ _ _ Hlt ltac:(rewrite length_rev; exact Hl)) as Hd.
    destruct U' as [Δ' D']; cbn [gu_params gu_def] in *.
    inversion Hd; subst.
    match goal with Hb0 : per_body _ _ _ _ |- _ => rename Hb0 into Hbd end.
    destruct (per_body_lookup_mod _ _ _ _ _ _ _ Hbd Hy) as (Φ1' & Uy' & ρ1x & ρ1' & Hy' & Hb1 & Hb1' & HU).
    pose proof (functional_eval_benv _ _ _ _ Hb Hb1) as <-.
    pose proof (IH _ _ _ HU HE') as Hr.
    destruct k; cbn in Hr |- *; destruct Hr as (v & v' & Hv & Hv' & Hvv); exists v, v'.
    + split; [ econstructor; [ eapply eval_selm_body; eassumption | eassumption ] |].
      split; [ econstructor; [ eapply eval_selm_body; [ lia | eassumption | eassumption ] | eassumption ] | exact Hvv ].
    + split; [ econstructor; [ eapply eval_selm_body; eassumption | eassumption ] |].
      split; [ econstructor; [ eapply eval_selm_body; [ lia | eassumption | eassumption ] | eassumption ] | exact Hvv ].
  - (* a saturated alias *)
    inversion Hw; subst.
    match goal with Hlt0 : per_ltele _ _ _ _ _ _ _ _ |- _ => rename Hlt0 into Hlt end.
    destruct (per_ltele_lengths _ _ _ _ _ _ _ _ Hlt) as [Hlen1 Hlen2]; rewrite !length_rev in Hlen1.
    cbn [gu_params gu_def] in *.
    pose proof (per_ltele_full _ _ _ _ _ _ _ _ Hlt ltac:(rewrite length_rev; exact Hl)) as Hd.
    destruct U' as [Δ' D']; cbn [gu_params gu_def] in *.
    inversion Hd; subst.
    match goal with
    | H1 : eval_modexp _ _ E _ ?h1, H3 : eval_modexp _ _ ?E' _ ?h', H5 : per_dmod ?h1 ?h' |- _ =>
        pose proof (functional_eval_modexp _ _ _ _ HE H1) as <-;
        rename H3 into HE'', H5 into Hhh
    end.
    pose proof (IH _ _ _ Hhh HE') as Hr.
    assert (Hl' : List.length args' = List.length Δ') by lia.
    destruct k; cbn in Hr |- *.
    + destruct Hr as (v & v' & Hv & Hv' & Hvv); exists v, v'.
      split; [ apply (selc_alias _ _ _ _ _ _ _ Hl HE); exact Hv |].
      split; [ apply (selc_alias _ _ _ _ _ _ _ Hl' HE''); exact Hv' | exact Hvv ].
    + destruct ch as [| y ch].
      * do 2 eexists; repeat split; [ constructor | constructor | exact Hw ].
      * destruct Hr as (v & v' & Hv & Hv' & Hvv); exists v, v'.
        assert (Hne : y :: ch <> nil) by discriminate.
        split; [ apply (selmc_alias _ _ _ _ _ _ _ Hl Hne HE); exact Hv |].
        split; [ apply (selmc_alias _ _ _ _ _ _ _ Hl' Hne HE''); exact Hv' | exact Hvv ].
  - (* a global definition *)
    inversion Hw; subst.
    match goal with Hm' : gc_module _ _ p = Some (mr_body ?T') |- _ =>
      rewrite Hm in Hm'; injection Hm' as <- end.
    match goal with Hg0 : per_gargs _ _ _ args _ |- _ => rename Hg0 into Hg end.
    rewrite <- (rev_involutive T) in HaA.
    destruct (apps_rel_gargs _ _ _ _ _ _ _ _ _ _ _ _ Hg HaA HaA HE Hff)
      as (v & v' & b1 & b1' & R1 & Hv & Hv' & Hb1 & Hb1' & HR1 & Hvv).
    rewrite skipn_rev, rev_involutive in Hb1.
    functional_eval_rewrite_clear.
    exists v, v'; split; [ constructor; econstructor; eassumption |].
    split; [ constructor; econstructor; eassumption |].
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HE' Ha) as E1.
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ Ha)) HR1) as E2.
    apply E1, E2, Hvv.
  - (* a global submodule *)
    inversion Hw; subst.
    match goal with Hm0 : gc_module _ _ p = Some (mr_body ?Tp) |- _ => rename Hm0 into Hmp end.
    match goal with Hg0 : per_gargs _ _ _ args _ |- _ => rename Hg0 into Hg end.
    destruct (HGc _ _ _ _ Hmp Hm) as [Δ ->].
    assert (Hw2 : per_dmod (dm_global (path_app p (y :: nil)) args) (dm_global (path_app p (y :: nil)) args'))
      by (econstructor; [ exact Hm | rewrite rev_app_distr; apply per_gargs_app; exact Hg ]).
    pose proof (IH _ _ _ Hw2 HE') as Hr.
    assert (Hna : forall U r, gc_module gc_deps gc_stack (path_app p (y :: nil)) <> Some (mr_alias U r))
      by (intros; rewrite Hm; discriminate).
    destruct k; cbn in Hr |- *; destruct Hr as (v & v' & Hv & Hv' & Hvv); exists v, v'.
    + repeat split; [ econstructor; [ apply eval_selm_global; exact Hna | exact Hv ]
                    | econstructor; [ apply eval_selm_global; exact Hna | exact Hv' ] | exact Hvv ].
    + repeat split; [ econstructor; [ apply eval_selm_global; exact Hna | exact Hv ]
                    | econstructor; [ apply eval_selm_global; exact Hna | exact Hv' ] | exact Hvv ].
  - (* a global alias *)
    inversion Hw; subst.
    match goal with Hm0 : gc_module _ _ p = Some (mr_body ?Tp) |- _ => rename Hm0 into Hmp end.
    match goal with Hg0 : per_gargs _ _ _ args _ |- _ => rename Hg0 into Hg end.
    pose proof (HGa _ _ _ _ _ _ _ Hmp Hm Hg) as Hw2.
    pose proof (IH _ _ _ Hw2 HE') as Hr.
    destruct k; cbn in Hr |- *; destruct Hr as (v & v' & Hv & Hv' & Hvv); exists v, v'.
    + specialize (Hk eq_refl).
      apply (eval_selc_app _ _ _ _ _ _ Hk) in Hv as (h1 & Hh1 & Hv).
      apply (eval_selc_app _ _ _ _ _ _ Hk) in Hv' as (h1' & Hh1' & Hv').
      repeat split; [ econstructor; [ eapply eval_selm_global_alias; eassumption | exact Hv ]
                    | econstructor; [ eapply eval_selm_global_alias; eassumption | exact Hv' ] | exact Hvv ].
    + apply eval_selmc_app in Hv as (h1 & Hh1 & Hv).
      apply eval_selmc_app in Hv' as (h1' & Hh1' & Hv').
      repeat split; [ econstructor; [ eapply eval_selm_global_alias; eassumption | exact Hv ]
                    | econstructor; [ eapply eval_selm_global_alias; eassumption | exact Hv' ] | exact Hvv ].
  - (* a member closure *)
    inversion Hw; subst.
    match goal with Hh0 : per_dmod (dm_local ρ U args) ?h' |- _ => rename Hh0 into Hh end.
    inversion Hh; subst.
    match goal with Hlt0 : per_ltele _ _ _ _ _ _ _ _ |- _ => rename Hlt0 into Hlt end.
    destruct (per_ltele_lengths _ _ _ _ _ _ _ _ Hlt) as [Hlen1 Hlen2]; rewrite !length_rev in Hlen1.
    assert (Hl' : List.length args' < List.length (gu_params U')) by lia.
    pose proof (IH _ _ _ Hh HE') as Hr.
    destruct k; cbn in Hr |- *; destruct Hr as (v & v' & Hv & Hv' & Hvv).
    + specialize (Hk eq_refl).
      rewrite (selc_unsat _ _ _ _ _ Hl Hv) in Hvv. rewrite (selc_unsat _ _ _ _ _ Hl' Hv') in Hvv.
      eexists; eexists; split; [ apply selc_member_ex; exact Hk |]; split; [ apply selc_member_ex; exact Hk | exact Hvv ].
    + assert (Hne : ch0 ++ ch <> nil) by (destruct ch0; [ congruence | discriminate ]).
      rewrite (selmc_unsat _ _ _ _ _ Hl Hne Hv) in Hvv. rewrite (selmc_unsat _ _ _ _ _ Hl' Hne Hv') in Hvv.
      eexists; eexists; split; [ apply selmc_member_ex |]; split; [ apply selmc_member_ex | exact Hvv ].
Qed.

End Fixed_GCtx.
