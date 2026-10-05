(** * Members of Module Values

    The members of a module value are typed at type values.  A module still
    lacking an argument types its members at [Π]-values whose domain is the
    type of that argument; a saturated body types a definition at its
    declared type, read under its self slot, the closure of the body before
    it; an alias types its members as its target does.  Related module values
    have related members ([mtyped_rel]). *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases UniverseCases SubstitutionCases LetCases UnitCases InstanceCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Lemma cons_neq_nil : forall {A : Type} (x : A) l, x :: l <> nil.
Proof. discriminate. Qed.

(** ** Closures of Units

    The closure of a unit over an environment with some arguments, read off
    the unit: a body closure or an alias closure.  [dm_of] is the closure
    with no argument yet. *)
Definition dm_local (ρ : env) (U : gunit) (args : list domain) : dmod :=
  match U with
  | gu_mk Δ (md_body Φ) => dm_body ρ Δ Φ args
  | gu_mk Δ (md_alias E) => dm_alias ρ Δ E args
  end.

(** The self slot of an entry of a body over [ρ], [Φ] the body before it. *)
Abbreviation self_env ρ Φ := (extend_env_mod ρ (dm_body ρ nil Φ nil)).

Lemma dm_of_local : forall ρ U, dm_of ρ U = dm_local ρ U nil.
Proof. intros ? [? []]; reflexivity. Qed.

Lemma dm_local_unsat : forall ρ U args,
    dm_unsat (dm_local ρ U args) <-> List.length args < List.length (gu_params U).
Proof. intros ? [? []] ?; reflexivity. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

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


(** The parts of related closures. *)
Lemma per_dmod_local : forall ρ U args ρ' U' args',
    per_ltele (rev (gu_params U)) ρ (gu_def U) (rev (gu_params U')) ρ' (gu_def U') args args' ->
    per_dmod (dm_local ρ U args) (dm_local ρ' U' args').
Proof.
  intros * H.
  destruct (per_ltele_kind _ _ _ _ _ _ _ _ H) as [(Φ & Φ' & HD & HD') | (E & E' & HD & HD')];
    destruct U as [Δ D], U' as [Δ' D']; cbn in *; subst; constructor; exact H.
Qed.

Lemma per_dmod_local_inv : forall ρ U args w',
    per_dmod (dm_local ρ U args) w' ->
    exists ρ' U' args', w' = dm_local ρ' U' args' /\
      per_ltele (rev (gu_params U)) ρ (gu_def U) (rev (gu_params U')) ρ' (gu_def U') args args' /\
      List.length (gu_params U) = List.length (gu_params U') /\ List.length args = List.length args'.
Proof.
  intros ? [Δ [Φ | E]] * H; cbn in H; inversion H; subst;
    match goal with Hl : per_ltele _ _ _ _ _ _ _ _ |- _ =>
      destruct (per_ltele_lengths _ _ _ _ _ _ _ _ Hl) as [H1 H2]; rewrite !length_rev in H1 end.
  - exists ρ', (gu_mk Δ' (md_body Φ')), args'; cbn; auto.
  - exists ρ', (gu_mk Δ' (md_alias E')), args'; cbn; auto.
Qed.

(** The definition named [x] of two related bodies. *)
Lemma per_body_lookup_def : forall ρ Φ ρ' Φ' x Φ1 pv A M,
    per_body ρ Φ ρ' Φ' ->
    gm_prefix_upto Φ x = Some (gm_ext Φ1 x (ge_def pv A (Some M))) ->
    exists Φ1' pv' A' M' i R,
      gm_prefix_upto Φ' x = Some (gm_ext Φ1' x (ge_def pv' A' (Some M'))) /\
      PER.Definitions.rel_typ i A (self_env ρ Φ1) A' (self_env ρ' Φ1') R /\
      PER.Definitions.rel_elem M (self_env ρ Φ1) M' (self_env ρ' Φ1') R.
Proof.
  intros * H; induction H; intros Hx; cbn in Hx |- *; try discriminate.
  - destruct (String.eqb x y) eqn:Ey; [ injection Hx as -> -> -> |].
    + apply String.eqb_eq in Ey; subst.
      do 6 eexists; split; [ reflexivity |]; eauto.
    + apply IHper_body; exact Hx.
  - destruct (String.eqb x y) eqn:Ey; [ discriminate |]; apply IHper_body; exact Hx.
Qed.

(** The submodule named [y] of two related bodies. *)
Lemma per_body_lookup_mod : forall ρ Φ ρ' Φ' y Φ1 pm Uy,
    per_body ρ Φ ρ' Φ' ->
    gm_prefix_upto Φ y = Some (gm_ext Φ1 y (ge_mod pm Uy)) ->
    exists Φ1' pm' Uy',
      gm_prefix_upto Φ' y = Some (gm_ext Φ1' y (ge_mod pm' Uy')) /\
      per_dmod (dm_of (self_env ρ Φ1) Uy) (dm_of (self_env ρ' Φ1') Uy').
Proof.
  intros * H; induction H; intros Hx; cbn in Hx |- *; try discriminate.
  - destruct (String.eqb y y0) eqn:Ey; [ discriminate |]; apply IHper_body; exact Hx.
  - destruct (String.eqb y y0) eqn:Ey; [ injection Hx as -> -> |].
    + apply String.eqb_eq in Ey; subst.
      do 3 eexists; split; [ reflexivity |]; eauto.
    + apply IHper_body; exact Hx.
Qed.

(** ** The Next Argument of a Module Value *)

Inductive nextparam : dmod -> domain -> Prop :=
| np_body : forall ρ Δ Φ args A a,
    nth_error (rev Δ) (List.length args) = Some (ce_ass A) ->
    ⟦ A ⟧ env_args ρ args ↘ a ->
    nextparam (dm_body ρ Δ Φ args) a
| np_alias_unsat : forall ρ Δ E args A a,
    nth_error (rev Δ) (List.length args) = Some (ce_ass A) ->
    ⟦ A ⟧ env_args ρ args ↘ a ->
    nextparam (dm_alias ρ Δ E args) a
| np_alias : forall ρ Δ E args h a,
    List.length args = List.length Δ ->
    eval_modexp gc_ctx E (env_args ρ args) h ->
    nextparam h a ->
    nextparam (dm_alias ρ Δ E args) a.

Lemma np_local : forall ρ U args A a,
    nth_error (rev (gu_params U)) (List.length args) = Some (ce_ass A) ->
    ⟦ A ⟧ env_args ρ args ↘ a ->
    nextparam (dm_local ρ U args) a.
Proof. intros ? [Δ [Φ | E]] *; cbn; [ apply np_body | apply np_alias_unsat ]. Qed.

Lemma nth_error_rev_lt : forall {A : Type} (l : list A) n x, nth_error (rev l) n = Some x -> n < List.length l.
Proof.
  intros * H; assert (Hn : nth_error (rev l) n <> None) by congruence.
  apply nth_error_Some in Hn; rewrite length_rev in Hn; exact Hn.
Qed.

Lemma eval_appm_local : forall ρ U args n,
    List.length args < List.length (gu_params U) ->
    $ᵐ| dm_local ρ U args & n | gc_ctx ↘ dm_local ρ U (args ++ n :: nil).
Proof. intros ? [Δ [Φ | E]] * Hl; cbn in *; constructor; exact Hl. Qed.

Lemma eval_appm_local_inv : forall ρ U args n r,
    $ᵐ| dm_local ρ U args & n | gc_ctx ↘ r ->
    (List.length args < List.length (gu_params U) /\ r = dm_local ρ U (args ++ n :: nil)) \/
    (exists Δ E h, U = gu_mk Δ (md_alias E) /\ List.length args = List.length Δ /\
       ⟦ E ⟧ᵐ gc_ctx ⍮ env_args ρ args ↘ h /\ $ᵐ| h & n | gc_ctx ↘ r).
Proof.
  intros ? [Δ [Φ | E]] * H; cbn in H; inversion H; subst; cbn; eauto 10.
Qed.

(** ** Saturated Module Values *)

Inductive msat : dmod -> Prop :=
| ms_body : forall ρ Δ Φ args,
    List.length args = List.length Δ -> msat (dm_body ρ Δ Φ args)
| ms_alias : forall ρ Δ E args h,
    List.length args = List.length Δ ->
    eval_modexp gc_ctx E (env_args ρ args) h -> msat h ->
    msat (dm_alias ρ Δ E args).

(** ** Typed Members

    [mtyped w ch k a]: the chain [ch] of [w] is a member of kind [k] at the
    type value [a] (for [k = mk_mod], the arity of the submodule).  A value
    lacking an argument types its members at a [Π] over that argument. *)

Inductive mtyped : dmod -> list String.string -> mkind -> domain -> Prop :=
| mty_pi : forall w ch k a0 a ρB B i in_rel,
    (exists ρ U args, w = dm_local ρ U args /\ List.length args < List.length (gu_params U)) ->
    nextparam w a0 -> per_univ_elem i in_rel a a0 ->
    (forall c w1 b, in_rel c c -> eval_appm gc_ctx w c w1 -> ⟦ B ⟧ ρB ↦ c ↘ b -> mtyped w1 ch k b) ->
    mtyped w ch k (Πᵈ a ρB B)
| mty_top : forall w a i R, msat w -> per_univ_elem i R a ⊤ᵈ -> mtyped w nil mk_mod a
| mty_def : forall ρ Δ Φ args x Φ' pv A M a a0 i R,
    List.length args = List.length Δ ->
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def pv A (Some M))) ->
    ⟦ A ⟧ self_env (env_args ρ args) Φ' ↘ a0 -> per_univ_elem i R a a0 ->
    mtyped (dm_body ρ Δ Φ args) (x :: nil) mk_term a
| mty_sub : forall ρ Δ Φ args y Φ' pm Uy ch k a,
    List.length args = List.length Δ ->
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
    mtyped (dm_of (self_env (env_args ρ args) Φ') Uy) ch k a ->
    mtyped (dm_body ρ Δ Φ args) (y :: ch) k a
| mty_alias : forall ρ Δ E args h ch k a,
    List.length args = List.length Δ ->
    eval_modexp gc_ctx E (env_args ρ args) h -> mtyped h ch k a ->
    mtyped (dm_alias ρ Δ E args) ch k a
| mty_member : forall ρ U args ch0 ch k a a1,
    List.length args < List.length (gu_params U) -> nextparam (dm_local ρ U args) a1 ->
    ch0 <> nil -> (k = mk_term -> ch <> nil) ->
    mtyped (dm_local ρ U args) (ch0 ++ ch) k a -> mtyped (dm_member (dm_local ρ U args) ch0) ch k a.

(** ** Applying Related Module Values *)

Lemma appm_rel : forall w w' a, per_dmod w w' -> nextparam w a ->
    forall i E b c c' r, per_univ_elem i E a b -> E c c' -> $ᵐ| w & c | gc_ctx ↘ r ->
    exists r', $ᵐ| w' & c' | gc_ctx ↘ r' /\ per_dmod r r'.
Proof.
  intros * Hw Hnp; revert w' Hw.
  assert (Hloc : forall ρ U args A a w', per_dmod (dm_local ρ U args) w' ->
             nth_error (rev (gu_params U)) (List.length args) = Some (ce_ass A) ->
             ⟦ A ⟧ env_args ρ args ↘ a ->
             forall i E b c c' r, per_univ_elem i E a b -> E c c' -> $ᵐ| dm_local ρ U args & c | gc_ctx ↘ r ->
             exists r', $ᵐ| w' & c' | gc_ctx ↘ r' /\ per_dmod r r').
  { intros * Hw Hn Ha * HR Hcc Hr.
    destruct (per_dmod_local_inv _ _ _ _ Hw) as (ρ' & U' & args' & -> & Hl & Hlen1 & Hlen2).
    destruct (per_ltele_supply _ _ _ _ _ _ _ _ _ Hl Hn) as (i0 & R0 & A' & [a1 a2 Ha1 Ha2 HR0] & Hsup).
    pose proof (functional_eval_exp _ _ _ _ Ha Ha1) as <-.
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR HR0) as EE.
    pose proof (Hsup _ _ (proj1 (EE _ _) Hcc)) as Hl'.
    pose proof (nth_error_rev_lt _ _ _ Hn) as Hlt.
    destruct (eval_appm_local_inv _ _ _ _ _ Hr) as [[_ ->] | (Δ0 & E0 & h & -> & Hl0 & _)]; [| cbn in Hlt; lia ].
    eexists; split; [ apply eval_appm_local; lia | apply per_dmod_local; exact Hl' ]. }
  induction Hnp as [ρ Δ Φ args A a Hn Ha | ρ Δ E args A a Hn Ha | ρ Δ E args h a Hl HE Hnp IH];
    intros w' Hw.
  - exact (Hloc ρ (gu_mk Δ (md_body Φ)) args A a w' Hw Hn Ha).
  - exact (Hloc ρ (gu_mk Δ (md_alias E)) args A a w' Hw Hn Ha).
  - intros * HR Hcc Hr.
    inversion Hw; subst.
    match goal with Hlt0 : per_ltele _ _ _ _ _ _ _ _ |- _ => rename Hlt0 into Hlt end.
    destruct (per_ltele_lengths _ _ _ _ _ _ _ _ Hlt) as [Hlen1 Hlen2].
    rewrite !length_rev in Hlen1.
    pose proof (per_ltele_full _ _ _ _ _ _ _ _ Hlt ltac:(rewrite length_rev; exact Hl)) as Hd.
    inversion Hd; subst.
    inversion Hr; subst; try lia.
    match goal with
    | H1 : eval_modexp _ E _ ?h0, H5 : per_dmod ?h0 ?h', H3 : eval_modexp _ ?E' _ ?h',
      H10 : eval_modexp _ E _ ?h1, H11 : eval_appm _ ?h1 c r |- _ =>
        pose proof (functional_eval_modexp _ _ _ _ HE H1) as <-;
        pose proof (functional_eval_modexp _ _ _ _ HE H10) as <-;
        destruct (IH _ H5 _ _ _ _ _ _ HR Hcc H11) as (r' & Hr' & Hrr');
        exists r'; split; [ eapply eval_appm_alias; [ lia | exact H3 | exact Hr' ] | exact Hrr' ]
    end.
Qed.

(** ** Selections from Module Values Still Lacking Arguments *)

Lemma selmc_member : forall w ch0 ch v,
    dm_member w ch0 ·ₘ* ch gc_ctx ↘ v -> v = dm_member w (ch0 ++ ch).
Proof.
  intros w ch0 ch; revert ch0; induction ch as [| y ch IH]; intros * H; inversion H; subst.
  - rewrite app_nil_r; reflexivity.
  - match goal with Hs : eval_selm _ _ _ _ |- _ => inversion Hs; subst end; [ contradiction |].
    rewrite (IH _ _ ltac:(eassumption)), <- app_assoc; reflexivity.
Qed.

Lemma selc_member : forall w ch0 ch v,
    dm_member w ch0 ·ₜ* ch gc_ctx ↘ v -> v = d_member w (ch0 ++ ch).
Proof.
  intros w ch0 ch; revert ch0; induction ch as [| y ch IH]; intros * H; inversion H; subst.
  - match goal with Hs : eval_sel _ _ _ _ |- _ => inversion Hs; subst end; [ contradiction | reflexivity ].
  - match goal with Hs : eval_selm _ _ _ _ |- _ => inversion Hs; subst end; [ contradiction |].
    rewrite (IH _ _ ltac:(eassumption)), <- app_assoc; reflexivity.
Qed.

Lemma selm_unsat : forall ρ U args y h,
    List.length args < List.length (gu_params U) ->
    dm_local ρ U args ·ₘ y gc_ctx ↘ h -> h = dm_member (dm_local ρ U args) (y :: nil).
Proof. intros ? [Δ [Φ | E]] * Hl H; cbn in *; inversion H; subst; cbn in *; [ reflexivity | lia | reflexivity | lia ]. Qed.

Lemma sel_unsat : forall ρ U args x v,
    List.length args < List.length (gu_params U) ->
    dm_local ρ U args ·ₜ x gc_ctx ↘ v -> v = d_member (dm_local ρ U args) (x :: nil).
Proof. intros ? [Δ [Φ | E]] * Hl H; cbn in *; inversion H; subst; cbn in *; [ reflexivity | lia | reflexivity | lia ]. Qed.

Lemma selc_unsat : forall ρ U args ch v,
    List.length args < List.length (gu_params U) ->
    dm_local ρ U args ·ₜ* ch gc_ctx ↘ v -> v = d_member (dm_local ρ U args) ch.
Proof.
  intros * Hl H; inversion H; subst.
  - eapply sel_unsat; eassumption.
  - match goal with Hs : eval_selm _ _ _ ?h1 |- _ => pose proof (selm_unsat _ _ _ _ _ Hl Hs); subst end.
    rewrite (selc_member _ _ _ _ ltac:(eassumption)); reflexivity.
Qed.

Lemma selmc_unsat : forall ρ U args ch v,
    List.length args < List.length (gu_params U) -> ch <> nil ->
    dm_local ρ U args ·ₘ* ch gc_ctx ↘ v -> v = dm_member (dm_local ρ U args) ch.
Proof.
  intros * Hl Hch H; inversion H; subst; [ congruence |].
  match goal with Hs : eval_selm _ _ _ ?h1 |- _ => pose proof (selm_unsat _ _ _ _ _ Hl Hs); subst end.
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

(** A saturated alias selects as its target. *)
Lemma selc_alias : forall ρ Δ E args h ch v,
    List.length args = List.length Δ ->
    ⟦ E ⟧ᵐ gc_ctx ⍮ env_args ρ args ↘ h ->
    dm_alias ρ Δ E args ·ₜ* ch gc_ctx ↘ v <-> h ·ₜ* ch gc_ctx ↘ v.
Proof.
  intros * Hl HE; split; intros H.
  - inversion H; subst.
    + match goal with Hs : eval_sel _ _ _ _ |- _ => inversion Hs; subst end; cbn in *; try lia.
      match goal with H1 : eval_modexp _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1); subst end.
      constructor; assumption.
    + match goal with Hs : eval_selm _ _ _ _ |- _ => inversion Hs; subst end; cbn in *; try lia.
      match goal with H1 : eval_modexp _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1); subst end.
      econstructor; eassumption.
  - inversion H; subst.
    + constructor; eapply eval_sel_alias; eassumption.
    + econstructor; [ eapply eval_selm_alias; eassumption | eassumption ].
Qed.

Lemma selmc_alias : forall ρ Δ E args h ch v,
    List.length args = List.length Δ -> ch <> nil ->
    ⟦ E ⟧ᵐ gc_ctx ⍮ env_args ρ args ↘ h ->
    dm_alias ρ Δ E args ·ₘ* ch gc_ctx ↘ v <-> h ·ₘ* ch gc_ctx ↘ v.
Proof.
  intros * Hl Hch HE; split; intros H.
  - inversion H; subst; [ congruence |].
    match goal with Hs : eval_selm _ _ _ _ |- _ => inversion Hs; subst end; cbn in *; try lia.
    match goal with H1 : eval_modexp _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1); subst end.
    econstructor; eassumption.
  - inversion H; subst; [ congruence |].
    econstructor; [ eapply eval_selm_alias; eassumption | eassumption ].
Qed.

Lemma selc_member_ex : forall h ch0 ch, ch <> nil ->
    dm_member h ch0 ·ₜ* ch gc_ctx ↘ d_member h (ch0 ++ ch).
Proof.
  intros h ch0 ch; revert ch0; induction ch as [| y ch IH]; intros ch0 Hch; [ congruence |].
  destruct ch as [| z ch].
  - apply eval_selc_one, eval_sel_member.
  - econstructor; [ apply eval_selm_member |].
    replace (ch0 ++ y :: z :: ch) with ((ch0 ++ y :: nil) ++ z :: ch) by (rewrite <- app_assoc; reflexivity).
    apply IH; discriminate.
Qed.

Lemma selmc_member_ex : forall h ch0 ch,
    dm_member h ch0 ·ₘ* ch gc_ctx ↘ dm_member h (ch0 ++ ch).
Proof.
  intros h ch0 ch; revert ch0; induction ch as [| y ch IH]; intros ch0.
  - rewrite app_nil_r; constructor.
  - econstructor; [ apply eval_selm_member |].
    replace (ch0 ++ y :: ch) with ((ch0 ++ y :: nil) ++ ch) by (rewrite <- app_assoc; reflexivity).
    apply IH.
Qed.

Lemma selc_unsat_ex : forall ρ U args ch,
    List.length args < List.length (gu_params U) -> ch <> nil ->
    dm_local ρ U args ·ₜ* ch gc_ctx ↘ d_member (dm_local ρ U args) ch.
Proof.
  intros * Hl Hch; apply (proj2 (dm_local_unsat ρ U args)) in Hl; destruct ch as [| y ch]; [ congruence |].
  destruct ch as [| z ch].
  - constructor; constructor; exact Hl.
  - econstructor; [ apply eval_selm_unsat; exact Hl |].
    apply (selc_member_ex _ (y :: nil) (z :: ch)); discriminate.
Qed.

Lemma selmc_unsat_ex : forall ρ U args ch,
    List.length args < List.length (gu_params U) -> ch <> nil ->
    dm_local ρ U args ·ₘ* ch gc_ctx ↘ dm_member (dm_local ρ U args) ch.
Proof.
  intros * Hl Hch; apply (proj2 (dm_local_unsat ρ U args)) in Hl; destruct ch as [| y ch]; [ congruence |].
  econstructor; [ apply eval_selm_unsat; exact Hl |].
  apply (selmc_member_ex _ (y :: nil) ch).
Qed.

Lemma appm_ex : forall w a, nextparam w a -> forall c, exists w1, $ᵐ| w & c | gc_ctx ↘ w1.
Proof.
  induction 1 as [ρ Δ Φ args A a Hn Ha | ρ Δ E args A a Hn Ha | ρ Δ E args h a Hl HE Hnp IH]; intros c.
  - eexists; apply eval_appm_body; exact (nth_error_rev_lt _ _ _ Hn).
  - eexists; apply eval_appm_alias_unsat; exact (nth_error_rev_lt _ _ _ Hn).
  - destruct (IH c) as [w1 Hw1]; eexists; eapply eval_appm_alias; eassumption.
Qed.

Lemma nextparam_local_lt : forall ρ U args a,
    nextparam (dm_local ρ U args) a -> List.length args <= List.length (gu_params U).
Proof.
  intros ? [Δ [Φ | E]] * H; cbn in *; inversion H; subst; cbn;
    try match goal with Hn : nth_error _ _ = Some _ |- _ => pose proof (nth_error_rev_lt _ _ _ Hn) end; lia.
Qed.

Definition mrel (k : mkind) (E : relation domain) (w : dmod) (ch : list String.string) (w' : dmod) : Prop :=
  match k with
  | mk_term => exists v v', eval_selc gc_ctx w ch v /\ eval_selc gc_ctx w' ch v' /\ E v v'
  | mk_mod => exists v v', eval_selmc gc_ctx w ch v /\ eval_selmc gc_ctx w' ch v' /\ per_dmod v v'
  end.

(** The body of a saturated body closure, against a related one. *)
Lemma per_dmod_body_sat : forall ρ Δ Φ args w',
    per_dmod (dm_body ρ Δ Φ args) w' -> List.length args = List.length Δ ->
    exists ρ' Δ' Φ' args', w' = dm_body ρ' Δ' Φ' args' /\ List.length args' = List.length Δ' /\
      per_body (env_args ρ args) Φ (env_args ρ' args') Φ'.
Proof.
  intros * Hw Hl; inversion Hw; subst.
  match goal with Hlt0 : per_ltele _ _ _ _ _ _ _ _ |- _ => rename Hlt0 into Hlt end.
  destruct (per_ltele_lengths _ _ _ _ _ _ _ _ Hlt) as [Hlen1 Hlen2]; rewrite !length_rev in Hlen1.
  pose proof (per_ltele_full _ _ _ _ _ _ _ _ Hlt ltac:(rewrite length_rev; exact Hl)) as Hd.
  inversion Hd; subst.
  do 4 eexists; split; [ reflexivity | split; [ lia | eassumption ] ].
Qed.

Lemma per_dmod_alias_sat : forall ρ Δ E args w',
    per_dmod (dm_alias ρ Δ E args) w' -> List.length args = List.length Δ ->
    exists ρ' Δ' E' args' h h', w' = dm_alias ρ' Δ' E' args' /\ List.length args' = List.length Δ' /\
      ⟦ E ⟧ᵐ gc_ctx ⍮ env_args ρ args ↘ h /\ ⟦ E' ⟧ᵐ gc_ctx ⍮ env_args ρ' args' ↘ h' /\ per_dmod h h'.
Proof.
  intros * Hw Hl; inversion Hw; subst.
  match goal with Hlt0 : per_ltele _ _ _ _ _ _ _ _ |- _ => rename Hlt0 into Hlt end.
  destruct (per_ltele_lengths _ _ _ _ _ _ _ _ Hlt) as [Hlen1 Hlen2]; rewrite !length_rev in Hlen1.
  pose proof (per_ltele_full _ _ _ _ _ _ _ _ Hlt ltac:(rewrite length_rev; exact Hl)) as Hd.
  inversion Hd; subst.
  do 6 eexists; split; [ reflexivity | split; [ lia | split; [ eassumption | split; eassumption ] ] ].
Qed.

(** ** Related Module Values Have Related Members *)
Lemma mtyped_rel :
    forall w ch k a, mtyped w ch k a -> forall w' i E, per_dmod w w' -> per_univ_elem i E a a -> mrel k E w ch w'.
Proof.
  induction 1 as [ w ch k a0 a ρB B i in_rel Hgl Hnp Ha Hty IH
                 | w a i R Hs Ha
                 | ρ Δ Φ args x Φ' pv A M a a0 i R Hl Hx HA Ha
                 | ρ Δ Φ args y Φ' pm Uy ch k a Hl Hy Hm IH
                 | ρ Δ E args h ch k a Hl HE Hm IH
                 | ρ U args ch0 ch k a a1 Hl Hnp1 Hch0 Hk Hty IH ];
    intros w' i' E' Hw HE';
    assert (HPd : PER per_dmod) by typeclasses eauto.
  - (* still lacking an argument *)
    destruct (per_univ_elem_pi_inv HE') as (in' & out' & Hin' & Hout' & HEq).
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hin' Ha) as Ein.
    assert (HPin : PER in') by (eapply per_elem_PER; exact Hin').
    destruct Hgl as (ρ & U & args & -> & Hlt).
    destruct (per_dmod_local_inv _ _ _ _ Hw) as (ρ' & U' & args' & -> & Hl & Hlen1 & Hlen2).
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
        destruct (appm_rel _ _ _ Hww Hnp _ _ _ _ _ _ Ha' Hc0' Hw1) as (w1' & Hw1' & Hw11).
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
      destruct (appm_rel _ _ _ Hw Hnp _ _ _ _ _ _ Ha' Hcc1 Hw1) as (w1' & Hw1' & Hw11).
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
    destruct (per_dmod_body_sat _ _ _ _ _ Hw Hl) as (ρ' & Δ' & Φ'' & args' & -> & Hl' & Hbd).
    destruct (per_body_lookup_def _ _ _ _ _ _ _ _ _ Hbd Hx)
      as (Φ1' & pv' & A' & M' & i0 & R0 & Hx' & [a1 a2 Ha1 Ha2 HR0] & [m m' Hm Hm' Hmm']).
    functional_eval_rewrite_clear.
    exists m, m'; split; [ constructor; eapply eval_sel_body; eassumption |].
    split; [ constructor; eapply eval_sel_body; eassumption |].
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HE' Ha) as E1.
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ Ha)) HR0) as E2.
    apply E1, E2, Hmm'.
  - (* a submodule *)
    destruct (per_dmod_body_sat _ _ _ _ _ Hw Hl) as (ρ' & Δ' & Φ'' & args' & -> & Hl' & Hbd).
    destruct (per_body_lookup_mod _ _ _ _ _ _ _ _ Hbd Hy) as (Φ1' & pm' & Uy' & Hy' & HU).
    pose proof (IH _ _ _ HU HE') as Hr.
    destruct k; cbn in Hr |- *; destruct Hr as (v & v' & Hv & Hv' & Hvv); exists v, v'.
    + split; [ econstructor; [ eapply eval_selm_body; eassumption | eassumption ] |].
      split; [ econstructor; [ eapply eval_selm_body; eassumption | eassumption ] | exact Hvv ].
    + split; [ econstructor; [ eapply eval_selm_body; eassumption | eassumption ] |].
      split; [ econstructor; [ eapply eval_selm_body; eassumption | eassumption ] | exact Hvv ].
  - (* a saturated alias *)
    destruct (per_dmod_alias_sat _ _ _ _ _ Hw Hl) as (ρ' & Δ' & E'' & args' & h0 & h' & -> & Hl' & HE0 & HE'' & Hhh).
    pose proof (functional_eval_modexp _ _ _ _ HE HE0) as <-.
    pose proof (IH _ _ _ Hhh HE') as Hr.
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
  - (* a member closure *)
    inversion Hw; subst.
    match goal with Hh0 : per_dmod (dm_local ρ U args) ?h' |- _ => rename Hh0 into Hh end.
    destruct (per_dmod_local_inv _ _ _ _ Hh) as (ρ' & U' & args' & -> & Hlt & Hlen1 & Hlen2).
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

(** ** Selecting along a Typed Chain *)

Lemma mtyped_selmc : forall w chain k a, mtyped w chain k a ->
    forall pre ch, chain = pre ++ ch -> (k = mk_term -> ch <> nil) ->
    forall w1, w ·ₘ* pre gc_ctx ↘ w1 -> mtyped w1 ch k a.
Proof.
  induction 1 as [ w chain k a0 a ρB B i in_rel Hgl Hnp Ha Hty IH
                 | w a i R Hs Ha
                 | ρ Δ Φ args x Φ' pv A M a a0 i R Hl Hx HA Ha
                 | ρ Δ Φ args y Φ' pm Uy chain k a Hl Hy Hm IH
                 | ρ Δ E args h chain k a Hl HE Hm IH
                 | ρ U args ch0 chain k a a1 Hl Hnp1 Hch0 Hk Hty IH ];
    intros pre ch Heq Hch w1 Hw1.
  - destruct pre as [| y pre]; cbn in Heq; subst.
    + inversion Hw1; subst; econstructor; eassumption.
    + destruct Hgl as (ρ & U & args & -> & Hlt).
      rewrite (selmc_unsat _ _ _ _ _ Hlt (cons_neq_nil _ _) Hw1).
      eapply mty_member; [ exact Hlt | exact Hnp | discriminate | exact Hch |].
      eapply mty_pi; [ do 3 eexists; split; [ reflexivity | exact Hlt ] | exact Hnp | exact Ha | exact Hty ].
  - destruct pre; [| discriminate ]; cbn in Heq; subst.
    inversion Hw1; subst; econstructor; eassumption.
  - destruct pre as [| z pre]; cbn in Heq; subst.
    + inversion Hw1; subst; econstructor; eassumption.
    + injection Heq as -> Heq; destruct pre; [| discriminate ]; cbn in Heq; subst.
      exfalso; apply Hch; reflexivity.
  - destruct pre as [| z pre]; cbn in Heq.
    + subst; inversion Hw1; subst; econstructor; eassumption.
    + injection Heq as -> Heq.
      inversion Hw1; subst.
      match goal with Hs : eval_selm _ _ _ _ |- _ => inversion Hs; subst end; cbn in *; try lia.
      match goal with Hp : gm_prefix_upto Φ _ = Some (gm_ext _ _ (ge_mod _ ?Uy')) |- _ =>
        rewrite Hy in Hp; injection Hp as <- <-; subst end.
      eapply IH; [ reflexivity | exact Hch | eassumption ].
  - destruct pre as [| z pre]; cbn in Heq.
    + subst; inversion Hw1; subst; eapply mty_alias; eassumption.
    + subst; apply (selmc_alias _ _ _ _ _ _ _ Hl (cons_neq_nil _ _) HE) in Hw1.
      eapply (IH (_ :: _) ch); [ reflexivity | exact Hch | exact Hw1 ].
  - destruct pre as [| z pre]; cbn in Heq; subst.
    + inversion Hw1; subst; eapply mty_member; eassumption.
    + rewrite (selmc_member _ _ _ _ Hw1).
      eapply mty_member; [ exact Hl | exact Hnp1 | destruct ch0; [ congruence | discriminate ] | exact Hch |].
      rewrite <- app_assoc; exact Hty.
Qed.

(** ** Applying a Typed Module Value *)

Lemma mtyped_app :
    forall w ch k a, mtyped w ch k a ->
    forall a1 ρB B, a = Πᵈ a1 ρB B ->
    (exists a0, nextparam w a0) \/ (exists h ch0, w = dm_member h ch0) ->
    forall i' Ein c w1 b, per_univ_elem i' Ein a1 a1 -> Ein c c ->
    $ᵐ| w & c | gc_ctx ↘ w1 -> ⟦ B ⟧ ρB ↦ c ↘ b -> mtyped w1 ch k b.
Proof.
  induction 1 as [ w ch k a0 a ρB B i in_rel Hgl Hnp Ha Hty IH
                 | w a i R Hs Ha
                 | ρ Δ Φ args x Φ' pv A M a a0 i R Hl Hx HA Ha
                 | ρ Δ Φ args y Φ' pm Uy ch k a Hl Hy Hm IH
                 | ρ Δ E args h ch k a Hl HE Hm IH
                 | ρ U args ch0 ch k a a1 Hl Hnp1 Hch0 Hk Hty IH ];
    intros a1' ρB' B' Heq Hun i' Ein c w1 b' Hin Hc Hw1 Hb'.
  - injection Heq as <- <- <-.
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hin Ha) as EE.
    eapply Hty; [ apply EE, Hc | exact Hw1 | exact Hb' ].
  - subst; basic_invert_per_univ_elem Ha.
  - destruct Hun as [(a2 & Hn) | (h0 & ch0 & Hh)]; [| discriminate ].
    inversion Hn; subst;
      match goal with Hn' : nth_error _ _ = Some _ |- _ => pose proof (nth_error_rev_lt _ _ _ Hn'); lia end.
  - destruct Hun as [(a2 & Hn) | (h0 & ch0 & Hh)]; [| discriminate ].
    inversion Hn; subst;
      match goal with Hn' : nth_error _ _ = Some _ |- _ => pose proof (nth_error_rev_lt _ _ _ Hn'); lia end.
  - destruct Hun as [(a2 & Hn) | (h0 & ch0 & Hh)]; [| discriminate ].
    inversion Hn; subst.
    + match goal with Hn' : nth_error _ _ = Some _ |- _ => pose proof (nth_error_rev_lt _ _ _ Hn'); lia end.
    + match goal with H1 : eval_modexp _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
      inversion Hw1; subst; try lia.
      match goal with H1 : eval_modexp _ E _ ?h1 |- _ => pose proof (functional_eval_modexp _ _ _ _ HE H1) as <- end.
      eapply IH; [ reflexivity | left; eexists; eassumption | exact Hin | exact Hc | eassumption | exact Hb' ].
  - inversion Hw1; subst.
    match goal with H1 : eval_appm _ (dm_local ρ U args) c ?h1, H4 : eval_selmc _ ?h1 ch0 w1 |- _ =>
      exact (mtyped_selmc _ _ _ _
               (IH _ _ _ eq_refl (or_introl (ex_intro _ _ Hnp1)) _ _ _ _ _ Hin Hc H1 Hb') ch0 ch eq_refl Hk _ H4) end.
Qed.

End Fixed_GCtx.
