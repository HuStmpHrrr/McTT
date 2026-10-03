(** * Valid Global Modules

    The members of a closed global module are read in its body, so a path to
    it is valid in its members ([gpath_at]) once its body is valid: its
    telescope is a semantically well-formed context, its definitions are valid
    at their types, and its aliases' units are valid. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import MemberLemmas GlobalModules.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases UniverseCases SubstitutionCases LetCases TrueFalseCases UnitCases InstanceCases
  MemberCases MemberTyping MemberReps MemberSem ModexpCases PathCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Arguments Related at a Telescope *)

Lemma gargs_rel : forall ts ρ ρ' args args', per_gargs ts ρ ρ' args args' ->
    forall Tb Rb, EF Tb ≈ Tb ∈ per_ctx_env ↘ Rb -> Rb ρ ρ' -> ⊨ rev ts ++ Tb ->
    exists R, EF rev (firstn (List.length args) ts) ++ Tb ≈ rev (firstn (List.length args) ts) ++ Tb ∈ per_ctx_env ↘ R /\
      R (env_args ρ args) (env_args ρ' args').
Proof.
  induction 1 as [ts ρ ρ' | i A ρ ρ' a a' ts args args' R1 HA Ha Hg IH]; intros Tb Rb HTb Hρ HC; cbn [firstn List.length rev app].
  - exists Rb; split; assumption.
  - cbn [rev] in HC; rewrite <- app_assoc in HC; cbn [app] in HC.
    destruct (sem_ctx_ass_inv (sem_ctx_app_r _ _ HC)) as [j HAv].
    pose proof (per_ctx_env_of_typ HTb HAv) as HTb'.
    assert (Hρ' : per_env_extend A A Rb (ρ ↦ a) (ρ' ↦ a')).
    { split; [ exact Hρ |].
      destruct HA as [x x' Hx Hx' Hxx]; eapply per_head_of; [ exact Hx | exact Hx' | exact Hxx | exact Ha ]. }
    destruct (IH _ _ HTb' Hρ' HC) as (R & HR & HRρ).
    exists R; rewrite <- app_assoc; cbn [app]; split; [ exact HR | exact HRρ ].
Qed.

Lemma per_ctx_env_nil_true : EF ⋅ ≈ ⋅ ∈ per_ctx_env ↘ (fun _ _ => True).
Proof. apply per_ctx_env_nil; reflexivity. Qed.

(** The parameters of a global module whose telescope is valid. *)
Lemma gparam_of_tele : forall qp T, ⊨ T -> gc_module gc_deps gc_stack qp = Some (mr_body T) -> gparam_at qp.
Proof.
  intros * HT Hq T' args args' A Hm Hg Hn.
  rewrite Hq in Hm; injection Hm as <-.
  destruct (nth_error_split _ _ Hn) as (l1 & l2 & Hl & Hlen).
  assert (HT' : ⊨ rev (rev T) ++ ⋅) by (rewrite rev_involutive, app_nil_r; exact HT).
  destruct (gargs_rel _ _ _ _ _ Hg _ _ per_ctx_env_nil_true I HT') as (R & HR & Hρ).
  assert (Hf : firstn (List.length args) (rev T) = l1)
    by (rewrite Hl, <- Hlen, firstn_app, Nat.sub_diag, firstn_all; cbn; rewrite app_nil_r; reflexivity).
  rewrite Hf, app_nil_r in HR.
  assert (HTs : T = rev l2 ++ ce_ass A :: rev l1)
    by (rewrite <- (rev_involutive T), Hl, rev_app_distr; cbn; rewrite <- app_assoc; reflexivity).
  rewrite HTs in HT.
  destruct (sem_ctx_ass_inv (sem_ctx_app_r _ _ HT)) as [i HA].
  destruct (rel_exp_of_typ_inversion_simple_at HR HA _ _ Hρ) as (a & a' & Ha & Ha' & [RA HRA]).
  exists i, RA; econstructor; eassumption.
Qed.

(** Supplying arguments related at a telescope to a closure still missing
    them. *)
Lemma ltele_supply_gargs : forall ts ρ ρ' args args', per_gargs ts ρ ρ' args args' ->
    forall rest D D', per_ltele (ts ++ rest) ρ D (ts ++ rest) ρ' D' nil nil ->
    per_ltele (ts ++ rest) ρ D (ts ++ rest) ρ' D' args args'.
Proof.
  induction 1 as [ts ρ ρ' | i A ρ ρ' a a' ts args args' R1 HA Ha Hg IH]; intros rest D D' Hl; [ exact Hl |].
  cbn [app] in Hl |- *.
  inversion Hl; subst.
  match goal with HA2 : PER.Definitions.rel_typ _ A ρ A ρ' ?R2, Hmiss : forall c c', ?R2 c c' -> _ |- _ =>
    econstructor; [ exact HA | exact Ha |]; apply IH, Hmiss;
    destruct HA as [x x' Hx Hx' Hxx]; destruct HA2 as [y y' Hy Hy' Hyy];
    functional_eval_rewrite_clear;
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hxx Hyy) as E; apply E, Ha end.
Qed.

Lemma galias_of : forall qp y U T Δ,
    gc_module gc_deps gc_stack qp = Some (mr_body T) ->
    gc_module gc_deps gc_stack (path_app qp (y :: nil)) = Some (mr_alias U nil) ->
    gu_params U = Δ ++ T -> ⋅ ⊨ᵐ me_lit U ≈ me_lit U -> galias_at qp y.
Proof.
  intros * Hq Hy HU HUv T' U' ch args args' Hm Hm' Hg.
  rewrite Hq in Hm; injection Hm as <-.
  rewrite Hy in Hm'; injection Hm' as <- <-.
  pose proof (unit_chain_at HUv per_ctx_env_nil_true nil nil I) as Hd.
  inversion Hd; subst.
  constructor.
  match goal with Hl : per_ltele _ _ _ _ _ _ nil nil |- _ => rename Hl into Hlt end.
  rewrite HU, rev_app_distr in Hlt |- *.
  exact (ltele_supply_gargs _ _ _ _ _ Hg _ _ _ Hlt).
Qed.

(** ** The Arity of a Global Module *)

Lemma gwalk : forall qp T, gparam_at qp -> gc_module gc_deps gc_stack qp = Some (mr_body T) -> tele_ass T -> ⊨ T ->
    forall Tin Tout args ρ R, T = Tin ++ Tout -> List.length args = List.length Tout ->
      EF Tout ≈ Tout ∈ per_ctx_env ↘ R -> R (env_args ρ args) (env_args nil args) ->
      exists a, ⟦ ctx_pi Tin a_True ⟧ env_args ρ args ↘ a /\ mtyped (dm_global qp args) nil mk_mod a.
Proof.
  intros * Hgp Hm HU HT Tin.
  induction Tin as [| e Tin IH] using rev_ind; intros Tout args ρ R ET Hl HR Hρ; cbn [app ctx_pi] in *.
  - subst; exists ⊤ᵈ; split; [ constructor |].
    eapply mty_top; [ econstructor; [ exact Hm | exact Hl ] | exact (per_univ_elem_True 0) ].
  - pose proof ET as ET'.
    rewrite ET in HU; destruct (tele_ass_app_inv _ _ HU) as [HU1 HU2].
    destruct (tele_ass_app_inv _ _ HU1) as [_ He]; inversion He as [| ? ? [A1 ->] _]; subst.
    pose proof HT as HT'.
    rewrite <- app_assoc in HT'; cbn [app] in HT'.
    destruct (sem_ctx_ass_inv (sem_ctx_app_r _ _ HT')) as [i HA1].
    destruct (rel_exp_of_typ_inversion_simple_at HR HA1 _ _ Hρ) as (a1 & a0 & Ha1 & Ha0 & [Ra HRa]).
    rewrite ctx_pi_app; cbn [ctx_pi].
    eexists; split; [ econstructor; exact Ha1 |].
    assert (Hn : nth_error (rev ((Tin ++ ce_ass A1 :: nil) ++ Tout)) (List.length args) = Some (ce_ass A1)).
    { rewrite <- app_assoc, rev_app_distr; cbn [app rev].
      rewrite nth_error_app1 by (rewrite length_app, length_rev; cbn; lia).
      rewrite nth_error_app2 by (rewrite length_rev; lia).
      rewrite length_rev, Hl, Nat.sub_diag; reflexivity. }
    eapply mty_pi; [ right; do 2 eexists; split; [ reflexivity | split; reflexivity ]
                   | econstructor; [ exact Hgp | exact Hm | exact Hn | exact Ha0 ] | exact HRa |].
    intros c w1 b Hc Hw1 Hb.
    inversion Hw1; subst.
    pose proof (per_ctx_env_of_typ HR HA1) as HR'.
    destruct (IH (ce_ass A1 :: Tout) (args ++ c :: nil) ρ _ ltac:(rewrite <- app_assoc; reflexivity)
                ltac:(rewrite length_app; cbn; lia) HR') as (b' & Hb' & Hm').
    { rewrite !env_args_snoc; split; [ exact Hρ |].
      eapply per_head_of; [ exact Ha1 | exact Ha0 | exact HRa | exact Hc ]. }
    rewrite env_args_snoc in Hb'.
    pose proof (functional_eval_exp _ _ _ _ Hb Hb') as <-; exact Hm'.
Qed.

(** ** Chains of Global Submodules *)

Definition chain_bodies (p : path) (pre : list String.string) : Prop :=
  forall pre1 y pre2, pre = pre1 ++ y :: pre2 ->
    exists T, gc_module gc_deps gc_stack (path_app p (pre1 ++ y :: nil)) = Some (mr_body T) /\
      gparam_at (path_app p (pre1 ++ y :: nil)).

Lemma chain_bodies_cons : forall p y pre, chain_bodies p (y :: pre) -> chain_bodies (path_app p (y :: nil)) pre.
Proof.
  intros * H pre1 z pre2 ->.
  destruct (H (y :: pre1) z pre2 eq_refl) as (T & HT & Hg).
  rewrite path_app_app; exists T; split; assumption.
Qed.

Lemma gsub_chain : forall pre p args ch k a, chain_bodies p pre ->
    mtyped (dm_global (path_app p pre) args) ch k a -> mtyped (dm_global p args) (pre ++ ch) k a.
Proof.
  induction pre as [| y pre IH]; intros * Hc Hm; cbn [app].
  - rewrite path_app_nil in Hm; exact Hm.
  - destruct (Hc nil y pre eq_refl) as (T & HT & Hg); cbn [app] in HT, Hg.
    eapply mty_gsub; [ exact Hg | exact HT |].
    apply IH; [ exact (chain_bodies_cons _ _ _ Hc) | rewrite path_app_app; exact Hm ].
Qed.

Lemma selc_global_chain : forall pre p args z d, chain_bodies p pre ->
    eval_selc gc_deps gc_stack (dm_global p args) (pre ++ z :: nil) d ->
    eval_selc gc_deps gc_stack (dm_global (path_app p pre) args) (z :: nil) d.
Proof.
  induction pre as [| y pre IH]; intros * Hc Hs; cbn [app] in Hs.
  - rewrite path_app_nil; exact Hs.
  - destruct (Hc nil y pre eq_refl) as (T & HT & _); cbn [app] in HT.
    inversion Hs; subst; [ destruct pre; discriminate |].
    match goal with Hs1 : eval_selm _ _ _ y _ |- _ => inversion Hs1; subst end;
      [| match goal with Ha : gc_module _ _ _ = Some (mr_alias _ _) |- _ => rewrite HT in Ha; discriminate end ].
    replace (path_app p (y :: pre)) with (path_app (path_app p (y :: nil)) pre) by (rewrite path_app_app; reflexivity).
    eapply IH; [ exact (chain_bodies_cons _ _ _ Hc) | eassumption ].
Qed.

Lemma selc_global_alias : forall pre p args y U r d, chain_bodies p pre -> r <> nil ->
    gc_module gc_deps gc_stack (path_app (path_app p pre) (y :: nil)) = Some (mr_alias U nil) ->
    eval_selc gc_deps gc_stack (dm_global p args) (pre ++ y :: r) d ->
    eval_selc gc_deps gc_stack (dm_local nil U args) r d.
Proof.
  induction pre as [| w pre IH]; intros * Hc Hr Hy Hs; cbn [app] in Hs.
  - rewrite path_app_nil in Hy.
    inversion Hs; subst; [ contradiction |].
    match goal with Hs1 : eval_selm _ _ _ y _ |- _ => inversion Hs1; subst end;
      [ match goal with Hn : forall U r, _ <> _ |- _ => contradiction (Hn _ _ Hy) end |].
    match goal with Ha : gc_module _ _ _ = Some (mr_alias _ _) |- _ => rewrite Hy in Ha; injection Ha; intros; subst end.
    match goal with Hm : eval_selmc _ _ _ nil _ |- _ => inversion Hm; subst end; assumption.
  - destruct (Hc nil w pre eq_refl) as (T & HT & _); cbn [app] in HT.
    inversion Hs; subst; [ destruct pre; discriminate |].
    match goal with Hs1 : eval_selm _ _ _ w _ |- _ => inversion Hs1; subst end;
      [| match goal with Ha : gc_module _ _ _ = Some (mr_alias _ _) |- _ => rewrite HT in Ha; discriminate end ].
    eapply IH; [ exact (chain_bodies_cons _ _ _ Hc) | exact Hr | rewrite !path_app_app in *; exact Hy | eassumption ].
Qed.

Lemma eval_glob_any : forall r ρ ρ' v, ⟦ a_glob r ⟧ ρ ↘ v -> ⟦ a_glob r ⟧ ρ' ↘ v.
Proof. intros * H; inversion H; subst; [ eapply eval_exp_glob_delta | eapply eval_exp_glob_neut ]; eassumption. Qed.

Lemma rep_closed_tele : forall T X i b, ⊨ T -> tele_ass T -> T ⊨ X : Type@i -> (b = true -> X = a_True) ->
    rep ⋅ (ctx_pi T X) (List.length T) b.
Proof.
  intros * HT HU HX Hb.
  assert (HT' : ⊨ T ++ ⋅) by (rewrite app_nil_r; exact HT).
  rewrite <- (app_nil_r T) in HX.
  pose proof (rep_nest _ _ _ nil T X 0 b (gsub_id _ sem_ctx_nil) HU (Forall_nil _) HT'
                (rep_leaf _ _ _ _ HT' HX Hb)) as H.
  rewrite exp_sub_id, Nat.add_0_r in H; exact H.
Qed.

(** ** Paths to Valid Global Modules *)

Section Paths.
  Variables (Θm : gdeps) (Ξm : gstack).
  Hypothesis Hgs : ⊢g Θm ⍮ Ξm.
  Hypothesis Hsub : gc_sub Θm Ξm gc_deps gc_stack.
  Hypothesis Hgm : gmod_ok Θm Ξm.
  Hypothesis HB : forall qp T Φ, gc_body Θm Ξm qp = Some (T, Φ) ->
    ⊨ T /\ tele_ass T /\
    (forall z b pv A B, gm_resolve Φ (z :: nil) = Some (ge_def b pv A B) ->
       (exists A0 i, A = ctx_pi T A0 /\ T ⊨ A0 : Type@i) /\ ⋅ ⊨ a_glob (path_app qp (z :: nil)) : A).
  Hypothesis HA : forall qp y U, gc_module Θm Ξm (path_app qp (y :: nil)) = Some (mr_alias U nil) ->
    sem_unit ⋅ U /\ unit_mt Θm Ξm ⋅ U /\ ⋅ ⊨ᵐ me_lit U ≈ me_lit U.

  Lemma body_target : forall qp T Φ, gc_body Θm Ξm qp = Some (T, Φ) -> gc_module gc_deps gc_stack qp = Some (mr_body T).
  Proof. intros * H; exact (gc_sub_module _ _ _ _ _ _ Hsub (gc_body_module _ _ _ _ _ H)). Qed.

  Lemma body_gparam : forall qp T Φ, gc_body Θm Ξm qp = Some (T, Φ) -> gparam_at qp.
  Proof. intros * H; exact (gparam_of_tele _ _ (proj1 (HB _ _ _ H)) (body_target _ _ _ H)). Qed.

  Lemma body_chain : forall p T Φ pre T' Φ', gc_body Θm Ξm p = Some (T, Φ) ->
      gm_body T Φ pre = Some (T', Φ') -> chain_bodies p pre.
  Proof.
    intros * Hp Hpre pre1 y pre2 ->.
    replace (pre1 ++ y :: pre2) with ((pre1 ++ y :: nil) ++ pre2) in Hpre by (rewrite <- app_assoc; reflexivity).
    destruct (gm_body_prefix _ _ _ _ _ _ Hpre) as (T1 & Φ1 & H1).
    destruct (closed_read _ _ Hgs _ _ _ Hp (pre1 ++ y :: nil)) as (_ & Hb & _).
    rewrite H1 in Hb.
    exists T1; split; [ exact (body_target _ _ _ Hb) | exact (body_gparam _ _ _ Hb) ].
  Qed.

  Lemma galias_at_of : forall qp T Φ y U, gc_body Θm Ξm qp = Some (T, Φ) ->
      gc_module Θm Ξm (path_app qp (y :: nil)) = Some (mr_alias U nil) -> galias_at qp y.
  Proof.
    intros * Hq Hy.
    pose proof (gc_body_module _ _ _ _ _ Hq) as Hq'.
    destruct (wf_gc_alias_params _ _ Hgs _ _ _ _ _ Hq' Hy) as (_ & Δ & HU & _).
    destruct (HA _ _ _ Hy) as (_ & _ & HUv).
    exact (galias_of _ _ _ _ _ (gc_sub_module _ _ _ _ _ _ Hsub Hq') (gc_sub_module _ _ _ _ _ _ Hsub Hy) HU HUv).
  Qed.

  Lemma path_value_body : forall p T Φ ρ h, gc_body Θm Ξm p = Some (T, Φ) ->
      eval_modexp gc_deps gc_stack (me_path p) ρ h -> h = dm_global p nil.
  Proof.
    intros * Hp Hh; inversion Hh; subst; [ reflexivity |].
    match goal with Ha : gc_module _ _ p = Some (mr_alias _ _) |- _ => rewrite (body_target _ _ _ Hp) in Ha; discriminate end.
  Qed.

  Lemma path_body_mt : forall p T Φ, gc_body Θm Ξm p = Some (T, Φ) ->
      forall ch k A, member_type Θm Ξm ⋅ (me_path p) ch k A -> (k = mk_term -> ch <> nil) ->
      (exists n b, rep ⋅ A n b) /\ mt_val ⋅ (me_path p) ch k A.
  Proof.
    intros * Hp * Hm Hch.
    pose proof (closed_read _ _ Hgs _ _ _ Hp) as Hcr.
    inversion Hm; subst.
    - destruct (exists_last H0) as (pre & z & ->).
      rewrite (proj2 (proj2 (Hcr _)) H0) in H2.
      destruct (gm_resolve_decomp _ _ T _ _ H2) as (T' & Φ' & Hb & Hz).
      assert (Hbq : gc_body Θm Ξm (path_app p pre) = Some (T', Φ')) by (rewrite (proj1 (proj2 (Hcr _))); exact Hb).
      destruct (HB _ _ _ Hbq) as (HT' & HU' & Hdef).
      destruct (Hdef _ _ _ _ _ Hz) as ((A0 & i & -> & HA0) & Hglob).
      split; [ exists (List.length T'), false; apply (rep_closed_tele _ _ _ _ HT' HU' HA0); discriminate |].
      intros R ρ HR Hρ h Hh; pose proof (path_value_body _ _ _ _ _ Hp Hh) as ->.
      destruct (rel_exp_under_ctx_simple_full_at per_ctx_env_nil_true Hglob) as [j Hg].
      destruct (Hg ρ nil I) as (a & a1 & R1 & Ha & Ha1 & HR1 & _).
      destruct (Hg nil nil I) as (aA & aA' & E & HaA & HaA' & HE & f & f' & Hf & Hf' & Hff).
      functional_eval_rewrite_clear.
      exists a; split; [ exact Ha |].
      apply (gsub_chain _ _ _ _ _ _ (body_chain _ _ _ _ _ _ Hp Hb)).
      eapply mty_gdef with (f := f) (aA := a1) (E := E) (a0 := a1) (R := R1);
        [ exact (body_target _ _ _ Hbq) | cbn; lia
        | apply (gc_sub_resolve _ _ _ _ _ _ Hsub); rewrite path_app_app, (proj2 (proj2 (Hcr _)) H0); exact H2
        | exact Hf | exact Ha1 | exact HE | exact Hff | | exact HR1 ].
      rewrite Nat.sub_0_r, firstn_all; exact Ha1.
    - destruct (gc_module_body _ _ _ _ H1) as (Φ0 & Hb0).
      destruct (HB _ _ _ Hb0) as (HT0 & HU0 & _).
      split; [ exists (List.length T0), true; apply (rep_closed_tele _ _ 0 _ HT0 HU0 (valid_exp_True HT0)); reflexivity |].
      intros R ρ HR Hρ h Hh; pose proof (path_value_body _ _ _ _ _ Hp Hh) as ->.
      assert (Hbc : gm_body T Φ ch = Some (T0, Φ0)) by (rewrite <- (proj1 (proj2 (Hcr _))); exact Hb0).
      destruct (gwalk _ _ (body_gparam _ _ _ Hb0) (body_target _ _ _ Hb0) HU0 HT0 T0 nil nil ρ _
                  ltac:(rewrite app_nil_r; reflexivity) eq_refl per_ctx_env_nil_true I) as (a & Ha & Hma).
      exists a; split; [ exact Ha |].
      rewrite <- (app_nil_r ch); exact (gsub_chain _ _ _ _ _ _ (body_chain _ _ _ _ _ _ Hp Hbc) Hma).
    - rewrite (proj1 (Hcr _)) in H1.
      destruct ch as [| x ip]; [ discriminate |]; cbn in H1.
      destruct (gm_submodule_alias_decomp _ _ _ _ _ _ H1) as (pre & y & T' & Φ' & Hch' & Hb & Hy).
      rewrite Hch' in *; clear Hch'.
      assert (Hbq : gc_body Θm Ξm (path_app p pre) = Some (T', Φ')) by (rewrite (proj1 (proj2 (Hcr _))); exact Hb).
      assert (Hys : gc_module Θm Ξm (path_app (path_app p pre) (y :: nil)) = Some (mr_alias U nil))
        by (rewrite path_app_app, (proj1 (Hcr _)), (proj1 (gm_body_snoc _ _ _ _ _ Hb y)); exact Hy).
      destruct (HA _ _ _ Hys) as (HUs & HUm & HUv).
      destruct (closure_typed _ _ _ _ _ H3 sem_ctx_nil HUs HUm H0) as ((n & b & Hrep & _) & Hval).
      split; [ exists n, b; exact Hrep |].
      intros R ρ HR Hρ h Hh; pose proof (path_value_body _ _ _ _ _ Hp Hh) as ->.
      destruct (Hval R ρ HR Hρ) as (a & Ha & Hma).
      exists a; split; [ exact Ha |].
      apply (gsub_chain _ _ _ _ _ _ (body_chain _ _ _ _ _ _ Hp Hb)).
      eapply mty_galias; [ exact (galias_at_of _ _ _ _ _ Hbq Hys) | exact (gc_sub_module _ _ _ _ _ _ Hsub Hys) | exact H0 |].
      exact (mtyped_per (proj1 Hgm) _ _ _ _ Hma _ (unit_chain_at HUv per_ctx_env_nil_true _ _ I)).
  Qed.

  Lemma path_body_pairs : forall p T Φ, gc_body Θm Ξm p = Some (T, Φ) ->
      forall ch0 A0 ch k A, member_type Θm Ξm ⋅ (me_path p) ch0 mk_mod A0 ->
      member_type Θm Ξm ⋅ (me_path p) (ch0 ++ ch) k A -> (k = mk_term -> ch0 ++ ch <> nil) ->
      exists m n, rep ⋅ A0 m true /\ rep ⋅ A n false /\ m <= n.
  Proof.
    intros * Hp * Hm0 Hm Hch.
    pose proof (closed_read _ _ Hgs _ _ _ Hp) as Hcr.
    inversion Hm0; subst.
    2: {
      destruct (gc_module_alias_decomp _ _ Hgs _ _ _ H1) as (qp & y & _ & Hy).
      destruct (HA _ _ _ Hy) as (HUs & HUm & _).
      destruct (gc_module_alias_app _ _ Hgs _ _ _ H1 ch) as (Hal & Hres).
      rewrite path_app_app in Hal, Hres.
      inversion Hm; subst.
      - destruct ch as [| c ch]; [ rewrite app_nil_r, (gc_module_alias_resolve _ _ Hgs _ _ _ H1) in *; discriminate |].
        rewrite Hres in *; [ discriminate | discriminate ].
      - rewrite Hal in *; discriminate.
      - match goal with Hx : gc_module _ _ _ = Some (mr_alias _ _) |- _ => rewrite Hal in Hx; injection Hx; intros; subst end.
        eapply closure_pairs; [ exact H3 | reflexivity | exact sem_ctx_nil | exact HUs | exact HUm | eassumption | assumption ]. }
    destruct (gc_module_body _ _ _ _ H1) as (Φ0 & Hb0).
    destruct (HB _ _ _ Hb0) as (HT0 & HU0 & _).
    pose proof (closed_read _ _ Hgs _ _ _ Hb0) as Hcr0.
    pose proof (gc_body_coh _ _ Hgs _ _ _ Hb0) as Hc0.
    assert (Htop : rep ⋅ (ctx_pi T0 ⊤) (List.length T0) true)
      by (apply (rep_closed_tele _ _ 0 _ HT0 HU0 (valid_exp_True HT0)); reflexivity).
    remember (ch0 ++ ch) as cc eqn:Ecc.
    inversion Hm; subst.
    - match goal with Hr : gc_resolve _ _ _ = Some _ |- _ => rename Hr into Hr2 end.
      destruct ch as [| c ch].
      + exfalso; rewrite app_nil_r in H0, Hr2.
        destruct (exists_last H0) as (pre & z & ->).
        rewrite (proj2 (proj2 (Hcr _)) H0) in Hr2.
        destruct (gm_resolve_decomp _ _ T _ _ Hr2) as (T' & Φ' & Hb & Hz).
        rewrite (proj1 (Hcr _)), (proj1 (gm_body_snoc _ _ _ _ _ Hb z)), (gm_resolve_def_not_module _ _ _ _ _ _ _ _ Hz) in H1.
        discriminate.
      + rewrite <- path_app_app in Hr2.
        assert (Hne : c :: ch <> nil) by discriminate.
        destruct (exists_last Hne) as (ch1' & z' & Ech).
        rewrite (proj2 (proj2 (Hcr0 _)) Hne), Ech in Hr2.
        destruct (gm_resolve_decomp _ _ T0 _ _ Hr2) as (T' & Φ' & Hb & Hz).
        destruct (gm_coh_body_tele _ _ _ _ _ Hc0 Hb) as (_ & Δ & -> & _).
        assert (Hbq : gc_body Θm Ξm (path_app (path_app p ch0) ch1') = Some (Δ ++ T0, Φ'))
          by (rewrite (proj1 (proj2 (Hcr0 _))); exact Hb).
        destruct (HB _ _ _ Hbq) as (HT' & HU' & Hdef).
        destruct (Hdef _ _ _ _ _ Hz) as ((A1 & i & -> & HA1) & _).
        exists (List.length T0), (List.length (Δ ++ T0)); split; [ exact Htop |]; split;
          [ apply (rep_closed_tele _ _ _ _ HT' HU' HA1); discriminate | rewrite length_app; lia ].
    - match goal with Hr : gc_module _ _ (path_app p (ch0 ++ ch)) = _ |- _ => rename Hr into Hr2 end.
      rewrite <- path_app_app, (proj1 (Hcr0 _)) in Hr2.
      destruct (gm_module_body_some _ _ _ _ Hr2) as (Φ' & Hb).
      destruct (gm_coh_body_tele _ _ _ _ _ Hc0 Hb) as (_ & Δ & -> & _).
      assert (Hbq : gc_body Θm Ξm (path_app (path_app p ch0) ch) = Some (Δ ++ T0, Φ'))
        by (rewrite (proj1 (proj2 (Hcr0 _))); exact Hb).
      destruct (HB _ _ _ Hbq) as (HT' & HU' & _).
      exists (List.length T0), (List.length (Δ ++ T0)); split; [ exact Htop |]; split;
        [ apply (rep_forget _ _ _ true), (rep_closed_tele _ _ 0 _ HT' HU' (valid_exp_True HT')); reflexivity
        | rewrite length_app; lia ].
    - match goal with Hr : gc_module _ _ (path_app p (ch0 ++ ch)) = _ |- _ => rename Hr into Hr2 end.
      rewrite <- path_app_app, (proj1 (Hcr0 _)) in Hr2.
      destruct ch as [| x ip]; [ discriminate |]; cbn in Hr2.
      destruct (gm_submodule_alias_decomp _ _ _ _ _ _ Hr2) as (pre & y & T' & Φ' & Hch' & Hb & Hy).
      destruct (gm_coh_body_tele _ _ _ _ _ Hc0 Hb) as (Hc' & Δ & -> & _).
      destruct (gm_coh_child _ _ _ _ Hc' Hy) as [(Δ1 & [=] & _) | (U' & Δ1 & [= <-] & HUp & _)].
      assert (Hys : gc_module Θm Ξm (path_app (path_app (path_app p ch0) pre) (y :: nil)) = Some (mr_alias U nil))
        by (rewrite path_app_app, (proj1 (Hcr0 _)), (proj1 (gm_body_snoc _ _ _ _ _ Hb y)); exact Hy).
      destruct (HA _ _ _ Hys) as (HUs & HUm & _).
      match goal with Hu : unit_member_type _ _ _ U _ _ _ |- _ => rename Hu into Hu2 end.
      destruct (closure_typed _ _ _ _ _ Hu2 sem_ctx_nil HUs HUm ltac:(assumption)) as ((n & b & Hrep & Hle) & _).
      exists (List.length T0), n; split; [ exact Htop |]; split; [ exact (rep_forget _ _ _ _ Hrep) |].
      rewrite HUp, !length_app in Hle; lia.
  Qed.

  Lemma path_body_unf : forall p T Φ, gc_body Θm Ξm p = Some (T, Φ) -> sem_unf Θm Ξm ⋅ (me_path p).
  Proof.
    intros * Hp ch A M Hm HM R ρ HR Hρ h Hh * Ha HE Hd Hdd.
    pose proof (path_value_body _ _ _ _ _ Hp Hh) as ->.
    pose proof (closed_read _ _ Hgs _ _ _ Hp) as Hcr.
    inversion Hm; subst; cbn in HM.
    - rewrite H2 in HM; injection HM as <-.
      destruct (exists_last H0) as (pre & z & ->).
      pose proof H2 as H2'; rewrite (proj2 (proj2 (Hcr _)) H0) in H2'.
      destruct (gm_resolve_decomp _ _ T _ _ H2') as (T' & Φ' & Hb & _).
      pose proof (selc_one_inv _ _ _ (selc_global_chain _ _ _ _ _ (body_chain _ _ _ _ _ _ Hp Hb) Hd)) as Hs.
      inversion Hs; subst.
      match goal with Hap : eval_apps _ _ _ nil _ |- _ => inversion Hap; subst end.
      exists d; split; [| exact Hdd ].
      rewrite <- path_app_app; eapply eval_glob_any; eassumption.
    - rewrite (gc_module_alias_resolve _ _ Hgs _ _ _ H1), H1 in HM.
      pose proof (H0 eq_refl) as Hr.
      pose proof H1 as H1'; rewrite (proj1 (Hcr _)) in H1'.
      destruct ch as [| x ip]; [ discriminate |]; cbn in H1'.
      destruct (gm_submodule_alias_decomp _ _ _ _ _ _ H1') as (pre & y & T' & Φ' & Hch' & Hb & Hy).
      rewrite Hch' in *; clear Hch'.
      assert (Hbq : gc_body Θm Ξm (path_app p pre) = Some (T', Φ')) by (rewrite (proj1 (proj2 (Hcr _))); exact Hb).
      destruct (HB _ _ _ Hbq) as (_ & HU' & _).
      destruct (gm_coh_body_tele _ _ _ _ _ (gc_body_coh _ _ Hgs _ _ _ Hp) Hb) as (Hc' & _).
      destruct (gm_coh_child _ _ _ _ Hc' Hy) as [(Δ1 & [=] & _) | (U' & Δ1 & [= <-] & HUp & HΔ1)].
      assert (HUa : tele_ass (gu_params U)) by (rewrite HUp; apply Forall_app; split; assumption).
      assert (Hys : gc_module Θm Ξm (path_app (path_app p pre) (y :: nil)) = Some (mr_alias U nil))
        by (rewrite path_app_app, (proj1 (Hcr _)), (proj1 (gm_body_snoc _ _ _ _ _ Hb y)); exact Hy).
      destruct (HA _ _ _ Hys) as (HUs & HUm & HUv).
      destruct (closure_typed _ _ _ _ _ H3 sem_ctx_nil HUs HUm H0) as (_ & Hval).
      destruct (Hval R ρ HR Hρ) as (a' & Ha' & Hma).
      pose proof (functional_eval_exp _ _ _ _ Ha Ha') as <-.
      pose proof (selc_global_alias _ _ _ _ _ _ _ (body_chain _ _ _ _ _ _ Hp Hb) Hr
                    (gc_sub_module _ _ _ _ _ _ Hsub Hys) Hd) as Hd'.
      destruct (mtyped_rel (proj1 Hgm) _ _ _ _ Hma _ _ _ (unit_chain_at HUv per_ctx_env_nil_true ρ nil I) HE)
        as (v & v' & Hv1 & Hv2 & Hvv).
      pose proof (functional_eval_selc _ _ _ _ Hd' Hv2) as <-.
      assert (HPE : PER E) by (eapply per_elem_PER; exact HE).
      assert (Hv : E v v) by (etransitivity; [ exact Hvv | symmetry; exact Hvv ]).
      destruct (unit_delta _ _ _ _ _ _ _ _ H3 eq_refl HM HUa _ _ _ _ _ Ha HE Hv1 Hv) as (m & Hm' & Hmv).
      exists m; split; [ exact Hm' | etransitivity; [ exact Hmv | exact Hvv ] ].
  Qed.

  Lemma path_body_val : forall p T Φ, gc_body Θm Ξm p = Some (T, Φ) ->
      exists h, eval_modexp gc_deps gc_stack (me_path p) nil h /\ per_dmod h h.
  Proof.
    intros * Hp; pose proof (body_target _ _ _ Hp) as Ht.
    exists (dm_global p nil); split.
    - apply eval_me_path; intros * Ha; rewrite Ht in Ha; discriminate.
    - econstructor; [ exact Ht | constructor ].
  Qed.

  Lemma gpath_body : forall p T Φ, gc_body Θm Ξm p = Some (T, Φ) -> gpath_at Θm Ξm p.
  Proof.
    intros * Hp; split; [ split |]; [ exact (path_body_mt _ _ _ Hp) | exact (path_body_pairs _ _ _ Hp) |].
    split; [ exact (path_body_unf _ _ _ Hp) | intros; exact (path_body_val _ _ _ Hp) ].
  Qed.

  Lemma alias_mt_inv : forall p U r0, gc_module Θm Ξm p = Some (mr_alias U r0) ->
      forall Γ ch k A, member_type Θm Ξm Γ (me_path p) ch k A ->
      unit_member_type Θm Ξm ⋅ U (r0 ++ ch) k A /\ (k = mk_term -> r0 ++ ch <> nil).
  Proof.
    intros * Hp * Hm.
    destruct (gc_module_alias_app _ _ Hgs _ _ _ Hp ch) as (Hal & Hres).
    inversion Hm; subst.
    - destruct ch as [| c ch]; [ rewrite path_app_nil, (gc_module_alias_resolve _ _ Hgs _ _ _ Hp) in *; discriminate |].
      rewrite Hres in *; [ discriminate | discriminate ].
    - rewrite Hal in *; discriminate.
    - match goal with Hx : gc_module _ _ _ = Some (mr_alias _ _) |- _ => rewrite Hal in Hx; injection Hx; intros; subst end.
      split; assumption.
  Qed.

  Lemma gpath_alias : forall p U r0, gc_module Θm Ξm p = Some (mr_alias U r0) -> gpath_at Θm Ξm p.
  Proof.
    intros * Hp.
    destruct (gc_module_alias_decomp _ _ Hgs _ _ _ Hp) as (qp & y & _ & Hy).
    destruct (HA _ _ _ Hy) as (HUs & HUm & HUv).
    assert (HUa : tele_ass (gu_params U)) by (destruct HUs; cbn; assumption).
    pose proof (gc_sub_module _ _ _ _ _ _ Hsub Hp) as Ht.
    assert (Hev : forall ρ h, eval_modexp gc_deps gc_stack (me_path p) ρ h ->
                    eval_selmc gc_deps gc_stack (dm_local nil U nil) r0 h).
    { intros * Hh; inversion Hh; subst;
        [ match goal with Hn : forall U r, _ <> _ |- _ => contradiction (Hn _ _ Ht) end |].
      match goal with Hx : gc_module _ _ p = Some _ |- _ => rewrite Ht in Hx; injection Hx; intros; subst end; assumption. }
    pose proof (fun ρ => unit_chain_at HUv per_ctx_env_nil_true ρ nil I) as Htie.
    split; [ split |].
    - intros ch k A Hm Hk.
      destruct (alias_mt_inv _ _ _ Hp _ _ _ _ Hm) as (Hu & Hk').
      destruct (closure_typed _ _ _ _ _ Hu sem_ctx_nil HUs HUm Hk') as ((n & b & Hrep & _) & Hval).
      split; [ eauto |].
      intros R ρ HR Hρ h Hh; destruct (Hval R ρ HR Hρ) as (a & Ha & Hma).
      exists a; split; [ exact Ha |].
      exact (mtyped_selmc _ _ _ _ (mtyped_per (proj1 Hgm) _ _ _ _ Hma _ (Htie ρ)) r0 ch eq_refl Hk _ (Hev _ _ Hh)).
    - intros ch0 A0 ch k A Hm0 Hm Hk.
      destruct (alias_mt_inv _ _ _ Hp _ _ _ _ Hm0) as (Hu0 & _).
      destruct (alias_mt_inv _ _ _ Hp _ _ _ _ Hm) as (Hu & Hk').
      rewrite app_assoc in Hu, Hk'.
      exact (closure_pairs _ _ _ _ _ Hu0 eq_refl sem_ctx_nil HUs HUm _ _ _ Hu Hk').
    - split.
      + intros ch A M Hm HM R ρ HR Hρ h Hh * Ha HE Hd Hdd.
        destruct (gc_module_alias_app _ _ Hgs _ _ _ Hp ch) as (Hal & Hres).
        assert (Hn : gc_resolve Θm Ξm (path_app p ch) = None)
          by (destruct ch; [ rewrite path_app_nil; exact (gc_module_alias_resolve _ _ Hgs _ _ _ Hp)
                           | apply Hres; discriminate ]).
        cbn in HM; rewrite Hn, Hal in HM.
        destruct (alias_mt_inv _ _ _ Hp _ _ _ _ Hm) as (Hu & Hk').
        destruct ch as [| c ch]; [ inversion Hd |].
        assert (Hne : c :: ch <> nil) by discriminate.
        assert (Hd' : eval_selc gc_deps gc_stack (dm_local nil U nil) (r0 ++ c :: ch) d)
          by (apply eval_selc_app; [ exact Hne | exists h; split; [ exact (Hev _ _ Hh) | exact Hd ] ]).
        destruct (closure_typed _ _ _ _ _ Hu sem_ctx_nil HUs HUm Hk') as (_ & Hval).
        destruct (Hval R ρ HR Hρ) as (a' & Ha' & Hma).
        pose proof (functional_eval_exp _ _ _ _ Ha Ha') as <-.
        destruct (mtyped_rel (proj1 Hgm) _ _ _ _ Hma _ _ _ (Htie ρ) HE) as (v & v' & Hv1 & Hv2 & Hvv).
        pose proof (functional_eval_selc _ _ _ _ Hd' Hv2) as <-.
        assert (HPE : PER E) by (eapply per_elem_PER; exact HE).
        assert (Hv : E v v) by (etransitivity; [ exact Hvv | symmetry; exact Hvv ]).
        destruct (unit_delta _ _ _ _ _ _ _ _ Hu eq_refl HM HUa _ _ _ _ _ Ha HE Hv1 Hv) as (m & Hm' & Hmv).
        exists m; split; [ exact Hm' | etransitivity; [ exact Hmv | exact Hvv ] ].
      + intros A Hm.
        destruct (alias_mt_inv _ _ _ Hp _ _ _ _ Hm) as (Hu & Hk').
        destruct (closure_typed _ _ _ _ _ Hu sem_ctx_nil HUs HUm Hk') as (_ & Hval).
        destruct (Hval _ nil per_ctx_env_nil_true I) as (a & _ & Hma).
        destruct (mtyped_selmc_ex _ _ _ _ Hma r0 nil eq_refl ltac:(discriminate)) as (h & Hs).
        destruct (mtyped_selmc_rel (proj1 Hgm) _ _ _ _ Hma r0 nil eq_refl ltac:(discriminate) _ (Htie nil) _ Hs)
          as (h' & Hs' & Hhh).
        pose proof (functional_eval_selmc _ _ _ _ Hs Hs') as <-.
        exists h; split; [ eapply eval_me_path_alias; eassumption | exact Hhh ].
  Qed.

  (** Every module of a valid global context is valid as a path. *)
  Theorem gpath_ok : forall p r, gc_module Θm Ξm p = Some r -> gpath_at Θm Ξm p.
  Proof.
    intros p [T | U r0] Hp.
    - destruct (gc_module_body _ _ _ _ Hp) as (Φ & Hb); exact (gpath_body _ _ _ Hb).
    - exact (gpath_alias _ _ _ Hp).
  Qed.

End Paths.

End Fixed_GCtx.

(** The syntactic facts the semantics of members uses hold in a valid global
    context. *)
Lemma gmod_ok_of_wf : forall Θ Ξ Θ1 Ξ1, ⊢g Θ ⍮ Ξ -> gctx_closed Θ1 Ξ1 -> @gmod_ok (gc_mk Θ Ξ) Θ1 Ξ1.
Proof.
  intros * H Hc; split; [| split; [| exact Hc ] ].
  - intros p T y T' H1 H2; destruct (wf_gc_child _ _ H _ _ _ _ H1 H2) as (Δ & -> & _); eauto.
  - intros p T y U ch H1 H2; destruct (wf_gc_alias_params _ _ H _ _ _ _ _ H1 H2) as (_ & Δ & HU & _); eauto.
Qed.
