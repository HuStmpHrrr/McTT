(** * The [ι] Rule of a Group

    The eliminator at a constructor of the member [m] is the constructor's
    branch at the non-uniform parameters, the arguments and the recursive
    results ([elim_ihs]): one per leaf path of each recursive argument
    ([leaf_ih]), the eliminator at the argument applied to the domains the
    path passes and projected at the fields it passes, under the domains.
    Under a domain its value is not the eliminator's own recursive result
    ([d_ihfn]), so the rule relates the two along the path
    ([rec_result_rel]): at the end of the path, the eliminator at its
    blocks moved past the domains, in the environment extended by the
    domains' values, against the eliminator at its own (an outer link of
    [Elim.v]).  The paths walk the frames of [Elim.v]: a recursive argument
    of the constructor, then the recursive fields of the record views the
    path passes. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing Views.
From Mctt.Core.Syntactic.System.Global Require Import Presup MemberLemmas MemberWf.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Instance Telescope.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness Require Import VariableCases FunctionCases LevelCases SubtypingCases.
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews ArgTypes ViewEquations ViewArgs CargsRel Con Elim.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules Evaluation.Lemmas.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma eval_exps_firstn' : forall Ms ρ ms k, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms ->
    ⟦ List.firstn k Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ List.firstn k ms.
Proof.
  induction Ms as [| M Ms IH]; intros * H; inversion H; subst; destruct k; cbn; try constructor; [ assumption | apply IH; assumption ].
Qed.

(** The components' substitution of a shape after the arguments [gs], past
    their non-recursive ones: the substitution they extend. *)
Lemma cargs_sub_ge : forall gs σ As y, List.length gs <= List.length As ->
    cargs_sub σ gs As (y + List.length (cargs_nonrec gs)) = σ y.
Proof.
  induction gs as [| [B | t] gs IH]; intros σ [| N As] y Hl; cbn in Hl |- *; try lia.
  - rewrite Nat.add_0_r; reflexivity.
  - rewrite Nat.add_0_r; reflexivity.
  - replace (y + S (List.length (cargs_nonrec gs))) with (S y + List.length (cargs_nonrec gs)) by lia.
    rewrite IH by lia; reflexivity.
  - apply IH; lia.
Qed.

(** The recursive results of arguments [gs1 ++ gs2]: those of [gs1], then
    those of [gs2]. *)
Lemma cargs_nrec_app_iota : forall Dx gs1 gs2, cargs_nrec Dx (gs1 ++ gs2) = cargs_nrec Dx gs1 + cargs_nrec Dx gs2.
Proof. intros Dx; induction gs1 as [| [] gs1 IH]; intros; cbn; rewrite ?IH; lia. Qed.

(** The recursive results of a recursive argument along its leaf paths
    [ls1 ++ ls2], as a context: those of [ls2] over those of [ls1]. *)
Lemma leaves_ctx_app : forall nn As Us na pat ls1 ls2 j,
    leaves_ctx nn As Us na pat j (ls1 ++ ls2) = leaves_ctx nn As Us na pat (j + List.length ls1) ls2 ++ leaves_ctx nn As Us na pat j ls1.
Proof.
  intros nn As Us na pat ls1; induction ls1 as [| l1 ls1 IH]; intros ls2 j; cbn [leaves_ctx List.app List.length];
    [ rewrite Nat.add_0_r, List.app_nil_r; reflexivity |].
  rewrite IH, <- List.app_assoc; replace (S j + List.length ls1) with (j + S (List.length ls1)) by lia; reflexivity.
Qed.

(** The names of the non-recursive fields of [fs1 ++ fs2]. *)
Lemma fields_args_app : forall fs1 fs2, fields_args (fs1 ++ fs2) = fields_args fs1 ++ fields_args fs2.
Proof. induction fs1 as [| [? []] fs1 IH]; intros; cbn; rewrite ?IH; reflexivity. Qed.

Lemma length_fields_args : forall fs, List.length (fields_args fs) = List.length (cargs_nonrec (List.map snd fs)).
Proof. induction fs as [| [? []] fs IH]; cbn; lia. Qed.

(** The functions of a list of bodies under a domain [A]. *)
Lemma eval_exps_fns : forall (ls : list leaf_path) A F ρ,
    ⟦ List.map (fun l => λ A (F l)) ls ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ List.map (fun l => λᵈ ρ (F l)) ls.
Proof. induction ls as [| l ls IH]; intros; cbn [List.map]; constructor; [ constructor | apply IH ]. Qed.

(** The functions of the recursive results along paths through a domain
    [A], applied to a value [c]: their bodies at the environment extended
    by [c]. *)
Lemma eval_exps_fns_app : forall (ls : list leaf_path) A F ρ rs c rcs,
    ⟦ List.map (fun l => λ A (F l)) ls ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ rs ->
    ⟦ List.map F ls ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↦ c ↘ rcs ->
    List.Forall2 (fun f r => $| f & c | gc_deps ⍮ gc_stack ↘ r) rs rcs.
Proof.
  induction ls as [| l ls IH]; intros * E1 E2; cbn [List.map] in E1, E2; inversion E1; subst; inversion E2; subst; constructor.
  - match goal with H : ⟦ λ _ _ ⟧ _ ↘ _ |- _ => inversion H; subst end.
    constructor; assumption.
  - eapply IH; eassumption.
Qed.

(** The functions of the eliminator's own recursive results under a
    domain, applied to a value [c]: the recursive results of the rest at
    the argument applied to [c]. *)
Lemma ihfn_app : forall ρ Bks p0 ups t v c fc rcs n,
    $| v & c | gc_deps ⍮ gc_stack ↘ fc -> ⟦ih fc of t under p0 ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ rcs ->
    List.length rcs = n ->
    List.Forall2 (fun f r => $| f & c | gc_deps ⍮ gc_stack ↘ r) (List.map (fun i => d_ihfn ρ Bks p0 ups t i v) (List.seq 0 n)) rcs.
Proof.
  intros * Ef Eih Ln.
  assert (G : forall k l, List.skipn k rcs = l ->
             List.Forall2 (fun f r => $| f & c | gc_deps ⍮ gc_stack ↘ r)
               (List.map (fun i => d_ihfn ρ Bks p0 ups t i v) (List.seq k (List.length l))) l).
  { intros k l; revert k; induction l as [| r l IH]; intros k Hs; cbn [List.length List.seq List.map]; constructor.
    - assert (Hk : k < List.length rcs)
        by (pose proof (f_equal (@List.length domain) Hs) as HL; rewrite List.length_skipn in HL; cbn in HL; lia).
      eapply eval_app_ihfn; [ exact Ef | exact Eih |].
      rewrite <- (List.firstn_skipn k rcs), Hs, List.nth_error_app2 by (rewrite List.length_firstn; lia).
      rewrite List.length_firstn; replace (k - Nat.min k (List.length rcs)) with 0 by lia; reflexivity.
    - apply IH.
      replace (S k) with (1 + k) by lia; rewrite <- List.skipn_skipn, Hs; reflexivity. }
  pose proof (G 0 rcs eq_refl) as H; rewrite Ln in H; exact H.
Qed.

(** ** The Eliminator at Blocks Moved by a Substitution

    The blocks [Bks] of an eliminator of the group [D] at [p], of a valid
    family [VP], valid in [Γ] at the uniform parameters [Us]: moved by a
    substitution [β] into [Ψ], the eliminator at a member [j] with a block
    is valid there. *)
Section Blocks.
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups VP) (HPD : VP p D).
  Let Hvg := valid_groups_valid VP HP p D HPD.
  Let HD := valid_group_valid _ _ Hvg.
  Let Hc := valid_group_closed _ _ Hvg.
  Let Hdt := valid_group_typed _ _ Hvg.
  Let Ua : tele_ass (ind_uparams D) := uparams_ass D Hc.

  Variable (Γ : ctx) (oq : option qname) (Us : list exp) (Bks : list eblock) (i : nat).
  Hypotheses (HΓ : ⊨ Γ) (Hoq : oq = Some p \/ oq = None) (HUl : List.length Us = ind_nu D)
    (HUs : forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Γ ⊨ U : T)
    (HBks : List.length Bks = ind_nblk D)
    (HnmA : blocks_nm_ok D Bks)
    (HMall : forall j Mj, ind_member D j = Some Mj -> ⊨ elim_mctx p D j Mj Us ++ Γ)
    (HAv : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b : Typeω@i)
    (HnaA : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> brs_names (im_cons Mj) (eb_brs b))
    (HBc : forall j Mj c gs, ind_member D j = Some Mj -> ind_con Mj c = Some gs ->
             ⊨ elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ)
    (HarA : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> ind_con Mj c = Some gs ->
              In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat)
    (HBv : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> ind_con Mj c = Some gs ->
             In (c, n, B) (eb_brs b) ->
             elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ ⊨ B : elim_bty p D j Mj c gs (eb_motive b) Us).

  Lemma elim_at_valid : forall Ψ β j Mj Ns M, gsub Ψ β Γ -> ind_member D j = Some Mj -> im_is_rview Mj = false ->
      List.length Ns = im_nn Mj ->
      (forall k N T, List.nth_error Ns k = Some N ->
         List.nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (List.map (fun U => U[β]) Us)) Ns) k = Some T -> Ψ ⊨ N : T) ->
      Ψ ⊨ M : ind_mty p D j (List.map (fun U => U[β]) Us) Ns ->
      Ψ ⊨ elim_at p D oq (List.map (fun U => U[β]) Us) (blocks_sub Bks β) j M
        : (List.nth j (blocks_motives Bks) a_True)[sb_of_list β (Ns ++ M :: nil)].
  Proof.
    intros * Hβ HMj Hrv HNl HNs HM.
    set (Us0 := List.map (fun U => U[β]) Us) in *.
    set (Bks0 := blocks_sub Bks β).
    pose proof (gsub_rel_ctx_wf _ _ _ Hβ) as HΨ.
    destruct (block_of_nblk D Bks Hdt HBks _ _ HMj Hrv) as [b Hb].
    assert (HUl0 : List.length Us0 = ind_nu D) by (unfold Us0; rewrite List.length_map; exact HUl).
    assert (HUs0 : forall k U T, List.nth_error Us0 k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us0) k = Some T ->
               Ψ ⊨ U : T).
    { intros k U' T' HU HT; unfold Us0 in HU, HT.
      rewrite <- (tele_insts_sub (ind_uparams D) 0 Id Id β Us Ua (decl_uparams_closed D Hc) ltac:(intros; lia)) in HT.
      apply nth_error_map_inv in HU as (U & HU & ->); apply nth_error_map_inv in HT as (T & HT & ->).
      exact (rel_exp_under_ctx_gsub Hβ (HUs _ _ _ HU HT)). }
    assert (HUU0 : forall k U U' T, List.nth_error Us0 k = Some U -> List.nth_error Us0 k = Some U' ->
               List.nth_error (tele_insts (ind_uparams D) Id Us0) k = Some T -> Ψ ⊨ U ≈ U' : T).
    { intros * HU HU' HT; rewrite HU in HU'; injection HU' as <-; exact (HUs0 _ _ _ HU HT). }
    assert (HBks0 : List.length Bks0 = ind_nblk D) by (unfold Bks0; rewrite length_blocks_sub; exact HBks).
    assert (Hgm : forall k Mk, ind_member D k = Some Mk -> gsub (elim_mctx p D k Mk Us0 ++ Ψ) (sb_qn (S (im_nn Mk)) β) (elim_mctx p D k Mk Us ++ Γ)).
    { intros * HMk.
      pose proof (gsub_qn _ _ _ _ Hβ (elim_mctx_ass p D k Mk Us Hc HMk) (HMall _ _ HMk)) as G.
      rewrite (elim_mctx_sub p D k Mk Us β Hc HMk HUl), length_elim_mctx in G; exact G. }
    assert (HMall0 : forall k Mk, ind_member D k = Some Mk -> ⊨ elim_mctx p D k Mk Us0 ++ Ψ)
      by (intros * HMk; exact (gsub_rel_ctx_wf _ _ _ (Hgm _ _ HMk))).
    assert (HnmA0 : blocks_nm_ok D Bks0) by (apply blocks_nm_ok_sub; exact HnmA).
    assert (HAA0 : forall k Mk b1 b1', ind_member D k = Some Mk -> List.nth_error Bks0 k = Some b1 -> List.nth_error Bks0 k = Some b1' ->
               elim_mctx p D k Mk Us0 ++ Ψ ⊨ eb_motive b1 ≈ eb_motive b1' : Typeω@i).
    { intros * HMk Hb1 Hb1'; rewrite Hb1 in Hb1'; injection Hb1' as <-.
      destruct (nth_error_blocks_sub_inv _ _ _ _ Hb1) as (b2 & Hb2 & ->).
      rewrite eb_motive_sub, (HnmA _ _ _ HMk Hb2).
      pose proof (rel_exp_under_ctx_gsub (Hgm _ _ HMk) (HAv _ _ _ HMk Hb2)) as H; cbn [exp_sub] in H; exact H. }
    assert (Hgb : forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
               gsub (elim_bctx p D Mk gs (blocks_motives Bks0) Us0 ++ Ψ)
                 (sb_qn (cargs_nrec D gs + List.length gs + im_nn Mk) β) (elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ)).
    { intros * HMk Hcon.
      pose proof (gsub_qn _ _ _ _ Hβ (elim_bctx_ass p D k Mk gs (blocks_motives Bks) Us Hc HMk) (HBc _ _ _ _ HMk Hcon)) as G.
      rewrite (elim_bctx_sub p D k Mk c gs (blocks_motives Bks) (blocks_motives Bks0) Us β Hc HMk (cons_lookup_in _ _ _ Hcon) HUl
                 (fun j0 Mj0 HMj0 => blocks_motives_sub D Bks β j0 Mj0 HnmA HMj0)), length_elim_bctx in G.
      exact G. }
    assert (HBc0 : forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
               ⊨ elim_bctx p D Mk gs (blocks_motives Bks0) Us0 ++ Ψ)
      by (intros * HMk Hcon; exact (gsub_rel_ctx_wf _ _ _ (Hgb _ _ _ _ HMk Hcon))).
    assert (HnaA0 : forall k Mk b1, ind_member D k = Some Mk -> List.nth_error Bks0 k = Some b1 -> brs_names (im_cons Mk) (eb_brs b1)).
    { intros * HMk Hb1; destruct (nth_error_blocks_sub_inv _ _ _ _ Hb1) as (b2 & Hb2 & ->).
      rewrite eb_brs_sub; apply brs_names_sub; exact (HnaA _ _ _ HMk Hb2). }
    assert (HarA0 : forall k Mk b1 c gs n B, ind_member D k = Some Mk -> List.nth_error Bks0 k = Some b1 -> ind_con Mk c = Some gs ->
               In (c, n, B) (eb_brs b1) -> n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat).
    { intros * HMk Hb1 Hcon Hin; destruct (nth_error_blocks_sub_inv _ _ _ _ Hb1) as (b2 & Hb2 & ->).
      rewrite eb_brs_sub in Hin; destruct (brs_in_sub _ _ _ _ _ Hin) as [B0 Hin0]; exact (HarA _ _ _ _ _ _ _ HMk Hb2 Hcon Hin0). }
    assert (HBB0 : forall k Mk b1 b1' c gs n B B', ind_member D k = Some Mk -> List.nth_error Bks0 k = Some b1 ->
               List.nth_error Bks0 k = Some b1' -> ind_con Mk c = Some gs ->
               brs_lookup (eb_brs b1) c = Some (n, B) -> brs_lookup (eb_brs b1') c = Some (n, B') ->
               elim_bctx p D Mk gs (blocks_motives Bks0) Us0 ++ Ψ ⊨ B ≈ B' : elim_bty p D k Mk c gs (eb_motive b1) Us0).
    { intros * HMk Hb1 Hb1' Hcon Hlk Hlk'; rewrite Hb1 in Hb1'; injection Hb1' as <-; rewrite Hlk in Hlk'; injection Hlk' as <-.
      destruct (nth_error_blocks_sub_inv _ _ _ _ Hb1) as (b2 & Hb2 & ->).
      rewrite eb_brs_sub in Hlk; destruct (brs_lookup_sub_inv _ _ _ _ _ Hlk) as (B0 & Hlk0 & ->).
      pose proof (HarA _ _ _ _ _ _ _ HMk Hb2 Hcon (brs_lookup_in _ _ _ _ Hlk0)) as ->.
      pose proof (rel_exp_under_ctx_gsub (Hgb _ _ _ _ HMk Hcon) (HBv _ _ _ _ _ _ _ HMk Hb2 Hcon (brs_lookup_in _ _ _ _ Hlk0))) as H.
      replace (cargs_nrec D gs + List.length gs + im_nn Mk) with (im_nn Mk + List.length gs + cargs_nrec D gs) in H by lia.
      rewrite (elim_bty_sub p D k Mk c gs _ Us β Hc HMk HUl) in H.
      rewrite eb_motive_sub, (HnmA _ _ _ HMk Hb2); exact H. }
    assert (Hgr : elim_grp D (if ind_has_views D then Some p else oq) p j).
    { destruct (ind_has_views D) eqn:Hv; [ left; reflexivity |].
      destruct Hoq as [-> | ->]; [ left; reflexivity | right; split; [ reflexivity |] ].
      apply (decl_typed_order _ _ _ Hdt _ _ HMj); exact (no_views_decl _ _ _ Hv HMj). }
    assert (Hb0 : List.nth_error Bks0 j = Some (eblock_sub b β)) by (unfold Bks0; rewrite nth_error_blocks_sub, Hb; reflexivity).
    pose proof (rel_exp_under_ctx_elim_at VP p D HP HPD Ψ _ _ j Mj (eblock_sub b β) Bks0 Bks0 Us0 Us0 Ns M M i HΨ Hgr Hgr
                  HMj Hb0 HBks0 HBks0 HUl0 HUs0 HUl0 HUU0 HNl HNs HM HnmA0 HnmA0 HMall0 HAA0 HnaA0
                  (fun _ _ _ H1 H2 => ltac:(rewrite H1 in H2; injection H2 as <-; reflexivity)) HBc0 HarA0 HBB0) as H.
    rewrite eb_motive_sub, (HnmA _ _ _ HMj Hb) in H.
    replace (S (im_nn Mj)) with (List.length (Ns ++ M :: nil)) in H by (rewrite List.length_app, HNl; cbn; lia).
    rewrite exp_sub_qn_of_list in H.
    rewrite (blocks_motives_nth _ _ _ Hb); unfold elim_at; destruct (ind_has_views D); exact H.
  Qed.

  (** *** The Recursive Results, Typed

      The recursive result along a leaf path of a frame's shape, past [kd]
      of its domains, is of the type of the result along it: the
      eliminator's blocks moved past the frame's base and the domains.  By
      strong induction on the member bounding the record view the shape
      ends in, and on the domains left. *)
  Lemma leaf_ih_valid : forall n k Mk ck gk gs1 t gs2, ind_member D k = Some Mk -> ind_con Mk ck = Some gk ->
      gk = gs1 ++ ca_rec t :: gs2 ->
      forall Mj, ind_member D (ptyp_mem t) = Some Mj -> (im_is_rview Mj = true -> ptyp_mem t < n) ->
      forall Ψ0 σ0 β0 x0, sem_frame p D Γ Us Mk gs1 t Ψ0 σ0 β0 x0 ->
      forall kd l, kd <= List.length (ptyp_doms t) ->
      In l (shape_leaves (rv_leaves D) (im_nn Mk + List.length (cargs_nonrec gs1) + kd) (ptyp_skip kd t)) ->
      tele_sub (doms_ctx (List.firstn kd (ptyp_doms t))) σ0 ++ Ψ0 ++ Γ
        ⊨ leaf_ih p D oq (List.map (fun U => U[sb_shift_iter kd β0]) Us) (blocks_sub Bks (sb_shift_iter kd β0))
            (sb_qn kd σ0) (apps_vars_iter kd x0) l
        : leaf_ihty (blocks_motives Bks) (sb_shift_iter kd β0) (sb_qn kd σ0) (apps_vars_iter kd x0) l.
  Proof.
    destruct (rel_ctx_wf_per_ctx_env HΓ) as [RΓ HRΓ].
    destruct (rel_ctx_wf_per_ctx_env (valid_ind_decl_uparams _ HD)) as [RU HRU].
    induction n as [n IHn] using Wf_nat.lt_wf_ind.
    intros k Mk ck gk gs1 t gs2 HMk Hck Heq0 Mj HMj Hrk Ψ0 σ0 β0 x0 Hf kd.
    remember (List.length (ptyp_doms t) - kd) as mm eqn:Hm; revert kd Hm.
    induction mm as [| mm IHm]; intros kd Hm l Hk Hin.
    - assert (kd = List.length (ptyp_doms t)) as -> by lia.
      rewrite (ptyp_skip_end t) in Hin; cbn [shape_leaves] in Hin.
      rewrite <- (frame_doms_tele VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HMall k Mk ck gk gs1 t gs2 HMk Hck Heq0
                    Ψ0 σ0 β0 x0 Hf Mj HMj).
      destruct (im_is_rview Mj) eqn:Hrv.
      + (** A record view: on to the frame of the field the path
            projects. *)
        specialize (Hrk eq_refl).
        destruct (im_head Mj) as [pm | qc k' Is0 vm | qr Is fl] eqn:Hh; unfold im_is_rview in Hrv; rewrite Hh in Hrv;
          try discriminate.
        destruct (rview_struct_con _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HMj Hh) as (gsr & Hcs & Hlen).
        pose proof (leaves_coherent_of_order _ (rview_struct_order _ _ _ (decl_typed_rstruct _ _ _ Hdt))) as Hco.
        rewrite (Hco _ _ _ _ _ _ _ HMj Hh Hcs) in Hin.
        apply List.in_map_iff in Hin as (l0 & <- & Hin0).
        rewrite leaf_ih_wk, leaf_ihty_wk.
        apply fields_leaves_in in Hin0 as (fs1 & f & tf & fs2 & l1 & Ec & -> & Hin1).
        cbn [leaf_ih leaf_ihty List.app] in Hin1 |- *.
        pose proof (record_view_step_frame VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HMall k Mk ck gk gs1 t gs2 HMk Hck Heq0
                      Ψ0 σ0 β0 x0 Hf Mj HMj _ _ _ _ _ _ _ _ _ Hh Hcs Ec) as Hf'; cbv zeta in Hf'.
        destruct (combine_split_at _ _ _ _ _ _ (eq_sym Hlen) Ec) as [Efl Egs].
        pose proof (ind_con_single _ _ _ Hcs) as Hcon'.
        destruct (rview_params _ _ _ _ _ _ _ _ Hdt HMj Hh) as [_ Hnn].
        destruct (length_rec_ps D HD _ _ HMj _ _ _ _ _ Hcon' Egs) as (Mt & HMt & _).
        assert (Hrk' : im_is_rview Mt = true -> ptyp_mem tf < ptyp_mem t)
          by (intros HrT; exact (rview_struct_order _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs Egs HMt HrT)).
        set (σv := ι (wk_shiftn (im_nn Mk + List.length (cargs_nonrec gs1) + List.length (ptyp_doms t))) ⨟ sb_qn (List.length (ptyp_doms t)) σ0).
        assert (Eσ : sb_eq (sb_of_list σv (projections_of (fields_args fs1) (apps_vars_iter (List.length (ptyp_doms t)) x0)))
                       (ι (wk_pat (cargs_pat (List.map snd fs1)))
                          ⨟ sb_of_list σv (projections_of (List.map fst fs1) (apps_vars_iter (List.length (ptyp_doms t)) x0)))).
        { pose proof (wk_pat_projections fs1 nil σv (apps_vars_iter (List.length (ptyp_doms t)) x0)) as E.
          rewrite List.app_nil_r in E; symmetry; etransitivity; [ exact E |]; apply sb_of_list_cong; intros z; reflexivity. }
        rewrite (leaf_ih_sb_eq _ _ _ l1 _ _ _ _ _ Eσ), (leaf_ihty_sb_eq l1 _ _ (sb_shift_iter (List.length (ptyp_doms t)) β0) _ _ _ (reflexivity _) Eσ).
        assert (Hin1' : In l1 (shape_leaves (rv_leaves D) (im_nn Mj + List.length (cargs_nonrec (List.map snd fs1)) + 0) (ptyp_skip 0 tf))).
        { replace (im_nn Mj + List.length (cargs_nonrec (List.map snd fs1)) + 0) with (List.length (fields_args fs1)); [ exact Hin1 |].
          rewrite Hnn; clear; induction fs1 as [| [? []] fs1 IH]; cbn [List.map snd fields_args cargs_nonrec]; cbn [List.length]; lia. }
        pose proof (IHn (ptyp_mem t) Hrk (ptyp_mem t) Mj rview_con gsr (List.map snd fs1) tf (List.map snd fs2) HMj Hcon' Egs Mt HMt Hrk'
                      _ _ _ _ Hf' 0 l1 (Nat.le_0_l _) Hin1') as H.
        cbn [List.firstn doms_ctx List.map List.rev tele_sub List.app sb_shift_iter sb_qn apps_vars_iter] in H.
        rewrite <- List.app_assoc in H; exact H.
      + (** A member with a block: its eliminator. *)
        rewrite (rv_leaves_not_rview _ _ _ HMj Hrv) in Hin; destruct Hin as [<- | []].
        cbn [leaf_ih leaf_ihty].
        apply (elim_at_valid _ _ (ptyp_mem t) Mj _ _
                 (frame_gsub_end_base VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HMall k Mk ck gk gs1 t gs2 HMk Hck Heq0
                    Ψ0 σ0 β0 x0 Hf Mj HMj) HMj Hrv).
        * rewrite List.length_map; exact (frame_end_params_len VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HMall k Mk ck gk gs1 t gs2
                                             HMk Hck Heq0 Ψ0 σ0 β0 x0 Hf Mj HMj).
        * apply (frame_end_params_each VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HMall k Mk ck gk gs1 t gs2 HMk Hck Heq0
                   Ψ0 σ0 β0 x0 Hf Mj HMj).
          intros y Hy; cbn [sb_compose].
          rewrite sb_of_list_map by (rewrite HUl; lia); rewrite <- sentry_exp_sub; reflexivity.
        * exact (frame_end_arg_typed VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HMall k Mk ck gk gs1 t gs2 HMk Hck Heq0
                   Ψ0 σ0 β0 x0 Hf Mj HMj).
    - (** At a domain. *)
      assert (Hk' : kd < List.length (ptyp_doms t)) by lia.
      destruct (ptyp_skip_lt kd t Hk') as (Bk & HBk & Hs).
      rewrite Hs in Hin; cbn [shape_leaves] in Hin.
      apply List.in_map_iff in Hin as (l' & <- & Hin').
      cbn [leaf_ih leaf_ihty].
      destruct (valid_ind_decl_dom _ HD k Mk ck gk gs1 t gs2 kd Bk HMk Hck Heq0 HBk) as (_ & j & HBv0).
      rewrite <- (frame_strat VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HMall k Mk ck gk gs1 t gs2 HMk Hck Heq0) in HBv0.
      pose proof (closed_app_valid _ _ _ _ _
                    (frame_doms_ass VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HMall k Mk ck gk gs1 t gs2 HMk Hck Heq0 kd)
                    (frame_doms_valid VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HMall k Mk ck gk gs1 t gs2 HMk Hck Heq0 kd
                       ltac:(lia)) HΓ HBv0) as HBv1.
      rewrite <- !List.app_assoc in HBv1.
      pose proof (rel_exp_under_ctx_gsub (frame_gsub_doms_at VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HMall k Mk ck gk gs1 t gs2
                                            HMk Hck Heq0 Ψ0 σ0 β0 x0 Hf kd ltac:(lia)) HBv1) as HBk'; cbn [exp_sub] in HBk'.
      assert (HUs1 : List.map (fun U => U[↑]ʷ) (List.map (fun U => U[sb_shift_iter kd β0]) Us)
                     = List.map (fun U => U[sb_shift_iter (S kd) β0]) Us)
        by (rewrite List.map_map; apply List.map_ext; intros; rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity).
      assert (HBs1 : blocks_wk (blocks_sub Bks (sb_shift_iter kd β0)) ↑ = blocks_sub Bks (sb_shift_iter (S kd) β0))
        by (rewrite <- blocks_sub_of_wk, blocks_sub_sub; reflexivity).
      rewrite HUs1, HBs1.
      assert (Hin'' : In l' (shape_leaves (rv_leaves D) (im_nn Mk + List.length (cargs_nonrec gs1) + S kd) (ptyp_skip (S kd) t)))
        by (replace (im_nn Mk + List.length (cargs_nonrec gs1) + S kd) with (S (im_nn Mk + List.length (cargs_nonrec gs1) + kd)) by lia;
            exact Hin').
      pose proof (IHm (S kd) ltac:(lia) l' ltac:(lia) Hin'') as H.
      rewrite (firstn_S_snoc _ _ _ HBk), doms_ctx_snoc in H; cbn [tele_sub List.app centry_sub] in H.
      rewrite (frame_doms_len VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HMall k Mk ck gk gs1 t gs2 HMk Hck Heq0 kd ltac:(lia)) in H.
      exact (rel_exp_under_ctx_fn_cong HBk' H).
  Qed.
End Blocks.

(** ** The Recursive Results as Terms, along a Recursive Argument

    The group's blocks [Bks] valid at the uniform parameters [Us] over
    [Γ], at an environment [C] of [Γ]: walking the leaf paths of a
    recursive argument in a frame, the values of the recursive results as
    terms ([leaf_ih]) against the eliminator's own recursive results at a
    related argument. *)
Section LeafVals.
  #[local] Set Default Proof Using "All".
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups VP) (HPD : VP p D).
  Let Hvg := valid_groups_valid VP HP p D HPD.
  Let HD := valid_group_valid _ _ Hvg.
  Let Hc := valid_group_closed _ _ Hvg.
  Let Hl := valid_group_lookup _ _ Hvg.
  Let Hdt := valid_group_typed _ _ Hvg.
  Let Ua : tele_ass (ind_uparams D) := uparams_ass D Hc.

  Variable (Γ : ctx) (oq : option qname) (Us : list exp) (Bks : list eblock) (i : nat).
  Hypotheses (HΓ : ⊨ Γ) (Hoq : oq = Some p \/ oq = None) (HUl : List.length Us = ind_nu D)
    (HUs : forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Γ ⊨ U : T)
    (HBks : List.length Bks = ind_nblk D)
    (HnmA : blocks_nm_ok D Bks)
    (HMall : forall j Mj, ind_member D j = Some Mj -> ⊨ elim_mctx p D j Mj Us ++ Γ)
    (HAv : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b : Typeω@i)
    (HnaA : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> brs_names (im_cons Mj) (eb_brs b))
    (HBc : forall j Mj c gs, ind_member D j = Some Mj -> ind_con Mj c = Some gs ->
             ⊨ elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ)
    (HarA : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> ind_con Mj c = Some gs ->
              In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat)
    (HBv : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> ind_con Mj c = Some gs ->
             In (c, n, B) (eb_brs b) ->
             elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ ⊨ B : elim_bty p D j Mj c gs (eb_motive b) Us).
  (** The blocks of the members with one. *)
  Let HBks' := block_of_nblk D Bks Hdt HBks.

  Lemma uparams_have_types : forall j U, List.nth_error Us j = Some U -> exists T, Γ ⊨ U : T.
  Proof.
    intros j U HU.
    destruct (nth_error_lt_some' (tele_insts (ind_uparams D) Id Us) j) as [T HT].
    { rewrite length_tele_insts by exact Ua.
      assert (j < List.length Us) by (apply List.nth_error_Some; congruence); unfold ind_nu in *; lia. }
    exists T; exact (HUs _ _ _ HU HT).
  Qed.

  (** The group of the eliminator at a member, as [elim_at] writes it. *)
  Lemma elim_at_grp : forall j Mj, ind_member D j = Some Mj -> elim_grp D (if ind_has_views D then Some p else oq) p j.
  Proof.
    intros j Mj HMj.
    destruct (ind_has_views D) eqn:Hv; [ left; reflexivity |].
    destruct Hoq as [-> | ->]; [ left; reflexivity | right; split; [ reflexivity |] ].
    apply (decl_typed_order _ _ _ Hdt _ _ HMj); exact (no_views_decl _ _ _ Hv HMj).
  Qed.

  Variable (RΓ RU : relation env).
  Hypotheses (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).
  Variable (C : env) (u0 : list domain).
  Hypotheses (HCC : RΓ C C) (HUC : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ C ↘ u0).
  Let nr := canon_nparams_rel D u0.
  Let ar := canon_args_rel D u0.
  Let dr := canon_doms_rel u0.
  Let G := grp_rel p D u0 nr ar dr.
  Let Rel := fun j ns m ns' m' =>
    per_head (List.nth j (blocks_motives Bks) a_True) (List.nth j (blocks_motives Bks) a_True)
      (env_args C (ns ++ m :: nil)) (env_args C (ns' ++ m' :: nil)).
  #[local] Abbreviation u0_len' := (u0_len D Us HUl C u0 HUC).
  #[local] Abbreviation u0_env' := (u0_env VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C u0 HCC HUC).
  #[local] Abbreviation u0_gargs' := (u0_gargs VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C u0 HCC HUC).
  #[local] Abbreviation Hcp := (vg_canon p D Hvg u0 u0_gargs' u0_len').
  #[local] Abbreviation HnP := (ind_canon_props_np_per _ _ Hcp).
  #[local] Abbreviation HnI := (ind_canon_props_np_iff _ _ Hcp).
  #[local] Abbreviation HaP := (ind_canon_props_arg_per _ _ Hcp).
  #[local] Abbreviation HaI := (ind_canon_props_arg_iff _ _ Hcp).
  #[local] Abbreviation HdP := (ind_canon_props_dom_per _ _ Hcp).
  #[local] Abbreviation HdI := (ind_canon_props_dom_iff _ _ Hcp).
  #[local] Abbreviation Had := (vg_adm p D Hvg u0 u0 u0_gargs' u0_len' u0_gargs').
  #[local] Abbreviation Hass := (valid_group_ass _ _ Hvg).
  #[local] Abbreviation isym := (proj1 (ind_rel_sym_all p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (okr_at D u0 nr))).
  #[local] Abbreviation itrans := (proj1 (ind_rel_trans_all p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (okr_at D u0 nr))).
  (** The lemmas of [Elim.v]: of the frames, of the base at [C], and of
      the motives at [C] on both sides. *)
  #[local] Abbreviation SF f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HMall).
  #[local] Abbreviation EB f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C u0 HCC HUC).
  #[local] Abbreviation EP f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C u0 HCC HUC C HCC Bks i HBks' HMall HAv).

  (** *** The Link of a Term to a Recursive Argument

      A term [x] over [C] extended by the values [ys], that is a recursive
      argument related to [v] whenever moved past further values [zs] that
      some context of [Γ]'s weakening relates to themselves: its value
      there is related to [v] at the shape [t]. *)
  Definition iota_arg_link (k : nat) (pre : list domain) (t : ptyp) (v : domain) (x : exp) (ys : list domain) : Prop :=
    forall Δ RΔ zs, EF Δ ≈ Δ ∈ per_ctx_env ↘ RΔ ->
      Δ ⊨ˢ sb_of_wk (wk_shiftn (List.length ys + List.length zs)) ≈ sb_of_wk (wk_shiftn (List.length ys + List.length zs)) : Γ ->
      RΔ (env_args C (ys ++ zs)) (env_args C (ys ++ zs)) ->
      exists pre0 m0, ⟦ x[wk_shiftn (List.length zs)]ʷ ⟧ env_args C (ys ++ zs) ↘ m0 /\
        rec_arg_rel p D (okr_at D u0 nr) nr ar dr k u0 u0 pre pre0 t v m0.

  (** What the walk along a recursive argument gives: the values of the
      recursive results as terms ([leaf_ih]) at an environment, the
      eliminator's own recursive results at the related argument [v'],
      and their relation, the terms' side on the left. *)
  #[warnings="-cannot-define-projection"]
  Record leaf_ihs_vals_out (k : nat) (pre pre' : list domain) (t : ptyp) (v v' : domain) (E : env)
      (Us0 : list exp) (Bks0 : list eblock) (σ : sub) (x : exp) (mk : nat) : Prop := mk_leaf_ihs_vals_out
    { (** The values of the recursive results as terms *)
      leaf_ihs_vals_terms : list domain
      (** The eliminator's own recursive results at [v'] *)
    ; leaf_ihs_vals_own : list domain
      (** The terms', at [E] *)
    ; leaf_ihs_vals_eval_terms :
        ⟦ List.map (leaf_ih p D oq Us0 Bks0 σ x) (shape_leaves (rv_leaves D) mk t) ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ leaf_ihs_vals_terms
      (** The eliminator's own, at [C] *)
    ; leaf_ihs_vals_eval_own : ⟦ih v' of t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C ↘ leaf_ihs_vals_own
      (** Related along the leaf paths *)
    ; leaf_ihs_vals_related : rec_result_rel D dr Rel k u0 u0 pre pre' t v v' leaf_ihs_vals_terms leaf_ihs_vals_own }.

  (** *** Along a Leaf Path

      A recursive argument [v] of the shape [t] of a frame, past [kd] of its
      domains at values [ys0], related to [v'] and linked to the frame's
      argument past them, over [C] extended by the frame's base values
      [zs] and the domains' values [ys] on the terms' side: the values of
      the terms and the recursive results at [v'] are related.  By strong
      induction on the member bounding the record view the shape ends in,
      and on the domains left. *)
  Lemma leaf_ihs_vals : forall n k Mk ck gk gs1 t gs2, ind_member D k = Some Mk -> ind_con Mk ck = Some gk ->
      gk = gs1 ++ ca_rec t :: gs2 ->
      forall Mj, ind_member D (ptyp_mem t) = Some Mj -> (im_is_rview Mj = true -> ptyp_mem t < n) ->
      forall Ψ0 σ0 β0 x0, sem_frame p D Γ Us Mk gs1 t Ψ0 σ0 β0 x0 -> forall RΨ, EF Ψ0 ++ Γ ≈ Ψ0 ++ Γ ∈ per_ctx_env ↘ RΨ ->
      forall zs w X nv vx ms nv0, sem_frame_vals D RΓ RU C u0 Mk gs1 Ψ0 σ0 x0 RΨ (env_args C zs) C zs w X nv vx ->
      tele_rel (nr k) (List.rev (im_nparams Mk)) ms X -> tele_prefix_rel (ar k ms ck) (List.length (cargs_nonrec gs1)) nv0 nv ->
      forall kd ys0 ys v v' pre', kd <= List.length (ptyp_doms t) -> List.length ys = kd ->
      tele_prefix_rel (shape_doms_rel (dr k) ms nv0 (ptyp_doms t)) kd ys0 ys ->
      rec_arg_rel p D (okr_at D u0 nr) nr ar dr k u0 u0 (ms ++ nv0 ++ ys0) pre' (ptyp_skip kd t) v v' ->
      iota_arg_link k (ms ++ nv0 ++ ys0) (ptyp_skip kd t) v (apps_vars_iter kd x0) (zs ++ ys) ->
      leaf_ihs_vals_out k (ms ++ nv0 ++ ys0) pre' (ptyp_skip kd t) v v' (env_args C (zs ++ ys))
        (List.map (fun U => U[sb_shift_iter kd β0]) Us) (blocks_sub Bks (sb_shift_iter kd β0)) (sb_qn kd σ0) (apps_vars_iter kd x0)
        (im_nn Mk + List.length (cargs_nonrec gs1) + kd).
  Proof.
    assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
    pose proof (leaves_coherent_of_order _ (rview_struct_order _ _ _ (decl_typed_rstruct _ _ _ Hdt))) as Hco.
    induction n as [n IHn] using Wf_nat.lt_wf_ind.
    intros k Mk ck gk gs1 t gs2 HMk Hck Heq0 Mj HMj Hrk Ψ0 σ0 β0 x0 Hf RΨ HRΨ zs w X nv vx ms nv0 Hv HX Hnv kd.
    remember (List.length (ptyp_doms t) - kd) as mm eqn:Hm; revert kd Hm.
    induction mm as [| mm IHm]; intros kd Hm ys0 ys v v' pre' Hk Lys Hys Hsh Hlk.
    - (** At the end of the shape: the environment of its end context,
          and the term's value there. *)
      assert (kd = List.length (ptyp_doms t)) as -> by lia.
      rewrite (ptyp_skip_end t) in Hsh, Hlk |- *.
      pose proof (SF frame_end_ctx_valid k Mk ck gk gs1 t gs2 HMk Hck Heq0 Ψ0 σ0 β0 x0 Hf Mj HMj) as HΨL.
      destruct (rel_ctx_wf_per_ctx_env HΨL) as [RSL HRSL].
      pose proof (EP frame_end_env k Mk ck gk gs1 t gs2 HMk Hck Heq0 Ψ0 σ0 β0 x0 Hf RΨ HRΨ Mj HMj ms nv0 ys0 (env_args C zs) C zs w X nv vx ys
                    Hv Lys HX Hnv Hys RSL HRSL) as HEL.
      rewrite <- env_args_app in HEL.
      pose proof (frame_vals_split_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hv) as Lzs.
      set (σL := sb_shift_iter (List.length (ptyp_doms t)) β0).
      pose proof (SF frame_gsub_end_base k Mk ck gk gs1 t gs2 HMk Hck Heq0 Ψ0 σ0 β0 x0 Hf Mj HMj) as HgL; fold σL in HgL.
      pose proof (SF frame_end_base_eq k Mk ck gk gs1 t gs2 HMk Hck Heq0 Ψ0 σ0 β0 x0 Hf Mj HMj) as EσL; fold σL in EσL.
      assert (Lall : List.length (tele_sub (ptyp_tele t) σ0 ++ Ψ0) = List.length (zs ++ ys))
        by (rewrite !List.length_app, length_tele_sub, Lzs, Lys; unfold ptyp_tele; rewrite doms_ctx_length; lia).
      assert (HwL : tele_sub (ptyp_tele t) σ0 ++ Ψ0 ++ Γ ⊨ˢ σL ≈ σL : Γ) by exact (gsub_valid HgL).
      assert (Hev : ⟦ σL ⟧s env_args C (zs ++ ys) ↘ C).
      { apply (eval_sub_sb_eq _ _ _ _ (symmetry EσL)).
        pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn (List.length (zs ++ ys))) (env_args C (zs ++ ys)) (wk_mono_shiftn _)) as H.
        rewrite eval_wk_shiftn_args in H; rewrite Lall; exact H. }
      assert (Hwk : tele_sub (ptyp_tele t) σ0 ++ Ψ0 ++ Γ
                      ⊨ˢ sb_of_wk (wk_shiftn (List.length (zs ++ ys) + List.length (@nil domain)))
                       ≈ sb_of_wk (wk_shiftn (List.length (zs ++ ys) + List.length (@nil domain))) : Γ).
      { cbn [List.length]; rewrite Nat.add_0_r, <- Lall.
        exact (rel_sub_under_ctx_sb_eq HwL EσL EσL). }
      destruct (Hlk _ _ nil HRSL Hwk ltac:(rewrite List.app_nil_r; exact HEL)) as (pre0 & m0 & Em0 & Hvm).
      rewrite List.app_nil_r, exp_wk_id_ext in Em0 by apply wk_shiftn_zero.
      destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvm) as (bs & bs0 & Ebs & Ebs0 & _ & _ & Hvm').
      destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh) as (bs1 & bs' & Ebs1 & Ebs' & _ & _ & Hff).
      pose proof (functional_eval_exps' _ _ _ _ Ebs1 Ebs) as ->.
      destruct (im_is_rview Mj) eqn:Hrv.
      + (** A record view: the recursive results of its fields, at the
            projections, each along the frame of the field. *)
        specialize (Hrk eq_refl).
        destruct (im_head Mj) as [pm | qc k' Is0 vm | qr Is fl] eqn:Hh; unfold im_is_rview in Hrv; rewrite Hh in Hrv;
          try discriminate.
        destruct (rview_struct_con _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HMj Hh) as (gsr & Hcs & Hlen).
        pose proof (ind_con_single _ _ _ Hcs) as Hcon'.
        destruct (rview_params _ _ _ _ _ _ _ _ Hdt HMj Hh) as [_ Hnn].
        destruct (ind_rel_rview_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs Hff) as (wsv & wsv' & Ewsv & Ewsv' & _ & Hcav).
        destruct (ind_rel_rview_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs Hvm') as (wsv0 & ws0 & Ewsv0 & Ews0 & Har0 & _).
        pose proof (functional_eval_projs _ _ _ _ Ewsv0 Ewsv) as ->.
        pose proof (eval_projs_length _ _ _ Ewsv) as Lwsv; pose proof (eval_projs_length _ _ _ Ewsv') as Lwsv'.
        set (xL := apps_vars_iter (List.length (ptyp_doms t)) x0) in *.
        set (φσ := ι (wk_shiftn (im_nn Mk + List.length (cargs_nonrec gs1) + List.length (ptyp_doms t)))
                     ⨟ sb_qn (List.length (ptyp_doms t)) σ0).
        assert (Ex : ⟦ xL ⟧ env_args (env_args C zs) ys ↘ m0) by (rewrite <- env_args_app; exact Em0).
        assert (Hnil : tele_rel (nr (ptyp_mem t)) (List.rev (im_nparams Mj)) nil nil).
        { assert (Enp : im_nparams Mj = nil) by (unfold im_nn in Hnn; destruct (im_nparams Mj); [ reflexivity | discriminate ]).
          rewrite Enp; split; [ reflexivity | exact I ]. }
        (** The fields after [fs1]: their recursive results, along the
            frames of the recursive ones. *)
        assert (Hfw : forall fs2 fs1, List.combine fl gsr = fs1 ++ fs2 ->
          exists rs rs',
            ⟦ List.map (leaf_ih p D oq (List.map (fun U => U[σL]) Us) (blocks_sub Bks σL) φσ xL)
                (fields_leaves (rv_leaves D) (fields_args fs1) fs2) ⟧* gc_deps ⍮ gc_stack ⍮ env_args C (zs ++ ys) ↘ rs /\
            ⟦ihs List.skipn (List.length fs1) wsv' of List.map snd fs2 under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C ↘ rs' /\
            rec_results_rel D dr Rel (ptyp_mem t) u0 u0
              (nonrec_arg_vals (List.map snd fs1) (List.firstn (List.length fs1) wsv))
              (nonrec_arg_vals (List.map snd fs1) (List.firstn (List.length fs1) wsv'))
              (List.map snd fs2) (List.skipn (List.length fs1) wsv) (List.skipn (List.length fs1) wsv') rs rs').
        { induction fs2 as [| [f g] fs2 IHf]; intros fs1 Ec.
          - rewrite List.app_nil_r in Ec.
            assert (Lfs1 : List.length fs1 = List.length fl) by (rewrite <- Ec, List.length_combine; lia).
            rewrite !List.skipn_all2 by lia.
            exists nil, nil; split; [ cbn; constructor | split; [ constructor | constructor ] ].
          - destruct (combine_app_split _ _ _ _ (eq_sym Hlen) Ec) as [Efl Egs].
            cbn [List.map] in Efl, Egs.
            assert (Hlt : List.length fs1 < List.length wsv) by (rewrite Lwsv, Efl, List.length_app, !List.length_map; cbn; lia).
            destruct (nth_error_lt_some wsv _ Hlt) as [wf Hwf].
            destruct (nth_error_lt_some wsv' (List.length fs1) ltac:(lia)) as [wf' Hwf'].
            rewrite (skipn_nth_cons _ _ _ Hwf), (skipn_nth_cons _ _ _ Hwf').
            assert (Ec' : List.combine fl gsr = (fs1 ++ (f, g) :: nil) ++ fs2) by (rewrite Ec, <- List.app_assoc; reflexivity).
            destruct (IHf _ Ec') as (rs2 & rs2' & Ers2 & Ers2' & Hrr2).
            rewrite List.length_app, Nat.add_1_r in Ers2', Hrr2; cbn [List.length] in Ers2', Hrr2.
            rewrite (firstn_S_nth _ _ _ Hwf), (firstn_S_nth _ _ _ Hwf'), List.map_app, !nonrec_arg_vals_app in Hrr2
              by (rewrite List.length_firstn, List.length_map; lia).
            rewrite fields_args_app in Ers2.
            destruct g as [A | tf].
            + (** A non-recursive field joins the prefixes. *)
              cbn [List.map snd fields_leaves nonrec_arg_vals fields_args] in Ers2, Hrr2 |- *.
              exists rs2, rs2'; split; [ exact Ers2 | split; [ constructor; exact Ers2' | constructor; exact Hrr2 ] ].
            + (** A recursive field: along its frame. *)
              cbn [List.map snd fields_leaves nonrec_arg_vals fields_args] in Ers2, Hrr2 |- *.
              rewrite !List.app_nil_r in Ers2, Hrr2.
              destruct (combine_split_at _ _ _ _ _ _ (eq_sym Hlen) Ec) as [Efl' Egs'].
              destruct (length_rec_ps D HD _ _ HMj _ _ _ _ _ Hcon' Egs') as (Mt & HMt & _).
              assert (Hrk' : im_is_rview Mt = true -> ptyp_mem tf < ptyp_mem t)
                by (intros HrT; exact (rview_struct_order _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs Egs' HMt HrT)).
              pose proof (record_view_step_frame VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HMall k Mk ck gk gs1 t gs2 HMk Hck Heq0
                            Ψ0 σ0 β0 x0 Hf Mj HMj _ _ _ _ _ _ _ _ _ Hh Hcs Ec) as Hf'; cbv zeta in Hf'.
              destruct (rel_ctx_wf_per_ctx_env (sem_frame_ctx _ _ _ _ _ _ _ _ _ _ _ Hf')) as [RΨ' HRΨ'].
              destruct (EP record_view_step_vals k Mk ck gk gs1 t gs2 HMk Hck Heq0 Ψ0 σ0 β0 x0 Hf RΨ HRΨ Mj HMj _ _ _ _ _ _ _ _ _ Hh Hcs Ec
                          ms nv0 ys0 (env_args C zs) C zs w X nv vx ys m0 ws0 Hv Lys HX Hnv Hys Ex Ews0 RΨ' HRΨ') as (w' & Hv').
              rewrite <- env_args_app in Hv'.
              (** The non-recursive fields before, related as the
                  pseudo-constructor's arguments. *)
              assert (Hnvf : tele_prefix_rel (ar (ptyp_mem t) nil rview_con) (List.length (cargs_nonrec (List.map snd fs1)))
                               (nonrec_arg_vals (List.map snd fs1) (List.firstn (List.length fs1) wsv))
                               (nonrec_arg_vals (List.map snd fs1) (List.firstn (List.length fs1) ws0))).
              { pose proof (eval_projs_length _ _ _ Ews0) as Lws0.
                replace (List.length fs1) with (List.length (List.map snd fs1)) by apply List.length_map.
                rewrite Egs' in Har0.
                rewrite <- !(nonrec_arg_vals_firstn _ (ca_rec tf :: List.map snd fs2))
                  by (rewrite <- Egs'; rewrite ?Lwsv, ?Lws0; exact (eq_sym Hlen)).
                apply tele_prefix_rel_of_full with (T := cargs_nonrec (List.map snd fs1 ++ ca_rec tf :: List.map snd fs2)); [ exact Har0 |].
                rewrite cargs_nonrec_app, List.length_app; lia. }
              (** The field of the two sides. *)
              destruct (con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcav (List.map snd fs1) tf (List.map snd fs2) Egs')
                as (x & x' & Hx & Hx' & Hshf).
              rewrite List.length_map in Hx, Hx', Hshf.
              rewrite Hwf in Hx; injection Hx as <-; rewrite Hwf' in Hx'; injection Hx' as <-.
              (** The field's link: the projection of the term. *)
              assert (Hlkf : iota_arg_link (ptyp_mem t) (nil ++ nonrec_arg_vals (List.map snd fs1) (List.firstn (List.length fs1) wsv) ++ nil)
                               (ptyp_skip 0 tf) wf (apps_vars_iter 0 (a_proj f xL)) ((zs ++ ys) ++ nil)).
              { intros Δ RΔ zs2 HRΔ Hw HE; rewrite List.app_nil_r in Hw, HE |- *.
                destruct (Hlk _ _ _ HRΔ Hw HE) as (pre1 & m1 & Em1 & Hvm1).
                destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvm1) as (bq & bq' & _ & _ & _ & _ & Hvm1').
                destruct (ind_rel_rview_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hcs Hvm1') as (wsv1 & ws1 & Ewsv1 & Ews1 & _ & Hca1).
                pose proof (functional_eval_projs _ _ _ _ Ewsv1 Ewsv) as ->.
                destruct (con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hca1 (List.map snd fs1) tf (List.map snd fs2) Egs')
                  as (y & y' & Hy & Hy' & Hshy).
                rewrite List.length_map in Hy, Hy', Hshy.
                rewrite Hwf in Hy; injection Hy as <-.
                rewrite Efl' in Ews1.
                destruct (eval_projs_at (List.map fst fs1) f _ _ _ Ews1) as (w1 & Hw1 & Hp1).
                rewrite List.length_map, Hy' in Hw1; injection Hw1 as ->.
                exists (nil ++ nonrec_arg_vals (List.map snd fs1) (List.firstn (List.length fs1) ws1)), w1; split.
                - cbn [apps_vars_iter exp_wk]; econstructor; [ exact Em1 | exact Hp1 ].
                - rewrite List.app_nil_r; exact Hshy. }
              destruct (IHn (ptyp_mem t) Hrk (ptyp_mem t) Mj rview_con gsr (List.map snd fs1) tf (List.map snd fs2) HMj Hcon' Egs' Mt HMt Hrk'
                          _ _ _ _ Hf' RΨ' HRΨ' (zs ++ ys) w' nil _ _ nil _ Hv' Hnil Hnvf 0 nil nil wf wf' _ (Nat.le_0_l _) eq_refl
                          (tele_prefix_rel_nil _) ltac:(cbn [ptyp_skip]; rewrite List.app_nil_r; exact Hshf) Hlkf)
                as [rsf rsf' Erf Erf' Hrf].
              cbn [ptyp_skip sb_shift_iter sb_qn apps_vars_iter List.app] in Erf, Erf', Hrf.
              rewrite !List.app_nil_r in Erf, Hrf.
              exists (rsf ++ rs2), (rsf' ++ rs2'); split; [| split ].
              * rewrite List.map_app, List.map_map; cbn [leaf_ih].
                apply eval_exps_app; [| exact Ers2 ].
                assert (Eσ : sb_eq (ι (wk_pat (cargs_pat (List.map snd fs1)))
                                     ⨟ sb_of_list φσ (projections_of (List.map fst fs1) xL))
                                   (sb_of_list φσ (projections_of (fields_args fs1) xL))).
                { pose proof (wk_pat_projections fs1 nil φσ xL) as E.
                  rewrite List.app_nil_r in E; etransitivity; [ exact E |]; apply sb_of_list_cong; intros z; reflexivity. }
                replace (im_nn Mj + List.length (cargs_nonrec (List.map snd fs1)) + 0) with (List.length (fields_args fs1)) in Erf
                  by (rewrite Hnn, length_fields_args; lia).
                rewrite (List.map_ext _ _ (fun l => leaf_ih_sb_eq _ _ _ l _ _ _ _ _ Eσ)) in Erf.
                exact Erf.
              * econstructor; [ exact Erf' | exact Ers2' ].
              * rewrite ?List.app_nil_r in Hrr2.
                eapply rec_results_rec; [| | exact Hrf | exact Hrr2 ].
                -- rewrite (eval_exps_length _ _ _ Erf), List.length_map; apply length_shape_leaves.
                -- exact (proj1 (proj2 eval_ih_length_all) _ _ _ _ _ _ _ Erf' D Hl Hco). }
        destruct (Hfw (List.combine fl gsr) nil eq_refl) as (rs & rs' & Eihs & Eihs' & Hrr).
        cbn [List.length List.skipn List.firstn List.map nonrec_arg_vals fields_args] in Eihs, Eihs', Hrr.
        rewrite combine_snd_eq in Eihs', Hrr by exact (eq_sym Hlen).
        eapply (mk_leaf_ihs_vals_out _ _ _ _ _ _ _ _ _ _ _ _ rs rs').
        * cbn [shape_leaves]; rewrite (Hco _ _ _ _ _ _ _ HMj Hh Hcs), List.map_map.
          rewrite (List.map_ext _ (leaf_ih p D oq (List.map (fun U => U[σL]) Us) (blocks_sub Bks σL) φσ xL))
            by (intros; apply leaf_ih_wk).
          exact Eihs.
        * eapply eval_ih_rview; [ exact Hl | exact HMj | exact Hh | exact Hcs | exact Ewsv' | exact Eihs' ].
        * eapply rec_result_rview; [ exact HMj | exact Hh | exact Hcs | exact Ewsv | exact Ewsv' | exact Hrr ].
      + (** A member with a block: the eliminators, at the end's outer
            link. *)
        destruct (vals_sub_link VP p D HP HPD Γ HΓ RU HRU Us HUl uparams_have_types
                    (proj2 (gsub_props (gsub_U VP p D HP HPD Γ HΓ Us HUl HUs))) _ RSL σL _ C u0 HRSL HwL HEL Hev HUC)
          as (wL & EwL & HwL0).
        assert (LwL : List.length wL = ind_nu D) by (rewrite (eval_exps_length _ _ _ EwL), List.length_map; exact HUl).
        pose proof (ups_ok VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C u0 HCC HUC wL u0 HwL0 u0_env' LwL u0_len') as Hok.
        destruct (blocks_sub_facts D Bks σL HBks' HnmA HnaA HarA) as (HbA1 & HnmA1 & HnaA1 & HarA1).
        assert (HAA0 : forall j Mj b b0, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> List.nth_error Bks j = Some b0 ->
                   elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b ≈ eb_motive b0 : Typeω@i).
        { intros * HMj0 Hb Hb0; rewrite Hb in Hb0; injection Hb0 as <-; exact (HAv _ _ _ HMj0 Hb). }
        assert (HB0s : forall j Mj b b0 c gs n B0, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
                   List.nth_error Bks j = Some b0 -> ind_con Mj c = Some gs -> brs_lookup (eb_brs b0) c = Some (n, B0) ->
                   n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat /\
                   elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ ⊨ B0 : elim_bty p D j Mj c gs (eb_motive b) Us).
        { intros * HMj0 Hb Hb0 Hcon1 Hlb; rewrite Hb in Hb0; injection Hb0 as <-.
          split; [ exact (HarA _ _ _ _ _ _ _ HMj0 Hb Hcon1 (brs_lookup_in _ _ _ _ Hlb))
                 | exact (HBv _ _ _ _ _ _ _ HMj0 Hb Hcon1 (brs_lookup_in _ _ _ _ Hlb)) ]. }
        pose proof (per_ind_elim_all p D u0 nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI Had i _ C (blocks_sub Bks σL) Bks wL u0 Hok
                      Rel HbA1 HBks' HnmA1 HnmA HnaA1 HnaA HarA1 HarA (decl_typed_nodup _ _ _ Hdt)
                      (EP mot_link Bks HnmA HAA0 _ RSL σL _ C HRSL HwL HEL Hev HCC)
                      (EB rneut_rel wL u0 HwL0 u0_env' LwL u0_len')
                      (EP br_out HBc Bks HB0s _ RSL σL _ C HRSL HwL HEL Hev HCC)) as [PE _].
        (** The term's value against the related argument [v']. *)
        pose proof (itrans _ _ _ _ _ _ _ (isym _ _ _ _ _ _ _ Hvm') _ _ _ _ Hff) as Hm0v.
        destruct (member_results_elim_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (PE _ _ _ _ _ _ _ Hm0v) HMj Hrv)
          as (r1 & r2 & Er1 & Er2 & Hr12).
        destruct (elim_grp_of_elem _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMj Hm0v (decl_typed_order _ _ _ Hdt) _ (elim_at_grp _ _ HMj))
          as [Hgr1 _].
        eapply (mk_leaf_ihs_vals_out _ _ _ _ _ _ _ _ _ _ _ _ (r1 :: nil) (r2 :: nil)).
        * cbn [shape_leaves]; rewrite (rv_leaves_not_rview _ _ _ HMj Hrv); cbn [List.map leaf_ih].
          econstructor; [| constructor ].
          unfold elim_at; eapply eval_exp_elim; [ exact EwL | exact Em0 | exact Hgr1 | exact Er1 ].
        * eapply eval_ih_self; [ exact Hl | exact HMj | exact Hrv | exact Er2 ].
        * eapply rec_result_self; [ exact HMj | exact Hrv | exact Ebs | exact Ebs' |].
          apply (proj1 (EP rel_resp _ _ HMj Hrv _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0v (isym _ _ _ _ _ _ _ Hff) Hff r1 r2)).
          exact Hr12.
    - (** At a domain: pointwise, at related values of the domain. *)
      assert (Hk' : kd < List.length (ptyp_doms t)) by lia.
      destruct (ptyp_skip_lt kd t Hk') as (Bk & HBk & Hs).
      rewrite Hs in Hsh, Hlk |- *.
      set (t' := ptyp_skip (S kd) t) in *.
      set (F := leaf_ih p D oq (List.map (fun U => U[↑]ʷ) (List.map (fun U => U[sb_shift_iter kd β0]) Us))
                  (blocks_wk (blocks_sub Bks (sb_shift_iter kd β0)) ↑) (sb_q (sb_qn kd σ0))
                  (a_app (apps_vars_iter kd x0)[↑]ʷ (a_var 0))).
      assert (Ers : ⟦ List.map (leaf_ih p D oq (List.map (fun U => U[sb_shift_iter kd β0]) Us) (blocks_sub Bks (sb_shift_iter kd β0))
                                  (sb_qn kd σ0) (apps_vars_iter kd x0))
                        (shape_leaves (rv_leaves D) (im_nn Mk + List.length (cargs_nonrec gs1) + kd) (pt_pi Bk t')) ⟧*
                      gc_deps ⍮ gc_stack ⍮ env_args C (zs ++ ys)
                      ↘ List.map (fun l => λᵈ (env_args C (zs ++ ys)) (F l))
                          (shape_leaves (rv_leaves D) (S (im_nn Mk + List.length (cargs_nonrec gs1) + kd)) t')).
      { cbn [shape_leaves]; rewrite List.map_map; cbn [leaf_ih]; apply eval_exps_fns. }
      eapply (mk_leaf_ihs_vals_out _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ers ltac:(eapply eval_ih_pi; exact Hl)).
      apply rec_result_pi; intros c0 c0' Hcc.
      destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsh c0 c0' Hcc) as (fc & fc' & Efc & Efc' & Hsh').
      (** The terms' side takes the left value of the domain, related to
          itself. *)
      assert (HPd : PER (dr k (ms ++ nv0 ++ ys0) Bk))
        by exact (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk HX Hck Heq0 Hnv HBk Hys).
      assert (Hcc0 : dr k (ms ++ nv0 ++ ys0) Bk c0 c0) by (etransitivity; [ exact Hcc | symmetry; exact Hcc ]).
      (** The domain's values, past the shape's domains so far. *)
      assert (Hys' : tele_prefix_rel (shape_doms_rel (dr k) ms nv0 (ptyp_doms t)) (S kd) (ys0 ++ c0 :: nil) (ys ++ c0 :: nil)).
      { apply tele_prefix_rel_snoc; [ exact Hys |].
        unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HBk); exact Hcc0. }
      (** The link, past the domain. *)
      assert (Hlk' : iota_arg_link k (ms ++ nv0 ++ ys0 ++ c0 :: nil) t' fc (apps_vars_iter (S kd) x0) (zs ++ ys ++ c0 :: nil)).
      { intros Δ RΔ zs2 HRΔ Hw HE.
        assert (Eys : (zs ++ ys ++ c0 :: nil) ++ zs2 = (zs ++ ys) ++ c0 :: zs2) by (rewrite <- !List.app_assoc; reflexivity).
        rewrite Eys in HE |- *.
        assert (Lw : List.length (zs ++ ys ++ c0 :: nil) + List.length zs2 = List.length (zs ++ ys) + List.length (c0 :: zs2))
          by (rewrite !List.length_app; cbn [List.length]; lia).
        rewrite Lw in Hw.
        destruct (Hlk _ _ _ HRΔ Hw HE) as (pre0 & m0 & Em0 & Hvm).
        destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvm c0 c0 Hcc0) as (r & r' & Er & Er' & Hr).
        assert (r = fc) as -> by (eapply functional_eval_app; eassumption).
        exists (pre0 ++ c0 :: nil), r'; split; [| rewrite <- !List.app_assoc in Hr; exact Hr ].
        cbn [apps_vars_iter exp_wk].
        econstructor; [| | exact Er' ].
        - rewrite exp_wk_wk, (exp_wk_wk_eq _ _ (wk_shiftn (List.length (c0 :: zs2)))) by (intros z; cbn; lia); exact Em0.
        - rewrite env_args_app.
          pose proof (eval_var_args (env_args C (zs ++ ys)) (c0 :: zs2) (List.length zs2) ltac:(cbn; lia)) as Hv0.
          replace (List.length (c0 :: zs2) - 1 - List.length zs2) with 0 in Hv0 by (cbn; lia).
          replace (wk_shiftn (List.length zs2) 0) with (List.length zs2) by (cbn; lia); exact Hv0. }
      assert (HUs1 : List.map (fun U => U[↑]ʷ) (List.map (fun U => U[sb_shift_iter kd β0]) Us)
                     = List.map (fun U => U[sb_shift_iter (S kd) β0]) Us)
        by (rewrite List.map_map; apply List.map_ext; intros; rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity).
      assert (HBs1 : blocks_wk (blocks_sub Bks (sb_shift_iter kd β0)) ↑ = blocks_sub Bks (sb_shift_iter (S kd) β0))
        by (rewrite <- blocks_sub_of_wk, blocks_sub_sub; reflexivity).
      rewrite <- !List.app_assoc in Hsh'; cbn [List.app] in Hsh'.
      destruct (IHm (S kd) ltac:(lia) (ys0 ++ c0 :: nil) (ys ++ c0 :: nil) fc fc' (pre' ++ c0' :: nil) ltac:(lia)
                  ltac:(rewrite List.length_app, Lys; cbn; lia) Hys' ltac:(rewrite <- ?List.app_assoc; exact Hsh')
                  ltac:(rewrite <- ?List.app_assoc; exact Hlk'))
        as [rcs' rcs Erc' Erc Hrc].
      fold t' in Erc, Erc', Hrc.
      refine (rec_result_app_mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc fc' rcs' rcs Efc Efc' _ _ _);
        [ | | rewrite <- ?List.app_assoc; exact Hrc ].
      + apply (eval_exps_fns_app (shape_leaves (rv_leaves D) (S (im_nn Mk + List.length (cargs_nonrec gs1) + kd)) t')
                 (Bk[sb_qn kd σ0]) F (env_args C (zs ++ ys))).
        * apply eval_exps_fns.
        * unfold F; rewrite HUs1, HBs1.
          replace (S (im_nn Mk + List.length (cargs_nonrec gs1) + kd)) with (im_nn Mk + List.length (cargs_nonrec gs1) + S kd) by lia.
          rewrite <- env_args_snoc, <- List.app_assoc; exact Erc'.
      + apply (ihfn_app _ _ _ _ _ _ _ _ _ _ Efc' Erc).
        exact (proj1 (proj2 eval_ih_length_all) _ _ _ _ _ _ _ Erc D Hl Hco).
  Qed.
End LeafVals.

(** ** The Rule

    An eliminator of the member [m] at a constructor [c] of it, at the
    parameters [Ps] and the arguments [As]. *)
Section Iota.
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups VP) (HPD : VP p D).
  Let Hvg := valid_groups_valid VP HP p D HPD.
  Let Hcv := containers_valid_of_groups VP HP p D HPD.
  Let HD := valid_group_valid _ _ Hvg.
  Let Hc := valid_group_closed _ _ Hvg.
  Let Hl := valid_group_lookup _ _ Hvg.
  Let Hdt := valid_group_typed _ _ Hvg.
  Let Ua : tele_ass (ind_uparams D) := uparams_ass D Hc.
  Let Usem : ⊨ ind_uparams D := valid_ind_decl_uparams _ HD.

  Variable (Γ : ctx) (oq : option qname) (m : nat) (Mm : imember) (bm : eblock) (Bks : list eblock)
    (c : String.string) (gs : list carg) (Ps As : list exp) (i : nat).
  Let Us := List.firstn (ind_nu D) Ps.
  Let Ns := List.skipn (ind_nu D) Ps.
  Let σP := sb_of_list Id Ps.
  Hypotheses (HΓ : ⊨ Γ) (Hgr : elim_grp D oq p m) (HMm : ind_member D m = Some Mm) (Hbm : List.nth_error Bks m = Some bm)
    (Hcon : ind_con Mm c = Some gs) (HPl : List.length Ps = im_np D Mm)
    (HPs : forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Γ ⊨ P : T)
    (HAl : List.length As = List.length gs)
    (HAs : forall k N T, List.nth_error As k = Some N -> List.nth_error (tele_insts (cargs_ctx p D Mm gs) σP As) k = Some T -> Γ ⊨ N : T)
    (HBks : List.length Bks = ind_nblk D)
    (HnmA : blocks_nm_ok D Bks)
    (HMall : forall j Mj, ind_member D j = Some Mj -> ⊨ elim_mctx p D j Mj Us ++ Γ)
    (HAv : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b : Typeω@i)
    (HnaA : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> brs_names (im_cons Mj) (eb_brs b))
    (HBc : forall j Mj c gs, ind_member D j = Some Mj -> ind_con Mj c = Some gs ->
             ⊨ elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ)
    (HarA : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> ind_con Mj c = Some gs ->
              In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat)
    (HBv : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> ind_con Mj c = Some gs ->
             In (c, n, B) (eb_brs b) ->
             elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ ⊨ B : elim_bty p D j Mj c gs (eb_motive b) Us).
  Let Hoq := elim_grp_oq _ _ _ _ Hgr.
  Let HΨ := vg_cargs_sem p D Hvg Hcv m Mm c gs HMm Hcon.
  (** The member has a block: it is not a record view. *)
  Let HrvM := Elim.block_not_rview D Bks m Mm bm Hdt HBks HMm Hbm.
  (** The blocks of the members with one. *)
  Let HBks' := block_of_nblk D Bks Hdt HBks.

  Lemma i_HUl : List.length Us = ind_nu D.
  Proof. unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia. Qed.

  Lemma i_HNl : List.length Ns = im_nn Mm.
  Proof. unfold Ns; rewrite List.length_skipn; unfold im_np in HPl; lia. Qed.

  Lemma i_HUs : forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Γ ⊨ U : T.
  Proof. exact (proj1 (params_valid_split D m Mm Γ Ps Hc HMm HPl HPs)). Qed.

  Lemma i_HNs : forall k N T, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) k = Some T ->
      Γ ⊨ N : T.
  Proof. exact (proj2 (params_valid_split D m Mm Γ Ps Hc HMm HPl HPs)). Qed.

  Lemma i_Ps : Ps = Us ++ Ns.
  Proof. symmetry; apply List.firstn_skipn. Qed.

  Lemma i_Us_id : List.map (fun U => U[Id]) Us = Us.
  Proof. rewrite (List.map_ext _ (fun U => U) exp_sub_id); apply List.map_id. Qed.

  (** *** The Parameters and the Arguments Before a Position *)
  Lemma gsub_P : gsub Γ σP (im_params D Mm ++ Γ).
  Proof.
    apply gsub_closed_inst; [ exact (member_params_ass D Hc _ _ HMm) | exact (valid_ind_decl_params _ HD _ _ HMm) | exact HΓ
                            | rewrite length_im_params; exact HPl | exact HPs ].
  Qed.

  Lemma gsub_args_pre : forall k, k <= List.length gs ->
      gsub Γ (sb_of_list σP (List.firstn k As)) (cargs_ctx p D Mm (List.firstn k gs) ++ im_params D Mm ++ Γ).
  Proof.
    intros k Hk.
    assert (Heq : gs = List.firstn k gs ++ List.skipn k gs) by (symmetry; apply List.firstn_skipn).
    pose proof (cargs_prefix_sem D p Mm gs HΨ _ _ Heq) as Hp.
    assert (Hpa : tele_ass (cargs_ctx p D Mm (List.firstn k gs) ++ im_params D Mm))
      by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc _ _ HMm) ]).
    destruct (closed_app_sem _ _ Hpa Hp HΓ) as [HpΓ _]; rewrite <- List.app_assoc in HpΓ.
    apply gsub_of_list; [ exact gsub_P | apply cargs_ctx_aux_ass | exact HpΓ
                        | rewrite List.length_firstn, length_cargs_ctx, List.length_firstn; lia |].
    intros j N T HN HT.
    assert (Hj : j < List.length (List.firstn k As)) by (apply List.nth_error_Some; congruence).
    rewrite List.length_firstn in Hj.
    apply (HAs j); [ rewrite List.nth_error_firstn in HN; destruct (Nat.ltb_spec j k); [ exact HN | lia ] |].
    rewrite Heq at 1; unfold cargs_ctx; rewrite cargs_ctx_aux_app, List.app_nil_r.
    rewrite <- (List.firstn_skipn k As), tele_insts_app;
      [| apply cargs_ctx_aux_ass | rewrite List.length_firstn, length_cargs_ctx_aux, List.length_firstn; lia ].
    rewrite List.nth_error_app1; [ exact HT |].
    rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx_aux, !List.length_firstn; lia.
  Qed.

  (** The substitution of a shape's components after [gs1]. *)
  Lemma gsub_sigt : forall gs1 gs2, gs = gs1 ++ gs2 ->
      gsub Γ (cargs_sub σP gs1 As) (cargs_strat gs1 ++ im_params D Mm ++ Γ).
  Proof.
    intros * Heq.
    assert (Lg1 : List.length gs1 <= List.length gs) by (rewrite Heq, List.length_app; lia).
    pose proof (gsub_args_pre _ Lg1) as Hg.
    assert (Hfg : List.firstn (List.length gs1) gs = gs1) by (rewrite Heq; apply firstn_app_exact; reflexivity).
    rewrite Hfg in Hg.
    destruct (gsub_props Hg) as [Hgv Hgl].
    pose proof (cargs_prefix_sem D p Mm gs HΨ _ _ Heq) as Hp.
    assert (Hpa : tele_ass (cargs_ctx p D Mm gs1 ++ im_params D Mm))
      by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc _ _ HMm) ]).
    destruct (closed_app_sem _ _ Hpa Hp HΓ) as [HpΓ _]; rewrite <- List.app_assoc in HpΓ.
    assert (HSa : tele_ass (cargs_strat gs1 ++ im_params D Mm))
      by (apply List.Forall_app; split; [ rewrite cargs_strat_nonrec; apply List.Forall_rev, tele_ass_map_ass
                                       | exact (member_params_ass D Hc _ _ HMm) ]).
    assert (HSs : ⊨ cargs_strat gs1 ++ im_params D Mm)
      by (rewrite (nonrec_args_prefix_cargs_strat gs1 gs2), <- Heq; apply (valid_ind_decl_strat _ HD _ _ _ _ _ HMm Hcon);
          rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    destruct (closed_app_sem _ _ HSa HSs HΓ) as [HSΓ _]; rewrite <- List.app_assoc in HSΓ.
    pose proof (gsub_wk _ _ _ (cargs_wk_ext VP p D HP HPD Γ HΓ Us i_HUl m Mm c gs HMm Hcon gs1 gs2 Heq) HpΓ HSΓ) as G0.
    eapply gsub_eq; [ exact (gsub_comp _ _ _ _ _ G0 HΓ Hgv Hgl) |].
    rewrite <- (cargs_sub_firstn gs1 σP As).
    apply cargs_sub_pat; rewrite List.length_firstn; lia.
  Qed.

  Lemma eval_sigt : forall gs1 gs2 ρ ps avs, gs = gs1 ++ gs2 ->
      ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ps -> ⟦ As ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ avs ->
      ⟦ cargs_sub σP gs1 As ⟧s ρ ↘ env_args ρ (ps ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) avs)).
  Proof.
    intros * Heq Hp Ha.
    assert (Lg1 : List.length gs1 <= List.length As) by (rewrite HAl, Heq, List.length_app; lia).
    rewrite <- (cargs_sub_firstn gs1 σP As).
    eapply eval_sub_sb_eq; [ apply cargs_sub_pat; rewrite List.length_firstn; lia |].
    pose proof (eval_exps_firstn' As ρ avs (List.length gs1) Ha) as Ha1.
    assert (La1 : List.length (List.firstn (List.length gs1) avs) = List.length gs1)
      by (rewrite List.length_firstn, (eval_exps_length _ _ _ Ha); lia).
    pose proof (eval_sb_of_list _ _ _ _ _ (eval_sb_of_list _ _ _ _ _ (eval_sub_id ρ) Hp) Ha1) as Hτ.
    replace (env_args ρ (ps ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) avs)))
      with (⟪wk_pat (cargs_pat gs1)⟫ (env_args (env_args ρ ps) (List.firstn (List.length gs1) avs)))
      by (rewrite eval_wk_pat_args by exact La1; rewrite <- env_args_app; reflexivity).
    intros x; cbn [sb_compose sb_of_wk sentry_sub]; rewrite (eval_wk_entry _ _ (wk_mono_pat _)).
    exact (Hτ _).
  Qed.

  (** *** The Frame of a Recursive Argument

      The recursive argument [Mt] of shape [t] after the arguments [gs1]:
      the frame of its position, over no context, at the components [σt]
      and the base [Id]. *)
  Section RecArg.
    #[local] Set Default Proof Using "All".
    Variable (gs1 : list carg) (t : ptyp) (gs2 : list carg).
    Hypothesis (Heq : gs = gs1 ++ ca_rec t :: gs2).
    Let σt := cargs_sub σP gs1 As.
    Let Mt := List.nth (List.length gs1) As (a_var 0).

    Lemma r_uc : shape_uc D Us (cargs_strat gs1 ++ im_params D Mm) σt Id.
    Proof.
      intros y Hy.
      assert (Lg1 : List.length gs1 <= List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      unfold σt; rewrite <- (cargs_sub_firstn gs1 σP As).
      rewrite <- (cargs_sub_pat gs1 σP (List.firstn (List.length gs1) As)) by (rewrite List.length_firstn; lia).
      cbn [sb_compose sb_of_wk sentry_sub].
      replace (y + (List.length (cargs_strat gs1 ++ im_params D Mm) - ind_nu D)) with (pat_nargs (cargs_pat gs1) + (im_nn Mm + y))
        by (rewrite List.length_app, length_im_params, pat_nargs_cargs_pat; unfold im_np; lia).
      rewrite wk_pat_ge, length_cargs_pat.
      replace (List.length gs1 + (im_nn Mm + y)) with (List.length (List.firstn (List.length gs1) As) + (im_nn Mm + y))
        by (rewrite List.length_firstn; lia).
      rewrite sb_of_list_ge; unfold σP; rewrite i_Ps, sb_of_list_app.
      replace (im_nn Mm + y) with (List.length Ns + y) by (rewrite i_HNl; lia).
      rewrite sb_of_list_ge; cbn [sb_compose]; rewrite sentry_sub_id; reflexivity.
    Qed.

    Lemma r_Mt : Γ ⊨ Mt : ptyp_ty_at p D Us σt t.
    Proof.
      assert (Hk : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some' As (List.length gs1) Hk) as [M HM0].
      unfold Mt; rewrite (List.nth_error_nth _ _ _ HM0).
      set (As1 := List.firstn (List.length gs1) As).
      assert (LAs1 : List.length As1 = List.length gs1) by (unfold As1; rewrite List.length_firstn; lia).
      assert (HAeq : As = As1 ++ M :: List.skipn (S (List.length gs1)) As)
        by (unfold As1; rewrite <- (skipn_nth_cons' _ _ _ HM0), List.firstn_skipn; reflexivity).
      apply (HAs (List.length gs1)); [ exact HM0 |].
      rewrite Heq at 1; unfold cargs_ctx; rewrite cargs_ctx_aux_app, List.app_nil_r; cbn [cargs_ctx_aux].
      rewrite HAeq.
      rewrite (tele_insts_app (cargs_ctx_aux p D (im_nn Mm) (true :: cargs_pat gs1) gs2
                                 ++ ce_ass (ptyp_ty p D (im_nn Mm) (cargs_pat gs1) t) :: nil)
                 (cargs_ctx_aux p D (im_nn Mm) nil gs1)); [| apply cargs_ctx_aux_ass | rewrite length_cargs_ctx_aux; exact LAs1 ].
      rewrite List.nth_error_app2 by (rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx_aux; lia).
      rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx_aux, LAs1.
      replace (List.length gs1 - Nat.min (List.length gs1) (List.length gs1)) with 0 by lia.
      change (M :: List.skipn (S (List.length gs1)) As) with ((M :: nil) ++ List.skipn (S (List.length gs1)) As).
      rewrite tele_insts_app; [| repeat constructor; eexists; reflexivity | reflexivity ].
      cbn; unfold tele_insts at 1; cbn [List.rev List.app tele_insts_aux]; f_equal.
      rewrite ptyp_ty_eq_at, ptyp_ty_at_sub by (try exact Hc; apply length_ind_uvars).
      rewrite (ptyp_ty_at_sb_eq _ _ _ _ _ σt); [ f_equal |].
      - unfold ind_uvars; rewrite length_cargs_pat.
        unfold σP; rewrite <- sb_of_list_app, i_Ps, <- List.app_assoc.
        replace (List.length gs1 + im_nn Mm) with (List.length (Ns ++ As1)) by (rewrite List.length_app, i_HNl; lia).
        rewrite <- i_HUl; apply vars_from_sb_of_list_app.
      - unfold σt; rewrite <- (cargs_sub_firstn gs1 σP As); fold As1.
        apply cargs_sub_pat; exact LAs1.
    Qed.

    (** The frame of the argument. *)
    Lemma iota_frame : sem_frame p D Γ Us Mm gs1 t nil σt Id Mt.
    Proof.
      constructor; cbn [List.app List.length].
      - exact HΓ.
      - exact (gsub_sigt gs1 _ Heq).
      - intros x; unfold sb_id, sb_of_wk; rewrite (wk_shiftn_zero x); reflexivity.
      - exact r_uc.
      - rewrite i_Us_id; exact r_Mt.
      - intros y; rewrite i_Us_id.
        assert (Lg1 : List.length gs1 <= List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
        replace (y + List.length (cargs_strat gs1 ++ im_nparams Mm)) with ((y + im_nn Mm) + List.length (cargs_nonrec gs1))
          by (rewrite List.length_app, cargs_strat_nonrec, List.length_rev, List.length_map, length_im_nparams; lia).
        unfold σt; rewrite cargs_sub_ge by exact Lg1.
        unfold σP; rewrite i_Ps, sb_of_list_app.
        replace (y + im_nn Mm) with (List.length Ns + y) by (rewrite i_HNl; lia).
        apply sb_of_list_ge.
    Qed.
  End RecArg.

  (** *** The Instance of the Branch's Context *)
  Lemma gsub_args : gsub Γ (sb_of_list Id (Ns ++ As)) (cinst Γ p D Mm Us gs).
  Proof.
    pose proof (gsub_ns VP p D HP HPD Γ HΓ Us m Mm HMm (HMall _ _ HMm) Ns i_HNl i_HNs) as HgN.
    pose proof (HBc _ _ _ _ HMm Hcon) as HB; unfold elim_bctx in HB.
    assert (HC : ⊨ cinst Γ p D Mm Us gs)
      by (unfold cinst; rewrite <- !List.app_assoc in HB; exact (rel_ctx_wf_app_r _ _ HB)).
    rewrite sb_of_list_app; unfold cinst in HC |- *.
    apply gsub_of_list; [ exact HgN | apply tele_ass_sub, cargs_ctx_aux_ass | exact HC
                        | rewrite length_tele_sub, length_cargs_ctx; exact HAl |].
    intros k N T HN HT; rewrite tele_insts_tele_sub in HT.
    rewrite (tele_insts_sb_eq _ _ σP) in HT; [ exact (HAs _ _ _ HN HT) |].
    rewrite <- i_HNl; etransitivity; [ apply sb_qn_of_list |].
    etransitivity; [ apply sb_of_list_cong; intros x; cbn; apply sentry_sub_id |].
    unfold σP; rewrite i_Ps, <- sb_of_list_app; reflexivity.
  Qed.

  Lemma ihs_pre : forall gs1 gs2, gs = gs1 ++ gs2 ->
      ⊨ ihs_ctx_aux (rv_leaves D) (im_nn Mm) (blocks_motives Bks) Us (List.length gs) nil 0 gs1 ++ cinst Γ p D Mm Us gs.
  Proof.
    intros * Heq; pose proof (HBc _ _ _ _ HMm Hcon) as H; unfold elim_bctx in H.
    replace (ihs_ctx_aux (rv_leaves D) (im_nn Mm) (blocks_motives Bks) Us (List.length gs) nil 0 gs)
      with (ihs_ctx_aux (rv_leaves D) (im_nn Mm) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1 ++ nil) (0 + cargs_nrec D gs1) gs2
              ++ ihs_ctx_aux (rv_leaves D) (im_nn Mm) (blocks_motives Bks) Us (List.length gs) nil 0 gs1) in H
      by (rewrite <- ihs_ctx_aux_app, <- Heq; reflexivity).
    unfold cinst; rewrite <- !List.app_assoc in H; exact (rel_ctx_wf_app_r _ _ H).
  Qed.

  (** The recursive results of a recursive argument [t] after [gs1], one
      per leaf path of its shape, as a context: after those of [gs1]. *)
  Lemma ihs_rec_split : forall gs1 t,
      ihs_ctx_aux (rv_leaves D) (im_nn Mm) (blocks_motives Bks) Us (List.length gs) nil 0 (gs1 ++ ca_rec t :: nil)
      = leaves_ctx (im_nn Mm) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) (cargs_nrec D gs1)
          (shape_leaves (rv_leaves D) (im_nn Mm + List.length (cargs_nonrec gs1)) t)
        ++ ihs_ctx_aux (rv_leaves D) (im_nn Mm) (blocks_motives Bks) Us (List.length gs) nil 0 gs1.
  Proof.
    intros gs1 t; rewrite ihs_ctx_aux_app, List.app_nil_r; cbn [ihs_ctx_aux List.app Nat.add].
    replace (pat_nargs (cargs_pat gs1) + im_nn Mm) with (im_nn Mm + List.length (cargs_nonrec gs1))
      by (rewrite pat_nargs_cargs_pat, cargs_strat_nonrec, List.length_rev, List.length_map; lia).
    reflexivity.
  Qed.

  (** The recursive results along the leaf paths [ls1] of a recursive
      argument [t] after [gs1], over those before: an instance of their
      context. *)
  Lemma gsub_iota_leaves : forall gs1 t rest, gs = gs1 ++ ca_rec t :: rest -> forall L0, List.length L0 = cargs_nrec D gs1 ->
      gsub Γ (sb_of_list Id (Ns ++ As ++ L0))
        (ihs_ctx_aux (rv_leaves D) (im_nn Mm) (blocks_motives Bks) Us (List.length gs) nil 0 gs1 ++ cinst Γ p D Mm Us gs) ->
      forall ls1 ls2, shape_leaves (rv_leaves D) (im_nn Mm + List.length (cargs_nonrec gs1)) t = ls1 ++ ls2 ->
      gsub Γ (sb_of_list Id (Ns ++ As ++ L0 ++
                List.map (leaf_ih p D oq Us Bks (cargs_sub σP gs1 As) (List.nth (List.length gs1) As (a_var 0))) ls1))
        (leaves_ctx (im_nn Mm) (blocks_motives Bks) Us (List.length gs) (cargs_pat gs1) (cargs_nrec D gs1) ls1
         ++ ihs_ctx_aux (rv_leaves D) (im_nn Mm) (blocks_motives Bks) Us (List.length gs) nil 0 gs1 ++ cinst Γ p D Mm Us gs).
  Proof.
    intros gs1 t rest Heq L0 HL Hδ ls1.
    assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
    destruct (nth_error_lt_some As _ Hlt) as [a Ha].
    rewrite (List.nth_error_nth _ _ _ Ha).
    destruct (length_rec_ps D HD m Mm HMm c gs gs1 t rest Hcon Heq) as (Mj & HMj & _).
    induction ls1 as [| l ls1 IH1] using List.rev_ind; intros ls2 Els.
    - cbn [List.map leaves_ctx List.app]; rewrite List.app_nil_r; exact Hδ.
    - specialize (IH1 (l :: ls2) ltac:(rewrite Els, <- List.app_assoc; reflexivity)).
      (** The entry of the path is a type. *)
      pose proof (ihs_pre (gs1 ++ ca_rec t :: nil) rest ltac:(rewrite <- List.app_assoc; exact Heq)) as HCT.
      rewrite ihs_rec_split, Els, leaves_ctx_app, <- !List.app_assoc in HCT.
      apply rel_ctx_wf_app_r in HCT.
      rewrite leaves_ctx_app in HCT; cbn [leaves_ctx List.app] in HCT.
      destruct (rel_ctx_wf_ass_inv HCT) as [jT HTj].
      (** The instance so far, extended by the path's result. *)
      rewrite List.map_app, leaves_ctx_app; cbn [leaves_ctx List.app List.map].
      set (L1 := L0 ++ List.map (leaf_ih p D oq Us Bks (cargs_sub σP gs1 As) a) ls1) in *.
      assert (LL1 : List.length L1 = cargs_nrec D gs1 + List.length ls1) by (unfold L1; rewrite List.length_app, List.length_map, HL; reflexivity).
      replace (Ns ++ As ++ L0 ++ List.map (leaf_ih p D oq Us Bks (cargs_sub σP gs1 As) a) ls1
                 ++ leaf_ih p D oq Us Bks (cargs_sub σP gs1 As) a l :: nil)
        with ((Ns ++ As ++ L1) ++ leaf_ih p D oq Us Bks (cargs_sub σP gs1 As) a l :: nil)
        by (unfold L1; rewrite <- !List.app_assoc; reflexivity).
      replace (Ns ++ As ++ L0 ++ List.map (leaf_ih p D oq Us Bks (cargs_sub σP gs1 As) a) ls1) with (Ns ++ As ++ L1) in IH1
        by (unfold L1; reflexivity).
      rewrite (sb_of_list_app (Ns ++ As ++ L1) (_ :: nil) Id).
      change (sb_of_list (sb_of_list Id (Ns ++ As ++ L1)) (?N :: nil)) with (sb_of_list Id (Ns ++ As ++ L1) ,, N).
      eapply gsub_ass; [ exact IH1 | exact HTj |].
      set (δ := sb_of_list Id (Ns ++ As ++ L1)).
      rewrite leaf_ihty_sub.
      assert (Hθδ : sb_eq (ihs_sub (im_nn Mm) Us (List.length gs) (cargs_pat gs1) (cargs_nrec D gs1 + List.length ls1) ⨟ δ)
                      (cargs_sub σP gs1 As)).
      { unfold δ, σP; rewrite <- LL1.
        exact (ihs_sub_iota D Mm Ps As L1 gs1 gs HPl HAl ltac:(rewrite Heq, List.length_app; lia)). }
      assert (Hbδ : sb_eq (sb_of_wk (wk_shiftn (cargs_nrec D gs1 + List.length ls1 + List.length gs + im_nn Mm)) ⨟ δ) Id).
      { intros z; unfold δ; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
        replace (z + (cargs_nrec D gs1 + List.length ls1 + List.length gs + im_nn Mm)) with (List.length (Ns ++ As ++ L1) + z)
          by (rewrite !List.length_app, i_HNl, HAl, LL1; lia).
        rewrite sb_of_list_ge; reflexivity. }
      assert (Hidx : (a_var (cargs_nrec D gs1 + List.length ls1 + List.length gs - 1 - List.length (cargs_pat gs1)))[δ] = a).
      { change (exp_sub (a_var ?y) ?s) with (sentry_exp (s y)); unfold δ.
        rewrite (sb_of_list_nth _ _ _ a) by (rewrite !List.length_app, i_HNl, HAl, LL1, Heq, List.length_app, length_cargs_pat; cbn; lia).
        rewrite !List.length_app, i_HNl, HAl, LL1, length_cargs_pat.
        replace (im_nn Mm + (List.length gs + (cargs_nrec D gs1 + List.length ls1)) - 1
                   - (cargs_nrec D gs1 + List.length ls1 + List.length gs - 1 - List.length gs1))
          with (im_nn Mm + List.length gs1) by (rewrite Heq, List.length_app; cbn; lia).
        cbn [sentry_exp]; rewrite List.app_nth2 by (rewrite i_HNl; lia); rewrite i_HNl.
        replace (im_nn Mm + List.length gs1 - im_nn Mm) with (List.length gs1) by lia.
        rewrite List.app_nth1 by exact Hlt; apply List.nth_error_nth; exact Ha. }
      rewrite Hidx, (leaf_ihty_sb_eq l _ _ Id _ (cargs_sub σP gs1 As) a Hbδ Hθδ).
      (** The path's result, at the argument's frame. *)
      assert (Hinl : In l (shape_leaves (rv_leaves D) (im_nn Mm + List.length (cargs_nonrec gs1) + 0) (ptyp_skip 0 t)))
        by (rewrite Nat.add_0_r; cbn [ptyp_skip]; rewrite Els; apply List.in_or_app; left; apply List.in_or_app; right; left; reflexivity).
      pose proof (leaf_ih_valid VP p D HP HPD Γ oq Us Bks i HΓ Hoq i_HUl i_HUs HBks HnmA HMall HAv HnaA HBc HarA HBv
                    (S (ptyp_mem t)) m Mm c gs gs1 t rest HMm Hcon Heq Mj HMj (fun _ => Nat.lt_succ_diag_r _)
                    _ _ _ _ (iota_frame gs1 t rest Heq) 0 l (Nat.le_0_l _) Hinl) as H.
      cbn [List.firstn doms_ctx List.map List.rev tele_sub List.app sb_shift_iter sb_qn apps_vars_iter] in H.
      rewrite i_Us_id, blocks_sub_id, (List.nth_error_nth _ _ _ Ha) in H; exact H.
  Qed.

  Lemma gsub_iota_ihs : forall rest gs1 L0, gs = gs1 ++ rest -> List.length L0 = cargs_nrec D gs1 ->
      gsub Γ (sb_of_list Id (Ns ++ As ++ L0))
        (ihs_ctx_aux (rv_leaves D) (im_nn Mm) (blocks_motives Bks) Us (List.length gs) nil 0 gs1 ++ cinst Γ p D Mm Us gs) ->
      gsub Γ (sb_of_list Id (Ns ++ As ++ L0 ++ elim_ihs p D oq Us Bks (cargs_sub σP gs1 As)
                                          (im_nn Mm + List.length (cargs_nonrec gs1)) rest (List.skipn (List.length gs1) As)))
        (ihs_ctx_aux (rv_leaves D) (im_nn Mm) (blocks_motives Bks) Us (List.length gs) nil 0 (gs1 ++ rest) ++ cinst Γ p D Mm Us gs).
  Proof.
    induction rest as [| [B0 | t] rest IH]; intros gs1 L0 Heq HL Hδ.
    - cbn [elim_ihs]; rewrite !List.app_nil_r; exact Hδ.
    - assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some As _ Hlt) as [a Ha].
      rewrite (skipn_nth_cons _ _ _ Ha); cbn [elim_ihs].
      assert (Hcs : cargs_sub σP (gs1 ++ ca_arg B0 :: nil) As = (cargs_sub σP gs1 As ,, a)).
      { rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r, (firstn_S_nth _ _ _ Ha).
        apply cargs_sub_snoc_arg; rewrite List.length_firstn; lia. }
      replace (S (List.length gs1)) with (List.length (gs1 ++ ca_arg B0 :: nil)) by (rewrite List.length_app; cbn; lia).
      replace (S (im_nn Mm + List.length (cargs_nonrec gs1))) with (im_nn Mm + List.length (cargs_nonrec (gs1 ++ ca_arg B0 :: nil)))
        by (rewrite cargs_nonrec_app, List.length_app; cbn; lia).
      rewrite <- Hcs.
      replace (gs1 ++ ca_arg B0 :: rest) with ((gs1 ++ ca_arg B0 :: nil) ++ rest) by (rewrite <- List.app_assoc; reflexivity).
      apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity | rewrite cargs_nrec_app_iota; cbn; lia |].
      rewrite ihs_ctx_aux_app, List.app_nil_r; cbn [ihs_ctx_aux List.app]; exact Hδ.
    - assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some As _ Hlt) as [a Ha].
      rewrite (skipn_nth_cons _ _ _ Ha); cbn [elim_ihs].
      assert (Hcs : cargs_sub σP (gs1 ++ ca_rec t :: nil) As = cargs_sub σP gs1 As).
      { rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r, (firstn_S_nth _ _ _ Ha).
        apply cargs_sub_snoc_rec; rewrite List.length_firstn; lia. }
      pose proof (gsub_iota_leaves gs1 t rest Heq L0 HL Hδ _ nil (eq_sym (List.app_nil_r _))) as Hall.
      rewrite (List.nth_error_nth _ _ _ Ha) in Hall.
      set (ls := shape_leaves (rv_leaves D) (im_nn Mm + List.length (cargs_nonrec gs1)) t) in *.
      set (F := leaf_ih p D oq Us Bks (cargs_sub σP gs1 As) a) in *.
      replace (Ns ++ As ++ L0 ++ List.map F ls ++ elim_ihs p D oq Us Bks (cargs_sub σP gs1 As) (im_nn Mm + List.length (cargs_nonrec gs1))
                 rest (List.skipn (S (List.length gs1)) As))
        with (Ns ++ As ++ (L0 ++ List.map F ls) ++ elim_ihs p D oq Us Bks (cargs_sub σP (gs1 ++ ca_rec t :: nil) As)
                (im_nn Mm + List.length (cargs_nonrec (gs1 ++ ca_rec t :: nil))) rest
                (List.skipn (List.length (gs1 ++ ca_rec t :: nil)) As))
        by (rewrite Hcs, cargs_nonrec_app, !List.length_app; cbn [cargs_nonrec List.length];
            rewrite !Nat.add_0_r, Nat.add_1_r, <- !List.app_assoc; reflexivity).
      replace (gs1 ++ ca_rec t :: rest) with ((gs1 ++ ca_rec t :: nil) ++ rest) by (rewrite <- List.app_assoc; reflexivity).
      apply IH; [ rewrite Heq, <- List.app_assoc; reflexivity
                | rewrite List.length_app, List.length_map, HL, cargs_nrec_app_iota; cbn [cargs_nrec];
                  unfold ls; rewrite (length_shape_leaves _ _ _ 0); lia |].
      rewrite ihs_rec_split, <- List.app_assoc; exact Hall.
  Qed.

  Lemma gsub_iota : gsub Γ (sb_of_list Id (Ns ++ As ++ elim_ihs p D oq Us Bks σP (im_nn Mm) gs As))
      (elim_bctx p D Mm gs (blocks_motives Bks) Us ++ Γ).
  Proof.
    pose proof gsub_args as Hδ.
    rewrite <- (List.app_nil_r As) in Hδ at 1.
    pose proof (gsub_iota_ihs gs nil nil eq_refl eq_refl ltac:(cbn [ihs_ctx_aux List.app]; exact Hδ)) as H.
    cbn [List.app List.skipn List.length cargs_sub cargs_nonrec] in H; rewrite Nat.add_0_r in H.
    unfold elim_bctx; unfold cinst in H; rewrite <- !List.app_assoc; exact H.
  Qed.

  (** The constructor applied, the scrutinee. *)
  Lemma iota_Mc_valid : Γ ⊨ apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c) (im_pre Mm Us ++ Ns ++ As)
      : ind_mty p D m Us Ns.
  Proof.
    apply (con_apps_ref_valid VP p D HP HPD Γ m Mm c gs Us Ns As HΓ HMm HrvM Hcon i_HUl i_HUs i_HNl i_HNs HAl).
    intros * HN HT; apply (HAs _ _ _ HN); unfold σP; rewrite i_Ps; exact HT.
  Qed.

  (** The member the constructor's value is of, as the group reads it. *)
  Lemma ref_target : exists Dq Mk, ind_lookup gc_deps gc_stack (fst (im_ref p m Mm)) = Some Dq /\
      ind_member Dq (snd (im_ref p m Mm)) = Some Mk /\ im_unu D Mm = ind_nu Dq /\ im_nn Mk = im_nn Mm.
  Proof.
    unfold im_ref, im_unu; destruct (im_head Mm) as [pm | qc kc Is vm | qr Is fl] eqn:Hh; cbn [fst snd].
    - exists D, Mm; repeat split; [ exact Hl | exact HMm ].
    - destruct (view_target_decl VP p D HP HPD m Mm HMm qc kc Is vm Hh) as (Dq & Mk' & pm & Hq & HMk' & _ & HIl).
      destruct (grp_tele_ass_views _ (valid_group_ass _ _ Hvg) m Mm qc kc Is vm HMm Hh) as (Dq0 & Mc & Hq0 & HMc & Hnn & _).
      rewrite Hq in Hq0; injection Hq0 as <-; rewrite HMk' in HMc; injection HMc as <-.
      exists Dq, Mk'; repeat split; [ exact Hq | exact HMk' | exact HIl | exact Hnn ].
    - exfalso; pose proof HrvM as H; unfold im_is_rview in H; rewrite Hh in H; discriminate.
  Qed.

  (** *** The Values at an Environment

      At an environment [C] of [Γ]: the recursive results of the
      eliminator's own evaluation are related, by [rec_results_rel], to
      the values of the recursive results [elim_ihs] in the branch's
      instance. *)
  Section IotaSem.
    #[local] Set Default Proof Using "All".
    Variable (RΓ RU : relation env).
    Hypotheses (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).
    Variable (C : env) (u0 ns avs : list domain).
    Hypotheses (HCC : RΓ C C) (HUC : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ C ↘ u0)
      (HNC : ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ C ↘ ns) (HAC : ⟦ As ⟧* gc_deps ⍮ gc_stack ⍮ C ↘ avs).
    Let nr := canon_nparams_rel D u0.
    Let ar := canon_args_rel D u0.
    Let dr := canon_doms_rel u0.
    Let G := grp_rel p D u0 nr ar dr.
    Let Rel := fun j ns m ns' m' =>
      per_head (List.nth j (blocks_motives Bks) a_True) (List.nth j (blocks_motives Bks) a_True)
        (env_args C (ns ++ m :: nil)) (env_args C (ns' ++ m' :: nil)).
    #[local] Abbreviation u0_len' := (u0_len D Us i_HUl C u0 HUC).
    #[local] Abbreviation u0_env' := (u0_env VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us i_HUl i_HUs C u0 HCC HUC).
    #[local] Abbreviation u0_gargs' := (u0_gargs VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us i_HUl i_HUs C u0 HCC HUC).
    #[local] Abbreviation Hcp := (vg_canon p D Hvg u0 u0_gargs' u0_len').
    #[local] Abbreviation HnP := (ind_canon_props_np_per _ _ Hcp).
    #[local] Abbreviation HnI := (ind_canon_props_np_iff _ _ Hcp).
    #[local] Abbreviation HaP := (ind_canon_props_arg_per _ _ Hcp).
    #[local] Abbreviation HaI := (ind_canon_props_arg_iff _ _ Hcp).
    #[local] Abbreviation HdP := (ind_canon_props_dom_per _ _ Hcp).
    #[local] Abbreviation HdI := (ind_canon_props_dom_iff _ _ Hcp).
    #[local] Abbreviation Had := (vg_adm p D Hvg u0 u0 u0_gargs' u0_len' u0_gargs').
    #[local] Abbreviation Hass := (valid_group_ass _ _ Hvg).
    #[local] Abbreviation isym := (proj1 (ind_rel_sym_all p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (okr_at D u0 nr))).
    #[local] Abbreviation itrans := (proj1 (ind_rel_trans_all p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (okr_at D u0 nr))).
    (** The lemmas of [Elim.v]: of the frames, of the base at [C], and of
        the motives at [C] on both sides. *)
    #[local] Abbreviation SF f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us i_HUl i_HUs HMall).
    #[local] Abbreviation EB f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us i_HUl i_HUs C u0 HCC HUC).
    #[local] Abbreviation EP f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us i_HUl i_HUs C u0 HCC HUC C HCC Bks i HBks' HMall HAv).

    Lemma s_Ln : List.length ns = im_nn Mm.
    Proof. rewrite (eval_exps_length _ _ _ HNC); exact i_HNl. Qed.

    Lemma s_La : List.length avs = List.length gs.
    Proof. rewrite (eval_exps_length _ _ _ HAC); exact HAl. Qed.

    Lemma s_Mc : exists cs, List.length cs = im_unu D Mm /\
        ⟦ apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c) (im_pre Mm Us ++ Ns ++ As) ⟧ C
          ↘ d_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c (cs ++ ns ++ avs).
    Proof.
      destruct (rel_exp_under_ctx_simple_at HRΓ iota_Mc_valid _ _ HCC) as (mv & _ & Emv & _ & _).
      assert (LNA : List.length (Ns ++ As) = (im_nn Mm + List.length gs)%nat) by (rewrite List.length_app, i_HNl, HAl; reflexivity).
      destruct (con_ref_apps_value VP p D HP HPD m Mm c gs C Us (Ns ++ As) (ns ++ avs) mv HMm HrvM Hcon i_HUl
                  ltac:(apply eval_exps_app; assumption) LNA Emv) as (cs & Lcs & ->).
      exists cs; split; assumption.
    Qed.

    Lemma s_HgN : gsub Γ (sb_of_list Id Ns) (tele_sub (im_nparams Mm) (sb_of_list Id Us) ++ Γ).
    Proof. exact (gsub_ns VP p D HP HPD Γ HΓ Us m Mm HMm (HMall _ _ HMm) Ns i_HNl i_HNs). Qed.

    (** The scrutinee's relation at [C]. *)
    Lemma s_scrut : forall x y, per_head (ind_mty p D m Us Ns) (ind_mty p D m Us Ns) C C x y -> G m u0 u0 ns ns x y.
    Proof.
      intros x y Hxy.
      destruct (presup_rel_exp_under_ctx iota_Mc_valid) as [iT HIT].
      destruct (rel_exp_of_typ_inversion_simple_at HRΓ HIT _ _ HCC) as (t1 & t2 & Et1 & Et2 & [R HR]).
      destruct (scrut_rel VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us i_HUl i_HUs C u0 HCC HUC m Mm HMm (HMall _ _ HMm) Ns i_HNl
                  s_HgN C HCC ns ns HNC HNC t1 t2 _ R Et1 Et2 HR) as [_ ERM].
      apply ERM, (per_head_iff Et1 Et2 HR); exact Hxy.
    Qed.

    Lemma s_self : forall cs, List.length cs = im_unu D Mm ->
        ⟦ apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c) (im_pre Mm Us ++ Ns ++ As) ⟧ C
          ↘ d_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c (cs ++ ns ++ avs) ->
        G m u0 u0 ns ns (d_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c (cs ++ ns ++ avs))
          (d_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c (cs ++ ns ++ avs)) /\
        tele_rel (ar m ns c) (cargs_nonrec gs) (nonrec_arg_vals gs avs) (nonrec_arg_vals gs avs) /\
        con_args_rel p D (okr_at D u0 nr) nr ar dr m u0 u0 ns ns gs avs avs.
    Proof.
      intros cs Lcs Emc.
      destruct (rel_exp_under_ctx_simple_at HRΓ iota_Mc_valid _ _ HCC) as (m1 & m2 & Em1 & Em2 & Hm12).
      assert (m1 = d_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c (cs ++ ns ++ avs)) as -> by (eapply functional_eval_exp; eassumption).
      assert (m2 = d_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c (cs ++ ns ++ avs)) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (s_scrut _ _ Hm12) as Hm.
      split; [ exact Hm |].
      assert (Lb : List.length (cs ++ ns) = (im_unu D Mm + im_nn Mm)%nat) by (rewrite List.length_app, Lcs, s_Ln; reflexivity).
      rewrite List.app_assoc in Hm.
      destruct (ind_rel_con_inv p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hm HMm HrvM Lb)
        as (gs0 & bs' & vs' & Ez & _ & _ & Hcon0 & Lbs' & _ & _ & Har & Hia).
      rewrite Hcon in Hcon0; injection Hcon0 as <-.
      injection Ez as Ez.
      destruct (app_split_eq _ _ _ _ Ez ltac:(congruence)) as [<- <-].
      rewrite (skipn_app_exact cs ns _ Lcs) in Har, Hia.
      split; assumption.
    Qed.

    Lemma s_args : tele_rel (ar m ns c) (cargs_nonrec gs) (nonrec_arg_vals gs avs) (nonrec_arg_vals gs avs) /\
        con_args_rel p D (okr_at D u0 nr) nr ar dr m u0 u0 ns ns gs avs avs.
    Proof. destruct s_Mc as (cs & Lcs & Emc); exact (proj2 (s_self cs Lcs Emc)). Qed.

    Lemma s_Hns : tele_rel (nr m) (List.rev (im_nparams Mm)) ns ns.
    Proof.
      destruct s_Mc as (cs & Lcs & Emc).
      exact (ind_rel_ns p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (okr_at D u0 nr) _ _ _ _ _ _ _ _ HMm (proj1 (s_self cs Lcs Emc))).
    Qed.

    Lemma s_HPC : ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ C ↘ u0 ++ ns.
    Proof. rewrite i_Ps; apply eval_exps_app; [ exact HUC | exact HNC ]. Qed.

    (** The walk along the leaf paths ([LeafVals]), at [C]. *)
    #[local] Abbreviation LV f := (f VP p D HP HPD Γ oq Us Bks i HΓ Hoq i_HUl i_HUs HBks HnmA HMall HAv HnaA HBc HarA HBv
                                     RΓ RU HRΓ HRU C u0 HCC HUC).
    #[local] Abbreviation iota_arg_link := (iota_arg_link p D Γ C u0).

    (** A recursive argument of the constructor: the scrutinee, moved
        along the weakening, is an element of the member, its argument
        related to the scrutinee's. *)
    Lemma iota_arg_link_start : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
        forall a, List.nth_error avs (List.length gs1) = Some a ->
        iota_arg_link m (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) avs)) t a
          (List.nth (List.length gs1) As (a_var 0)) nil.
    Proof.
      intros gs1 t gs2 Heq a Ha Δ RΔ zs HRΔ Hw HE.
      change (List.length (@nil domain) + List.length zs) with (List.length zs) in Hw.
      change (env_args C (nil ++ zs)) with (env_args C zs) in HE |- *.
      set (σL := sb_of_wk (wk_shiftn (List.length zs))).
      assert (Hev : ⟦ σL ⟧s env_args C zs ↘ C).
      { pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn (List.length zs)) (env_args C zs) (wk_mono_shiftn _)) as H.
        rewrite eval_wk_shiftn_args in H; exact H. }
      destruct (exp_inst_link _ _ _ _ _ _ _ _ _ iota_Mc_valid HRΔ Hw HE Hev) as (mw & mC & Emw & EmC & Hm).
      destruct s_Mc as (cs & Lcs & EMc).
      assert (mC = d_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c (cs ++ ns ++ avs)) as -> by (eapply functional_eval_exp; eassumption).
      apply s_scrut, isym in Hm.
      rewrite apps_exp_sub in Emw; cbn [exp_sub] in Emw.
      fold σL in Emw; rewrite !List.map_app, (im_pre_sub D m Mm Us σL Hc HMm i_HUl) in Emw.
      pose proof Emw as Emw0; apply eval_apps_exp in Emw0 as (f0 & ws & _ & Ews & _).
      apply eval_exps_app_inv in Ews as (us1 & zs' & -> & _ & Ezs).
      pose proof Ezs as Ezs0; apply eval_exps_app_inv in Ezs0 as (ns1 & as1 & -> & Ens1 & Eas1).
      assert (Ln1 : List.length ns1 = im_nn Mm) by (rewrite (eval_exps_length _ _ _ Ens1), List.length_map; exact i_HNl).
      destruct (con_ref_apps_value VP p D HP HPD m Mm c gs (env_args C zs) (List.map (fun U => U[σL]) Us) _ _ mw HMm HrvM Hcon
                  ltac:(rewrite List.length_map; exact i_HUl) Ezs ltac:(rewrite List.length_app, !List.length_map, i_HNl, HAl; reflexivity) Emw)
        as (cs' & Lcs' & ->).
      rewrite (List.app_assoc cs ns avs) in Hm.
      destruct (ind_rel_con_inv p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hm HMm HrvM
                  ltac:(rewrite List.length_app, Lcs, s_Ln; reflexivity))
        as (gs0 & bs' & vs' & Ez & _ & _ & Hcon0 & Lbs' & _ & _ & _ & Hia).
      rewrite Hcon in Hcon0; injection Hcon0 as <-.
      injection Ez as Ez; rewrite List.app_assoc in Ez.
      destruct (app_split_eq _ _ _ _ Ez ltac:(rewrite Lbs', List.length_app, Lcs', Ln1; reflexivity)) as [<- <-].
      rewrite (skipn_app_exact cs ns _ Lcs), (skipn_app_exact cs' ns1 _ Lcs') in Hia.
      destruct (con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia gs1 t gs2 Heq) as (x & x' & Hx & Hx' & Hshw).
      rewrite Ha in Hx; injection Hx as <-.
      assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some' As _ Hlt) as [M0 HM0].
      rewrite (List.nth_error_nth _ _ _ HM0).
      destruct (eval_exps_nth _ _ _ (List.length gs1) (M0[σL]) Eas1) as (v0 & Hv0 & Ev0);
        [ rewrite List.nth_error_map, HM0; reflexivity |].
      rewrite Hx' in Hv0; injection Hv0 as <-.
      exists (ns1 ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1)), x'; split; [| exact Hshw ].
      unfold σL in Ev0; rewrite exp_sub_of_wk in Ev0; exact Ev0.
    Qed.

    (** *** The Recursive Results of the Arguments

        The recursive results of the arguments after [gs1]: the
        eliminator's own and the values of [elim_ihs], related. *)
    Lemma s_ihs : forall rest gs1, gs = gs1 ++ rest ->
        exists ihe ihc, ⟦ihs List.skipn (List.length gs1) avs of rest under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C ↘ ihe /\
          ⟦ elim_ihs p D oq Us Bks (cargs_sub σP gs1 As) (im_nn Mm + List.length (cargs_nonrec gs1)) rest
              (List.skipn (List.length gs1) As) ⟧* gc_deps ⍮ gc_stack ⍮ C ↘ ihc /\
          rec_results_rel D dr Rel m u0 u0 (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) avs))
            (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) avs)) rest
            (List.skipn (List.length gs1) avs) (List.skipn (List.length gs1) avs) ihc ihe.
    Proof.
      pose proof (leaves_coherent_of_order _ (rview_struct_order _ _ _ (decl_typed_rstruct _ _ _ Hdt))) as Hco.
      induction rest as [| g rest IH]; intros gs1 Heq.
      - assert (E : List.skipn (List.length gs1) avs = nil)
          by (apply List.skipn_all2; rewrite s_La, Heq, List.app_nil_r; lia).
        rewrite E; exists nil, nil; split; [ constructor | split; [ cbn; constructor | constructor ] ].
      - assert (Hlt : List.length gs1 < List.length avs) by (rewrite s_La, Heq, List.length_app; cbn; lia).
        destruct (nth_error_lt_some avs _ Hlt) as [v Hv].
        assert (HltA : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
        destruct (nth_error_lt_some As _ HltA) as [M0 HM0].
        assert (Lf : List.length (List.firstn (List.length gs1) avs) = List.length gs1) by (rewrite List.length_firstn; lia).
        assert (Heq' : gs = (gs1 ++ g :: nil) ++ rest) by (rewrite <- List.app_assoc; exact Heq).
        destruct (IH _ Heq') as (ihe & ihc & Ee & Ec & Hr).
        rewrite List.length_app in Ee, Ec, Hr; cbn [List.length] in Ee, Ec, Hr; rewrite Nat.add_1_r in Ee, Ec, Hr.
        rewrite (firstn_S_nth _ _ _ Hv), nonrec_arg_vals_app in Hr by exact Lf.
        rewrite (skipn_nth_cons _ _ _ Hv), (skipn_nth_cons _ _ _ HM0).
        rewrite cargs_nonrec_app, List.length_app in Ec.
        destruct g as [B0 | t].
        + assert (Hcs : cargs_sub σP (gs1 ++ ca_arg B0 :: nil) As = (cargs_sub σP gs1 As ,, M0)).
          { rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r, (firstn_S_nth _ _ _ HM0).
            apply cargs_sub_snoc_arg; rewrite List.length_firstn; lia. }
          rewrite Hcs in Ec; cbn [nonrec_arg_vals cargs_nonrec List.length] in Hr, Ec; rewrite List.app_assoc in Hr.
          replace (im_nn Mm + (List.length (cargs_nonrec gs1) + 1)) with (S (im_nn Mm + List.length (cargs_nonrec gs1))) in Ec by lia.
          exists ihe, ihc; split; [ constructor; exact Ee | split; [ cbn [elim_ihs]; exact Ec | constructor; exact Hr ] ].
        + assert (Hcs : cargs_sub σP (gs1 ++ ca_rec t :: nil) As = cargs_sub σP gs1 As).
          { rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r, (firstn_S_nth _ _ _ HM0).
            apply cargs_sub_snoc_rec; rewrite List.length_firstn; lia. }
          rewrite Hcs in Ec; cbn [nonrec_arg_vals cargs_nonrec List.length] in Hr, Ec; rewrite List.app_nil_r in Hr.
          rewrite Nat.add_0_r in Ec.
          destruct (length_rec_ps D HD m Mm HMm c gs gs1 t rest Hcon Heq) as (Mj & HMj & _).
          (** The argument at its frame, at [C]. *)
          set (nv1 := nonrec_arg_vals gs1 (List.firstn (List.length gs1) avs)) in *.
          destruct s_args as (Hnva & Hia).
          destruct (con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia gs1 t rest Heq) as (x & x' & Hx & Hx' & Hsh).
          rewrite Hv in Hx, Hx'; injection Hx as <-; injection Hx' as <-.
          assert (Hnv : tele_prefix_rel (ar m ns c) (List.length (cargs_nonrec gs1)) nv1 nv1).
          { unfold nv1; rewrite <- (List.firstn_skipn (List.length gs1) avs) in Hnva.
            exact (nonrec_prefix_gen _ gs gs1 (ca_rec t :: rest) _ _ _ _ Heq Lf Lf Hnva). }
          assert (Lnv1 : List.length nv1 = List.length (cargs_nonrec gs1)) by (apply length_nonrec_arg_vals; exact Lf).
          assert (Hvals : sem_frame_vals D RΓ RU C u0 Mm gs1 nil (cargs_sub σP gs1 As) (List.nth (List.length gs1) As (a_var 0))
                            RΓ (env_args C nil) C nil u0 ns nv1 v).
          { constructor; cbn [env_args List.fold_left List.length].
            - exact HCC.
            - reflexivity.
            - reflexivity.
            - exact HCC.
            - exists C; pose proof (eval_sigt gs1 _ C (u0 ++ ns) avs Heq s_HPC HAC) as H.
              rewrite <- List.app_assoc in H; exact H.
            - rewrite (List.nth_error_nth _ _ _ HM0).
              destruct (eval_exps_nth _ _ _ (List.length gs1) M0 HAC HM0) as (v0 & Hv0 & Ev0).
              rewrite Hv in Hv0; injection Hv0 as ->; exact Ev0.
            - exact u0_env'.
            - exact u0_len'.
            - exact s_Ln.
            - exact Lnv1. }
          destruct (LV leaf_ihs_vals (S (ptyp_mem t)) m Mm c gs gs1 t rest HMm Hcon Heq Mj HMj (fun _ => Nat.lt_succ_diag_r _)
                      _ _ _ _ (iota_frame gs1 t rest Heq) RΓ HRΓ nil u0 ns nv1 v ns nv1 Hvals s_Hns Hnv 0 nil nil v v (ns ++ nv1 ++ nil)
                      (Nat.le_0_l _) eq_refl (tele_prefix_rel_nil _) ltac:(cbn [ptyp_skip]; rewrite List.app_nil_r; exact Hsh)
                      ltac:(cbn [ptyp_skip apps_vars_iter List.app]; rewrite List.app_nil_r; exact (iota_arg_link_start gs1 t rest Heq v Hv)))
            as [rs' rs Ers' Ers Hrs].
          cbn [ptyp_skip sb_shift_iter sb_qn apps_vars_iter List.app env_args List.fold_left] in Ers, Ers', Hrs.
          rewrite List.app_nil_r in Hrs; rewrite Nat.add_0_r, i_Us_id, blocks_sub_id, (List.nth_error_nth _ _ _ HM0) in Ers'.
          exists (rs ++ ihe), (rs' ++ ihc); split; [ constructor; [ exact Ers | exact Ee ] | split ].
          * cbn [elim_ihs]; apply eval_exps_app; [ exact Ers' | exact Ec ].
          * apply rec_results_rec; [| | exact Hrs | exact Hr ].
            -- rewrite (eval_exps_length _ _ _ Ers'), List.length_map; apply length_shape_leaves.
            -- exact (proj1 (proj2 eval_ih_length_all) _ _ _ _ _ _ _ Ers D Hl Hco).
    Qed.

  End IotaSem.

  (** *** The Rule *)
  Lemma rel_exp_under_ctx_elim_iota_at : forall n B, brs_lookup (eb_brs bm) c = Some (n, B) ->
      Γ ⊨ a_elim oq Us m Bks (apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c) (im_pre Mm Us ++ Ns ++ As))
        ≈ B[sb_of_list Id (Ns ++ As ++ elim_ihs p D oq Us Bks σP (im_nn Mm) gs As)]
        : (eb_motive bm)[sb_of_list Id (Ns ++ apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                                                (im_pre Mm Us ++ Ns ++ As) :: nil)].
  Proof.
    intros n B Hlk.
    set (Mc := apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c) (im_pre Mm Us ++ Ns ++ As)).
    pose proof iota_Mc_valid as HMc; fold Mc in HMc.
    (** The left side, an eliminator. *)
    assert (HUU : forall j U U' T, List.nth_error Us j = Some U -> List.nth_error Us j = Some U' ->
               List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊨ U ≈ U' : T)
      by (intros * HU HU' HT; rewrite HU in HU'; injection HU' as <-; exact (i_HUs _ _ _ HU HT)).
    assert (HAA : forall k Mk b b', ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> List.nth_error Bks k = Some b' ->
               elim_mctx p D k Mk Us ++ Γ ⊨ eb_motive b ≈ eb_motive b' : Typeω@i)
      by (intros * HMk Hb Hb'; rewrite Hb in Hb'; injection Hb' as <-; exact (HAv _ _ _ HMk Hb)).
    assert (HBB : forall k Mk b b' c0 gs0 n0 B0 B0', ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
               List.nth_error Bks k = Some b' -> ind_con Mk c0 = Some gs0 ->
               brs_lookup (eb_brs b) c0 = Some (n0, B0) -> brs_lookup (eb_brs b') c0 = Some (n0, B0') ->
               elim_bctx p D Mk gs0 (blocks_motives Bks) Us ++ Γ ⊨ B0 ≈ B0' : elim_bty p D k Mk c0 gs0 (eb_motive b) Us)
      by (intros * HMk Hb Hb' Hc0 Hl1 Hl2; rewrite Hb in Hb'; injection Hb' as <-; rewrite Hl1 in Hl2; injection Hl2 as <-;
          exact (HBv _ _ _ _ _ _ _ HMk Hb Hc0 (brs_lookup_in _ _ _ _ Hl1))).
    pose proof (rel_exp_under_ctx_elim_at VP p D HP HPD Γ oq oq m Mm bm Bks Bks Us Us Ns Mc Mc i HΓ Hgr Hgr HMm Hbm HBks HBks
                  i_HUl i_HUs i_HUl HUU i_HNl i_HNs HMc HnmA HnmA HMall HAA HnaA
                  (fun _ _ _ H1 H2 => ltac:(rewrite H1 in H2; injection H2 as <-; reflexivity)) HBc HarA HBB) as HL.
    (** The right side, the branch at its instance. *)
    pose proof gsub_iota as Hgi.
    pose proof (HBv _ _ _ _ _ _ _ HMm Hbm Hcon (brs_lookup_in _ _ _ _ Hlk)) as HBv'.
    assert (Lih : List.length (elim_ihs p D oq Us Bks σP (im_nn Mm) gs As) = cargs_nrec D gs) by (apply length_elim_ihs; exact HAl).
    pose proof (rel_exp_under_ctx_gsub Hgi HBv') as HR.
    rewrite (elim_bty_iota p D m Mm c gs (eb_motive bm) Us Ns As _ Hc HMm i_HUl i_HNl HAl Lih) in HR; fold Mc in HR.
    destruct (rel_ctx_wf_per_ctx_env HΓ) as [RΓ HRΓ].
    destruct (rel_ctx_wf_per_ctx_env Usem) as [RU HRU].
    assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
    destruct (presup_rel_exp_under_ctx HL) as [iT HT].
    destruct (presup_rel_exp_under_ctx HBv') as [iB HTb].
    apply (rel_exp_under_ctx_of_simple HRΓ HL HR).
    intros ρ ρ' Hρρ'.
    assert (Hρ'ρ' : RΓ ρ' ρ') by (etransitivity; [ symmetry; exact Hρρ' | exact Hρρ' ]).
    destruct (rel_exp_under_ctx_simple_at HRΓ HL _ _ Hρρ') as (l & l' & El & El' & Hll').
    (** The values at [ρ']. *)
    destruct (us_vals VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us i_HUl i_HUs ρ' ρ' Hρ'ρ') as (u0 & u0' & Hu0 & Hu0' & _).
    destruct (rel_exp_under_ctx_simple_at HRΓ HMc _ _ Hρ'ρ') as (mv & _ & Emv & _ & _).
    pose proof Emv as Emv0; unfold Mc in Emv0; apply eval_apps_exp in Emv0 as (f0 & ws & _ & Ews & _).
    apply eval_exps_app_inv in Ews as (us1 & vrest & -> & _ & Evrest).
    apply eval_exps_app_inv in Evrest as (ns & avs & -> & HNC & HAC).
    destruct (s_Mc RΓ RU HRΓ HRU ρ' u0 ns avs Hρ'ρ' Hu0 HNC HAC) as (cs & Lcs & EMc).
    destruct (s_self RΓ RU HRΓ HRU ρ' u0 ns avs Hρ'ρ' Hu0 HNC HAC cs Lcs EMc) as (Hself & _ & _).
    destruct (s_ihs RΓ RU HRΓ HRU ρ' u0 ns avs Hρ'ρ' Hu0 HNC HAC gs nil eq_refl) as (ihe & ihc & Ee & Ec & Hir).
    cbn [List.length List.skipn List.firstn nonrec_arg_vals cargs_sub cargs_nonrec] in Ee, Ec, Hir.
    rewrite List.app_nil_r in Hir; rewrite Nat.add_0_r in Ec.
    assert (Hsk : List.skipn (im_unu D Mm) (cs ++ ns) = ns) by exact (skipn_app_exact cs ns _ Lcs).
    rewrite (List.app_assoc cs ns avs) in Hself, EMc.
    (** The branch's environments. *)
    pose proof (HBc _ _ _ _ HMm Hcon) as HBm.
    destruct (rel_ctx_wf_per_ctx_env HBm) as [RB HRB].
    assert (HPB : PER RB) by (eapply per_env_PER; exact HRB).
    pose proof (cv_bctx_elem VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us i_HUl i_HUs ρ' u0 Hρ'ρ' Hu0 ρ' Hρ'ρ' Bks i HBks' HMall HAv
                  m Mm c gs HMm Hcon HBm HrvM ρ' ρ' Hρ'ρ' Hρ'ρ' u0 u0 _ _ (cs ++ ns) (cs ++ ns) avs avs ihc ihe
                  ltac:(rewrite Hsk; exact Hself) ltac:(rewrite Hsk; exact Hir) RB HRB) as Hec.
    rewrite Hsk in Hec; symmetry in Hec.
    destruct (rel_exp_under_ctx_simple_at HRB HBv' _ _ Hec) as (r1 & r2 & Er1 & Er2 & Hr12).
    (** The eliminator's own value. *)
    destruct ref_target as (Dq & Mk & HDq & HMk & Hunu & Hnn).
    assert (Enp : im_np Dq Mk = List.length (cs ++ ns))
      by (unfold im_np; rewrite List.length_app, Lcs, (eval_exps_length _ _ _ HNC), i_HNl, Hunu, Hnn; lia).
    assert (Eel : ⟦elim d_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c ((cs ++ ns) ++ avs) at m of p u0 Bks ⟧
                    gc_deps ⍮ gc_stack ⍮ ρ' ↘ r1).
    { eapply eval_elim_con; [ exact Hl | exact HMm | apply surjective_pairing | exact HDq | exact HMk | exact Hcon | | exact Hbm
                            | exact Hlk | | exact (leaves_coherent_of_order _ (rview_struct_order _ _ _ (decl_typed_rstruct _ _ _ Hdt))) | |].
      - rewrite Enp, List.length_app, (eval_exps_length _ _ _ HAC), HAl; reflexivity.
      - rewrite (HarA _ _ _ _ _ _ _ HMm Hbm Hcon (brs_lookup_in _ _ _ _ Hlk)), Hnn; reflexivity.
      - rewrite Enp, skipn_app_exact by reflexivity; exact Ee.
      - rewrite Enp, skipn_app_exact, firstn_app_exact by reflexivity; rewrite <- Hunu, Hsk; exact Er1. }
    destruct (elim_grp_of_elem _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMm Hself (decl_typed_order _ _ _ Hdt) oq Hgr) as [Hgr1 _].
    assert (l' = r1) as -> by (eapply functional_eval_exp; [ exact El' | eapply eval_exp_elim; [ exact Hu0 | exact EMc | exact Hgr1 | exact Eel ] ]).
    (** The right side's value. *)
    set (Eτ := env_args ρ' (ns ++ avs ++ ihc)) in *.
    assert (Hτ : ⟦ sb_of_list Id (Ns ++ As ++ elim_ihs p D oq Us Bks σP (im_nn Mm) gs As) ⟧s ρ' ↘ Eτ)
      by (apply eval_sb_of_list; [ apply eval_sub_id | apply eval_exps_app; [ exact HNC | apply eval_exps_app; [ exact HAC | exact Ec ] ] ]).
    destruct (exp_inst_link _ _ _ _ _ _ _ _ _ HBv' HRΓ (gsub_valid Hgi) Hρ'ρ' Hτ) as (r & n0 & Er & En0 & Hrn).
    assert (n0 = r2) as -> by (eapply functional_eval_exp; eassumption).
    assert (Hcc : RB Eτ Eτ) by (etransitivity; [ symmetry; exact Hec | exact Hec ]).
    assert (EC1 : per_head (elim_bty p D m Mm c gs (eb_motive bm) Us) (elim_bty p D m Mm c gs (eb_motive bm) Us)
                    (env_args ρ' (ns ++ avs ++ ihe)) Eτ
                  <~> per_head (elim_bty p D m Mm c gs (eb_motive bm) Us) (elim_bty p D m Mm c gs (eb_motive bm) Us) Eτ Eτ).
    { apply (per_head_of_typ_resp HRB HTb).
      apply rel_chain_cons; [ exact Hec |]. apply rel_chain_cons; [ exact Hcc |]. apply rel_chain_of_pair; exact Hcc. }
    pose proof (per_head_inst _ _ _ _ _ _ _ _ _ _ HTb HRΓ (gsub_valid Hgi) Hρ'ρ' Hτ Hτ) as ER.
    rewrite (elim_bty_iota p D m Mm c gs (eb_motive bm) Us Ns As _ Hc HMm i_HUl i_HNl HAl Lih) in ER; fold Mc in ER.
    exists l, r; split; [ exact El | split; [ exact Er |] ].
    set (T := (eb_motive bm)[sb_of_list Id (Ns ++ Mc :: nil)]) in *.
    assert (HT' : Γ ⊨ T : Typeω@iT) by exact (rel_exp_under_ctx_refl_left HT).
    assert (Hl'r2 : per_head T T ρ' ρ' r1 r2) by (apply ER, EC1; exact Hr12).
    assert (Hrr2 : per_head T T ρ' ρ' r r2) by (apply ER; exact Hrn).
    pose proof (per_head_sym _ _ _ _ _ _ HRΓ HT' Hρ'ρ' _ _ Hrr2) as Hr2r.
    pose proof (per_head_trans _ _ _ _ _ _ HRΓ HT' Hρ'ρ' _ _ _ Hl'r2 Hr2r) as Hlr.
    assert (EC : per_head T T ρ' ρ' <~> per_head T T ρ ρ').
    { apply (per_head_of_typ_resp HRΓ HT).
      apply rel_chain_cons; [ exact Hρ'ρ' |]. apply rel_chain_cons; [ symmetry; exact Hρρ' |]. apply rel_chain_of_pair; exact Hρρ'. }
    exact (per_head_trans _ _ _ _ _ _ HRΓ HT' Hρρ' _ _ _ Hll' (proj1 (EC _ _) Hlr)).
  Qed.
End Iota.

End Fixed_GCtx.
