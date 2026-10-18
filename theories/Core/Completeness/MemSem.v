(** * Term Members of Valid Units

    A term member a valid unit, or a module expression valid in what it
    denotes, has by lookup is valid at the type lookup reads, its δ-reduct
    at it too ([valid_unit_mem_all]).  A definition of a body, read through the
    entries its local opens generate, is related to the definition of the
    same name of any body the module PER relates to it ([body_sel_term]);
    a unit lacking parameters types its members at the [Π] over them
    ([unit_walk]). *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping IndSyntax GlobalPaths MemberLemmas
  MemberWf DescTyping LookupSound.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases FunctionCases UniverseCases SubstitutionCases LetCases UnitCases InstanceCases MemberReps
  ModuleVal ModuleSem UnitSub ModexpRules GlobalArgs TeleSem IndSem ValidUnit UnitBody FiledSem UnitSem CanonSem.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules Kinds KindsTyping KindsEval KindsPER.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

(** ** Generated Entries *)

Lemma body_eq_upto_types_gens_inv : forall gs1 gs2 Φk Φx k, List.length gs1 = List.length gs2 ->
    body_eq_upto_types (gens_append Φk k gs1) (gens_append Φx k gs2) -> body_eq_upto_types Φk Φx.
Proof.
  induction gs1 as [| g1 gs1 IH]; intros [| g2 gs2] * Hl Hk; cbn in Hl; try lia; [ exact Hk |].
  cbn [gens_append] in Hk; destruct (ig_entry g1) as [d1 E1], (ig_entry g2) as [d2 E2].
  exact (proj1 (IH gs2 _ _ _ ltac:(lia) Hk)).
Qed.

Lemma kgens_prefix_at : forall Θ Ξ ρ H its gs, kgens Θ Ξ ρ H its gs ->
    forall y its1 it, items_upto y its = Some (its1, it) ->
    exists gs0 g Rg, gs = gs0 ++ g :: Rg /\ S (List.length gs0) = List.length its1 /\ kgens Θ Ξ ρ H (it :: nil) (g :: nil) /\
      forall Φ k, gm_prefix_upto (gens_append Φ k gs) y = Some (gens_append Φ k (gs0 ++ g :: nil)).
Proof.
  intros * Hg; induction Hg as [| | | ]; intros y its1 it0 Hu; cbn [items_upto] in Hu; try discriminate.
  all: destruct (items_upto y its) as [[its1' it1] |] eqn:Eu.
  all: try (injection Hu as <- <-;
            destruct (IHHg _ _ _ Eu) as (gs0 & g0 & Rg & -> & Hl & Hg1 & Hp);
            match goal with |- exists _ _ _, ?g :: _ = _ /\ _ => exists (g :: gs0), g0, Rg end;
            split; [ reflexivity |]; split; [ cbn; lia |]; split; [ exact Hg1 |];
            intros Φ k; cbn [gens_append app ig_entry]; apply Hp).
  all: match type of Hu with context [String.eqb ?a ?b] => destruct (String.eqb a b) eqn:Ey end; [| discriminate ]; injection Hu as <- <-.
  all: pose proof (items_upto_none_iff _ _ Eu) as Hn; rewrite <- (kgens_names _ _ _ _ _ _ Hg) in Hn.
  all: eexists nil, _, _; split; [ reflexivity |]; split; [ reflexivity |]; split; [ solve [ econstructor; eauto using kg_nil ] |].
  all: intros Φ k; cbn [gens_append app ig_entry]; rewrite gens_prefix_none by exact Hn;
         cbn [gm_prefix_upto iitem_name] in *; rewrite Ey; reflexivity.
Qed.

Lemma gens_prefix_none_items : forall Θ Ξ io Γ H its gs Φ k y, items_gen Θ Ξ io Γ H its gs -> items_upto y its = None ->
    gm_prefix_upto (gens_append Φ k gs) y = gm_prefix_upto Φ y.
Proof.
  intros * Hg Hu; apply gens_prefix_none.
  rewrite (items_gen_names _ _ _ _ _ _ _ Hg); exact (items_upto_none_iff _ _ Hu).
Qed.

Lemma kgens_prefix_none_items : forall Θ Ξ ρ H its gs Φ k y, kgens Θ Ξ ρ H its gs -> items_upto y its = None ->
    gm_prefix_upto (gens_append Φ k gs) y = gm_prefix_upto Φ y.
Proof.
  intros * Hg Hu; apply gens_prefix_none.
  rewrite (kgens_names _ _ _ _ _ _ Hg); exact (items_upto_none_iff _ _ Hu).
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  Variables (Θm : gdeps) (Ξm : gstack).
  Hypothesis Hgm : ⊢ᵍ Θm ⍮ Ξm.
  Hypothesis Hsub : gc_sub Θm Ξm gc_deps gc_stack.
  Hypothesis Hgf : valid_filed_mods Θm Ξm.

  #[local] Abbreviation valid_unit := (valid_unit Θm Ξm).
  #[local] Abbreviation valid_modexp := (valid_modexp Θm Ξm).

Lemma kbody_functional : forall ρ Φ Φk1 Φk2, kbody gc_deps gc_stack ρ Φ Φk1 -> kbody gc_deps gc_stack ρ Φ Φk2 -> Φk1 = Φk2.
Proof. intros * H1 H2; exact (proj1 (proj2 (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack))))) _ _ _ H1 _ H2). Qed.

Lemma kenv_functional : forall ρ Φ σ1 σ2, kenv gc_deps gc_stack ρ Φ σ1 -> kenv gc_deps gc_stack ρ Φ σ2 -> σ1 = σ2.
Proof. intros * H1 H2; exact (proj1 (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack)))) _ _ _ H1 _ H2). Qed.

(** The kind a value an open's kinds read gives a member. *)
Lemma open_kind : forall ρ Φk ρ1 σ1 H h n k, ⟦ Φk ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 -> kenv gc_deps gc_stack ρ Φk σ1 ->
    ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ1 ↘ h -> skind gc_deps gc_stack σ1 H (n :: nil) k -> dkind gc_deps gc_stack h (n :: nil) k.
Proof.
  intros * Hb Hk Hh Hs.
  destruct (kind_eval_benv _ _ _ _ _ Hb _ (kshape_refl _ _ ρ)) as (σ' & Hk' & Hs').
  pose proof (kenv_functional _ _ _ _ Hk Hk') as <-.
  apply (kind_eval_modexp _ _ _ _ _ Hh), (skind_id _ _ _ _ (proj1 Hs')); exact Hs.
Qed.

(** ** Definitions of a Body *)

(** A definition of a valid body, against the definition of the same name
    of any body related to it. *)
Lemma body_sel_term : forall D Φ Φx, body_xp Θm Ξm D Φ Φx -> body_shape Φx Φx -> ⊨ body_ctx Φx ++ D ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Ψ ++ D ⊨ᵐ H ≈ H /\
       forall n Rn An, mdenote Θm Ξm (Ψ ++ D) (me_mem H n) Rn -> ds_ty Θm Ξm Rn = Some An -> valid_mem (Ψ ++ D) H n An (ds_red Rn)) ->
    forall RD ρ, EF D ≈ D ∈ per_ctx_env ↘ RD -> RD ρ ρ -> forall Φk, kbody gc_deps gc_stack ρ Φ Φk -> body_eq_upto_types Φk Φx ->
    forall x Φx' b pv A M, gm_prefix_upto Φx x = Some (gm_ext Φx' x (ge_def b pv A (Some M))) ->
    exists ρ' a i RA r, ⟦ Φx' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' /\ ⟦ A ⟧ ρ' ↘ a /\ per_univ_elem i RA a a /\ ⟦ M ⟧ ρ' ↘ r /\
      forall ρh Φh Φhk, per_body ρh Φh ρ Φ -> kbody gc_deps gc_stack ρh Φh Φhk ->
        exists Φhk' bh pvh Ah Mh ρh' rh, gm_prefix_upto Φhk x = Some (gm_ext Φhk' x (ge_def bh pvh Ah (Some Mh))) /\
          ⟦ Φhk' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρh ↘ ρh' /\ ⟦ Mh ⟧ ρh' ↘ rh /\ RA rh r.
Proof.
  intros D Φ Φx Hx; induction Hx as [Γ | Γ Φ Φx y E Hx IH | Γ Φ Φx H its R Rm gs Hx IH HR HRm Hg Hok];
    intros Hsx HC Ho RD ρ HRD Hρ Φk Hkb Hkx x Φx' b pv A M Hp.
  - discriminate.
  - inversion Hkb as [| ? ? Φk0 ? ? Hkb0 |]; subst.
    destruct Hkx as (Hkx0 & _ & _).
    cbn [body_shape] in Hsx; destruct Hsx as (Hsx0 & _ & HsE).
    cbn [body_opens gm_dropn] in Ho.
    pose proof (body_xp_nopens _ _ _ _ _ Hx) as Hn.
    cbn [gm_prefix_upto] in Hp; destruct (String.eqb x y) eqn:Exy.
    + (* the definition itself *)
      apply String.eqb_eq in Exy; subst y; injection Hp as <- ->.
      cbn [body_ctx app] in HC.
      destruct (rel_ctx_wf_def_inv HC) as [[i HA] HM].
      pose proof (rel_ctx_wf_tail HC) as HC0.
      destruct (rel_ctx_wf_per_ctx_env HC0) as [R1 HR1].
      destruct (benv_exists _ _ Hn (proj1 (body_shape_fill _ _ Hn Hsx0)) HC0 _ _ HRD HR1 _ Hρ) as (ρ1 & Hb1 & Hρ1).
      destruct (rel_exp_of_typ_inversion_simple_at HR1 HA _ _ Hρ1) as (a & a' & Ha & Ha' & [RA HRA]).
      pose proof (functional_eval_exp _ _ _ _ Ha Ha') as <-.
      destruct (rel_exp_under_ctx_simple_at HR1 HM _ _ Hρ1) as (r & _ & Hr & _ & _).
      exists ρ1, a, i, RA, r; split; [ exact Hb1 | split; [ exact Ha | split; [ exact HRA | split; [ exact Hr |] ] ] ].
      intros ρh Φh Φhk Hbh Hkh.
      inversion Hbh as [| ? Φh0 ? ? Φxh Φx'' ρh1 ρ1' ? ? ? ? ? ? ? ? ? ? ? Rr Hbh0 Hkh0 Hk0 Hbh1 Hb1' HT HM' | |]; subst.
      pose proof (kbody_functional _ _ _ _ Hkh0 Hkb0) as ->.
      apply (body_eq_upto_types_benv _ _ Hkx0) in Hbh1; pose proof (functional_eval_benv _ _ _ _ Hbh1 Hb1) as ->.
      inversion Hkh as [| ? ? Φhk0 ? ? Hkh1 |]; subst.
      pose proof (kbody_functional _ _ _ _ Hkh1 Hbh0) as ->.
      destruct Hb1' as [ah a2 Hah Ha2 HRah].
      destruct HT as [mh m2 Hmh Hm2 HRm].
      functional_eval_rewrite_clear.
      assert (E : R <~> RA) by (eapply per_univ_elem_left_irrel; [ exact HRah | exact HRA ]).
      exists Φxh; do 6 eexists; split; [ cbn; rewrite String.eqb_refl; reflexivity |].
      split; [ exact Hk0 | split; [ exact Hmh | apply E; exact HRm ] ].
    + (* an entry before it *)
      assert (HC0 : ⊨ body_ctx Φx ++ Γ) by (destruct E as [? ? ? [] | | |]; cbn in HsE; try contradiction; exact (rel_ctx_wf_tail HC)).
      destruct (IH Hsx0 HC0 Ho _ _ HRD Hρ _ Hkb0 Hkx0 _ _ _ _ _ _ Hp) as (ρ' & a & i & RA & r & Hb & Ha & HRA & Hr & Hh).
      exists ρ', a, i, RA, r; split; [ exact Hb | split; [ exact Ha | split; [ exact HRA | split; [ exact Hr |] ] ] ].
      intros ρh Φh Φhk Hbh Hkh.
      assert (Hrest : exists Φh0 Eh, Φh = gm_ext Φh0 y Eh /\ per_body ρh Φh0 ρ Φ)
        by (inversion Hbh; subst; eauto).
      destruct Hrest as (Φh0 & Eh & -> & Hbh0).
      inversion Hkh as [| ? ? Φhk0 ? ? Hkh0 |]; subst.
      destruct (Hh _ _ _ Hbh0 Hkh0) as (Φhk' & bh & pvh & Ah & Mh & ρh' & rh & Hph & Hbh' & Hmh & Hrr).
      exists Φhk', bh, pvh, Ah, Mh, ρh', rh; split; [ cbn; rewrite Exy; exact Hph | split; [ exact Hbh' | split; assumption ] ].
  - (* an open *)
    pose proof (items_gen_length _ _ _ _ _ _ _ Hg) as Hl.
    assert (Eo : body_opens (gm_open Φ H its) (gens_append Φx 0 gs) = (body_ctx Φx, H) :: body_opens Φ Φx).
    { cbn [body_opens]; rewrite <- Hl, gm_dropn_gens_append; reflexivity. }
    rewrite Eo in Ho.
    pose proof (body_shape_gens_l _ _ _ Hsx) as Hsx0.
    pose proof HC as HC'.
    rewrite gens_body_ctx_base, <- app_assoc in HC.
    pose proof (rel_ctx_wf_app_r _ _ HC) as HC0.
    pose proof (body_xp_nopens _ _ _ _ _ Hx) as Hn.
    inversion Hkb as [| | ? ? Φk0 σ1 ? ? gsk Hkb0 Hke Hkg]; subst.
    assert (Hlk : List.length gsk = List.length gs).
    { pose proof (f_equal (@List.length _) (kgens_names _ _ _ _ _ _ Hkg)) as E1.
      pose proof (f_equal (@List.length _) (items_gen_names _ _ _ _ _ _ _ Hg)) as E2.
      rewrite !length_map in E1, E2; lia. }
    pose proof (body_eq_upto_types_gens_inv _ _ _ _ _ Hlk Hkx) as Hkx0.
    destruct (items_upto x its) as [[its1 it] |] eqn:Eu.
    + (* generated by this open *)
      destruct (gens_prefix_some _ _ _ _ _ _ _ Hg _ _ _ Eu) as (its0 & gs0 & g & -> & Hg0 & Hg1 & (Rits & Rg & -> & ->) & Hpx).
      rewrite Hpx, gens_append_snoc in Hp; injection Hp as <- Hd HE.
      pose proof (items_gen_length _ _ _ _ _ _ _ Hg0) as Hl0.
      inversion Hg1 as [| ? ? ? d pv0 ? ? Hg2 | ? ? ? n d pv0 A_n om ? ? HmH Hg2 | ? ? ? n d pv0 Rn ? ? HmH HRn Hg2 |]; subst;
        cbn [ig_entry snd gentry_wk] in HE; try discriminate.
      injection HE as <- <- <- <-.
      cbn [ig_name ig_entry fst] in Eu, Hpx |- *.
      (* the target and its members, before the open's entries *)
      destruct (Ho 0 _ _ eq_refl) as [HH HS].
      destruct (rel_ctx_wf_per_ctx_env HC0) as [Ro HRo].
      destruct (benv_exists _ _ Hn (proj1 (body_shape_fill _ _ Hn Hsx0)) HC0 _ _ HRD HRo _ Hρ) as (ρo & Hbo & Hρo).
      destruct (HS _ _ _ HmH eq_refl) as [[iA HAn] _ HSn].
      destruct (HSn _ HRo _ Hρo) as [t an i_n RAn Ht Han HRAn Hmt _].
      (* the environment after the first [j] entries *)
      assert (HnP : gm_nopens (gens_append Φx 0 gs0) = 0) by (rewrite gens_append_nopens; exact Hn).
      assert (HshP : body_shape (gens_append Φx 0 gs0) (gens_append Φx 0 gs0)).
      { apply (body_shape_gens_l (ig_def d pv0 A_n (a_mem H n) :: Rg) _ (0 + List.length gs0)).
        rewrite <- gens_append_app; exact Hsx. }
      assert (HCP : ⊨ body_ctx (gens_append Φx 0 gs0) ++ Γ).
      { destruct (body_ctx_gens_firstn (gs0 ++ ig_def d pv0 A_n (a_mem H n) :: Rg) Φx 0 (List.length gs0)) as (X & HX).
        rewrite firstn_app, Nat.sub_diag, firstn_all in HX; cbn [firstn] in HX; rewrite app_nil_r in HX.
        rewrite HX, <- app_assoc in HC'; exact (rel_ctx_wf_app_r _ _ HC'). }
      destruct (rel_ctx_wf_per_ctx_env HCP) as [RP HRP].
      destruct (benv_exists _ _ HnP (proj1 (body_shape_fill _ _ HnP HshP)) HCP _ _ HRD HRP _ Hρ) as (ρ' & Hb' & Hρ').
      pose proof Hb' as Hb''; apply eval_gens_split in Hb'' as (ρo' & Hbo' & Hbg).
      pose proof (functional_eval_benv _ _ _ _ Hbo' Hbo) as ->.
      pose proof (skipn_benv_gens _ _ _ Hbg) as Hskip.
      assert (HlX : List.length (body_ctx (gens_append gm_nil 0 gs0)) = List.length gs0) by apply gens_body_ctx_length.
      rewrite <- HlX in Hskip.
      rewrite gens_body_ctx_base, <- app_assoc in HRP, HCP.
      destruct (wk_coh_ex _ _ _ _ _ _ HH HCP HRP Hρ' Hskip) as (hj & Hhj).
      pose proof (wk_coh _ _ _ _ _ _ _ _ HH HCP HRP Hρ' Hskip Ht Hhj) as Hhjt.
      rewrite HlX in Hhj.
      destruct (Hmt _ Hhjt) as [r r0 Hr Hr0 Hrr0].
      (* the type, under the shift past the entries *)
      pose proof (rel_sub_of_wk (rel_wk_under_ctx_shiftn _ _ HCP)) as Hτ.
      pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn (List.length (body_ctx (gens_append gm_nil 0 gs0)))) ρ' (wk_mono_shiftn _)) as Hev.
      rewrite eval_wk_shiftn, Hskip in Hev.
      destruct (valid_typ_inst _ _ _ _ _ _ HAn Hτ HRP _ _ Hρ' Hev) as (a1 & a2 & Ha1 & Ha2 & [Rw Hww]).
      rewrite exp_sub_of_wk, HlX in Ha1.
      functional_eval_rewrite_clear.
      assert (HPw : PER Rw) by (eapply per_elem_PER; exact Hww).
      assert (Ew : Rw <~> RAn) by (eapply per_univ_elem_left_irrel; [ exact Hww | exact HRAn ]).
      assert (Hw11 : per_univ_elem iA Rw a1 a1) by (etransitivity; [ exact Hww | symmetry; exact Hww ]).
      assert (HPn : PER RAn) by (eapply per_elem_PER; exact HRAn).
      exists ρ', a1, iA, Rw, r; split; [ exact Hb' |]; split; [ exact Ha1 |]; split; [ exact Hw11 |].
      split; [ cbn [exp_wk]; eapply eval_mem_of_sel; eassumption |].
      (* a related body's entry of the same name *)
      intros ρh Φh Φhk Hbh Hkh.
      inversion Hbh; subst.
      pose proof (kbody_functional _ _ _ _ H6 Hkb0) as ->.
      apply (body_eq_upto_types_benv _ _ Hkx0) in H8; pose proof (functional_eval_benv _ _ _ _ H8 Hbo) as ->.
      pose proof (functional_eval_modexp _ _ _ _ H10 Ht) as ->.
      pose proof (kbody_functional _ _ _ _ H12 Hkh) as ->.
      inversion Hkh as [| | ? ? Φhk0 σh1 ? ? gshk Hkh1 Hkhe Hkhg]; subst.
      pose proof (kbody_functional _ _ _ _ Hkh1 H5) as ->.
      destruct (kgens_prefix_at _ _ _ _ _ _ Hkhg _ _ _ Eu) as (gsh0 & gh & Rgh & -> & Hlh & Hkg1 & Hph).
      destruct (kgens_prefix_at _ _ _ _ _ _ Hkg _ _ _ Eu) as (gsk0 & gk & Rgk & -> & Hlk0 & Hkgk & Hpk).
      rewrite length_app in Hlh, Hlk0; cbn in Hlh, Hlk0.
      clear IH Ho HS HSn HC HC' Eo Hsx.
      (* the kind both sides give the member *)
      assert (Hkdef : skind gc_deps gc_stack σ1 H (n :: nil) mk_term).
      { destruct (body_eq_upto_types_prefix _ _ Hkx d _ _ ltac:(rewrite Hpx, gens_append_snoc; reflexivity)) as (Φk' & Ek & Hpk' & _ & HE).
        rewrite Hpk, gens_append_snoc in Hpk'; injection Hpk' as _ _ HEk.
        inversion Hkgk as [| ? ? ? ? ? ? Hk2 | ? ? ? ? ? ? ? Hsk Hk2 | ? ? ? ? ? ? ? Hsk Hk2]; subst;
          cbn [ig_entry snd gentry_wk] in HE;
          destruct HE as [HE | (? & ? & ? & ? & ? & HE & _)]; try discriminate; exact Hsk. }
      assert (Hkt : dkind gc_deps gc_stack h (n :: nil) mk_term).
      { apply (per_dmod_kequiv _ _ H11).
        exact (open_kind _ _ _ _ _ _ _ _ (proj2 (body_eq_upto_types_benv _ _ Hkx0 _ _) Hbo) Hke Ht Hkdef). }
      inversion Hkg1 as [| ? ? ? ? ? ? Hk2 | ? ? ? ? ? ? ? Hsk Hk2 | ? ? ? ? ? ? ? Hsk Hk2]; subst.
      2: { exfalso. pose proof (open_kind _ _ _ _ _ _ _ _ H7 Hkhe H9 Hsk) as Hkm.
           pose proof (proj1 (@functional_kind gc_deps gc_stack) _ _ _ Hkt _ Hkm) as Hc; discriminate. }
      (* the entry evaluates, and its target re-read is related to the target *)
      apply eval_gens_split in H14 as (ρh1' & Hbh1' & Hbhg).
      pose proof (functional_eval_benv _ _ _ _ Hbh1' H7) as ->.
      rewrite gens_append_app in Hbhg; apply eval_gens_split in Hbhg as (ρq & Hbq & _).
      assert (Hbq' : ⟦ gens_append Φx0 0 gsh0 ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρh ↘ ρq) by (apply eval_gens_split; exists ρ1; split; assumption).
      assert (Hj : List.length gsh0 < List.length ((its0 ++ (Some n, d, pv0) :: nil) ++ Rits)) by (rewrite !length_app; cbn; lia).
      assert (Hdq : ⟦ gm_dropn (List.length ((its0 ++ (Some n, d, pv0) :: nil) ++ Rits) - List.length gsh0)
                       (gens_append Φx0 0 (gsh0 ++ ig_def d pv0 a_True (a_mem H0 n) :: Rgh)) ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρh ↘ ρq).
      { assert (Hlh2 : List.length (gsh0 ++ ig_def d pv0 a_True (a_mem H0 n) :: Rgh) = List.length ((its0 ++ (Some n, d, pv0) :: nil) ++ Rits))
          by (pose proof (f_equal (@List.length _) (kgens_names _ _ _ _ _ _ Hkhg)) as E; rewrite !length_map in E; exact E).
        rewrite gm_dropn_gens by lia.
        replace (List.length (gsh0 ++ ig_def d pv0 a_True (a_mem H0 n) :: Rgh) - _) with (List.length gsh0) by lia.
        rewrite firstn_app, Nat.sub_diag, firstn_all; cbn [firstn]; rewrite app_nil_r; exact Hbq'. }
      destruct (H16 _ _ Hj Hdq) as (hhj & Hhhj).
      pose proof (H21 _ _ _ Hj Hdq Hhhj) as Hhth.
      destruct (Hmt _ (per_dmod_trans _ _ _ Hhth H11)) as [rh r0' Hrh Hr0' Hrr'].
      pose proof (functional_eval_sel _ _ _ _ Hr0' Hr0) as ->.
      rewrite Hph, gens_append_snoc.
      do 7 eexists; split; [ reflexivity |].
      split; [ exact Hbq' |]; split; [ cbn [ig_entry snd gentry_wk exp_wk Nat.add]; eapply eval_mem_of_sel; [ exact Hhhj | exact Hrh ] |].
      apply Ew; etransitivity; [ exact Hrr' | symmetry; exact Hrr0 ].
    + (* an entry before the open *)
      rewrite (gens_prefix_none_items _ _ _ _ _ _ _ _ _ _ Hg Eu) in Hp.
      destruct (IH Hsx0 HC0 (fun k => Ho (S k)) _ _ HRD Hρ _ Hkb0 Hkx0 _ _ _ _ _ _ Hp) as (ρ' & a & i & RA & r & Hb & Ha & HRA & Hr & Hh).
      exists ρ', a, i, RA, r; split; [ exact Hb | split; [ exact Ha | split; [ exact HRA | split; [ exact Hr |] ] ] ].
      intros ρh Φh Φhk Hbh Hkh.
      inversion Hbh; subst.
      inversion Hkh as [| | ? ? Φhk0 σh1 ? ? gshk Hkh1 Hkhe Hkhg]; subst.
      match goal with Hb0 : per_body ρh ?Φh0 ρ Φ |- _ =>
        destruct (Hh _ _ _ Hb0 Hkh1) as (Φhk' & bh & pvh & Ah & Mh & ρh' & rh & Hph & Hbh' & Hmh & Hrr) end.
      exists Φhk', bh, pvh, Ah, Mh, ρh', rh.
      split; [ rewrite (kgens_prefix_none_items _ _ _ _ _ _ _ _ _ Hkhg Eu); exact Hph | split; [ exact Hbh' | split; assumption ] ].
Qed.

(** ** What the Term Members of Literals Denote *)

Lemma ds_ty_mod_none : forall R, ds_is_mod R -> ds_ty Θm Ξm R = None.
Proof. intros [| | |] H; cbn in *; first [ contradiction | reflexivity ]. Qed.

(** A definition of a body, filled in, over the parameters. *)
Lemma body_mem_desc : forall Γ Δ Φ Φx x R A, body_xp Θm Ξm (Δ ++ Γ) Φ Φx ->
    mdenote Θm Ξm Γ (me_mem (me_lit (gu_open Δ Φ)) x) R -> ds_ty Θm Ξm R = Some A ->
    exists Φ' b pv A0 M0 σ, gm_prefix_upto Φx x = Some (gm_ext Φ' x (ge_def b pv A0 (Some M0))) /\ gm_fill Φ' = Some σ /\
      R = ds_term (ctx_pi Δ A0[σ]) (Some (ctx_fn Δ M0[σ])).
Proof.
  intros * Hx Hm Ht.
  inversion Hm as [? ? ? ? ? Hq _ | | | | ? ? ? R0 R0m Γy E rd R1 ? Hm0 Hmd He Hed Hr]; subst; [ cbn in Hq; discriminate |].
  inversion Hm0; subst; [ match goal with Hq : mod_qname (me_lit _) = Some _ |- _ => cbn in Hq; discriminate end |].
  match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
  match goal with Hb : ds_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
  match goal with Hx' : body_xp _ _ _ Φ ?Φx1 |- _ =>
    pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hgm)))) _ _ _ Hx _ Hx') as <- end.
  cbn in Hmd; injection Hmd as <-.
  cbn in He; destruct (gm_prefix_upto Φx x) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
  pose proof (gm_prefix_name _ _ _ _ _ Hp) as ->.
  destruct E0 as [[|] pv A0 [M0 |] | pv U | | ]; try discriminate; injection He as <- <- <-.
  - inversion Hed; subst; cbn in Hr.
    destruct (gm_fill Φ') as [σ |] eqn:Hf; cbn in Hr; [ injection Hr as <- | discriminate ].
    do 6 eexists; split; [ reflexivity | split; [ exact Hf | reflexivity ] ].
  - exfalso; inversion Hed; subst.
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hmod end.
    cbn in Hr; destruct (gm_fill Φ') as [σ |]; cbn in Hr; [ injection Hr as <- | discriminate ].
    rewrite (ds_ty_mod_none _ (ds_is_mod_up Δ _ (ds_is_mod_sub _ σ Hmod))) in Ht; discriminate.
Qed.

(** The outside parameters of a closed module part read with more of them:
    the same, except that a term of no δ-reduct read bare is read as its
    name with them. *)
Lemma ds_named_app : forall Θ Δ Ns M R,
    ds_named (Θ ++ Δ) Ns M R = ds_named Θ Ns M R \/
    (Θ = nil /\ Ns = nil /\ exists A0, R = ds_term A0 None /\ ds_named (Θ ++ Δ) Ns M R = ds_term A0 (Some M)).
Proof.
  intros [| e Θ] [| e' Δ] [| N Ns] M R; cbn [List.app]; try (left; reflexivity).
  destruct R as [A0 [M0 |] | | |]; try (left; reflexivity).
  right; repeat split; eauto.
Qed.

(** A term member of an alias is its target's, over the parameters; or,
    when the target is a filed module read bare and the member has no
    δ-reduct there, the member read as its name over the parameters. *)
Lemma alias_mem_desc : forall Γ Δ E x R A,
    mdenote Θm Ξm Γ (me_mem (me_lit (gu_mk Δ (md_alias E))) x) R -> ds_ty Θm Ξm R = Some A ->
    exists R', mdenote Θm Ξm (Δ ++ Γ) (me_mem E x) R' /\
      (R = ds_up Δ R' \/
       exists A0 RE p T Φ, R' = ds_term A0 None /\ mdenote Θm Ξm (Δ ++ Γ) E RE /\
         ds_mod Θm Ξm RE = Some (ds_closed nil p T Φ nil) /\ R = ds_up Δ (ds_term A0 (Some (a_mem (qname_mod p) x)))).
Proof.
  intros * Hm Ht.
  inversion Hm as [? ? ? ? ? Hq _ | | | | ? ? ? R0 R0m Γy Ee rd R1 ? Hm0 Hmd He Hed Hr]; subst; [ cbn in Hq; discriminate |].
  inversion Hm0; subst; [ match goal with Hq : mod_qname (me_lit _) = Some _ |- _ => cbn in Hq; discriminate end |].
  match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu as [| ? ? ? ? RE REm HmE HmodE]; subst end.
  pose proof (ds_mod_is_mod _ _ _ _ HmodE) as HisE.
  rewrite (ds_is_mod_mod _ _ _ (ds_is_mod_up _ _ HisE)) in Hmd; injection Hmd as <-.
  destruct REm as [| Δe Φ Φx | Θ p T Φ Ns | ]; cbn in HisE; try contradiction; cbn [ds_up] in He, Hed.
  - (* an open module part *)
    cbn in He; destruct (gm_prefix_upto Φx x) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
    pose proof (gm_prefix_name _ _ _ _ _ Hp) as ->.
    assert (He' : exists Ee', ds_entry (ds_open Δe Φ Φx) x = Some (body_ctx Φ' ++ Δe, Ee', rd_open Δe Φ') /\
                    Ee = Ee' /\ Γy = body_ctx Φ' ++ Δe ++ Δ /\ rd = rd_open (Δe ++ Δ) Φ').
    { cbn; rewrite Hp; destruct E0 as [[|] ? ? [] | | | ]; try discriminate; injection He as <- <- <-; eexists; repeat split. }
    destruct He' as (Ee' & He' & -> & -> & ->).
    cbn [ds_read] in Hr; destruct (gm_fill Φ') as [σ |] eqn:Hf; cbn in Hr; [ injection Hr as <- | discriminate ].
    exists (ds_up Δe (ds_sub R1 σ)); split; [| left; rewrite ds_up_cat; reflexivity ].
    cbn [ds_epath] in Hed; rewrite <- !app_assoc in Hed.
    eapply dn_mem; [ exact HmE | exact HmodE | exact He' | cbn [ds_epath]; rewrite <- app_assoc; exact Hed | cbn; rewrite Hf; reflexivity ].
  - (* a closed module part *)
    cbn in He; destruct (gm_prefix_upto Φ x) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
    injection He as <- <- <-.
    cbn [ds_read] in Hr; destruct (ds_ats R1 Ns) as [R2 |] eqn:Ha; cbn in Hr; [ injection Hr as <- | discriminate ].
    assert (Hed' : edenote Θm Ξm (nil ++ Δ ++ Γ) (Some (qname_in p x)) (ge_read T E0) R1).
    { destruct E0 as [? ? ? ? | pv U | | ]; cbn [ge_read] in Hed |- *; try (inversion Hed; subst; constructor).
      exfalso.
      assert (HU : exists U', match U with | gu_mk Δ (md_body sm_closed Φ) => ge_mod pv (gu_mk (Δ ++ T) (md_body sm_closed Φ)) | _ => ge_mod pv U end = ge_mod pv U')
        by (destruct U as [? [[] ?|?]]; eexists; reflexivity).
      destruct HU as [U' HU]; rewrite HU in Hed; inversion Hed; subst.
      match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (ds_ats_is_mod _ _ _ (udenote_is_mod _ _ _ _ _ _ Hu) Ha) as Hmod end.
      rewrite ds_up_cat in Ht.
      destruct R2; cbn in Hmod; try contradiction; rewrite ds_named_fix in Ht by reflexivity; cbn in Ht; discriminate. }
    exists (ds_up Θ (ds_named Θ Ns (apps (a_mem (qname_mod p) x) Ns) R2)); split.
    { eapply dn_mem; [ exact HmE | exact HmodE | cbn; rewrite Hp; reflexivity | exact Hed' | cbn; rewrite Ha; reflexivity ]. }
    destruct (ds_named_app Θ Δ Ns (apps (a_mem (qname_mod p) x) Ns) R2) as [Hn | (-> & -> & A0 & -> & Hn)];
      rewrite Hn; [ left; rewrite ds_up_cat; reflexivity |].
    right; exists A0, RE, p, T, Φ; split; [ reflexivity | split; [ exact HmE | split; [ exact HmodE | reflexivity ] ] ].
Qed.

(** A member of no δ-reduct of a module expression whose module part is a
    filed module read bare is related to that filed member. *)
Lemma valid_mem_bare_name : forall Γ E RE p T Φ x A,
    valid_modexp Γ E -> mdenote Θm Ξm Γ E RE -> ds_mod Θm Ξm RE = Some (ds_closed nil p T Φ nil) ->
    valid_mem Γ E x A None -> valid_mem Γ E x A (Some (a_mem (qname_mod p) x)).
Proof.
  intros * Hs Hm Hmd Hsm.
  assert (HEP : Γ ⊨ᵐ E ≈ ds_unit (ds_closed nil p T Φ nil)) by (eapply valid_modexp_canon; eassumption).
  cbn [ds_unit me_apps] in HEP.
  pose proof (valid_mem_transport _ _ _ _ _ _ (rel_modexp_under_ctx_sym HEP) Hsm) as HsmP.
  pose proof (rel_mem_of_valid_mem _ _ _ _ _ _ (rel_modexp_under_ctx_trans (rel_modexp_under_ctx_sym HEP) HEP) HsmP) as HPx.
  destruct Hsm as [HA _ HS].
  constructor; [ exact HA | intros M [= <-]; exact HPx |].
  intros RΓ HR ρ Hρ.
  destruct (HS _ HR _ Hρ) as [k a i RA Hk Ha HRA Hmt _].
  destruct (rel_modexp_at _ _ _ _ _ HEP HR _ _ Hρ) as (k1 & kp & Hk1 & Hkp & Hkk).
  pose proof (functional_eval_modexp _ _ _ _ Hk1 Hk) as ->.
  destruct (Hmt _ (per_dmod_sym _ _ Hkk)) as [r r' Hr Hr' Hrr].
  apply mk_valid_mem_at with (vma_mod := k) (vma_typ := a) (vma_lvl := i) (vma_rel := RA); try assumption.
  intros M [= <-]; apply (mk_rel_mem_reduct _ _ _ _ _ r r'); [ eapply eval_mem_of_sel; eassumption | assumption | assumption ].
Qed.

(** ** Units Lacking Parameters *)

(** A unit's closure lacking its parameters types a member at the [Π] over
    them of the type its closure with all of them given types it at, and
    the [λ] over them of a term related to that member is related to it. *)
Lemma unit_walk : forall Δ Γ D x A0 om0 RΓ,
    tele_ass Δ -> ⊨ Δ ++ Γ -> (exists i, Δ ++ Γ ⊨ A0 : Typeω@i) ->
    (forall R, EF Δ ++ Γ ≈ Δ ++ Γ ∈ per_ctx_env ↘ R -> forall ρ, R ρ ρ -> forall k0, ⟦ nil ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ k0 ->
       exists a i Ra, ⟦ A0 ⟧ ρ ↘ a /\ per_univ_elem i Ra a a /\ dmod_has_mem k0 x Ra /\
         forall M0, om0 = Some M0 -> exists m r, ⟦ M0 ⟧ ρ ↘ m /\ k0 ·ₜ x gc_deps ⍮ gc_stack ↘ r /\ Ra m r) ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    forall ρ, RΓ ρ ρ -> forall k, ⟦ Δ ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ k -> per_dmod k k ->
    exists a i Ra, ⟦ ctx_pi Δ A0 ⟧ ρ ↘ a /\ per_univ_elem i Ra a a /\ dmod_has_mem k x Ra /\
      forall M0, om0 = Some M0 -> exists m r, ⟦ ctx_fn Δ M0 ⟧ ρ ↘ m /\ k ·ₜ x gc_deps ⍮ gc_stack ↘ r /\ Ra m r.
Proof.
  induction Δ as [| e Δ0 IH] using rev_ind; intros * HΔ HC HA0 Hbase HΓ ρ Hρ k Hk Hkk; cbn [List.app] in *.
  - exact (Hbase _ HΓ _ Hρ _ Hk).
  - destruct (tele_ass_app_inv _ _ HΔ) as [HΔ0 He]; inversion He as [| ? ? [X ->] _]; subst.
    destruct HA0 as [iA HA].
    destruct (valid_exp_under_ctx_ctx_pi _ _ _ _ HC HA) as [iP HPi].
    rewrite <- app_assoc in HC, HA, Hbase; cbn [List.app] in HC, HA, Hbase.
    pose proof (rel_ctx_wf_app_r _ _ HC) as HXΓ.
    destruct (rel_ctx_wf_ass_inv HXΓ) as [iX HX].
    pose proof (per_ctx_env_of_typ HΓ HX) as HΓX.
    assert (HP : PER RΓ) by (eapply per_env_PER; exact HΓ).
    pose proof (functional_eval_close _ _ _ _ _ Hk (close_unsat (Δ0 ++ ce_ass X :: nil) D ρ ltac:(rewrite length_app; cbn; lia))) as ->.
    rewrite ctx_pi_app in HPi |- *; cbn [ctx_pi] in HPi |- *.
    destruct (rel_exp_of_typ_inversion_simple_at HΓ HPi _ _ Hρ) as (a & a' & Ha & Ha' & [Ra HRa]).
    functional_eval_rewrite_clear.
    inversion Ha; subst.
    match goal with H3 : ⟦ X ⟧ ρ ↘ ?a0 |- _ => rename H3 into HXa; rename a0 into a0 end.
    set (k := dm_local (Δ0 ++ ce_ass X :: nil) D ρ) in *.
    assert (Hnp : nextparam k a0) by (constructor; exact HXa).
    assert (Hsel : k ·ₜ x gc_deps ⍮ gc_stack ↘ d_member k (x :: nil)) by (apply eval_sel_unsat; rewrite length_app; cbn; lia).
    destruct (rel_exp_of_typ_inversion_simple_at HΓ HX _ _ Hρ) as (x0 & x0' & Hx0 & Hx0' & [RX HRX]).
    functional_eval_rewrite_clear.
    assert (Hstep : forall j Rx c, per_univ_elem j Rx a0 a0 -> Rx c c -> forall kc, $ᵐ| k & c | gc_deps ⍮ gc_stack ↘ kc ->
               exists b l Rb, ⟦ ctx_pi Δ0 A0 ⟧ ρ ↦ c ↘ b /\ per_univ_elem l Rb b b /\ dmod_has_mem kc x Rb /\
                 forall M0, om0 = Some M0 -> exists m r, ⟦ ctx_fn Δ0 M0 ⟧ ρ ↦ c ↘ m /\ kc ·ₜ x gc_deps ⍮ gc_stack ↘ r /\ Rb m r).
    { intros j Rx c HRx Hc kc Hkc.
      assert (Hρc : per_env_extend X X RΓ (ρ ↦ c) (ρ ↦ c))
        by (split; [ exact Hρ | eapply per_head_of; [ exact HXa | exact HXa | exact HRx | exact Hc ] ]).
      destruct (per_dmod_appm _ _ _ Hkk Hnp) as (ih & Rh & ah & Hph & HRh & Happ).
      pose proof (nextparam_functional _ _ Hph _ Hnp) as ->.
      assert (Eh : Rh <~> Rx) by (eapply per_univ_elem_right_irrel; [ exact HRh | exact HRx ]).
      destruct (Happ c c (proj2 (Eh _ _) Hc)) as (kc1 & kc2 & Hk1 & Hk2 & Hkk').
      pose proof (functional_eval_appm _ _ _ _ Hk1 Hkc) as ->; pose proof (functional_eval_appm _ _ _ _ Hk2 Hkc) as ->.
      inversion Hkc as [| ? ? ? ? ? ? Hkc' Hl |]; subst.
      apply app_inj_tail in Hl as [<- [= <-]].
      destruct (IH _ _ _ _ _ _ HΔ0 HC (ex_intro (fun i => _ ⊨ _ : Typeω@i) _ HA) Hbase HΓX _ Hρc _ Hkc' Hkk')
        as (b & l & Rb & Hb & HRb & Hm & Hred).
      exists b, l, Rb; repeat split; assumption. }
    exists (Πᵈ a0 ρ (ctx_pi Δ0 A0)), iP, Ra; split; [ exact Ha | split; [ exact HRa | split ] ].
    + eapply dmod_has_mem_fun; [ exact Hnp | exact Hkk | exact HRa | exists iX, RX; exact HRX | | eexists; exact Hsel ].
      intros j Rx c HRx Hc kc b Hkc Hb; destruct (Hstep _ _ _ HRx Hc _ Hkc) as (b' & l & Rb & Hb' & HRb & Hm & _).
      functional_eval_rewrite_clear; exists l, Rb; split; assumption.
    + intros M0 HM0; rewrite ctx_fn_app; cbn [ctx_fn].
      exists (λᵈ ρ (ctx_fn Δ0 M0)), (d_member k (x :: nil)).
      split; [ apply eval_exp_fn |]; split; [ exact Hsel |].
      eapply red_fun; [ exact Hnp | exact HRa | exists iX, RX; exact HRX | exact Hkk | exact Hsel |].
      intros j Rx c HRx Hc kc b Hkc Hb; destruct (Hstep _ _ _ HRx Hc _ Hkc) as (b' & l & Rb & Hb' & HRb & Hm & Hred).
      functional_eval_rewrite_clear.
      destruct (Hred _ eq_refl) as (m & r & Hm0 & Hr & Hmr).
      exists l, Rb, m, r; repeat split; try assumption; apply eval_app_fn; exact Hm0.
Qed.

(** ** Definitions of a Saturated Body *)

Lemma per_body_kbody_l : forall ρ Φ ρ' Φ', per_body ρ Φ ρ' Φ' -> exists Φk, kbody gc_deps gc_stack ρ Φ Φk.
Proof.
  intros * Hb; destruct Φ; inversion Hb; subst; eexists; first [ constructor; eassumption | eassumption | constructor ].
Qed.

(** A definition filled in, at an environment, against its value in the
    environment the body before it makes. *)
Lemma body_def_rel : forall D Φx x Φ' b pv A M σ,
    gm_nopens Φx = 0 -> ⊨ body_ctx Φx ++ D ->
    gm_prefix_upto Φx x = Some (gm_ext Φ' x (ge_def b pv A (Some M))) -> gm_fill Φ' = Some σ ->
    forall RD, EF D ≈ D ∈ per_ctx_env ↘ RD -> forall ρ, RD ρ ρ ->
    exists ρ1 a1 a3 m1 m3 (i : nat) R, ⟦ Φ' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 /\
      ⟦ A[σ] ⟧ ρ ↘ a1 /\ ⟦ A ⟧ ρ1 ↘ a3 /\ per_univ_elem i R a1 a3 /\
      ⟦ M[σ] ⟧ ρ ↘ m1 /\ ⟦ M ⟧ ρ1 ↘ m3 /\ R m1 m3 /\
      D ⊨ A[σ] : Typeω@i /\ D ⊨ M[σ] : A[σ].
Proof.
  intros * Hn HC Hp Hf RD HD ρ Hρ.
  destruct (prefix_body_ctx _ _ _ Hn Hp) as [Ψ HΨ]; cbn [body_ctx] in HΨ.
  rewrite HΨ, <- app_assoc in HC; cbn [List.app] in HC.
  pose proof (rel_ctx_wf_app_r _ _ HC) as HC1.
  pose proof (rel_ctx_wf_tail HC1) as HC0.
  destruct (rel_ctx_wf_def_inv HC1) as [[i HA] HM].
  pose proof (prefix_nopens _ _ _ Hn Hp) as Hn'; cbn in Hn'.
  destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0].
  destruct (fill_rel _ _ _ Hn' Hf HC0 _ _ HD HR0 _ Hρ) as (ρσ & ρ1 & Hσ & Hb & H01).
  pose proof (fill_gsub _ _ _ Hn' Hf HC0) as Hg.
  pose proof (gsub_valid Hg) as Hτ.
  destruct (valid_typ_inst _ _ _ _ _ _ HA Hτ HD _ _ Hρ Hσ) as (a1 & a2 & Ha1 & Ha2 & [Ra12 H12]).
  destruct (rel_exp_of_typ_inversion_simple_at HR0 HA _ _ H01) as (a2' & a3 & Ha2' & Ha3 & [Ra23 H23]).
  functional_eval_rewrite_clear.
  destruct (valid_inst _ _ _ _ _ _ HM Hτ HD _ _ Hρ Hσ) as (m1 & m2 & a2' & j & Rm & Hm1 & Hm2 & Ha2' & HRm & Hm12).
  destruct (valid_at _ _ _ _ HM HR0 _ _ H01) as (m2' & m3 & a2'' & j' & Rm' & Hm2' & Hm3 & Ha2'' & HRm' & Hm23).
  functional_eval_rewrite_clear.
  assert (E1 : Rm <~> Ra12) by (eapply per_univ_elem_right_irrel; [ exact HRm | apply per_univ_elem_sym; exact H12 ]).
  assert (E2 : Rm' <~> Ra12) by (eapply per_univ_elem_right_irrel; [ exact HRm' | apply per_univ_elem_sym; exact H12 ]).
  assert (E3 : Ra23 <~> Ra12) by (eapply per_univ_elem_right_irrel; [ exact H23 | apply per_univ_elem_sym; exact H12 ]).
  assert (HP12 : PER Ra12) by (eapply per_elem_PER; exact H12).
  assert (H13 : per_univ_elem i Ra12 a1 a3)
    by (eapply per_univ_trans; [ exact H12 | exact (per_univ_elem_resp_iff H23 E3) ]).
  pose proof (rel_exp_under_ctx_gsub Hg HA) as HAσ; cbn [exp_sub] in HAσ.
  pose proof (rel_exp_under_ctx_gsub Hg HM) as HMσ.
  exists ρ1, a1, a3, m1, m3, i, Ra12; repeat split; try assumption.
  apply E1 in Hm12; apply E2 in Hm23; etransitivity; eassumption.
Qed.

Lemma body_base : forall D Φ Φx x Φ' b pv A M σ,
    body_xp Θm Ξm D Φ Φx -> body_shape Φx Φx -> ⊨ body_ctx Φx ++ D ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Ψ ++ D ⊨ᵐ H ≈ H /\ kinds_ok Θm Ξm (Ψ ++ D) H /\
       forall n Rn An, mdenote Θm Ξm (Ψ ++ D) (me_mem H n) Rn -> ds_ty Θm Ξm Rn = Some An -> valid_mem (Ψ ++ D) H n An (ds_red Rn)) ->
    gm_prefix_upto Φx x = Some (gm_ext Φ' x (ge_def b pv A (Some M))) -> gm_fill Φ' = Some σ ->
    forall RD, EF D ≈ D ∈ per_ctx_env ↘ RD -> forall ρ, RD ρ ρ -> forall sm,
    exists a i Ra, ⟦ A[σ] ⟧ ρ ↘ a /\ per_univ_elem i Ra a a /\ dmod_has_mem (dm_local nil (md_body sm Φ) ρ) x Ra /\
      exists m r, ⟦ M[σ] ⟧ ρ ↘ m /\ dm_local nil (md_body sm Φ) ρ ·ₜ x gc_deps ⍮ gc_stack ↘ r /\ Ra m r.
Proof.
  intros * Hx Hsx HC Ho Hp Hf RD HD ρ Hρ sm.
  pose proof (body_xp_nopens _ _ _ _ _ Hx) as Hn.
  destruct (kbody_exists _ _ _ _ _ Hx Hsx HC (fun k Ψ H Hk => proj1 (proj2 (Ho k Ψ H Hk))) _ _ _ HD Hρ (kshape_refl _ _ ρ))
    as (Φk & Hkb & Hkx).
  destruct (body_sel_term _ _ _ Hx Hsx HC (fun k Ψ H Hk => conj (proj1 (Ho k Ψ H Hk)) (proj2 (proj2 (Ho k Ψ H Hk))))
              _ _ HD Hρ _ Hkb Hkx _ _ _ _ _ _ Hp) as (ρ' & a & i & RA & r & Hb' & Ha & HRA & Hr & Hh).
  destruct (body_def_rel _ _ _ _ _ _ _ _ _ Hn HC Hp Hf _ HD _ Hρ)
    as (ρ1 & a1 & a3 & m1 & m3 & i1 & R1 & Hb1 & Ha1 & Ha3 & HR13 & Hm1 & Hm3 & HRm & _ & _).
  pose proof (functional_eval_benv _ _ _ _ Hb1 Hb') as ->.
  functional_eval_rewrite_clear.
  destruct (body_eq_upto_types_prefix _ _ Hkx _ _ _ Hp) as (Φk' & Ek & Hpk & Hkx' & HE).
  assert (HEk : exists A', Ek = ge_def b pv A' (Some M)) by (destruct HE as [-> | (? & ? & ? & A' & ? & -> & [= -> -> -> ->])]; eauto).
  destruct HEk as [A' ->].
  assert (Hsel : dm_local nil (md_body sm Φ) ρ ·ₜ x gc_deps ⍮ gc_stack ↘ r)
    by (eapply eval_sel_body; [ exact Hkb | exact Hpk | apply (body_eq_upto_types_benv _ _ Hkx'); exact Hb' | exact Hr ]).
  assert (HPR : PER R1) by (eapply per_elem_PER; exact HR13).
  assert (HR11 : per_univ_elem i1 R1 a1 a1) by (etransitivity; [ exact HR13 | symmetry; exact HR13 ]).
  assert (E : R1 <~> RA) by (eapply per_univ_elem_right_irrel; [ apply per_univ_elem_sym; exact HR13 | exact HRA ]).
  exists a1, i1, R1; split; [ exact Ha1 | split; [ exact HR11 | split ] ].
  - intros h Hh0.
    inversion Hh0; subst;
      [| exfalso; match goal with Hn : nextparam (dm_local nil (md_body _ _) _) _ |- _ => exact (nextparam_body_nil _ _ _ _ Hn) end ].
    match goal with Hb0 : per_body ?ρh ?Φh ρ Φ |- _ => rename Hb0 into Hbh end.
    destruct (per_body_kbody_l _ _ _ _ Hbh) as (Φhk & Hkh).
    destruct (Hh _ _ _ Hbh Hkh) as (Φhk' & bh & pvh & Ah & Mh & ρh' & rh & Hph & Hbh' & Hmh & Hrr).
    apply (mk_rel_mem_val _ _ _ _ rh r); [ eapply eval_sel_body; eassumption | exact Hsel | apply E; exact Hrr ].
  - exists m1, r; split; [ exact Hm1 | split; [ exact Hsel | exact HRm ] ].
Qed.

Lemma body_def_valid : forall D Φx x Φ' b pv A M σ,
    gm_nopens Φx = 0 -> ⊨ body_ctx Φx ++ D ->
    gm_prefix_upto Φx x = Some (gm_ext Φ' x (ge_def b pv A (Some M))) -> gm_fill Φ' = Some σ ->
    (exists i, D ⊨ A[σ] : Typeω@i) /\ D ⊨ M[σ] : A[σ].
Proof.
  intros * Hn HC Hp Hf.
  destruct (prefix_body_ctx _ _ _ Hn Hp) as [Ψ HΨ]; cbn [body_ctx] in HΨ.
  rewrite HΨ, <- app_assoc in HC; cbn [List.app] in HC.
  pose proof (rel_ctx_wf_app_r _ _ HC) as HC1.
  pose proof (rel_ctx_wf_tail HC1) as HC0.
  destruct (rel_ctx_wf_def_inv HC1) as [[i HA] HM].
  pose proof (prefix_nopens _ _ _ Hn Hp) as Hn'; cbn in Hn'.
  pose proof (fill_gsub _ _ _ Hn' Hf HC0) as Hg.
  split; [ exists i; pose proof (rel_exp_under_ctx_gsub Hg HA) as H0; cbn [exp_sub] in H0; exact H0 |].
  exact (rel_exp_under_ctx_gsub Hg HM).
Qed.

(** ** The Term Members of Valid Units *)

Lemma valid_unit_mem_all :
  (forall Γ K, valid_unit Γ K -> forall x R A, mdenote Θm Ξm Γ (me_mem K x) R -> ds_ty Θm Ξm R = Some A ->
     valid_mem Γ K x A (ds_red R)) /\
  (forall Γ H, valid_modexp Γ H -> forall x R A, mdenote Θm Ξm Γ (me_mem H x) R -> ds_ty Θm Ξm R = Some A ->
     valid_mem Γ H x A (ds_red R)).
Proof.
  apply valid_unit_modexp_ind.
  - (* a filed module at arguments *)
    intros Γ p T Φ Ns Hw Hgl HΓ Hs x R A Hm Ht.
    eapply filed_mem; eassumption.
  - (* a body *)
    intros Γ Δ Φ Φx Hw Hx HΔ HΓ HC Hsl IHsl Hs Hsx HK Hopv Hops IHops x R A Hm Ht.
    destruct (body_mem_desc _ _ _ _ _ _ _ Hx Hm Ht) as (Φ' & b & pv & A0 & M0 & σ & Hp & Hf & ->).
    cbn in Ht |- *; injection Ht as <-.
    pose proof (rel_ctx_wf_app_r _ _ HC) as HΔΓ.
    pose proof (body_xp_nopens _ _ _ _ _ Hx) as Hn.
    destruct (body_def_valid _ _ _ _ _ _ _ _ _ Hn HC Hp Hf) as ([i HAσ] & HMσ).
    destruct (valid_exp_under_ctx_ctx_pi _ _ _ _ HΔΓ HAσ) as [j HP].
    constructor; [ exists j; exact HP | intros M' [= <-]; exact (valid_exp_under_ctx_ctx_fn _ _ _ _ HΔ HΔΓ HMσ) |].
    intros RΓ HRΓ ρ Hρ.
    destruct (rel_modexp_at _ _ _ _ _ HK HRΓ _ _ Hρ) as (k & k' & Hk & Hk' & Hkk).
    pose proof (functional_eval_modexp _ _ _ _ Hk' Hk) as ->.
    apply eval_me_lit_iff in Hk.
    assert (Ho : forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Ψ ++ Δ ++ Γ ⊨ᵐ H ≈ H /\
               kinds_ok Θm Ξm (Ψ ++ Δ ++ Γ) H /\
               forall n Rn An, mdenote Θm Ξm (Ψ ++ Δ ++ Γ) (me_mem H n) Rn -> ds_ty Θm Ξm Rn = Some An ->
                 valid_mem (Ψ ++ Δ ++ Γ) H n An (ds_red Rn))
      by (intros k0 Ψ H Hk0; split; [ exact (Hopv _ _ _ Hk0) | split; [ exact (valid_modexp_kinds _ _ Hgm Hgf _ _ (Hops _ _ _ Hk0)) | exact (IHops _ _ _ Hk0) ] ]).
    destruct (unit_walk Δ Γ (md_body sm_open Φ) x A0[σ] (Some M0[σ]) RΓ HΔ HΔΓ (ex_intro _ i HAσ)
                ltac:(intros R' HR' ρ' Hρ' k0 Hk0; inversion Hk0; subst;
                      destruct (body_base _ _ _ _ _ _ _ _ _ _ Hx Hsx HC Ho Hp Hf _ HR' _ Hρ' sm_open)
                        as (a & i' & Ra & Ha & HRa & Hm' & m & r & Hm0 & Hr & Hmr);
                      exists a, i', Ra; repeat split; try assumption; intros M1 [= <-]; exists m, r; repeat split; assumption)
                HRΓ _ Hρ _ Hk Hkk)
      as (a & i' & Ra & Ha & HRa & Hmt & Hred).
    apply mk_valid_mem_at with (vma_mod := k) (vma_typ := a) (vma_lvl := i') (vma_rel := Ra);
      [ exact Hk' | exact Ha | exact HRa | exact Hmt |].
    intros M' [= <-]; destruct (Hred _ eq_refl) as (m & r & Hm0 & Hr & Hmr).
    exact (mk_rel_mem_reduct _ _ _ _ _ m r Hm0 Hr Hmr).
  - (* an alias *)
    intros Γ Δ E Hw HΔ HΓ HΔΓ HK HE Hsmt IHE x R A Hm Ht.
    (* the target's member, its δ-reduct, if any, or the filed member it
       is read as over the parameters *)
    assert (Hk : exists A' om', A = ctx_pi Δ A' /\ ds_red R = option_map (ctx_fn Δ) om' /\ valid_mem (Δ ++ Γ) E x A' om').
    { destruct (alias_mem_desc _ _ _ _ _ _ Hm Ht) as (R' & Hm' & [-> | (A0 & RE & p & T & Φ & -> & HmE & HmdE & ->)]).
      - destruct (ds_ty_up_inv _ _ _ _ _ Ht) as (A' & Ht' & ->).
        exists A', (ds_red R'); split; [ reflexivity | split; [ apply ds_red_up | exact (IHE _ _ _ Hm' Ht') ] ].
      - cbn in Ht; injection Ht as <-.
        exists A0, (Some (a_mem (qname_mod p) x)); split; [ reflexivity | split; [ reflexivity |] ].
        exact (valid_mem_bare_name _ _ _ _ _ _ _ _ Hsmt HmE HmdE (IHE _ _ _ Hm' eq_refl)). }
    destruct Hk as (A' & om' & -> & -> & [[iA HA'] HM' HS']).
    destruct (valid_exp_under_ctx_ctx_pi _ _ _ _ HΔΓ HA') as [j HP].
    constructor; [ exists j; exact HP
                 | intros M Hom; destruct om' as [M' |]; cbn in Hom; [ injection Hom as <- | discriminate ];
                   exact (valid_exp_under_ctx_ctx_fn _ _ _ _ HΔ HΔΓ (HM' _ eq_refl)) |].
    intros RΓ HRΓ ρ Hρ.
    destruct (rel_modexp_at _ _ _ _ _ HK HRΓ _ _ Hρ) as (k & k' & Hk & Hk' & Hkk).
    pose proof (functional_eval_modexp _ _ _ _ Hk' Hk) as ->.
    apply eval_me_lit_iff in Hk.
    destruct (unit_walk Δ Γ (md_alias E) x A' om' RΓ HΔ HΔΓ (ex_intro _ iA HA')
                ltac:(intros R0 HR0 ρ0 Hρ0 k0 Hk0; inversion Hk0; subst; try (cbn in *; lia);
                      destruct (HS' _ HR0 _ Hρ0) as [k1 a i' Ra Hk1 Ha HRa Hm1 Hred1];
                      match goal with Hk2 : ⟦ E ⟧ᵐ _ ⍮ _ ⍮ ρ0 ↘ k0 |- _ => pose proof (functional_eval_modexp _ _ _ _ Hk1 Hk2) as -> end;
                      exists a, i', Ra; repeat split; try assumption;
                      intros M0 HM0; destruct (Hred1 _ HM0) as [m r Hm2 Hr2 Hmr2]; exists m, r; repeat split; assumption)
                HRΓ _ Hρ _ Hk Hkk)
      as (a & i' & Ra & Ha & HRa & Hmt & Hred).
    apply mk_valid_mem_at with (vma_mod := k) (vma_typ := a) (vma_lvl := i') (vma_rel := Ra);
      [ exact Hk' | exact Ha | exact HRa | exact Hmt |].
    intros M Hom; destruct om' as [M' |]; cbn in Hom; [ injection Hom as <- | discriminate ].
    destruct (Hred _ eq_refl) as (m & r & Hm0 & Hr & Hmr).
    exact (mk_rel_mem_reduct _ _ _ _ _ m r Hm0 Hr Hmr).
  - (* a module expression equal to a valid unit *)
    intros Γ H R Rm K RK HwH HmH HmodH HHK HK IHK HmK HmodK x R' A Hm Ht.
    inversion Hm as [? ? ? ? ? _ _ | | | | ? ? ? R0 R0m Γy E rd R1 ? Hm0 Hmd He Hed Hr]; subst; [ cbn in Ht; discriminate |].
    pose proof (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm0 _ HmH) as ->.
    rewrite HmodH in Hmd; injection Hmd as <-.
    assert (HmKx : mdenote Θm Ξm Γ (me_mem K x) R') by (eapply dn_mem; [ exact HmK | exact HmodK | exact He | exact Hed | exact Hr ]).
    exact (valid_mem_transport _ _ _ _ _ _ HHK (IHK _ _ _ HmKx Ht)).
Qed.

End Fixed_GCtx.
