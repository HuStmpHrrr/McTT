(** * Units: the Closures of Related Units are Related

    A unit's closure is related to another's when their parameters, read
    outermost first, and their entries, read in order, are related.  A context
    PER of the units' extended contexts says exactly that: its parameter
    entries relate the parameter types, its definition entries the types and
    bodies, and its slot entries the closures of the nested units.  This file
    walks such a PER to produce the module PER of the closures. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases SubstitutionCases LetCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules Kinds KindsTyping KindsEval KindsPER.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Context PERs of Extended Contexts *)

Lemma per_ctx_env_app_tail : forall Ψ Ψ' Γ Γ' R,
    List.length Ψ = List.length Ψ' ->
    EF Ψ ++ Γ ≈ Ψ' ++ Γ' ∈ per_ctx_env ↘ R ->
    exists RΓ, EF Γ ≈ Γ' ∈ per_ctx_env ↘ RΓ.
Proof.
  induction Ψ as [| e Ψ IH]; intros [| e' Ψ'] * Hl H; cbn in *; try discriminate; eauto.
  inversion H; subst; eauto.
Qed.

(** The relation of an extension by a slot, with its tail relation fixed. *)
Lemma per_ctx_env_cons_mod_inversion : forall {Γ Γ' U U' RΓ R},
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ RΓ ->
    EF Γ ▹ₘ U ≈ Γ' ▹ₘ U' ∈ per_ctx_env ↘ R ->
    (forall ρ ρ', RΓ ρ ρ' -> per_dmod (dm_local ρ U nil) (dm_local ρ' U' nil)) /\
    (R <~> fun ρ ρ' =>
       RΓ ρ↯ ρ'↯ /\
       per_dmod (env_mod ρ 0) (dm_local ρ↯ U nil) /\
       per_dmod (env_mod ρ 0) (dm_local ρ↯ U' nil) /\
       per_dmod (env_mod ρ' 0) (dm_local ρ'↯ U nil) /\
       per_dmod (env_mod ρ' 0) (dm_local ρ'↯ U' nil)).
Proof.
  intros * HΓ H; inversion H; subst.
  match goal with Ht : per_ctx_env ?T Γ Γ' |- _ =>
    assert (HT : T <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption) end.
  split.
  - intros ρ ρ' Hρ; apply H6, HT, Hρ.
  - intros ρ ρ'; split; intros Hρ;
      [ apply H7 in Hρ as (Ht & ?); split; [ apply HT; assumption | assumption ]
      | apply H7; destruct Hρ as (Ht & ?); split; [ apply HT; assumption | assumption ] ].
Qed.

(** ** Walking Parameters

    A telescope of parameters is walked outermost first, so it is given as the
    reversed context.  At the end of the walk, the environments are related
    in the extended context's PER. *)

Lemma walk_params : forall ts ts' Γ Γ' RΓ R D D',
    tele_ass ts -> tele_ass ts' -> List.length ts = List.length ts' ->
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ RΓ ->
    EF rev ts ++ Γ ≈ rev ts' ++ Γ' ∈ per_ctx_env ↘ R ->
    (forall ρ ρ', R ρ ρ' -> per_mdef ρ D ρ' D') ->
    forall ρ ρ', RΓ ρ ρ' -> per_ltele ts ρ D ts' ρ' D' nil nil.
Proof.
  induction ts as [| e ts IH]; intros [| e' ts'] * Hts Hts' Hl HΓ HR HD ρ ρ' Hρ; cbn in Hl; try discriminate.
  - constructor; apply HD.
    assert (HRR : R <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    apply HRR, Hρ.
  - inversion Hts as [| ? ? [A ->] Hts0]; inversion Hts' as [| ? ? [A' ->] Hts0']; subst.
    cbn [rev] in HR; rewrite <- !app_assoc in HR; cbn [app] in HR.
    destruct (per_ctx_env_app_tail (rev ts) (rev ts') _ _ _ ltac:(rewrite !length_rev; congruence) HR)
      as [R1 HR1].
    destruct (per_ctx_env_cons_clean_inversion HΓ HR1) as (i & head_rel & Hhead & HE).
    eapply per_ltele_missing with (R := head_rel _ _ Hρ); [ apply Hhead |].
    intros c c' Hc.
    eapply IH; [ eassumption | eassumption | congruence | exact HR1 | exact HR | exact HD |].
    apply HE; exists Hρ; exact Hc.
Qed.

(** ** Walking Entries

    A body of definitions and submodules as evaluation reads it, against one
    as the context reads it: the same entries, the definitions with the same
    values, maybe at other types ([ematch]).  This is how the entries a local
    open generates are read: evaluation does not know their types. *)

Definition ematch_entry (Ee Et : gentry) : Prop :=
  match Ee, Et with
  | ge_def _ _ _ (Some M), ge_def _ _ _ (Some M') => M = M'
  | ge_mod _ U, ge_mod _ U' => U = U'
  | _, _ => False
  end.

Fixpoint ematch (Φe Φt : gmod) : Prop :=
  match Φt with
  | gm_nil => Φe = gm_nil
  | gm_ext Φt0 _ Et => exists Φe0 ye Ee, Φe = gm_ext Φe0 ye Ee /\ ematch Φe0 Φt0 /\ ematch_entry Ee Et
  | gm_open _ _ _ => False
  end.

Lemma walk_eval : forall Φt Φt' Φe Φe' Θl Θr RΘ R,
    ematch Φe Φt -> ematch Φe' Φt' ->
    EF Θl ≈ Θr ∈ per_ctx_env ↘ RΘ ->
    EF body_ctx Φt ++ Θl ≈ body_ctx Φt' ++ Θr ∈ per_ctx_env ↘ R ->
    forall ρ ρ', RΘ ρ ρ' ->
      exists ρ1 ρ1', ⟦ Φe ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 /\ ⟦ Φe' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ' ↘ ρ1' /\ R ρ1 ρ1'.
Proof.
  induction Φt as [| Φt IH yt Et | Φt IH Ht its]; intros [| Φt' yt' Et' | Φt' Ht' its'] * Hm Hm' HΘ HR ρ ρ' Hρ;
    cbn [ematch] in Hm, Hm'; try contradiction;
    pose proof (per_ctx_respects_length (ex_intro _ _ HR)) as L1;
    pose proof (per_ctx_respects_length (ex_intro _ _ HΘ)) as L2;
    rewrite !length_app, ?length_body_ctx in L1; cbn [gm_binders] in L1; try lia.
  - subst; assert (HRR : R <~> RΘ) by (eapply per_ctx_env_right_irrel; eassumption).
    exists ρ, ρ'; repeat split; try constructor; apply HRR, Hρ.
  - destruct Hm as (Φe0 & ye & Ee & -> & Hm & HEe), Hm' as (Φe0' & ye' & Ee' & -> & Hm' & HEe').
    destruct Ee as [? ? ? [M |] | pm Uy | ? ? ? | ? ? ? ?], Et as [bt pvt At [Mt |] | pmt Ut | ? ? ? | ? ? ? ?];
      cbn in HEe; try contradiction; subst;
      destruct Ee' as [? ? ? [M' |] | pm' Uy' | ? ? ? | ? ? ? ?], Et' as [bt' pvt' At' [Mt' |] | pmt' Ut' | ? ? ? | ? ? ? ?];
      cbn in HEe'; try contradiction; subst;
      cbn [body_ctx app] in HR; inversion HR; subst.
    + (* a definition *)
      match goal with
      | Htyp : forall ρ0 ρ'0 (e : tail_rel ρ0 ρ'0), rel_typ _ At _ At' _ _,
        Helem : forall ρ0 ρ'0 (e : tail_rel ρ0 ρ'0), rel_elem Mt _ Mt' _ _,
        HER : R <~> _ |- _ =>
          destruct (IH _ _ _ _ _ _ _ Hm Hm' HΘ equiv_Γ_Γ' _ _ Hρ) as (ρ1 & ρ1' & Hb1 & Hb1' & H1);
          assert (H11 : tail_rel ρ1 ρ1) by (etransitivity; [ exact H1 | symmetry; exact H1 ]);
          assert (H1'1' : tail_rel ρ1' ρ1') by (etransitivity; [ symmetry; exact H1 | exact H1 ]);
          destruct (Helem _ _ H1) as [m m' Hm1 Hm1' Hmm'];
          exists (ρ1 ↦ m), (ρ1' ↦ m'); repeat split; [ econstructor; eassumption | econstructor; eassumption |];
          apply HER; exists H1; cbn;
          pose proof (Htyp _ _ H11); pose proof (Htyp _ _ H1'1'); pose proof (Helem _ _ H11);
          pose proof (Helem _ _ H1'1'); pose proof (Htyp _ _ H1);
          solve_def_heads
      end.
    + (* a module *)
      match goal with
      | HU : forall ρ0 ρ'0, tail_rel ρ0 ρ'0 -> per_dmod _ _, HER : R <~> _ |- _ =>
          destruct (IH _ _ _ _ _ _ _ Hm Hm' HΘ equiv_Γ_Γ' _ _ Hρ) as (ρ1 & ρ1' & Hb1 & Hb1' & H1);
          assert (H11 : tail_rel ρ1 ρ1) by (etransitivity; [ exact H1 | symmetry; exact H1 ]);
          assert (H1'1' : tail_rel ρ1' ρ1') by (etransitivity; [ symmetry; exact H1 | exact H1 ]);
          exists (ρ1 ↦ᵐ dm_local ρ1 Ut nil), (ρ1' ↦ᵐ dm_local ρ1' Ut' nil);
          repeat split; [ econstructor; eassumption | econstructor; eassumption |];
          destruct (mod_closure_move _ _ _ _ _ _ H11 HU) as (M1 & M2 & _);
          destruct (mod_closure_move _ _ _ _ _ _ H1'1' HU) as (_ & _ & M3 & M4);
          apply HER; repeat split; cbn; assumption
      end.
Qed.

(** A generated item other than an inductive alias: what a local open
    generates. *)
Definition ig_local (g : igen) : Prop :=
  match g with
  | ig_ind_alias _ _ _ _ _ => False
  | _ => True
  end.

Lemma items_gen_local : forall Θ Ξ Γ H its gs,
    items_gen Θ Ξ None Γ H its gs -> Forall ig_local gs.
Proof. intros * Hg; remember None as io eqn:Eio; induction Hg; subst; try discriminate; constructor; cbn; auto. Qed.

Lemma ematch_gens : forall gs Φe Φt k, Forall ig_local gs -> ematch Φe Φt ->
    ematch (gens_append Φe k (List.map ig_erase gs)) (gens_append Φt k gs).
Proof.
  induction gs as [| g gs IH]; intros * Hl Hm; cbn [gens_append List.map]; [ exact Hm |].
  inversion Hl as [| ? ? Hg Hl']; subst.
  destruct g; cbn [ig_erase ig_entry gentry_wk] in *; try contradiction; (apply IH; [ exact Hl' |]);
    cbn [ematch]; do 3 eexists; (split; [ reflexivity | split; [ exact Hm | cbn; reflexivity ] ]).
Qed.

(** ** A Body and its Expansion Evaluate Alike

    Evaluation reads an open off the kinds of its target's members, which in
    an environment that matches the context are those typing gives
    ([member_kind]); the entries it then evaluates are the expansion's, but
    for their types, which evaluation does not read. *)

Lemma eval_entry_reloc : forall ρ Φ y E ρ',
    ⟦ gm_ext Φ y E ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' <->
    exists ρ1, ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 /\ ⟦ gm_ext gm_nil y E ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ1 ↘ ρ'.
Proof.
  intros; split.
  - intros He; inversion He; subst; eexists; split; try eassumption;
      first [ apply eval_benv_def; [ constructor | eassumption ] | apply eval_benv_mod; constructor ].
  - intros (ρ1 & H1 & H2); inversion H2; subst;
      match goal with Hn : ⟦ gm_nil ⟧ᵇ _ ⍮ _ ⍮ ρ1 ↘ ?r |- _ => inversion Hn; subst end; econstructor; eassumption.
Qed.

Lemma eval_gens_split : forall gs Φ k ρ ρ2,
    ⟦ gens_append Φ k gs ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ2 <->
    exists ρ1, ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 /\ ⟦ gens_append gm_nil k gs ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ1 ↘ ρ2.
Proof.
  induction gs as [| g gs IH]; intros; cbn [gens_append].
  - split; [ intros He; exists ρ2; split; [ exact He | constructor ] | intros (ρ1 & H1 & H2); inversion H2; subst; exact H1 ].
  - destruct (ig_entry g) as [d E]; rewrite IH.
    split.
    + intros (ρ1' & H1 & H2); apply eval_entry_reloc in H1 as (ρ1 & H1a & H1b).
      exists ρ1; split; [ exact H1a |]; apply IH; exists ρ1'; split; assumption.
    + intros (ρ1 & H1 & H2); apply IH in H2 as (ρm & Hm & H2); exists ρm; split; [| exact H2 ].
      apply eval_entry_reloc; exists ρ1; split; assumption.
Qed.

Lemma ematch_eval : forall Φt Φe ρ ρ', ematch Φe Φt ->
    ⟦ Φt ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' -> ⟦ Φe ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ'.
Proof.
  induction Φt as [| Φt IH y Et | Φt IH H its]; intros * Hm He; cbn [ematch] in Hm; try contradiction.
  - subst; exact He.
  - destruct Hm as (Φe0 & ye & Ee & -> & Hm & HEe).
    destruct Ee as [? ? ? [M |] | pm U | ? ? ? | ? ? ? ?], Et as [bt pvt At [Mt |] | pmt Ut | ? ? ? | ? ? ? ?];
      cbn in HEe; try contradiction; subst; inversion He; subst; econstructor; eauto.
Qed.

Lemma eval_benv_nopens_app : forall ρ Φ ρ', ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' -> gm_nopens Φ = 0 ->
    exists X, ρ' = X ++ ρ /\ List.length X = gm_binders Φ.
Proof.
  intros * Hev; induction Hev; intros Hn; cbn in Hn |- *; try discriminate.
  - exists nil; split; reflexivity.
  - destruct (IHHev Hn) as (X & -> & HX); exists (de_term m :: X); cbn; split; [ reflexivity | congruence ].
  - destruct (IHHev Hn) as (X & -> & HX); eexists (_ :: X); cbn; split; [ reflexivity | congruence ].
Qed.

Lemma kmatch_benv : forall Γ ρ Φ ρ', ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' -> gm_nopens Φ = 0 ->
    kmatch gc_deps gc_stack Γ ρ -> kmatch gc_deps gc_stack (body_ctx Φ ++ Γ) ρ'.
Proof.
  intros * He; induction He; intros Hn Hm; cbn [gm_nopens body_ctx app] in *; try discriminate.
  - exact Hm.
  - apply kmatch_cons_term; [ auto | discriminate ].
  - apply kmatch_cons_mod; [ auto | apply kequiv_refl ].
Qed.

Lemma eval_body_xp : forall Γ Φ Φx, body_xp gc_deps gc_stack Γ Φ Φx ->
    forall ρ ρ', kmatch gc_deps gc_stack Γ ρ -> ⟦ Φx ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' ->
    ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' /\ kmatch gc_deps gc_stack (body_ctx Φx ++ Γ) ρ'.
Proof.
  intros * Hx; induction Hx as [Γ | Γ Φ Φx x E Hx IH | Γ Φ Φx H its R T gs Hx IH HR HT Hg Hok]; intros ρ ρ' Hm He.
  - inversion He; subst; split; [ constructor | exact Hm ].
  - inversion He; subst;
      match goal with H1 : ⟦ Φx ⟧ᵇ _ ⍮ _ ⍮ ρ ↘ ?r |- _ => destruct (IH _ _ Hm H1) as [Hb Hm1] end.
    + split; [ econstructor; eassumption |]; cbn [body_ctx app]; apply kmatch_cons_term; [ exact Hm1 | discriminate ].
    + split; [ econstructor; eassumption |]; cbn [body_ctx app]; apply kmatch_cons_mod; [ exact Hm1 | apply kequiv_refl ].
  - apply eval_gens_split in He as (ρ1 & H1 & H2).
    destruct (IH _ _ Hm H1) as [Hb Hm1].
    pose proof (proj2 (proj2 (proj2 (member_kind _ _))) _ _ _ _ _ Hg eq_refl _ Hm1) as Hk.
    split.
    + econstructor; [ exact Hb | exact Hk |].
      exact (ematch_eval _ _ _ _ (ematch_gens gs gm_nil gm_nil 0 (items_gen_local _ _ _ _ _ _ Hg) eq_refl) H2).
    + rewrite gens_body_ctx_base, <- app_assoc.
      apply (kmatch_benv _ _ _ _ H2); [ rewrite gens_append_nopens; reflexivity | exact Hm1 ].
Qed.

Lemma ematch_eval_rev : forall Φt Φe ρ ρ', ematch Φe Φt ->
    ⟦ Φe ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' -> ⟦ Φt ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ'.
Proof.
  induction Φt as [| Φt IH y Et | Φt IH H its]; intros * Hm He; cbn [ematch] in Hm; try contradiction.
  - subst; exact He.
  - destruct Hm as (Φe0 & ye & Ee & -> & Hm & HEe).
    destruct Ee as [? ? ? [M |] | pm U | ? ? ? | ? ? ? ?], Et as [bt pvt At [Mt |] | pmt Ut | ? ? ? | ? ? ? ?];
      cbn in HEe; try contradiction; subst; inversion He; subst; econstructor; eauto.
Qed.

(** Conversely, a body evaluates as its expansion does. *)
Lemma eval_body_xp_rev : forall Γ Φ Φx, body_xp gc_deps gc_stack Γ Φ Φx ->
    forall ρ ρ', kmatch gc_deps gc_stack Γ ρ -> ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' ->
    ⟦ Φx ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ'.
Proof.
  intros * Hx; induction Hx as [Γ | Γ Φ Φx x E Hx IH | Γ Φ Φx H its R T gs Hx IH HR HT Hg Hok]; intros ρ ρ' Hm He.
  - exact He.
  - inversion He; subst; econstructor; eauto.
  - inversion He; subst.
    match goal with
    | H1 : ⟦ Φ ⟧ᵇ _ ⍮ _ ⍮ ρ ↘ ?r1, Hk0 : kgens _ _ _ _ _ _, H3 : ⟦ gens_append gm_nil 0 _ ⟧ᵇ _ ⍮ _ ⍮ _ ↘ _ |- _ =>
        rename r1 into ρ1, Hk0 into Hk, H3 into H2; pose proof (IH _ _ Hm H1) as H1x
    end.
    destruct (eval_body_xp _ _ _ Hx _ _ Hm H1x) as [_ Hm1].
    pose proof (proj2 (proj2 (proj2 (member_kind _ _))) _ _ _ _ _ Hg eq_refl _ Hm1) as Hk'.
    rewrite (functional_kgens _ _ _ _ _ Hk Hk') in H2.
    apply eval_gens_split; exists ρ1; split; [ exact H1x |].
    exact (ematch_eval_rev _ _ _ _ (ematch_gens gs gm_nil gm_nil 0 (items_gen_local _ _ _ _ _ _ Hg) eq_refl) H2).
Qed.

(** An entry of an expansion: an entry of the body, or one an open of the
    body generates. *)
Lemma xp_prefix : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx ->
    forall x Φ' E, gm_prefix_upto Φx x = Some (gm_ext Φ' x E) ->
    (exists Φr, gm_prefix_upto Φ x = Some (gm_ext Φr x E) /\ body_xp Θ Ξ Γ Φr Φ') \/
    (exists Φ0 Φx0 H its1 it its0 gs0 g T k,
        gm_item_upto Φ x = Some (Φ0, H, its1, it) /\ body_xp Θ Ξ Γ Φ0 Φx0 /\
        (exists R, member_type Θ Ξ (body_ctx Φx0 ++ Γ) H nil R /\ mres_tl R = Some T) /\
        items_gen Θ Ξ None (body_ctx Φx0 ++ Γ) H its0 gs0 /\
        items_gen Θ Ξ None (body_ctx Φx0 ++ Γ) H (it :: nil) (g :: nil) /\
        its1 = its0 ++ it :: nil /\ Φ' = gens_append Φx0 0 gs0 /\
        E = gentry_wk (snd (ig_entry g)) (wk_shiftn (List.length gs0)) /\
        nth_error (body_opens Φ Φx) k = Some (body_ctx Φx0, H)).
Proof.
  intros * Hx; induction Hx as [Γ | Γ Φ Φx y E Hx IH | Γ Φ Φx H its R T gs Hx IH HR HT Hg Hok]; intros x Φ' E' Hp.
  - discriminate Hp.
  - cbn [gm_prefix_upto] in Hp |- *; cbn [gm_item_upto body_opens gm_dropn].
    destruct (String.eqb x y) eqn:Ey.
    + injection Hp as -> -> ->; apply String.eqb_eq in Ey; subst.
      left; exists Φ; split; [ reflexivity | exact Hx ].
    + destruct (IH _ _ _ Hp) as [(Φr & Hr & Hxr) | (Φ0 & Φx0 & H & its1 & it & its0 & gs0 & g & T & k & Hi & Rx)].
      * left; exists Φr; split; [ exact Hr | exact Hxr ].
      * right; exists Φ0, Φx0, H, its1, it, its0, gs0, g, T, k; split; [ exact Hi | exact Rx ].
  - cbn [gm_prefix_upto gm_item_upto body_opens].
    pose proof (items_gen_length _ _ _ _ _ _ _ Hg) as Hl.
    assert (E1 : gm_dropn (List.length its) (gens_append Φx 0 gs) = Φx) by (rewrite <- Hl; apply gm_dropn_gens_append).
    rewrite E1.
    destruct (items_upto x its) as [[its1 it] |] eqn:Eu.
    + destruct (gens_prefix_some _ _ _ _ _ _ _ Hg _ _ _ Eu) as (its0 & gs0 & g & -> & Hg0 & Hg1 & _ & Hgp).
      rewrite Hgp, gens_append_snoc in Hp; injection Hp as <- Hn HE.
      right; exists Φ, Φx, H, (its0 ++ it :: nil), it, its0, gs0, g, T, 0.
      repeat split; try assumption; try reflexivity; try (eexists; split; eassumption).
      cbn; rewrite <- HE; reflexivity.
    + pose proof (items_upto_none_iff _ _ Eu) as Hn.
      assert (HnG : existsb (String.eqb x) (map ig_name gs) = false) by (rewrite (items_gen_names _ _ _ _ _ _ _ Hg); exact Hn).
      rewrite gens_prefix_none in Hp by exact HnG.
      rewrite Hn.
      destruct (IH _ _ _ Hp) as [(Φr & Hr & Hxr) | (Φ0 & Φx0 & H0 & its1 & it & its0 & gs0 & g & T0 & k & Hi & Rx)].
      * left; exists Φr; split; [ exact Hr | exact Hxr ].
      * right; exists Φ0, Φx0, H0, its1, it, its0, gs0, g, T0, (S k); split; [ exact Hi |].
        destruct Rx as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8); repeat split; assumption.
Qed.

(** A valid module expression, at environments a context PER relates. *)
Lemma rel_modexp_at : forall Γ Γ' H H' R,
    Γ ⊨ᵐ H ≈ H' -> EF Γ ≈ Γ' ∈ per_ctx_env ↘ R ->
    forall ρ ρ', R ρ ρ' ->
      exists h h', ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h /\ ⟦ H' ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ' ↘ h' /\ per_dmod h h'.
Proof.
  intros * [RE [HΓE HEg]] HR ρ ρ' Hρ.
  assert (Ex : R <~> RE) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (HEg _ _ HΓE _ _ (rel_sub_id (ex_intro _ _ HΓE)) _ _ _ _ (proj1 (Ex _ _) Hρ) (eval_sub_id _) (eval_sub_id _))
    as [h1 h2 h3 h4 _ Hh2 Hh3 _ [_ [Hh _]]].
  exists h2, h3; repeat split; assumption.
Qed.

(** ** Walking a Body

    Each entry is read in the environment its predecessors make; a local
    open, as the entries it generates, whose kinds evaluation reads off the
    target ([member_kind]).  The environments the body makes are related in
    the PER of the context it extends, read as its expansion. *)

Lemma walk_body : forall Φ Φ' Θc Θc' Φx Φx' RΘ R,
    ⊢g gc_deps ⍮ gc_stack ->
    body_xp gc_deps gc_stack Θc Φ Φx -> body_xp gc_deps gc_stack Θc' Φ' Φx' ->
    body_shape Φ Φ' ->
    EF Θc ≈ Θc' ∈ per_ctx_env ↘ RΘ ->
    EF body_ctx Φx ++ Θc ≈ body_ctx Φx' ++ Θc' ∈ per_ctx_env ↘ R ->
    (forall k Ψ H Ψ' H', nth_error (body_opens Φ Φx) k = Some (Ψ, H) ->
       nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> Ψ ++ Θc ⊨ᵐ H ≈ H') ->
    forall ρ ρ', RΘ ρ ρ' ->
      per_body ρ Φ ρ' Φ' /\
      exists ρ1 ρ1', ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 /\ ⟦ Φ' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ' ↘ ρ1' /\ R ρ1 ρ1'.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros [| Φ' y' E' | Φ' H' its'] * Hg Hx Hx' Hs HΘ HR Ho ρ ρ' Hρ;
    cbn in Hs; try contradiction.
  - inversion Hx; inversion Hx'; subst.
    assert (HRR : R <~> RΘ) by (eapply per_ctx_env_right_irrel; eassumption).
    split; [ constructor |]; exists ρ, ρ'; repeat split; try constructor; apply HRR, Hρ.
  - destruct Hs as (Hs & <- & HE).
    inversion Hx as [| ? ? Φx0 ? ? Hx0 |]; subst; inversion Hx' as [| ? ? Φx0' ? ? Hx0' |]; subst.
    cbn [body_opens gm_dropn] in Ho.
    destruct E as [b pv A [M |] | pm Uy | pv D Φd | ? ? ? ?], E' as [b' pv' A' [M' |] | pm' Uy' | pv' D' Φd' | ? ? ? ?]; cbn in HE; try contradiction.
    + (* a definition *)
      cbn [body_ctx app] in HR.
      inversion HR; subst.
      match goal with
      | Htyp : forall ρ0 ρ'0 (e : tail_rel ρ0 ρ'0), rel_typ _ A _ A' _ _,
        Helem : forall ρ0 ρ'0 (e : tail_rel ρ0 ρ'0), rel_elem M _ M' _ _,
        HER : R <~> _ |- _ =>
          destruct (IH _ _ _ _ _ _ _ Hg Hx0 Hx0' Hs HΘ equiv_Γ_Γ' Ho _ _ Hρ) as (Hb & ρ1 & ρ1' & Hb1 & Hb1' & H1);
          assert (H11 : tail_rel ρ1 ρ1) by (etransitivity; [ exact H1 | symmetry; exact H1 ]);
          assert (H1'1' : tail_rel ρ1' ρ1') by (etransitivity; [ symmetry; exact H1 | exact H1 ]);
          split;
          [ eapply per_body_def; [ exact Hb | exact Hb1 | exact Hb1' | apply (Htyp _ _ H1) | apply (Helem _ _ H1) ]
          | destruct (Helem _ _ H1) as [m m' Hm Hm' Hmm'];
            exists (ρ1 ↦ m), (ρ1' ↦ m'); repeat split; [ econstructor; eassumption | econstructor; eassumption |];
            apply HER; exists H1; cbn;
            pose proof (Htyp _ _ H11); pose proof (Htyp _ _ H1'1'); pose proof (Helem _ _ H11);
            pose proof (Helem _ _ H1'1'); pose proof (Htyp _ _ H1);
            solve_def_heads ]
      end.
    + (* a module *)
      cbn [body_ctx app] in HR.
      inversion HR; subst.
      match goal with
      | HU : forall ρ0 ρ'0, tail_rel ρ0 ρ'0 -> per_dmod _ _, HER : R <~> _ |- _ =>
          destruct (IH _ _ _ _ _ _ _ Hg Hx0 Hx0' Hs HΘ equiv_Γ_Γ' Ho _ _ Hρ) as (Hb & ρ1 & ρ1' & Hb1 & Hb1' & H1);
          assert (H11 : tail_rel ρ1 ρ1) by (etransitivity; [ exact H1 | symmetry; exact H1 ]);
          assert (H1'1' : tail_rel ρ1' ρ1') by (etransitivity; [ symmetry; exact H1 | exact H1 ]);
          split;
          [ eapply per_body_mod; [ exact Hb | exact Hb1 | exact Hb1' | apply HU, H1 ]
          | exists (ρ1 ↦ᵐ dm_local ρ1 Uy nil), (ρ1' ↦ᵐ dm_local ρ1' Uy' nil);
            repeat split; [ econstructor; eassumption | econstructor; eassumption |];
            destruct (mod_closure_move _ _ _ _ _ _ H11 HU) as (M1 & M2 & _);
            destruct (mod_closure_move _ _ _ _ _ _ H1'1' HU) as (_ & _ & M3 & M4);
            apply HER; repeat split; cbn; assumption ]
      end.
  - (* a local open *)
    destruct Hs as (Hs & <-).
    inversion Hx as [| | ? ? Φx0 ? ? Rm T gs Hx0 HRm HT Hgs Hok ]; subst;
      inversion Hx' as [| | ? ? Φx0' ? ? Rm' T' gs' Hx0' HRm' HT' Hgs' Hok' ]; subst.
    pose proof (items_gen_length _ _ _ _ _ _ _ Hgs) as Hl.
    pose proof (items_gen_length _ _ _ _ _ _ _ Hgs') as Hl'.
    cbn [body_opens] in Ho.
    assert (E1 : gm_dropn (List.length its) (gens_append Φx0 0 gs) = Φx0) by (rewrite <- Hl; apply gm_dropn_gens_append).
    assert (E2 : gm_dropn (List.length its) (gens_append Φx0' 0 gs') = Φx0') by (rewrite <- Hl'; apply gm_dropn_gens_append).
    rewrite E1, E2 in Ho.
    rewrite gens_body_ctx_base, (gens_body_ctx_base gs'), <- !app_assoc in HR.
    assert (Lg : List.length (body_ctx (gens_append gm_nil 0 gs)) = List.length (body_ctx (gens_append gm_nil 0 gs')))
      by (rewrite !gens_body_ctx_length; congruence).
    destruct (per_ctx_env_app_tail _ _ _ _ _ Lg HR) as [R1 HR1].
    destruct (IH _ _ _ _ _ _ _ Hg Hx0 Hx0' Hs HΘ HR1 (fun k => Ho (S k)) _ _ Hρ) as (Hb & ρ1 & ρ1' & Hb1 & Hb1' & H1).
    destruct (rel_modexp_at _ _ _ _ _ (Ho 0 _ _ _ _ eq_refl eq_refl) HR1 _ _ H1) as (h & h' & Hh & Hh' & Hhh).
    destruct (per_ctx_env_kmatch Hg _ _ _ HR1 _ _ H1) as [K1 K1'].
    pose proof (proj2 (proj2 (proj2 (member_kind _ _))) _ _ _ _ _ Hgs eq_refl _ K1) as Hk.
    pose proof (proj2 (proj2 (proj2 (member_kind _ _))) _ _ _ _ _ Hgs' eq_refl _ K1') as Hk'.
    destruct (walk_eval (gens_append gm_nil 0 gs) (gens_append gm_nil 0 gs')
                        (gens_append gm_nil 0 (List.map ig_erase gs)) (gens_append gm_nil 0 (List.map ig_erase gs')) _ _ _ _
                        (ematch_gens gs gm_nil gm_nil 0 (items_gen_local _ _ _ _ _ _ Hgs) eq_refl)
                        (ematch_gens gs' gm_nil gm_nil 0 (items_gen_local _ _ _ _ _ _ Hgs') eq_refl)
                        HR1 HR _ _ H1) as (ρ2 & ρ2' & Hb2 & Hb2' & H2).
    split; [ eapply per_body_open; eassumption |].
    exists ρ2, ρ2'; repeat split; [ econstructor; eassumption | econstructor; eassumption | exact H2 ].
Qed.

(** ** Related Closures *)

Lemma rel_closure_body : forall Γ Γ' Δ Δ' Φ Φ' Φx Φx' RΓ R,
    ⊢g gc_deps ⍮ gc_stack ->
    tele_ass Δ -> tele_ass Δ' -> List.length Δ = List.length Δ' ->
    body_xp gc_deps gc_stack (Δ ++ Γ) Φ Φx -> body_xp gc_deps gc_stack (Δ' ++ Γ') Φ' Φx' ->
    body_shape Φ Φ' -> body_shape Φx Φx' ->
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ RΓ ->
    EF body_ctx Φx ++ Δ ++ Γ ≈ body_ctx Φx' ++ Δ' ++ Γ' ∈ per_ctx_env ↘ R ->
    (forall k Ψ H Ψ' H', nth_error (body_opens Φ Φx) k = Some (Ψ, H) ->
       nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> Ψ ++ Δ ++ Γ ⊨ᵐ H ≈ H') ->
    forall ρ ρ', RΓ ρ ρ' -> per_dmod (dm_local ρ (gu_body Δ Φ) nil) (dm_local ρ' (gu_body Δ' Φ') nil).
Proof.
  intros * Hg HΔ HΔ' Hl Hx Hx' Hs Hsx HΓ HR Ho ρ ρ' Hρ.
  destruct (per_ctx_env_app_tail (body_ctx Φx) (body_ctx Φx') _ _ _ ltac:(rewrite !length_body_ctx; apply body_shape_binders; exact Hsx) HR)
    as [RΔ HRΔ].
  constructor; cbn [gu_params gu_def].
  eapply walk_params; [ apply Forall_rev; exact HΔ | apply Forall_rev; exact HΔ' | rewrite !length_rev; exact Hl
                      | exact HΓ | rewrite !rev_involutive; exact HRΔ | | exact Hρ ].
  intros ρ1 ρ1' Hρ1; constructor.
  exact (proj1 (walk_body _ _ _ _ _ _ _ _ Hg Hx Hx' Hs HRΔ HR Ho _ _ Hρ1)).
Qed.

Lemma rel_closure_alias : forall Γ Γ' Δ Δ' E E' RΓ R,
    tele_ass Δ -> tele_ass Δ' -> List.length Δ = List.length Δ' ->
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ RΓ ->
    EF Δ ++ Γ ≈ Δ' ++ Γ' ∈ per_ctx_env ↘ R ->
    (forall ρ ρ', R ρ ρ' -> exists h h', ⟦ E ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h /\
                                     ⟦ E' ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ' ↘ h' /\ per_dmod h h') ->
    forall ρ ρ', RΓ ρ ρ' ->
      per_dmod (dm_local ρ (gu_mk Δ (md_alias E)) nil) (dm_local ρ' (gu_mk Δ' (md_alias E')) nil).
Proof.
  intros * HΔ HΔ' Hl HΓ HR HE ρ ρ' Hρ.
  constructor; cbn [gu_params gu_def].
  eapply walk_params; [ apply Forall_rev; exact HΔ | apply Forall_rev; exact HΔ' | rewrite !length_rev; exact Hl
                      | exact HΓ | rewrite !rev_involutive; exact HR | | exact Hρ ].
  intros ρ1 ρ1' Hρ1; destruct (HE _ _ Hρ1) as (h & h' & ? & ? & ?); econstructor; eassumption.
Qed.

(** ** Slots

    The context PER of a slot, its semantic substitutions, and what the
    validity of a unit says of its closures. *)

Definition env_ext_mod (U U' : gunit) (R : relation env) : relation env :=
  fun ρ ρ' =>
    R ρ↯ ρ'↯ /\
    per_dmod (env_mod ρ 0) (dm_local ρ↯ U nil) /\
    per_dmod (env_mod ρ 0) (dm_local ρ↯ U' nil) /\
    per_dmod (env_mod ρ' 0) (dm_local ρ'↯ U nil) /\
    per_dmod (env_mod ρ' 0) (dm_local ρ'↯ U' nil).

(** The closures of a valid unit, along a substitution. *)
Lemma unit_chain : forall {Γ U U'},
    Γ ⊨ᵐ me_lit U ≈ me_lit U' ->
    exists R (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ R),
    forall Γ' R' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R') σ σ',
      Γ' ⊨s σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        R' ρ ρ' -> ⟦ σ ⟧s ρ ↘ ρσ -> ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        rel_chain per_dmod ([dm_local ρ U[σ]ᵘ nil; dm_local ρσ U nil; dm_local ρ'σ' U' nil; dm_local ρ' U'[σ']ᵘ nil]).
Proof.
  intros * [R [HΓ HU]]; exists R, HΓ; intros * HΓ' * Hσ * Hρ Hev Hev'.
  destruct (HU _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [h1 h2 h3 h4 H1 H2 H3 H4 Hc].
  cbn [modexp_sub] in H1, H4.
  inversion H1; inversion H2; inversion H3; inversion H4; subst; exact Hc.
Qed.

Lemma unit_chain_at : forall {Γ U U' R},
    Γ ⊨ᵐ me_lit U ≈ me_lit U' ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    forall ρ ρ', R ρ ρ' -> per_dmod (dm_local ρ U nil) (dm_local ρ' U' nil).
Proof.
  intros * HU HΓ ρ ρ' Hρ.
  destruct (unit_chain HU) as [R0 [HΓ0 Hc]].
  assert (E : R <~> R0) by (eapply per_ctx_env_right_irrel; eassumption).
  pose proof (Hc _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hρ (eval_sub_id _) (eval_sub_id _)) as Hch.
  destruct Hch as (_ & H & _); exact H.
Qed.

Lemma per_ctx_env_of_mod : forall {Γ U U' R},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U' ->
    EF Γ ▹ₘ U ≈ Γ ▹ₘ U' ∈ per_ctx_env ↘ env_ext_mod U U' R.
Proof.
  intros * HΓ HU.
  eapply per_ctx_env_cons_mod; [ exact HΓ | eapply per_env_PER; exact HΓ | | reflexivity ].
  intros; eapply unit_chain_at; eassumption.
Qed.

Lemma per_ctx_env_of_mod_sub : forall {Γ' Γ σ σ' U R'},
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' ->
    Γ' ⊨s σ ≈ σ' : Γ ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    EF Γ' ▹ₘ U[σ]ᵘ ≈ Γ' ▹ₘ U[σ]ᵘ ∈ per_ctx_env ↘ env_ext_mod U[σ]ᵘ U[σ]ᵘ R'.
Proof.
  intros * HΓ' Hσ HU.
  eapply per_ctx_env_cons_mod; [ exact HΓ' | eapply per_env_PER; exact HΓ' | | reflexivity ].
  intros ρ ρ' Hρ.
  pose proof (rel_sub_under_ctx_refl_left Hσ) as Hσσ.
  destruct (rel_sub_under_ctx_simple Hσσ) as [R1 [HΓ1 [RΓ [HΓ0 Hs]]]].
  assert (E : R' <~> R1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E _ _) Hρ)) as (ρσ & ρ'σ & Hev & Hev' & _).
  destruct (unit_chain HU) as [R0 [HΓ00 Hc]].
  pose proof (Hc _ _ HΓ' _ _ Hσσ _ _ _ _ Hρ Hev Hev') as Hch.
  assert (PER per_dmod) by typeclasses eauto.
  pairwise.
Qed.

(** [q σ] into a slot.  The four tails come from [σ] at the Kripke stage, as
    for an assumption; the head is the same module value on each side, tied to
    the closures of [U[σ]] over the stage's tails, which the validity of [U]
    relates to the closures of [U] over the tails of [q σ]. *)
Lemma rel_sub_under_ctx_q_mod : forall {Γ' Γ σ σ' U},
    Γ' ⊨s σ ≈ σ' : Γ ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    Γ' ▹ₘ U[σ]ᵘ ⊨s q σ ≈ q σ' : Γ ▹ₘ U.
Proof.
  intros * Hσj HU.
  pose proof Hσj as [R' [HΓ' [R [HΓ Hσ]]]].
  pose proof (per_ctx_env_of_mod_sub HΓ' Hσj HU) as HΓ'U.
  pose proof (per_ctx_env_of_mod HΓ HU) as HΓU.
  pose proof (rel_wk_shift HΓ' HΓ'U) as Hshift.
  pose proof (rel_sub_under_ctx_wk Hσj (rel_wk_under_ctx_intro HΓ'U HΓ' Hshift)) as Hσwkj.
  pose proof Hσwkj as [R'U [HΓ'U' [R2 [HΓ2 Hσwk]]]].
  assert (E1 : R'U <~> env_ext_mod U[σ]ᵘ U[σ]ᵘ R') by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E2 : R2 <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (HPR : PER R) by (eapply per_env_PER; exact HΓ).
  assert (HPR' : PER R') by (eapply per_env_PER; exact HΓ').
  destruct (unit_chain HU) as [R0 [HΓ0 Hch]].
  exists (env_ext_mod U[σ]ᵘ U[σ]ᵘ R'), HΓ'U, (env_ext_mod U U R), HΓU.
  intros Γ'' R'' HΓ'' ψ Hψ ρ ρ' Hρ.
  destruct (Hψ _ _ Hρ) as (Htail & Tρ & _ & Tρ' & _).
  destruct (Hσwk _ _ HΓ'' _ (proj2 (rel_wk_morphism ψ _ _ (reflexivity R'') _ _ E1) Hψ) _ _ Hρ)
    as [x1 y1 y4 x4 Hx1 Hy1 Hy4 Hx4 Htails].
  apply (rel_chain_mono _ _ (fun a b H => proj1 (E2 a b) H)) in Htails.
  destruct (Hσ _ _ HΓ'U _ Hshift _ _ (Hψ _ _ Hρ)) as [z1 y2 y3 z4 Hz1 Hy2 Hy3 Hz4 Hbtails].
  rewrite ?eval_wk_shift in *.
  assert (Heq1 : env_eq y1 z1) by (eapply functional_eval_sub; eassumption).
  assert (Heq4 : env_eq y4 z4) by (eapply functional_eval_sub; eassumption).
  assert (Hy12 : R y1 y2) by (rewrite Heq1; pairwise).
  assert (Hy43 : R y4 y3) by (rewrite Heq4; pairwise).
  (** The closures of [U[σ]] over the stage's tails, against those of [U]. *)
  assert (Htl : R' (⟪ψ⟫ ρ)↯ (⟪ψ⟫ ρ)↯) by (etransitivity; [ exact Htail | symmetry; exact Htail ]).
  assert (Htr : R' (⟪ψ⟫ ρ')↯ (⟪ψ⟫ ρ')↯) by (etransitivity; [ symmetry; exact Htail | exact Htail ]).
  pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
  pose proof (Hch _ _ HΓ' _ _ Hσσ _ _ _ _ Htl Hy2 Hy2) as C1.
  destruct (rel_sub_under_ctx_simple Hσσ) as [R1 [HΓ1 [R3 [HΓ3 Hs]]]].
  assert (E3 : R' <~> R1) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E4 : R3 <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E3 _ _) Htr)) as (w & _ & Hw & _ & _).
  pose proof (Hch _ _ HΓ' _ _ Hσσ _ _ _ _ Htr Hw Hw) as C2.
  assert (Hw3 : R w y3) by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  assert (Hm : forall t, R t y2 -> per_dmod (env_mod ρ (ψ 0)) (dm_local t U nil)).
  { intros t Ht; rewrite <- (eval_wk_app_mod ψ).
    eapply per_dmod_trans; [ exact Tρ |].
    eapply per_dmod_trans; [ destruct C1 as (C & _); exact C |].
    destruct (mod_closure_move _ _ _ _ _ HPR (symmetry Ht) (unit_chain_at HU HΓ)) as (M & _); exact M. }
  assert (Hm' : forall t, R t w -> per_dmod (env_mod ρ' (ψ 0)) (dm_local t U nil)).
  { intros t Ht; rewrite <- (eval_wk_app_mod ψ).
    eapply per_dmod_trans; [ exact Tρ' |].
    eapply per_dmod_trans; [ destruct C2 as (C & _); exact C |].
    destruct (mod_closure_move _ _ _ _ _ HPR (symmetry Ht) (unit_chain_at HU HΓ)) as (M & _); exact M. }
  assert (Hl : forall t, In t (x1 :: y1 :: nil) -> R t y2)
    by (intros t Ht; etransitivity; [| exact Hy12 ]; eapply (rel_chain_pairwise R); [ exact Htails | | solve_in ];
        destruct Ht as [<- | [<- | []]]; solve_in).
  assert (Hr : forall t, In t (y4 :: x4 :: nil) -> R t w).
  { intros t Ht; etransitivity; [| symmetry; exact Hw3 ]; etransitivity; [| exact Hy43 ].
    eapply (rel_chain_pairwise R); [ exact Htails | | solve_in ].
    destruct Ht as [<- | [<- | []]]; solve_in. }
  apply (mk_rel_sub (env_entry ρ (ψ 0) :: x1) (env_entry ρ (ψ 0) :: y1)
                    (env_entry ρ' (ψ 0) :: y4) (env_entry ρ' (ψ 0) :: x4));
    [ apply eval_sub_wk_q; eassumption
    | rewrite <- (eval_wk_app_entry ψ); apply eval_sub_q; eassumption
    | rewrite <- (eval_wk_app_entry ψ); apply eval_sub_q; eassumption
    | apply eval_sub_wk_q; eassumption
    | ].
  cbn [rel_chain]; unfold env_ext_mod; cbn [drop_env tl].
  unfold env_mod in Hm, Hm' |- *; cbn [env_entry hd] in Hm, Hm' |- *.
  repeat split.
  all: try solve [ eapply (rel_chain_pairwise R); [ exact Htails | solve_in | solve_in ]
          | apply Hm, Hl; solve_in | apply Hm', Hr; solve_in ].
Qed.

(** ** Walking a Unit and its Substitute

    A unit [U] of [Γ] and its substitute [U[σ]] of [Γ'] are walked together,
    entry by entry: the substitute's entries are read in an environment [ρl]
    of [Γ'] extended by its entries, the unit's in an environment [ρr] of [Γ]
    extended by its own.  The invariant is that [σ], lifted over the entries
    so far, takes [ρl] to an environment related to [ρr]. *)

Definition hw_inv (Γ' Γ : ctx) (σ : sub) (Ψ : ctx) (ρl ρr : env) : Prop :=
  exists Rl Rr (_ : EF tele_sub Ψ σ ++ Γ' ≈ tele_sub Ψ σ ++ Γ' ∈ per_ctx_env ↘ Rl)
    (_ : EF Ψ ++ Γ ≈ Ψ ++ Γ ∈ per_ctx_env ↘ Rr),
    (tele_sub Ψ σ ++ Γ') ⊨s sb_qn (List.length Ψ) σ ≈ sb_qn (List.length Ψ) σ : Ψ ++ Γ /\
    Rl ρl ρl /\ exists ρm, ⟦ sb_qn (List.length Ψ) σ ⟧s ρl ↘ ρm /\ Rr ρm ρr.

Lemma hw_init : forall Γ' Γ σ σ' R' R ρ ρσ,
    Γ' ⊨s σ ≈ σ' : Γ ->
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    R' ρ ρ -> ⟦ σ ⟧s ρ ↘ ρσ ->
    hw_inv Γ' Γ σ nil ρ ρσ.
Proof.
  intros * Hσ HΓ' HΓ Hρ Hev.
  pose proof (rel_sub_under_ctx_refl_left Hσ) as Hσσ.
  exists R', R, HΓ', HΓ; cbn; split; [ exact Hσσ | split; [ exact Hρ |] ].
  exists ρσ; split; [ exact Hev |].
  assert (Hr : R ρσ ρσ) by (eapply (rel_sub_under_ctx_at' Hσσ HΓ' HΓ); eassumption).
  exact Hr.
Qed.

(** The two values of an assumption's type are related, and so are the
    extended environments, at any related pair of values. *)
Lemma hw_ass : forall Γ' Γ σ Ψ A i ρl ρr,
    hw_inv Γ' Γ σ Ψ ρl ρr ->
    Ψ ++ Γ ⊨ A : Typeω@i ->
    exists R, PER.Definitions.rel_typ i A[sb_qn (List.length Ψ) σ] ρl A ρr R /\
      forall c c', R c c' -> hw_inv Γ' Γ σ (Ψ ▹ A) (ρl ↦ c) (ρr ↦ c').
Proof.
  intros * (Rl & Rr & HΓl & HΓr & Hsub & Hl & ρm & Hm & Hmr) HA.
  set (τ := sb_qn (List.length Ψ) σ) in *.
  pose proof (rel_exp_of_typ_inversion HA) as [R0 [HΓ0 HAgen]].
  assert (HPl : PER Rl) by (eapply per_env_PER; exact HΓl).
  assert (HPr : PER Rr) by (eapply per_env_PER; exact HΓr).
  destruct (HAgen _ _ HΓl _ _ Hsub _ _ _ _ Hl Hm Hm) as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hc1].
  destruct (HAgen _ _ HΓr _ _ (rel_sub_id (ex_intro _ _ HΓr)) _ _ _ _ Hmr (eval_sub_id _) (eval_sub_id _))
    as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hc2].
  rewrite exp_sub_id in Hb1, Hb4.
  functional_eval_rewrite_clear.
  assert (H14 : Dom a1 ≈ b3 ∈ per_univ i)
    by (destruct Hc1 as [H12 _]; destruct Hc2 as [_ [H23 _]]; etransitivity; eassumption).
  destruct H14 as [R HR].
  destruct Hc2 as [_ [[R2 HR2] _]].
  exists R; split; [ econstructor; eassumption |].
  intros c c' Hcc'.
  assert (HRP : PER R) by (eapply per_elem_PER; eassumption).
  assert (Hcc : R c c) by (etransitivity; [ exact Hcc' | symmetry; exact Hcc' ]).
  pose proof (per_ctx_env_of_typ_sub HΓl Hsub HA) as HΓl'.
  pose proof (per_ctx_env_of_typ HΓr HA) as HΓr'.
  assert (Hl' : per_env_extend A[τ] A[τ] Rl (ρl ↦ c) (ρl ↦ c))
    by (eapply (per_env_extend_sub_intro HΓl Hsub HA); eassumption).
  destruct (rel_sub_under_ctx_q_at HΓl HΓr' Hsub HA _ _ _ _ _ _ Hl' Hm Hm) as [s [s' [Hs [_ Hch]]]].
  assert (Hmr' : per_env_extend A A Rr (ρm ↦ c) (ρr ↦ c')).
  { apply per_env_extend_intro'; [ exact Hmr |].
    eapply per_head_of; [ exact Ha2 | exact Hb3 | exact HR2 |].
    eapply (per_univ_elem_left_irrel _ _ _ _ _ _ _ HR HR2); exact Hcc'. }
  exists (per_env_extend A[τ] A[τ] Rl), (per_env_extend A A Rr), HΓl', HΓr'.
  split; [ exact (rel_sub_under_ctx_q Hsub HA) |].
  split; [ exact Hl' |].
  exists (s ↦ c); split; [ exact Hs |].
  assert (HPr' : PER (per_env_extend A A Rr)) by (eapply per_env_PER; exact HΓr').
  etransitivity; [| exact Hmr' ].
  destruct Hch as [_ [H1 _]]; exact H1.
Qed.

(** [q τ] at an environment of an extension: the head is kept, and the
    tail is related to the value of [τ] at the environment's tail. *)
Lemma rel_sub_q_entry : forall {Γ'' Δ τ τ' e Re RΔ},
    EF (e :: Γ'') ≈ (e :: Γ'') ∈ per_ctx_env ↘ Re ->
    EF Δ ≈ Δ ∈ per_ctx_env ↘ RΔ ->
    Γ'' ⊨s τ ≈ τ' : Δ ->
    forall x u, Re x x -> ⟦ τ ⟧s x↯ ↘ u ->
      exists t, ⟦ q τ ⟧s x ↘ env_entry x 0 :: t /\ RΔ t u.
Proof.
  intros * He HΔ [R1 [H1 [R2 [H2 Hσ]]]] x u Hx Hu.
  pose proof (rel_wk_shift H1 He) as Hsh.
  destruct (Hσ _ _ He _ Hsh _ _ Hx) as [t v v' t' Ht Hv Hv' Ht' Hc].
  rewrite eval_wk_shift in Hv, Hv'.
  assert (Heq : env_eq v u) by (eapply functional_eval_sub; eassumption).
  exists t; split; [ apply eval_sub_q; exact Ht |].
  assert (E : R2 <~> RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  apply E; rewrite <- Heq; destruct Hc as [Hc _]; exact Hc.
Qed.

(** A definition's types and values along the walk, and the extended
    invariant at any values of its two sides. *)
Lemma hw_def : forall Γ' Γ σ Ψ A i M ρl ρr,
    hw_inv Γ' Γ σ Ψ ρl ρr ->
    Ψ ++ Γ ⊨ A : Typeω@i ->
    Ψ ++ Γ ⊨ M : A ->
    exists j R, PER.Definitions.rel_typ j A[sb_qn (List.length Ψ) σ] ρl A ρr R /\
      PER.Definitions.rel_elem M[sb_qn (List.length Ψ) σ] ρl M ρr R /\
      forall m m', ⟦ M[sb_qn (List.length Ψ) σ] ⟧ ρl ↘ m -> ⟦ M ⟧ ρr ↘ m' ->
        hw_inv Γ' Γ σ (Ψ ▸ A ≔ M) (ρl ↦ m) (ρr ↦ m').
Proof.
  intros * (Rl & Rr & HΓl & HΓr & Hsub & Hl & ρm & Hm & Hmr) HA HM.
  set (τ := sb_qn (List.length Ψ) σ) in *.
  assert (HPl : PER Rl) by (eapply per_env_PER; exact HΓl).
  assert (HPr : PER Rr) by (eapply per_env_PER; exact HΓr).
  pose proof HM as [R0 [HΓ0 [j HMgen]]].
  destruct (HMgen _ _ HΓl _ _ Hsub _ _ _ _ Hl Hm Hm)
    as [R1 [[a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hac] [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmc]]].
  destruct (HMgen _ _ HΓr _ _ (rel_sub_id (ex_intro _ _ HΓr)) _ _ _ _ Hmr (eval_sub_id _) (eval_sub_id _))
    as [R2 [[b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbc] [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnc]]].
  rewrite exp_sub_id in Hb1, Hb4, Hn1, Hn4.
  functional_eval_rewrite_clear.
  destruct Hac as [Ha12 _]; destruct Hbc as [_ [Hab3 _]].
  destruct Hmc as [Hm12 _]; destruct Hnc as [_ [Hmn3 _]].
  assert (Hu : Dom a1 ≈ b3 ∈ per_univ j) by (etransitivity; eexists; eassumption).
  destruct Hu as [R HR].
  pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR Ha12) as E1.
  pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ Hab3 HR) as E2.
  assert (HRP : PER R) by (eapply per_elem_PER; eassumption).
  assert (Hmn : R m1 n3) by (etransitivity; [ apply E1; exact Hm12 | apply E2; exact Hmn3 ]).
  exists j, R; split; [ econstructor; eassumption |]; split; [ econstructor; eassumption |].
  intros m m' Hm' Hm''.
  functional_eval_rewrite_clear.
  pose proof (per_ctx_env_of_def_sub HΓl Hsub HA HM) as HΓl'.
  pose proof (per_ctx_env_of_def HΓr HA HM) as HΓr'.
  pose proof (rel_exp_of_typ_sub_simple HΓl Hsub HA) as HSl.
  pose proof (rel_exp_under_ctx_sub_simple HΓl Hsub HM) as HMl.
  pose proof (rel_exp_of_typ_inversion_simple_at HΓr HA) as HSr.
  pose proof (rel_exp_under_ctx_simple_at HΓr HM) as HMr.
  assert (Ha11 : per_univ_elem j R a1 a1) by (etransitivity; [ exact HR | symmetry; exact HR ]).
  assert (Hb33 : per_univ_elem j R b3 b3) by (etransitivity; [ symmetry; exact HR | exact HR ]).
  assert (Hc : per_head A[τ] A[τ] ρl ρl m1 m1)
    by (eapply per_head_of; [ exact Ha1 | exact Ha1 | exact Ha11 | etransitivity; [ exact Hmn | symmetry; exact Hmn ] ]).
  assert (Hl' : per_env_extend_def A[τ] M[τ] Rl (ρl ↦ m1) (ρl ↦ m1))
    by (eapply per_env_extend_def_intro; [ exact HPl | exact HSl | exact HMl | exact Hl | exact Hc | exact Hm1 | exact Hc ]).
  destruct (rel_sub_q_entry HΓl' HΓr Hsub _ _ Hl' Hm) as [t [Hq Htm]].
  assert (Htr : Rr t ρr) by (etransitivity; eassumption).
  assert (Hh : per_head A A ρm ρr m1 n3)
    by (eapply per_head_of; [ exact Ha2 | exact Hb3 | exact Hab3 | apply E2; exact Hmn ]).
  assert (Hh' : per_head A A t ρr m1 n3).
  { eapply (per_head_of_typ_resp HΓr HA); [| exact Hh ].
    apply rel_chain_4; [ exact Htr | symmetry; exact Hmr | exact Hmr ]. }
  assert (Hext : per_env_extend A A Rr (t ↦ m1) (ρr ↦ n3)) by (apply per_env_extend_intro'; assumption).
  assert (Tr : def_tie A M (ρr ↦ n3)).
  { exists n3; split; [ exact Hn3 |].
    eapply per_head_of; [ exact Hb3 | exact Hb3 | exact Hb33 | etransitivity; [ symmetry; exact Hmn | exact Hmn ] ]. }
  assert (HPe : PER (per_env_extend A A Rr)) by (eapply per_env_PER; eapply per_ctx_env_of_typ; eassumption).
  assert (Tl : def_tie A M (t ↦ m1)) by (eapply (def_tie_resp HPr HSr HMr); [ symmetry; exact Hext | exact Tr ]).
  exists (per_env_extend_def A[τ] M[τ] Rl), (per_env_extend_def A M Rr), HΓl', HΓr'.
  split; [ exact (rel_sub_under_ctx_q_def Hsub HA HM) |].
  split; [ exact Hl' |].
  exists (t ↦ m1); split; [ exact Hq |].
  split; [ exact Hext | split; assumption ].
Qed.

(** A nested unit along the walk: its two closures are related, and so are
    the environments they extend. *)
Lemma hw_mod : forall Γ' Γ σ Ψ U ρl ρr,
    hw_inv Γ' Γ σ Ψ ρl ρr ->
    Ψ ++ Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    per_dmod (dm_local ρl U[sb_qn (List.length Ψ) σ]ᵘ nil) (dm_local ρr U nil) /\
    hw_inv Γ' Γ σ (Ψ ▹ₘ U) (ρl ↦ᵐ dm_local ρl U[sb_qn (List.length Ψ) σ]ᵘ nil) (ρr ↦ᵐ dm_local ρr U nil).
Proof.
  intros * (Rl & Rr & HΓl & HΓr & Hsub & Hl & ρm & Hm & Hmr) HU.
  set (τ := sb_qn (List.length Ψ) σ) in *.
  assert (HPr : PER Rr) by (eapply per_env_PER; exact HΓr).
  assert (HPd : PER per_dmod) by typeclasses eauto.
  destruct (unit_chain HU) as [R0 [HΓ0 Hch]].
  pose proof (Hch _ _ HΓl _ _ Hsub _ _ _ _ Hl Hm Hm) as [Hlm _].
  pose proof (unit_chain_at HU HΓr _ _ Hmr) as Hmr'.
  assert (Hlr : per_dmod (dm_local ρl U[τ]ᵘ nil) (dm_local ρr U nil)) by (etransitivity; eassumption).
  split; [ exact Hlr |].
  pose proof (per_ctx_env_of_mod_sub HΓl Hsub HU) as HΓl'.
  pose proof (per_ctx_env_of_mod HΓr HU) as HΓr'.
  assert (Hll : per_dmod (dm_local ρl U[τ]ᵘ nil) (dm_local ρl U[τ]ᵘ nil))
    by (etransitivity; [ exact Hlm | symmetry; exact Hlm ]).
  assert (Hl' : env_ext_mod U[τ]ᵘ U[τ]ᵘ Rl (ρl ↦ᵐ dm_local ρl U[τ]ᵘ nil) (ρl ↦ᵐ dm_local ρl U[τ]ᵘ nil))
    by (unfold env_ext_mod; cbn; repeat split; assumption).
  destruct (rel_sub_q_entry HΓl' HΓr Hsub _ _ Hl' Hm) as [t [Hq Htm]].
  assert (Htr : Rr t ρr) by (etransitivity; eassumption).
  pose proof (unit_chain_at HU HΓr _ _ (symmetry Htm)) as Hmt.
  exists (env_ext_mod U[τ]ᵘ U[τ]ᵘ Rl), (env_ext_mod U U Rr), HΓl', HΓr'.
  split; [ exact (rel_sub_under_ctx_q_mod Hsub HU) |].
  split; [ exact Hl' |].
  exists (env_entry (ρl ↦ᵐ dm_local ρl U[τ]ᵘ nil) 0 :: t); split; [ exact Hq |].
  unfold env_ext_mod; cbn.
  assert (Hrr : per_dmod (dm_local ρr U nil) (dm_local ρr U nil))
    by (etransitivity; [ symmetry; exact Hlr | exact Hlr ]).
  assert (Hlt : per_dmod (dm_local ρl U[τ]ᵘ nil) (dm_local t U nil)) by (etransitivity; [ exact Hlm | exact Hmt ]).
  repeat split; assumption.
Qed.

(** An alias's targets along the walk are related. *)
Lemma hw_alias : forall Γ' Γ σ Ψ E ρl ρr,
    hw_inv Γ' Γ σ Ψ ρl ρr ->
    Ψ ++ Γ ⊨ᵐ E ≈ E ->
    exists h h', eval_modexp gc_deps gc_stack E[sb_qn (List.length Ψ) σ]ᵐ ρl h /\
      ⟦ E ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρr ↘ h' /\ per_dmod h h'.
Proof.
  intros * (Rl & Rr & HΓl & HΓr & Hsub & Hl & ρm & Hm & Hmr) [R0 [HΓ0 HE]].
  destruct (HE _ _ HΓl _ _ Hsub _ _ _ _ Hl Hm Hm) as [h1 h2 h3 h4 H1 H2 H3 H4 [Hc _]].
  destruct (HE _ _ HΓr _ _ (rel_sub_id (ex_intro _ _ HΓr)) _ _ _ _ Hmr (eval_sub_id _) (eval_sub_id _))
    as [g1 g2 g3 g4 G1 G2 G3 G4 [_ [Hg _]]].
  pose proof (functional_eval_modexp _ _ _ _ H2 G2) as <-.
  exists h1, g3; split; [ exact H1 | split; [ exact G3 | eapply per_dmod_trans; eassumption ] ].
Qed.

Lemma sem_ctx_app_r : forall Ψ Γ, ⊨ Ψ ++ Γ -> ⊨ Γ.
Proof. induction Ψ; intros * H; cbn in *; [ exact H | apply IHΨ; eapply sem_ctx_tail; exact H ]. Qed.

(** The parameters, outermost first: [ts] is the rest of the telescope,
    reversed. *)
Lemma hw_params : forall Γ' Γ σ ts Ψ Dl D ρl ρr,
    tele_ass ts ->
    ⊨ rev ts ++ Ψ ++ Γ ->
    hw_inv Γ' Γ σ Ψ ρl ρr ->
    (forall ρl' ρr', hw_inv Γ' Γ σ (rev ts ++ Ψ) ρl' ρr' -> per_mdef ρl' Dl ρr' D) ->
    per_ltele (rev (tele_sub (rev ts) (sb_qn (List.length Ψ) σ))) ρl Dl ts ρr D nil nil.
Proof.
  induction ts as [| e ts IH]; intros * Hts HΨ Hinv HD; cbn [rev tele_sub app] in *.
  - constructor; apply HD; exact Hinv.
  - inversion Hts as [| ? ? [A ->] Hts0]; subst.
    rewrite tele_sub_app, rev_app_distr; cbn [rev app tele_sub length sb_qn centry_sub].
    rewrite <- !app_assoc in HΨ; cbn [app] in HΨ.
    pose proof (sem_ctx_app_r _ _ HΨ) as HΨA.
    inversion HΨA; subst.
    destruct (hw_ass _ _ _ _ _ _ _ _ Hinv ltac:(eassumption)) as [R [HR Hc]].
    eapply per_ltele_missing; [ exact HR |].
    intros c c' Hcc.
    apply (IH (Ψ ▹ A)); [ exact Hts0 | exact HΨ | apply Hc, Hcc |].
    intros ρl' ρr' Hi; apply HD; rewrite <- app_assoc; exact Hi.
Qed.

Lemma ematch_binders : forall Φt Φe, ematch Φe Φt -> gm_binders Φe = gm_binders Φt.
Proof.
  induction Φt as [| Φt IH y E | Φt IH H its]; intros Φe Hm; cbn [ematch] in Hm; try contradiction; [ subst; reflexivity |].
  destruct Hm as (Φe0 & ye & Ee & -> & Hm & _); cbn; f_equal; auto.
Qed.

(** Entries along the walk of a unit and its substitute. *)
Lemma hw_walk_eval : forall Γ' Γ σ Φt Φe Ψ ρl ρr,
    ematch Φe Φt ->
    ⊨ body_ctx Φt ++ Ψ ++ Γ ->
    hw_inv Γ' Γ σ Ψ ρl ρr ->
    exists ρl1 ρr1, ⟦ gmod_sub Φe (sb_qn (List.length Ψ) σ) ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρl ↘ ρl1 /\
      ⟦ Φe ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρr ↘ ρr1 /\ hw_inv Γ' Γ σ (body_ctx Φt ++ Ψ) ρl1 ρr1.
Proof.
  induction Φt as [| Φt IH y Et | Φt IH H its]; intros * Hm HΦ Hinv; cbn [ematch] in Hm; try contradiction.
  - subst; exists ρl, ρr; repeat split; try constructor; exact Hinv.
  - destruct Hm as (Φe0 & ye & Ee & -> & Hm & HEe).
    assert (Hq : sb_eq (sb_qn (gm_binders Φe0) (sb_qn (List.length Ψ) σ)) (sb_qn (List.length (body_ctx Φt ++ Ψ)) σ))
      by (rewrite sb_qn_add, length_app, length_body_ctx, (ematch_binders _ _ Hm); reflexivity).
    destruct Ee as [? ? ? [M |] | pm Uy | ? ? ? | ? ? ? ?], Et as [bt pvt At [Mt |] | pmt Ut | ? ? ? | ? ? ? ?];
      cbn in HEe; try contradiction; subst; cbn [gmod_sub gentry_sub body_ctx app] in *.
    + inversion HΦ; subst.
      match goal with H : ⊨ body_ctx Φt ++ Ψ ++ Γ |- _ => rename H into HΦ0 end.
      destruct (IH _ _ _ _ Hm HΦ0 Hinv) as (ρl1 & ρr1 & Hb1 & Hb1' & Hi1).
      rewrite app_assoc in *.
      destruct (hw_def _ _ _ _ _ _ _ _ _ Hi1 ltac:(eassumption) ltac:(eassumption)) as (j & R & HR & HM & Hstep).
      rewrite (exp_sub_sb_eq Mt _ _ Hq).
      destruct HM as [m m' Hm1 Hm1' Hmm'].
      exists (ρl1 ↦ m), (ρr1 ↦ m'); repeat split; [ econstructor; eassumption | econstructor; eassumption |].
      apply Hstep; assumption.
    + inversion HΦ; subst.
      match goal with H : ⊨ body_ctx Φt ++ Ψ ++ Γ |- _ => rename H into HΦ0 end.
      destruct (IH _ _ _ _ Hm HΦ0 Hinv) as (ρl1 & ρr1 & Hb1 & Hb1' & Hi1).
      rewrite app_assoc in *.
      destruct (hw_mod _ _ _ _ _ _ _ Hi1 ltac:(eassumption)) as (HU & Hstep).
      rewrite (gunit_sub_sb_eq Ut _ _ Hq).
      eexists; eexists; repeat split; [ econstructor; eassumption | econstructor; eassumption |].
      exact Hstep.
Qed.

(** What the kinds read off an open of a target, read off an open of its
    substitute with the same kinds. *)
Lemma kgens_sub_transfer : forall ρl ρr H τ its gs,
    kgens gc_deps gc_stack ρr H its gs ->
    (forall n k, skind gc_deps gc_stack ρr H (n :: nil) k -> skind gc_deps gc_stack ρl H[τ]ᵐ (n :: nil) k) ->
    kgens gc_deps gc_stack ρl H[τ]ᵐ its (List.map (fun g => igen_sub g τ) gs).
Proof. intros * Hg Hs; induction Hg; cbn [List.map igen_sub exp_sub modexp_sub]; constructor; auto. Qed.

Lemma body_shape_gens_base : forall gs gs' Φ Φ' k, List.length gs = List.length gs' ->
    body_shape (gens_append Φ k gs) (gens_append Φ' k gs') -> body_shape Φ Φ'.
Proof.
  induction gs as [| g gs IH]; intros [| g' gs'] * Hl Hs; cbn in Hl; try discriminate; [ exact Hs |].
  cbn [gens_append] in Hs; destruct (ig_entry g), (ig_entry g').
  apply IH in Hs; [ cbn in Hs; tauto | congruence ].
Qed.

(** A body, entry by entry; a local open, as the entries it generates. *)
Lemma hw_body : forall Γ' Γ σ Φ Φx Ψ ρl ρr,
    ⊢g gc_deps ⍮ gc_stack ->
    body_xp gc_deps gc_stack (Ψ ++ Γ) Φ Φx ->
    body_shape Φ Φ -> body_shape Φx Φx ->
    ⊨ body_ctx Φx ++ Ψ ++ Γ ->
    (forall k Ψo H, nth_error (body_opens Φ Φx) k = Some (Ψo, H) -> Ψo ++ Ψ ++ Γ ⊨ᵐ H ≈ H) ->
    hw_inv Γ' Γ σ Ψ ρl ρr ->
    per_body ρl (gmod_sub Φ (sb_qn (List.length Ψ) σ)) ρr Φ /\
    exists ρl1 ρr1, ⟦ gmod_sub Φ (sb_qn (List.length Ψ) σ) ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρl ↘ ρl1 /\
      ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρr ↘ ρr1 /\ hw_inv Γ' Γ σ (body_ctx Φx ++ Ψ) ρl1 ρr1.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros * Hg Hx Hs Hsx HΦ Ho Hinv; cbn in Hs.
  - inversion Hx; subst; split; [ constructor |]; exists ρl, ρr; repeat split; try constructor; exact Hinv.
  - destruct Hs as (Hs & _ & HE).
    inversion Hx as [| ? ? Φx0 ? ? Hx0 |]; subst.
    cbn [body_opens gm_dropn] in Ho; cbn [body_shape] in Hsx; destruct Hsx as (Hsx & _ & _).
    assert (Hq : sb_eq (sb_qn (gm_binders Φ) (sb_qn (List.length Ψ) σ)) (sb_qn (List.length (body_ctx Φx0 ++ Ψ)) σ))
      by (rewrite sb_qn_add, length_app, length_body_ctx, (body_xp_binders _ _ _ _ _ Hx0); reflexivity).
    destruct E as [b pv A [M |] | pm Uy | pv D Φd | ? ? ? ?]; cbn in HE; try contradiction; cbn [gmod_sub gentry_sub body_ctx app] in *.
    + inversion HΦ; subst.
      match goal with H : ⊨ body_ctx Φx0 ++ Ψ ++ Γ |- _ => rename H into HΦ0 end.
      destruct (IH _ _ _ _ Hg Hx0 Hs Hsx HΦ0 Ho Hinv) as (Hb & ρl1 & ρr1 & Hb1 & Hb1' & Hi1).
      rewrite app_assoc in *.
      destruct (hw_def _ _ _ _ _ _ _ _ _ Hi1 ltac:(eassumption) ltac:(eassumption)) as (j & R & HR & HM & Hstep).
      rewrite (exp_sub_sb_eq A _ _ Hq), (exp_sub_sb_eq M _ _ Hq).
      destruct HM as [m m' Hm Hm' Hmm'].
      split; [ eapply per_body_def; [ exact Hb | exact Hb1 | exact Hb1' | exact HR | econstructor; eassumption ] |].
      exists (ρl1 ↦ m), (ρr1 ↦ m'); repeat split; [ econstructor; eassumption | econstructor; eassumption |].
      apply Hstep; assumption.
    + inversion HΦ; subst.
      match goal with H : ⊨ body_ctx Φx0 ++ Ψ ++ Γ |- _ => rename H into HΦ0 end.
      destruct (IH _ _ _ _ Hg Hx0 Hs Hsx HΦ0 Ho Hinv) as (Hb & ρl1 & ρr1 & Hb1 & Hb1' & Hi1).
      rewrite app_assoc in *.
      destruct (hw_mod _ _ _ _ _ _ _ Hi1 ltac:(eassumption)) as (HU & Hstep).
      rewrite (gunit_sub_sb_eq Uy _ _ Hq).
      split; [ eapply per_body_mod; [ exact Hb | exact Hb1 | exact Hb1' | exact HU ] |].
      eexists; eexists; repeat split; [ econstructor; eassumption | econstructor; eassumption |].
      exact Hstep.
  - (* a local open *)
    destruct Hs as [Hs _].
    inversion Hx as [| | ? ? Φx0 ? ? Rm T gs Hx0 HRm HT Hgs Hok ]; subst.
    pose proof (items_gen_length _ _ _ _ _ _ _ Hgs) as Hl.
    cbn [body_opens] in Ho.
    assert (E1 : gm_dropn (List.length its) (gens_append Φx0 0 gs) = Φx0) by (rewrite <- Hl; apply gm_dropn_gens_append).
    rewrite E1 in Ho.
    pose proof (body_shape_gens_base _ _ _ _ _ eq_refl Hsx) as Hsx0.
    rewrite gens_body_ctx_base, <- app_assoc in HΦ.
    pose proof (sem_ctx_app_r _ _ HΦ) as HΦ0.
    destruct (IH _ _ _ _ Hg Hx0 Hs Hsx0 HΦ0 (fun k => Ho (S k)) Hinv) as (Hb & ρl1 & ρr1 & Hb1 & Hb1' & Hi1).
    pose proof (Ho 0 _ _ eq_refl) as HH; rewrite app_assoc in HH.
    destruct (hw_alias _ _ _ _ _ _ _ Hi1 HH) as (hl & hr & Hhl & Hhr & Hhh).
    set (τ1 := sb_qn (List.length (body_ctx Φx0 ++ Ψ)) σ) in *.
    assert (Hq : sb_eq (sb_qn (gm_binders Φ) (sb_qn (List.length Ψ) σ)) τ1)
      by (subst τ1; rewrite sb_qn_add, length_app, length_body_ctx, (body_xp_binders _ _ _ _ _ Hx0); reflexivity).
    cbn [gmod_sub]; rewrite (modexp_sub_sb_eq H _ _ Hq).
    (* the kinds of the two targets *)
    pose proof Hi1 as (Rl & Rr & HΓl & HΓr & _ & _ & ρm & _ & Hmr).
    destruct (per_ctx_env_kmatch Hg _ _ _ HΓr _ _ Hmr) as [_ Kr].
    rewrite <- app_assoc in Kr.
    pose proof (proj2 (proj2 (proj2 (member_kind _ _))) _ _ _ _ _ Hgs eq_refl _ Kr) as Hkr.
    assert (Hkl : kgens gc_deps gc_stack ρl1 H[τ1]ᵐ its (List.map (fun g => igen_sub g τ1) (List.map ig_erase gs))).
    { apply (kgens_sub_transfer _ ρr1); [ exact Hkr |].
      intros n k Hk; rewrite <- (kind_eval_modexp _ _ Hg _ _ _ Hhl).
      apply (per_dmod_kequiv Hg _ _ Hhh), (kind_eval_modexp _ _ Hg _ _ _ Hhr), Hk. }
    (* the entries they generate *)
    assert (HΦ' : ⊨ body_ctx (gens_append gm_nil 0 gs) ++ (body_ctx Φx0 ++ Ψ) ++ Γ) by (rewrite <- app_assoc; exact HΦ).
    destruct (hw_walk_eval _ _ _ (gens_append gm_nil 0 gs) (gens_append gm_nil 0 (List.map ig_erase gs)) (body_ctx Φx0 ++ Ψ) _ _
                (ematch_gens gs gm_nil gm_nil 0 (items_gen_local _ _ _ _ _ _ Hgs) eq_refl) HΦ' Hi1)
      as (ρl2 & ρr2 & Hb2 & Hb2' & Hi2).
    rewrite (gens_append_sub _ gm_nil 0 _ (le_n 0)) in Hb2; cbn [gmod_sub gm_binders Nat.sub sb_qn] in Hb2.
    split; [ eapply per_body_open; [ exact Hb | exact Hb1 | exact Hb1' | exact Hhl | exact Hhr | exact Hhh ] |].
    exists ρl2, ρr2; repeat split; [ econstructor; [ exact Hb1 | exact Hkl | exact Hb2 ] | econstructor; [ exact Hb1' | exact Hkr | exact Hb2' ] |].
    rewrite gens_body_ctx_base, <- app_assoc; exact Hi2.
Qed.

(** ** Closures Commute with Substitution

    The closure of [U[σ]] over [ρ] is related to that of [U] over [⟦σ⟧ρ],
    for any unit valid in its parts. *)
Lemma unit_sub_link : forall Γ' Γ σ σ' U R' ρ ρσ,
    ⊢g gc_deps ⍮ gc_stack ->
    sem_unit Γ U ->
    Γ' ⊨s σ ≈ σ' : Γ ->
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' ->
    R' ρ ρ -> ⟦ σ ⟧s ρ ↘ ρσ ->
    per_dmod (dm_local ρ U[σ]ᵘ nil) (dm_local ρσ U nil).
Proof.
  intros * Hg HU Hσ HΓ' Hρ Hev.
  inversion HU as [? Δ Φ Φx HΔ Hx Hs Hsx HΦ Ho | ? Δ E HΔ HΔΓ HE]; subst;
    rewrite gunit_sub_mk; constructor; cbn [gu_params gu_def moddef_sub].
  - destruct (sem_ctx_per_ctx_env (sem_ctx_app_r _ _ (sem_ctx_app_r _ _ HΦ))) as [R HΓ].
    pose proof (hw_init _ _ _ _ _ _ _ _ Hσ HΓ' HΓ Hρ Hev) as Hi.
    pose proof (hw_params Γ' Γ σ (rev Δ) nil (md_body (gmod_sub Φ (sb_qn (List.length Δ) σ))) (md_body Φ) ρ ρσ
                  ltac:(apply Forall_rev; exact HΔ)
                  ltac:(rewrite rev_involutive, app_nil_l; exact (sem_ctx_app_r _ _ HΦ)) Hi)
      as Hp.
    rewrite rev_involutive in Hp; apply Hp.
    intros ρl' ρr' Hi'; rewrite app_nil_r in Hi'.
    constructor; exact (proj1 (hw_body _ _ _ _ _ _ _ _ Hg Hx Hs Hsx HΦ Ho Hi')).
  - destruct (sem_ctx_per_ctx_env (sem_ctx_app_r _ _ HΔΓ)) as [R HΓ].
    pose proof (hw_init _ _ _ _ _ _ _ _ Hσ HΓ' HΓ Hρ Hev) as Hi.
    pose proof (hw_params Γ' Γ σ (rev Δ) nil (md_alias E[sb_qn (List.length Δ) σ]ᵐ) (md_alias E) ρ ρσ
                  ltac:(apply Forall_rev; exact HΔ) ltac:(rewrite rev_involutive, app_nil_l; exact HΔΓ) Hi)
      as Hp.
    rewrite rev_involutive in Hp; apply Hp.
    intros ρl' ρr' Hi'; rewrite app_nil_r in Hi'.
    destruct (hw_alias _ _ _ _ _ _ _ Hi' HE) as (h & h' & Hh & Hh' & Hhh).
    econstructor; eassumption.
Qed.

(** ** Module Expressions: Symmetry and Transitivity *)

Lemma rel_modexp_sym : forall {Γ H H'}, Γ ⊨ᵐ H ≈ H' -> Γ ⊨ᵐ H' ≈ H.
Proof.
  intros * [R [HΓ HH]]; exists R, HΓ.
  intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HP : PER R') by (eapply per_env_PER; exact HΓ').
  destruct (HH _ _ HΓ' _ _ (rel_sub_under_ctx_sym Hσ) _ _ _ _ (symmetry Hρ) Hev' Hev) as [? ? ? ? ? ? ? ? Hc].
  econstructor; try eassumption.
  assert (PER per_dmod) by typeclasses eauto.
  now apply rel_chain_4_sym.
Qed.

Lemma rel_modexp_trans : forall {Γ H1 H2 H3}, Γ ⊨ᵐ H1 ≈ H2 -> Γ ⊨ᵐ H2 ≈ H3 -> Γ ⊨ᵐ H1 ≈ H3.
Proof.
  intros * [R [HΓ H12]] [R2 [HΓ2 H23]].
  exists R, HΓ.
  intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HP : PER R') by (eapply per_env_PER; exact HΓ').
  assert (Hρ' : R' ρ' ρ') by (etransitivity; [ symmetry |]; eassumption).
  destruct (H12 _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [v1 v2 v3 v4 ? ? ? ? Hc1].
  destruct (H23 _ _ HΓ' _ _ (rel_sub_under_ctx_refl_right Hσ) _ _ _ _ Hρ' Hev' Hev')
    as [w1 w2 w3 w4 ? ? ? ? Hc2].
  repeat match goal with
         | H : eval_modexp _ _ ?E ?r ?a, H' : eval_modexp _ _ ?E ?r ?b |- _ =>
             pose proof (functional_eval_modexp _ _ _ _ H H'); subst; clear H'
         end.
  econstructor; try eassumption.
  assert (PER per_dmod) by typeclasses eauto.
  match type of Hc1 with rel_chain _ (_ :: _ :: ?c :: _) => merge_rel_chain Hc1 Hc2 c end.
Qed.

Corollary rel_modexp_refl_left : forall {Γ H H'}, Γ ⊨ᵐ H ≈ H' -> Γ ⊨ᵐ H ≈ H.
Proof. intros * HH; eapply rel_modexp_trans; [ exact HH | apply rel_modexp_sym, HH ]. Qed.

Corollary rel_modexp_refl_right : forall {Γ H H'}, Γ ⊨ᵐ H ≈ H' -> Γ ⊨ᵐ H' ≈ H'.
Proof. intros * HH; eapply rel_modexp_trans; [ apply rel_modexp_sym, HH | exact HH ]. Qed.

(** ** Extensions *)

(** Two definition entries with related types and bodies, over related
    contexts. *)
Lemma per_ctx_env_extend_def_cross : forall {Δ Δ' A A' M M'} {i : nat} {R},
    EF Δ ≈ Δ' ∈ per_ctx_env ↘ R ->
    Δ ⊨ A ≈ A' : Typeω@i ->
    Δ ⊨ M ≈ M' : A ->
    exists R', EF Δ ▸ A ≔ M ≈ Δ' ▸ A' ≔ M' ∈ per_ctx_env ↘ R'.
Proof.
  intros * HR HA HM.
  pose proof (rel_exp_of_typ_inversion_simple HA) as [RΔ [HΔ HAs]].
  assert (E : R <~> RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  pose proof (rel_exp_of_typ_inversion_simple_at HΔ (rel_exp_under_ctx_refl_left HA)) as HAl.
  pose proof (rel_exp_under_ctx_simple_at HΔ HM) as HMs.
  eexists.
  eapply (@per_ctx_env_cons_def _ Δ Δ' i A A' M M' R (fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ R) => per_head A A' ρ ρ')
            (fun ρ ρ' => exists (H : R ρ↯ ρ'↯),
               per_head A A' ρ↯ ρ'↯ (ρ 0) (ρ' 0) /\
               (exists m, ⟦ M ⟧ ρ↯ ↘ m /\ per_head A A' ρ↯ ρ'↯ m (ρ 0)) /\
               (exists m, ⟦ M' ⟧ ρ↯ ↘ m /\ per_head A A' ρ↯ ρ'↯ m (ρ 0)) /\
               (exists m', ⟦ M ⟧ ρ'↯ ↘ m' /\ per_head A A' ρ↯ ρ'↯ m' (ρ' 0)) /\
               (exists m', ⟦ M' ⟧ ρ'↯ ↘ m' /\ per_head A A' ρ↯ ρ'↯ m' (ρ' 0))));
    [ exact HR | eapply per_env_PER; exact HR | | | reflexivity ].
  - intros ρ ρ' Hρ.
    destruct (HAs _ _ (proj1 (E _ _) Hρ)) as [a [a' [Ha [Ha' [R1 HR1]]]]].
    econstructor; try eassumption.
    eapply per_univ_elem_resp_iff; [ eassumption |].
    eapply per_head_iff; eassumption.
  - intros ρ ρ' Hρ.
    destruct (HAs _ _ (proj1 (E _ _) Hρ)) as [a [a' [Ha [Ha' [R1 HR1]]]]].
    destruct (HAl _ _ (proj1 (E _ _) Hρ)) as [a0 [b [Ha0 [Hb [R2 HR2]]]]].
    destruct (HMs _ _ (proj1 (E _ _) Hρ)) as [m [m' [Hm [Hm' Hmm']]]].
    functional_eval_rewrite_clear.
    econstructor; try eassumption.
    apply (per_head_iff Ha Ha' HR1).
    apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR2 HR1).
    apply (per_head_iff Ha Hb HR2); exact Hmm'.
Qed.

Lemma rel_ext_nil : forall {Γ}, ⊨ Γ -> Γ ⊨ˣ nil ≈ nil.
Proof. intros * H; split; [| split ]; [ exact H | exact H | exact (sem_ctx_per_ctx H) ]. Qed.

Lemma rel_ext_ass : forall {Γ Ψ Ψ' A A'} {i : nat},
    Γ ⊨ˣ Ψ ≈ Ψ' ->
    Ψ ++ Γ ⊨ A : Typeω@i ->
    Ψ ++ Γ ⊨ A ≈ A' : Typeω@i ->
    Ψ' ++ Γ ⊨ A' : Typeω@i ->
    Γ ⊨ˣ Ψ ▹ A ≈ Ψ' ▹ A'.
Proof.
  intros * (H1 & H2 & H3) HA HAA' HA'.
  split; [| split ]; cbn [app].
  - exact (rel_ctx_extend' H1 HA).
  - exact (rel_ctx_extend' H2 HA').
  - exact (rel_ctx_extend H3 HAA').
Qed.

Lemma rel_ext_def : forall {Γ Ψ Ψ' A A' M M'} {i : nat},
    Γ ⊨ˣ Ψ ≈ Ψ' ->
    Ψ ++ Γ ⊨ A : Typeω@i ->
    Ψ ++ Γ ⊨ A ≈ A' : Typeω@i ->
    Ψ ++ Γ ⊨ M : A ->
    Ψ ++ Γ ⊨ M ≈ M' : A ->
    Ψ' ++ Γ ⊨ A' : Typeω@i ->
    Ψ' ++ Γ ⊨ M' : A' ->
    Γ ⊨ˣ Ψ ▸ A ≔ M ≈ Ψ' ▸ A' ≔ M'.
Proof.
  intros * (H1 & H2 & [R HR]) HA HAA' HM HMM' HA' HM'.
  split; [| split ]; cbn [app].
  - exact (rel_ctx_extend_def' H1 HA HM).
  - exact (rel_ctx_extend_def' H2 HA' HM').
  - exact (per_ctx_env_extend_def_cross HR HAA' HMM').
Qed.

Lemma rel_ext_mod : forall {Γ Ψ Ψ' U U'},
    Γ ⊨ˣ Ψ ≈ Ψ' ->
    Ψ ++ Γ ⊨ᵘ U ≈ U' ->
    Ψ' ++ Γ ⊨ᵘ U' ≈ U' ->
    Γ ⊨ˣ Ψ ▹ₘ U ≈ Ψ' ▹ₘ U'.
Proof.
  intros * (H1 & H2 & [Rx HRx]) (HU & HsU & _) (HU' & HsU' & _).
  destruct (sem_ctx_per_ctx_env H1) as [R HR].
  destruct (sem_ctx_per_ctx_env H2) as [R' HR'].
  pose proof (rel_modexp_refl_left HU) as HUU.
  split; [| split ]; cbn [app].
  - econstructor; [ exact H1 | exact (per_ctx_env_of_mod HR HUU) | exact HUU | exact HsU ].
  - econstructor; [ exact H2 | exact (per_ctx_env_of_mod HR' HU') | exact HU' | exact HsU' ].
  - assert (E : Rx <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
    exists (env_ext_mod U U' Rx).
    eapply per_ctx_env_cons_mod; [ exact HRx | eapply per_env_PER; exact HRx | | reflexivity ].
    intros ρ ρ' Hρ; eapply unit_chain_at; [ exact HU | exact HR | apply E, Hρ ].
Qed.

(** ** Units *)

Lemma body_shape_refl : forall Φ Φ', body_shape Φ Φ' -> body_shape Φ Φ /\ body_shape Φ' Φ'.
Proof.
  induction Φ as [| Φ IH x E | Φ IH c]; intros [| Φ' x' E' | Φ' c'] Hs; cbn in *; try contradiction; auto.
  - destruct Hs as (Hs & -> & HE); destruct (IH _ Hs).
    destruct E as [? ? ? [] | | | ], E' as [? ? ? [] | | | ]; cbn in *; intuition (subst; auto).
  - destruct Hs as (Hs & ->); destruct (IH _ Hs); auto.
Qed.

(** Two units valid in their parts are equivalent when their closures over
    related environments are related: the outer links of the chain are the
    commutation of each closure with substitution. *)
Lemma rel_unit_lit_intro : forall {Γ U U'},
    ⊢g gc_deps ⍮ gc_stack ->
    ⊨ Γ ->
    sem_unit Γ U -> sem_unit Γ U' ->
    (forall R, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> forall ρ ρ', R ρ ρ' -> per_dmod (dm_local ρ U nil) (dm_local ρ' U' nil)) ->
    Γ ⊨ᵘ U ≈ U'.
Proof.
  intros * Hg HΓ HsU HsU' HUU'.
  destruct (sem_ctx_per_ctx_env HΓ) as [R HR].
  split; [| split; assumption ].
  exists R, HR.
  intros Γ'' R'' HΓ'' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HP : PER R'') by (eapply per_env_PER; exact HΓ'').
  assert (PER per_dmod) by typeclasses eauto.
  econstructor; cbn [modexp_sub]; try apply eval_me_lit.
  apply rel_chain_4.
  - eapply unit_sub_link; [ exact Hg | exact HsU | exact Hσ | exact HΓ'' | etransitivity; [ exact Hρ | symmetry; exact Hρ ] | exact Hev ].
  - apply (HUU' _ HR); eapply (rel_sub_under_ctx_at' Hσ HΓ'' HR); eassumption.
  - symmetry; eapply unit_sub_link;
      [ exact Hg | exact HsU' | exact (rel_sub_under_ctx_refl_right Hσ) | exact HΓ''
      | etransitivity; [ symmetry; exact Hρ | exact Hρ ] | exact Hev' ].
Qed.

Lemma rel_unit_body : forall {Γ Δ Δ' Φ Φ' Φx Φx'},
    ⊢g gc_deps ⍮ gc_stack ->
    body_xp gc_deps gc_stack (Δ ++ Γ) Φ Φx -> body_xp gc_deps gc_stack (Δ' ++ Γ) Φ' Φx' ->
    Γ ⊨ˣ body_ctx Φx ++ Δ ≈ body_ctx Φx' ++ Δ' ->
    (forall k Ψ H Ψ' H', nth_error (body_opens Φ Φx) k = Some (Ψ, H) ->
       nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> Ψ ++ Δ ++ Γ ⊨ᵐ H ≈ H') ->
    (forall k Ψ H Ψ' H', nth_error (body_opens Φ Φx) k = Some (Ψ, H) ->
       nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> Ψ' ++ Δ' ++ Γ ⊨ᵐ H' ≈ H') ->
    tele_ass Δ -> tele_ass Δ' -> List.length Δ = List.length Δ' ->
    body_shape Φ Φ' -> body_shape Φx Φx' ->
    Γ ⊨ᵘ gu_body Δ Φ ≈ gu_body Δ' Φ'.
Proof.
  intros * Hg Hx Hx' (H1 & H2 & [Rx HRx]) Ho Ho' HΔ HΔ' Hl Hs Hsx.
  rewrite <- app_assoc in H1, H2, HRx; rewrite <- app_assoc in HRx.
  destruct (body_shape_refl _ _ Hs) as [Hs1 Hs2].
  destruct (body_shape_refl _ _ Hsx) as [Hsx1 Hsx2].
  assert (Hol : List.length (body_opens Φ Φx) = List.length (body_opens Φ' Φx'))
    by (rewrite (body_opens_length _ _ _ _ _ Hx), (body_opens_length _ _ _ _ _ Hx'); apply body_shape_nopens, Hs).
  apply rel_unit_lit_intro;
    [ exact Hg | exact (sem_ctx_app_r _ _ (sem_ctx_app_r _ _ H1)) | econstructor; try eassumption | econstructor; try eassumption |].
  - intros k Ψ H Hk.
    destruct (nth_error (body_opens Φ' Φx') k) as [[Ψ' H'] |] eqn:Hk';
      [| apply nth_error_None in Hk';
         assert (Hb : k < List.length (body_opens Φ Φx)) by (apply nth_error_Some; rewrite Hk; discriminate); lia ].
    exact (rel_modexp_refl_left (Ho _ _ _ _ _ Hk Hk')).
  - intros k Ψ' H' Hk'.
    destruct (nth_error (body_opens Φ Φx) k) as [[Ψ H] |] eqn:Hk;
      [| apply nth_error_None in Hk;
         assert (Hb : k < List.length (body_opens Φ' Φx')) by (apply nth_error_Some; rewrite Hk'; discriminate); lia ].
    exact (Ho' _ _ _ _ _ Hk Hk').
  - intros R HR ρ ρ' Hρ.
    eapply rel_closure_body; eassumption.
Qed.

Lemma rel_unit_alias : forall {Γ Δ Δ' E E'},
    ⊢g gc_deps ⍮ gc_stack ->
    Γ ⊨ˣ Δ ≈ Δ' ->
    tele_ass Δ -> tele_ass Δ' ->
    Δ ++ Γ ⊨ᵐ E ≈ E' ->
    Δ' ++ Γ ⊨ᵐ E' ≈ E' ->
    Γ ⊨ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E').
Proof.
  intros * Hg (H1 & H2 & [Rx HRx]) HΔ HΔ' HE HE'.
  assert (Hl : List.length Δ = List.length Δ').
  { pose proof (per_ctx_respects_length (ex_intro _ _ HRx)) as Hl; rewrite !length_app in Hl; lia. }
  apply rel_unit_lit_intro;
    [ exact Hg | exact (sem_ctx_app_r _ _ H1) | constructor; [ exact HΔ | exact H1 | exact (rel_modexp_refl_left HE) ]
    | constructor; assumption |].
  intros R HR ρ ρ' Hρ.
  eapply rel_closure_alias; [ exact HΔ | exact HΔ' | exact Hl | exact HR | exact HRx | | exact Hρ ].
  intros ρ1 ρ1' Hρ1.
  destruct HE as [RE [HΓE HEg]].
  assert (Ex : Rx <~> RE) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (HEg _ _ HΓE _ _ (rel_sub_id (ex_intro _ _ HΓE)) _ _ _ _ (proj1 (Ex _ _) Hρ1) (eval_sub_id _) (eval_sub_id _))
    as [h1 h2 h3 h4 _ Hh2 Hh3 _ [_ [Hh _]]].
  exists h2, h3; repeat split; assumption.
Qed.

Lemma rel_unit_sym : forall {Γ U U'}, Γ ⊨ᵘ U ≈ U' -> Γ ⊨ᵘ U' ≈ U.
Proof. intros * (H & H1 & H2); split; [ apply rel_modexp_sym, H | split; assumption ]. Qed.

Lemma rel_unit_trans : forall {Γ U1 U2 U3}, Γ ⊨ᵘ U1 ≈ U2 -> Γ ⊨ᵘ U2 ≈ U3 -> Γ ⊨ᵘ U1 ≈ U3.
Proof.
  intros * (H12 & H1 & _) (H23 & _ & H3).
  split; [ eapply rel_modexp_trans; eassumption | split; assumption ].
Qed.

(** ** Module Lets *)

Lemma eval_sub_wk_extend_mod : forall σ H φ ρ ρσ h,
    ⟦ sb_wk σ φ ⟧s ρ ↘ ρσ ->
    ⟦ modexp_wk H φ ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h ->
    ⟦ sb_wk (σ ,,ₘ H) φ ⟧s ρ ↘ ρσ ↦ᵐ h.
Proof. intros * Hσ HH [| x]; [ exists h; split; [ reflexivity | assumption ] | apply Hσ ]. Qed.

(** A substitution extended into a slot by the literals of equivalent units. *)
Lemma rel_sub_under_ctx_extend_mod : forall {Γ' Γ σ σ' U U'},
    Γ' ⊨s σ ≈ σ' : Γ ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U' ->
    Γ' ⊨s σ ,,ₘ me_lit U[σ]ᵘ ≈ σ' ,,ₘ me_lit U'[σ']ᵘ : Γ ▹ₘ U.
Proof.
  intros * Hσj HU.
  pose proof Hσj as [R' [HΓ' [R [HΓ Hσ]]]].
  pose proof (rel_modexp_refl_left HU) as HUU.
  destruct (unit_chain HU) as [R0 [HΓ0 Hch]].
  destruct (unit_chain HUU) as [R1 [HΓ1 Hch1]].
  assert (HPd : PER per_dmod) by typeclasses eauto.
  exists R', HΓ', (env_ext_mod U U R), (per_ctx_env_of_mod HΓ HUU).
  intros Γ'' R'' HΓ'' φ Hφ ρ ρ' Hρ.
  assert (HP'' : PER R'') by (eapply per_env_PER; exact HΓ'').
  pose proof (rel_sub_under_ctx_wk Hσj (rel_wk_under_ctx_intro HΓ'' HΓ' Hφ)) as Hσφ.
  destruct (Hσ _ _ HΓ'' _ Hφ _ _ Hρ) as [x1 x2 x3 x4 Hx1 Hx2 Hx3 Hx4 Hc].
  assert (Hρρ : R'' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  assert (Hρ'ρ' : R'' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
  pose proof (rel_wk_app _ _ _ Hφ _ _ Hρρ) as Hφρ.
  pose proof (rel_wk_app _ _ _ Hφ _ _ Hρ'ρ') as Hφρ'.
  pose proof (Hch1 _ _ HΓ'' _ _ (rel_sub_under_ctx_refl_left Hσφ) _ _ _ _ Hρρ Hx1 Hx1) as [C1 _].
  pose proof (Hch1 _ _ HΓ' _ _ (rel_sub_under_ctx_refl_left Hσj) _ _ _ _ Hφρ Hx2 Hx2) as [C2 _].
  pose proof (Hch _ _ HΓ' _ _ (rel_sub_under_ctx_refl_right Hσj) _ _ _ _ Hφρ' Hx3 Hx3) as (C3a & C3b & C3c).
  pose proof (Hch _ _ HΓ'' _ _ (rel_sub_under_ctx_refl_right Hσφ) _ _ _ _ Hρ'ρ' Hx4 Hx4) as (C4a & C4b & C4c).
  cbn [rel_chain] in C3c, C4c.
  assert (T3 : per_dmod (dm_local ⟪ φ ⟫ ρ' U'[σ']ᵘ nil) (dm_local x3 U nil))
    by (etransitivity; [ symmetry; exact C3c | symmetry; exact C3b ]).
  assert (T4 : per_dmod (dm_local ρ' U'[sb_wk σ' φ]ᵘ nil) (dm_local x4 U nil))
    by (etransitivity; [ symmetry; exact C4c | symmetry; exact C4b ]).
  apply (mk_rel_sub (x1 ↦ᵐ dm_local ρ U[sb_wk σ φ]ᵘ nil) (x2 ↦ᵐ dm_local ⟪ φ ⟫ ρ U[σ]ᵘ nil)
                    (x3 ↦ᵐ dm_local ⟪ φ ⟫ ρ' U'[σ']ᵘ nil) (x4 ↦ᵐ dm_local ρ' U'[sb_wk σ' φ]ᵘ nil)).
  - apply eval_sub_wk_extend_mod; [ exact Hx1 |]; cbn [modexp_wk]; rewrite gunit_wk_sub; constructor.
  - apply eval_sub_extend_mod; [ exact Hx2 | constructor ].
  - apply eval_sub_extend_mod; [ exact Hx3 | constructor ].
  - apply eval_sub_wk_extend_mod; [ exact Hx4 |]; cbn [modexp_wk]; rewrite gunit_wk_sub; constructor.
  - destruct Hc as (H12 & H23 & H34).
    unfold env_ext_mod; cbn.
    repeat split; assumption.
Qed.

(** The instance [B[Id,,ₘ⌜U⌝]] against a module [let] whose unit [U'] is
    equivalent to [U] and whose body [B'] is related to [B].  The four values
    are [⟦B[σ,,ₘ⌜U[σ]⌝]⟧ρ], [⟦B[Id,,ₘ⌜U⌝]⟧ρσ], [⟦B'⟧(ρ'σ' ↦ᵐ ⟦⌜U'⌝⟧ρ'σ')] and
    [⟦B'[q σ']⟧(ρ' ↦ᵐ ⟦⌜U'[σ']⌝⟧ρ')]; as for definitions, the links come from
    [B] along [σ,,ₘ⌜U[σ]⌝] and [Id,,ₘ⌜U⌝], from [B ≈ B'], and from [B'] along
    [q σ'], bridged at the heads, which the slot PER relates through the
    closures of the units. *)
Lemma rel_exp_let_mod_gen : forall {Γ U U' B B' C},
    Γ ⊨ᵘ U ≈ U' ->
    Γ ▹ₘ U ⊨ B ≈ B' : C ->
    Γ ⊨ B[Id ,,ₘ me_lit U] ≈ ℓₘ U' in B' : C[Id ,,ₘ me_lit U].
Proof.
  intros * (HU & _ & _) HB.
  pose proof (rel_modexp_refl_left HU) as HUl.
  pose proof (rel_modexp_refl_right HU) as HUr.
  pose proof HU as [R [HΓ _]].
  assert (HPR : PER R) by (eapply per_env_PER; exact HΓ).
  assert (HPd : PER per_dmod) by typeclasses eauto.
  pose proof (per_ctx_env_of_mod HΓ HUl) as HΓU.
  pose proof (per_ctx_env_of_mod HΓ HUr) as HΓU'.
  pose proof (rel_exp_under_ctx_refl_left HB) as HBl.
  pose proof (rel_exp_under_ctx_refl_right HB) as HBr.
  (** [B'] in the context of the right-hand unit. *)
  assert (HB'r : Γ ▹ₘ U' ⊨ B' ≈ B' : C).
  { eapply rel_exp_under_ctx_restrict; [ exact HΓU' | exact HΓU | | exact HBr ].
    intros ρ ρ' (Ht & T1 & _ & T3 & _).
    assert (Htt : R ρ↯ ρ↯) by (etransitivity; [ exact Ht | symmetry; exact Ht ]).
    assert (Ht't' : R ρ'↯ ρ'↯) by (etransitivity; [ symmetry; exact Ht | exact Ht ]).
    pose proof (unit_chain_at HU HΓ _ _ Htt) as E1.
    pose proof (unit_chain_at HU HΓ _ _ Ht't') as E2.
    repeat split; try assumption; etransitivity; try eassumption; symmetry; assumption. }
  destruct (rel_exp_under_ctx_simple_full_at HΓU HB) as [kX HX].
  destruct (rel_exp_under_ctx_simple_full_at HΓU HBl) as [kY HY].
  destruct (rel_exp_under_ctx_simple_full_at HΓU' HB'r) as [kZ HZ].
  pose proof HBl as [? [? [k HBlgen]]].
  pose proof HB'r as [? [? [k3 HB'gen]]].
  exists R, HΓ, k.
  intros Γ' R' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HPR' : PER R') by (eapply per_env_PER; exact HΓ').
  assert (Hρσ : R ρσ ρ'σ') by (eapply rel_sub_under_ctx_at'; eassumption).
  pose proof (rel_sub_under_ctx_refl_right Hσj) as Hσ'σ'.
  (** *** The Instances *)
  pose proof (rel_sub_under_ctx_extend_mod Hσj HUl) as Hτ.
  pose proof (rel_sub_under_ctx_extend_mod (rel_sub_id (ex_intro _ _ HΓ)) HUl) as Hid.
  rewrite gunit_sub_id in Hid.
  destruct (HBlgen _ _ HΓ' _ _ Hτ _ _ _ _ Hρ
              (eval_sub_extend_mod _ _ _ _ _ Hev (eval_me_lit _ _ _ _))
              (eval_sub_extend_mod _ _ _ _ _ Hev' (eval_me_lit _ _ _ _)))
    as [R1 [[c1 cA2 cA3 c4 Hc1 HcA2 HcA3 Hc4 Hc1chain] [w1 bA2 bA3 w4x Hw1 HbA2 HbA3 Hw4 Hw1chain]]].
  destruct (HBlgen _ _ HΓ _ _ Hid _ _ _ _ Hρσ
              (eval_sub_single_mod _ _ _ (eval_me_lit _ _ _ _)) (eval_sub_single_mod _ _ _ (eval_me_lit _ _ _ _)))
    as [R2 [[c2 cB2 cB3 c3 Hc2 HcB2 HcB3 Hc3 Hc2chain] [w2 bB2 bB3 w3x Hw2 HbB2 HbB3 Hw3 Hw2chain]]].
  (** *** The Bridges at the Substituted Environments *)
  destruct (unit_chain HUl) as [R5 [HΓ5 HchU]].
  destruct (unit_chain HUr) as [R6 [HΓ6 HchU']].
  assert (Hρρ : R' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  assert (Hρ'ρ' : R' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
  assert (Hσσ : R ρσ ρσ) by (etransitivity; [ exact Hρσ | symmetry; exact Hρσ ]).
  assert (Hσ'σ'' : R ρ'σ' ρ'σ') by (etransitivity; [ symmetry; exact Hρσ | exact Hρσ ]).
  pose proof (HchU _ _ HΓ' _ _ (rel_sub_under_ctx_refl_left Hσj) _ _ _ _ Hρρ Hev Hev) as (Ty1 & Ty2 & _).
  pose proof (HchU' _ _ HΓ' _ _ Hσ'σ' _ _ _ _ Hρ'ρ' Hev' Hev') as (Tz1 & Tz2 & _).
  pose proof (unit_chain_at HU HΓ _ _ Hσ'σ'') as Tx.
  assert (HY1 : env_ext_mod U U R (ρσ ↦ᵐ dm_local ρ U[σ]ᵘ nil) (ρσ ↦ᵐ dm_local ρσ U nil))
    by (unfold env_ext_mod; cbn; repeat split; assumption).
  assert (HX1 : env_ext_mod U U R (ρσ ↦ᵐ dm_local ρσ U nil) (ρ'σ' ↦ᵐ dm_local ρ'σ' U' nil)).
  { unfold env_ext_mod; cbn; repeat split; try assumption; symmetry; exact Tx. }
  destruct (HY _ _ HY1) as [cy1 [cy2 [RY [Hcy1 [Hcy2 [HRY [by1 [by2 [Hby1 [Hby2 Hby]]]]]]]]]].
  destruct (HX _ _ HX1) as [cx1 [cx2 [RX [Hcx1 [Hcx2 [HRX [bx1 [bx2 [Hbx1 [Hbx2 Hbx]]]]]]]]]].
  (** *** The Right Commutation *)
  pose proof (per_ctx_env_of_mod_sub HΓ' Hσ'σ' HUr) as HΓ'U'.
  assert (Hm44 : per_dmod (dm_local ρ' U'[σ']ᵘ nil) (dm_local ρ' U'[σ']ᵘ nil))
    by (etransitivity; [ exact Tz1 | symmetry; exact Tz1 ]).
  assert (Hpair : env_ext_mod U'[σ']ᵘ U'[σ']ᵘ R' (ρ' ↦ᵐ dm_local ρ' U'[σ']ᵘ nil) (ρ' ↦ᵐ dm_local ρ' U'[σ']ᵘ nil))
    by (unfold env_ext_mod; cbn; repeat split; assumption).
  destruct (rel_sub_q_entry HΓ'U' HΓ Hσ'σ' _ _ Hpair Hev') as [t [Hqt Htr]].
  pose proof (rel_sub_under_ctx_q_mod Hσ'σ' HUr) as Hq.
  destruct (HB'gen _ _ HΓ'U' _ _ Hq _ _ _ _ Hpair Hqt Hqt)
    as [R3 [[e1 e2 e3 e4 He1 He2 He3 He4 He1chain] [v4 f2 f3 v4' Hv4 Hf2 Hf3 Hv4' Hv4chain]]].
  pose proof (unit_chain_at HUr HΓ _ _ (symmetry Htr)) as Tt.
  assert (HZ1 : env_ext_mod U' U' R (ρ'σ' ↦ᵐ dm_local ρ'σ' U' nil)
                  (env_entry (ρ' ↦ᵐ dm_local ρ' U'[σ']ᵘ nil) 0 :: t)).
  { assert (Tt' : per_dmod (dm_local ρ' U'[σ']ᵘ nil) (dm_local t U' nil)) by (etransitivity; [ exact Tz1 | exact Tt ]).
    assert (Tr' : per_dmod (dm_local ρ'σ' U' nil) (dm_local ρ'σ' U' nil))
      by (etransitivity; [ symmetry; exact Tz1 | exact Tz1 ]).
    unfold env_ext_mod; cbn; repeat split; try assumption; symmetry; exact Htr. }
  destruct (HZ _ _ HZ1) as [cz1 [cz2 [RZ [Hcz1 [Hcz2 [HRZ [bz1 [bz2 [Hbz1 [Hbz2 Hbz]]]]]]]]]].
  functional_eval_rewrite_clear.
  (** *** One Element PER *)
  assert (Hp1 : DF c1 ≈ cA2 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp1' : DF cA2 ≈ cA3 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp14 : DF c1 ≈ c4 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp2 : DF cB2 ≈ c2 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp2' : DF cB2 ≈ cB3 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp23 : DF c2 ≈ c3 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp3 : DF e1 ≈ e2 ∈ per_univ_elem k3 ↘ R3) by pairwise.
  assert (Ht1 : Dom w1 ≈ bA2 ∈ R1) by pairwise.
  assert (Ht2 : Dom w2 ≈ bB2 ∈ R2) by pairwise.
  assert (Ht3 : Dom f2 ≈ v4 ∈ R3) by pairwise.
  assert (E1 : R1 <~> RY) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hp1' HRY).
  assert (E2 : R2 <~> RY) by exact (per_univ_elem_cross_irrel _ _ _ _ _ _ _ Hp2' HRY).
  assert (E3 : R2 <~> RX) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hp2' HRX).
  assert (E4 : RZ <~> RX) by exact (per_univ_elem_cross_irrel _ _ _ _ _ _ _ HRZ HRX).
  assert (E5 : R3 <~> RZ) by exact (per_univ_elem_left_irrel _ _ _ _ _ _ _ Hp3 HRZ).
  assert (F1 : R1 <~> R2) by (rewrite E1, E2; reflexivity).
  assert (FY : RY <~> R2) by (rewrite E2; reflexivity).
  assert (FX : RX <~> R2) by (rewrite E3; reflexivity).
  assert (FZ : RZ <~> R2) by (rewrite E4, E3; reflexivity).
  assert (F3 : R3 <~> R2) by (rewrite E5, FZ; reflexivity).
  apply (fun H => per_univ_elem_resp_iff H F1) in Hp1, Hp14.
  apply F1 in Ht1.
  apply (fun H => per_univ_elem_resp_iff H FY) in HRY.
  apply FY in Hby.
  apply FX in Hbx.
  apply FZ in Hbz.
  apply F3 in Ht3.
  assert (PER R2) by (eapply per_elem_PER; exact Hp23).
  exists R2; split.
  - apply (mk_rel_exp c1 c2 c3 c4); try eassumption.
    + rewrite exp_sub_extend_mod_sub; exact Hc1.
    + rewrite exp_sub_extend_mod_sub; exact Hc4.
    + assert (Hc12 : DF c1 ≈ c2 ∈ per_univ_elem k ↘ R2)
        by (eapply per_univ_trans; [ eapply per_univ_trans; [ exact Hp1 | exact HRY ] | exact Hp2 ]).
      apply rel_chain_4; [ exact Hc12 | exact Hp23 | solve_per ].
  - apply (mk_rel_exp w1 w2 bx2 v4); try eassumption.
    + rewrite exp_sub_extend_mod_sub; exact Hw1.
    + apply eval_exp_let_mod; exact Hbx2.
    + cbn [exp_sub bnd_sub]; apply eval_exp_let_mod; exact Hv4.
    + apply rel_chain_4; solve_per.
Qed.

(** [ζ] for modules. *)
Corollary rel_exp_let_mod_zeta : forall {Γ U B C},
    Γ ⊨ᵘ U ≈ U ->
    Γ ▹ₘ U ⊨ B : C ->
    Γ ⊨ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : C[Id ,,ₘ me_lit U].
Proof.
  intros * HU HB.
  apply rel_exp_under_ctx_sym.
  exact (rel_exp_let_mod_gen HU HB).
Qed.

(** Congruence: both sides are related to the instance [B[Id,,ₘ⌜U⌝]]. *)
Corollary rel_exp_let_mod_cong : forall {Γ U U' B B' C},
    Γ ⊨ᵘ U ≈ U' ->
    Γ ▹ₘ U ⊨ B ≈ B' : C ->
    Γ ⊨ ℓₘ U in B ≈ ℓₘ U' in B' : C[Id ,,ₘ me_lit U].
Proof.
  intros * HU HB.
  pose proof HU as (HU0 & HsU & _).
  eapply rel_exp_under_ctx_trans; [| exact (rel_exp_let_mod_gen HU HB) ].
  apply rel_exp_under_ctx_sym.
  exact (rel_exp_let_mod_gen (U' := U) (conj (rel_modexp_refl_left HU0) (conj HsU HsU))
           (rel_exp_under_ctx_refl_left HB)).
Qed.

Corollary valid_exp_let_mod : forall {Γ U B C},
    Γ ⊨ᵘ U ≈ U ->
    Γ ▹ₘ U ⊨ B : C ->
    Γ ⊨ ℓₘ U in B : C[Id ,,ₘ me_lit U].
Proof. intros * HU HB; exact (rel_exp_let_mod_cong HU HB). Qed.

(** What the gluing model needs of an instance by a literal:
    [⟦B[Id,,ₘ⌜U⌝]⟧ρ] and [⟦B⟧(ρ ↦ᵐ ⟦⌜U⌝⟧ρ)] are related. *)
Lemma per_univ_of_instance_mod : forall {Γ U B k env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ᵘ U ≈ U ->
    Γ ▹ₘ U ⊨ B : Typeω@k ->
    forall ρ,
      Dom ρ ≈ ρ ∈ env_relΓ ->
      exists a b,
        ⟦ B[Id ,,ₘ me_lit U] ⟧ ρ ↘ a /\ ⟦ B ⟧ (ρ ↦ᵐ dm_local ρ U nil) ↘ b /\
          Dom a ≈ a ∈ per_univ k /\ Dom a ≈ b ∈ per_univ k.
Proof.
  intros * HΓ (HU & _ & _) HB * Hρ.
  pose proof (rel_sub_under_ctx_extend_mod (rel_sub_id (ex_intro _ _ HΓ)) HU) as Hid.
  rewrite gunit_sub_id in Hid.
  pose proof (rel_exp_of_typ_inversion HB) as [env_relΓU [HΓU HBgen]].
  destruct (HBgen _ _ HΓ _ _ Hid _ _ _ _ Hρ
                  (eval_sub_single_mod _ _ _ (eval_me_lit _ _ _ _))
                  (eval_sub_single_mod _ _ _ (eval_me_lit _ _ _ _)))
    as [t1 t2 t3 t4 Ht1 Ht2 Ht3 Ht4 Hchain].
  destruct Hchain as [Ht12 _].
  exists t1, t2.
  do 2 (split; [ eassumption |]).
  split; [| eassumption ].
  etransitivity; [ eassumption | symmetry; eassumption ].
Qed.

(** ** Members of Applied Modules

    A member of an applied module evaluates exactly as its root's member
    applied to the arguments, before and after any substitution. *)

Lemma rel_exp_under_ctx_eval_iff_l : forall {Γ A M N N'},
    (forall σ ρ r, ⟦ M[σ] ⟧ ρ ↘ r <-> ⟦ N[σ] ⟧ ρ ↘ r) ->
    (forall ρ r, ⟦ M ⟧ ρ ↘ r <-> ⟦ N ⟧ ρ ↘ r) ->
    Γ ⊨ N ≈ N' : A ->
    Γ ⊨ M ≈ N' : A.
Proof.
  intros * Hs H0 [R [HΓ [i HN]]].
  exists R, HΓ, i.
  intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HN _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [E [HT [m1 m2 m3 m4 H1 H2 H3 H4 Hc]]].
  exists E; split; [ exact HT |].
  econstructor; [ apply Hs; exact H1 | apply H0; exact H2 | exact H3 | exact H4 | exact Hc ].
Qed.

Lemma rel_exp_mem_app : forall {Γ H x R args pre A N'},
    modexp_spine H = (R, args, pre) ->
    Γ ⊨ apps (member_ref R (pre ++ x :: nil)) args ≈ N' : A ->
    Γ ⊨ a_mem H x ≈ N' : A.
Proof.
  intros * Hs HN.
  eapply rel_exp_under_ctx_eval_iff_l; [ | | exact HN ].
  - intros σ ρ r; exact (eval_mem_apps_sub _ _ _ _ _ σ ρ r Hs).
  - intros ρ r; exact (eval_mem_apps _ _ _ _ _ _ _ _ _ Hs).
Qed.

Corollary valid_exp_mem_app : forall {Γ H x R args pre A},
    modexp_spine H = (R, args, pre) ->
    Γ ⊨ apps (member_ref R (pre ++ x :: nil)) args : A ->
    Γ ⊨ a_mem H x : A.
Proof.
  intros * Hs HN.
  pose proof (rel_exp_mem_app Hs HN) as H1.
  eapply rel_exp_under_ctx_trans; [ exact H1 | apply rel_exp_under_ctx_sym, H1 ].
Qed.

(** ** Environments of Arguments *)

Lemma env_args_rev : forall ρ xs, env_args ρ xs = List.rev (List.map de_term xs) ++ ρ.
Proof.
  intros ρ xs; revert ρ; induction xs as [| x xs IH]; intros; [ reflexivity |].
  cbn [env_args List.fold_left List.map List.rev]; change (List.fold_left extend_env xs (ρ ↦ x)) with (env_args (ρ ↦ x) xs).
  rewrite IH, <- List.app_assoc; reflexivity.
Qed.

Lemma skipn_env_args : forall ρ xs, List.skipn (List.length xs) (env_args ρ xs) = ρ.
Proof.
  intros; rewrite env_args_rev.
  rewrite List.skipn_app, List.skipn_all2 by (rewrite List.length_rev, List.length_map; lia).
  rewrite List.length_rev, List.length_map, Nat.sub_diag; reflexivity.
Qed.

Lemma eval_wk_shiftn : forall n ρ, ⟪wk_shiftn n⟫ ρ = List.skipn n ρ.
Proof.
  intros n ρ.
  assert (Hm : wk_mono (wk_shiftn n)) by (intros x y Hxy; cbn; lia).
  assert (Hl : wk_len (wk_shiftn n) (List.length ρ) = List.length (List.skipn n ρ)).
  { apply nat_eq_of_lt_iff; intros x; rewrite wk_len_spec by exact Hm; rewrite List.length_skipn; cbn; lia. }
  apply env_ext; [ rewrite eval_wk_length; exact Hl |].
  intros x Hx; rewrite eval_wk_length, Hl in Hx.
  rewrite eval_wk_var by (rewrite Hl; exact Hx).
  rewrite !env_entry_nth, List.nth_skipn; cbn; f_equal; lia.
Qed.

Lemma eval_wk_shiftn_args : forall ρ xs, ⟪wk_shiftn (List.length xs)⟫ (env_args ρ xs) = ρ.
Proof. intros; rewrite eval_wk_shiftn; apply skipn_env_args. Qed.

(** ** The [n]-fold Shift *)

Lemma wk_mono_shiftn : forall n, wk_mono (wk_shiftn n).
Proof. intros n x y H; cbn; lia. Qed.

#[export] Instance WkMono_shiftn (n : nat) : WkMono (wk_shiftn n) := wk_mono_shiftn n.

Lemma rel_wk_shiftn : forall Ψ Γ RΨ RΓ,
    EF Ψ ++ Γ ≈ Ψ ++ Γ ∈ per_ctx_env ↘ RΨ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    rel_wk (wk_shiftn (List.length Ψ)) RΨ RΓ.
Proof.
  intros * HΨ HΓ; split; [ intros x y Hxy; cbn; lia |].
  revert RΨ HΨ; induction Ψ as [| e Ψ IH]; intros RΨ HΨ ρ ρ' Hρ; cbn [List.app List.length] in *.
  - rewrite !eval_wk_shiftn; cbn [List.skipn].
    assert (E : RΨ <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption). apply E; exact Hρ.
  - destruct (rel_wk_shift_tail HΨ) as (R' & HR' & Hsh).
    pose proof (Hsh _ _ Hρ) as Ht; rewrite !eval_wk_shift in Ht.
    rewrite !eval_wk_shiftn; cbn [List.skipn].
    destruct ρ as [| d ρ], ρ' as [| d' ρ']; cbn [drop_env List.tl] in Ht;
      (pose proof (IH _ HR' _ _ Ht) as H; rewrite !eval_wk_shiftn in H; try exact H);
      rewrite List.skipn_nil in *; exact H.
Qed.

Lemma rel_wk_under_ctx_shiftn : forall Ψ Γ, ⊨ Ψ ++ Γ -> Ψ ++ Γ ⊨w (wk_shiftn (List.length Ψ)) : Γ.
Proof.
  intros * H.
  destruct (sem_ctx_per_ctx_env H) as [R HR].
  destruct (sem_ctx_per_ctx_env (sem_ctx_app_r _ _ H)) as [RΓ HΓ].
  eapply rel_wk_under_ctx_intro; [ exact HR | exact HΓ | exact (rel_wk_shiftn _ _ _ _ HR HΓ) ].
Qed.

End Fixed_GCtx.
