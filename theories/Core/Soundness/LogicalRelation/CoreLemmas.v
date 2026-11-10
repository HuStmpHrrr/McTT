From Stdlib Require Import Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Corollaries Substitution.
From Mctt.Core.Syntactic.Levels Require Import LevelEq.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Records Require Import Typing.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndCanon.
From Mctt.Core.Completeness.Consequences Require Import AnnotatedUpto.
From Mctt.Core.Soundness.LogicalRelation Require Import CoreTactics Definitions.
From Mctt.Core.Soundness.Weakening Require Export Lemmas.
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The same lemmas for [glu_lvl], which is the readback clause of a neutral at
    [Level]. *)
Lemma glu_lvl_escape : forall Γ M a n,
    Dom a ≈ a ∈ per_lvl ->
    glu_lvl n Γ M a ->
    ⊢ Γ ->
    Γ ⊢ M : Level@n.
Proof.
  intros * Hper H HΓ.
  assert (Γ ⊢ᵏ wk_id : Γ) by mauto 2.
  destruct (Hper (length Γ)) as [L HL _ _].
  assert (Γ ⊢ M[wk_id]ʷ ≈ nf_lvl_of L : Level@n) as HM by (eapply H; eassumption).
  rewrite exp_wk_id in HM.
  gen_presups.
  mauto.
Qed.

Hint Resolve glu_lvl_escape : mctt.

(** The sort of a glued level moves up: the readback equation does, by
    subsumption between the types of levels. *)
Lemma glu_lvl_sort_le : forall Γ M a m n,
    m <= n ->
    glu_lvl m Γ M a ->
    glu_lvl n Γ M a.
Proof.
  intros * Hmn H Δ φ L Hφ Hr.
  assert (⊢ Δ) by (eapply kripke_dom; eassumption).
  destruct (H _ _ _ Hφ Hr) as [Heq Hws]; split.
  - eapply wf_exp_eq_subtyp'; [ exact Heq | apply wf_subtyp_level; assumption ].
  - destruct L; cbn in Hws |- *; try contradiction.
    destruct Hws; split; [ lia | eapply level_atoms_well_scoped_mono; eassumption ].
Qed.

Lemma glu_lvl_resp_ctxsub : forall Γ M a n Δ,
    glu_lvl n Γ M a ->
    Δ ⊆ Γ ->
    glu_lvl n Δ M a.
Proof.
  intros * H ? Δ' φ L **; mauto 4.
Qed.

Hint Resolve glu_lvl_resp_ctxsub : mctt.

Lemma glu_lvl_resp_exp_eq : forall Γ M a n,
    glu_lvl n Γ M a ->
    forall M',
    Γ ⊢ M ≈ M' : Level@n ->
    glu_lvl n Γ M' a.
Proof.
  intros * H * ? Δ φ L Hφ Hr.
  destruct (H _ _ _ Hφ Hr) as [Heq Hws]; split; [| exact Hws ].
  transitivity M[φ]ʷ; mauto 4.
Qed.

#[local]
Hint Resolve glu_lvl_resp_exp_eq : mctt.

(** ** Cumulativity of an Element of a Small Universe

    An element of a small universe is a type of that universe [Type⟨t⟩], and
    its type-level gluing is at the ambient large universe.  These two lemmas
    are where the gluing relies on cumulativity ([wf_subtyp_small_large]):
    they move the element's typing and its equations from [Type⟨t⟩] to every
    large universe. *)
Lemma suniv_elem_large : forall Γ M A t j k,
    Γ ⊢ M : A ->
    Γ ⊢ A ≈ Type⟨t⟩ : Typeω@j ->
    Γ ⊢ M : Typeω@k.
Proof.
  intros * HM HA.
  assert (Γ ⊢ Type⟨t⟩ : Typeω@j) by (gen_presups; eassumption).
  assert (exists n, Γ ⊢ t : Level@n) as [n' Ht] by (eapply wf_univ_lvl_inversion; eassumption).
  eapply wf_exp_subtyp'; [ eapply wf_conv'; eassumption | eapply wf_subtyp_small_large; mauto 3 ].
Qed.

Lemma suniv_elem_eq_large : forall Γ M M' A t j k,
    Γ ⊢ M ≈ M' : A ->
    Γ ⊢ A ≈ Type⟨t⟩ : Typeω@j ->
    Γ ⊢ M ≈ M' : Typeω@k.
Proof.
  intros * HM HA.
  assert (Γ ⊢ Type⟨t⟩ : Typeω@j) by (gen_presups; eassumption).
  assert (exists n, Γ ⊢ t : Level@n) as [n' Ht] by (eapply wf_univ_lvl_inversion; eassumption).
  eapply wf_exp_eq_subtyp';
    [ eapply wf_exp_eq_conv'; eassumption | eapply wf_subtyp_small_large; mauto 3 ].
Qed.

(** A glued small universe is the universe at a level term glued to the level
    value.  As an introduction lemma this is what every proof that moves such
    a type needs: the term is kept and the equation composed, and it is a hint
    so that the shared scripts of the gluing lemmas reach it. *)
Lemma suniv_glu_typ_pred_intro : forall l U Γ A t n,
    glu_lvl n Γ t l ->
    Γ ⊢ A ≈ Type⟨t⟩ : U ->
    suniv_glu_typ_pred l U Γ A.
Proof. intros; econstructor; eassumption. Qed.

(** It is deliberately not a hint: its conclusion is an existential whose
    witness the search cannot guess, and as a hint it also fires on the goals
    of the other universe clauses, whose predicate is an evar. *)

Lemma glu_lvl_readback : forall Γ M a n,
    glu_lvl n Γ M a ->
    forall Δ φ M',
      Δ ⊢ᵏ φ : Γ ->
      Rnf ⇓ Levelᵈ a in length Δ ↘ M' ->
      Δ ⊢ M[φ]ʷ ≈ M' : Level@n.
Proof.
  intros * H * Hφ Hr; exact (proj1 (H _ _ _ Hφ Hr)).
Qed.

(** The readback of a glued level is a canonical level of its sort. *)
Lemma glu_lvl_well_scoped_readback : forall Γ M a n,
    glu_lvl n Γ M a ->
    forall Δ φ M',
      Δ ⊢ᵏ φ : Γ ->
      Rnf ⇓ Levelᵈ a in length Δ ↘ M' ->
      nf_lvl_well_scoped n Δ M'.
Proof.
  intros * H * Hφ Hr; exact (proj2 (H _ _ _ Hφ Hr)).
Qed.

(** A literal level of a tier at most [n] is glued to its value: its readback
    is itself. *)
Lemma glu_lvl_lit : forall Γ o n,
    fst o <= n ->
    ⊢ Γ ->
    glu_lvl n Γ (𝕃ᵒ o) (domain_level_lit o).
Proof.
  intros * Ho HΓ Δ φ L Hφ Hr.
  assert (⊢ Δ) by (eapply kripke_dom; eassumption).
  assert (L = nf_lvl_of (lvl_lit o)) as -> by (eapply functional_read_nf; [ exact Hr | apply read_nf_domain_level_lit ]).
  cbn; split; [ apply wf_exp_eq_llit_cong; assumption | split; [ exact Ho | exact I ] ].
Qed.

(** ** The Elements of an Inductive Type *)

Lemma nonrec_prefix_pre : forall tr gs vs gs1 g gs2,
    tele_rel tr (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs) -> List.length vs = List.length gs ->
    gs = gs1 ++ g :: gs2 ->
    tele_prefix_rel tr (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
      (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)).
Proof.
  intros * H Hl Heq.
  assert (Hnv : List.firstn (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs vs) = nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)).
  { rewrite <- (List.firstn_skipn (List.length gs1) vs) at 1.
    rewrite Heq at 1.
    rewrite nonrec_arg_vals_app by (rewrite List.length_firstn; subst; rewrite List.length_app in Hl; cbn in Hl; lia).
    rewrite firstn_app_exact by (apply length_nonrec_arg_vals; rewrite List.length_firstn; subst; rewrite List.length_app in Hl; cbn in Hl; lia).
    reflexivity. }
  rewrite <- Hnv; apply tele_prefix_rel_of_full with (T := cargs_nonrec gs); [ exact H |].
  subst; rewrite cargs_nonrec_app, List.length_app; lia.
Qed.

Lemma nonrec_firstn : forall gs gs1 g gs2 vs, gs = gs1 ++ g :: gs2 -> List.length vs = List.length gs ->
    List.firstn (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs vs) = nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs).
Proof.
  intros * Heq Hl.
  rewrite <- (List.firstn_skipn (List.length gs1) vs) at 1.
  rewrite Heq at 1.
  rewrite nonrec_arg_vals_app by (rewrite List.length_firstn; subst; rewrite List.length_app in Hl; cbn in Hl; lia).
  rewrite firstn_app_exact by (apply length_nonrec_arg_vals; rewrite List.length_firstn; subst; rewrite List.length_app in Hl; cbn in Hl; lia).
  reflexivity.
Qed.

Lemma nonrec_nth_arg : forall gs gs1 r A gs2 vs v, gs = gs1 ++ ca_arg r A :: gs2 -> List.length vs = List.length gs ->
    List.nth_error vs (List.length gs1) = Some v ->
    List.nth_error (nonrec_arg_vals gs vs) (List.length (cargs_nonrec gs1)) = Some v.
Proof.
  intros * Heq Hl Hv; subst gs.
  rewrite <- (List.firstn_skipn (List.length gs1) vs) in Hv |- *.
  assert (Hl1 : List.length (List.firstn (List.length gs1) vs) = List.length gs1)
    by (rewrite List.length_firstn; rewrite List.length_app in Hl; cbn in Hl; lia).
  rewrite nonrec_arg_vals_app by exact Hl1.
  rewrite List.nth_error_app2 in Hv by lia; rewrite Hl1 in Hv.
  replace (List.length gs1 - List.length gs1) with 0 in Hv by lia.
  rewrite List.nth_error_app2 by (rewrite length_nonrec_arg_vals by exact Hl1; lia).
  rewrite length_nonrec_arg_vals by exact Hl1.
  replace (List.length (cargs_nonrec gs1) - List.length (cargs_nonrec gs1)) with 0 by lia.
  destruct (List.skipn (List.length gs1) vs) as [| v0 ws]; cbn in Hv |- *; [ discriminate | exact Hv ].
Qed.

(** A declared member's type at its parameters, and the position of a
    declared member among the members. *)
Lemma im_ty_at_decl : forall p k Mk pm Us Ns, im_head Mk = mh_decl pm ->
    im_ty_at p k Mk Us Ns = apps (a_ind p k) (Us ++ Ns).
Proof. intros * Hh; unfold im_ty_at, im_ref, im_pre; rewrite Hh; reflexivity. Qed.

Lemma decl_member_lt : forall Γ p D k Mk pm, ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D ->
    ind_member D k = Some Mk -> im_head Mk = mh_decl pm -> k < ind_ndecl D.
Proof.
  intros * HΓ Hl HM Hh; destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD _].
  apply (decl_typed_order _ _ _ HD _ _ HM); unfold im_is_decl; rewrite Hh; reflexivity.
Qed.

(** The two premises of a gluing clause on a family, read at every
    position: its types evaluate, and their values glue. *)
Lemma ind_case_N_helper : forall D ups (X : nat -> nat -> list domain -> Prop), group_structure D ->
    (forall m Mm j κ A vs, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass κ A) ->
       tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
       exists b, ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm)) vs ↘ b) ->
    (forall m Mm j κ A vs b, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass κ A) ->
       tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
       ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm)) vs ↘ b -> X m j vs) ->
    forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
      X m j vs.
Proof.
  intros * Hass Hev HX m Mm j vs HM Hj Hp.
  destruct (nparams_lt_ass D m Mm j Hass HM ltac:(rewrite List.length_rev; exact Hj)) as (κ & A & HA).
  destruct (Hev _ _ _ _ _ _ HM HA Hp) as [b Hb]; exact (HX _ _ _ _ _ _ _ HM HA Hp Hb).
Qed.

Lemma ind_case_A_helper : forall D ups (X : nat -> list domain -> String.string -> nat -> list domain -> Prop),
    (forall m Mm ms c gs j A vs, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
       tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
       exists b, ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs) ↘ b) ->
    (forall m Mm ms c gs j A vs b, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
       tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
       ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs) ↘ b -> X m ms c j vs) ->
    forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
      j < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs -> X m ms c j vs.
Proof.
  intros * Hev HX * HM Hms Hcon Hj Hp.
  destruct (nth_error_lt_some' (cargs_nonrec gs) j Hj) as [A HA].
  destruct (Hev _ _ _ _ _ _ _ _ HM Hms Hcon HA Hp) as [b Hb]; exact (HX _ _ _ _ _ _ _ _ _ HM Hms Hcon HA Hp Hb).
Qed.

Lemma map_wk_wk : forall (Ps : list exp) φ ψ,
    List.map (fun P => P[ψ]ʷ) (List.map (fun P => P[φ]ʷ) Ps) = List.map (fun P => P[φ ⊙ ψ]ʷ) Ps.
Proof. intros; rewrite List.map_map; apply List.map_ext; intros; apply exp_wk_wk. Qed.

(** ** Readback Equations Move up to Proofs, to a Typed Annotation

    A readback equation holds of a normal form equal to the readback up to
    proofs whose annotation is typed: the two annotations are then equal
    ([nf_annotate_proofs_upto]).  The hypothesis is what excludes a value
    whose readback holds a junk proof (see [glu_nf_eq]): the gluing moves
    only to values whose own readback is typed. *)
Lemma glu_nf_eq_upto : forall Γ M W W' A, nf_eq_upto_proofs W W' -> glu_nf_eq Γ M W A ->
    (exists T, Γ ⊢ nf_annotate_proofs W' : T) -> glu_nf_eq Γ M W' A.
Proof.
  unfold glu_nf_eq; intros * E H HW'.
  etransitivity; [ exact H | exact (nf_annotate_proofs_upto _ _ _ _ _ _ (presup_exp_eq_right H) HW' E) ].
Qed.

Lemma glu_ne_eq_upto : forall Γ M W W' A, ne_eq_upto_proofs W W' -> glu_ne_eq Γ M W A ->
    (exists T, Γ ⊢ ne_annotate_proofs W' : T) -> glu_ne_eq Γ M W' A.
Proof.
  unfold glu_ne_eq; intros * E H HW'.
  etransitivity; [ exact H | exact (proj2 nf_ne_annotate_proofs_upto _ _ _ _ E _ _ (presup_exp_eq_right H) HW') ].
Qed.

(** An instance of a telescope at a position exists whenever it does at
    another list of the same length: it depends only on the shape. *)
Lemma tele_insts_aux_nth_length : forall Δr σ σ' Ms Ms' k A, List.length Ms = List.length Ms' ->
    List.nth_error (tele_insts_aux Δr σ Ms) k = Some A -> exists A', List.nth_error (tele_insts_aux Δr σ' Ms') k = Some A'.
Proof.
  induction Δr as [| e Δr IH]; intros * L H; [ destruct k; discriminate |].
  destruct e; destruct Ms as [| M Ms], Ms' as [| M' Ms']; cbn in L, H |- *; try (destruct k; discriminate); try (cbn in L; lia).
  all: destruct k as [| k]; cbn in H |- *; [ eexists; reflexivity |].
  all: injection L as L; exact (IH _ _ _ _ _ _ L H).
Qed.

(** The equations of a list move to a list equal up to proofs whose own
    equations hold (a witness at the target), as [glu_nf_eq_upto]. *)
Lemma glu_nfs_eq_at_upto : forall Γ T Ms Ms' Ws Ws', nfs_eq_upto_proofs Ws Ws' -> glu_nfs_eq_at Γ T Ms Ws ->
    glu_nfs_eq_at Γ T Ms' Ws' -> glu_nfs_eq_at Γ T Ms Ws'.
Proof.
  unfold glu_nfs_eq_at; intros * E [L H] [L' H'].
  pose proof (nfs_eq_upto_proofs_length _ _ E) as LW.
  rewrite !List.length_map in L, L'.
  split; [ rewrite !List.length_map; congruence |].
  intros k X Y A HX HY HA.
  rewrite !List.nth_error_map in HY.
  destruct (List.nth_error Ws' k) as [W' |] eqn:HW'; cbn in HY; [| discriminate ]; injection HY as <-.
  assert (Hk : k < List.length Ws') by (apply List.nth_error_Some; congruence).
  destruct (List.nth_error Ws k) as [W |] eqn:HW; [| apply List.nth_error_None in HW; lia ].
  destruct (List.nth_error Ms' k) as [X' |] eqn:HX'; [| apply List.nth_error_None in HX'; lia ].
  destruct (nfs_eq_upto_proofs_nth _ _ _ _ E HW) as (W'' & HW'' & EW).
  rewrite HW' in HW''; injection HW'' as <-.
  assert (HXW : Γ ⊢ X ≈ nf_annotate_proofs W : A) by (apply (H k); [ exact HX | rewrite !List.nth_error_map, HW; reflexivity | exact HA ]).
  (** The target's own equation types its annotation *)
  destruct (tele_insts_aux_nth_length (List.rev T) Id Id Ms Ms' k A ltac:(lia) HA) as [A' HA'].
  assert (HXW' : Γ ⊢ X' ≈ nf_annotate_proofs W' : A') by (apply (H' k); [ exact HX' | rewrite !List.nth_error_map, HW'; reflexivity | exact HA' ]).
  etransitivity; [ exact HXW |].
  exact (nf_annotate_proofs_upto _ _ _ _ _ _ (presup_exp_eq_right HXW) (ex_intro _ _ (presup_exp_eq_right HXW')) EW).
Qed.

(** The readback equations move along an equal term. *)
Lemma glu_nf_eq_exp_eq : forall Γ M M' W A, Γ ⊢ M' ≈ M : A -> glu_nf_eq Γ M W A -> glu_nf_eq Γ M' W A.
Proof. unfold glu_nf_eq; intros * E H; etransitivity; [ exact E | exact H ]. Qed.

Lemma glu_ne_eq_exp_eq : forall Γ M M' W A, Γ ⊢ M' ≈ M : A -> glu_ne_eq Γ M W A -> glu_ne_eq Γ M' W A.
Proof. unfold glu_ne_eq; intros * E H; etransitivity; [ exact E | exact H ]. Qed.

(** A proposition glued at its value, along an equation in [Prop]. *)
Lemma prop_glu_typ_pred_resp_exp_eq : forall a Γ A A',
    Γ ⊢ A ® prop_glu_typ_pred a -> Γ ⊢ A ≈ A' : Propₘ -> Γ ⊢ A' ® prop_glu_typ_pred a.
Proof.
  intros * [HA HR] HAA; split; [ exact (presup_exp_eq_right HAA) |].
  intros Δ φ W Hφ HW; eapply glu_nf_eq_exp_eq; [| exact (HR _ _ _ Hφ HW) ].
  symmetry; eapply kripke_preserves_prop_eq; eassumption.
Qed.

(** The same along a weakening. *)
Lemma prop_glu_typ_pred_wk : forall a Γ A Δ φ,
    Γ ⊢ A ® prop_glu_typ_pred a -> Δ ⊢ᵏ φ : Γ -> Δ ⊢ A[φ]ʷ ® prop_glu_typ_pred a.
Proof.
  intros * [HA HR] Hφ; split; [ eapply kripke_preserves_prop; eassumption |].
  intros Δ' ψ W Hψ HW; rewrite exp_wk_wk; apply HR; [ mauto 3 | exact HW ].
Qed.

(** Conversion along an equation of types at the sort of a kind. *)
Lemma wf_exp_eq_conv_kind : forall Γ M M' A A' κ i,
    Γ ⊢ M ≈ M' : A -> Γ ⊢ A ≈ A' : abs_kind_sort κ Typeω@i -> Γ ⊢ M ≈ M' : A'.
Proof.
  intros * HM HA; eapply wf_exp_eq_conv_sort;
    [ exact HM | exact (presup_exp_eq_right HA) | apply type_sort_abs_kind; constructor | exact HA ].
Qed.

(** The readback equations move along an equation of their types. *)
Lemma glu_nf_eq_conv : forall Γ M W A A' κ i,
    Γ ⊢ A ≈ A' : abs_kind_sort κ Typeω@i -> glu_nf_eq Γ M W A -> glu_nf_eq Γ M W A'.
Proof. unfold glu_nf_eq; intros * E H; eapply wf_exp_eq_conv_kind; eassumption. Qed.

Lemma glu_ne_eq_conv : forall Γ M W A A' κ i,
    Γ ⊢ A ≈ A' : abs_kind_sort κ Typeω@i -> glu_ne_eq Γ M W A -> glu_ne_eq Γ M W A'.
Proof. unfold glu_ne_eq; intros * E H; eapply wf_exp_eq_conv_kind; eassumption. Qed.

(** The relations of the domains of a shape at two representatives of
    the uniform parameters whose families agree, on the diagonal of a
    shape's context. *)
Lemma canon_doms_rel_agree : forall (p : qname) D ups ups',
    ind_fam_agree D (canon_nparams_rel D ups) (canon_nparams_rel D ups') (canon_args_rel D ups) (canon_args_rel D ups')
      (canon_doms_rel D ups) (canon_doms_rel D ups') ->
    forall m Mm ms c gs gs1 t gs2 ws k B ys, ind_member D m = Some Mm ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
      gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
      List.nth_error (ptyp_doms t) k = Some B ->
      tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) k ys ys ->
      (canon_doms_rel D ups m (ms ++ ws ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn k (shape_doms_tele t)) B
       <~> canon_doms_rel D ups' m (ms ++ ws ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn k (shape_doms_tele t)) B).
Proof.
  intros p D ups ups' Hag; destruct Hag as [Hfn Hfa Hfd]; intros * HM Hm Hc Heq Hw HB Hy.
  pose proof (tele_rel_nr_change p D ups _ _ _ _ _ _ Hfn Hfa Hfd m Mm HM) as F1.
  assert (Hkl : k < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
  assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
    by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
  pose proof (F1 _ _ Hm) as Hm2.
  pose proof (tele_prefix_rel_ar_change p D ups _ _ _ _ _ _ Hfn Hfa Hfd m Mm HM ms ms ms c gs _ ws ws Hm Hm2 Hc HK Hw) as Hw2.
  pose proof (tele_prefix_rel_sh_change p D ups _ _ _ _ _ _ Hfn Hfa Hfd m Mm HM ms ms ms c gs gs1 t gs2 ws ws ws k ys ys
                Hm Hm2 Hc Heq Hw Hw2 ltac:(lia) Hy) as Hy2.
  pose proof (Hfd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hm2 Hc Heq Hw Hw2 Hkl Hy Hy2) as Hdd.
  unfold shape_doms_rel in Hdd; rewrite (List.nth_error_nth _ _ _ HB) in Hdd; exact Hdd.
Qed.

(** The gluing of the type of a recursive argument moves along a
    representative [ups'] of the uniform parameters whose domains'
    relations agree, and along gluings of the domains whose types'
    contain the given ones, and whose elements' are contained in the given
    ones at the given types, and along an end clause [SE'] implied by the
    given [SE]. *)
Lemma glu_shape_typ_change : forall (p : qname) D ups ups' m Mm (DP DP' : list domain -> list centry -> exp -> glu_typ_pred)
    (DEl DEl' : list domain -> list centry -> exp -> glu_exp_pred)
    (SE SE' : ctx -> list exp -> list domain -> list centry -> nat -> list exp -> typ -> Prop),
    group_structure D -> ind_canon_props D ups -> ind_member D m = Some Mm ->
    (forall Γ Us pre Ts j Ps T, SE Γ Us pre Ts j Ps T -> SE' Γ Us pre Ts j Ps T) ->
    (forall ms c gs gs1 t gs2 ws k B ys, tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs ->
       gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) k = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) k ys ys ->
       (canon_doms_rel D ups m (ms ++ ws ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn k (shape_doms_tele t)) B
        <~> canon_doms_rel D ups' m (ms ++ ws ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn k (shape_doms_tele t)) B)) ->
    (forall ms c gs gs1 t gs2 ws k B ys, tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
       ind_con Mm c = Some gs ->
       gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) k = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) k ys ys ->
       let Ts := List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn k (shape_doms_tele t) in
       (forall Γ A, DP (ms ++ ws ++ ys) Ts B Γ A -> DP' (ms ++ ws ++ ys) Ts B Γ A) /\
       (forall Γ A M n, DP (ms ++ ws ++ ys) Ts B Γ A -> DEl' (ms ++ ws ++ ys) Ts B Γ A M n -> DEl (ms ++ ws ++ ys) Ts B Γ A M n)) ->
    forall t Γ Us pre Ts T, glu_shape_typ (canon_doms_rel D ups m) DP DEl SE Γ Us pre Ts t T ->
      forall ms c0 gs1 t0 gs2 ws k ys, pre = ms ++ ws ++ ys ->
        Ts = List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn k (shape_doms_tele t0) ->
        tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
        ind_con Mm c0 = Some (gs1 ++ ca_rec t0 :: gs2) ->
        tele_prefix_rel (canon_args_rel D ups m ms c0) (List.length (cargs_nonrec gs1)) ws ws ->
        ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
        tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t0) k ys ys ->
        glu_shape_typ (canon_doms_rel D ups' m) DP' DEl' SE' Γ Us pre Ts t T.
Proof.
  intros p D ups ups' m Mm DP DP' DEl DEl' SE SE' Hass Hcp HM HSE Hdr HD t.
  pose proof Hcp as [HnP HnI HaP HaI HdP HdI].
  induction t as [? ? | B t IH]; intros Γ Us pre Ts T H ms c0 gs1 t0 gs2 ws k ys Hpre HTs Hm Hc Hw Hsk Hk Hy;
    cbn [glu_shape_typ] in *; [ exact (HSE _ _ _ _ _ _ _ H) |].
  intros IT OT HT; destruct (H _ _ HT) as [H1 H2].
  destruct (shape_pi_step p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups) Hass HnP HnI HaP HaI HdP HdI
              m Mm ms c0 gs1 t0 gs2 ws ws k ys ys B t HM Hm Hc Hw Hsk Hy) as (HB & Hs' & Hk' & _ & Hstep).
  subst pre Ts.
  destruct (HD _ _ _ _ _ _ _ _ _ _ Hm Hc eq_refl Hw HB Hy) as [HDP HDEl].
  pose proof (Hdr _ _ _ _ _ _ _ _ _ _ Hm Hc eq_refl Hw HB Hy) as Edr.
  split.
  - intros Δ φ Hφ; exact (HDP _ _ (H1 Δ φ Hφ)).
  - intros Δ φ b c Hφ Hc' Hb.
    pose proof (proj2 (Edr _ _) Hc') as Hc0.
    eapply (IH _ _ _ _ _ (H2 Δ φ b c Hφ Hc0 (HDEl _ _ _ _ (H1 Δ φ Hφ) Hb)) ms c0 gs1 t0 gs2 ws (S k) (ys ++ c :: nil));
      [ rewrite <- !List.app_assoc; reflexivity | exact (prefix_tele_snoc_dom _ _ _ _ _ HB) | exact Hm | exact Hc | exact Hw
      | exact Hs' | exact Hk' | exact (Hstep _ _ Hc0) ].
Qed.

(** The relation of a recursive argument's values. *)
Lemma con_args_rel_shape : forall p D Ok nr ar dr k u u' pre pre' Ts gs vs vs', con_args_rel p D Ok nr ar dr k u u' pre pre' Ts gs vs vs' ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
    exists x x', List.nth_error vs (List.length gs1) = Some x /\ List.nth_error vs' (List.length gs1) = Some x' /\
      rec_arg_rel p D Ok nr ar dr k u u' (pre ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
        (pre' ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs')) (Ts ++ cargs_nonrec_tele gs1) t x x'.
Proof.
  induction 1; intros [| g gs1] Qs gs2 Heq; cbn [List.app] in Heq; inversion Heq; subst;
    try match goal with IH : forall _ _ _, _ = _ -> _ |- _ => destruct (IH _ _ _ eq_refl) as (x & x' & Hx & Hx' & Hr0) end.
  - exists x, x'; cbn; rewrite <- !List.app_assoc in Hr0; repeat split; assumption.
  - do 2 eexists; cbn; rewrite !List.app_nil_r; repeat split; eassumption.
  - exists x, x'; cbn; repeat split; assumption.
Qed.

Lemma con_args_rel_rec : forall p D Ok nr ar dr k u u' pre pre' Ts gs vs vs', con_args_rel p D Ok nr ar dr k u u' pre pre' Ts gs vs vs' ->
    forall gs1 Pr gs2 v v', gs = gs1 ++ ca_rec Pr :: gs2 ->
      List.nth_error vs (List.length gs1) = Some v -> List.nth_error vs' (List.length gs1) = Some v' ->
      rec_arg_rel p D Ok nr ar dr k u u' (pre ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
        (pre' ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs')) (Ts ++ cargs_nonrec_tele gs1) Pr v v'.
Proof.
  intros * H * Heq Hv Hv'.
  destruct (con_args_rel_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ Heq) as (x & x' & Hx & Hx' & Hr).
  rewrite Hv in Hx; injection Hx as <-; rewrite Hv' in Hx'; injection Hx' as <-; exact Hr.
Qed.

Lemma con_args_rel_len : forall p D Ok nr ar dr k u u' pre pre' Ts gs vs vs', con_args_rel p D Ok nr ar dr k u u' pre pre' Ts gs vs vs' ->
    List.length vs = List.length gs /\ List.length vs' = List.length gs.
Proof. induction 1; cbn; lia. Qed.

(** What two elements [v] and [v'] of a record view [k] related by the
    group at the non-uniform parameters [ns] and [ns'] are: their
    projections at the record's fields [fl], related as the arguments [gs]
    of the view's constructor [c], after no non-uniform parameter
    ([ind_rel_record]). *)
#[warnings="-cannot-define-projection"]
Record ind_rel_record_parts (p : qname) (D : ind_decl)
    (okr : nat -> list domain -> list centry -> list exp -> list domain -> Prop)
    (nr : nat -> nat -> list domain -> relation domain)
    (ar : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
    (dr : nat -> list domain -> list centry -> exp -> relation domain)
    (k : nat) (u u' ns ns' : list domain) (fl : list String.string) (c : String.string) (gs : list carg)
    (v v' : domain) : Prop := mk_ind_rel_record_parts
  { (** The projections of [v] *)
    rview_rel_vals : list domain
    (** The projections of [v'] *)
  ; rview_rel_vals' : list domain
    (** [v] is at no non-uniform parameter *)
  ; rview_rel_ns_nil : ns = nil
    (** [v'] is at no non-uniform parameter *)
  ; rview_rel_ns_nil' : ns' = nil
    (** [rview_rel_vals] are [v]'s projections *)
  ; rview_rel_projs : ⟦projs fl of v ⟧ gc_deps ⍮ gc_stack ↘ rview_rel_vals
    (** [rview_rel_vals'] are [v']'s projections *)
  ; rview_rel_projs' : ⟦projs fl of v' ⟧ gc_deps ⍮ gc_stack ↘ rview_rel_vals'
    (** The non-recursive projections are related at their types *)
  ; rview_rel_args : tele_rel (ar k nil c) (cargs_nonrec gs) (nonrec_arg_vals gs rview_rel_vals) (nonrec_arg_vals gs rview_rel_vals')
    (** The projections are related as the constructor's arguments *)
  ; rview_rel_cargs : con_args_rel p D okr nr ar dr k u u' nil nil nil gs rview_rel_vals rview_rel_vals' }.

(** Two related elements of a record view: their projections, related as
    the view's constructor's arguments, after no non-uniform parameter. *)
Lemma ind_rel_record_inv : forall p D okr nr ar dr k u u' ns ns' Mk qr Is fl c gs v v',
    ind_rel p D okr nr ar dr k u u' ns ns' v v' -> ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
    im_cons Mk = (c, gs) :: nil ->
    ind_rel_record_parts p D okr nr ar dr k u u' ns ns' fl c gs v v'.
Proof.
  intros * H HM Hh Hcs; inversion H; subst;
    match goal with H0 : ind_member _ _ = Some ?M0 |- _ =>
      assert_fails (unify M0 Mk); rewrite HM in H0; injection H0 as <- end;
    try (exfalso; eapply not_rview_record; eassumption).
  match goal with H0 : im_head Mk = mh_record _ _ _ |- _ => rewrite Hh in H0; injection H0 as <- <- <- end.
  match goal with H0 : im_cons Mk = _ |- _ => rewrite Hcs in H0; injection H0 as <- <- end.
  econstructor; [ reflexivity | reflexivity | eassumption .. ].
Qed.

Section GluIndProps.
  Variable (p : qname) (D : ind_decl) (ups : list domain)
    (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred).
  Hypothesis (Hass : group_structure D) (Hcp : ind_canon_props D ups).
  Let nr := canon_nparams_rel D ups.
  Let ar := canon_args_rel D ups.
  Let dr := canon_doms_rel D ups.

  Lemma glu_nparams_mono : forall NEl' : nat -> nat -> list domain -> glu_exp_pred,
      (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (nr m) j vs vs ->
         forall Γ A M n, NEl m j vs Γ A M n -> NEl' m j vs Γ A M n) ->
      forall k Mk Γ Us Ns ns, ind_member D k = Some Mk -> tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns ->
        glu_nparams k Mk NEl Γ Us Ns ns -> glu_nparams k Mk NEl' Γ Us Ns ns.
  Proof.
    intros NEl' HN * HMk Hns [L1 L2 H]; constructor; [ exact L1 | exact L2 |].
    intros j N A n HN0 HA Hn.
    assert (Hj : j < im_nn Mk) by (rewrite <- L1; apply List.nth_error_Some; congruence).
    eapply HN; [ exact HMk | exact Hj | | exact (H _ _ _ _ HN0 HA Hn) ].
    apply tele_prefix_rel_of_full with (T := List.rev (im_nparams Mk));
      [ exact Hns | rewrite List.length_rev; unfold im_nn in Hj; lia ].
  Qed.

  Lemma ind_glu_elem_resp_exp_eq : forall k Γ Us Ns M m, ind_glu_elem p D ups NEl AEl DP DEl k Γ Us Ns M m ->
      forall Mk M', ind_member D k = Some Mk -> Γ ⊢ M ≈ M' : im_ty_at p k Mk Us Ns ->
      ind_glu_elem p D ups NEl AEl DP DEl k Γ Us Ns M' m.
  Proof.
    intros * H; destruct H; intros Mk1 M' HM1 HMM;
      match goal with HA : ind_member D _ = Some ?A |- _ => assert_fails (unify A Mk1); rewrite HM1 in HA; injection HA as -> end.
    - eapply ind_glu_elem_con; try eassumption.
      etransitivity; [ symmetry; exact HMM | eassumption ].
    - eapply ind_glu_elem_neut; [ eassumption | eassumption | eassumption | eassumption | | eassumption | eassumption ].
      intros * Hφ Hrb.
      eapply glu_ne_eq_exp_eq; [| match goal with Hr : forall _ _ _, _ -> _ -> _ |- _ => eapply Hr; eassumption end ].
      symmetry; mauto 4.
    - eapply ind_glu_elem_record; try eassumption.
      etransitivity; [ symmetry; exact HMM | eassumption ].
  Qed.

  (** [ind_glu_elem] moves along a related representative [ups'] of the
      uniform parameters, to gluings of the families whose components are
      glued at the element's uniform parameters: the non-uniform
      parameters and the non-recursive arguments move at their types
      glued at the other side, which the other side's components give,
      and the domains of the shapes move back at their types glued at the
      given side. *)
  Lemma ind_glu_elem_move : forall ups' (NP' : nat -> nat -> list domain -> glu_typ_pred)
      (NEl' : nat -> nat -> list domain -> glu_exp_pred)
      (AP' : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
      (AEl' : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
      (DP' : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl' : nat -> list domain -> list centry -> exp -> glu_exp_pred),
      ind_fam_agree D nr (canon_nparams_rel D ups') ar (canon_args_rel D ups') dr (canon_doms_rel D ups') ->
      adm_uparams D ups nr ar dr ups' ->
      (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (nr m) j vs vs ->
         forall Γ A M n, NEl m j vs Γ A M n -> NP' m j vs Γ A -> NEl' m j vs Γ A M n) ->
      (forall m Mm ms c gs j vs, ind_member D m = Some Mm -> tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms ->
         ind_con Mm c = Some gs -> j < List.length (cargs_nonrec gs) ->
         tele_prefix_rel (ar m ms c) j vs vs ->
         forall Γ A M n, AEl m ms c j vs Γ A M n -> AP' m ms c j vs Γ A -> AEl' m ms c j vs Γ A M n) ->
      (forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
         tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
         tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws -> List.nth_error (ptyp_doms t) j = Some B ->
         tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
         let Ts := List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t) in
         forall Γ A M n, DEl' m (ms ++ ws ++ ys) Ts B Γ A M n -> DP m (ms ++ ws ++ ys) Ts B Γ A ->
           DEl m (ms ++ ws ++ ys) Ts B Γ A M n) ->
      (** Equal parameters are equal at their uniform part, which is
          typed, and the components at uniform parameters move to equal
          ones at weakenings *)
      (forall j Mj Δ Xs Ys, ind_member D j = Some Mj -> List.length Xs = im_np D Mj ->
         exps_eq_at Δ (im_params D Mj) Xs Ys ->
         exps_eq_at Δ (ind_uparams D) (List.firstn (ind_nu D) Xs) (List.firstn (ind_nu D) Ys)) ->
      (forall Δ Xs Ys, ⊢ Δ -> List.length Xs = ind_nu D -> exps_eq_at Δ (ind_uparams D) Xs Ys -> exps_eq_at Δ (ind_uparams D) Ys Ys) ->
      (forall Γ Δ φ Xs, Δ ⊢ᵏ φ : Γ -> exps_eq_at Γ (ind_uparams D) Xs Xs ->
         exps_eq_at Δ (ind_uparams D) (List.map (fun X => X[φ]ʷ) Xs) (List.map (fun X => X[φ]ʷ) Xs)) ->
      (forall Γ Us Δ φ Us', List.length Us = ind_nu D -> Δ ⊢ᵏ φ : Γ ->
         exps_eq_at Δ (ind_uparams D) (List.map (fun U => U[φ]ʷ) Us) Us' ->
         (forall Δ0 φ0 Us0, Δ0 ⊢ᵏ φ0 : Γ -> exps_eq_at Δ0 (ind_uparams D) (List.map (fun U => U[φ0]ʷ) Us) Us0 ->
            ind_glu_components p D ups' NP' NEl' AP' AEl' DP' DEl' Δ0 Us0) ->
         forall Δ1 φ1 Us1, Δ1 ⊢ᵏ φ1 : Δ -> exps_eq_at Δ1 (ind_uparams D) (List.map (fun U => U[φ1]ʷ) Us') Us1 ->
           ind_glu_components p D ups' NP' NEl' AP' AEl' DP' DEl' Δ1 Us1) ->
      forall k Γ Us Ns M m, ind_glu_elem p D ups NEl AEl DP DEl k Γ Us Ns M m -> ⊢ Γ ->
        exps_eq_at Γ (ind_uparams D) Us Us ->
        (forall Δ φ Us', Δ ⊢ᵏ φ : Γ -> exps_eq_at Δ (ind_uparams D) (List.map (fun U => U[φ]ʷ) Us) Us' ->
           ind_glu_components p D ups' NP' NEl' AP' AEl' DP' DEl' Δ Us') ->
        ind_glu_elem p D ups' NEl' AEl' DP' DEl' k Γ Us Ns M m.
  Proof.
    intros ups' NP' NEl' AP' AEl' DP' DEl' Hag Hadm HN HA HD Hup Hur Huw Hct.
    pose proof Hcp as [HnP HnI HaP HaI HdP HdI].
    destruct (ind_fam_agree_sym _ _ _ _ _ _ _ Hag) as [Hfn' Hfa' Hfd'].
    pose proof (canon_doms_rel_agree p D ups ups' Hag) as Hdr.
    destruct Hag as [Hfn Hfa Hfd].
    pose proof (tele_rel_nr_change p D ups _ _ _ _ _ _ Hfn Hfa Hfd) as F1.
    pose proof (tele_rel_nr_change p D ups _ _ _ _ _ _ Hfn' Hfa' Hfd') as F2.
    destruct Hadm as [_ _ Hcl _].
    set (CH := fun Γ Us => forall Δ φ Us', Δ ⊢ᵏ φ : Γ -> exps_eq_at Δ (ind_uparams D) (List.map (fun U => U[φ]ʷ) Us) Us' ->
                 ind_glu_components p D ups' NP' NEl' AP' AEl' DP' DEl' Δ Us').
    (** The non-uniform parameters move at their types at [ups'], which the
        components at [ups'] give *)
    assert (Hnpm : forall k Mk Γ Us Ns ms, ind_member D k = Some Mk -> tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms ->
                     ⊢ Γ -> exps_eq_at Γ (ind_uparams D) Us Us -> CH Γ Us ->
                     glu_nparams k Mk NEl Γ Us Ns ms -> glu_nparams k Mk NEl' Γ Us Ns ms).
    { intros k Mk Γ Us Ns ms HMk Hnr HΓ HUs HCH Hnp.
      assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
      pose proof (HCH Γ wk_id Us Hid ltac:(rewrite (List.map_ext _ (fun P => P) exp_wk_id), List.map_id; exact HUs)) as Hcomp0.
      pose proof (F1 _ _ HMk _ _ Hnr) as Hnr'.
      destruct Hnp as [L1 L2 Hg]; constructor; [ exact L1 | exact L2 |].
      enough (Hall : forall n j N A0 n0, j = n -> List.nth_error Ns j = Some N ->
                List.nth_error (tele_insts (im_nparams Mk) (sb_of_list Id Us) Ns) j = Some A0 ->
                List.nth_error ms j = Some n0 -> Γ ⊢ N : A0 ® n0 ∈ NEl' k j (List.firstn j ms))
        by (intros; eapply Hall; eauto).
      intros n; induction n as [n IHn] using (well_founded_induction PeanoNat.Nat.lt_wf_0); intros j N A0 n0 Hjn HN0 HA0 Hn0; subst n.
      assert (Hj : j < im_nn Mk) by (rewrite <- L2; apply List.nth_error_Some; congruence).
      assert (Hpj : tele_prefix_rel (nr k) j (List.firstn j ms) (List.firstn j ms))
        by (apply tele_prefix_rel_of_full with (T := List.rev (im_nparams Mk)); [ exact Hnr | rewrite List.length_rev; unfold im_nn in Hj; lia ]).
      apply (HN _ _ _ _ HMk Hj Hpj _ _ _ _ (Hg _ _ _ _ HN0 HA0 Hn0)).
      apply (ind_glu_components_nparams _ _ _ _ _ _ _ _ _ _ _ Hcomp0 k Mk j Ns (List.firstn j ms) A0 HMk
               ltac:(rewrite List.length_firstn; lia) Hj HA0).
      + intros j' N' T' n' Hj' HN' HT' Hn'.
        rewrite List.nth_error_firstn in Hn'; destruct (PeanoNat.Nat.ltb_spec j' j); [| discriminate ].
        rewrite List.firstn_firstn, PeanoNat.Nat.min_l by lia.
        exact (IHn j' Hj' j' N' T' n' eq_refl HN' HT' Hn').
      + apply tele_prefix_rel_of_full with (T := List.rev (im_nparams Mk));
          [ exact Hnr' | rewrite List.length_rev; unfold im_nn in Hj; lia ]. }
    apply (ind_glu_elem_mut_ind p D ups NEl AEl DP DEl
             (fun k Γ Us Ns M m _ => ⊢ Γ -> exps_eq_at Γ (ind_uparams D) Us Us -> CH Γ Us ->
                ind_glu_elem p D ups' NEl' AEl' DP' DEl' k Γ Us Ns M m)
             (fun k Γ Us pre Ts t A N v _ => forall Mk ms c0 gs1 t0 gs2 ws kk ys, ind_member D k = Some Mk -> pre = ms ++ ws ++ ys ->
                Ts = List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn kk (shape_doms_tele t0) ->
                tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms ->
                ind_con Mk c0 = Some (gs1 ++ ca_rec t0 :: gs2) ->
                tele_prefix_rel (ar k ms c0) (List.length (cargs_nonrec gs1)) ws ws ->
                ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
                tele_prefix_rel (shape_doms_rel (dr k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ms ws t0) kk ys ys ->
                List.length Us = ind_nu D -> exps_eq_at Γ (ind_uparams D) Us Us -> CH Γ Us ->
                glu_shape_typ (canon_doms_rel D ups' k) (DP' k) (DEl' k) (glu_self_params p D ups' NEl') Γ Us pre Ts t A ->
                glu_rec p D ups' NEl' AEl' DP' DEl' k Γ Us pre Ts t A N v)).
    - intros k Mk hd k' c gs Us Ns bs vs As Γ M HMk Hrv Href Hc HUl HNl Hbl Hvl HAl Heq Hnr Har Hnp Htyp Harg Hrec IHrec
        HΓ HUs HCH.
      assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
      pose proof (HCH Γ wk_id Us Hid ltac:(rewrite (List.map_ext _ (fun P => P) exp_wk_id), List.map_id; exact HUs)) as Hcomp0.
      set (ms := List.skipn (im_unu D Mk) bs) in *.
      pose proof (F1 _ _ HMk _ _ Hnr) as Hnr'.
      (** The non-uniform parameters, at their types at [ups'] *)
      pose proof (Hnpm k Mk Γ Us Ns ms HMk Hnr HΓ HUs HCH Hnp) as Hnp'.
      (** The non-recursive arguments related at [ups'] *)
      assert (Har' : tele_rel (canon_args_rel D ups' k ms c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs)).
      { apply (tele_rel_map _ (ar k ms c)); [| exact Har ].
        intros j pa pb x y Hj Hp1 Hp2 Hr.
        apply (Hfa _ _ _ _ _ _ _ _ _ _ _ HMk Hnr Hnr' Hc Hj Hp1 Hp2); exact Hr. }
      (** The non-recursive arguments, at their types at [ups'] *)
      assert (Hax : forall n gs1 r0 A0 gs2 N T v, List.length gs1 = n -> gs = gs1 ++ ca_arg r0 A0 :: gs2 ->
                 List.nth_error As (List.length gs1) = Some N ->
                 List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some T ->
                 List.nth_error vs (List.length gs1) = Some v ->
                 Γ ⊢ N : T ® v ∈ AEl' k ms c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))).
      { intros n; induction n as [n IHn] using (well_founded_induction PeanoNat.Nat.lt_wf_0);
          intros gs1 r0 A0 gs2 N T v Hn Heq0 HN1 HT1 Hv0.
        assert (HK : List.length (cargs_nonrec gs1) < List.length (cargs_nonrec gs))
          by (rewrite Heq0, cargs_nonrec_app, List.length_app; cbn; lia).
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Har Hvl Heq0) as Hpre.
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Har' Hvl Heq0) as Hpre'.
        assert (Hl1 : List.length (List.firstn (List.length gs1) vs) = List.length gs1)
          by (rewrite List.length_firstn, Hvl, Heq0, List.length_app; cbn; lia).
        apply (HA _ _ _ _ _ _ _ HMk Hnr Hc HK Hpre _ _ _ _ (Harg _ _ _ _ _ _ _ Heq0 HN1 HT1 Hv0)).
        apply (ind_glu_components_args _ _ _ _ _ _ _ _ _ _ _ Hcomp0 k Mk c gs gs1 r0 A0 gs2 Ns ms As (List.firstn (List.length gs1) vs) T
                 HMk Hc Heq0 Hnp' Hnr' Hl1 HT1); [| exact Hpre' ].
        intros hs1 rB B hs2 N' T' v' Heq1 HN' HT' Hv'.
        assert (Hlt : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
        rewrite List.nth_error_firstn in Hv'; destruct (PeanoNat.Nat.ltb_spec (List.length hs1) (List.length gs1)); [| lia ].
        rewrite List.firstn_firstn, PeanoNat.Nat.min_l by lia.
        exact (IHn (List.length hs1) ltac:(lia) hs1 rB B (hs2 ++ ca_arg r0 A0 :: gs2) N' T' v' eq_refl
                 ltac:(rewrite Heq0, Heq1, <- List.app_assoc; reflexivity) HN' HT' Hv'). }
      eapply ind_glu_elem_con; [ exact HMk | exact Hrv | exact Href | exact Hc | exact HUl | exact HNl | exact Hbl | exact Hvl | exact HAl
                               | exact Heq | exact Hnr' | exact Har' | exact Hnp' | exact Htyp | | ].
      + intros gs1 r0 A0 gs2 N A v Heq0 HN0 HA0 Hv0; exact (Hax _ gs1 r0 A0 gs2 N A v eq_refl Heq0 HN0 HA0 Hv0).
      + intros gs1 t gs2 N A v Heq0 HN0 HA0 Hv0.
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Har Hvl Heq0) as Hpre.
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Har' Hvl Heq0) as Hpre'.
        assert (Hl1 : List.length (List.firstn (List.length gs1) vs) = List.length gs1)
          by (rewrite List.length_firstn, Hvl, Heq0, List.length_app; cbn; lia).
        assert (Hsht : glu_shape_typ (canon_doms_rel D ups' k) (DP' k) (DEl' k) (glu_self_params p D ups' NEl') Γ Us
                         (ms ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
                         (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) t A).
        { apply (ind_glu_components_recs _ _ _ _ _ _ _ _ _ _ _ Hcomp0 k Mk c gs gs1 t gs2 Ns ms As (List.firstn (List.length gs1) vs) A
                   HMk Hc Heq0 Hnp' Hnr' Hl1 HA0); [| exact Hpre' ].
          intros hs1 rB B hs2 N' T' v' Heq1 HN' HT' Hv'.
          assert (Hlt : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
          rewrite List.nth_error_firstn in Hv'; destruct (PeanoNat.Nat.ltb_spec (List.length hs1) (List.length gs1)); [| lia ].
          rewrite List.firstn_firstn, PeanoNat.Nat.min_l by lia.
          exact (Hax (List.length hs1) hs1 rB B (hs2 ++ ca_rec t :: gs2) N' T' v' eq_refl
                   ltac:(rewrite Heq0, Heq1, <- List.app_assoc; reflexivity) HN' HT' Hv'). }
        apply (IHrec _ _ _ _ _ _ Heq0 HN0 HA0 Hv0 Mk ms c gs1 t gs2
                 (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) 0 nil);
          [ exact HMk | rewrite List.app_nil_r; reflexivity | cbn [List.firstn]; rewrite List.app_nil_r; reflexivity
          | exact Hnr | rewrite <- Heq0; exact Hc | exact Hpre | reflexivity | lia | apply tele_prefix_rel_nil
          | exact HUl | exact HUs | exact HCH | cbn [List.firstn]; rewrite ?List.app_nil_r; exact Hsht ].
    - (** A neutral: its annotation's non-uniform parameters at their types
          at [ups'] *)
      intros k Mk hd k' m Γ M Us Ns as' HMk Hrv Href Hm Hrb Hnr [NsX Hnp] HΓ HUs HCH.
      eapply ind_glu_elem_neut; [ exact HMk | exact Hrv | exact Href | exact Hm | exact Hrb | exact (F1 _ _ HMk _ _ Hnr)
                                | exists NsX; exact (Hnpm k Mk Γ Us NsX _ HMk Hnr HΓ HUs HCH Hnp) ].
    - (** A record view: its fields, as a constructor's arguments after no
          non-uniform parameter, at their types at [ups'] *)
      intros k Mk qr Is fl c gs Us Ns As m vs Γ M HMk Hh Hcs HUl HNl HAl Hps Heq Har Htyp Harg Hrec IHrec HΓ HUs HCH.
      assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
      pose proof (HCH Γ wk_id Us Hid ltac:(rewrite (List.map_ext _ (fun P => P) exp_wk_id), List.map_id; exact HUs)) as Hcomp0.
      pose proof (rview_struct_nparams _ _ _ (group_structure_record_struct _ Hass) _ _ _ _ _ HMk Hh) as Hnp0.
      destruct (rview_struct_con _ _ _ (group_structure_record_struct _ Hass) _ _ _ _ _ HMk Hh) as (gs0 & Hcs0 & Hlg).
      rewrite Hcs in Hcs0; injection Hcs0 as _ <-.
      pose proof (ind_con_single _ _ _ Hcs) as Hc.
      assert (Hvl : List.length vs = List.length gs) by (rewrite (eval_projs_length _ _ _ Hps); congruence).
      assert (Hnr : tele_rel (nr k) (List.rev (im_nparams Mk)) nil nil) by (rewrite Hnp0; split; reflexivity + exact I).
      assert (Hnr' : tele_rel (canon_nparams_rel D ups' k) (List.rev (im_nparams Mk)) nil nil)
        by (rewrite Hnp0; split; reflexivity + exact I).
      assert (HNs : Ns = nil) by (destruct Ns; [ reflexivity | unfold im_nn in HNl; rewrite Hnp0 in HNl; discriminate HNl ]).
      subst Ns.
      assert (Hnil : glu_nparams k Mk NEl' Γ Us nil nil).
      { constructor; [ unfold im_nn; rewrite Hnp0; reflexivity | unfold im_nn; rewrite Hnp0; reflexivity |].
        intros j0 N0 A1 n0 HN0; destruct j0; discriminate HN0. }
      assert (Har' : tele_rel (canon_args_rel D ups' k nil c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs)).
      { apply (tele_rel_map _ (ar k nil c)); [| exact Har ].
        intros j pa pb x y Hj Hp1 Hp2 Hr.
        apply (Hfa _ _ _ _ _ _ _ _ _ _ _ HMk Hnr Hnr' Hc Hj Hp1 Hp2); exact Hr. }
      assert (Hax : forall n gs1 r0 A0 gs2 N T v, List.length gs1 = n -> gs = gs1 ++ ca_arg r0 A0 :: gs2 ->
                 List.nth_error As (List.length gs1) = Some N ->
                 List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ nil)) As) (List.length gs1) = Some T ->
                 List.nth_error vs (List.length gs1) = Some v ->
                 Γ ⊢ N : T ® v ∈ AEl' k nil c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))).
      { intros n; induction n as [n IHn] using (well_founded_induction PeanoNat.Nat.lt_wf_0);
          intros gs1 r0 A0 gs2 N T v Hn Heq0 HN1 HT1 Hv0.
        assert (HK : List.length (cargs_nonrec gs1) < List.length (cargs_nonrec gs))
          by (rewrite Heq0, cargs_nonrec_app, List.length_app; cbn; lia).
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Har Hvl Heq0) as Hpre.
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Har' Hvl Heq0) as Hpre'.
        assert (Hl1 : List.length (List.firstn (List.length gs1) vs) = List.length gs1)
          by (rewrite List.length_firstn, Hvl, Heq0, List.length_app; cbn; lia).
        apply (HA _ _ _ _ _ _ _ HMk Hnr Hc HK Hpre _ _ _ _ (Harg _ _ _ _ _ _ _ Heq0 HN1 HT1 Hv0)).
        apply (ind_glu_components_args _ _ _ _ _ _ _ _ _ _ _ Hcomp0 k Mk c gs gs1 r0 A0 gs2 nil nil As (List.firstn (List.length gs1) vs) T
                 HMk Hc Heq0 Hnil Hnr' Hl1 HT1); [| exact Hpre' ].
        intros hs1 rB B hs2 N' T' v' Heq1 HN' HT' Hv'.
        assert (Hlt : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
        rewrite List.nth_error_firstn in Hv'; destruct (PeanoNat.Nat.ltb_spec (List.length hs1) (List.length gs1)); [| lia ].
        rewrite List.firstn_firstn, PeanoNat.Nat.min_l by lia.
        exact (IHn (List.length hs1) ltac:(lia) hs1 rB B (hs2 ++ ca_arg r0 A0 :: gs2) N' T' v' eq_refl
                 ltac:(rewrite Heq0, Heq1, <- List.app_assoc; reflexivity) HN' HT' Hv'). }
      eapply ind_glu_elem_record; [ exact HMk | exact Hh | exact Hcs | exact HUl | exact HNl | exact HAl | exact Hps | exact Heq
                                  | exact Har' | exact Htyp | | ].
      + intros gs1 r0 A0 gs2 N A v Heq0 HN0 HA0 Hv0.
        exact (Hax _ gs1 r0 A0 gs2 N A v eq_refl Heq0 HN0 HA0 Hv0).
      + intros gs1 t gs2 N A v Heq0 HN0 HA0 Hv0.
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Har Hvl Heq0) as Hpre.
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Har' Hvl Heq0) as Hpre'.
        assert (Hl1 : List.length (List.firstn (List.length gs1) vs) = List.length gs1)
          by (rewrite List.length_firstn, Hvl, Heq0, List.length_app; cbn; lia).
        assert (Hsht : glu_shape_typ (canon_doms_rel D ups' k) (DP' k) (DEl' k) (glu_self_params p D ups' NEl') Γ Us
                         (nil ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
                         (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) t A).
        { apply (ind_glu_components_recs _ _ _ _ _ _ _ _ _ _ _ Hcomp0 k Mk c gs gs1 t gs2 nil nil As (List.firstn (List.length gs1) vs) A
                   HMk Hc Heq0 Hnil Hnr' Hl1 HA0); [| exact Hpre' ].
          intros hs1 rB B hs2 N' T' v' Heq1 HN' HT' Hv'.
          assert (Hlt : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
          rewrite List.nth_error_firstn in Hv'; destruct (PeanoNat.Nat.ltb_spec (List.length hs1) (List.length gs1)); [| lia ].
          rewrite List.firstn_firstn, PeanoNat.Nat.min_l by lia.
          exact (Hax (List.length hs1) hs1 rB B (hs2 ++ ca_rec t :: gs2) N' T' v' eq_refl
                   ltac:(rewrite Heq0, Heq1, <- List.app_assoc; reflexivity) HN' HT' Hv'). }
        apply (IHrec _ _ _ _ _ _ Heq0 HN0 HA0 Hv0 Mk nil c gs1 t gs2
                 (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) 0 nil);
          [ exact HMk | rewrite List.app_nil_r; reflexivity
          | rewrite Hnp0; cbn [List.firstn List.rev List.app]; rewrite List.app_nil_r; reflexivity
          | exact Hnr | rewrite <- Heq0; exact Hc | exact Hpre | reflexivity | lia | apply tele_prefix_rel_nil
          | exact HUl | exact HUs | exact HCH
          | rewrite Hnp0 in Hsht; cbn [List.firstn List.rev List.app] in Hsht |- *; rewrite ?List.app_nil_r in Hsht;
            rewrite ?List.app_nil_r; exact Hsht ].
    - (** The end of a shape: the element at every equal instance, whose
          uniform parameters are equal to the type's *)
      intros j Mj Ps Ts pre A Us Γ N x k HMj Hc1 Hc2 IH2 Mk ms c0 gs1 t0 gs2 ws k1 ys HMk Hpre HTs Hm Hc Hw Hsk Hk Hy
        HUl HUs HCH _.
      destruct (ptyp_skip_self _ _ _ _ Hsk) as (HkL & Hj & HPs).
      assert (Hk1 : k1 = List.length (ptyp_doms t0)) by lia.
      assert (Hys : tele_rel (shape_doms_rel (dr k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ms ws t0) (ptyp_doms t0) ys ys)
        by (apply tele_rel_of_pre; rewrite <- Hk1; exact Hy).
      assert (HTs' : Ts = List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0)
        by (rewrite HTs, shape_doms_tele_firstn_all; [ reflexivity | lia ]).
      (** The shape's parameters at [ups'] are related to those at [ups]. *)
      assert (Hev : forall bsr', ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups' Ts pre ↘ bsr' ->
                 exists bsr, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups Ts pre ↘ bsr /\
                   tele_rel (nr j) (List.rev (im_nparams Mj)) bsr bsr').
      { intros bsr' Hbs'.
        destruct (Hcl k Mk ms ms c0 _ gs1 t0 gs2 ws ws ys ys HMk Hm Hc eq_refl Hw Hys) as [b0 b1 E0 E1 H01].
        rewrite HPs, <- HTs' in E0, E1; subst pre.
        pose proof (functional_eval_exps' _ _ _ _ E1 Hbs') as ->.
        rewrite Hj in H01; unfold nparams_tele_rel in H01; rewrite HMj in H01.
        exists b0; split; assumption. }
      apply glu_rec_self with (Mj := Mj); [ exact HMj | |].
      + intros bsr' Q Hbs' HQ.
        destruct (Hev _ Hbs') as (bsr0 & E0 & H01).
        destruct (Hc1 _ _ E0 HQ) as (HQl & _).
        split; [ exact HQl | exact (F1 _ _ HMj _ _ (canon_nparams_rel_refl_r' p D ups Hass Hcp _ _ _ _ HMj H01)) ].
      + intros bsr' Q Hbs' HQ Δ φ Us' Q' Hφ HUl' HQ'.
        destruct (Hev _ Hbs') as (bsr0 & E0 & _).
        destruct (Hc1 _ _ E0 HQ) as (HQl & _).
        assert (HUq : exps_eq_at Δ (ind_uparams D) (List.map (fun U => U[φ]ʷ) Us) Us').
        { pose proof (Hup j Mj Δ (List.map (fun P => P[φ]ʷ) (Us ++ Q)) (Us' ++ Q') HMj
                        ltac:(rewrite List.length_map, List.length_app; unfold im_np, im_nn, ind_nu in *; lia) HQ') as H.
          rewrite List.map_app, firstn_app_exact, firstn_app_exact in H by (rewrite ?List.length_map; lia); exact H. }
        exact (IH2 _ _ E0 HQ Δ φ Us' Q' Hφ HUl' HQ' ltac:(eapply kripke_dom; eassumption)
                 (Hur _ _ _ ltac:(eapply kripke_dom; eassumption) ltac:(rewrite List.length_map; exact HUl) HUq)
                 (Hct _ _ _ _ _ HUl Hφ HUq HCH)).
    - (** A domain: the argument moves back to the given domain's gluing *)
      intros A Γ k pre Ts B x Us t N Hd He Hg IH Mk ms c0 gs1 t0 gs2 ws k1 ys HMk Hpre HTs Hm Hc Hw Hsk Hk Hy HUl HUs HCH Hsht.
      destruct (shape_pi_step p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk ms c0 gs1 t0 gs2 ws ws k1 ys ys B t
                  HMk Hm Hc Hw Hsk Hy) as (HB & Hs' & Hk' & _ & Hstep).
      subst pre Ts.
      cbn [glu_shape_typ] in Hsht.
      pose proof (Hdr _ _ _ _ _ _ _ _ _ _ _ _ HMk Hm Hc eq_refl Hw HB Hy) as Edr.
      apply glu_rec_pi.
      + intros * HA0 Δ φ Hφ; exact (proj1 (Hsht _ _ HA0) Δ φ Hφ).
      + intros * HA0 Δ φ b0 c Hφ Hc' Hb.
        exact (He _ _ HA0 Δ φ b0 c Hφ (proj2 (Edr _ _) Hc')
                 (HD _ _ _ _ _ _ _ _ _ _ _ _ HMk Hm Hc eq_refl Hw HB Hy _ _ _ _ Hb (Hd _ _ HA0 Δ φ Hφ))).
      + intros * HA0 Δ φ b0 c fc Hφ Hc' Hb Hfc.
        pose proof (proj2 (Edr _ _) Hc') as Hc0.
        pose proof (HD _ _ _ _ _ _ _ _ _ _ _ _ HMk Hm Hc eq_refl Hw HB Hy _ _ _ _ Hb (Hd _ _ HA0 Δ φ Hφ)) as Hb0.
        pose proof (proj2 (Hsht _ _ HA0) Δ φ b0 c Hφ Hc' Hb) as Hsht'.
        pose proof (Huw _ _ _ _ Hφ HUs) as HUs'.
        apply (IH _ _ HA0 Δ φ b0 c fc Hφ Hc0 Hb0 Hfc Mk ms c0 gs1 t0 gs2 ws (S k1) (ys ++ c :: nil));
          [ exact HMk | rewrite <- !List.app_assoc; reflexivity | exact (prefix_tele_snoc_dom _ _ _ _ _ HB)
          | exact Hm | exact Hc | exact Hw | exact Hs' | exact Hk' | exact (Hstep _ _ Hc0)
          | rewrite List.length_map; exact HUl | exact HUs' | exact (Hct _ _ _ _ _ HUl Hφ HUs' HCH) | exact Hsht' ].
  Qed.

  Lemma ind_glu_elem_mono : forall (NEl' : nat -> nat -> list domain -> glu_exp_pred)
      (AEl' : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
      (DP' : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl' : nat -> list domain -> list centry -> exp -> glu_exp_pred),
      (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (nr m) j vs vs ->
         forall Γ A M n, NEl m j vs Γ A M n -> NEl' m j vs Γ A M n) ->
      (forall m Mm ms c gs j vs, ind_member D m = Some Mm -> tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms ->
         ind_con Mm c = Some gs -> j < List.length (cargs_nonrec gs) ->
         tele_prefix_rel (ar m ms c) j vs vs -> forall Γ A M n, AEl m ms c j vs Γ A M n -> AEl' m ms c j vs Γ A M n) ->
      (forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
         tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
         tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws -> List.nth_error (ptyp_doms t) j = Some B ->
         tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
         let Ts := List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t) in
         (forall Γ A, DP m (ms ++ ws ++ ys) Ts B Γ A -> DP' m (ms ++ ws ++ ys) Ts B Γ A) /\
         (forall Γ A M n, DP m (ms ++ ws ++ ys) Ts B Γ A -> DEl' m (ms ++ ws ++ ys) Ts B Γ A M n -> DEl m (ms ++ ws ++ ys) Ts B Γ A M n)) ->
      forall k Γ Us Ns M m, ind_glu_elem p D ups NEl AEl DP DEl k Γ Us Ns M m ->
        ind_glu_elem p D ups NEl' AEl' DP' DEl' k Γ Us Ns M m.
  Proof.
    intros NEl' AEl' DP' DEl' HN HA HD.
    pose proof Hcp as [HnP HnI HaP HaI HdP HdI].
    apply (ind_glu_elem_mut_ind p D ups NEl AEl DP DEl
             (fun k Γ Us Ns M m _ => ind_glu_elem p D ups NEl' AEl' DP' DEl' k Γ Us Ns M m)
             (fun k Γ Us pre Ts t A N v _ => forall Mk ms c0 gs1 t0 gs2 ws kk ys, ind_member D k = Some Mk -> pre = ms ++ ws ++ ys ->
                Ts = List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn kk (shape_doms_tele t0) ->
                tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms ->
                ind_con Mk c0 = Some (gs1 ++ ca_rec t0 :: gs2) ->
                tele_prefix_rel (ar k ms c0) (List.length (cargs_nonrec gs1)) ws ws ->
                ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
                tele_prefix_rel (shape_doms_rel (dr k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ms ws t0) kk ys ys ->
                glu_rec p D ups NEl' AEl' DP' DEl' k Γ Us pre Ts t A N v)).
    - intros k Mk hd k' c gs Us Ns bs vs As Γ M HMk Hrv Href Hc HUl HNl Hbl Hvl HAl Heq Hnr Har Hnp Htyp Harg Hrec IHrec.
      eapply ind_glu_elem_con; [ exact HMk | exact Hrv | exact Href | exact Hc | exact HUl | exact HNl | exact Hbl | exact Hvl | exact HAl
                               | exact Heq | exact Hnr | exact Har | | exact Htyp | | ].
      + eapply glu_nparams_mono; [ exact HN | exact HMk | exact Hnr | exact Hnp ].
      + intros * Heq0 HN0 HA0 Hv0.
        eapply HA; [ exact HMk | exact Hnr | exact Hc | | eapply nonrec_prefix_pre; [ exact Har | exact Hvl | exact Heq0 ]
                   | exact (Harg _ _ _ _ _ _ _ Heq0 HN0 HA0 Hv0) ].
        rewrite Heq0, cargs_nonrec_app, List.length_app; cbn; lia.
      + intros * Heq0 HN0 HA0 Hv0.
        apply (IHrec _ _ _ _ _ _ Heq0 HN0 HA0 Hv0 Mk (List.skipn (im_unu D Mk) bs) c gs1 t gs2
                 (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) 0 nil);
          [ exact HMk | rewrite List.app_nil_r; reflexivity | cbn [List.firstn]; rewrite List.app_nil_r; reflexivity
          | exact Hnr | rewrite <- Heq0; exact Hc
          | eapply nonrec_prefix_pre; [ exact Har | exact Hvl | exact Heq0 ] | reflexivity | lia | apply tele_prefix_rel_nil ].
    - intros k Mk hd k' m Γ M Us Ns as' HMk Hrv Href Hm Hrb Hnr [NsX Hnp].
      eapply ind_glu_elem_neut; [ exact HMk | exact Hrv | exact Href | exact Hm | exact Hrb | exact Hnr
                                | exists NsX; eapply glu_nparams_mono; [ exact HN | exact HMk | exact Hnr | exact Hnp ] ].
    - (** A record view: its fields, as a constructor's arguments. *)
      intros k Mk qr Is fl c gs Us Ns As m vs Γ M HMk Hh Hcs HUl HNl HAl Hps Heq Har Htyp Harg Hrec IHrec.
      pose proof (rview_struct_nparams _ _ _ (group_structure_record_struct _ Hass) _ _ _ _ _ HMk Hh) as Hnp0.
      destruct (rview_struct_con _ _ _ (group_structure_record_struct _ Hass) _ _ _ _ _ HMk Hh) as (gs0 & Hcs0 & Hlg).
      rewrite Hcs in Hcs0; injection Hcs0 as _ <-.
      pose proof (ind_con_single _ _ _ Hcs) as Hc.
      assert (Hvl : List.length vs = List.length gs) by (rewrite (eval_projs_length _ _ _ Hps); congruence).
      assert (Hnr : tele_rel (nr k) (List.rev (im_nparams Mk)) nil nil) by (rewrite Hnp0; split; reflexivity + exact I).
      eapply ind_glu_elem_record; [ exact HMk | exact Hh | exact Hcs | exact HUl | exact HNl | exact HAl | exact Hps | exact Heq
                                  | exact Har | exact Htyp | | ].
      + intros * Heq0 HN0 HA0 Hv0.
        eapply HA; [ exact HMk | exact Hnr | exact Hc | | eapply nonrec_prefix_pre; [ exact Har | exact Hvl | exact Heq0 ]
                   | exact (Harg _ _ _ _ _ _ _ Heq0 HN0 HA0 Hv0) ].
        rewrite Heq0, cargs_nonrec_app, List.length_app; cbn; lia.
      + intros * Heq0 HN0 HA0 Hv0.
        apply (IHrec _ _ _ _ _ _ Heq0 HN0 HA0 Hv0 Mk nil c gs1 t gs2
                 (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) 0 nil);
          [ exact HMk | rewrite List.app_nil_r; reflexivity | rewrite Hnp0; cbn [List.firstn List.rev List.app]; rewrite List.app_nil_r; reflexivity
          | exact Hnr | rewrite <- Heq0; exact Hc
          | eapply nonrec_prefix_pre; [ exact Har | exact Hvl | exact Heq0 ] | reflexivity | lia | apply tele_prefix_rel_nil ].
    - intros j Mj Ps Ts pre A Us Γ N x k HMj Hc1 Hc2 IH2 Mk ms c0 gs1 t0 gs2 ws k1 ys HMk Hpre HTs Hm Hc Hw Hsk Hk Hy.
      apply glu_rec_self with (Mj := Mj); [ exact HMj | |].
      + exact Hc1.
      + intros bsr Q Hbs HQ Δ φ Us' Q' Hφ HUl' HQ'; exact (IH2 _ _ Hbs HQ Δ φ Us' Q' Hφ HUl' HQ').
    - intros A Γ k pre Ts B x Us t N Hd He Hg IH Mk ms c0 gs1 t0 gs2 ws k1 ys HMk Hpre HTs Hm Hc Hw Hsk Hk Hy.
      destruct (shape_pi_step p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk ms c0 gs1 t0 gs2 ws ws k1 ys ys B t
                  HMk Hm Hc Hw Hsk Hy) as (HB & Hs' & Hk' & _ & Hstep).
      subst pre Ts.
      destruct (HD _ _ _ _ _ _ _ _ _ _ _ _ HMk Hm Hc eq_refl Hw HB Hy) as [HDP HDEl].
      apply glu_rec_pi.
      + intros * HA0 Δ φ Hφ; exact (HDP _ _ (Hd _ _ HA0 Δ φ Hφ)).
      + intros * HA0 Δ φ b0 c Hφ Hc' Hb; exact (He _ _ HA0 Δ φ b0 c Hφ Hc' (HDEl _ _ _ _ (Hd _ _ HA0 Δ φ Hφ) Hb)).
      + intros * HA0 Δ φ b0 c fc Hφ Hc' Hb Hfc.
        apply (IH _ _ HA0 Δ φ b0 c fc Hφ Hc' (HDEl _ _ _ _ (Hd _ _ HA0 Δ φ Hφ) Hb) Hfc Mk ms c0 gs1 t0 gs2 ws (S k1)
                 (ys ++ c :: nil));
          [ exact HMk | rewrite <- !List.app_assoc; reflexivity | exact (prefix_tele_snoc_dom _ _ _ _ _ HB)
          | exact Hm | exact Hc | exact Hw | exact Hs' | exact Hk' | exact (Hstep _ _ Hc') ].
  Qed.

End GluIndProps.


(** The monotonicity premises on the families of a group's clause: the
    types' gluings grow, the elements' shrink, but the non-uniform
    parameters' elements are the same (they are glued at the end of a
    recursive argument's shape, [glu_self_params]). *)
Lemma ind_glu_components_mono : forall p D ups NP NEl AP AEl DP DEl NP' NEl' AP' AEl' DP' DEl' Γ Us,
    group_structure D -> ind_canon_props D ups ->
    (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
       (forall Γ T, NP m j vs Γ T -> NP' m j vs Γ T) /\ (forall Γ T N n, NEl' m j vs Γ T N n -> NEl m j vs Γ T N n)) ->
    (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
       forall Γ T N n, NEl m j vs Γ T N n -> NEl' m j vs Γ T N n) ->
    (forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
       j < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
       (forall Γ T, AP m ms c j vs Γ T -> AP' m ms c j vs Γ T) /\
       (forall Γ T N n, AEl' m ms c j vs Γ T N n -> AEl m ms c j vs Γ T N n)) ->
    (forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
       gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
       let Ts := List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t) in
       (forall Γ A, DP m (ms ++ ws ++ ys) Ts B Γ A -> DP' m (ms ++ ws ++ ys) Ts B Γ A) /\
       (forall Γ A M n, DP m (ms ++ ws ++ ys) Ts B Γ A -> DEl' m (ms ++ ws ++ ys) Ts B Γ A M n -> DEl m (ms ++ ws ++ ys) Ts B Γ A M n)) ->
    ind_glu_components p D ups NP NEl AP AEl DP DEl Γ Us -> ind_glu_components p D ups NP' NEl' AP' AEl' DP' DEl' Γ Us.
Proof.
  intros * Hass Hcp HN HN' HA HD [HCN HCA HCR].
  assert (HNm : forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
                forall Γ A M n, NEl' m j vs Γ A M n -> NEl m j vs Γ A M n)
    by (intros * HM Hj Hp; exact (proj2 (HN _ _ _ _ HM Hj Hp))).
  (** The non-recursive arguments before an argument, glued at the given
      gluings. *)
  assert (Hargs : forall m Mm c gs gs1 gs2 g Ns ns As vs, ind_member D m = Some Mm -> ind_con Mm c = Some gs ->
            gs = gs1 ++ g :: gs2 ->
            tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns -> List.length vs = List.length gs1 ->
            tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs)
              (nonrec_arg_vals gs1 vs) ->
            (forall hs1 rB B hs2 N T' v, gs1 = hs1 ++ ca_arg rB B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
               List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
               List.nth_error vs (List.length hs1) = Some v ->
               Γ ⊢ N : T' ® v ∈ AEl' m ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))) ->
            (forall hs1 rB B hs2 N T' v, gs1 = hs1 ++ ca_arg rB B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
               List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
               List.nth_error vs (List.length hs1) = Some v ->
               Γ ⊢ N : T' ® v ∈ AEl m ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs)))).
  { intros m Mm c gs gs1 gs2 g Ns ns As vs HM Hc Heq Hns Hvl Hp Hpre hs1 rB B hs2 N T' v Heq1 HN0 HT' Hv.
    assert (HK1 : List.length (cargs_nonrec hs1) < List.length (cargs_nonrec gs))
      by (rewrite Heq, Heq1, !cargs_nonrec_app, !List.length_app; cbn; lia).
    assert (Hpre1 : tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec hs1))
                      (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))).
    { pose proof (tele_prefix_rel_of_pre _ _ _ _ (List.length (cargs_nonrec hs1)) Hp
                    ltac:(rewrite Heq1, cargs_nonrec_app, List.length_app; cbn; lia)) as Hq.
      rewrite (nonrec_firstn _ _ _ _ _ Heq1 Hvl) in Hq; exact Hq. }
    apply (proj2 (HA _ _ _ _ _ _ _ HM Hns Hc HK1 Hpre1)).
    eapply Hpre; eassumption. }
  constructor.
  - intros m Mm k Ns ns T HM Hl Hk HT Hpre Hp.
    apply (proj1 (HN m Mm k ns HM Hk Hp)).
    apply (HCN m Mm k Ns ns T HM Hl Hk HT); [| exact Hp ].
    intros j N T' n Hj HN0 HT' Hn.
    assert (Hpj : tele_prefix_rel (canon_nparams_rel D ups m) j (List.firstn j ns) (List.firstn j ns))
      by exact (tele_prefix_rel_of_pre _ _ _ _ j Hp ltac:(lia)).
    apply (proj2 (HN m Mm j (List.firstn j ns) HM ltac:(lia) Hpj)).
    apply Hpre; assumption.
  - intros m Mm c gs gs1 r0 A0 gs2 Ns ns As vs T HM Hc Heq Hnp Hns Hvl HT Hpre Hp.
    assert (HK : List.length (cargs_nonrec gs1) < List.length (cargs_nonrec gs))
      by (rewrite Heq, cargs_nonrec_app, List.length_app; cbn; lia).
    apply (proj1 (HA _ _ _ _ _ _ _ HM Hns Hc HK Hp)).
    eapply HCA; [ exact HM | exact Hc | exact Heq | | exact Hns | exact Hvl | exact HT | | exact Hp ].
    + eapply (glu_nparams_mono D ups NEl'); [ exact HNm | exact HM | exact Hns | exact Hnp ].
    + exact (Hargs _ _ _ _ _ _ _ _ _ _ _ HM Hc Heq Hns Hvl Hp Hpre).
  - intros m Mm c gs gs1 t gs2 Ns ns As vs T HM Hc Heq Hnp Hns Hvl HT Hpre Hp.
    pose proof (HCR m Mm c gs gs1 t gs2 Ns ns As vs T HM Hc Heq
                  ltac:(eapply (glu_nparams_mono D ups NEl'); [ exact HNm | exact HM | exact Hns | exact Hnp ])
                  Hns Hvl HT (Hargs _ _ _ _ _ _ _ _ _ _ _ HM Hc Heq Hns Hvl Hp Hpre) Hp) as H.
    subst gs.
    (** The end of the shape: the parameters' gluings are the same *)
    assert (HSE : forall Γ0 Us0 pre Ts j Ps T0, glu_self_params p D ups NEl Γ0 Us0 pre Ts j Ps T0 ->
                  glu_self_params p D ups NEl' Γ0 Us0 pre Ts j Ps T0).
    { intros * HS Mj Q bsr HMj HT0 Hb; destruct (HS Mj Q bsr HMj HT0 Hb) as [Hr Hn Ht].
      constructor; [ exact Hr | | exact Ht ].
      eapply (glu_nparams_mono D ups NEl); [ exact HN' | exact HMj | exact Hr | exact Hn ]. }
    exact (glu_shape_typ_change p D ups ups m Mm (DP m) (DP' m) (DEl m) (DEl' m) _ _ Hass Hcp HM HSE ltac:(intros; reflexivity)
             (fun ms0 c1 gs0 gs3 t1 gs4 ws0 j0 B0 ys0 Hm0 Hc0 Heq0 Hw0 HB0 Hy0 =>
                HD m Mm ms0 c1 gs0 gs3 t1 gs4 ws0 j0 B0 ys0 HM Hm0 Hc0 Heq0 Hw0 HB0 Hy0)
             t Γ _ _ _ T H ns c gs1 t gs2 (nonrec_arg_vals gs1 vs) 0 nil ltac:(rewrite List.app_nil_r; reflexivity)
             ltac:(cbn [List.firstn]; rewrite List.app_nil_r; reflexivity)
             Hns Hc Hp eq_refl ltac:(lia) (tele_prefix_rel_nil _)).
Qed.

Lemma ind_typ_at_mono : forall p D ups ns NP NEl AP AEl DP DEl NP' NEl' AP' AEl' DP' DEl' k Mk U Γ A Ps,
    group_structure D -> ind_canon_props D ups -> ind_member D k = Some Mk ->
    tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns ->
    (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
       (forall Γ T, NP m j vs Γ T -> NP' m j vs Γ T) /\ (forall Γ T N n, NEl' m j vs Γ T N n -> NEl m j vs Γ T N n)) ->
    (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
       forall Γ T N n, NEl m j vs Γ T N n -> NEl' m j vs Γ T N n) ->
    (forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
       j < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
       (forall Γ T, AP m ms c j vs Γ T -> AP' m ms c j vs Γ T) /\
       (forall Γ T N n, AEl' m ms c j vs Γ T N n -> AEl m ms c j vs Γ T N n)) ->
    (forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
       gs = gs1 ++ ca_rec t :: gs2 -> tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
       let Ts := List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t) in
       (forall Γ A, DP m (ms ++ ws ++ ys) Ts B Γ A -> DP' m (ms ++ ws ++ ys) Ts B Γ A) /\
       (forall Γ A M n, DP m (ms ++ ws ++ ys) Ts B Γ A -> DEl' m (ms ++ ws ++ ys) Ts B Γ A M n -> DEl m (ms ++ ws ++ ys) Ts B Γ A M n)) ->
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk U Γ A Ps -> ind_typ_at p D ups ns NP' NEl' AP' AEl' DP' DEl' k Mk U Γ A Ps.
Proof.
  intros * Hass Hcp HMk Hns HN HN' HA HD (HA0 & Hk); split; [ exact HA0 |].
  intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as [Hpt Hs Hc Hnp].
  constructor; [ exact Hpt | exact Hs | |].
  - intros Us HUs; eapply ind_glu_components_mono; [ exact Hass | exact Hcp | exact HN | exact HN' | exact HA | exact HD | eauto ].
  - eapply (glu_nparams_mono D ups NEl); [ exact HN' | exact HMk | exact Hns | exact Hnp ].
Qed.

(** The type predicate of an inductive type, along an equation, a context
    refinement and a weakening. *)

Lemma ind_typ_at_resp_exp_eq : forall p D ups ns NP NEl AP AEl DP DEl k Mk n Γ A A' Ps,
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A Ps -> Γ ⊢ A ≈ A' : Typeω@n ->
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A' Ps.
Proof.
  intros * (HA & Hk) HAA; split; [ etransitivity; [ symmetry; exact HAA | exact HA ] | exact Hk ].
Qed.

Lemma ind_typ_at_resp_ctxsub : forall p D ups ns NP NEl AP AEl DP DEl k Mk n Γ A Ps Δ,
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A Ps -> Δ ⊆ Γ ->
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Δ A Ps.
Proof.
  intros * (HA & Hk) Hs; split; [ eapply ctxsub_exp_eq; [ exact (ctx_sub_escape _ _ _ _ Hs) | exact HA ] |].
  intros Θ ψ Hψ; apply Hk; eapply kripke_ctxsub; eassumption.
Qed.

Lemma ind_typ_at_wk : forall p D ups ns NP NEl AP AEl DP DEl k Mk n Γ A Ps Δ φ,
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A Ps -> Δ ⊢ᵏ φ : Γ ->
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Δ A[φ]ʷ (List.map (fun P => P[φ]ʷ) Ps).
Proof.
  intros * (HA & Hk) Hφ; split; [ rewrite <- wk_apps_ind; mauto 3 |].
  intros Θ ψ Hψ; rewrite !map_wk_wk; apply Hk; eapply kripke_compose; eassumption.
Qed.

(** The type at the parameters of a type predicate is the one at equal
    ones. *)
Lemma ind_typ_at_params_conv : forall p D ups ns NP NEl AP AEl DP DEl k Mk pm n Γ A Ps Δ φ Ps',
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
    ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A Ps -> Δ ⊢ᵏ φ : Γ ->
    exps_eq_at Δ (im_params D Mk) (List.map (fun P => P[φ]ʷ) Ps) Ps' ->
    Δ ⊢ apps (a_ind p k) (List.map (fun P => P[φ]ʷ) Ps) ≈ apps (a_ind p k) Ps' : Typeω@n.
Proof.
  intros * Hl HMk Hh (_ & Hk) Hφ [HlP HPP].
  destruct (Hk _ _ Hφ) as [[HPl _ _] Hs _ _].
  assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
  eapply wf_exp_eq_subtyp'; [| exact Hs ].
  eapply wf_exp_eq_ind_apps; [ exact Hl | exact HMk | exact (decl_member_lt _ _ _ _ _ _ HΔ Hl HMk Hh) | exact HΔ
                             | exact HPl | lia | exact HPP ].
Qed.

(** The non-uniform parameters glued to [X] are glued there at equal
    parameters [Ps'], when the gluings [NEl] of their types move along an
    equation of terms to a type glued at [NP]: the [j]-th one is equal to
    the [j]-th of [Ps'], whose type is glued by the components at [Ps']
    after the ones before it. *)
Lemma glu_nparams_params_eq : forall p D ups NP NEl AP AEl DP DEl k Mk Γ Us Ns X Ps',
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> ⊢ Γ -> List.length Us = ind_nu D ->
    tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) X X ->
    ind_glu_components p D ups NP NEl AP AEl DP DEl Γ (List.firstn (ind_nu D) Ps') ->
    (forall j A A' N N' n, j < im_nn Mk -> Γ ⊢ N : A ® n ∈ NEl k j (List.firstn j X) -> Γ ⊢ N ≈ N' : A ->
       Γ ⊢ A' ® NP k j (List.firstn j X) -> Γ ⊢ N' : A' ® n ∈ NEl k j (List.firstn j X)) ->
    glu_nparams k Mk NEl Γ Us Ns X -> exps_eq_at Γ (im_params D Mk) (Us ++ Ns) Ps' ->
    glu_nparams k Mk NEl Γ (List.firstn (ind_nu D) Ps') (List.skipn (ind_nu D) Ps') X.
Proof.
  intros * Hl HMk HΓ HUl HXr Hcomp Hresp [L1 L2 H] [HlP HP].
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [_ Hc].
  pose proof (decl_closed_nparams_ass D Hc _ _ HMk) as HassN.
  pose proof (decl_uparams_ass D Hc) as HassU.
  rewrite List.length_app in HlP.
  assert (LPs : List.length Ps' = im_np D Mk) by (unfold im_np; lia).
  constructor; [ rewrite List.length_skipn; unfold im_np in LPs; lia | exact L2 |].
  enough (Hall : forall m j N' A' n, j = m -> List.nth_error (List.skipn (ind_nu D) Ps') j = Some N' ->
            List.nth_error (tele_insts (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps')) (List.skipn (ind_nu D) Ps')) j = Some A' ->
            List.nth_error X j = Some n -> Γ ⊢ N' : A' ® n ∈ NEl k j (List.firstn j X))
    by (intros; eapply Hall; eauto).
  intros m; induction m as [m IHm] using (well_founded_induction PeanoNat.Nat.lt_wf_0); intros j N' A' n Hjm HN' HA' Hn; subst m.
  assert (Hj : j < im_nn Mk) by (rewrite <- L2; apply List.nth_error_Some; congruence).
  destruct (nth_error_lt_some Ns j ltac:(lia)) as [N HN].
  destruct (nth_error_lt_some (tele_insts (im_nparams Mk) (sb_of_list Id Us) Ns) j) as [A HA].
  { rewrite length_tele_insts by exact HassN; rewrite length_im_nparams; lia. }
  pose proof (H _ _ _ _ HN HA Hn) as Hg.
  (** At the parameters' telescope, past the uniform ones *)
  assert (Eins : forall Ms Ms', List.length Ms = ind_nu D ->
             tele_insts (im_params D Mk) Id (Ms ++ Ms') = tele_insts (ind_uparams D) Id Ms ++ tele_insts (im_nparams Mk) (sb_of_list Id Ms) Ms')
    by (intros Ms Ms' HMs; unfold im_params; apply tele_insts_app; [ exact HassU | exact HMs ]).
  assert (LI : forall Ms, List.length Ms = ind_nu D -> List.length (tele_insts (ind_uparams D) Id Ms) = ind_nu D)
    by (intros Ms HMs; rewrite length_tele_insts by exact HassU; unfold ind_nu in *; lia).
  assert (LU' : List.length (List.firstn (ind_nu D) Ps') = ind_nu D) by (rewrite List.length_firstn; unfold im_np in LPs; lia).
  assert (HX : List.nth_error (Us ++ Ns) (ind_nu D + j) = Some N)
    by (rewrite List.nth_error_app2, HUl, PeanoNat.Nat.add_comm, PeanoNat.Nat.add_sub by lia; exact HN).
  assert (HY : List.nth_error Ps' (ind_nu D + j) = Some N').
  { rewrite <- (List.firstn_skipn (ind_nu D) Ps'), List.nth_error_app2, LU', PeanoNat.Nat.add_comm, PeanoNat.Nat.add_sub by lia;
      exact HN'. }
  assert (HT : List.nth_error (tele_insts (im_params D Mk) Id (Us ++ Ns)) (ind_nu D + j) = Some A)
    by (rewrite (Eins _ _ HUl), List.nth_error_app2, (LI _ HUl), PeanoNat.Nat.add_comm, PeanoNat.Nat.add_sub
          by (rewrite (LI _ HUl); lia); exact HA).
  pose proof (HP _ _ _ _ HX HY HT) as HNN.
  (** The type at [Ps'], glued after the ones before it ([IHm]) *)
  assert (HAP : Γ ⊢ A' ® NP k j (List.firstn j X)).
  { apply (ind_glu_components_nparams _ _ _ _ _ _ _ _ _ _ _ Hcomp k Mk j (List.skipn (ind_nu D) Ps') (List.firstn j X) A' HMk
             ltac:(rewrite List.length_firstn; lia) Hj HA').
    + intros j' N'' T'' n' Hj' HN'' HT'' Hn'.
      rewrite List.nth_error_firstn in Hn'; destruct (PeanoNat.Nat.ltb_spec j' j); [| discriminate ].
      rewrite List.firstn_firstn, PeanoNat.Nat.min_l by lia.
      exact (IHm j' Hj' j' N'' T'' n' eq_refl HN'' HT'' Hn').
    + apply tele_prefix_rel_of_full with (T := List.rev (im_nparams Mk));
        [ exact HXr | rewrite List.length_rev; unfold im_nn in Hj; lia ]. }
  exact (Hresp _ _ _ _ _ _ Hj Hg HNN HAP).
Qed.

Lemma ind_glu_typ_pred_resp_exp_eq : forall p D ups ns NP NEl AP AEl DP DEl k Mk n Γ A A',
    ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A -> Γ ⊢ A ≈ A' : Typeω@n ->
    ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A'.
Proof. intros * (Ps & HPs) HAA; exists Ps; eapply ind_typ_at_resp_exp_eq; eassumption. Qed.

Lemma ind_glu_typ_pred_resp_ctxsub : forall p D ups ns NP NEl AP AEl DP DEl k Mk n Γ A Δ,
    ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A -> Δ ⊆ Γ ->
    ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Δ A.
Proof. intros * (Ps & HPs) Hs; exists Ps; eapply ind_typ_at_resp_ctxsub; eassumption. Qed.

Lemma ind_glu_typ_pred_wk : forall p D ups ns NP NEl AP AEl DP DEl k Mk n Γ A Δ φ,
    ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Γ A -> Δ ⊢ᵏ φ : Γ ->
    ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk Typeω@n Δ A[φ]ʷ.
Proof. intros * (Ps & HPs) Hφ; eexists; eapply ind_typ_at_wk; eassumption. Qed.

Lemma ind_glu_exp_pred_resp_typ_exp_eq : forall p D ups ns NP NEl AP AEl DP DEl k Mk R n Γ A A' M m,
    ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k Mk R Typeω@n Γ A M m -> Γ ⊢ A ≈ A' : Typeω@n ->
    ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k Mk R Typeω@n Γ A' M m.
Proof.
  intros * [HM Hm Ps HPs Hk] HAA.
  refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Ps _ Hk);
    [ eapply wf_conv'; [ exact HM | exact HAA ] | eapply ind_typ_at_resp_exp_eq; eassumption ].
Qed.

Lemma ind_glu_exp_pred_wk : forall p D ups ns NP NEl AP AEl DP DEl k Mk R n Γ A M m Δ φ,
    ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k Mk R Typeω@n Γ A M m -> Δ ⊢ᵏ φ : Γ ->
    ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k Mk R Typeω@n Δ A[φ]ʷ M[φ]ʷ m.
Proof.
  intros * [HM Hm Ps HPs Hk] Hφ.
  refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm (List.map (fun P => P[φ]ʷ) Ps) _ _);
    [ mauto 3 | eapply ind_typ_at_wk; eassumption |].
  intros Θ ψ Ps' Hψ HPs'; rewrite map_wk_wk in HPs'; rewrite exp_wk_wk; apply Hk; [ eapply kripke_compose; eassumption | exact HPs' ].
Qed.

Lemma ind_glu_exp_pred_resp_exp_eq : forall p D ups ns NP NEl AP AEl DP DEl k Mk pm R n Γ A M M' m,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
    ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k Mk R Typeω@n Γ A M m -> Γ ⊢ M ≈ M' : A ->
    ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k Mk R Typeω@n Γ A M' m.
Proof.
  intros * Hl HMk Hh [HM Hm Ps HPs Hk] HMM.
  refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Ps HPs _); [ mauto 3 |].
  intros Δ φ Ps' Hφ HPs'.
  eapply ind_glu_elem_resp_exp_eq; [ exact (Hk Δ φ Ps' Hφ HPs') | exact HMk |].
  rewrite (im_ty_at_decl _ _ _ _ _ _ Hh), List.firstn_skipn.
  pose proof (ind_typ_at_params_conv p D ups ns NP NEl AP AEl DP DEl k Mk pm n Γ A Ps Δ φ Ps' Hl HMk Hh HPs Hφ HPs') as HPP.
  rewrite <- wk_apps_ind in HPP.
  destruct HPs as [HA _].
  assert (Γ ⊢ M ≈ M' : apps (a_ind p k) Ps) by (eapply wf_exp_eq_conv'; eassumption).
  eapply wf_exp_eq_conv'; [| exact HPP ].
  mauto 3.
Qed.

(** ** Record Types

    The type and element predicates of a record type, along an equation, a
    context refinement and a weakening. *)
Lemma wk_apps_record : forall p Ps φ, (apps (a_record p) Ps)[φ]ʷ = apps (a_record p) (List.map (fun P => P[φ]ʷ) Ps).
Proof. intros; rewrite apps_exp_wk; reflexivity. Qed.

Lemma record_typ_at_resp_exp_eq : forall p R ns FP FEl n Γ A A' Ns,
    record_typ_at p R ns FP FEl Typeω@n Γ A Ns -> Γ ⊢ A ≈ A' : Typeω@n ->
    record_typ_at p R ns FP FEl Typeω@n Γ A' Ns.
Proof.
  intros * [HA Hk] HAA; constructor; [ etransitivity; [ symmetry; exact HAA | exact HA ] | exact Hk ].
Qed.

Lemma record_typ_at_resp_ctxsub : forall p R ns FP FEl n Γ A Ns Δ,
    record_typ_at p R ns FP FEl Typeω@n Γ A Ns -> Δ ⊆ Γ ->
    record_typ_at p R ns FP FEl Typeω@n Δ A Ns.
Proof.
  intros * [HA Hk] Hs; constructor; [ eapply ctxsub_exp_eq; [ exact (ctx_sub_escape _ _ _ _ Hs) | exact HA ] |].
  intros Θ ψ Hψ; apply Hk; eapply kripke_ctxsub; eassumption.
Qed.

Lemma record_typ_at_wk : forall p R ns FP FEl n Γ A Ns Δ φ,
    record_typ_at p R ns FP FEl Typeω@n Γ A Ns -> Δ ⊢ᵏ φ : Γ ->
    record_typ_at p R ns FP FEl Typeω@n Δ A[φ]ʷ (List.map (fun N => N[φ]ʷ) Ns).
Proof.
  intros * [HA Hk] Hφ; constructor; [ rewrite <- wk_apps_record; mauto 3 |].
  intros Θ ψ Hψ; rewrite !map_wk_wk; apply Hk; eapply kripke_compose; eassumption.
Qed.

Lemma record_glu_typ_pred_resp_exp_eq : forall p R ns FP FEl n Γ A A',
    record_glu_typ_pred p R ns FP FEl Typeω@n Γ A -> Γ ⊢ A ≈ A' : Typeω@n ->
    record_glu_typ_pred p R ns FP FEl Typeω@n Γ A'.
Proof. intros * (Ns & HNs) HAA; exists Ns; eapply record_typ_at_resp_exp_eq; eassumption. Qed.

Lemma record_glu_typ_pred_resp_ctxsub : forall p R ns FP FEl n Γ A Δ,
    record_glu_typ_pred p R ns FP FEl Typeω@n Γ A -> Δ ⊆ Γ ->
    record_glu_typ_pred p R ns FP FEl Typeω@n Δ A.
Proof. intros * (Ns & HNs) Hs; exists Ns; eapply record_typ_at_resp_ctxsub; eassumption. Qed.

Lemma record_glu_typ_pred_wk : forall p R ns FP FEl n Γ A Δ φ,
    record_glu_typ_pred p R ns FP FEl Typeω@n Γ A -> Δ ⊢ᵏ φ : Γ ->
    record_glu_typ_pred p R ns FP FEl Typeω@n Δ A[φ]ʷ.
Proof. intros * (Ns & HNs) Hφ; eexists; eapply record_typ_at_wk; eassumption. Qed.

Lemma record_glu_exp_pred_resp_typ_exp_eq : forall p R ns FP FEl elem_rel n Γ A A' M m,
    record_glu_exp_pred p R ns FP FEl elem_rel Typeω@n Γ A M m -> Γ ⊢ A ≈ A' : Typeω@n ->
    record_glu_exp_pred p R ns FP FEl elem_rel Typeω@n Γ A' M m.
Proof.
  intros * [HM Hm Ns HNs vs Hvs Hk] HAA.
  refine (mk_record_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ Hm Ns _ vs Hvs Hk);
    [ eapply wf_conv'; [ exact HM | exact HAA ] | eapply record_typ_at_resp_exp_eq; eassumption ].
Qed.

Lemma record_glu_exp_pred_wk : forall p R ns FP FEl elem_rel n Γ A M m Δ φ,
    record_glu_exp_pred p R ns FP FEl elem_rel Typeω@n Γ A M m -> Δ ⊢ᵏ φ : Γ ->
    record_glu_exp_pred p R ns FP FEl elem_rel Typeω@n Δ A[φ]ʷ M[φ]ʷ m.
Proof.
  intros * [HM Hm Ns HNs vs Hvs Hk] Hφ.
  refine (mk_record_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ Hm (List.map (fun N => N[φ]ʷ) Ns) _ vs Hvs _);
    [ mauto 3 | eapply record_typ_at_wk; eassumption |].
  intros Θ ψ Ns' Hψ HNs'; rewrite map_wk_wk in HNs'; rewrite exp_wk_wk.
  apply Hk; [ eapply kripke_compose; eassumption | exact HNs' ].
Qed.

(** The predicates of a record type at two families of field gluings
    equivalent along related prefixes. *)
Definition record_fams_equiv (R : record_decl) (ns : list domain)
    (FP FP' : nat -> list domain -> glu_typ_pred) (FEl FEl' : nat -> list domain -> glu_exp_pred) : Prop :=
  forall k f T vs, List.nth_error (record_fields R) k = Some (f, T) -> tele_prefix_rel (canon_fields_rel R ns) k vs vs ->
    (FP k vs <∙> FP' k vs) /\ (FEl k vs <∙> FEl' k vs).

Lemma record_fields_glu_mono : forall R ns FP FEl FP' FEl' Γ Ns,
    record_fams_equiv R ns FP FP' FEl FEl' ->
    record_fields_glu R ns FP FEl Γ Ns -> record_fields_glu R ns FP' FEl' Γ Ns.
Proof.
  intros * Heq Hg k f T Ms ms Hk HMl Hml HMs Hp.
  destruct (Heq _ _ _ _ Hk Hp) as [EP _]; apply EP.
  apply (Hg k f T Ms ms); [ exact Hk | exact HMl | exact Hml | | exact Hp ].
  intros j g T' M m0 Hj HM Hm.
  assert (Hjk : j < k) by (rewrite <- Hml; apply List.nth_error_Some; congruence).
  destruct (Heq _ _ _ _ Hj (tele_prefix_rel_of_pre _ _ _ _ j Hp ltac:(lia))) as [_ EE]; apply EE.
  exact (HMs _ _ _ _ _ Hj HM Hm).
Qed.

Lemma record_typ_at_mono : forall p R ns FP FEl FP' FEl' U Γ A Ns,
    record_fams_equiv R ns FP FP' FEl FEl' ->
    record_typ_at p R ns FP FEl U Γ A Ns -> record_typ_at p R ns FP' FEl' U Γ A Ns.
Proof.
  intros * Heq [HA Hk]; constructor; [ exact HA |].
  intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as [Hp Hs Hf]; constructor; [ exact Hp | exact Hs |].
  intros Ns' HNs'; exact (record_fields_glu_mono _ _ _ _ _ _ _ _ Heq (Hf Ns' HNs')).
Qed.

(** At related parameters, given terms glued to the other side's: the
    readbacks agree, and the prefixes of the other side's canonical
    relations are the first side's. *)
Lemma params_glu_top_resp_per_top_ps : forall T ps ps' Γ Ps Ps',
    per_top_ps (List.rev T) ps ps' -> params_glu_top T Γ Ps ps -> params_glu_top T Γ Ps' ps' -> params_glu_top T Γ Ps ps'.
Proof.
  intros * Ht [L Ht' Hr] [_ _ Hr']; constructor; [ exact L | exact Ht' |].
  intros Δ φ Ms Hφ HR.
  destruct (Ht (length Δ)) as [C1 C2 HC1 HC2 E].
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (@functional_read gc_deps gc_stack)))))) as Fps.
  rewrite (Fps _ _ _ _ _ HR _ HC2); exact (glu_nfs_eq_at_upto _ _ _ _ _ _ E (Hr _ _ _ Hφ HC1) (Hr' _ _ _ Hφ HC2)).
Qed.

Lemma record_typ_at_resp_per : forall p R ns ns' FP FEl FP' FEl' U Γ A A' Ns Ns2,
    per_top_ps (List.rev (record_params R)) ns ns' ->
    (forall k vs, k <= List.length (record_fields R) ->
       tele_prefix_rel (canon_fields_rel R ns') k vs vs -> tele_prefix_rel (canon_fields_rel R ns) k vs vs) ->
    record_typ_at p R ns FP FEl U Γ A Ns -> record_typ_at p R ns' FP' FEl' U Γ A' Ns2 ->
    record_typ_at p R ns' FP FEl U Γ A Ns.
Proof.
  intros * Ht Hmv [HA Hk] [_ Hk']; constructor; [ exact HA |].
  intros Δ φ Hφ; destruct (Hk Δ φ Hφ) as [Hp Hs Hf]; destruct (Hk' Δ φ Hφ) as [Hp' _ _]; constructor;
    [ exact (params_glu_top_resp_per_top_ps _ _ _ _ _ _ Ht Hp Hp') | exact Hs |].
  intros Ns' HNs' k f T Ms ms Hfk HMl Hml HMs Hpre.
  assert (Hlt : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence).
  exact (Hf Ns' HNs' k f T Ms ms Hfk HMl Hml HMs (Hmv k ms ltac:(lia) Hpre)).
Qed.

(** The projections of an element related to itself are related to
    themselves, prefix by prefix. *)
Lemma record_projs_prefix_diag : forall R ns m vs k,
    record_rel R (canon_fields_rel R ns) m m -> record_projs R m vs -> k <= List.length (record_fields R) ->
    tele_prefix_rel (canon_fields_rel R ns) k (List.firstn k vs) (List.firstn k vs).
Proof.
  intros * [vs1 vs2 H1 H2 Hrel] Hvs Hk.
  pose proof (record_projs_functional _ _ _ _ H1 Hvs) as ->; pose proof (record_projs_functional _ _ _ _ H2 Hvs) as ->.
  exact (tele_prefix_rel_of_full _ _ _ _ _ Hrel Hk).
Qed.

Lemma record_glu_exp_mono : forall p R ns FP FEl FP' FEl' elem_rel elem_rel' U Γ A M m,
    record_fams_equiv R ns FP FP' FEl FEl' -> (elem_rel <~> elem_rel') ->
    (elem_rel <~> record_rel R (canon_fields_rel R ns)) ->
    record_glu_exp p R ns FP FEl elem_rel U Γ A M m -> record_glu_exp p R ns FP' FEl' elem_rel' U Γ A M m.
Proof.
  intros * Heq HEE HE [HM Hm Ns HNs vs Hvs Hk].
  refine (mk_record_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ (proj1 (HEE _ _) Hm) Ns
            (record_typ_at_mono _ _ _ _ _ _ _ _ _ _ _ Heq HNs) vs Hvs _); [ exact HM |].
  intros Δ φ Ns' Hφ HNs' k f T r Hfk Hr.
  assert (Hlt : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence).
  destruct (Heq _ _ _ _ Hfk (record_projs_prefix_diag _ _ _ _ k (proj1 (HE _ _) Hm) Hvs ltac:(lia))) as [_ EE].
  apply EE; exact (Hk Δ φ Ns' Hφ HNs' k f T r Hfk Hr).
Qed.

(** An element of a record type along an equation of terms: each field's
    projection moves along the congruence, at the field's type moved along
    the projections before it ([record_pre_eq]); the gluings of the fields
    move along both ([HFr] and [HFt]). *)
Lemma record_glu_exp_pred_resp_exp_eq : forall p R ns FP FEl elem_rel n Γ A M M' m,
    record_lookup gc_deps gc_stack p = Some R ->
    (forall k f T vs Δ T' N N' r, List.nth_error (record_fields R) k = Some (f, T) ->
       tele_prefix_rel (canon_fields_rel R ns) k vs vs ->
       Δ ⊢ N : T' ® r ∈ FEl k vs -> Δ ⊢ N ≈ N' : T' -> Δ ⊢ N' : T' ® r ∈ FEl k vs) ->
    (forall k f T vs Δ T' T'' N r, List.nth_error (record_fields R) k = Some (f, T) ->
       tele_prefix_rel (canon_fields_rel R ns) k vs vs ->
       Δ ⊢ N : T' ® r ∈ FEl k vs -> Δ ⊢ T' ≈ T'' : abs_kind_sort (record_field_kind R k) Typeω@n ->
       Δ ⊢ N : T'' ® r ∈ FEl k vs) ->
    elem_rel <~> record_rel R (canon_fields_rel R ns) ->
    record_glu_exp_pred p R ns FP FEl elem_rel Typeω@n Γ A M m -> Γ ⊢ M ≈ M' : A ->
    record_glu_exp_pred p R ns FP FEl elem_rel Typeω@n Γ A M' m.
Proof.
  intros * Hl HFr HFt HE [HM Hm Ns HNs vs Hvs Hk] HMM.
  refine (mk_record_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ Hm Ns HNs vs Hvs _); [ gen_presups; eassumption |].
  intros Δ φ Ns' Hφ HNs' k f T r Hfk Hr.
  assert (Hlt : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence).
  pose proof (record_projs_prefix_diag _ _ _ _ k (proj1 (HE _ _) Hm) Hvs ltac:(lia)) as Hpre.
  pose proof (Hk Δ φ Ns' Hφ HNs' k f T r Hfk Hr) as G.
  destruct HNs as [HAeq Hwk]; destruct (Hwk Δ φ Hφ) as [[HNl HNt _] HS _].
  destruct HNs' as [HNl' HNs'].
  assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
  assert (HMMa : Δ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns)).
  { rewrite <- wk_apps_record.
    eapply wf_exp_eq_conv'; [ mauto 3 |]; mauto 3. }
  assert (Hrt : Δ ⊢ a_record p : record_ty R).
  { assert (HAt : Δ ⊢ (apps_exp (a_record p) Ns)[φ]ʷ : Typeω@n) by (gen_presups; mauto 3).
    rewrite wk_apps_record in HAt; eapply wf_record_own_apps; [ exact HAt | exact Hl ]. }
  destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i0 Hty HF HSu HFs _].
  rewrite Hl in Hl0; injection Hl0 as <-.
  pose proof (wf_record_closed _ _ _ _ _ HΔ Hl) as Hc.
  rewrite List.length_map in HNl, HNl'.
  pose proof (wf_exp_eq_record_apps _ _ _ _ _ (List.map (fun N => N[φ]ʷ) Ns) Ns' Hrt Hl
                ltac:(rewrite List.length_map; exact HNl) ltac:(lia) HNs') as Happs.
  assert (HNt' : forall j Y T0, List.nth_error Ns' j = Some Y -> List.nth_error (tele_insts (record_params R) Id Ns') j = Some T0 ->
             Δ ⊢ Y : T0)
    by (eapply (record_params_eq_right _ _ _ R (List.map (fun N => N[φ]ʷ) Ns) Ns');
        [ exact Hc | exact Hass | exact HF | exact HΔ | rewrite List.length_map; exact HNl | lia | exact HNs' ]).
  destruct (record_sort_inst_cong _ _ _ R (List.map (fun N => N[φ]ʷ) Ns) Ns' Hc Hass HSu HΔ
              ltac:(rewrite List.length_map; exact HNl) ltac:(lia) HNs') as [is HSS].
  assert (HS' : Δ ⊢ (record_sort R)[sb_of_list Id Ns'] ⊆ Typeω@n).
  { eapply wf_subtyp_trans; [| exact HS ].
    eapply wf_subtyp_refl; [ gen_presups; eassumption | constructor | symmetry; exact HSS ]. }
  assert (HMMb : Δ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : apps_exp (a_record p) Ns').
  { eapply wf_exp_eq_conv'; [ exact HMMa |].
    eapply wf_exp_eq_subtyp'; [ exact Happs | eapply wf_subtyp_trans; [| exact HS ];
                                eapply wf_subtyp_refl; [ gen_presups; eassumption | constructor
                                                       | apply wf_exp_eq_refl; gen_presups; eassumption ] ]. }
  pose proof (record_pre_eq _ _ _ _ _ _ _ _ HMMb Hrt Hl ltac:(lia) HNt' k ltac:(lia)) as Hpe.
  pose proof (record_field_sort_cong _ _ _ R k f T Ns' (record_pre R k M[φ]ʷ) (Ns' ++ record_pre R k M'[φ]ʷ)
                Hc Hass HFs HΔ Hfk ltac:(lia)
                ltac:(apply length_record_pre; lia) ltac:(rewrite List.length_app, length_record_pre by lia; lia) Hpe) as HTT.
  assert (HTTn : Δ ⊢ T[sb_of_list Id (Ns' ++ record_pre R k M[φ]ʷ)] ≈ T[sb_of_list Id (Ns' ++ record_pre R k M'[φ]ʷ)]
                   : abs_kind_sort (record_field_kind R k) Typeω@n)
    by (eapply abs_kind_sort_exp_eq_up; [ exact HTT | exact HS' ]).
  assert (Hp : Δ ⊢ a_proj f M[φ]ʷ : T[sb_of_list Id (Ns' ++ record_pre R k M[φ]ʷ)])
    by (eapply wf_proj; [ gen_presups; eassumption | exact Hrt | exact Hl | lia | exact HNt' | exact Hfk
                        | exact (presup_exp_eq_left HTTn) | apply type_sort_abs_kind; constructor ]).
  assert (Hp' : Δ ⊢ a_proj f M'[φ]ʷ : T[sb_of_list Id (Ns' ++ record_pre R k M'[φ]ʷ)])
    by (eapply wf_proj; [ gen_presups; eassumption | exact Hrt | exact Hl | lia | exact HNt' | exact Hfk
                        | exact (presup_exp_eq_right HTTn) | apply type_sort_abs_kind; constructor ]).
  assert (Hpp : Δ ⊢ a_proj f M[φ]ʷ ≈ a_proj f M'[φ]ʷ : T[sb_of_list Id (Ns' ++ record_pre R k M[φ]ʷ)])
    by (eapply wf_exp_eq_proj_cong; [ exact HMMb | exact Hrt | exact Hl | lia | exact HNt' | exact Hfk
                                    | exact (presup_exp_eq_left HTTn) | apply type_sort_abs_kind; constructor
                                    | eapply wf_conv_rel; [ exact Hp' | symmetry; exact HTTn ] ]).
  eapply HFt; [ exact Hfk | exact Hpre | eapply HFr; [ exact Hfk | exact Hpre | exact G | exact Hpp ] | exact HTTn ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve glu_lvl_escape glu_lvl_resp_ctxsub : mctt.
(** [glu_lvl] has one constructor, so [split] breaks a goal
    [glu_lvl Γ M m] into its premises; the readback clause is then
    [glu_lvl_readback], and it is a hint so that the shared scripts reach it. *)
#[local]
Hint Resolve glu_lvl_resp_exp_eq glu_lvl_readback glu_lvl_well_scoped_readback : mctt.
#[global]
Ltac simpl_glu_rel :=
  apply_equiv_left;
  repeat invert_glu_rel1;
  apply_equiv_left;
  destruct_all;
  destruct_ind_glu_exp;
  (** The elements of a type of levels are related levels of its sort; the
      lemmas about glued levels need the first half. *)
  repeat match goal with
    | H : per_lvl_at _ ?m ?m' |- _ =>
        lazymatch goal with
        | _ : per_lvl m m' |- _ => fail
        | _ => pose proof (per_lvl_at_lvl _ _ _ H)
        end
    end;
  gen_presups.

(** The sort of the kind of a glued type's value, in a case of the
    induction on [glu_univ_elem]: the kind computes at a known head; a
    neutral type's is relevant ([glu_univ_elem_core_neut]), a
    proposition's propositional ([per_prop_left]). *)
#[global]
Ltac simpl_glu_sort :=
  repeat match goal with
    | H : domain_kind ?a = _ |- context [domain_kind ?a] => rewrite H
    | H : domain_kind ?a = _, H' : context [domain_kind ?a] |- _ =>
        lazymatch type of H' with domain_kind a = _ => fail | _ => rewrite H in H' end
    | H : per_prop ?a _ |- context [domain_kind ?a] => rewrite (per_prop_left _ _ H)
    | H : per_prop ?a _, H' : context [domain_kind ?a] |- _ =>
        lazymatch type of H' with domain_kind a = _ => fail | _ => rewrite (per_prop_left _ _ H) in H' end
    end;
  repeat match goal with H : context [abs_kind_sort] |- _ => progress cbn [domain_kind abs_kind_sort] in H end;
  cbn [domain_kind abs_kind_sort].

(** [LevelSort] in a typing or an equation: impossible, as it is of no
    sort ([level_sort_untyped]). *)
#[global]
Ltac level_sort_in_equation :=
  match goal with
  | H : ?A = LevelSort, H' : _ ⊢ ?A ≈ _ : _ |- _ => rewrite H in H'; exact (level_sort_untyped (presup_exp_eq_left H'))
  | H : ?A = LevelSort, H' : _ ⊢ _ ≈ ?A : _ |- _ => rewrite H in H'; exact (level_sort_untyped (presup_exp_eq_right H'))
  | H : ?A = LevelSort, H' : _ ⊢ ?A : _ |- _ => rewrite H in H'; exact (level_sort_untyped H')
  | H' : _ ⊢ LevelSort ≈ _ : _ |- _ => exact (level_sort_untyped (presup_exp_eq_left H'))
  | H' : _ ⊢ _ ≈ LevelSort : _ |- _ => exact (level_sort_untyped (presup_exp_eq_right H'))
  | H' : _ ⊢ LevelSort : _ |- _ => exact (level_sort_untyped H')
  end.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The sort a glued type other than [LevelSort] is a type of: the sort of
    its value's kind next to the large universe of the index.  ([LevelSort]
    is of no sort.) *)
Lemma glu_univ_elem_univ_lvl_gen : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    not_level_sort a ->
    forall Γ A,
      Γ ⊢ A ® P ->
      Γ ⊢ A : abs_kind_sort (domain_kind a) Typeω@(large_level i).
Proof.
  simpl.
  glu_univ_elem_induction1; intros; simpl_glu_sort.
  10:{ apply_equiv_left; match goal with H : exists Ns, record_typ_at _ _ _ _ _ _ _ _ Ns |- _ => destruct H as (Ns & [HA _]) end;
      gen_presups; assumption. }
  9:{ apply_equiv_left; match goal with H : exists Ps, ind_typ_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ps |- _ => destruct H as (Ps & HA & _) end;
      gen_presups; assumption. }
  (** [LevelSort]: excluded *)
  5:{ exfalso; match goal with H : not_level_sort _ |- _ => apply H; reflexivity end. }
  all: simpl_glu_rel; trivial.
Qed.

Lemma glu_univ_elem_univ_lvl : forall i U P El a,
    abs_kind_sort (domain_kind a) Typeω@(large_level i) = U ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    not_level_sort a ->
    forall Γ A,
      Γ ⊢ A ® P ->
      Γ ⊢ A : U.
Proof. intros * <- **; eapply glu_univ_elem_univ_lvl_gen; eassumption. Qed.

Lemma glu_univ_elem_typ_resp_exp_eq : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A A',
      Γ ⊢ A ® P ->
      Γ ⊢ A ≈ A' : abs_kind_sort (domain_kind a) Typeω@(large_level i) ->
      Γ ⊢ A' ® P.
Proof.
  simpl.
  glu_univ_elem_induction1; intros; simpl_glu_sort.
  10:{ apply_equiv_left; eapply record_glu_typ_pred_resp_exp_eq; eassumption. }
  9:{ apply_equiv_left; eapply (ind_glu_typ_pred_resp_exp_eq p D ups ns NP NEl AP AEl DP DEl); eassumption. }
  all: simpl_glu_rel;
    (** A small universe keeps the level term it is indexed by, and composes
        the equation with the one of the two types. *)
    try solve [ destruct_conjs; glu_witness2;
                [ eassumption | transitivity A; mauto 4 ] ];
    mauto 4.
  (** A proposition and a neutral type: the readback equations move along
      the equation, weakened. *)
  (** [LevelSort]: of no sort, so in no equation *)
  all: try solve [ exfalso; level_sort_in_equation ].
  all: split; [ assumption | intros; first [ eapply glu_nf_eq_exp_eq | eapply glu_ne_eq_exp_eq ]; [| eauto ]; symmetry; mauto 4 ].
Qed.

Add Parametric Morphism i P El a (H : glu_univ_elem i P El a) Γ : (P Γ)
    with signature wf_exp_eq gc_deps gc_stack Γ (abs_kind_sort (domain_kind a) Typeω@(large_level i)) ==> iff
    as glu_univ_elem_typ_morphism_iff1.
Proof.
  split; intros; eapply glu_univ_elem_typ_resp_exp_eq; mauto 2.
Qed.

(** A type glued at an index, along an equation at the sort of its
    value's kind. *)
Lemma glu_univ_typ_resp_exp_eq : forall j m Γ M M' κ,
    Γ ⊢ M ® glu_univ_typ j m -> domain_kind m = κ -> Γ ⊢ M ≈ M' : abs_kind_sort κ Typeω@(large_level j) ->
    Γ ⊢ M' ® glu_univ_typ j m.
Proof. intros * [P El Hm HP] <- HMM; econstructor; [ exact Hm | eapply glu_univ_elem_typ_resp_exp_eq; eassumption ]. Qed.

Lemma glu_univ_elem_trm_resp_typ_exp_eq : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ M A m A',
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ A ≈ A' : abs_kind_sort (domain_kind a) Typeω@(large_level i) ->
      Γ ⊢ M : A' ® m ∈ El.
Proof.
  simpl.
  glu_univ_elem_induction1; intros; simpl_glu_sort.
  10:{ apply_equiv_left; eapply record_glu_exp_pred_resp_typ_exp_eq; eassumption. }
  9:{ apply_equiv_left; eapply (ind_glu_exp_pred_resp_typ_exp_eq p D ups ns NP NEl AP AEl DP DEl); eassumption. }
  (** A proof: its proposition's readback equations move along the
      equation, weakened *)
  7:{ simpl_glu_rel; econstructor;
        [| eapply wf_conv_sort; [ eassumption | eassumption | constructor | eassumption ] | eassumption |].
      - match goal with H : prop_glu_typ_pred _ _ _ |- _ => destruct H as [_ HR] end;
          split; [ assumption | intros; eapply glu_nf_eq_exp_eq; [| eapply HR; eassumption ]; symmetry; mauto 4 ].
      - intros Δ φ R Hφ HR; eapply wf_exp_eq_conv_sort; [ eapply proof_glu_exp_read; eassumption | mauto 4 | constructor | mauto 4 ]. }
  (** A function: the type moves by conversion at the codomain's sort *)
  6:{ simpl_glu_rel; econstructor; try eassumption;
      [ eapply wf_conv_rel; eassumption | etransitivity; [ symmetry; eassumption | eassumption ] ]. }
  (** An element of [LevelSort]: its type is in no equation *)
  5:{ simpl_glu_rel; exfalso; level_sort_in_equation. }
  (** A proposition, as an element of [Prop]: the type equation composes *)
  4:{ simpl_glu_rel; econstructor; try eassumption;
      [ etransitivity; [ symmetry; eassumption | eassumption ] | eapply wf_conv'; eassumption ]. }
  all:
    simpl_glu_rel; repeat split; intros;
    (** A small universe keeps the level term it is indexed by, and composes
        the equation with the one of the two types. *)
    try solve [ glu_witness2; [ eassumption | transitivity A; mauto 4 ] ];
    mauto 3.
  (** The readback clauses of a neutral type, and those of an element of a
      small universe and of a neutral, which move their type by conversion
      in the ambient universe. *)
  all: first
    [ eapply glu_ne_eq_exp_eq; [| eauto ]; symmetry; mauto 4
    | eapply (glu_nf_eq_conv _ _ _ _ _ ak_relevant); [ cbn [abs_kind_sort]; mauto 3 | eauto ]
    | eapply (glu_ne_eq_conv _ _ _ _ _ ak_relevant); [ cbn [abs_kind_sort]; mauto 3 | eauto ] ].
Qed.

Add Parametric Morphism i P El a (H : glu_univ_elem i P El a) Γ : (El Γ)
    with signature wf_exp_eq gc_deps gc_stack Γ (abs_kind_sort (domain_kind a) Typeω@(large_level i)) ==> eq ==> eq ==> iff
    as glu_univ_elem_trm_morphism_iff1.
Proof.
  split; intros;
    eapply glu_univ_elem_trm_resp_typ_exp_eq;
    mauto 2.
Qed.

Lemma glu_univ_elem_typ_resp_ctxsub : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A Δ,
      Γ ⊢ A ® P ->
      Δ ⊆ Γ ->
      Δ ⊢ A ® P.
Proof.
  simpl.
  glu_univ_elem_induction1; intros.
  10:{ apply_equiv_left; eapply record_glu_typ_pred_resp_ctxsub; eassumption. }
  9:{ apply_equiv_left; eapply (ind_glu_typ_pred_resp_ctxsub p D ups ns NP NEl AP AEl DP DEl); eassumption. }
  all:
    simpl_glu_rel;
    (** A small universe: its level term and its equation both move to the
        refined context. *)
    try solve [ glu_witness2;
                [ eapply glu_lvl_resp_ctxsub; eassumption | mauto 3 ] ];
    mauto 3.

  - assert (HIT : Δ ⊢ IT : abs_kind_sort κd Typeω@(large_level i)) by mauto 3.
    assert (Δ ▹{κd} IT ⊆ Γ ▹{κd} IT).
    { eapply ctx_sub_extend with (Srt := abs_kind_sort κd Typeω@(large_level i));
        [ eassumption | eassumption | apply sort_kind_abs_kind_sort | exact HIT | apply sort_kind_abs_kind_sort |].
      eapply wf_subtyp_refl; [ exact HIT | apply type_sort_abs_kind; constructor | mauto 3 ]. }
    econstructor; mauto 3; intros; mauto 4.

  (** A proposition and a neutral type *)
  - split; [ mauto 3 | intros; mauto 4 ].
  - split; [ mauto 3 | intros; mauto 4 ].
Qed.

Lemma glu_lvl_resp_wk : forall Γ M a n,
    glu_lvl n Γ M a ->
    forall Δ φ,
      Δ ⊢ᵏ φ : Γ ->
      glu_lvl n Δ M[φ]ʷ a.
Proof.
  intros * H * ? Δ' ψ M' Hψ Hr.
  rewrite exp_wk_wk.
  assert (Δ' ⊢ᵏ φ ⊙ ψ : Γ) by mauto 3.
  exact (H _ _ _ ltac:(eassumption) Hr).
Qed.

Hint Resolve glu_lvl_resp_wk : mctt.

Lemma glu_univ_elem_trm_escape : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ M A m,
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ M : A.
Proof.
  simpl.
  glu_univ_elem_induction1; intros;
    simpl_glu_rel; mauto 4.
  (** A level: of [Level@n], and its type is equal to it in [LevelSort] *)
  eapply wf_conv_sort; [ eapply glu_lvl_escape; eassumption | eassumption | constructor | symmetry; eassumption ].
Qed.

Lemma glu_univ_elem_per_univ : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Dom a ≈ a ∈ per_univ i.
Proof.
  simpl.
  glu_univ_elem_induction1; intros.
  10:{ eexists; eassumption. }
  9:{ eexists; eassumption. }
  all: eexists;
    try solve [per_univ_elem_econstructor; try reflexivity; trivial].
  (** A [Π]: its clause carries its relation *)
  eassumption.
Qed.

Hint Resolve glu_univ_elem_per_univ : mctt.

(** A type glued at [m] that is of the sort of a kind: [m] is of that kind
    (kinds are unique, [exp_eq_same_kind]) and not [LevelSort] (which is of
    no type, [level_sort_untyped]).  One of a universe is so an element of
    the universe of the index. *)
Lemma glu_univ_elem_typ_kind : forall j P El m Γ M κ l,
    DG m ∈ glu_univ_elem j ↘ P ↘ El -> Γ ⊢ M ® P -> Γ ⊢ M : abs_kind_sort κ Typeω@l ->
    domain_kind m = κ /\ not_level_sort m.
Proof.
  intros * Hm HM HMl.
  assert (Hn : not_level_sort m).
  { intros ->; basic_invert_glu_univ_elem Hm;
      try (match goal with H : per_prop _ _ |- _ => destruct H as [Hp _ _]; cbn in Hp; discriminate end).
    apply_equiv_left; destruct HM as [-> _]; eapply level_sort_untyped; exact HMl. }
  pose proof (glu_univ_elem_univ_lvl_gen _ _ _ _ Hm Hn _ _ HM) as HMk.
  split; [| exact Hn ].
  symmetry; eapply exp_eq_same_kind with (S := abs_kind_sort κ Typeω@l);
    [ apply wf_exp_eq_refl; exact HMl | apply sort_kind_abs_kind_sort | exact HMk | apply sort_kind_abs_kind_sort ].
Qed.

Lemma glu_univ_elem_univ_element : forall j P El m Γ M l,
    DG m ∈ glu_univ_elem j ↘ P ↘ El -> Γ ⊢ M ® P -> Γ ⊢ M : Typeω@l ->
    Dom m ≈ m ∈ per_universe_elements (per_univ j).
Proof.
  intros * Hm HM HMl.
  destruct (glu_univ_elem_typ_kind j P El m Γ M ak_relevant l Hm HM HMl) as [Hk Hn].
  constructor; [ exact (glu_univ_elem_per_univ _ _ _ _ Hm) | exact Hk | exact Hk | exact Hn | exact Hn ].
Qed.

Lemma glu_univ_elem_per_elem : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ M A m R,
      Γ ⊢ M : A ® m ∈ El ->
      DF a ≈ a ∈ per_univ_elem i ↘ R ->
      Dom m ≈ m ∈ R.
Proof.
  simpl.
  glu_univ_elem_induction1; intros.
  10:{ simpl_glu_rel. match goal with HR : per_univ_elem _ ?R (d_record _ _) (d_record _ _), HE : per_univ_elem _ ?E (d_record _ _) (d_record _ _), Hm : ?E ?m ?m |- ?R ?m ?m => assert (EE : E <~> R) by (eapply per_univ_elem_right_irrel; eassumption); apply EE; exact Hm end. }
  9:{ simpl_glu_rel. match goal with HR : per_univ_elem _ ?R (d_ind _ _ _) (d_ind _ _ _), HE : per_univ_elem _ ?E (d_ind _ _ _) (d_ind _ _ _), Hm : ?E ?m ?m |- ?R ?m ?m => assert (EE : E <~> R) by (eapply per_univ_elem_right_irrel; eassumption); apply EE; exact Hm end. }
  (** A function: the clause's relation is the given one *)
  6:{ simpl_glu_rel. match goal with HR : per_univ_elem _ ?R (d_pi _ _ _ _ _) (d_pi _ _ _ _ _), HE : per_univ_elem _ ?E (d_pi _ _ _ _ _) (d_pi _ _ _ _ _), Hm : ?E ?m ?m |- ?R ?m ?m => assert (EE : E <~> R) by (eapply per_univ_elem_right_irrel; eassumption); apply EE; exact Hm end. }
  all:
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H);
    simpl_glu_rel;
    try fold (per_univ j m m); try fold (per_univ (us (domain_level_real l)) m m);
    mauto 4.
  (** An element of a universe: a type of it, glued as one *)
  all: try solve [ eapply glu_univ_elem_univ_element; [ eassumption | eassumption | eapply wf_conv'; eassumption ] ].
  - assert (HMt : Γ ⊢ M : Type⟨suniv_glu_typ_lvl⟩) by (eapply wf_conv'; eassumption).
    assert (HL : Γ ⊢ suniv_glu_typ_lvl : Level@suniv_glu_typ_sort) by (eapply glu_lvl_escape; eassumption).
    destruct (wf_exp_is_univ_large (wf_is_univ_small _ _ _ _ _ HL) HMt) as [l0 Hl0].
    eapply glu_univ_elem_univ_element; eassumption.
  (** An element of [LevelSort]: a level code, glued as a type at the
      least small index *)
  - split; [ assumption | split; [ assumption | eapply glu_univ_elem_per_univ; eassumption ] ].
Qed.

Lemma glu_univ_elem_trm_typ : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ M A m,
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ A ® P.
Proof.
  simpl.
  glu_univ_elem_induction1; intros.
  10:{ apply_equiv_left;
      match goal with H : record_glu_exp_pred _ _ _ _ _ _ _ _ _ _ _ |- _ => destruct H as [_ _ Ns HNs _ _ _] end;
      exists Ns; exact HNs. }
  9:{ apply_equiv_left;
      match goal with H : ind_glu_exp_pred _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => destruct H as [_ _ Ps HPs _] end;
      exists Ps; exact HPs. }
  all:
    simpl_glu_rel;
    mauto 4.

  (** A function: its codomain at a glued argument is glued, as the
      codomain's value at the argument is *)
  econstructor; eauto.
  intros Δ φ N n Hφ HN equiv_n.
  match goal with Hp : per_univ_elem _ _ (d_pi _ _ _ _ _) _ |- _ => invert_per_univ_elem Hp end.
  match goal with Hrm : forall c c' (e : _), rel_mod_eval _ _ _ _ _ _ |- _ => destruct (Hrm n n equiv_n) as [b b' Hb Hb' _] end.
  match goal with Ha : forall Δ0 φ0 N0 n0, _ -> _ -> forall e : _, exists mn, _ /\ _ |- _ =>
    destruct (Ha Δ φ N n Hφ HN equiv_n) as (mn & _ & HO) end.
  eauto.
Qed.

Lemma glu_univ_elem_trm_univ_lvl : forall i U P El a,
    abs_kind_sort (domain_kind a) Typeω@(large_level i) = U ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    not_level_sort a ->
    forall Γ M A m,
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ A : U.
Proof.
  intros. eapply glu_univ_elem_univ_lvl; [ eassumption | eassumption | eassumption | eapply glu_univ_elem_trm_typ ]; eassumption.
Qed.

Lemma glu_univ_elem_trm_resp_exp_eq : forall i P El a,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A M m M',
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ M ≈ M' : A ->
      Γ ⊢ M' : A ® m ∈ El.
Proof.
  simpl.
  glu_univ_elem_induction1; intros.
  10:{ apply_equiv_left; eapply record_glu_exp_pred_resp_exp_eq; [ exact H | | | eapply record_rel_canon; eassumption | eassumption | eassumption ].
      - intros * Hk Hp HN HNN; destruct (H1 _ _ _ _ Hk Hp) as [b Hb]; eapply (H3 _ _ _ _ _ Hk Hp Hb); eassumption.
      - intros * Hk Hp HN HTT; destruct (H1 _ _ _ _ Hk Hp) as [b Hb].
        (** The field's type is of the field's kind, so its value is *)
        pose proof (H2 _ _ _ _ _ Hk Hp Hb) as Hgb.
        destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hgb (glu_univ_elem_trm_typ _ _ _ _ Hgb _ _ _ _ HN)
                    (presup_exp_eq_left HTT)) as [Hkb _].
        eapply (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hgb); [ eassumption | rewrite Hkb; eassumption ]. }
  9:{ apply_equiv_left; eapply (ind_glu_exp_pred_resp_exp_eq p D ups ns NP NEl AP AEl DP DEl); eassumption. }
  (** A proof: its typing and its readback equations move along *)
  7:{ simpl_glu_rel; econstructor; [ eassumption | mauto 3 | eassumption |].
      intros Δ φ R Hφ HR; transitivity (M[φ]ʷ); [ symmetry; mauto 4 | eapply proof_glu_exp_read; eassumption ]. }
  (** A type of levels, as an element of [LevelSort]: glued as a type
      along the equation at [LevelSort], the sort of its kind *)
  5:{ simpl_glu_rel; subst; econstructor; [ reflexivity | eassumption | eassumption |].
      eapply glu_univ_typ_resp_exp_eq; [ econstructor; eassumption | apply level_code_kind; eassumption | eassumption ]. }
  (** A proposition, as an element of [Prop]: glued as one along the
      equation at [Prop] *)
  4:{ simpl_glu_rel; econstructor; [ eassumption | eassumption | eassumption |].
      assert (HMM : Γ ⊢ M ≈ M' : Propₘ) by (eapply wf_exp_eq_conv'; eassumption).
      eapply prop_glu_typ_pred_resp_exp_eq; eassumption. }
  all:
    simpl_glu_rel;
    repeat split; mauto 3.

  (** The type of the element is unchanged, so a small universe's level term
      and its equation carry over. *)
  all: try solve [ eapply suniv_glu_typ_pred_intro; eassumption ].

  (** An element of a large universe: glued as a type along the equation
      at the universe, of the relevant kind *)
  - assert (HMj : Γ ⊢ M : Typeω@j) by (eapply wf_conv'; eassumption).
    destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ ak_relevant _ glu_typ_at_elem glu_typ_at_glu HMj) as [Hk _].
    eapply glu_univ_typ_resp_exp_eq; [ econstructor; eassumption | exact Hk | eapply wf_exp_eq_conv'; eassumption ].

  (** An element of a small universe: its type-level gluing moves along
      the equation lifted to the ambient [Typeω@0] by cumulativity, and its
      readback clause by transitivity. *)
  - assert (HM0' : Γ ⊢ M : Typeω@0) by (eapply suniv_elem_large; eassumption).
    destruct (glu_univ_elem_typ_kind _ _ _ _ _ _ ak_relevant _ glu_typ_at_elem glu_typ_at_glu HM0') as [Hk _].
    eapply glu_univ_typ_resp_exp_eq; [ econstructor; eassumption | exact Hk | eapply suniv_elem_eq_large; eassumption ].
  - intros; eapply glu_nf_eq_exp_eq; [| eauto ]; symmetry; mauto 3.

  (** A level: the readback clause, by transitivity at [Level@n] *)
  - assert (Γ ⊢ M ≈ M' : Level@n) by (eapply wf_exp_eq_conv_sort; [ eassumption | eassumption | constructor | eassumption ]).
    transitivity M[φ]ʷ; [ symmetry; mauto 3 | eapply glu_lvl_readback; eassumption ].

  (** A function: applied, the two are equal *)
  - econstructor; eauto.
    intros Δ φ N n Hφ HN equiv_n.
    match goal with Hp : per_univ_elem _ _ (d_pi _ _ _ _ _) _ |- _ => invert_per_univ_elem Hp end.
    assert (Δ ⊢ N : IT[φ]ʷ) by eauto using glu_univ_elem_trm_escape.
    match goal with Ha : forall Δ0 φ0 N0 n0, _ -> _ -> forall e : _, exists mn, _ /\ _ |- _ =>
      destruct (Ha Δ φ N n Hφ HN equiv_n) as (mn & Hmn & HO) end.
    eexists; split; [ exact Hmn |].
    match goal with Hrm : forall c c' (e : _), rel_mod_eval _ _ _ _ _ _ |- _ => destruct (Hrm n n equiv_n) as [b b' Hb Hb' _] end.
    enough (Δ ⊢ M[φ]ʷ $ N ≈ M'[φ]ʷ $ N : OT[(ι φ),,N]) by eauto.
    assert (Γ ⊢ M ≈ M' : a_pi κd κc IT OT) as Hty by (eapply wf_exp_eq_conv_kind; eassumption).
    assert (Δ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : (a_pi κd κc IT OT)[φ]ʷ) as Hty' by mauto 2.
    rewrite exp_wk_pi in Hty'.
    eapply wf_exp_eq_app_cong' with (N := N) (N' := N) in Hty'; [| mauto 2].
    rewrite exp_sub_wk_q_extend in Hty'.
    eassumption.
  (** A neutral: the readback clause, by transitivity *)
  - intros; eapply glu_ne_eq_exp_eq; [| eauto ]; symmetry; mauto 4.
Qed.

Add Parametric Morphism i P El a (H : glu_univ_elem i P El a) Γ T : (El Γ T)
    with signature wf_exp_eq gc_deps gc_stack Γ T ==> eq ==> iff as glu_univ_elem_trm_morphism_iff3.
Proof.
  split; intros;
    eapply glu_univ_elem_trm_resp_exp_eq;
    mauto 2.
Qed.

Lemma glu_univ_elem_core_univ' : forall j i typ_rel el_rel,
    universe_index_lt (ul j) i ->
    (typ_rel <∙> univ_glu_typ_pred j (Typeω@(large_level i))) ->
    (el_rel <∙> univ_glu_exp_pred j (Typeω@(large_level i))) ->
    DG 𝕌ω@j ∈ glu_univ_elem i ↘ typ_rel ↘ el_rel.
Proof.
  intros.
  unshelve basic_glu_univ_elem_econstructor; mautosolve.
Qed.

Hint Resolve glu_univ_elem_core_univ' : mctt.

Lemma glu_univ_elem_core_suniv' : forall l i typ_rel el_rel,
    Dom l ≈ l ∈ per_lvl ->
    universe_index_lt (us (domain_level_real l)) i ->
    (typ_rel <∙> suniv_glu_typ_pred l (Typeω@(large_level i))) ->
    (el_rel <∙> suniv_glu_exp_pred l (Typeω@(large_level i))) ->
    DG 𝕌@l ∈ glu_univ_elem i ↘ typ_rel ↘ el_rel.
Proof.
  intros.
  unshelve basic_glu_univ_elem_econstructor; mautosolve.
Qed.

Hint Resolve glu_univ_elem_core_suniv' : mctt.

(** The gluing of a universe at either tier, in one statement. *)
Lemma glu_univ_elem_univ_at : forall {u i},
    universe_index_lt u i ->
    DG universe_index_value u ∈ glu_univ_elem i ↘ univ_glu_typ_pred_at u (Typeω@(large_level i)) ↘ univ_glu_exp_pred_at u (Typeω@(large_level i)).
Proof.
  intros [n | j] * Hlt; cbn [universe_index_value univ_glu_typ_pred_at univ_glu_exp_pred_at].
  - apply glu_univ_elem_core_suniv';
      [ apply per_lvl_lit | exact Hlt | reflexivity | reflexivity ].
  - apply glu_univ_elem_core_univ'; [ exact Hlt | reflexivity | reflexivity ].
Qed.

End Fixed_GCtx.

#[export] Existing Instance glu_univ_elem_typ_morphism_iff1_Proper.
#[export] Existing Instance glu_univ_elem_trm_morphism_iff1_Proper.
#[export]
Hint Resolve glu_lvl_resp_wk : mctt.
#[export]
Hint Resolve glu_univ_elem_per_univ : mctt.
#[export] Existing Instance glu_univ_elem_trm_morphism_iff3_Proper.
#[export]
Hint Resolve glu_univ_elem_core_univ' glu_univ_elem_core_suniv' glu_univ_elem_univ_at : mctt.
Ltac glu_univ_elem_econstructor :=
  eapply glu_univ_elem_core_univ' + eapply glu_univ_elem_core_suniv' + basic_glu_univ_elem_econstructor.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma glu_univ_elem_univ_simple_constructor : forall {i : nat},
    glu_univ_elem (S i) (univ_glu_typ_pred i Typeω@(S i)) (univ_glu_exp_pred i Typeω@(S i)) 𝕌ω@i.
Proof.
  intros.
  apply glu_univ_elem_core_univ'; [ cbn; lia | reflexivity | reflexivity ].
Qed.

Hint Resolve glu_univ_elem_univ_simple_constructor : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve glu_univ_elem_univ_simple_constructor : mctt.
Ltac rewrite_predicate_equivalence_left :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        try setoid_rewrite H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac rewrite_predicate_equivalence_right :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        try setoid_rewrite <- H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite <- H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac clear_predicate_equivalence :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        (unify R1 R2; clear H) + (is_var R1; clear R1 H) + (is_var R2; clear R2 H)
    end.

Ltac apply_predicate_equivalence :=
  clear_predicate_equivalence;
  rewrite_predicate_equivalence_right;
  clear_predicate_equivalence;
  rewrite_predicate_equivalence_left;
  clear_predicate_equivalence.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** *** Simple Morphism instance for [glu_univ_elem] *)
Add Parametric Morphism i : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> iff as simple_glu_univ_elem_morphism_iff.
Proof with mautosolve.
  intros P P' ? El El'.
  split; intro Horig; [gen El' P' | gen El P];
    glu_univ_elem_induction Horig; unshelve glu_univ_elem_econstructor;
    try (etransitivity; [symmetry + idtac|]; eassumption); eauto.
Qed.

(** *** Moving [neut_glu_*_pred]s along [per_bot] *)
(** A neutral type glued at its value, along neutrals that read back alike
    up to proofs, given a type glued at the other neutral: that one's
    readback is then typed. *)
Lemma neut_glu_typ_pred_resp_per_bot : forall U b b' Γ A A',
    Dom b ≈ b' ∈ per_bot -> Γ ⊢ A ® neut_glu_typ_pred U b -> Γ ⊢ A' ® neut_glu_typ_pred U b' ->
    Γ ⊢ A ® neut_glu_typ_pred U b'.
Proof.
  intros * Hb [HA HR] [_ HR']; split; [ exact HA |].
  intros Δ φ A0 Hφ HA0; destruct (Hb (length Δ)) as [W1 W2 HW1 HW2 E].
  pose proof (functional_read_ne _ _ _ _ HA0 HW2) as ->.
  apply (glu_ne_eq_upto _ _ _ _ _ E (HR _ _ _ Hφ HW1)).
  exists U; exact (presup_exp_eq_right (HR' _ _ _ Hφ HW2)).
Qed.

(** The same for a neutral element, at a type glued at the other
    neutral. *)
Lemma neut_glu_exp_pred_resp_per_bot : forall U b b' Γ A A' M m,
    Dom b ≈ b' ∈ per_bot -> Γ ⊢ M : A ® m ∈ neut_glu_exp_pred U b -> Γ ⊢ A' ® neut_glu_typ_pred U b' ->
    Γ ⊢ M : A ® m ∈ neut_glu_exp_pred U b'.
Proof.
  intros * Hb [] HA'; econstructor; [ eapply neut_glu_typ_pred_resp_per_bot; eassumption | eassumption .. ].
Qed.

(** *** Morphism instances for [pi_glu_*_pred]s *)
Add Parametric Morphism κd κc U IR : (pi_glu_typ_pred κd κc U IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> eq ==> eq ==> iff as pi_glu_typ_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism κd κc U IR : (pi_glu_typ_pred κd κc U IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> glu_typ_pred_equivalence as pi_glu_typ_pred_morphism_glu_typ_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism κd κc U IR : (pi_glu_exp_pred κd κc U IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> relation_equivalence ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff as pi_glu_exp_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism κd κc U IR : (pi_glu_exp_pred κd κc U IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> relation_equivalence ==> eq ==> glu_exp_pred_equivalence as pi_glu_exp_pred_morphism_glu_exp_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

(** Each component's gluings of two equivalent families are contained in
    the other's. *)
Local Ltac fam_tac HNq HAq HDq :=
  first
    [ intros mf Mf jf vsf HMf Hk' Hp; destruct (HNq mf Mf jf vsf HMf Hk' Hp) as [E1 E2];
      split; intros; [ apply E1 | apply E2 ]; assumption
    | intros mf Mf jf vsf HMf Hk' Hp; destruct (HNq mf Mf jf vsf HMf Hk' Hp) as [E1 E2];
      intros; apply E2; assumption
    | intros mf Mf msf cf gsf jf vsf HMf Hm Hc Hk' Hp; destruct (HAq mf Mf msf cf gsf jf vsf HMf Hm Hc Hk' Hp) as [E1 E2];
      split; intros; [ apply E1 | apply E2 ]; assumption
    | intros mf Mf msf cf gsf gsf1 tf gsf2 wsf jf Bf ysf HMf Hm Hc Heq Hw HB Hy;
      destruct (HDq mf Mf msf cf gsf gsf1 tf gsf2 wsf jf Bf ysf HMf Hm Hc Heq Hw HB Hy) as [E1 E2];
      split; intros; [ apply E1 | apply E2 ]; assumption ].

Lemma functional_glu_univ_elem : forall i a P P' El El',
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem i ↘ P' ↘ El' ->
    (P <∙> P') /\ (El <∙> El').
Proof.
  simpl.
  intros * Ha Ha'. gen P' El'.
  glu_univ_elem_induction Ha; intros.
  (** A record type: the field gluings agree, by the induction hypothesis,
      and so do the predicates built of them. *)
  10:{ basic_invert_glu_univ_elem Ha'.
      match goal with Hl2 : record_lookup _ _ p = Some ?R2 |- _ => assert_fails constr_eq R2 R;
        rewrite H in Hl2; injection Hl2 as <- end.
      assert (EE : elem_rel <~> elem_rel0) by (eapply per_univ_elem_right_irrel; eassumption).
      assert (Heq : record_fams_equiv R ns FP FP0 FEl FEl0).
      { intros k f T vs Hk Hp; destruct (H1 _ _ _ _ Hk Hp) as [b Hb].
        eapply H3; [ exact Hk | exact Hp | exact Hb |]; eauto. }
      assert (Heq' : record_fams_equiv R ns FP0 FP FEl0 FEl)
        by (intros k f T vs Hk Hp; destruct (Heq _ _ _ _ Hk Hp) as [E1 E2]; split; symmetry; assumption).
      pose proof (record_rel_canon _ _ _ _ _ _ H H0) as HE.
      assert (HE0 : elem_rel0 <~> record_rel R (canon_fields_rel R ns)) by (rewrite <- EE; exact HE).
      apply_predicate_equivalence.
      split.
      - intros Γ A; cbn [record_glu_typ_pred pointwise_lifting].
        split; intros (Ns & HNs); exists Ns; eapply record_typ_at_mono; eassumption.
      - intros Γ A M' m; cbn [record_glu_exp_pred pointwise_lifting].
        split; intros HG; eapply record_glu_exp_mono; try eassumption; [ symmetry; exact EE ]. }
  9:{ basic_invert_glu_univ_elem Ha'.
      assert (D0 = D) by congruence; subst D0.
      assert (M0 = M) by congruence; subst M0.
      destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
      assert (EE : elem_rel0 <~> elem_rel) by (eapply per_univ_elem_right_irrel; eassumption).
      assert (HNq : forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm ->
                    tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
                    (NP m j vs <∙> NP0 m j vs) /\ (NEl m j vs <∙> NEl0 m j vs)).
      { refine (ind_case_N_helper D ups _ H0 H5 _); intros;
          eapply H8; [ eassumption | eassumption | eassumption | eassumption | eapply H24; eassumption ]. }
      assert (HAq : forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
                    tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
                    ind_con Mm c = Some gs -> j < List.length (cargs_nonrec gs) ->
                    tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
                    (AP m ms c j vs <∙> AP0 m ms c j vs) /\ (AEl m ms c j vs <∙> AEl0 m ms c j vs)).
      { refine (ind_case_A_helper D ups _ H6 _); intros;
          eapply H10; [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
                      | eapply H25; eassumption ]. }
      assert (HDq : forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
                    tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
                    ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                    tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
                    List.nth_error (ptyp_doms t) j = Some B ->
                    tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1)
                                       ms ws t) j ys ys ->
                    let Ts := List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t) in
                    (DP m (ms ++ ws ++ ys) Ts B <∙> DP0 m (ms ++ ws ++ ys) Ts B) /\
                    (DEl m (ms ++ ws ++ ys) Ts B <∙> DEl0 m (ms ++ ws ++ ys) Ts B)).
      { intros * HM Hm Hc Heq Hw HB Hy.
        destruct (H11 _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hc Heq Hw HB Hy) as [b Hb].
        eapply H13; [ exact HM | exact Hm | exact Hc | exact Heq | exact Hw | exact HB | exact Hy | exact Hb
                    | eapply H27; eassumption ]. }
      pose proof (ind_canon_of_per _ _ _ _ _ _ _ _ _ H4 H H3 H3) as Hcp.
      assert (Hns : tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams M)) ns ns)
        by (pose proof (ind_canon_clause_ns _ _ _ _ _ _ _ _ (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ H4 H H3 H3)) as Hns0;
            rewrite (member_nparams_eq _ _ _ H1) in Hns0; exact Hns0).
      apply_predicate_equivalence.
      split.
      - intros Γ A; cbn [ind_glu_typ_pred pointwise_lifting].
        split; intros (Ps & HPs); exists Ps;
          (eapply ind_typ_at_mono; [ exact H0 | exact Hcp | exact H1 | exact Hns | | | | | exact HPs ]); fam_tac HNq HAq HDq.
      - intros Γ A M' m; cbn [ind_glu_exp_pred pointwise_lifting].
        split; intros [? ? Ps HPs Hk];
          (econstructor; [ assumption | apply EE + apply EE; assumption | | ]).
        + eapply ind_typ_at_mono; [ exact H0 | exact Hcp | exact H1 | exact Hns | | | | | exact HPs ]; fam_tac HNq HAq HDq.
        + intros Δ φ Ps' Hφ HPs'; eapply (ind_glu_elem_mono p D ups _ _ _ _ H0 Hcp); [ | | | exact (Hk Δ φ Ps' Hφ HPs') ];
            intros; [ eapply HNq | eapply HAq | ]; try eassumption.
          destruct (HDq _ _ _ _ _ _ _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
                      ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as [E1 E2].
          split; intros; [ apply E1 | apply E2 ]; assumption.
        + eapply ind_typ_at_mono; [ exact H0 | exact Hcp | exact H1 | exact Hns | | | | | exact HPs ]; fam_tac HNq HAq HDq.
        + intros Δ φ Ps' Hφ HPs'; eapply (ind_glu_elem_mono p D ups _ _ _ _ H0 Hcp); [ | | | exact (Hk Δ φ Ps' Hφ HPs') ];
            intros; [ eapply HNq | eapply HAq | ]; try eassumption.
          destruct (HDq _ _ _ _ _ _ _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
                      ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as [E1 E2].
          split; intros; [ apply E1 | apply E2 ]; assumption. }
  (** A proposition: the other gluing is the proposition clause too, as no
      other clause is at a value of the propositional kind *)
  7:{ basic_invert_glu_univ_elem Ha'; try (pose proof (per_prop_left _ _ H) as Hk; cbn in Hk; congruence).
      all: apply_predicate_equivalence; try solve [ split; reflexivity ].
      all: exfalso; pose proof (per_prop_left _ _ H) as Hk;
        first [ congruence | cbn in Hk; subst; match goal with Hv : evaluated_kind _ |- _ => inversion Hv end ]. }
  (** Elsewhere the other gluing is the same clause, as the proposition
      clause is at a value of another kind *)
  all: basic_invert_glu_univ_elem Ha';
    try (exfalso; match goal with Hp : per_prop _ _ |- _ => pose proof (per_prop_left _ _ Hp) as Hk end;
         first [ congruence | cbn in Hk; subst; match goal with Hv : evaluated_kind _ |- _ => inversion Hv end ]);
    apply_predicate_equivalence; try solve [split; reflexivity].
  assert ((IP <∙> IP0) /\ (IEl <∙> IEl0)) as [] by mauto.
  apply_predicate_equivalence.
  handle_per_univ_elem_irrel.
  (on_all_hyp: fun H => directed invert_per_univ_elem H).
  handle_per_univ_elem_irrel.
  split; [intros Γ C | intros Γ M C m].
  - split; intros []; econstructor; intuition;
      [rename equiv_m into equiv0_m; assert (equiv_m : in_rel m m) by intuition
      | assert (equiv0_m : in_rel0 m m) by intuition ];
      destruct_rel_mod_eval;
      functional_eval_rewrite_clear;
      assert ((OP m equiv_m <∙> OP0 m equiv0_m) /\ (OEl m equiv_m <∙> OEl0 m equiv0_m)) as [] by mauto 3;
      intuition.
  - split; intros []; econstructor; intuition;
      [rename equiv_n into equiv0_n; assert (equiv_n : in_rel n n) by intuition
      | assert (equiv0_n : in_rel0 n n) by intuition];
      destruct_rel_mod_eval;
      [assert (exists m0n, $| m0 & n |↘ m0n /\ Δ ⊢ M0[φ]ʷ $ N : OT[(ι φ),,N] ® m0n ∈ OEl n equiv_n) by intuition
      | assert (exists m0n, $| m0 & n |↘ m0n /\ Δ ⊢ M0[φ]ʷ $ N : OT[(ι φ),,N] ® m0n ∈ OEl0 n equiv0_n) by intuition];
      destruct_conjs;
      assert ((OP n equiv_n <∙> OP0 n equiv0_n) /\ (OEl n equiv_n <∙> OEl0 n equiv0_n)) as [] by mauto 3;
      eexists; split; intuition.
Qed.

End Fixed_GCtx.

#[export] Existing Instance simple_glu_univ_elem_morphism_iff_Proper.
#[export] Existing Instance pi_glu_typ_pred_morphism_iff_Proper.
#[export] Existing Instance pi_glu_typ_pred_morphism_glu_typ_pred_equivalence_Proper.
#[export] Existing Instance pi_glu_exp_pred_morphism_iff_Proper.
#[export] Existing Instance pi_glu_exp_pred_morphism_glu_exp_pred_equivalence_Proper.
Ltac apply_functional_glu_univ_elem1 :=
  let tactic_error o1 o2 := fail 2 "functional_glu_univ_elem biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : (DG ?a ∈ glu_univ_elem ?i ↘ ?P1 ↘ ?El1),
      H2 : DG ?a ∈ glu_univ_elem ?i' ↘ ?P2 ↘ ?El2 |- _ =>
      unify i i';
      assert_fails (unify P1 P2; unify El1 El2);
      match goal with
      | H : P1 <∙> P2, H0 : El1 <∙> El2 |- _ => fail 1
      | H : P1 <∙> P2, H0 : El2 <∙> El1 |- _ => fail 1
      | H : P2 <∙> P1, H0 : El1 <∙> El2 |- _ => fail 1
      | H : P2 <∙> P1, H0 : El2 <∙> El1 |- _ => fail 1
      | _ => assert ((P1 <∙> P2) /\ (El1 <∙> El2)) as [] by (eapply functional_glu_univ_elem; [apply H1 | apply H2]) || tactic_error P1 P2
      end
  end.

Ltac apply_functional_glu_univ_elem :=
  repeat apply_functional_glu_univ_elem1.

Ltac handle_functional_glu_univ_elem :=
  functional_eval_rewrite_clear;
  fold glu_typ_pred in *;
  fold glu_exp_pred in *;
  apply_functional_glu_univ_elem;
  apply_predicate_equivalence;
  clear_dups.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** A [Π] not into propositions, glued: its clause, at the given relation
    of its domain. *)
Lemma glu_univ_elem_pi_clean_inversion1 : forall {i κd κc a ρ B in_rel P El},
  DF a ≈ a ∈ per_univ_elem i ↘ in_rel ->
  evaluated_kind κc ->
  DG d_pi κd κc a ρ B ∈ glu_univ_elem i ↘ P ↘ El ->
  exists IP IEl (OP : forall c (equiv_c_c : Dom c ≈ c ∈ in_rel), glu_typ_pred)
     (OEl : forall c (equiv_c_c : Dom c ≈ c ∈ in_rel), glu_exp_pred) elem_rel,
      DG a ∈ glu_univ_elem i ↘ IP ↘ IEl /\
        (forall c (equiv_c : Dom c ≈ c ∈ in_rel) b,
            ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a ↘ b ->
            DG b ∈ glu_univ_elem i ↘ OP _ equiv_c ↘ OEl _ equiv_c) /\
        DF d_pi κd κc a ρ B ≈ d_pi κd κc a ρ B ∈ per_univ_elem i ↘ elem_rel /\
        (P <∙> pi_glu_typ_pred κd κc (Typeω@(large_level i)) in_rel IP IEl OP) /\
        (El <∙> pi_glu_exp_pred κd κc (Typeω@(large_level i)) in_rel IP IEl elem_rel OEl).
Proof.
  intros *.
  simpl.
  intros Hinper Hev Hglu.
  (** The proposition clause is dropped: [κc] is evaluated *)
  basic_invert_glu_univ_elem Hglu.
  handle_functional_glu_univ_elem.
  handle_per_univ_elem_irrel.
  do 5 eexists.
  repeat split.
  1,3: eassumption.
  1: instantiate (1 := fun c equiv_c Γ A M m => forall (b : domain) Pb Elb,
                          ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a ↘ b ->
                          DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb ->
                          Γ ⊢ M : A ® m ∈ Elb).
  1: instantiate (1 := fun c equiv_c Γ A => forall (b : domain) Pb Elb,
                          ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a ↘ b ->
                          DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb ->
                          Γ ⊢ A ® Pb).
  2-5: intros []; econstructor; mauto.
  all: intros.
  - assert (Dom c ≈ c ∈ in_rel0) as equiv0_c by intuition.
    assert (DG b ∈ glu_univ_elem i ↘ OP c equiv0_c ↘ OEl c equiv0_c) by mauto 3.
    apply -> simple_glu_univ_elem_morphism_iff; [| reflexivity | |]; [eauto | |].
    + intros ? ? ? ?.
      split; intros; handle_functional_glu_univ_elem; intuition.
    + intros ? ?.
      split; [intros; handle_functional_glu_univ_elem |]; intuition.
  - assert (Dom m ≈ m ∈ in_rel0) as equiv0_m by intuition.
    assert (DG b ∈ glu_univ_elem i ↘ OP m equiv0_m ↘ OEl m equiv0_m) by mauto 3.
    handle_functional_glu_univ_elem.
    intuition.
  - match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_rel_mod_eval.
    intuition.
  - assert (Dom n ≈ n ∈ in_rel0) as equiv0_n by intuition.
    assert (exists mn : domain, $| m & n |↘ mn /\ Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® mn ∈ OEl n equiv0_n) by mauto 3.
    destruct_conjs.
    eexists.
    intuition.
    assert (DG b ∈ glu_univ_elem i ↘ OP n equiv0_n ↘ OEl n equiv0_n) by mauto 3.
    handle_functional_glu_univ_elem.
    intuition.
  - assert (exists mn : domain,
               $| m & n |↘ mn /\
                 (forall (b : domain) (Pb : glu_typ_pred) (Elb : glu_exp_pred),
                     ⟦ B ⟧ ρ ↦ n ⦂ entry_type_value a ↘ b ->
                     DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb ->
                     Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® mn ∈ Elb)) by intuition.
    destruct_conjs.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    functional_eval_rewrite_clear.
    eexists.
    intuition.
Qed.

(** The same at a given gluing of the domain. *)
Lemma glu_univ_elem_pi_clean_inversion2 : forall {i κd κc a ρ B in_rel IP IEl P El},
  DF a ≈ a ∈ per_univ_elem i ↘ in_rel ->
  DG a ∈ glu_univ_elem i ↘ IP ↘ IEl ->
  evaluated_kind κc ->
  DG d_pi κd κc a ρ B ∈ glu_univ_elem i ↘ P ↘ El ->
  exists (OP : forall c (equiv_c_c : Dom c ≈ c ∈ in_rel), glu_typ_pred)
     (OEl : forall c (equiv_c_c : Dom c ≈ c ∈ in_rel), glu_exp_pred) elem_rel,
    (forall c (equiv_c : Dom c ≈ c ∈ in_rel) b,
        ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a ↘ b ->
        DG b ∈ glu_univ_elem i ↘ OP _ equiv_c ↘ OEl _ equiv_c) /\
      DF d_pi κd κc a ρ B ≈ d_pi κd κc a ρ B ∈ per_univ_elem i ↘ elem_rel /\
      (P <∙> pi_glu_typ_pred κd κc (Typeω@(large_level i)) in_rel IP IEl OP) /\
      (El <∙> pi_glu_exp_pred κd κc (Typeω@(large_level i)) in_rel IP IEl elem_rel OEl).
Proof.
  intros *.
  simpl.
  intros Hinper Hinglu Hev Hglu.
  unshelve eapply (glu_univ_elem_pi_clean_inversion1 _ Hev) in Hglu; shelve_unifiable; [eassumption |];
    destruct Hglu as [? [? [? [? [? [? [? [? []]]]]]]]].
  handle_functional_glu_univ_elem.
  do 3 eexists.
  repeat split; try eassumption;
    intros []; econstructor; mauto.
Qed.

End Fixed_GCtx.

Ltac invert_glu_univ_elem H :=
  (unshelve eapply (glu_univ_elem_pi_clean_inversion2 _ _ _) in H; shelve_unifiable; [eassumption | eassumption | eassumption |];
   destruct H as [? [? [? [? [? []]]]]])
  + (unshelve eapply (glu_univ_elem_pi_clean_inversion1 _ _) in H; shelve_unifiable; [eassumption | eassumption |];
   destruct H as [? [? [? [? [? [? [? [? []]]]]]]]])
  + basic_invert_glu_univ_elem H.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma per_lvl_read_left : forall d d' s L, Dom d ≈ d' ∈ per_lvl -> Rnf ⇓ Levelᵈ d' in s ↘ L -> Rnf ⇓ Levelᵈ d in s ↘ L.
Proof.
  intros * Hd Hr; destruct (Hd s) as [L0 HL HL' _].
  pose proof (functional_read_nf _ _ _ _ HL' Hr) as <-; exact HL.
Qed.

Lemma glu_lvl_resp_per : forall Γ M m n, glu_lvl n Γ M m -> forall m', Dom m ≈ m' ∈ per_lvl -> glu_lvl n Γ M m'.
Proof.
  intros * H * Hm Δ φ L Hφ Hr.
  apply H; [ eassumption | eapply per_lvl_read_left; eassumption ].
Qed.

(** Related levels give equivalent small-universe predicates: a level term
    glued to one is glued to the other, and the two have the same realiser,
    which indexes the elements. *)
Lemma suniv_glu_typ_pred_resp_per : forall l l' U,
    Dom l ≈ l' ∈ per_lvl ->
    suniv_glu_typ_pred l U <∙> suniv_glu_typ_pred l' U.
Proof.
  intros * Hl Γ A; cbn; split; intros [t n Ht Heq]; apply (mk_suniv_glu_typ _ _ _ _ t n); try assumption;
    (eapply glu_lvl_resp_per; [ eassumption | first [ eassumption | symmetry; assumption ] ]).
Qed.

Lemma suniv_glu_exp_pred_resp_per : forall l l' U,
    Dom l ≈ l' ∈ per_lvl ->
    suniv_glu_exp_pred l U <∙> suniv_glu_exp_pred l' U.
Proof.
  intros * Hl Γ A M m; unfold suniv_glu_exp_pred; cbn.
  rewrite (per_lvl_real _ _ Hl).
  pose proof (suniv_glu_typ_pred_resp_per l l' U Hl Γ A) as Ht; cbn in Ht.
  split; intros [? HA ? ?]; constructor; try assumption; apply Ht; assumption.
Qed.

(** The parameters of every member of a group at two related types of one
    of its members, the non-uniform ones related at the canonical relation
    of the left: they read back alike at the member's telescope. *)
Lemma ind_params_per_top : forall i R p D k ups ups' ns ns',
    DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups' ++ ns') ∈ per_univ_elem i ↘ R ->
    ind_lookup gc_deps gc_stack p = Some D -> List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
    forall j Mj bs bs', ind_member D j = Some Mj -> tele_rel (canon_nparams_rel D ups j) (List.rev (im_nparams Mj)) bs bs' ->
      per_top_ps (List.rev (im_params D Mj)) (ups ++ bs) (ups' ++ bs').
Proof.
  intros * HR Hl Hu Hu' j Mj bs bs' HMj Hbs s.
  destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ HR Hl Hu Hu') as [Hass Hps _ _ _ _ _ _].
  destruct (per_univ_elem_ind_evals _ _ _ _ _ _ _ _ _ HR Hl Hu Hu') as (HevN & _ & _).
  destruct (Hps s) as [Ms1 Ms1' HM1 HM1' HE1].
  assert (Hassn : all_assumptions (List.rev (im_nparams Mj)))
    by (apply List.Forall_rev; exact (group_structure_nparams _ Hass _ _ HMj)).
  destruct (read_ps_tele (List.rev (im_nparams Mj)) (canon_nparams_rel D ups j) (decl_env D ups) (decl_env D ups') Hassn
              ltac:(intros j0 κ A pre pre' Hj0 Hp;
                    destruct (HevN _ _ _ _ _ _ _ HMj Hj0 Hp) as [a a' Ea Ea' HRa];
                    exists a, a'; split; [ exact Ea | split; [ exact Ea' | intros b b' Hb; exact (per_elem_then_per_top HRa Hb) ] ])
              _ _ Hbs s) as (Ms2 & Ms2' & HM2 & HM2' & HE2).
  rewrite rev_im_params_split.
  apply (mk_params_read_alike _ _ _ _ (Ms1 ++ Ms2) (Ms1' ++ Ms2'));
    [ apply read_ps_app; assumption | apply read_ps_app; assumption | apply nfs_eq_upto_proofs_app; assumption ].
Qed.

(** A proposition is glued by the proposition clause only. *)
Lemma glu_univ_elem_prop_inv : forall i a P El,
    Dom a ≈ a ∈ per_prop -> DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    (P <∙> prop_glu_typ_pred a) /\ (El <∙> proof_glu_exp_pred a).
Proof.
  intros * Hp Hg; eapply functional_glu_univ_elem; [ exact Hg |].
  simp glu_univ_elem; eapply glu_univ_elem_core_prop; [ exact Hp | reflexivity | reflexivity ].
Qed.

End Fixed_GCtx.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma per_univ_glu_univ_elem : forall i a,
    Dom a ≈ a ∈ per_univ i ->
    exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El.
Proof.
  simpl.
  (** [per_univ_elem_induction] wants distinct indices; [induction] abstracted
      the right one. *)
  intros i a [R Hper].
  enough (forall a0, DF a0 ≈ a ∈ per_univ_elem i ↘ R -> exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El) by eauto.
  clear Hper; intros a0 Hper.
  per_univ_elem_induction Hper; intros.
  10:{ (** A record type: its fields glue at their canonical gluings, at the
          right parameters. *)
      match goal with
      | Hl : record_lookup _ _ ?p = Some ?R, Hnd : List.NoDup _, Hn : List.length ?ns = _, Hn' : List.length ?ns' = _,
        Hps : per_top_ps _ ?ns ?ns', HfP : fields_per ?R ?fr, HfI : fields_inv ?R ?fr,
        HfE : fields_evals _ ?R ?ns ?ns' ?fr, HE : ?er <~> record_rel ?R ?fr |- _ =>
          assert (Hpu : per_univ_elem i er (d_record p ns) (d_record p ns'));
          [ basic_per_univ_elem_econstructor; try eassumption;
            red; intros * Hk Hp; destruct (HfE _ _ _ _ _ Hk Hp) as [a a' Ea Ea' [HR _]]; econstructor; eauto |];
          rename Hl into Hlc, HfE into HfEc;
          pose proof (record_canon_prefix_clause _ _ R ns ns' fr (fun _ _ _ H => proj1 H) HfP HfI HfEc) as Hcl
      end.
      assert (HR' : per_univ_elem i elem_rel (d_record p ns') (d_record p ns'))
        by (eapply per_univ_trans; [ apply per_univ_sym; exact Hpu | exact Hpu ]).
      assert (Hcan : forall b P El (E : domain -> Prop), (forall b', E b' -> b' = b) -> E b -> glu_univ_elem i P El b ->
                 glu_univ_elem i (fun Γ T => forall b' P' El', E b' -> glu_univ_elem i P' El' b' -> P' Γ T)
                                 (fun Γ T M m => forall b' P' El', E b' -> glu_univ_elem i P' El' b' -> El' Γ T M m) b).
      { intros * HE Eb Hg.
        eapply simple_glu_univ_elem_morphism_iff; [ | | reflexivity | exact Hg ].
        - intros Γ T; split; [ intros HP; exact (HP _ _ _ Eb Hg) |].
          intros HP b' P' El' Eb' Hg'; pose proof (HE _ Eb') as ->.
          destruct (functional_glu_univ_elem _ _ _ _ _ _ Hg Hg') as [HPP _]; apply HPP; exact HP.
        - intros Γ T M' m; split; [ intros HP; exact (HP _ _ _ Eb Hg) |].
          intros HP b' P' El' Eb' Hg'; pose proof (HE _ Eb') as ->.
          destruct (functional_glu_univ_elem _ _ _ _ _ _ Hg Hg') as [_ HEE]; apply HEE; exact HP. }
      set (FP := fun k vs Γ T => forall b P El, ⟦ nth_ftyp R k ⟧ record_fields_env R ns' vs ↘ b ->
                                   glu_univ_elem i P El b -> P Γ T).
      set (FEl := fun k vs Γ T M m0 => forall b P El, ⟦ nth_ftyp R k ⟧ record_fields_env R ns' vs ↘ b ->
                                         glu_univ_elem i P El b -> El Γ T M m0).
      do 2 eexists.
      simp glu_univ_elem.
      refine (glu_univ_elem_core_record i _ FP FEl _ _ elem_rel Hlc HR' _ _ _ _);
        try rewrite <- glu_univ_elem_equation_1 in *; try reflexivity.
      - intros k f T vs Hk Hp.
        assert (Hkl : k < length (record_fields R)) by (apply List.nth_error_Some; congruence).
        destruct (HfEc _ _ _ _ _ Hk (proj1 (Hcl k vs ltac:(lia) Hp))) as [a a' Ea Ea' _]; eauto.
      - intros k f T vs b Hk Hp Eb.
        assert (Hkl : k < length (record_fields R)) by (apply List.nth_error_Some; congruence).
        destruct (HfEc _ _ _ _ _ Hk (proj1 (Hcl k vs ltac:(lia) Hp))) as [a a' Ea Ea' [_ (Pb & Elb & Hgb)]].
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        unfold FP, FEl; rewrite (nth_ftyp_eq _ _ _ _ Hk).
        eapply Hcan; [ intros; eapply functional_eval_exp; eassumption | exact Eb | exact Hgb ]. }
  9:{ (** An inductive type: its telescopes glue at their canonical
          gluings, at the right uniform parameters. *)
      rename H into Hl, H0 into Hass, H1 into HMk, H2 into Hh, H3 into Hu, H4 into Hu',
        H7 into Hn, H10 into Ha, H13 into Hd.
      assert (Hpu : per_univ_elem i elem_rel (d_ind p k (ups ++ ns)) (d_ind p k (ups' ++ ns'))).
      { basic_per_univ_elem_econstructor; try eassumption.
        - red; intros * HM0 HA Hp; destruct (Hn _ _ _ _ _ _ _ HM0 HA Hp) as [a a' Ea Ea' [HR _]]; econstructor; eauto.
        - red; intros * HM0 Hm Hc HA Hp; destruct (Ha _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc HA Hp) as [a a' Ea Ea' [HR _]];
            econstructor; eauto.
        - red; intros * HM0 Hm Hc Heq Hw HB Hy;
            destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc Heq Hw HB Hy) as [a a' Ea Ea' [HR _]];
            econstructor; eauto. }
      assert (Hcan : forall b P El (E : domain -> Prop), (forall b', E b' -> b' = b) -> E b -> glu_univ_elem i P El b ->
                 glu_univ_elem i (fun Γ T => forall b' P' El', E b' -> glu_univ_elem i P' El' b' -> P' Γ T)
                                 (fun Γ T M m => forall b' P' El', E b' -> glu_univ_elem i P' El' b' -> El' Γ T M m) b).
      { intros * HE Eb Hg.
        eapply simple_glu_univ_elem_morphism_iff; [ | | reflexivity | exact Hg ].
        - intros Γ T; split; [ intros HP; exact (HP _ _ _ Eb Hg) |].
          intros HP b' P' El' Eb' Hg'; pose proof (HE _ Eb') as ->.
          destruct (functional_glu_univ_elem _ _ _ _ _ _ Hg Hg') as [HPP _]; apply HPP; exact HP.
        - intros Γ T M' m; split; [ intros HP; exact (HP _ _ _ Eb Hg) |].
          intros HP b' P' El' Eb' Hg'; pose proof (HE _ Eb') as ->.
          destruct (functional_glu_univ_elem _ _ _ _ _ _ Hg Hg') as [_ HEE]; apply HEE; exact HP. }
      assert (Hag : ind_fam_agree D nr (canon_nparams_rel D ups) ar (canon_args_rel D ups) dr (canon_doms_rel D ups)).
      { eapply (ind_fam_agree_of_evals i D ups ups'); [ exact Hass | | | ].
        - red; intros * HM0 HA Hp; destruct (Hn _ _ _ _ _ _ _ HM0 HA Hp) as [a a' Ea Ea' [HR _]]; econstructor; eauto.
        - red; intros * HM0 Hm Hc HA Hp; destruct (Ha _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc HA Hp) as [a a' Ea Ea' [HR _]];
            econstructor; eauto.
        - red; intros * HM0 Hm Hc Heq Hw HB Hy;
            destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hm Hc Heq Hw HB Hy) as [a a' Ea Ea' [HR _]];
            econstructor; eauto. }
      destruct Hag as [Hn0 Ha0 Hd0].
      pose proof (tele_prefix_rel_nr_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0) as P2.
      destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ Hpu Hl Hu Hu') as [_ _ Hcp Hfam Hadm _ _ _].
      destruct (ind_fam_agree_sym _ _ _ _ _ _ _ Hfam) as [Hfn' Hfa' Hfd'].
      pose proof Hfam as [Hfn Hfa Hfd].
      pose proof (tele_rel_nr_change p D ups _ _ _ _ _ _ Hfn' Hfa' Hfd') as G1.
      pose proof (tele_prefix_rel_nr_change' p D ups _ _ _ _ _ _ Hfn Hfa Hfd) as Q2.
      assert (HR' : per_univ_elem i elem_rel (d_ind p k (ups' ++ ns')) (d_ind p k (ups' ++ ns')))
        by (eapply per_univ_trans; [ apply per_univ_sym; exact Hpu | exact Hpu ]).
      destruct (ind_fam_agree_sym _ _ _ _ _ _ _ (mk_ind_fam_agree _ _ _ _ _ _ _ Hn0 Ha0 Hd0)) as [Hn0' Ha0' Hd0'].
      pose proof (tele_rel_nr_change p D ups _ _ _ _ _ _ Hn0' Ha0' Hd0') as F2.
      assert (Hpre : forall m Mm j vs, ind_member D m = Some Mm -> j < length (List.rev (im_nparams Mm)) ->
                     tele_prefix_rel (canon_nparams_rel D ups' m) j vs vs -> tele_prefix_rel (nr m) j vs vs).
      { intros * HM Hj Hp. exact (P2 m Mm HM j vs vs ltac:(lia) (Q2 m Mm HM j vs vs ltac:(lia) Hp)). }
      assert (Hpra : forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
                     tele_rel (canon_nparams_rel D ups' m) (List.rev (im_nparams Mm)) ms ms ->
                     ind_con Mm c = Some gs -> j <= length (cargs_nonrec gs) ->
                     tele_prefix_rel (canon_args_rel D ups' m ms c) j vs vs ->
                     tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms /\ tele_prefix_rel (ar m ms c) j vs vs).
      { intros * HM Hm Hc Hj Hp.
        pose proof (G1 m Mm HM _ _ Hm) as Hm1. pose proof (F2 m Mm HM _ _ Hm1) as Hm2.
        pose proof (tele_prefix_rel_ar_change' p D ups _ _ _ _ _ _ Hfn Hfa Hfd m Mm HM ms ms ms c gs j vs vs Hm1 Hm Hc Hj Hp) as Hp1.
        exact (conj Hm2 (tele_prefix_rel_ar_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM ms ms ms c gs j vs vs Hm2 Hm1 Hc Hj Hp1)). }
      assert (Hprd : forall m Mm ms c gs gs1 t gs2 ws j ys, ind_member D m = Some Mm ->
                     tele_rel (canon_nparams_rel D ups' m) (List.rev (im_nparams Mm)) ms ms ->
                     ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                     tele_prefix_rel (canon_args_rel D ups' m ms c) (length (cargs_nonrec gs1)) ws ws ->
                     j <= length (ptyp_doms t) ->
                     tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups' m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1)
                                        ms ws t) j ys ys ->
                     tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms /\
                     tele_prefix_rel (ar m ms c) (length (cargs_nonrec gs1)) ws ws /\
                     tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys).
      { intros * HM Hm Hc Heq Hw Hj Hy.
        assert (HK : length (cargs_nonrec gs1) <= length (cargs_nonrec gs))
          by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
        pose proof (G1 m Mm HM _ _ Hm) as Hm1. pose proof (F2 m Mm HM _ _ Hm1) as Hm2.
        pose proof (tele_prefix_rel_ar_change' p D ups _ _ _ _ _ _ Hfn Hfa Hfd m Mm HM ms ms ms c gs _ ws ws Hm1 Hm Hc HK Hw) as Hw1.
        pose proof (tele_prefix_rel_ar_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM ms ms ms c gs _ ws ws Hm2 Hm1 Hc HK Hw1)
          as Hw2.
        pose proof (tele_prefix_rel_sh_change' p D ups _ _ _ _ _ _ Hfn Hfa Hfd m Mm HM ms ms ms c gs gs1 t gs2 ws ws ws j ys ys
                      Hm1 Hm Hc Heq Hw1 Hw Hj Hy) as Hy1.
        pose proof (tele_prefix_rel_sh_change' p D ups _ _ _ _ _ _ Hn0 Ha0 Hd0 m Mm HM ms ms ms c gs gs1 t gs2 ws ws ws j ys ys
                      Hm2 Hm1 Hc Heq Hw2 Hw1 Hj Hy1) as Hy2.
        exact (conj Hm2 (conj Hw2 Hy2)). }
      (** The gluings of the components, at the right uniform parameters: of
          the value of the component's type, read off the member and the
          constructor ([nth_ctyp], [nth_atyp]) or given ([DP]) *)
      set (NP := fun m j vs Γ T => forall b P El,
                   (exists Mm, ind_member D m = Some Mm /\
                      ⟦ nth_ctyp (List.rev (member_nparams D m)) j ⟧ components_env D ups' (List.rev (im_nparams Mm)) vs ↘ b) ->
                   glu_univ_elem i P El b -> P Γ T).
      set (NEl := fun m j vs Γ T M m0 => forall b P El,
                    (exists Mm, ind_member D m = Some Mm /\
                       ⟦ nth_ctyp (List.rev (member_nparams D m)) j ⟧ components_env D ups' (List.rev (im_nparams Mm)) vs ↘ b) ->
                    glu_univ_elem i P El b -> El Γ T M m0).
      set (AP := fun m ms c j vs Γ T => forall b P El,
                   (exists Mm gs, ind_member D m = Some Mm /\ ind_con Mm c = Some gs /\
                      ⟦ nth_atyp D m c j ⟧ components_env D ups' (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs) ↘ b) ->
                   glu_univ_elem i P El b -> P Γ T).
      set (AEl := fun m ms c j vs Γ T M m0 => forall b P El,
                    (exists Mm gs, ind_member D m = Some Mm /\ ind_con Mm c = Some gs /\
                       ⟦ nth_atyp D m c j ⟧ components_env D ups' (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs) ↘ b) ->
                    glu_univ_elem i P El b -> El Γ T M m0).
      set (DP := fun (m : nat) pre Ts B Γ T => forall b P El, ⟦ B ⟧ components_env D ups' Ts pre ↘ b ->
                                                 glu_univ_elem i P El b -> P Γ T).
      set (DEl := fun (m : nat) pre Ts B Γ T M m0 => forall b P El, ⟦ B ⟧ components_env D ups' Ts pre ↘ b ->
                                                       glu_univ_elem i P El b -> El Γ T M m0).
      do 2 eexists.
      simp glu_univ_elem.
      refine (glu_univ_elem_core_indty i _ NP NEl AP AEl DP DEl _ _ elem_rel Hl Hass HMk Hh Hu' HR' _ _ _ _ _ _ _ _);
        try rewrite <- glu_univ_elem_equation_1 in *; try reflexivity.
      - intros m Mm j κ A vs HM HA Hp.
        assert (Hj : j < length (List.rev (im_nparams Mm))) by (apply List.nth_error_Some; congruence).
        destruct (Hn _ _ _ _ _ _ _ HM HA (Hpre _ _ _ _ HM Hj Hp)) as [a a' Ea Ea' _]; eauto.
      - intros m Mm ms c gs j A vs HM Hm Hc HA Hp.
        assert (Hj : j < length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        destruct (Hpra _ _ ms c gs j vs HM Hm Hc ltac:(lia) Hp) as (Hm2 & Hp2).
        destruct (Ha _ _ _ _ _ _ _ _ _ _ HM Hm2 Hc HA Hp2) as [a a' Ea Ea' _]; eauto.
      - intros m Mm j κ A vs b HM HA Hp Eb.
        assert (Hj : j < length (List.rev (im_nparams Mm))) by (apply List.nth_error_Some; congruence).
        destruct (Hn _ _ _ _ _ _ _ HM HA (Hpre _ _ _ _ HM Hj Hp)) as [a a' Ea Ea' [_ (Pb & Elb & Hgb)]].
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        unfold NP, NEl.
        eapply (Hcan b Pb Elb (fun b' => exists Mm', ind_member D m = Some Mm' /\
                   ⟦ nth_ctyp (List.rev (member_nparams D m)) j ⟧ components_env D ups' (List.rev (im_nparams Mm')) vs ↘ b'));
          [ intros b' (Mm' & HM' & Eb'); rewrite HM in HM'; injection HM' as <-;
            rewrite (nth_ctyp_eq _ _ _ _ _ _ HM HA) in Eb'; eapply functional_eval_exp; eassumption
          | exists Mm; split; [ exact HM | rewrite (nth_ctyp_eq _ _ _ _ _ _ HM HA); exact Eb ] | exact Hgb ].
      - intros m Mm ms c gs j A vs b HM Hm Hc HA Hp Eb.
        assert (Hj : j < length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        destruct (Hpra _ _ ms c gs j vs HM Hm Hc ltac:(lia) Hp) as (Hm2 & Hp2).
        destruct (Ha _ _ _ _ _ _ _ _ _ _ HM Hm2 Hc HA Hp2) as [a a' Ea Ea' [_ (Pb & Elb & Hgb)]].
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        unfold AP, AEl.
        eapply (Hcan b Pb Elb (fun b' => exists Mm' gs', ind_member D m = Some Mm' /\ ind_con Mm' c = Some gs' /\
                   ⟦ nth_atyp D m c j ⟧ components_env D ups' (List.rev (im_nparams Mm') ++ cargs_nonrec_tele gs') (ms ++ vs) ↘ b'));
          [ intros b' (Mm' & gs' & HM' & Hc' & Eb'); rewrite HM in HM'; injection HM' as <-; rewrite Hc in Hc'; injection Hc' as <-;
            rewrite (nth_atyp_eq _ _ _ _ _ _ _ HM Hc HA) in Eb'; eapply functional_eval_exp; eassumption
          | exists Mm, gs; split; [ exact HM | split; [ exact Hc | rewrite (nth_atyp_eq _ _ _ _ _ _ _ HM Hc HA); exact Eb ] ]
          | exact Hgb ].
      - intros m Mm ms c gs gs1 t gs2 ws j B ys HM Hm Hc Heq Hw HB Hy.
        assert (Hjl : j < length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
        destruct (Hprd _ _ ms c gs gs1 t gs2 ws j ys HM Hm Hc Heq Hw ltac:(lia) Hy) as (Hm2 & Hw2 & Hy2).
        destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm2 Hc Heq Hw2 HB Hy2) as [a a' Ea Ea' _]; eauto.
      - intros m Mm ms c gs gs1 t gs2 ws j B ys b HM Hm Hc Heq Hw HB Hy Eb.
        assert (Hjl : j < length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
        destruct (Hprd _ _ ms c gs gs1 t gs2 ws j ys HM Hm Hc Heq Hw ltac:(lia) Hy) as (Hm2 & Hw2 & Hy2).
        destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hm2 Hc Heq Hw2 HB Hy2) as [a a' Ea Ea' [_ (Pb & Elb & Hgb)]].
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        (** The domain is evaluated in the environment of the components
            before it: of the domains before it, and as many *)
        assert (Hlens : List.length ms = List.length (im_nparams Mm) /\ List.length ws = List.length (cargs_nonrec gs1) /\
                        List.length ys = j).
        { rewrite tele_rel_iff in Hm; destruct Hm as (Hlm & _ & _); rewrite List.length_rev in Hlm.
          split; [ exact Hlm | split; [ exact (proj1 Hw) | exact (proj1 Hy) ] ]. }
        destruct Hlens as (Hlm & Hlw & Hly).
        rewrite (components_env_shape_prefix D ups' Mm gs1 t ms ws ys Hlm Hlw ltac:(lia)), Hly in Eb.
        unfold DP, DEl.
        eapply Hcan; [ intros; eapply functional_eval_exp; eassumption | exact Eb | exact Hgb ]. }
  all:
    try solve [do 2 eexists; unshelve (glu_univ_elem_econstructor; try reflexivity; subst; trivial)].
  (** A small universe at the right-hand level, which has the realiser of the
      left-hand one. *)
  all: try match goal with
         | H : per_lvl ?l ?l' |- exists _ _, glu_univ_elem _ _ _ 𝕌@?l' =>
             do 2 eexists; apply glu_univ_elem_core_suniv';
               [ etransitivity; [ symmetry |]; exact H
               | rewrite <- (per_lvl_real _ _ H); assumption
               | reflexivity | reflexivity ]
         end.

  (** A proposition: the proposition clause *)
  - do 2 eexists; simp glu_univ_elem; eapply glu_univ_elem_core_prop;
      [ exact (per_prop_trans _ _ _ (per_prop_sym _ _ H) H) | reflexivity | reflexivity ].
  - destruct_conjs.
    do 2 eexists.
    glu_univ_elem_econstructor; try (eassumption + reflexivity).
    + saturate_refl; eassumption.
    + instantiate (1 := fun (c : domain) (equiv_c : in_rel c c) Γ A M m =>
                          forall b P El,
                            ⟦ B' ⟧ ρ' ↦ c ⦂ entry_type_value a' ↘ b ->
                            glu_univ_elem i P El b ->
                            Γ ⊢ M : A ® m ∈ El).
      instantiate (1 := fun (c : domain) (equiv_c : in_rel c c) Γ A =>
                          forall b P El,
                            ⟦ B' ⟧ ρ' ↦ c ⦂ entry_type_value a' ↘ b ->
                            glu_univ_elem i P El b ->
                            Γ ⊢ A ® P).
      intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      handle_per_univ_elem_irrel.
      rewrite simple_glu_univ_elem_morphism_iff; try (eassumption + reflexivity);
        split; intros; handle_functional_glu_univ_elem; intuition.
    + enough (DF d_pi κd κc a ρ B ≈ d_pi κd κc a' ρ' B' ∈ per_univ_elem i ↘ elem_rel) by (etransitivity; [symmetry |]; eassumption).
      per_univ_elem_econstructor; mauto.
      intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      econstructor; mauto.
  - do 2 eexists.
    glu_univ_elem_econstructor; try reflexivity; mauto.
Qed.

Hint Resolve per_univ_glu_univ_elem : mctt.

Corollary per_univ_elem_glu_univ_elem : forall i a R,
    DF a ≈ a ∈ per_univ_elem i ↘ R ->
    exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El.
Proof.
  intros.
  apply per_univ_glu_univ_elem; mauto.
Qed.

Hint Resolve per_univ_elem_glu_univ_elem : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve per_univ_glu_univ_elem per_univ_elem_glu_univ_elem : mctt.

Ltac saturate_glu_info1 :=
  match goal with
  | H : glu_univ_elem _ ?P _ ?a, Hn : not_level_sort ?a,
      H1 : ?P _ _ |- _ =>
      pose proof (glu_univ_elem_univ_lvl_gen _ _ _ _ H Hn _ _ H1);
      fail_if_dup
  | H : glu_univ_elem _ _ ?El _,
      H1 : ?El _ _ _ _ |- _ =>
      pose proof (glu_univ_elem_trm_escape _ _ _ _ H _ _ _ _ H1);
      fail_if_dup
  end.

Ltac saturate_glu_info :=
  clear_dups;
  repeat saturate_glu_info1.

(** The type-level gluing of a small universe along a weakening [φ]: its level
    term is weakened with the type. *)
Ltac suniv_glu_typ_pred_wk :=
  match goal with
  | H : suniv_glu_typ_pred ?l _ ?Γ _,
      Hφ : ?Δ ⊢ᵏ ?φ : ?Γ
    |- suniv_glu_typ_pred ?l _ ?Δ _ =>
      let t := fresh "t" in
      let Heq := fresh "Heq" in
      destruct H as [t ? ? Heq]; eapply (mk_suniv_glu_typ _ _ _ _ t[φ]ʷ _);
      [ eapply glu_lvl_resp_wk; eassumption
      | match type of Heq with
        | wf_exp_eq ?T ?X _ ?U ?A _ =>
            assert (T ⍮ X ⍮ Δ ⊢ A[φ]ʷ ≈ (Type⟨t⟩)[φ]ʷ : U) by mauto 2; eassumption
        end ]
  end.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** Gluing predicates are monotone along Kripke weakenings. Two weakenings
    collapse to a single [[φ ⊙ ψ]ʷ] by [exp_wk_wk], and the [q] of a [Π]
    codomain absorbs the extension of the second weakening by
    [exp_sub_wk_q_extend_wk]. Both are propositional equalities, so each case
    is a [rewrite] away from its hypothesis. *)

Lemma glu_univ_elem_typ_monotone : forall i a P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Δ φ Γ A,
      Γ ⊢ A ® P ->
      Δ ⊢ᵏ φ : Γ ->
      Δ ⊢ A[φ]ʷ ® P.
Proof.
  simpl. glu_univ_elem_induction1; intros.
  10:{ apply_equiv_left; eapply record_glu_typ_pred_wk; eassumption. }
  9:{ apply_equiv_left; eapply (ind_glu_typ_pred_wk p D ups ns NP NEl AP AEl DP DEl); eassumption. }
  all: saturate_kripke;
    handle_functional_glu_univ_elem;
    simpl in *;
    try solve [mauto 2].
  (** A small universe: the level term weakens with the type. *)
  all: try solve [ suniv_glu_typ_pred_wk ].
  (** [Prop] and a type of levels: the equation weakens *)
  all: try solve [ eapply kripke_preserves_typ_eq_prop; eassumption ].
  all: try solve [ eapply kripke_preserves_level_sort_eq_level; eassumption ].
  (** [LevelSort]: unchanged *)
  - match goal with H : _ = LevelSort /\ _ |- _ => destruct H as [-> _] end; split; [ reflexivity | assumption ].
  - simpl_glu_rel.
    assert (Δ ⊢ A[φ]ʷ ≈ (a_pi κd κc IT OT)[φ]ʷ : abs_kind_sort κc Typeω@(large_level i)) as HAeq
      by (eapply kripke_preserves_kind_sort_eq; eassumption).
    rewrite exp_wk_pi in HAeq.
    econstructor; [ eassumption | eapply kripke_preserves_kind_sort; eassumption
                  | eapply kripke_preserves_kind_sort_q; eassumption | | ]; intros.
    + rewrite exp_wk_wk; mauto 4.
    + rewrite exp_wk_wk in *.
      rewrite exp_sub_wk_q_extend_wk.
      mauto 4.
  (** A proposition and a neutral type *)
  - destruct_conjs; split; [ mauto 2 | intros; rewrite exp_wk_wk; mauto 4 ].
  - destruct_conjs; split; [ mauto 2 | intros; rewrite exp_wk_wk; mauto 4 ].
Qed.

Lemma glu_univ_elem_exp_monotone : forall i a P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Δ φ Γ M A m,
      Γ ⊢ M : A ® m ∈ El ->
      Δ ⊢ᵏ φ : Γ ->
      Δ ⊢ M[φ]ʷ : A[φ]ʷ ® m ∈ El.
Proof.
  simpl. glu_univ_elem_induction1; intros.
  10:{ apply_equiv_left; eapply record_glu_exp_pred_wk; eassumption. }
  9:{ apply_equiv_left; eapply (ind_glu_exp_pred_wk p D ups ns NP NEl AP AEl DP DEl); eassumption. }
  all: saturate_kripke;
    handle_functional_glu_univ_elem;
    simpl in *;
    destruct_all; destruct_glu_records.
  all: try solve [ repeat eexists; mauto 2; eapply glu_univ_elem_typ_monotone; eauto ].
  all: try solve [ econstructor; [ mauto 2 | mauto 2 | glu_witness2; [ eassumption | eapply glu_univ_elem_typ_monotone; eauto ] ] ].
  (** An element of a small universe: its type's level term weakens with it,
      and its readback clause composes the two weakenings. *)
  all: try solve [ econstructor;
                   [ mauto 2
                   | glu_witness2; [ eapply glu_lvl_resp_wk; eassumption | mauto 2 ]
                   | glu_witness2;
                     [ eassumption | eapply glu_univ_elem_typ_monotone; eassumption ]
                   | intros; rewrite !exp_wk_wk; mauto 3 ] ].
  (** A level: its readback clause weakens. *)
  all: try solve [ econstructor; [ mauto 2 | assumption | eapply glu_lvl_resp_wk; eassumption ] ].
  all: try solve [ repeat split; mauto 2 ].
  (** A proposition, as an element of [Prop] *)
  - econstructor; [ eapply kripke_preserves_typ_eq_prop; eassumption | mauto 2 | assumption
                  | eapply prop_glu_typ_pred_wk; eassumption ].
  (** A type of levels, as an element of [LevelSort] *)
  - subst; econstructor; [ reflexivity | eapply kripke_preserves_level_sort; eassumption | assumption
                         | econstructor; [ eassumption | eapply glu_univ_elem_typ_monotone; eassumption ] ].
  - simpl_glu_rel.
    assert (Δ ⊢ A[φ]ʷ ≈ (a_pi κd κc IT OT)[φ]ʷ : abs_kind_sort κc Typeω@(large_level i)) as HAeq
      by (eapply kripke_preserves_kind_sort_eq; eassumption).
    rewrite exp_wk_pi in HAeq.
    econstructor; [ mauto 2 | eassumption | eassumption | eapply kripke_preserves_kind_sort; eassumption
                  | eapply kripke_preserves_kind_sort_q; eassumption | | ]; intros.
    + rewrite exp_wk_wk; mauto 4.
    + rewrite exp_wk_wk in *.
      rewrite exp_sub_wk_q_extend_wk.
      mauto 4.
  (** A proof: its proposition weakens *)
  - econstructor; [ eapply prop_glu_typ_pred_wk; eassumption | mauto 2 | assumption |].
    intros Δ0 φ0 R Hφ0 HR; rewrite !exp_wk_wk; mauto 3.
  - simpl_glu_rel.
    econstructor; [ split; [ mauto 2 | ] | mauto 2 | eassumption | ]; intros.
    + rewrite exp_wk_wk; mauto 4.
    + do 2 rewrite exp_wk_wk; mauto 4.
Qed.

(** Transport along a context refinement, as in [glu_lvl_resp_ctxsub]: a
    Kripke weakening into [Δ] extends to one into [Γ] by [kripke_ctxsub], which
    is all three lemmas need. *)

Lemma glu_elem_bot_resp_ctxsub : forall i a Γ A M m Δ,
    Γ ⊢ M : A ® m ∈ glu_elem_bot i a ->
    Δ ⊆ Γ ->
    Δ ⊢ M : A ® m ∈ glu_elem_bot i a.
Proof.
  intros * [] ?; econstructor;
    [ mauto 3 | eassumption | eapply glu_univ_elem_typ_resp_ctxsub | eassumption | intros ];
    mauto 4.
Qed.

Lemma glu_elem_top_resp_ctxsub : forall i a Γ A M m Δ,
    Γ ⊢ M : A ® m ∈ glu_elem_top i a ->
    Δ ⊆ Γ ->
    Δ ⊢ M : A ® m ∈ glu_elem_top i a.
Proof.
  intros * [] ?; econstructor;
    [ mauto 3 | eassumption | eapply glu_univ_elem_typ_resp_ctxsub | eassumption | intros ];
    mauto 4.
Qed.

Lemma glu_typ_top_resp_ctxsub : forall i a Γ A Δ,
    Γ ⊢ A ® glu_typ_top i a ->
    Δ ⊆ Γ ->
    Δ ⊢ A ® glu_typ_top i a.
Proof.
  intros * [] ?; econstructor; [ mauto 3 | eassumption | intros ]; mauto 4.
Qed.

Hint Resolve glu_elem_bot_resp_ctxsub glu_elem_top_resp_ctxsub glu_typ_top_resp_ctxsub : mctt.

(** The realisability predicates along equations: of the type, at the sort
    of its value's kind next to the large universe of the index, and of the
    term. *)
Lemma glu_elem_bot_resp_typ_exp_eq : forall i a Γ A A' M m,
    Γ ⊢ M : A ® m ∈ glu_elem_bot i a -> Γ ⊢ A ≈ A' : abs_kind_sort (domain_kind a) Typeω@(large_level i) ->
    Γ ⊢ M : A' ® m ∈ glu_elem_bot i a.
Proof.
  intros * [P El Hwf Hu Ht Hp Hr] HAA'.
  econstructor; [ eapply wf_conv_rel; eassumption | exact Hu | eapply glu_univ_elem_typ_resp_exp_eq; eassumption
                | exact Hp | intros Δ φ M' Hφ HM' ].
  eapply glu_ne_eq_conv; [ eapply kripke_preserves_kind_sort_eq; eassumption | exact (Hr _ _ _ Hφ HM') ].
Qed.

Lemma glu_elem_bot_resp_exp_eq : forall i a Γ A M M' m,
    Γ ⊢ M : A ® m ∈ glu_elem_bot i a -> Γ ⊢ M ≈ M' : A -> Γ ⊢ M' : A ® m ∈ glu_elem_bot i a.
Proof.
  intros * [P El Hwf Hu Ht Hp Hr] HMM'.
  econstructor; [ exact (presup_exp_eq_right HMM') | exact Hu | exact Ht | exact Hp | intros Δ φ M0 Hφ HM0 ].
  eapply glu_ne_eq_exp_eq; [| exact (Hr _ _ _ Hφ HM0) ]; symmetry; mauto 4.
Qed.

Lemma glu_elem_top_resp_typ_exp_eq : forall i a Γ A A' M m,
    Γ ⊢ M : A ® m ∈ glu_elem_top i a -> Γ ⊢ A ≈ A' : abs_kind_sort (domain_kind a) Typeω@(large_level i) ->
    Γ ⊢ M : A' ® m ∈ glu_elem_top i a.
Proof.
  intros * [P El Hwf Hu Ht Hp Hr] HAA'.
  econstructor; [ eapply wf_conv_rel; eassumption | exact Hu | eapply glu_univ_elem_typ_resp_exp_eq; eassumption
                | exact Hp | intros Δ φ w Hφ Hw ].
  eapply glu_nf_eq_conv; [ eapply kripke_preserves_kind_sort_eq; eassumption | exact (Hr _ _ _ Hφ Hw) ].
Qed.

Lemma glu_elem_top_resp_exp_eq : forall i a Γ A M M' m,
    Γ ⊢ M : A ® m ∈ glu_elem_top i a -> Γ ⊢ M ≈ M' : A -> Γ ⊢ M' : A ® m ∈ glu_elem_top i a.
Proof.
  intros * [P El Hwf Hu Ht Hp Hr] HMM'.
  econstructor; [ exact (presup_exp_eq_right HMM') | exact Hu | exact Ht | exact Hp | intros Δ φ w Hφ Hw ].
  eapply glu_nf_eq_exp_eq; [| exact (Hr _ _ _ Hφ Hw) ]; symmetry; mauto 4.
Qed.

Lemma glu_typ_top_resp_exp_eq : forall i a Γ A A',
    Γ ⊢ A ® glu_typ_top i a -> Γ ⊢ A ≈ A' : abs_kind_sort (domain_kind a) Typeω@(large_level i) ->
    Γ ⊢ A' ® glu_typ_top i a.
Proof.
  intros * [Hwf Hp Hr] HAA'.
  econstructor; [ exact (presup_exp_eq_right HAA') | exact Hp | intros Δ φ A0 Hφ HA0 ].
  eapply glu_nf_eq_exp_eq; [| exact (Hr _ _ _ Hφ HA0) ]; symmetry; eapply kripke_preserves_kind_sort_eq; eassumption.
Qed.

Add Parametric Morphism i a Γ : (glu_elem_bot i a Γ)
    with signature wf_exp_eq gc_deps gc_stack Γ (abs_kind_sort (domain_kind a) Typeω@(large_level i)) ==> eq ==> eq ==> iff
    as glu_elem_bot_morphism_iff2.
Proof.
  intros A A' HAA' M m; split; intro H; eapply glu_elem_bot_resp_typ_exp_eq; [ exact H | exact HAA' | exact H | symmetry; exact HAA' ].
Qed.

Add Parametric Morphism i a Γ A : (glu_elem_bot i a Γ A)
    with signature wf_exp_eq gc_deps gc_stack Γ A ==> eq ==> iff as glu_elem_bot_morphism_iff3.
Proof.
  intros M M' HMM' m; split; intro H; eapply glu_elem_bot_resp_exp_eq; [ exact H | exact HMM' | exact H | symmetry; exact HMM' ].
Qed.

Add Parametric Morphism i a Γ : (glu_elem_top i a Γ)
    with signature wf_exp_eq gc_deps gc_stack Γ (abs_kind_sort (domain_kind a) Typeω@(large_level i)) ==> eq ==> eq ==> iff
    as glu_elem_top_morphism_iff2.
Proof.
  intros A A' HAA' M m; split; intro H; eapply glu_elem_top_resp_typ_exp_eq; [ exact H | exact HAA' | exact H | symmetry; exact HAA' ].
Qed.

Add Parametric Morphism i a Γ A : (glu_elem_top i a Γ A)
    with signature wf_exp_eq gc_deps gc_stack Γ A ==> eq ==> iff as glu_elem_top_morphism_iff3.
Proof.
  intros M M' HMM' m; split; intro H; eapply glu_elem_top_resp_exp_eq; [ exact H | exact HMM' | exact H | symmetry; exact HMM' ].
Qed.

Add Parametric Morphism i a Γ : (glu_typ_top i a Γ)
    with signature wf_exp_eq gc_deps gc_stack Γ (abs_kind_sort (domain_kind a) Typeω@(large_level i)) ==> iff
    as glu_typ_top_morphism_iff2.
Proof.
  intros A A' HAA'; split; intro H; eapply glu_typ_top_resp_exp_eq; [ exact H | exact HAA' | exact H | symmetry; exact HAA' ].
Qed.

(** *** Simple Morphism instance for [glu_ctx_env] *)
Add Parametric Morphism : glu_ctx_env
    with signature glu_sub_pred_equivalence ==> eq ==> iff as simple_glu_ctx_env_morphism_iff.
Proof.
  intros Sb Sb' HSbSb' a.
  split; intro Horig; [gen Sb' | gen Sb];
    induction Horig; econstructor;
    try (etransitivity; [symmetry + idtac|]; eassumption); eauto.
Qed.

End Fixed_GCtx.

#[export] Existing Instance glu_elem_bot_morphism_iff2_Proper.
#[export] Existing Instance glu_elem_bot_morphism_iff3_Proper.
#[export] Existing Instance glu_elem_top_morphism_iff2_Proper.
#[export] Existing Instance glu_elem_top_morphism_iff3_Proper.
#[export] Existing Instance glu_typ_top_morphism_iff2_Proper.
#[export] Existing Instance simple_glu_ctx_env_morphism_iff_Proper.
#[export]
Hint Resolve glu_elem_bot_resp_ctxsub glu_elem_top_resp_ctxsub glu_typ_top_resp_ctxsub : mctt.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The right side of equal lists at a closed telescope is typed at its
    own instance of the telescope. *)
Lemma tele_eq_typed_r : forall Δ C Xs Ys, all_assumptions C -> ⊢ C ++ Δ ->
    List.length Xs = List.length C -> List.length Ys = List.length C ->
    (forall k X Y T, List.nth_error Xs k = Some X -> List.nth_error Ys k = Some Y ->
       List.nth_error (tele_insts C Id Xs) k = Some T -> Δ ⊢ X ≈ Y : T) ->
    forall j Y T, List.nth_error Ys j = Some Y -> List.nth_error (tele_insts C Id Ys) j = Some T -> Δ ⊢ Y : T.
Proof.
  intros * Hass HC HXl HYl HXY j Y T HY HT.
  assert (HΔ : ⊢ Δ) by (eapply ctx_app_wf_tail; exact HC).
  destruct (nth_error_lt_some Xs j ltac:(rewrite HXl, <- HYl; apply List.nth_error_Some; congruence)) as [X HX].
  destruct (nth_error_lt_some (tele_insts C Id Xs) j) as [T0 HT0].
  { rewrite length_tele_insts by exact Hass.
    assert (j < List.length Ys) by (apply List.nth_error_Some; congruence); lia. }
  destruct (tele_insts_cong C Δ Δ Id Id Xs Ys Hass HC ltac:(apply wf_sub_eq_refl; mauto 3) HXl HYl HXY _ _ _ HT0 HT)
    as (S & HS & HTT).
  eapply wf_conv_sort; [ exact (presup_exp_eq_right (HXY _ _ _ _ HX HY HT0)) | exact (presup_exp_eq_right HTT) | exact HS | exact HTT ].
Qed.

(** Lists equal to the annotations of readbacks related up to proofs, at
    a closed telescope, are equal ([nf_annotate_proofs_upto]). *)
Lemma tele_eq_annotate_upto : forall Δ C Ps Qs W1 W2, all_assumptions C -> ⊢ C ++ Δ ->
    List.length Ps = List.length C -> List.length Qs = List.length C ->
    exps_eq_at Δ C Ps (List.map nf_to_exp (List.map nf_annotate_proofs W1)) ->
    exps_eq_at Δ C Qs (List.map nf_to_exp (List.map nf_annotate_proofs W2)) ->
    nfs_eq_upto_proofs W1 W2 -> exps_eq_at Δ C Ps Qs.
Proof.
  intros * Hass HC HPl HQl HP HQ E.
  set (A1 := List.map nf_to_exp (List.map nf_annotate_proofs W1)) in *.
  set (A2 := List.map nf_to_exp (List.map nf_annotate_proofs W2)) in *.
  destruct HP as [HlP HP], HQ as [HlQ HQ].
  assert (HA1 : List.length A1 = List.length C) by congruence.
  assert (HA2 : List.length A2 = List.length C) by congruence.
  assert (H12 : forall j X Y T, List.nth_error A1 j = Some X -> List.nth_error A2 j = Some Y ->
                  List.nth_error (tele_insts C Id A1) j = Some T -> Δ ⊢ X ≈ Y : T).
  { intros j X Y T HX HY HT.
    unfold A1, A2 in HX, HY; rewrite !List.nth_error_map in HX, HY.
    destruct (List.nth_error W1 j) as [w1 |] eqn:Hw1; [| discriminate ];
      destruct (List.nth_error W2 j) as [w2 |] eqn:Hw2; [| discriminate ]; cbn in HX, HY; injection HX as <-; injection HY as <-.
    destruct (nfs_eq_upto_proofs_nth _ _ _ _ E Hw1) as (w2' & Hw2' & Ew); rewrite Hw2 in Hw2'; injection Hw2' as <-.
    destruct (nth_error_lt_some (tele_insts C Id A2) j) as [T2 HT2].
    { rewrite length_tele_insts by exact Hass; rewrite <- HA2, ?PeanoNat.Nat.min_id; apply List.nth_error_Some.
      unfold A2; rewrite !List.nth_error_map, Hw2; discriminate. }
    eapply nf_annotate_proofs_upto; [ | eexists | exact Ew ].
    - eapply (tele_eq_typed_r Δ C Ps A1 Hass HC HPl HA1 HP); [| exact HT ].
      unfold A1; rewrite !List.nth_error_map, Hw1; reflexivity.
    - eapply (tele_eq_typed_r Δ C Qs A2 Hass HC HQl HA2 HQ); [| exact HT2 ].
      unfold A2; rewrite !List.nth_error_map, Hw2; reflexivity. }
  split; [ congruence |].
  eapply (tele_eq_trans _ C Ps A1 Qs Hass HC HPl HA1 HQl HP).
  eapply (tele_eq_trans _ C A1 A2 Qs Hass HC HA1 HA2 HQl H12).
  eapply (tele_eq_sym _ C Qs A2 Hass HC HQl HA2 HQ).
Qed.

(** Equal lists of terms at a closed telescope are equal at every
    weakening. *)
Lemma exps_eq_at_wk : forall Δ Δ' φ T Xs Ys, all_assumptions T -> ctx_scoped 0 T -> Δ' ⊢ᵏ φ : Δ ->
    exps_eq_at Δ T Xs Ys -> exps_eq_at Δ' T (List.map (fun X => X[φ]ʷ) Xs) (List.map (fun Y => Y[φ]ʷ) Ys).
Proof.
  intros * Hass Hs Hφ [Hl H]; split; [ rewrite !List.length_map; exact Hl |].
  intros k X Y A HX HY HA.
  rewrite List.nth_error_map in HX, HY.
  destruct (List.nth_error Xs k) as [X0 |] eqn:HX0; [| discriminate ]; injection HX as <-.
  destruct (List.nth_error Ys k) as [Y0 |] eqn:HY0; [| discriminate ]; injection HY as <-.
  rewrite <- (tele_insts_closed_wk _ _ _ Hass Hs), List.nth_error_map in HA.
  destruct (List.nth_error (tele_insts T Id Xs) k) as [A0 |] eqn:HA0; [| discriminate ]; injection HA as <-.
  pose proof (H _ _ _ _ HX0 HY0 HA0); mauto 3.
Qed.

(** The parameters of a type predicate at a weakening, at a list equal to
    them there, are equal to the ones of another predicate glued to the same
    values. *)
Lemma exps_eq_at_params_wk : forall p D k Mk Δ Δ' φ Xs Ys, ind_lookup gc_deps gc_stack p = Some D ->
    ind_member D k = Some Mk -> Δ' ⊢ᵏ φ : Δ ->
    exps_eq_at Δ (im_params D Mk) Xs Ys ->
    exps_eq_at Δ' (im_params D Mk) (List.map (fun X => X[φ]ʷ) Xs) (List.map (fun Y => Y[φ]ʷ) Ys).
Proof.
  intros * Hl HMk Hφ H.
  assert (HΔ : ⊢ Δ) by (eapply kripke_cod; eassumption).
  destruct (decl_of_lookup _ _ _ _ _ HΔ Hl) as [_ Hc].
  eapply exps_eq_at_wk; [ eapply decl_closed_params_ass; eassumption | eapply decl_closed_params; eassumption
                       | exact Hφ | exact H ].
Qed.

(** Equal parameters are equal at their uniform part. *)
Lemma exps_eq_at_uparams_of_params : forall D Mk Δ Xs Ys, decl_closed D ->
    List.length Xs = im_np D Mk -> exps_eq_at Δ (im_params D Mk) Xs Ys ->
    exps_eq_at Δ (ind_uparams D) (List.firstn (ind_nu D) Xs) (List.firstn (ind_nu D) Ys).
Proof.
  intros * Hc HXl [Hl H]; split; [ rewrite !List.length_firstn; lia |].
  pose proof (decl_uparams_ass D Hc) as HassU.
  intros k X Y A HX HY HA.
  rewrite List.nth_error_firstn in HX, HY.
  destruct (PeanoNat.Nat.ltb_spec k (ind_nu D)); [| discriminate ].
  apply (H k X Y A HX HY).
  unfold im_params; rewrite <- (List.firstn_skipn (ind_nu D) Xs), tele_insts_app
    by (try exact HassU; rewrite List.length_firstn; unfold im_np, ind_nu in *; lia).
  rewrite List.nth_error_app1; [ exact HA |].
  rewrite length_tele_insts by exact HassU; rewrite List.length_firstn; unfold im_np, ind_nu in *; lia.
Qed.

(** Parameters with an equal uniform part, the rest unchanged. *)
Lemma exps_eq_at_params_of_uparams : forall D Mk Δ Xs Us', decl_closed D ->
    List.length Xs = im_np D Mk ->
    (forall k X A, List.nth_error Xs k = Some X -> List.nth_error (tele_insts (im_params D Mk) Id Xs) k = Some A -> Δ ⊢ X : A) ->
    exps_eq_at Δ (ind_uparams D) (List.firstn (ind_nu D) Xs) Us' ->
    exps_eq_at Δ (im_params D Mk) Xs (Us' ++ List.skipn (ind_nu D) Xs).
Proof.
  intros * Hc HXl HXt [Hl H].
  pose proof (decl_uparams_ass D Hc) as HassU.
  assert (LU : List.length (List.firstn (ind_nu D) Xs) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HXl; lia).
  pose proof Hl as Hl0; rewrite LU in Hl0.
  split; [ rewrite List.length_app, List.length_skipn; unfold im_np, im_nn in HXl; lia |].
  intros k X Y A HX HY HA.
  destruct (PeanoNat.Nat.lt_ge_cases k (ind_nu D)) as [Hk | Hk].
  - rewrite List.nth_error_app1 in HY by lia.
    apply (H k X Y A); [ rewrite List.nth_error_firstn; destruct (PeanoNat.Nat.ltb_spec k (ind_nu D)); [ exact HX | lia ] | exact HY |].
    unfold im_params in HA; rewrite <- (List.firstn_skipn (ind_nu D) Xs), tele_insts_app in HA
      by (try exact HassU; rewrite LU; unfold ind_nu; lia).
    rewrite List.nth_error_app1 in HA; [ exact HA |].
    rewrite length_tele_insts by exact HassU; rewrite LU; unfold ind_nu in *; lia.
  - rewrite List.nth_error_app2 in HY by lia.
    rewrite List.nth_error_skipn in HY.
    replace (ind_nu D + (k - List.length Us')) with k in HY by lia.
    rewrite HX in HY; injection HY as <-.
    apply wf_exp_eq_refl; eapply HXt; eassumption.
Qed.

Lemma exps_eq_at_uparams_trans : forall p D Δ Xs Ys Zs, ind_lookup gc_deps gc_stack p = Some D -> ⊢ Δ ->
    List.length Xs = ind_nu D -> exps_eq_at Δ (ind_uparams D) Xs Ys -> exps_eq_at Δ (ind_uparams D) Ys Zs ->
    exps_eq_at Δ (ind_uparams D) Xs Zs.
Proof.
  intros * Hl HΔ HXl [Hl1 H1] [Hl2 H2].
  destruct (decl_of_lookup _ _ _ _ _ HΔ Hl) as [_ Hc].
  split; [ congruence |].
  unfold ind_nu in HXl.
  eapply (tele_eq_trans Δ (ind_uparams D) Xs Ys Zs (decl_uparams_ass D Hc) (uparams_ctx_wf _ _ _ Hl HΔ)); [ lia | lia | lia | exact H1 | exact H2 ].
Qed.

(** ** Moving an Element of an Inductive Type

    An element glued at the uniform parameters [ups] is glued at [ups'],
    where its type is glued: its type's two parameter lists are equal
    where they are glued to the two values ([Hpe]), and the element's
    telescopes move by the witnessed moves of their gluings, the target's
    components given by the target type ([ind_glu_elem_move]). *)
Lemma ind_glu_exp_move : forall p D ups ups' ns ns' k Mk NP NEl AP AEl DP DEl NP' NEl' AP' AEl' DP' DEl' er er' U U' Γ A M m,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk ->
    group_structure D -> ind_canon_props D ups ->
    ind_fam_agree D (canon_nparams_rel D ups) (canon_nparams_rel D ups') (canon_args_rel D ups) (canon_args_rel D ups')
      (canon_doms_rel D ups) (canon_doms_rel D ups') ->
    adm_uparams D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups) ups' ->
    (forall m Mm j vs, ind_member D m = Some Mm -> j < im_nn Mm -> tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
       forall Γ A N n, NEl m j vs Γ A N n -> NP' m j vs Γ A -> NEl' m j vs Γ A N n) ->
    (forall m Mm ms c gs j vs, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
       j < List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
       forall Γ A N n, AEl m ms c j vs Γ A N n -> AP' m ms c j vs Γ A -> AEl' m ms c j vs Γ A N n) ->
    (forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
       tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms -> ind_con Mm c = Some gs ->
       gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t)
         j ys ys ->
       let Ts := List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t) in
       forall Γ A N n, DEl' m (ms ++ ws ++ ys) Ts B Γ A N n -> DP m (ms ++ ws ++ ys) Ts B Γ A ->
         DEl m (ms ++ ws ++ ys) Ts B Γ A N n) ->
    (forall v, er v v -> er' v v) ->
    (forall Δ Xs Ys, ⊢ Δ -> glu_params_top D Mk Δ Xs (ups ++ ns) -> glu_params_top D Mk Δ Ys (ups' ++ ns') ->
       exps_eq_at Δ (im_params D Mk) Xs Ys) ->
    ind_glu_exp p D ups ns NP NEl AP AEl DP DEl k Mk er U Γ A M m ->
    (exists Ps2, ind_typ_at p D ups' ns' NP' NEl' AP' AEl' DP' DEl' k Mk U' Γ A Ps2) ->
    ind_glu_exp p D ups' ns' NP' NEl' AP' AEl' DP' DEl' k Mk er' U' Γ A M m.
Proof.
  intros * Hl HMk Hass Hcp Hfam Hadm HNm HAm HDm Her Hpe [HMt Hm Ps HPs Hk] (Ps2 & HPs2).
  assert (Hdc : forall Δ, ⊢ Δ -> decl_closed D) by (intros Δ HΔ; exact (proj2 (decl_of_lookup _ _ _ _ _ HΔ Hl))).
  assert (Hur : forall Δ Xs Ys, ⊢ Δ -> List.length Xs = ind_nu D -> exps_eq_at Δ (ind_uparams D) Xs Ys ->
                  exps_eq_at Δ (ind_uparams D) Ys Ys).
  { intros Δ Xs Ys HΔ HXl [HXY1 HXY]; pose proof (Hdc _ HΔ) as Hc.
    split; [ reflexivity |]; intros j0 X Y T0 HX HY HT0; rewrite HX in HY; injection HY as <-.
    apply wf_exp_eq_refl.
    exact (tele_eq_typed_r Δ (ind_uparams D) Xs Ys (decl_uparams_ass D Hc) (uparams_ctx_wf _ _ _ Hl HΔ) HXl
             ltac:(unfold ind_nu in HXl; congruence) HXY j0 X T0 HX HT0). }
  assert (Hct : forall Γ0 Us Δ0 φ0 Us', List.length Us = ind_nu D -> Δ0 ⊢ᵏ φ0 : Γ0 ->
             exps_eq_at Δ0 (ind_uparams D) (List.map (fun U => U[φ0]ʷ) Us) Us' ->
             (forall Δ φ Us0, Δ ⊢ᵏ φ : Γ0 -> exps_eq_at Δ (ind_uparams D) (List.map (fun U => U[φ]ʷ) Us) Us0 ->
                ind_glu_components p D ups' NP' NEl' AP' AEl' DP' DEl' Δ Us0) ->
             forall Δ1 φ1 Us1, Δ1 ⊢ᵏ φ1 : Δ0 -> exps_eq_at Δ1 (ind_uparams D) (List.map (fun U => U[φ1]ʷ) Us') Us1 ->
               ind_glu_components p D ups' NP' NEl' AP' AEl' DP' DEl' Δ1 Us1).
  { intros * HUl Hφ0 HUq HCH0 Δ1 φ1 Us1 Hφ1 HUs1.
    assert (HΔ1 : ⊢ Δ1) by (eapply kripke_dom; eassumption).
    pose proof (Hdc _ HΔ1) as Hc.
    apply (HCH0 Δ1 _ Us1 (kripke_compose _ _ _ _ _ Hφ1 Hφ0)).
    rewrite <- map_wk_wk.
    eapply exps_eq_at_uparams_trans; [ exact Hl | exact HΔ1 | rewrite !List.length_map; exact HUl
                                     | exact (exps_eq_at_wk _ _ _ _ _ _ (decl_uparams_ass D Hc) (decl_uparams_closed D Hc) Hφ1 HUq)
                                     | exact HUs1 ]. }
  refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMt (Her _ Hm) Ps2 HPs2 _).
  intros Δ φ Ps'' Hφ HPs''.
  assert (HΔ : ⊢ Δ) by (eapply kripke_dom; eassumption).
  pose proof (Hdc _ HΔ) as Hc.
  pose proof HPs as [_ HPk]; destruct (HPk Δ φ Hφ) as [Hpt _ _ _].
  pose proof HPs2 as [_ HPk2]; destruct (HPk2 Δ φ Hφ) as [Hpt2 _ _ _].
  pose proof (glu_params_top_len _ _ _ _ _ Hpt) as HL1; pose proof (glu_params_top_len _ _ _ _ _ Hpt2) as HL2.
  pose proof (decl_closed_params_ass _ _ _ Hc HMk) as HassP.
  pose proof (params_ctx_wf _ _ _ _ _ Hl HMk HΔ) as HCP.
  pose proof (Hpe _ _ _ HΔ Hpt Hpt2) as HEq.
  assert (HEq'' : exps_eq_at Δ (im_params D Mk) (List.map (fun P => P[φ]ʷ) Ps) Ps'').
  { destruct HEq as [Hl1 H1e]; destruct HPs'' as [Hl2 H2e]; split; [ congruence |].
    eapply (tele_eq_trans _ _ _ (List.map (fun P => P[φ]ʷ) Ps2) _ HassP HCP);
      [ rewrite length_im_params; exact HL1 | rewrite length_im_params; exact HL2 | rewrite length_im_params; congruence
      | exact H1e | exact H2e ]. }
  pose proof (Hk Δ φ Ps'' Hφ HEq'') as Hsrc.
  assert (HL'' : List.length Ps'' = im_np D Mk) by (destruct HPs'' as [Hl2 _]; unfold im_np in *; congruence).
  pose proof (exps_eq_at_uparams_of_params _ _ _ _ _ Hc HL2 HPs'') as HU2.
  eapply (ind_glu_elem_move p D ups NEl AEl DP DEl Hass Hcp ups' NP' NEl' AP' AEl' DP' DEl' Hfam Hadm HNm HAm HDm);
    [ intros j0 Mj Δ0 Xs Ys HMj HXl HXY; exact (exps_eq_at_uparams_of_params _ _ _ _ _ Hc HXl HXY)
    | exact Hur
    | intros Γ0 Δ0 φ0 Xs Hφ0 HXX; pose proof (Hdc _ (ltac:(eapply kripke_dom; eassumption))) as Hc0;
      exact (exps_eq_at_wk _ _ _ _ _ _ (decl_uparams_ass D Hc0) (decl_uparams_closed D Hc0) Hφ0 HXX)
    | exact Hct | exact Hsrc | exact HΔ
    | exact (Hur Δ (List.firstn (ind_nu D) (List.map (fun P => P[φ]ʷ) Ps2)) (List.firstn (ind_nu D) Ps'') HΔ
               ltac:(rewrite List.length_firstn; unfold im_np in HL2; lia) HU2)
    | ].
  intros Δ0 φ0 Us0 Hφ0 HU0.
  assert (HΔ0 : ⊢ Δ0) by (eapply kripke_dom; eassumption).
  destruct (HPk2 Δ0 _ (kripke_compose _ _ _ _ _ Hφ0 Hφ)) as [_ _ Hcs2 _].
  assert (HUl0 : List.length Us0 = ind_nu D)
    by (destruct HU0 as [Hl0 _]; rewrite List.length_map, List.length_firstn in Hl0; unfold im_np in HL''; unfold ind_nu in *; lia).
  replace Us0 with (List.firstn (ind_nu D) (Us0 ++ List.skipn (ind_nu D) (List.map (fun P => P[φ0]ʷ) Ps'')))
    by (rewrite List.firstn_app, <- HUl0, PeanoNat.Nat.sub_diag, List.firstn_all, List.firstn_O, List.app_nil_r; reflexivity).
  apply Hcs2.
  rewrite <- map_wk_wk.
  pose proof (exps_eq_at_params_wk _ _ _ _ _ _ _ _ _ Hl HMk Hφ0 HPs'') as HP0.
  assert (HPt0 : forall j0 X T0, List.nth_error (List.map (fun P => P[φ0]ʷ) Ps'') j0 = Some X ->
                   List.nth_error (tele_insts (im_params D Mk) Id (List.map (fun P => P[φ0]ʷ) Ps'')) j0 = Some T0 ->
                   Δ0 ⊢ X : T0).
  { destruct HP0 as [Hl0 Hp0].
    eapply (tele_eq_typed_r Δ0 (im_params D Mk) _ _ HassP (params_ctx_wf _ _ _ _ _ Hl HMk HΔ0)); [ | | exact Hp0 ];
      rewrite ?List.length_map, length_im_params; [ rewrite List.length_map in HL2; exact HL2 | congruence ]. }
  pose proof (exps_eq_at_params_of_uparams _ _ _ _ Us0 Hc ltac:(rewrite List.length_map; exact HL'') HPt0
                ltac:(rewrite ?List.firstn_map; exact HU0)) as HP1.
  destruct HP0 as [Hl0 Hp0]; destruct HP1 as [Hl1 Hp1]; split; [ congruence |].
  eapply (tele_eq_trans _ _ _ (List.map (fun P => P[φ0]ʷ) Ps'') _ HassP (params_ctx_wf _ _ _ _ _ Hl HMk HΔ0));
    [ rewrite !List.length_map, length_im_params; rewrite List.length_map in HL2; exact HL2
    | rewrite List.length_map, length_im_params; exact HL''
    | rewrite length_im_params, <- Hl1, List.length_map; exact HL'' | exact Hp0 | exact Hp1 ].
Qed.

End Fixed_GCtx.

