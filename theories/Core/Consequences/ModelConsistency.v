(** * Consistency and Canonical Forms from the Set Model

    At a global context the set model models ([set_gctx_ok]), no closed
    term inhabits [⊥] ([consistency_False]) nor every type of a universe
    ([consistency]): the fundamental theorem of the set model reads a
    closed term as an element of its type's value, and [⊥]'s value, and a
    universe's empty inductive code, have none.  The model is a premise:
    a tower of universes and a valuation of the globals; the kinds of a
    λ, which the model's interpretation of a λ reads, are unique by the
    typing ([fn_kinds_unique_ext_wf]).  Over it, at a
    transparent global context, closed terms have canonical forms
    ([canonical_form_of_typ], [canonical_form_of_ind]): a closed neutral
    would be headed by a variable or would prove [⊥].  Without axioms,
    where opaque definitions may leave normal forms stuck, the canonical
    forms are read after unsealing ([canonical_form_of_ind_nat_no_axioms]),
    and so for every program ([canonical_form_of_bound_nat_prog]).

    It sits after the set model's fundamental theorem, which the
    consequences of NbE in [Consistency.v] come before. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Consequences Require Export Consistency.
From Mctt.Core.Consequences Require Import FnKinds.
From Mctt.Core Require Export Soundness.
From Mctt.Core.Completeness.Consequences Require Export Types.
From Mctt.Core.Semantic Require Export Transparency Stuck.
From Mctt.Core.Syntactic Require Export Unseal.
From Mctt.Core.Syntactic Require Import CoreInversions.
From Mctt.Core.Semantic Require Import Realizability Levels.
From Mctt.Core.Completeness.LogicalRelation Require Import Lemmas.
From Mctt.Core.Completeness Require Import UniverseCases ContextCases FunctionCases.
From Mctt.Core.Completeness.Consequences Require Import Rules.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
Require Import Mctt.Core.Syntactic.Command.
From Mctt.Core.Syntactic Require Import Builtin NfRename.
From Mctt.Core.SetModel Require Import Judgments FundamentalTheorem.
From Mctt.Core.SetModel.Interpretation Require Import ContextRelation.
From Mctt.Core.SetModel.Cases Require Import SubtypingCases.

Import Domain_Notations Fixed_Notations.
Import Wk_Notations.
#[local] Open Scope list_scope.

(** ** Consistency

    At a global context the set model models, a closed term is an element
    of its type's value at the empty environment. *)

Section Modelled_GCtx.
  Context {GC : GCtx}.
  (** The tower of universes of the model *)
  Variable T : universe_tower.
  (** The valuation of the globals *)
  Variable γ : global_valuation.
  (** It models the global context *)
  Hypothesis Hok : set_gctx_ok T γ.

(** A typed term holds in the model at its own context: the fundamental
    theorem read where the derivation is checked, the kinds of a λ unique
    by the typing ([fn_kinds_unique_ext_wf]). *)
Lemma set_rel_exp_eq_of_wf_exp : forall Γ A M, Γ ⊢ M : A -> set_rel_exp_eq T γ Γ A M M.
Proof.
  intros Γ A M HM.
  pose proof (ctx_wf_gctx _ _ _ (presup_exp_ctx HM)) as Hg.
  pose proof Hok as Hok'. pose proof (fn_kinds_unique_ext_wf Hg) as Hfn'.
  rewrite (gc_mk_eta GC) in Hok', Hfn'.
  pose proof (set_gctx_embedding_refl _ _ T γ Hg Hfn' Hok') as Hμ.
  destruct (proj1 (proj2 (set_fundamental T γ)) _ _ _ _ _ HM) as [_ HM'].
  pose proof (HM' _ _ Hμ) as H. rewrite <- gc_mk_eta in H. exact H.
Qed.

(** A universe holds in the model at its own context. *)
Lemma set_rel_universe_of_wf_is_univ : forall Γ U, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵤ U -> set_rel_universe T γ Γ U.
Proof.
  intros Γ U HU.
  pose proof (ctx_wf_gctx _ _ _ (presup_is_univ_ctx HU)) as Hg.
  pose proof Hok as Hok'. pose proof (fn_kinds_unique_ext_wf Hg) as Hfn'.
  rewrite (gc_mk_eta GC) in Hok', Hfn'.
  pose proof (set_gctx_embedding_refl _ _ T γ Hg Hfn' Hok') as Hμ.
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 (set_fundamental T γ))))) _ _ _ _ HU) as [_ HU'].
  pose proof (HU' _ _ Hμ) as H. rewrite <- gc_mk_eta in H. exact H.
Qed.

(** The empty environment is one of the empty context. *)
Lemma set_env_in_empty : set_env_in T γ nil empty_set_env.
Proof. intros x; constructor; apply set_eq_refl. Qed.

(** There is no closed proof of [⊥]: its value would be an element of
    [⊥]'s value, the false proposition's code, which has none. *)
Theorem consistency_False : forall M,
    ~ ⋅ ⊢ M : ⊥.
Proof.
  intros M HM.
  destruct (set_rel_exp_eq_of_wf_exp _ _ _ HM) as (FA & FM & FM' & [HFA _ _ _ Hm]).
  pose proof (Hm _ set_env_in_empty) as Hv.
  pose proof (set_denotes_unique _ _ _ _ _ HFA _ _ _ set_env_in_empty (set_interp_False T γ nil empty_set_env)) as EA.
  pose proof (set_mem_eq_r _ _ _ (code_carrier_resp _ _ (set_eq_sym _ _ EA)) Hv) as Hv'.
  unfold prop_code in Hv'. pose proof (set_mem_eq_r _ _ _ (code_carrier_type_code _ _ _) Hv') as Hv''.
  apply set_mem_truth in Hv''. exact (proj1 Hv'').
Qed.

(** Consistency at a universe: there is no closed inhabitant of [Π U #0]
    for a universe term [U].  Its value would apply to the universe's code
    of the empty inductive type ([grothendieck_empty_inductive_code]), at
    an element of that code's empty carrier.  At [Typeω@i] this is
    [consistency_large], at [Type@n] [consistency_lit]. *)
Theorem consistency : forall U M,
    univ_term U ->
    ~ ⋅ ⊢ M : Π{ak_relevant} U #0.
Proof.
  intros U M HUt HM.
  assert (HUC : exists C, ⋅ ⊢ U : C).
  { gen_presups.
    match goal with H : _ ⍮ _ ⍮ _ ⊢ a_pi _ _ _ _ : _ |- _ =>
      destruct (wf_pi_inversion H) as [(i & Hdom & _) | (L & n & _ & Hdom & _)] end; eexists; exact Hdom. }
  destruct HUC as [C HUC].
  assert (HUu : gc_deps ⍮ gc_stack ⍮ ⋅ ⊢ᵤ U).
  { destruct HUt as [i | t]; [ apply wf_is_univ_large; exact (presup_exp_ctx HUC) |].
    destruct (wf_univ_lvl_inversion HUC) as [n Ht]. eapply wf_is_univ_small; exact Ht. }
  destruct (set_rel_universe_of_wf_is_univ _ _ HUu) as (FU & [_ HFU Hsh]).
  destruct (set_rel_exp_eq_of_wf_exp _ _ _ HM) as (FA & FM & FM' & [HFA _ _ _ Hm]).
  destruct (Hsh _ set_env_in_empty) as (V & HV & l & El).
  (** The [Π]'s value is the code of the functions from the universe into
      the codes' carriers *)
  assert (Hpi : set_interp T γ nil empty_set_env (Π{ak_relevant} U #0) (pi_code (FU empty_set_env) (fun x => x))).
  { apply set_interp_pi;
      [ discriminate | | exact (set_denotes_exists _ _ _ _ _ HFU _ set_env_in_empty) | intros x _; exact (set_interp_var _ _ _ _ 0) ].
    gen_presups.
    match goal with H : _ ⍮ _ ⍮ _ ⊢ a_pi _ _ _ _ : _ |- _ =>
      destruct (wf_pi_inversion H) as [(i & _ & Hcod & _) | (L & n & _ & _ & Hcod & _)] end; exact (presup_exp_ctx Hcod). }
  pose proof (set_denotes_unique _ _ _ _ _ HFA _ _ _ set_env_in_empty Hpi) as EA.
  pose proof (Hm _ set_env_in_empty) as Hf.
  pose proof (set_mem_eq_r _ _ _ (code_carrier_resp _ _ (set_eq_sym _ _ EA)) Hf) as Hf1.
  unfold pi_code in Hf1. pose proof (set_mem_eq_r _ _ _ (code_carrier_type_code _ _ _) Hf1) as Hf2.
  assert (Hc : set_mem (inductive_code empty_set) (code_carrier (FU empty_set_env))).
  { eapply set_mem_eq_r; [ apply code_carrier_resp, set_eq_sym, El |].
    apply set_mem_universe_code.
    split; [ apply grothendieck_empty_inductive_code; exact HV | exact empty_inductive_code_relevant ]. }
  pose proof (function_set_apply _ _ _ _ code_carrier_resp Hf2 Hc) as Hy.
  unfold inductive_code in Hy. destruct (set_mem_eq_r _ _ _ (code_carrier_type_code _ _ _) Hy) as [[] _].
Qed.

Corollary consistency_large : forall {i} M,
    ~ ⋅ ⊢ M : Π{ak_relevant} Typeω@i #0.
Proof. intros; apply consistency, univ_term_typ. Qed.

Corollary consistency_lit : forall {n} M,
    ~ ⋅ ⊢ M : Π{ak_relevant} Type@n #0.
Proof. intros; apply consistency, univ_term_suniv. Qed.

End Modelled_GCtx.

(** ** Canonical Forms

    These hold only at a transparent global context: otherwise an axiom
    [c : Nat] is a closed neutral.  At a transparent context a normal form
    has no global head ([nbe_clean]), and a neutral without one has no
    type in the empty local context ([no_closed_neutral]). *)

Section Transparent_GCtx.
  Context {GC : GCtx}.
  Hypothesis Htr : gc_transparent gc_deps gc_stack.
  (** The tower of universes of the model *)
  Variable T : universe_tower.
  (** The valuation of the globals *)
  Variable γ : global_valuation.
  (** It models the global context *)
  Hypothesis Hok : set_gctx_ok T γ.

(** In the empty context, a neutral without a global head has no type: its
    head would be a variable, or it is an ex falso, whose proof of [⊥]
    ([closed_clean_neutral_proves_False]) there is none of. *)
Lemma no_closed_neutral : forall {A} {W : ne},
    ne_clean W ->
    ~ (⋅ ⊢ W : A).
Proof.
  intros * Hc HW; destruct (closed_clean_neutral_proves_False Hc HW) as [M HM]; exact (consistency_False T γ Hok _ HM).
Qed.

(** Canonicity at a universe.  A closed type of a universe term [U] has a
    normal form of the shape [typ_nf_below u], where [u] is the normal form
    of [U] ([typ_nf_below_of_nbe]): it is not neutral, since at a
    transparent context a closed neutral has no type.  At [Typeω@i] this is
    [canonical_form_of_large_typ], at [Type@n] [canonical_form_of_typ_lit]. *)
Theorem canonical_form_of_typ : forall {U M},
    univ_term U ->
    ⋅ ⊢ M : U ->
    exists u W, nbe_ty_f ⋅ U (universe_nf_to_nf u) /\ nbe_f ⋅ M U W /\ typ_nf_below u W.
Proof.
  intros * HT HM.
  destruct (soundness HM) as (W & Hn & HMW).
  destruct (univ_term_typed_large HT HM) as [k Hk].
  destruct (soundness_ty Hk) as (Ut & HU & _).
  destruct (nbe_ty_univ_term HT HU) as [u ->].
  exists u, W; split; [ exact HU | split; [ exact Hn |] ].
  eapply typ_nf_below_of_nbe; [ exact HT | exact HM | exact HU | exact Hn |].
  intros κ V ->.
  pose proof (nbe_clean _ _ Htr _ _ _ _ Hn) as Hc; cbn in Hc.
  assert (⋅ ⊢ V : U) by (gen_presups; assumption).
  eapply no_closed_neutral; eassumption.
Qed.

Corollary canonical_form_of_large_typ : forall {i M},
    ⋅ ⊢ M : Typeω@i ->
    exists W, nbe_f ⋅ M Typeω@i W /\ is_typ_constr W /\ (forall κ V, W <> ⇑ⁿ{κ} V).
Proof.
  intros * HM; destruct (canonical_form_of_typ (univ_term_typ i) HM) as (u & W & Hu & Hn & Hb).
  apply nbe_ty_typ_univ_nf in Hu as ->; exists W; split; [ exact Hn | exact (typ_nf_below_large _ _ Hb) ].
Qed.
Hint Resolve canonical_form_of_large_typ : mctt.

Corollary canonical_form_of_typ_lit : forall {n M},
    ⋅ ⊢ M : Type@n ->
    exists W, nbe_f ⋅ M Type@n W /\ small_typ_nf n W.
Proof.
  intros * HM; destruct (canonical_form_of_typ (univ_term_suniv _) HM) as (u & W & Hu & Hn & Hb).
  apply nbe_ty_lit_univ_nf in Hu as ->; exists W; split; [ exact Hn | exact (typ_nf_below_lit _ _ Hb) ].
Qed.

(** ** Canonical Forms of Inductive Types

    A closed term of an inductive type normalises to one of its
    constructors, applied to normal forms of its parameters and arguments:
    a neutral would be closed. *)
Theorem canonical_form_of_ind : forall {M p k Ps},
    ⋅ ⊢ M : apps (a_ind p k) Ps ->
    exists W, nbe_f ⋅ M (apps (a_ind p k) Ps) W /\
      exists D Mk c gs Vs, ind_lookup gc_deps gc_stack p = Some D /\ ind_member D k = Some Mk /\
        ind_con Mk c = Some gs /\ W = nf_con p k c Vs.
Proof.
  intros * HM.
  destruct (soundness HM) as (W & Hn & HMW).
  exists W; split; [ exact Hn |].
  pose proof (nbe_clean _ _ Htr _ _ _ _ Hn) as Hc.
  assert (HW : ⋅ ⊢ W : apps (a_ind p k) Ps) by (gen_presups; assumption).
  inversion Hn as [? a Hi Ha Hnt]; subst.
  inversion Hi; subst.
  destruct (eval_ind_value _ _ _ _ _ Ha) as [ms ->].
  (** An inductive type is relevant: its terms are read back *)
  destruct Hnt as [Hp | m ? _ Hm Hr]; [ cbn in Hp; discriminate |].
  inversion Hr; subst; try (cbn in *; discriminate).
  1,2: do 5 eexists; split; [ eassumption | split; [ eassumption | split; [ eassumption | reflexivity ] ] ].
  (* a record view's value: its one constructor *)
  - do 5 eexists; split; [ eassumption | split; [ eassumption | split; [| reflexivity ] ] ].
    match goal with Hc : im_cons ?Mj = ((?c, ?gs) :: nil)%list |- ind_con ?Mj _ = _ =>
      unfold ind_con; rewrite Hc; cbn; rewrite String.eqb_refl; reflexivity end.
  - exfalso; cbn in Hc, HW; eapply no_closed_neutral; eassumption.
Qed.

(** The member of a group of the shape of the natural numbers
    ([nat_shape]), whose constructors are [z] and [s]: declared, without
    non-uniform parameters, and with the constructors [z], without
    arguments, and [s], with one recursive argument of the member itself. *)
Record nat_member_shape (z s : String.string) (Mn : imember) : Prop := mk_nat_member_shape
  { (** The member is declared *)
    nat_member_shape_decl : im_is_decl Mn = true
    (** It has no non-uniform parameter *)
  ; nat_member_shape_nparams : im_nparams Mn = nil
    (** Its constructors are [z], without arguments, and [s], with one
        recursive argument of itself *)
  ; nat_member_shape_cons : forall c gs, ind_con Mn c = Some gs -> (c = z /\ gs = nil) \/ (c = s /\ gs = ca_rec (pt_self 0 nil) :: nil) }.

Lemma nat_shape_inv : forall D z s, nat_shape D = Some (z, s) ->
    ind_uparams D = nil /\ (forall k Mk, ind_member D k = Some Mk -> k = 0 /\ nat_member_shape z s Mk).
Proof.
  intros [Δ S ms] z s H; unfold nat_shape in H; cbn in H.
  destruct Δ; [| discriminate ].
  destruct ms as [| [[pm | ? ? ? ? | ? ? ?] [|] cs] [|]]; try discriminate.
  split; [ reflexivity |].
  intros [| k] Mk Hk; cbn in Hk; [| destruct k; discriminate ].
  injection Hk as <-; split; [ reflexivity |].
  constructor; [ reflexivity | reflexivity |].
  intros c gs Hc; unfold ind_con in Hc; cbn in Hc; unfold nat_cons_shape in H.
  repeat (match type of H with context [match ?x with _ => _ end] => destruct x; try discriminate end).
  all: injection H as <- <-; cbn in Hc.
  all: repeat (match type of Hc with context [String.eqb ?a ?b] => destruct (String.eqb_spec a b) as [-> | ?]; [ injection Hc as <-; auto | ] end); discriminate.
Qed.

(** A term of the domain of a [Π] into a universe is one of the domain of
    a [Π] below. *)
Lemma subtyp_pi_dom_conv : forall {Γ κ' A' B' κ A B N},
    Γ ⊢ Π{κ'} A' B' ⊆ Π{κ} A B -> Γ ⊢ N : A -> Γ ⊢ N : A'.
Proof using GC.
  intros * H HN.
  assert (exists C, Γ ⊢ Π{κ} A B : C) as [C HC] by (gen_presups; eexists; eassumption).
  destruct (wf_pi_typed_large HC) as [k0 Hk0].
  (** A type at the sort of a kind is one at a sort *)
  assert (HSs : forall κ0 (j : nat), type_sort (abs_kind_sort κ0 Typeω@j))
    by (intros; exact (sort_kind_type_sort _ _ (sort_kind_abs_kind_sort _ _))).
  apply (subtyp_spec_large (k := k0)) in H
    as [[k Heq] | [(U & V & [k1 HU] & [k2 HV] & Hs) | (κ1 & A1 & A2 & B1 & B2 & [k1 HA] & [k2 HB] & (S3 & HS3 & H13) & _)]];
    [| | | right; exact Hk0 ].
  - apply exp_eq_pi_inversion in Heq as (_ & Hd & _).
    eapply exp_conv_sort; [ apply HSs | symmetry; exact Hd | exact HN ].
  - exfalso; destruct (univ_sub_sort_term Hs) as [HUt _]; eapply pi_sort_term_absurd; [ exact HUt | exact HU ].
  - apply exp_eq_pi_inversion in HA as (_ & HA & _); apply exp_eq_pi_inversion in HB as (_ & HB & _).
    assert (Γ ⊢ N : B1) by (eapply exp_conv_sort; [ apply HSs | symmetry; exact HB | exact HN ]).
    assert (Γ ⊢ N : A1) by (eapply exp_conv_sort; [ exact (sort_kind_type_sort _ _ HS3) | symmetry; exact H13 | assumption ]).
    eapply exp_conv_sort; [ apply HSs | symmetry; exact HA | assumption ].
Qed.

(** The normal forms of a type shaped as the natural numbers
    ([nat_shape]), its constructors [z] and [s]: chains of [s] ending in
    [z]. *)
Inductive nat_chain_nf (p : qname) (z s : String.string) : nf -> Prop :=
(** The constructor [z] *)
| nat_chain_nf_zero : nat_chain_nf p z s (nf_con p 0 z nil)
(** The constructor [s] at a chain *)
| nat_chain_nf_succ : forall W, nat_chain_nf p z s W -> nat_chain_nf p z s (nf_con p 0 s (cons W nil)).

(** The number of constructors of one argument heading a normal form: the
    number a chain of [s] ending in [z] stands for. *)
Definition nf_succ_depth (W : nf) : nat :=
  (fix go (W : nf) : nat :=
     match W with
     | nf_con _ _ _ (cons V nil) => S (go V)
     | _ => 0
     end) W.

(** The readback of a value of a type of the shape of the natural numbers
    at that type, one step: the constructor [z], the constructor [s] at the
    readback of a value of the same type, or a neutral. *)
Inductive nat_read_step (p : qname) (z s : String.string) : nf -> Prop :=
(** The constructor [z] *)
| nat_read_step_zero : nat_read_step p z s (nf_con p 0 z nil)
(** The constructor [s] at the readback of a value of the same type *)
| nat_read_step_succ : forall v V, Rnf ⇓ (d_ind p 0 nil) v in gc_deps ⍮ gc_stack ⍮ 0 ↘ V ->
    nat_read_step p z s (nf_con p 0 s (cons V nil))
(** A neutral *)
| nat_read_step_neut : forall κ M, nat_read_step p z s ⇑ⁿ{κ} M.

Lemma nat_read_step_of_read : forall p D z s W v, ind_lookup gc_deps gc_stack p = Some D -> nat_shape D = Some (z, s) ->
    Rnf ⇓ (d_ind p 0 nil) v in gc_deps ⍮ gc_stack ⍮ 0 ↘ W -> nat_read_step p z s W.
Proof.
  intros * Hl Hs Hr; destruct (nat_shape_inv _ _ _ Hs) as (Hnu & Hms).
  inversion Hr; subst; try (cbn in *; discriminate); [| | | constructor ].
  all: match goal with H : ind_lookup _ _ _ = Some ?D0 |- _ => assert (D0 = D) as -> by congruence end.
  all: match goal with H : ind_member _ 0 = Some _ |- _ => destruct (Hms _ _ H) as [_ [Hdec Hnp Hcs]] end.
  (** A view, or a record view, is not a declared member. *)
  2: match goal with H : im_head _ = mh_view _ _ _ _ |- _ => unfold im_is_decl in Hdec; rewrite H in Hdec; discriminate end.
  2: match goal with H : im_head _ = mh_record _ _ _ |- _ => unfold im_is_decl in Hdec; rewrite H in Hdec; discriminate end.
  match goal with H : ind_con _ _ = Some _ |- _ => destruct (Hcs _ _ H) as [[-> ->] | [-> ->]] end.
  all: unfold im_params, im_np, im_nn, ind_nu in *; rewrite Hnu, Hnp in *; cbn in *.
  all: match goal with H : Rps _ at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H; subst end.
  all: match goal with H : Rcargs _ at _ of _ _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H; subst end.
  1: constructor.
  match goal with H : Rcargs _ at nil of _ _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H; subst end.
  match goal with H : Rsh _ at _ of _ _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H; subst end.
  match goal with H : ⟦ nil ⟧* _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H; subst end.
  cbn; econstructor; eassumption.
Qed.

(** An inductive type is below no [Π] into a universe. *)
Lemma subtyp_ind_pi_absurd : forall {Γ p m X κ A B},
    Γ ⊢ apps (a_ind p m) X ⊆ Π{κ} A B -> False.
Proof.
  intros * H.
  assert (exists C, Γ ⊢ Π{κ} A B : C) as [C HC] by (gen_presups; eexists; eassumption).
  destruct (wf_pi_typed_large HC) as [k0 Hk0].
  apply (subtyp_spec_large (k := k0)) in H as [[k Heq] | [(U & V & [k1 HU] & [k2 HV] & Hs) | (κ1 & A1 & A2 & B1 & B2 & [k1 HA] & _)]];
    [| | | right; exact Hk0 ].
  - eapply exp_eq_ind_pi_absurd; exact Heq.
  - destruct (univ_sub_sort_term Hs) as [HUt _]; eapply exp_eq_ind_sort_absurd; [ exact HUt | exact HU ].
  - eapply exp_eq_ind_pi_absurd; exact HA.
Qed.

(** The argument of the constructor [s] of a closed term of a type of the
    shape of the natural numbers is of that type. *)
Lemma nat_succ_arg_typed : forall p D z s V, ind_lookup gc_deps gc_stack p = Some D -> nat_shape D = Some (z, s) ->
    ⋅ ⊢ nf_con p 0 s (cons V nil) : a_ind p 0 -> ⋅ ⊢ V : a_ind p 0.
Proof.
  intros * Hl Hs HT; destruct (nat_shape_inv _ _ _ Hs) as (Hnu & Hms).
  cbn [nf_to_exp List.map apps_exp] in HT.
  apply wf_app_inversion in HT as [κd κc A B Hf HV HBs].
  assert (HPi : exists C, ⋅ ⊢ a_pi κd κc A B : C) by (gen_presups; eexists; eassumption).
  destruct HPi as [C HPi].
  destruct κc.
  (** A constructor is no proof of a [∀]: its codomain is a proposition,
      below no inductive type *)
  2:{ exfalso; apply (subtyp_prop_ind_absurd (Ps := nil) HBs).
      assert (Hall : ⋅ ⊢ ∀ₚ{κd} A B : Propₘ) by (eapply prop_former_typed; [ exact HPi | eauto 7 ]).
      destruct (wf_all_inversion _ _ _ _ _ _ _ Hall) as [S HS HA HB _].
      change Propₘ with (Propₘ[Id,,nf_to_exp V]); mauto 3. }
  (** Nor a function between levels: its codomain is a type of levels,
      below no inductive type *)
  2:{ exfalso; apply (subtyp_level_ind_absurd (Ps := nil) HBs).
      destruct (wf_pi_inversion_at HPi) as [U HU HA HB Hk _]; cbn [abs_kind_sort exp_wk] in HB.
      change LevelSort with (LevelSort[Id,,nf_to_exp V]); mauto 3. }
  apply wf_con_inversion in Hf as [D' Mk gs Hl' Hk Hc Hsub].
  rewrite Hl in Hl'; injection Hl' as <-.
  destruct (Hms _ _ Hk) as [_ [Hdec Hnp Hcs]].
  unfold im_is_decl in Hdec; destruct (im_head Mk) eqn:Eh; [| discriminate | discriminate ].
  destruct (Hcs _ _ Hc) as [[_ ->] | [_ ->]].
  all: unfold con_ty, im_params, cargs_ctx, im_nn in Hsub; rewrite Hnu, Hnp in Hsub; cbn in Hsub.
  all: unfold ind_mty in Hsub; rewrite Hk in Hsub.
  all: unfold im_ty_at, im_ref, im_pre in Hsub; rewrite Eh in Hsub.
  all: unfold ind_uvars, vars_from, ind_nu in Hsub; rewrite Hnu in Hsub; cbn in Hsub.
  - (** [s] without arguments is no function. *)
    exfalso; exact (subtyp_ind_pi_absurd (X := nil) Hsub).
  - exact (subtyp_pi_dom_conv Hsub HV).
Qed.

Lemma nat_chain_of_read : forall p D z s, ind_lookup gc_deps gc_stack p = Some D -> nat_shape D = Some (z, s) ->
    forall W v, Rnf ⇓ (d_ind p 0 nil) v in gc_deps ⍮ gc_stack ⍮ 0 ↘ W -> nf_clean W -> ⋅ ⊢ W : a_ind p 0 -> nat_chain_nf p z s W.
Proof.
  intros p D z s Hl Hs W; remember (nf_succ_depth W) as k eqn:Ek; revert W Ek.
  induction k as [| k IH]; intros W Ek v Hr Hc HT.
  all: destruct (nat_read_step_of_read _ _ _ _ _ _ Hl Hs Hr) as [| v' V Hr' | M].
  all: try (exfalso; cbn in Hc, HT; eapply no_closed_neutral; eassumption).
  - constructor.
  - cbn in Ek; discriminate.
  - constructor.
  - constructor.
    cbn in Hc; destruct_conjs.
    unfold nf_succ_depth in Ek; cbn in Ek; injection Ek as Ek.
    exact (IH V Ek v' Hr' ltac:(assumption) (nat_succ_arg_typed p D z s V Hl Hs HT)).
Qed.

Lemma nat_chain_nf_numeral : forall p z s W, nat_chain_nf p z s W -> exists n, nf_to_exp W = nat_chain p z s n.
Proof. induction 1 as [| W _ [n IH]]; [ exists 0; reflexivity | exists (S n); cbn; rewrite IH; reflexivity ]. Qed.

(** A closed term of a type shaped as the natural numbers is a numeral:
    its normal form is the chain of constructors [nat_chain p z s n] a
    numeral stands for where the type is bound as the natural numbers. *)
Corollary canonical_form_of_ind_nat : forall {M p D z s},
    ind_lookup gc_deps gc_stack p = Some D -> nat_shape D = Some (z, s) ->
    ⋅ ⊢ M : a_ind p 0 ->
    exists W n, nbe_f ⋅ M (a_ind p 0) W /\ nat_chain_nf p z s W /\ nf_to_exp W = nat_chain p z s n.
Proof.
  intros * Hl Hs HM.
  destruct (soundness HM) as (W & Hn & HMW).
  pose proof (nbe_clean _ _ Htr _ _ _ _ Hn) as Hc.
  assert (HW : ⋅ ⊢ W : a_ind p 0) by (gen_presups; assumption).
  assert (Hch : nat_chain_nf p z s W).
  { inversion Hn as [? a Hi Ha Hnt]; subst.
    inversion Hi; subst; inversion Ha; subst.
    destruct Hnt as [Hp | m ? _ Hm Hr]; [ cbn in Hp; discriminate |].
    eapply nat_chain_of_read; eassumption. }
  destruct (nat_chain_nf_numeral _ _ _ _ Hch) as [n Hnum].
  exists W, n; auto.
Qed.

End Transparent_GCtx.

#[export]
Hint Resolve canonical_form_of_large_typ : mctt.

(** ** With the Global Context Explicit *)

(** The canonical forms of inductive types. *)
Corollary canonical_form_of_ind_gctx : forall Θ Ξ T γ M p k Ps,
    gc_transparent Θ Ξ ->
    @set_gctx_ok (gc_mk Θ Ξ) T γ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : apps (a_ind p k) Ps ->
    exists W, nbe Θ Ξ ⋅ M (apps (a_ind p k) Ps) W /\
      exists D Mk c gs Vs, ind_lookup Θ Ξ p = Some D /\ ind_member D k = Some Mk /\
        ind_con Mk c = Some gs /\ W = nf_con p k c Vs.
Proof. intros * Htr Hok HM; exact (@canonical_form_of_ind (gc_mk Θ Ξ) Htr T γ Hok M p k Ps HM). Qed.

Corollary canonical_form_of_ind_nat_gctx : forall Θ Ξ T γ M p D z s,
    gc_transparent Θ Ξ ->
    @set_gctx_ok (gc_mk Θ Ξ) T γ ->
    ind_lookup Θ Ξ p = Some D -> nat_shape D = Some (z, s) ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : a_ind p 0 ->
    exists W n, nbe Θ Ξ ⋅ M (a_ind p 0) W /\ nat_chain_nf p z s W /\ nf_to_exp W = nat_chain p z s n.
Proof. intros * Htr Hok Hl Hs HM; exact (@canonical_form_of_ind_nat (gc_mk Θ Ξ) Htr T γ Hok M p D z s Hl Hs HM). Qed.

Corollary canonical_form_of_typ_gctx : forall Θ Ξ T γ U M,
    gc_transparent Θ Ξ ->
    @set_gctx_ok (gc_mk Θ Ξ) T γ ->
    univ_term U ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : U ->
    exists u W, nbe_ty Θ Ξ ⋅ U (universe_nf_to_nf u) /\ nbe Θ Ξ ⋅ M U W /\ typ_nf_below u W.
Proof. intros * Htr Hok HT HM; exact (@canonical_form_of_typ (gc_mk Θ Ξ) Htr T γ Hok U M HT HM). Qed.

Corollary canonical_form_of_large_typ_gctx : forall Θ Ξ T γ i M,
    gc_transparent Θ Ξ ->
    @set_gctx_ok (gc_mk Θ Ξ) T γ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Typeω@i ->
    exists W, nbe Θ Ξ ⋅ M Typeω@i W /\ is_typ_constr W /\ (forall κ V, W <> ⇑ⁿ{κ} V).
Proof. intros * Htr Hok HM; exact (@canonical_form_of_large_typ (gc_mk Θ Ξ) Htr T γ Hok i M HM). Qed.

Corollary canonical_form_of_typ_lit_gctx : forall Θ Ξ T γ n M,
    gc_transparent Θ Ξ ->
    @set_gctx_ok (gc_mk Θ Ξ) T γ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Type@n ->
    exists W, nbe Θ Ξ ⋅ M Type@n W /\ small_typ_nf n W.
Proof. intros * Htr Hok HM; exact (@canonical_form_of_typ_lit (gc_mk Θ Ξ) Htr T γ Hok n M HM). Qed.

(** The consistency theorems. *)
Corollary consistency_gctx : forall Θ Ξ T γ U M,
    @set_gctx_ok (gc_mk Θ Ξ) T γ ->
    univ_term U ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π{ak_relevant} U #0).
Proof. intros * Hok; exact (@consistency (gc_mk Θ Ξ) T γ Hok U M). Qed.

Corollary consistency_large_gctx : forall Θ Ξ T γ i M,
    @set_gctx_ok (gc_mk Θ Ξ) T γ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π{ak_relevant} Typeω@i #0).
Proof. intros * Hok; exact (@consistency_large (gc_mk Θ Ξ) T γ Hok i M). Qed.

Corollary consistency_lit_gctx : forall Θ Ξ T γ n M,
    @set_gctx_ok (gc_mk Θ Ξ) T γ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Π{ak_relevant} Type@n #0).
Proof. intros * Hok; exact (@consistency_lit (gc_mk Θ Ξ) T γ Hok n M). Qed.

Corollary consistency_False_gctx : forall Θ Ξ T γ M,
    @set_gctx_ok (gc_mk Θ Ξ) T γ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : ⊥).
Proof. intros * Hok; exact (@consistency_False (gc_mk Θ Ξ) T γ Hok M). Qed.

(** ** Opaque Definitions

    With [abstract] definitions allowed, a closed normal form of a type
    shaped as the natural numbers can be stuck: an opaque global applied to
    arguments, as [c] is in [abstract c : Nat := 3].  At a global context
    without axioms, every closed normal form of such a type is a chain of
    its constructors, or one wrapped around a neutral headed by an opaque
    definition with a body, and after unsealing every definition
    ([unseal_exp], [gc_no_axioms_unseal_transparent]) the term computes to
    a chain, equal in the unsealed context to the sealed normal form
    ([canonical_form_of_ind_nat_no_axioms]).  The model is one of the
    unsealed context. *)

(** The global at the head of a neutral, if any.  An ex falso has none:
    no closed one is typed where a model exists ([consistency_False]). *)
Fixpoint ne_head (W : ne) : option qname :=
  match W with
  | ne_elim _ _ _ _ W | ne_app W _ | ne_proj _ W => ne_head W
  | ne_absurd _ _ | ne_var _ => None
  | ne_glob p => Some p
  end.

(** In the empty context of a global context whose unsealing is modelled,
    a neutral is headed by a global: a variable has no type there, and an
    ex falso would need a closed proof of [⊥], which unsealed would be one
    in the model ([consistency_False_gctx]). *)
Local Lemma no_closed_neutral_head : forall {Θ Ξ T γ A} {W : ne},
    @set_gctx_ok (gc_mk (gds_unseal Θ) (gs_unseal Ξ)) T γ ->
    ne_head W = None ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ W : A).
Proof.
  intros * Hok HWc HW.
  dependent induction HW; try (destruct W; simpl in *; congruence);
    try solve [ eauto ].
  all: destruct W; simpl in *; try congruence; autoinjections; destruct_all;
    try contradiction; eauto.
  all: try solve [ match_by_head ctx_lookup ltac:(fun H => inversion H) ].
  all: try solve [ match goal with H : _ ⍮ _ ⍮ ⋅ ⊢ ?M : ⊥ |- _ =>
                     exact (consistency_False_gctx _ _ _ _ _ Hok (unseal_exp _ _ _ _ _ H)) end ].
Qed.

(** In the empty context of a global context whose unsealing is modelled,
    a neutral has a head global. *)
Local Lemma closed_neutral_head : forall {Θ Ξ T γ A} {W : ne},
    @set_gctx_ok (gc_mk (gds_unseal Θ) (gs_unseal Ξ)) T γ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ W : A ->
    exists p, ne_head W = Some p.
Proof.
  intros * Hok HW; destruct (ne_head W) as [p |] eqn:Hh; [ eauto |].
  exfalso; exact (no_closed_neutral_head Hok Hh HW).
Qed.

(** A chain of the constructors [z] and [s] of [p], possibly around a
    neutral whose globals satisfy [G], headed by one. *)
Inductive nat_chain_stuck (G : qname -> Prop) (p : qname) (z s : String.string) : nf -> Prop :=
(** The constructor [z] *)
| nat_chain_stuck_zero : nat_chain_stuck G p z s (nf_con p 0 z nil)
(** The constructor [s] at a chain *)
| nat_chain_stuck_succ : forall W, nat_chain_stuck G p z s W -> nat_chain_stuck G p z s (nf_con p 0 s (cons W nil))
(** A neutral headed by a global, its globals satisfying [G] *)
| nat_chain_stuck_neut : forall κ W h, ne_head W = Some h -> ne_stuck G W -> nat_chain_stuck G p z s ⇑ⁿ{κ} W.
#[export]
Hint Constructors nat_chain_stuck : mctt.

(** A global that is an opaque definition with a body. *)
Definition global_opaque (Θ : gdeps) (Ξ : gstack) (p : qname) : Prop :=
  exists pv r A M, gc_resolve Θ Ξ p = Some (ge_def false pv r A (Some M)).

Lemma global_stuck_opaque : forall Θ Ξ p, gc_no_axioms Θ Ξ -> global_stuck Θ Ξ p -> global_opaque Θ Ξ p.
Proof.
  intros * Hna [b pv r A B Hr Hb].
  pose proof (gc_no_axioms_resolve _ _ _ _ _ _ _ _ Hna Hr) as HB.
  destruct B as [M |]; [| congruence ].
  destruct Hb as [-> | ?]; [| discriminate ].
  unfold global_opaque; eauto.
Qed.

Lemma nf_ne_stuck_mono : forall (G G' : qname -> Prop), (forall p, G p -> G' p) ->
    (forall W, nf_stuck G W -> nf_stuck G' W) /\ (forall W, ne_stuck G W -> ne_stuck G' W).
Proof.
  intros G G' HG; apply nf_ne_ind; intros; cbn [nf_stuck ne_stuck] in *; intuition auto;
    repeat match goal with H : _ /\ _ |- _ => destruct H end; try split; auto.
  (** The lists, element by element; a block by its scrutinee's type, its
      motive and its branches. *)
  all: eapply list_all_all_list_impl; [ eassumption | eassumption |]; cbn; intros x Hx Hy.
  all: try solve [ auto ].
  all: try solve [ destruct Hx; cbn in *; auto ].
  destruct Hx as [n' Z HZ A HA brs Hbrs]; cbn in *; destruct Hy as [HyZ [HyA Hybrs]]; split; [ auto | split; [ auto |] ];
    eapply list_all_all_list_impl; [ exact Hbrs | exact Hybrs |];
    intros br Hbr Hy'; destruct Hbr; cbn in *; auto.
Qed.

Lemma nf_stuck_mono : forall (G G' : qname -> Prop), (forall p, G p -> G' p) ->
    forall W, nf_stuck G W -> nf_stuck G' W.
Proof. intros * HG; apply (nf_ne_stuck_mono _ _ HG). Qed.

Lemma ne_stuck_mono : forall (G G' : qname -> Prop), (forall p, G p -> G' p) ->
    forall W, ne_stuck G W -> ne_stuck G' W.
Proof. intros * HG; apply (nf_ne_stuck_mono _ _ HG). Qed.

Lemma nat_chain_stuck_mono : forall (G G' : qname -> Prop), (forall p, G p -> G' p) ->
    forall p z s W, nat_chain_stuck G p z s W -> nat_chain_stuck G' p z s W.
Proof.
  intros * HG; induction 1; econstructor; eauto using ne_stuck_mono.
Qed.

(** The stuck normal forms of closed terms at a global context, which may
    have opaque definitions, whose unsealing is modelled: the steps of the
    theorems below. *)
Section Stuck_GCtx.
  Context {GC : GCtx}.
  (** The tower of universes of the model *)
  Variable T : universe_tower.
  (** The valuation of the globals *)
  Variable γ : global_valuation.
  (** It models the unsealed global context *)
  Hypothesis Hok : @set_gctx_ok (gc_mk (gds_unseal gc_deps) (gs_unseal gc_stack)) T γ.

(** The normal forms of a closed term of a type shaped as the natural
    numbers: a chain of its constructors, possibly around a neutral headed
    by a stuck global. *)
Local Lemma nat_chain_stuck_of_read : forall G p D z s, ind_lookup gc_deps gc_stack p = Some D -> nat_shape D = Some (z, s) ->
    forall W v, Rnf ⇓ (d_ind p 0 nil) v in gc_deps ⍮ gc_stack ⍮ 0 ↘ W -> nf_stuck G W -> ⋅ ⊢ W : a_ind p 0 ->
      nat_chain_stuck G p z s W.
Proof.
  intros G p D z s Hl Hs W; remember (nf_succ_depth W) as k eqn:Ek; revert W Ek.
  induction k as [| k IH]; intros W Ek v Hr Hc HT.
  all: destruct (nat_read_step_of_read _ _ _ _ _ _ Hl Hs Hr) as [| v' V Hr' | M].
  all: try (cbn in Hc, HT; destruct (closed_neutral_head Hok HT) as [h Hh]; eapply nat_chain_stuck_neut; eassumption).
  - constructor.
  - cbn in Ek; discriminate.
  - constructor.
  - constructor.
    cbn in Hc; destruct_conjs.
    unfold nf_succ_depth in Ek; cbn in Ek; injection Ek as Ek.
    exact (IH V Ek v' Hr' ltac:(assumption) (nat_succ_arg_typed p D z s V Hl Hs HT)).
Qed.

(** A closed term of a type shaped as the natural numbers: its normal form
    is a chain of the type's constructors, possibly around a neutral headed
    by a global that does not unfold. *)
Local Lemma canonical_form_of_ind_nat_stuck : forall {M p D z s},
    ind_lookup gc_deps gc_stack p = Some D -> nat_shape D = Some (z, s) ->
    ⋅ ⊢ M : a_ind p 0 ->
    exists W, nbe_f ⋅ M (a_ind p 0) W /\ nat_chain_stuck (global_stuck gc_deps gc_stack) p z s W.
Proof.
  intros * Hl Hs HM.
  destruct (soundness HM) as (W & Hn & HMW).
  pose proof (nbe_stuck _ _ _ _ _ _ Hn) as Hc.
  assert (HW : ⋅ ⊢ W : a_ind p 0) by (gen_presups; assumption).
  exists W; split; [ exact Hn |].
  inversion Hn as [? a Hi Ha Hnt]; subst.
  inversion Hi; subst; inversion Ha; subst.
  destruct Hnt as [Hp | m ? _ Hm Hr]; [ cbn in Hp; discriminate |].
  eapply nat_chain_stuck_of_read; eassumption.
Qed.

(** Canonicity at a universe: the normal form is of the shape
    [typ_nf_below u], or a neutral headed by a stuck global. *)
Local Lemma canonical_form_of_typ_stuck : forall {U M},
    univ_term U ->
    ⋅ ⊢ M : U ->
    exists u W, nbe_ty_f ⋅ U (universe_nf_to_nf u) /\ nbe_f ⋅ M U W /\ nf_stuck (global_stuck gc_deps gc_stack) W /\
      (typ_nf_below u W \/ (exists κ V p, W = ⇑ⁿ{κ} V /\ ne_head V = Some p)).
Proof.
  intros * HT HM.
  destruct (soundness HM) as (W & Hn & HMW).
  destruct (univ_term_typed_large HT HM) as [k Hk].
  destruct (soundness_ty Hk) as (Ut & HU & _).
  destruct (nbe_ty_univ_term HT HU) as [u ->].
  exists u, W; split; [ exact HU | split; [ exact Hn | split; [ exact (nbe_stuck _ _ _ _ _ _ Hn) |] ] ].
  assert (Hd : (exists κ V, W = ⇑ⁿ{κ} V) \/ (forall κ V, W <> ⇑ⁿ{κ} V))
    by (destruct W; try (right; intros ? ? Heq; discriminate Heq); left; do 2 eexists; reflexivity).
  destruct Hd as [(κ & V & ->) | Hne].
  - right; assert (HV : ⋅ ⊢ V : U) by (gen_presups; assumption).
    destruct (closed_neutral_head Hok HV) as [p Hp]; eauto.
  - left; eapply typ_nf_below_of_nbe; eassumption.
Qed.

End Stuck_GCtx.

(** *** Without Axioms, Opaque Definitions Included *)

(** The sealed normal form of a closed term of a type shaped as the natural
    numbers is a chain of its constructors around a neutral headed by an
    opaque definition; unsealed, the term computes to a numeral's chain,
    which is equal to the sealed normal form once the definitions unfold. *)
Theorem canonical_form_of_ind_nat_no_axioms : forall Θ Ξ T γ M p D z s,
    gc_no_axioms Θ Ξ ->
    @set_gctx_ok (gc_mk (gds_unseal Θ) (gs_unseal Ξ)) T γ ->
    ind_lookup Θ Ξ p = Some D -> nat_shape D = Some (z, s) ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : a_ind p 0 ->
    exists W, nbe Θ Ξ ⋅ M (a_ind p 0) W /\ nat_chain_stuck (global_opaque Θ Ξ) p z s W /\
      exists V n, nbe (gds_unseal Θ) (gs_unseal Ξ) ⋅ M (a_ind p 0) V /\ nat_chain_nf p z s V /\
        nf_to_exp V = nat_chain p z s n /\
        gds_unseal Θ ⍮ gs_unseal Ξ ⍮ ⋅ ⊢ W ≈ V : a_ind p 0.
Proof.
  intros * Hna Hok Hl Hs HM.
  pose proof (gc_no_axioms_unseal_transparent _ _ Hna) as Htr.
  pose proof (unseal_exp _ _ _ _ _ HM) as HM'.
  destruct (@canonical_form_of_ind_nat_stuck (gc_mk Θ Ξ) T γ Hok _ _ _ _ _ Hl Hs HM) as (W & HW & Hc).
  assert (Hl' : ind_lookup (gds_unseal Θ) (gs_unseal Ξ) p = Some D) by (rewrite ind_lookup_unseal; exact Hl).
  destruct (canonical_form_of_ind_nat_gctx _ _ _ _ _ _ _ _ _ Htr Hok Hl' Hs HM') as (V & n & HV & HcV & Hn).
  exists W; split; [ exact HW | split ].
  - eapply nat_chain_stuck_mono; [| exact Hc ]; intros; apply global_stuck_opaque; assumption.
  - exists V, n; repeat split; [ exact HV | exact HcV | exact Hn |].
    pose proof (unseal_exp_eq _ _ _ _ _ _ (soundness' HM HW)).
    pose proof (soundness' HM' HV).
    etransitivity; [ symmetry |]; eassumption.
Qed.

(** At a universe term [U]: sealed, the normal form is of the shape
    [typ_nf_below u] or a neutral headed by an opaque definition; unsealed,
    it is of the shape [typ_nf_below u'], where [u] and [u'] are the normal
    forms of [U] sealed and unsealed; and the two normal forms are equal once
    the definitions unfold. *)
Theorem canonical_form_of_typ_no_axioms : forall Θ Ξ T γ U M,
    gc_no_axioms Θ Ξ ->
    @set_gctx_ok (gc_mk (gds_unseal Θ) (gs_unseal Ξ)) T γ ->
    univ_term U ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : U ->
    exists u W, nbe_ty Θ Ξ ⋅ U (universe_nf_to_nf u) /\ nbe Θ Ξ ⋅ M U W /\ nf_stuck (global_opaque Θ Ξ) W /\
      (typ_nf_below u W \/ (exists κ V p, W = ⇑ⁿ{κ} V /\ ne_head V = Some p)) /\
      exists u' V, nbe_ty (gds_unseal Θ) (gs_unseal Ξ) ⋅ U (universe_nf_to_nf u') /\
        nbe (gds_unseal Θ) (gs_unseal Ξ) ⋅ M U V /\ typ_nf_below u' V /\
        gds_unseal Θ ⍮ gs_unseal Ξ ⍮ ⋅ ⊢ W ≈ V : U.
Proof.
  intros * Hna Hok HT HM.
  pose proof (gc_no_axioms_unseal_transparent _ _ Hna) as Htr.
  pose proof (unseal_exp _ _ _ _ _ HM) as HM'.
  destruct (@canonical_form_of_typ_stuck (gc_mk Θ Ξ) T γ Hok _ _ HT HM) as (u & W & Hu & HW & Hs & Hc).
  destruct (canonical_form_of_typ_gctx _ _ _ _ _ _ Htr Hok HT HM') as (u' & V & Hu' & HV & HcV).
  exists u, W; split; [ exact Hu | split; [ exact HW | split; [| split; [ exact Hc |] ] ] ].
  - apply (nf_stuck_mono (global_stuck Θ Ξ)); [ intros; apply global_stuck_opaque; assumption | exact Hs ].
  - exists u', V; split; [ exact Hu' | split; [ exact HV | split; [ exact HcV |] ] ].
    pose proof (unseal_exp_eq _ _ _ _ _ _ (soundness' HM HW)).
    pose proof (soundness' HM' HV).
    etransitivity; [ symmetry |]; eassumption.
Qed.

Corollary canonical_form_of_large_typ_no_axioms : forall Θ Ξ T γ i M,
    gc_no_axioms Θ Ξ ->
    @set_gctx_ok (gc_mk (gds_unseal Θ) (gs_unseal Ξ)) T γ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Typeω@i ->
    exists W, nbe Θ Ξ ⋅ M Typeω@i W /\ nf_stuck (global_opaque Θ Ξ) W /\
      ((is_typ_constr W /\ (forall κ V, W <> ⇑ⁿ{κ} V)) \/ (exists κ V p, W = ⇑ⁿ{κ} V /\ ne_head V = Some p)) /\
      exists V, nbe (gds_unseal Θ) (gs_unseal Ξ) ⋅ M Typeω@i V /\ is_typ_constr V /\ (forall κ V', V <> ⇑ⁿ{κ} V') /\
        gds_unseal Θ ⍮ gs_unseal Ξ ⍮ ⋅ ⊢ W ≈ V : Typeω@i.
Proof.
  intros * Hna Hok HM.
  destruct (canonical_form_of_typ_no_axioms _ _ _ _ _ _ Hna Hok (univ_term_typ i) HM)
    as (u & W & Hu & HW & Hs & Hc & u' & V & Hu' & HV & HcV & HWV).
  apply (@nbe_ty_typ_univ_nf (gc_mk Θ Ξ)) in Hu as ->.
  apply (@nbe_ty_typ_univ_nf (gc_mk (gds_unseal Θ) (gs_unseal Ξ))) in Hu' as ->.
  exists W; split; [ exact HW | split; [ exact Hs | split ] ].
  - destruct Hc as [Hb | Hneu]; [ left; exact (typ_nf_below_large _ _ Hb) | right; exact Hneu ].
  - destruct (typ_nf_below_large _ _ HcV) as [HcV' HnV].
    exists V; split; [ exact HV | split; [ exact HcV' | split; [ exact HnV | exact HWV ] ] ].
Qed.

Corollary canonical_form_of_typ_lit_no_axioms : forall Θ Ξ T γ n M,
    gc_no_axioms Θ Ξ ->
    @set_gctx_ok (gc_mk (gds_unseal Θ) (gs_unseal Ξ)) T γ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : Type@n ->
    exists W, nbe Θ Ξ ⋅ M Type@n W /\ nf_stuck (global_opaque Θ Ξ) W /\
      (small_typ_nf n W \/ (exists κ V p, W = ⇑ⁿ{κ} V /\ ne_head V = Some p)) /\
      exists V, nbe (gds_unseal Θ) (gs_unseal Ξ) ⋅ M Type@n V /\ small_typ_nf n V /\
        gds_unseal Θ ⍮ gs_unseal Ξ ⍮ ⋅ ⊢ W ≈ V : Type@n.
Proof.
  intros * Hna Hok HM.
  destruct (canonical_form_of_typ_no_axioms _ _ _ _ _ _ Hna Hok (univ_term_suniv _) HM)
    as (u & W & Hu & HW & Hs & Hc & u' & V & Hu' & HV & HcV & HWV).
  apply (@nbe_ty_lit_univ_nf (gc_mk Θ Ξ)) in Hu as ->.
  apply (@nbe_ty_lit_univ_nf (gc_mk (gds_unseal Θ) (gs_unseal Ξ))) in Hu' as ->.
  exists W; split; [ exact HW | split; [ exact Hs | split ] ].
  - destruct Hc as [Hb | Hneu]; [ left; exact (typ_nf_below_lit _ _ Hb) | right; exact Hneu ].
  - exists V; split; [ exact HV | split; [ exact (typ_nf_below_lit _ _ HcV) | exact HWV ] ].
Qed.

(** *** Every Program

    A run of commands that declare no axiom, loading units that declare
    none, files no axiom ([run_no_axioms]), so the theorems above hold at
    what such a program files, where its unsealing is modelled. *)

Section Programs.
  Variables (load_path : path -> option String.string) (read : String.string -> option Cst.prog)
            (to_core : Cst.prog -> option surface_compilation_unit).
  Hypothesis Hload : forall prg u, to_core prg = Some u -> unit_no_axioms u.

(** No closed proof of [⊥] at a global context a run of commands reaches,
    where its unsealing is modelled: unsealed, a proof would be one in
    the model ([consistency_False_gctx]). *)
Corollary consistency_False_run : forall ch B Rb cs B' Rb' Θ Ξ T γ M,
    Mctt.Core.Syntactic.System.Command.run_cmds load_path read to_core ch B Rb nil nil cs B' Rb' Θ Ξ ->
    items_no_axioms cs ->
    @set_gctx_ok (gc_mk (gds_unseal Θ) (gs_unseal Ξ)) T γ ->
    ~ (Θ ⍮ Ξ ⍮ ⋅ ⊢ M : ⊥).
Proof. intros * _ _ Hok HM; exact (consistency_False_gctx _ _ _ _ _ Hok (unseal_exp _ _ _ _ _ HM)). Qed.

(** No closed proof of [⊥] at what a program files, where its unsealing
    is modelled. *)
Corollary consistency_False_prog : forall prg B Θ U T γ M,
    Mctt.Core.Syntactic.System.Command.prog_sem load_path read to_core prg B Θ U ->
    let Θ' := ((prog_path prg, U) :: Θ) in
    @set_gctx_ok (gc_mk (gds_unseal Θ') nil) T γ ->
    ~ (Θ' ⍮ nil ⍮ ⋅ ⊢ M : ⊥).
Proof. intros * _ Θ' Hok HM; exact (consistency_False_gctx _ _ _ _ _ Hok (unseal_exp _ _ _ _ _ HM)). Qed.

(** A program's bound natural numbers: the type a program binds as the
    natural numbers is read at its end ([prog_sem_builtins_wf]), and a
    closed term of it computes, once its definitions unfold, to the chain
    of constructors a numeral stands for ([nat_chain]). *)
Corollary canonical_form_of_bound_nat_prog : forall prg B Θ U T γ M p,
    Mctt.Core.Syntactic.System.Command.prog_sem load_path read to_core prg B Θ U ->
    let Θ' := ((prog_path prg, U) :: Θ) in
    @set_gctx_ok (gc_mk (gds_unseal Θ') nil) T γ ->
    builtins_nat B = Some p ->
    Θ' ⍮ nil ⍮ ⋅ ⊢ M : a_ind p 0 ->
    exists z s V n, nat_view Θ' nil B = Some (p, z, s) /\
      nbe (gds_unseal Θ') nil ⋅ M (a_ind p 0) V /\ nf_to_exp V = nat_chain p z s n.
Proof.
  intros * Hp Θ' Hok Hb HM.
  pose proof (prog_sem_no_axioms _ _ _ Hload _ _ _ _ Hp) as Hna.
  pose proof (Mctt.Core.Syntactic.System.Command.prog_sem_builtins_wf _ _ _ _ _ _ _ Hp) as Hw.
  destruct (Hw _ Hb) as [D z s Hl Hs _].
  exists z, s.
  destruct (canonical_form_of_ind_nat_no_axioms _ _ _ _ _ _ _ _ _ Hna Hok Hl Hs HM) as (_ & _ & _ & V & n & HV & _ & Hn & _).
  exists V, n; split; [ unfold nat_view, Θ'; rewrite Hb, Hl, Hs; reflexivity | split; assumption ].
Qed.

End Programs.
