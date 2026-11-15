(** * Inversions of Conversion and Subtyping

    What completeness and soundness of NbE give together: the inversions
    of conversion and subtyping that normal forms decide (of [Π], of the
    universes and levels, of inductive and record types), and the
    canonical form of closed terms of [Π] ([canonical_form_of_pi]).  The
    normal forms of the types of a universe are in
    [UniverseNormalForms.v]; the consistency of the core and the canonical
    forms that rest on it, read off the set model, are in
    [Consistency.v]. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core Require Export Soundness.
From Mctt.Core.Completeness.Consequences Require Export RigidTypes.
From Mctt.Core.Semantic Require Export Transparency Stuck.
From Mctt.Core.Syntactic Require Export Unseal.
From Mctt.Core.Syntactic Require Import CoreInversions.
From Mctt.Core.Syntactic.Levels Require Import LevelEq.
From Mctt.Core.Semantic Require Import Realizability Levels.
From Mctt.Core.Completeness.LogicalRelation Require Import Lemmas.
From Mctt.Core.Completeness Require Import LogicalRelation.Universes LogicalRelation.Contexts LogicalRelation.Functions.
From Mctt.Core.Completeness.Consequences Require Import ContextEquality.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Cong.
Require Import Mctt.Core.Syntactic.Command.
From Mctt.Core.Syntactic Require Import Builtin NfRename.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.
#[local] Open Scope list_scope.


Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The normal form of a type is its own normal form, up to its proofs: a
    proof is read back over the environment it is kept over, so
    normalizing a normal form again binds its positions once more.  For
    [Γ = (P : Prop) ▹ (F : P → Type@0) ▹ (h : P)] and [A = F h], the
    normal form [B] of [A] has the proof [h] as a let over its position,
    and the normal form of [B] binds that let's free position again.  The
    exact form [B = C] is believed false for that reason, not proved
    false. *)
Lemma idempotent_nbe_ty : forall {Γ i A B C},
    Γ ⊢ A : Typeω@i ->
    nbe_ty_f Γ A B ->
    nbe_ty_f Γ B C ->
    nf_eq_upto_proofs B C.
Proof.
  intros.
  assert (Γ ⊢ A ≈ B : Typeω@i) as (? & ? & ? & ? & ?)%completeness_ty by mauto 2 using soundness_ty'.
  functional_nbe_rewrite_clear.
  assumption.
Qed.
Hint Resolve idempotent_nbe_ty : mctt.

(** ** Types at Their Sorts

    A type of a large universe is no proposition ([subtyp_same_kind]),
    so equations of types at sorts ([type_sort]) compose, and a context
    extended by equal types refines either extension. *)
Lemma typ_prop_absurd : forall {Γ A i},
    Γ ⊢ A : Typeω@i -> Γ ⊢ A : Propₘ -> False.
Proof.
  intros * Hi Hp.
  assert (Hs : Γ ⊢ A ⊆ A) by (eapply wf_subtyp_refl; [ exact Hp | constructor | mauto 3 ]).
  discriminate (subtyp_same_kind Γ A A ak_relevant ak_propositional i i Hs Hi Hp).
Qed.

(** The sort of a sort's types is at the sort's kind ([sort_exp_kind]). *)
Lemma sort_kind_sort_exp_kind : forall S, type_sort S -> sort_kind S (sort_exp_kind S).
Proof. intros * []; constructor. Qed.

(** The kind of the sort at a kind is that kind. *)
Lemma sort_exp_kind_abs_kind_sort : forall κ (i : nat), sort_exp_kind (abs_kind_sort κ Typeω@i) = κ.
Proof. intros []; reflexivity. Qed.

(** The value at an environment of a type of a sort is of the sort's
    kind. *)
Lemma rel_value_kind_of_sort : forall {Γ X T R ρ ρ' x}, type_sort T -> Γ ⊨ X : T ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> R ρ ρ' -> ⟦ X ⟧ ρ ↘ x -> domain_kind x = sort_exp_kind T.
Proof.
  intros * HT HX HR Hρ Hx.
  destruct (rel_type_kind_of_sort_kind (sort_kind_sort_exp_kind _ HT) HX _ HR _ _ Hρ) as (x' & Hx' & Hk).
  pose proof (functional_eval_exp _ _ _ _ Hx' Hx) as <-; exact Hk.
Qed.

(** The normal form of a type of a sort gives its elements the sort's
    kind ([nf_type_kind]): its value at the initial environment is of that
    kind ([rel_value_kind_of_sort]), and readback keeps the kind of a
    value ([read_typ_kind]). *)
Lemma nbe_ty_kind_of_sort : forall {Γ A S W}, type_sort S -> Γ ⊢ A : S -> nbe_ty_f Γ A W ->
    nf_type_kind W = sort_exp_kind S.
Proof.
  intros * HS HA [ρ a Hi Ha Hr].
  pose proof (completeness_fundamental_exp _ _ _ HA) as HAs.
  pose proof HAs as [R HR _ _].
  pose proof (wf_ctx_scoped_exp HA) as HsΓ.
  destruct (per_ctx_then_per_env_initial_env HR HsΓ HsΓ) as (ρ0 & ρ0' & Hi0 & _ & Hρ).
  pose proof (functional_initial_env _ _ Hi0 _ Hi) as ->.
  rewrite (read_typ_kind _ _ _ Hr).
  exact (rel_value_kind_of_sort HS HAs HR Hρ Ha).
Qed.

(** A type of levels is of no large universe: at the initial environment
    its value is an element of [LevelSort], a type of levels
    ([per_level_sort]), and an element of the universe, no type of levels
    ([rel_exp_of_typ_nonlevel_at]).  For example
    [⋅ ⊢ Level@0 : Type@0] fails. *)
Lemma level_type_not_large : forall {Γ A k}, Γ ⊢ A : LevelSort -> Γ ⊢ A : Typeω@k -> False.
Proof.
  intros * HL HT.
  pose proof (completeness_fundamental_exp _ _ _ HT) as HTs.
  pose proof HTs as [R HR _ _].
  pose proof (wf_ctx_scoped_exp HT) as HsΓ.
  destruct (per_ctx_then_per_env_initial_env HR HsΓ HsΓ) as (ρ & ρ' & _ & _ & Hρ).
  destruct (rel_exp_of_level_sort_inversion_simple_at HR (completeness_fundamental_exp _ _ _ HL) _ _ Hρ)
    as (a & a' & Ha & _ & (Hl & _)).
  exact (rel_exp_of_typ_nonlevel_at HR HTs _ _ Hρ _ Ha Hl).
Qed.

(** A type of levels is no proposition: its value is of the kind of
    levels, and a proposition's is propositional. *)
Lemma level_type_not_prop : forall {Γ A}, Γ ⊢ A : LevelSort -> Γ ⊢ A : Propₘ -> False.
Proof.
  intros * HL HP.
  pose proof (completeness_fundamental_exp _ _ _ HP) as HPs.
  pose proof HPs as [R HR _ _].
  pose proof (wf_ctx_scoped_exp HP) as HsΓ.
  destruct (per_ctx_then_per_env_initial_env HR HsΓ HsΓ) as (ρ & ρ' & _ & _ & Hρ).
  destruct (rel_type_kind_of_sort_kind sort_kind_prop HPs _ HR _ _ Hρ) as (a & Ha & Hk).
  pose proof (rel_value_kind_of_sort type_sort_level (completeness_fundamental_exp _ _ _ HL) HR Hρ Ha) as Hk'.
  cbn [sort_exp_kind] in Hk'; congruence.
Qed.

(** Subtyping relates types of sorts of one kind ([sort_exp_kind]), as
    [subtyp_same_kind] for the sorts at a kind.  So no type of levels is
    below a proposition, nor a proposition below a type of levels. *)
Lemma subtyp_type_sort_kind : forall {Γ A A' S S'},
    Γ ⊢ A ⊆ A' -> type_sort S -> type_sort S' -> Γ ⊢ A : S -> Γ ⊢ A' : S' ->
    sort_exp_kind S = sort_exp_kind S'.
Proof.
  intros * Hs HS HS' HA HA'.
  pose proof (completeness_fundamental_subtyp _ _ _ Hs) as [R HR k Hsub].
  pose proof (completeness_fundamental_exp _ _ _ HA) as HAs.
  pose proof (completeness_fundamental_exp _ _ _ HA') as HA's.
  pose proof (wf_ctx_scoped_exp HA) as HsΓ.
  pose proof (per_ctx_then_per_env_initial_env HR HsΓ HsΓ) as [ρ [ρ' [_ [_ Hρ]]]].
  assert (HPR : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρρ : R ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  destruct (eval_sub_id_rel HR Hρρ) as [Hid Hid'].
  destruct (Hsub _ _ HR _ _ (rel_sub_id (ex_intro _ _ HR)) _ _ _ _ Hρρ Hid Hid')
    as [aσ a0 a'σ' a0' Ha _ Ha' _ [Rl Hll] [Rr Hrr] Hsa].
  rewrite exp_sub_id in Ha, Ha'.
  pose proof (eq_trans (per_univ_elem_kind _ _ _ _ Hll)
                (eq_trans (per_subtyp_kind _ _ _ Hsa) (eq_sym (per_univ_elem_kind _ _ _ _ Hrr)))) as Hr.
  rewrite <- (rel_value_kind_of_sort HS HAs HR Hρρ Ha), <- (rel_value_kind_of_sort HS' HA's HR Hρρ Ha'); exact Hr.
Qed.

(** A subtyping read at the initial environment of its context: the two
    values are in the semantic subtyping ([per_subtyp]).  The semantic
    judgment is read at the identity, whose value is the initial
    environment retagged, and moved back along the types' relatedness
    ([per_subtyp_transp]). *)
Lemma subtyp_at_initial_env : forall {Γ A A'},
    Γ ⊢ A ⊆ A' ->
    exists ρ a a' k, initial_env_f Γ ρ /\ ⟦ A ⟧ ρ ↘ a /\ ⟦ A' ⟧ ρ ↘ a' /\ Sub a <: a' at k.
Proof.
  intros * Hs.
  pose proof (completeness_fundamental_subtyp _ _ _ Hs) as [R HR k Hsub].
  pose proof (proj1 (proj1 (proj1 (proj2 (proj2 (proj2 wf_scoped))) _ _ _ _ _ Hs))) as HsΓ.
  pose proof (per_ctx_then_per_env_initial_env HR HsΓ HsΓ) as [ρ [ρ' [Hρ [_ Hρρ]]]].
  assert (HPR : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρ1 : R ρ ρ) by (etransitivity; [ exact Hρρ | symmetry; exact Hρρ ]).
  destruct (eval_sub_id_rel HR Hρ1) as [Hid Hid'].
  destruct (Hsub _ _ HR _ _ (rel_sub_id (ex_intro _ _ HR)) _ _ _ _ Hρ1 Hid Hid')
    as [aσ a0 a'σ' a0' Ha Ha0 Ha' Ha0' [R1 HR1] [R2 HR2] Hsa].
  rewrite exp_sub_id in Ha, Ha'.
  exists ρ, aσ, a'σ', k; repeat split; [ exact Hρ | exact Ha | exact Ha' |].
  eapply per_subtyp_transp; [ exact Hsa | symmetry; exact HR1 | symmetry; exact HR2 ].
Qed.

(** NbE at [Prop] reads a proposition back as a type. *)
Lemma nbe_prop_to_nbe_ty : forall {Γ T W}, nbe_f Γ T Propₘ W -> nbe_ty_f Γ T W.
Proof.
  intros * [ρ a Hi Ha Hw]; inversion Ha; subst.
  destruct Hw as [Hp | m w Hr Hm Hw]; [ cbn in Hp; discriminate |].
  inversion Hw; subst; try (cbn in *; discriminate).
  econstructor; eassumption.
Qed.

(** NbE at [LevelSort] reads a type of levels back as a type. *)
Lemma nbe_level_sort_to_nbe_ty : forall {Γ T W}, nbe_f Γ T LevelSort W -> nbe_ty_f Γ T W.
Proof.
  intros * [ρ a Hi Ha Hw]; inversion Ha; subst.
  destruct Hw as [Hp | m w Hr Hm Hw]; [ cbn in Hp; discriminate |].
  inversion Hw; subst; try (cbn in *; discriminate).
  econstructor; eassumption.
Qed.

(** NbE at a sort reads a type of it back as a type. *)
Lemma nbe_sort_to_nbe_ty : forall {Γ S T W}, type_sort S -> nbe_f Γ T S W -> nbe_ty_f Γ T W.
Proof.
  intros * [i | |] H; [ exact (nbe_type_to_nbe_ty _ _ _ _ H) | exact (nbe_prop_to_nbe_ty H) | exact (nbe_level_sort_to_nbe_ty H) ].
Qed.

(** NbE of a type, at a sort. *)
Lemma nbe_ty_to_nbe_sort : forall {Γ S T W}, type_sort S -> nbe_ty_f Γ T W -> nbe_f Γ T S W.
Proof.
  intros * [i | |] H;
    [ exact (nbe_ty_to_nbe_type _ _ _ _ H) | exact (nbe_ty_to_nbe_prop _ _ _ H) | exact (nbe_ty_to_nbe_level_sort _ _ _ H) ].
Qed.

(** The normal form of a type of a sort is its own normal form, up to its
    proofs, as for [idempotent_nbe_ty]. *)
Lemma idempotent_nbe_ty_sort : forall {Γ S A B C},
    type_sort S ->
    Γ ⊢ A : S ->
    nbe_ty_f Γ A B ->
    nbe_ty_f Γ B C ->
    nf_eq_upto_proofs B C.
Proof.
  intros * HS HA HB HC.
  pose proof (soundness_ty_at_sort HS HA HB) as HE.
  destruct (completeness HE) as (W & W' & H1 & H2 & Heq).
  apply (nbe_sort_to_nbe_ty HS) in H1, H2.
  functional_nbe_rewrite_clear; exact Heq.
Qed.

(** A type of a sort has a normal form. *)
Lemma nbe_ty_exists_sort : forall {Γ S A}, type_sort S -> Γ ⊢ A : S -> exists W, nbe_ty_f Γ A W.
Proof.
  intros * HS HA; destruct (normalization HA) as (W & HW); exists W; exact (nbe_sort_to_nbe_ty HS HW).
Qed.

(** Semantically equal contexts give a type of a sort one normal form, up
    to its proofs. *)
Lemma ctxeq_nbe_ty_eq_sort : forall {Γ Γ' S A W W'},
    type_sort S -> Γ ⊢ A : S -> ⊨ Γ ≈ Γ' -> ctx_scoped 0 Γ' -> nbe_ty_f Γ A W -> nbe_ty_f Γ' A W' ->
    nf_eq_upto_proofs W W'.
Proof.
  intros * HS HA HΓ HsΓ' HW HW'.
  destruct (ctxeq_nbe_eq _ _ _ _ HA HsΓ' HΓ) as (W1 & W2 & H1 & H2 & Heq).
  apply (nbe_sort_to_nbe_ty HS) in H1, H2.
  functional_nbe_rewrite_clear; exact Heq.
Qed.

(** Contexts extended by equal types of a sort are semantically equal. *)
Lemma ctx_extend_sem_eq : forall {Γ κ S A A'}, type_sort S -> Γ ⊢ A ≈ A' : S -> ⊨ Γ ▹{κ} A ≈ Γ ▹{κ} A'.
Proof.
  intros * HS HAA.
  destruct (rel_type_of_sort HS (completeness_fundamental_exp_eq _ _ _ _ HAA)) as [k Hk].
  eapply per_ctx_extend_type; [| exact Hk ].
  apply rel_ctx_wf_per_ctx, completeness_fundamental_ctx; gen_presups; assumption.
Qed.

(** Types related at an index, of either sort, in a scoped context, have
    normal forms equal up to their proofs: at the initial environment
    their values are related in [per_univ i], so read back alike. *)
Lemma nbe_ty_of_rel_type : forall {Γ A A' i}, ctx_scoped 0 Γ -> Γ ⊨ᵗ A ≈ A' at i ->
    exists W W', nbe_ty_f Γ A W /\ nbe_ty_f Γ A' W' /\ nf_eq_upto_proofs W W'.
Proof.
  intros * HsΓ H.
  destruct (rel_type_under_ctx_at_initial_env HsΓ H) as (ρ & a & a' & Hρi & Ha & Ha' & [Rm HRm]).
  destruct (per_univ_then_per_top_typ HRm (length Γ)) as [W W' HW HW' HE].
  exists W, W'; repeat split; [ econstructor; [ exact Hρi | exact Ha | exact HW ] | econstructor; [ exact Hρi | exact Ha' | exact HW' ] | exact HE ].
Qed.

(** A type of a sort is of the sort at the kind its value at the initial
    environment is of ([abs_kind_sort]): a type of a large universe has
    relevant values, a proposition propositional ones, a type of levels
    values of levels. *)
Lemma typed_at_sort_of_initial_kind : forall {Γ A S ρ a},
    type_sort S -> Γ ⊢ A : S -> initial_env_f Γ ρ -> ⟦ A ⟧ ρ ↘ a ->
    exists k : nat, Γ ⊢ A : abs_kind_sort (domain_kind a) Typeω@k.
Proof.
  intros * HS HA Hρi Ha.
  pose proof (completeness_fundamental_exp _ _ _ HA) as HAs.
  pose proof HAs as [R HR _ _].
  pose proof (wf_ctx_scoped_exp HA) as HsΓ.
  pose proof (per_ctx_then_per_env_initial_env HR HsΓ HsΓ) as [ρ0 [ρ0' [Hρ0 [_ Hρ]]]].
  functional_initial_env_rewrite_clear.
  rewrite (rel_value_kind_of_sort HS HAs HR Hρ Ha).
  destruct (sort_kind_abs_kind_sort_inv _ _ (sort_kind_sort_exp_kind _ HS)) as [i Hi].
  exists i; rewrite <- Hi; exact HA.
Qed.

(** Types each below the other have normal forms equal up to their proofs
    ([rel_type_of_mutual_subtyp]). *)
Lemma nbe_ty_of_mutual_subtyp : forall {Γ A A'},
    Γ ⊢ A ⊆ A' -> Γ ⊢ A' ⊆ A -> exists W W', nbe_ty_f Γ A W /\ nbe_ty_f Γ A' W' /\ nf_eq_upto_proofs W W'.
Proof.
  intros * H H'.
  (** [A] is of a sort: not [LevelSort]. *)
  destruct (presup_subtyp_left_sorted H) as (S & HS & HA).
  destruct (rel_type_of_mutual_subtyp (completeness_fundamental_subtyp _ _ _ H) (completeness_fundamental_subtyp _ _ _ H')
              (rel_type_not_level_sort_of_sort HS (completeness_fundamental_exp _ _ _ HA)))
    as [i Hi].
  assert (HsΓ : ctx_scoped 0 Γ) by (gen_presups; eapply wf_ctx_scoped; eassumption).
  exact (nbe_ty_of_rel_type HsΓ Hi).
Qed.

(** Completeness for types equal at a sort: normal forms equal up to their
    proofs. *)
Lemma completeness_ty_sort : forall {Γ S A B},
    type_sort S -> Γ ⊢ A ≈ B : S -> exists W W', nbe_ty_f Γ A W /\ nbe_ty_f Γ B W' /\ nf_eq_upto_proofs W W'.
Proof.
  intros * HS H.
  destruct (completeness H) as (W & W' & H1 & H2 & HE); exists W, W'; repeat split; try exact HE;
    apply (nbe_sort_to_nbe_ty HS); assumption.
Qed.

(** An equation at a sort, between types one of which is of a large
    universe, is at a large universe: a proposition and a type of levels
    are of no large universe ([typ_prop_absurd], [level_type_not_large]). *)
Lemma exp_eq_sort_large : forall {Γ A B S k},
    type_sort S -> Γ ⊢ A ≈ B : S -> Γ ⊢ A : Typeω@k \/ Γ ⊢ B : Typeω@k ->
    exists k', Γ ⊢ A ≈ B : Typeω@k'.
Proof.
  intros * [i | |] H Hk; [ eauto | |].
  - exfalso; assert (Γ ⊢ A : Propₘ /\ Γ ⊢ B : Propₘ) as [] by (gen_presups; split; assumption).
    destruct Hk; eapply typ_prop_absurd; eassumption.
  - exfalso; assert (Γ ⊢ A : LevelSort /\ Γ ⊢ B : LevelSort) as [HA HB] by (gen_presups; split; assumption).
    destruct Hk as [Hk | Hk]; [ exact (level_type_not_large HA Hk) | exact (level_type_not_large HB Hk) ].
Qed.

(** Two equations of types at sorts compose, at a sort: the middle type
    has one sort. *)
Lemma exp_eq_trans_sort : forall {Γ A B C S S'},
    type_sort S -> type_sort S' -> Γ ⊢ A ≈ B : S -> Γ ⊢ B ≈ C : S' ->
    exists S'', type_sort S'' /\ Γ ⊢ A ≈ C : S''.
Proof.
  intros * HS HS' H1 H2.
  assert (Γ ⊢ B : S /\ Γ ⊢ B : S') as [HB1 HB2] by (gen_presups; split; assumption).
  destruct HS as [i | |], HS' as [j | |].
  - eexists; split; [ constructor | eapply exp_eq_trans_typ_max; eassumption ].
  - exfalso; eapply typ_prop_absurd; eassumption.
  - exfalso; eapply level_type_not_large; eassumption.
  - exfalso; eapply typ_prop_absurd; eassumption.
  - exists Propₘ; split; [ constructor | etransitivity; eassumption ].
  - exfalso; eapply level_type_not_prop; eassumption.
  - exfalso; eapply level_type_not_large; eassumption.
  - exfalso; eapply level_type_not_prop; eassumption.
  - exists LevelSort; split; [ constructor | etransitivity; eassumption ].
Qed.

(** Two equations of types at sorts of one kind compose, at a sort of
    that kind. *)
Lemma exp_eq_trans_sort_kind : forall {Γ κ A B C S S'},
    sort_kind S κ -> sort_kind S' κ -> Γ ⊢ A ≈ B : S -> Γ ⊢ B ≈ C : S' ->
    exists S'', sort_kind S'' κ /\ Γ ⊢ A ≈ C : S''.
Proof.
  intros * HS HS' H1 H2.
  destruct (sort_kind_abs_kind_sort_inv _ _ HS) as [j ->]; destruct (sort_kind_abs_kind_sort_inv _ _ HS') as [j' ->].
  exists (abs_kind_sort κ Typeω@(max j j')); split; [ apply sort_kind_abs_kind_sort |].
  destruct κ; cbn [abs_kind_sort] in *; [| etransitivity; eassumption .. ].
  etransitivity; [ eapply lift_exp_eq_ge; [| exact H1 ] | eapply lift_exp_eq_ge; [| exact H2 ] ]; lia.
Qed.

(** A term of a type is one of a type equal to it at a sort. *)
Lemma exp_conv_sort : forall {Γ M A A' S},
    type_sort S -> Γ ⊢ A ≈ A' : S -> Γ ⊢ M : A -> Γ ⊢ M : A'.
Proof.
  intros * HS H HM.
  assert (Γ ⊢ A : S /\ Γ ⊢ A' : S) as [] by (gen_presups; split; assumption).
  eapply wf_exp_subtyp'; [ exact HM | eapply proj1, wf_subtyp_of_exp_eq; eassumption ].
Qed.

(** No type of a large universe is below a proposition. *)
Lemma subtyp_relevant_prop_absurd : forall {Γ A A' i},
    Γ ⊢ A ⊆ A' -> Γ ⊢ A : Typeω@i -> Γ ⊢ A' : Propₘ -> False.
Proof. intros * Hs HA HA'; discriminate (subtyp_same_kind Γ A A' ak_relevant ak_propositional i 0 Hs HA HA'). Qed.

(** No proposition is below a type of a large universe. *)
Lemma subtyp_prop_relevant_absurd : forall {Γ A A' i},
    Γ ⊢ A ⊆ A' -> Γ ⊢ A : Propₘ -> Γ ⊢ A' : Typeω@i -> False.
Proof. intros * Hs HA HA'; discriminate (subtyp_same_kind Γ A A' ak_propositional ak_relevant 0 i Hs HA HA'). Qed.

(** [Π] congruence over a domain of a sort at its tag: a type, a
    proposition or a type of levels. *)
Lemma pi_cong_sort : forall {Θ Ξ Γ κ A A' B B' Sd i},
    sort_kind Sd κ -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Sd -> Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Sd -> Θ ⍮ Ξ ⍮ Γ ▹{κ} A ⊢ B ≈ B' : Typeω@i ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ Π{κ} A B ≈ Π{κ} A' B' : Typeω@j.
Proof.
  intros * HS HA HAA HB.
  exact (wf_exp_eq_pi_sort_at _ _ _ κ ak_relevant A A' B B' Sd i HA HS HAA HB ltac:(discriminate)).
Qed.

(** [∀ₚ] congruence over a domain of a sort at its tag. *)
Lemma all_cong_sort : forall {Θ Ξ Γ κ A A' P P' Sd},
    sort_kind Sd κ -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Sd -> Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Sd -> Θ ⍮ Ξ ⍮ Γ ▹{κ} A ⊢ P ≈ P' : Propₘ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ∀ₚ{κ} A P ≈ ∀ₚ{κ} A' P' : Propₘ.
Proof.
  intros * HS HA HAA HP.
  destruct (wf_exp_eq_pi_sort_at _ _ _ κ ak_propositional A A' P P' Sd 0 HA HS HAA HP ltac:(discriminate)) as [j Hj].
  exact Hj.
Qed.

(** A [Π] into a universe is a type of a large universe, of the universe
    it is in or of every large one above the small one it is in. *)
Lemma wf_pi_typed_large : forall {Γ κ A B C}, Γ ⊢ Π{κ} A B : C -> exists k, Γ ⊢ Π{κ} A B : Typeω@k.
Proof.
  intros * H.
  destruct (wf_pi_inversion_at H) as [U HU HA HB Hk _].
  assert (HP : Γ ⊢ Π{κ} A B : U) by (change U with (abs_kind_sort ak_relevant U); eapply wf_pi; eassumption).
  inversion HU; subst; [ eexists; exact HP |].
  exists 0; eapply wf_exp_subtyp'; [ exact HP | eapply wf_subtyp_small_large; [ gen_presups; assumption | eassumption ] ].
Qed.

(** A typed proposition former, [⊤], [⊥], a [∀ₚ] or a [Σₚ], is a
    proposition. *)
Lemma prop_former_typed : forall {Γ A C},
    Γ ⊢ A : C -> (A = ⊤ \/ A = ⊥ \/ (exists κ B P, A = ∀ₚ{κ} B P) \/ (exists P Q, A = Σₚ P Q)) ->
    Γ ⊢ A : Propₘ.
Proof.
  intros * H [-> | [-> | [(κ & B & P & ->) | (P & Q & ->)]]].
  - apply wf_True; gen_presups; assumption.
  - apply wf_False; gen_presups; assumption.
  - destruct (wf_all_inversion _ _ _ _ _ _ _ H) as [S HS HB HP _].
    destruct (wf_pi_sort_at _ _ _ κ ak_propositional B P S 0 HB HS HP ltac:(discriminate)) as [j Hj].
    exact Hj.
  - destruct (wf_and_inversion _ _ _ _ _ _ H) as [HP HQ _].
    apply wf_and; assumption.
Qed.

(** A [Π] into a universe, a type of a large universe, is below no [∀],
    a proposition ([subtyp_same_kind]). *)
Lemma subtyp_pi_all_absurd : forall {Γ κ A B κ' X Y},
    Γ ⊢ Π{κ} A B ⊆ ∀ₚ{κ'} X Y -> False.
Proof.
  intros * Hs.
  assert (exists C, Γ ⊢ Π{κ} A B : C) as [C HC] by (gen_presups; eexists; eassumption).
  assert (exists C', Γ ⊢ ∀ₚ{κ'} X Y : C') as [C' HC'] by (gen_presups; eexists; eassumption).
  pose proof (prop_former_typed HC' ltac:(eauto 7)) as Hp.
  destruct (wf_pi_typed_large HC) as [k Hk].
  discriminate (subtyp_same_kind Γ _ _ ak_relevant ak_propositional k k Hs Hk Hp).
Qed.

(** Extended by equal types of a sort at their tag, a context refines the
    other extension. *)
Lemma sub_id_extend_of_exp_eq : forall {Γ κ A A' S},
    sort_kind S κ -> Γ ⊢ A ≈ A' : S -> Γ ▹{κ} A ⊢ˢ Id : Γ ▹{κ} A'.
Proof.
  intros * HS H.
  assert (HId : Γ ⊢ˢ Id : Γ) by (gen_presups; mauto 3).
  assert (Γ ⊢ A : S /\ Γ ⊢ A' : S) as [] by (gen_presups; split; assumption).
  eapply wf_sub_id_extend; [ exact HId | eassumption | exact HS | eassumption | exact HS |].
  eapply proj1, wf_subtyp_of_exp_eq; [ eassumption | eassumption | exact (sort_kind_type_sort _ _ HS) | eassumption ].
Qed.

(** Two types of one sort whose normal forms are equal up to their proofs
    are equal at it ([soundness_upto_proofs]).  The sort is given on both
    sides: normal forms do not determine it, since the readback of a
    neutral type drops its sort, so [⇑ 𝕌ω@0 #x] and [⇑ Propᵈ #x], a
    relevant type and a proposition, read back alike. *)
Lemma exp_eq_of_nbe_ty_same : forall {Γ A A' S W W'},
    type_sort S ->
    Γ ⊢ A : S ->
    Γ ⊢ A' : S ->
    nbe_ty_f Γ A W ->
    nbe_ty_f Γ A' W' ->
    nf_eq_upto_proofs W W' ->
    Γ ⊢ A ≈ A' : S.
Proof.
  intros * HS HA HA' Hn Hn' HE.
  exact (soundness_upto_proofs HA HA' (nbe_ty_to_nbe_sort HS Hn) (nbe_ty_to_nbe_sort HS Hn') HE).
Qed.

(** The value at the initial environment of a type of a sort is of the
    sort's kind ([sort_exp_kind]). *)
Lemma initial_value_kind_of_sort : forall {Γ X T ρ x}, type_sort T -> Γ ⊢ X : T -> initial_env_f Γ ρ -> ⟦ X ⟧ ρ ↘ x ->
    domain_kind x = sort_exp_kind T.
Proof.
  intros * HT HX Hρ Hx.
  pose proof (completeness_fundamental_exp _ _ _ HX) as HXs.
  pose proof HXs as [R HR _ _].
  pose proof (wf_ctx_scoped_exp HX) as HsΓ.
  destruct (per_ctx_then_per_env_initial_env HR HsΓ HsΓ) as (ρ0 & ρ0' & Hρ0 & Hρ0' & Hρρ).
  assert (ρ0 = ρ) as -> by (eapply functional_initial_env; eassumption).
  exact (rel_value_kind_of_sort HT HXs HR Hρρ Hx).
Qed.

(** Two types at sorts of one kind are types at the sort of the kind at
    one index. *)
Lemma sort_kind_common : forall {Θ Ξ Γ κ A A' S S'}, sort_kind S κ -> sort_kind S' κ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : S -> Θ ⍮ Ξ ⍮ Γ ⊢ A' : S' ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : abs_kind_sort κ Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ⊢ A' : abs_kind_sort κ Typeω@i.
Proof.
  intros * HS HS' HA HA'.
  destruct (sort_kind_abs_kind_sort_inv _ _ HS) as [j ->]; destruct (sort_kind_abs_kind_sort_inv _ _ HS') as [j' ->].
  exists (max j j'); split; eapply abs_kind_sort_lift; [ exact HA | | exact HA' | ]; lia.
Qed.

(** [Π] is injective, at its domain's tag too: the two tags are those of
    the two domains' values, related at the initial environment
    ([per_univ_elem_kind]), so the domains are at the sort of one kind
    ([wf_pi_inversion']) and equal there. *)
Lemma exp_eq_pi_inversion : forall {Γ κ κ' A B A' B' i},
    Γ ⊢ Π{κ} A B ≈ Π{κ'} A' B' : Typeω@i ->
    κ = κ' /\ Γ ⊢ A ≈ A' : abs_kind_sort κ Typeω@i /\ Γ ▹{κ} A ⊢ B ≈ B' : Typeω@i.
Proof.
  intros * H.
  assert (HsΓ : ctx_scoped 0 Γ) by (gen_presups; eapply wf_ctx_scoped; eassumption).
  assert (Γ ⊢ Π{κ} A B : Typeω@i /\ Γ ⊢ Π{κ'} A' B' : Typeω@i) as [HΠ1 HΠ2] by (gen_presups; split; assumption).
  apply wf_pi_inversion' in HΠ1 as [HA HB]; apply wf_pi_inversion' in HΠ2 as [HA' HB'].
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hs.
  destruct (rel_typ_under_ctx_at_initial_env HsΓ Hs) as (ρ & aΠ & aΠ' & Hρ & HaΠ & HaΠ' & [R HR]).
  inversion HaΠ; subst; inversion HaΠ'; subst.
  (** Related [Π]-values have one tag, the kind of the domains' values *)
  invert_per_univ_elem HR.
  match goal with H5 : ⟦ A ⟧ ρ ↘ ?a |- _ => set (κ := domain_kind a) in * end.
  split; [ reflexivity |].
  pose proof (sort_kind_type_sort _ _ (sort_kind_abs_kind_sort κ i)) as HS.
  destruct (per_univ_then_per_top_typ equiv_a_a' (length Γ)) as [WA WA' HWA HWA' HEA].
  assert (HAA : Γ ⊢ A ≈ A' : abs_kind_sort κ Typeω@i)
    by (eapply exp_eq_of_nbe_ty_same; [ exact HS | exact HA | exact HA' | econstructor; eassumption | econstructor; eassumption | exact HEA ]).
  split; [ exact HAA |].
  pose proof (sort_kind_abs_kind_sort κ i) as HSk.
  (** The codomains, at the variables, read back alike; the right one
      moved to the left domain *)
  assert (Hc : in_rel (⇑! a (length Γ)) (⇑! a0 (length Γ))) by (apply (var_per_elem _ equiv_a_a'); assumption).
  match goal with H1 : forall c c' (equiv_c_c' : in_rel c c'), rel_mod_eval _ B _ B' _ _ |- _ =>
    destruct (H1 _ _ Hc) as [b b' Hb Hb' HRb] end.
  destruct (per_univ_then_per_top_typ HRb (Datatypes.S (length Γ))) as [WB WB' HWB HWB' HEB].
  assert (HnB : nbe_ty_f (Γ ▹{κ} A) B WB) by (econstructor; [ econstructor; eassumption | exact Hb | exact HWB ]).
  assert (HnB' : nbe_ty_f (Γ ▹{κ} A') B' WB') by (econstructor; [ econstructor; eassumption | exact Hb' | exact HWB' ]).
  assert (HId : Γ ▹{κ} A ⊢ˢ Id : Γ ▹{κ} A') by exact (sub_id_extend_of_exp_eq HSk HAA).
  assert (HB'A : Γ ▹{κ} A ⊢ B' : Typeω@i) by (eapply ctxsub_exp; [ exact HId | exact HB' ]).
  destruct (normalization_ty HB'A) as (WB'' & HnB'').
  assert (HsΓA : ctx_scoped 0 (Γ ▹{κ} A)) by (gen_presups; eapply wf_ctx_scoped; eassumption).
  assert (Hsem : ⊨ Γ ▹{κ} A' ≈ Γ ▹{κ} A) by (apply (ctx_extend_sem_eq HS); symmetry; exact HAA).
  pose proof (ctxeq_nbe_ty_eq_sort (type_sort_universe i) HB' Hsem HsΓA HnB' HnB'') as HE'.
  eapply exp_eq_of_nbe_ty_same; [ apply type_sort_universe | exact HB | exact HB'A | exact HnB | exact HnB'' | etransitivity; eassumption ].
Qed.

(** A [Π] between types of levels is injective, as a [Π] into a universe
    is ([exp_eq_pi_inversion]), at [LevelSort]: its domain is a type of
    levels too ([pi_kinds_level]). *)
Lemma exp_eq_pi_level_inversion : forall {Γ κ κ' A B A' B'},
    Γ ⊢ a_pi κ ak_level A B ≈ a_pi κ' ak_level A' B' : LevelSort ->
    κ = κ' /\ Γ ⊢ A ≈ A' : LevelSort /\ Γ ▹{κ} A ⊢ B ≈ B' : LevelSort.
Proof.
  intros * H.
  assert (HsΓ : ctx_scoped 0 Γ) by (gen_presups; eapply wf_ctx_scoped; eassumption).
  assert (Γ ⊢ a_pi κ ak_level A B : LevelSort /\ Γ ⊢ a_pi κ' ak_level A' B' : LevelSort) as [HΠ1 HΠ2]
    by (gen_presups; split; assumption).
  destruct (wf_pi_inversion_at HΠ1) as [U HU HA HB Hk _]; inversion Hk; subst.
  destruct (wf_pi_inversion_at HΠ2) as [U' HU' HA' HB' Hk' _]; inversion Hk'; subst.
  cbn [abs_kind_sort] in HA, HB, HA', HB'.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hs.
  pose proof Hs as [R0 HR0 _ _].
  destruct (per_ctx_then_per_env_initial_env HR0 HsΓ HsΓ) as (ρ & ρ' & Hρ & Hρ' & Hrel).
  assert (ρ' = ρ) as -> by (eapply functional_initial_env; eassumption).
  destruct (rel_exp_of_level_sort_inversion_simple_at HR0 Hs _ _ Hrel) as (aΠ & aΠ' & HaΠ & HaΠ' & (_ & _ & [R HR])).
  inversion HaΠ; subst; inversion HaΠ'; subst.
  invert_per_univ_elem HR.
  cbn [exp_wk] in HB, HB'.
  split; [ reflexivity |].
  (** The domains read back alike *)
  destruct (per_univ_then_per_top_typ equiv_a_a' (length Γ)) as [WA WA' HWA HWA' HEA].
  assert (HAA : Γ ⊢ A ≈ A' : LevelSort)
    by (eapply exp_eq_of_nbe_ty_same;
        [ exact type_sort_level | exact HA | exact HA' | econstructor; eassumption | econstructor; eassumption | exact HEA ]).
  split; [ exact HAA |].
  (** So do the codomains at the variables; the right one moved to the left
      domain *)
  assert (Hc : in_rel (⇑! a (length Γ)) (⇑! a0 (length Γ))) by (apply (var_per_elem _ equiv_a_a'); assumption).
  match goal with H1 : forall c c' (equiv_c_c' : in_rel c c'), rel_mod_eval _ B _ B' _ _ |- _ =>
    destruct (H1 _ _ Hc) as [b b' Hb Hb' HRb] end.
  destruct (per_univ_then_per_top_typ HRb (Datatypes.S (length Γ))) as [WB WB' HWB HWB' HEB].
  assert (HnB : nbe_ty_f (Γ ▹{ak_level} A) B WB) by (econstructor; [ econstructor; eassumption | exact Hb | exact HWB ]).
  assert (HnB' : nbe_ty_f (Γ ▹{ak_level} A') B' WB') by (econstructor; [ econstructor; eassumption | exact Hb' | exact HWB' ]).
  assert (HId : Γ ▹{ak_level} A ⊢ˢ Id : Γ ▹{ak_level} A') by exact (sub_id_extend_of_exp_eq sort_kind_level HAA).
  assert (HB'A : Γ ▹{ak_level} A ⊢ B' : LevelSort) by (eapply ctxsub_exp; [ exact HId | exact HB' ]).
  destruct (nbe_ty_exists_sort type_sort_level HB'A) as (WB'' & HnB'').
  assert (HsΓA : ctx_scoped 0 (Γ ▹{ak_level} A)) by (gen_presups; eapply wf_ctx_scoped; eassumption).
  assert (Hsem : ⊨ Γ ▹{ak_level} A' ≈ Γ ▹{ak_level} A) by (apply (ctx_extend_sem_eq type_sort_level); symmetry; exact HAA).
  pose proof (ctxeq_nbe_ty_eq_sort type_sort_level HB' Hsem HsΓA HnB' HnB'') as HE'.
  eapply exp_eq_of_nbe_ty_same; [ exact type_sort_level | exact HB | exact HB'A | exact HnB | exact HnB'' | etransitivity; eassumption ].
Qed.

(** [Level@n] is no [Π] between types of levels: their values are of
    distinct heads, and related types of levels are of one head. *)
Lemma exp_eq_level_pi_level_absurd : forall {Γ n κ A B},
    Γ ⊢ Level@n ≈ a_pi κ ak_level A B : LevelSort -> False.
Proof.
  intros * H.
  assert (HsΓ : ctx_scoped 0 Γ) by (gen_presups; eapply wf_ctx_scoped; eassumption).
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hs.
  pose proof Hs as [R0 HR0 _ _].
  destruct (per_ctx_then_per_env_initial_env HR0 HsΓ HsΓ) as (ρ & ρ' & Hρ & Hρ' & Hrel).
  destruct (rel_exp_of_level_sort_inversion_simple_at HR0 Hs _ _ Hrel) as (a & a' & Ha & Ha' & (_ & _ & [R HR])).
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
Qed.

(** [Level@n] determines its sort, at [LevelSort]. *)
Lemma exp_eq_level_inj_level_sort : forall {Γ m n},
    Γ ⊢ Level@m ≈ Level@n : LevelSort -> m = n.
Proof.
  intros * H.
  assert (HsΓ : ctx_scoped 0 Γ) by (gen_presups; eapply wf_ctx_scoped; eassumption).
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hs.
  pose proof Hs as [R0 HR0 _ _].
  destruct (per_ctx_then_per_env_initial_env HR0 HsΓ HsΓ) as (ρ & ρ' & Hρ & Hρ' & Hrel).
  destruct (rel_exp_of_level_sort_inversion_simple_at HR0 Hs _ _ Hrel) as (a & a' & Ha & Ha' & (_ & _ & [R HR])).
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
  reflexivity.
Qed.

(** [∀] is injective, at its domain's tag too: two equal propositions [∀]
    have the same tag, domains equal at the sort of the tag and
    propositions equal under the left domain.  Their normal forms are
    equal up to their proofs ([Πⁿ{κ}] keeps the tag), so are their
    domains' and their bodies'; the right body is moved to the left domain
    ([ctxeq_nbe_ty_eq_sort]).  The tag fixes the domains' sort: a domain
    [A : Type@0] and a domain [A' : LevelSort] are of distinct tags. *)
Lemma exp_eq_all_inversion : forall {Γ κ κ' A P A' P'},
    Γ ⊢ ∀ₚ{κ} A P ≈ ∀ₚ{κ'} A' P' : Propₘ ->
    κ = κ' /\ (exists i, Γ ⊢ A ≈ A' : abs_kind_sort κ Typeω@i) /\ Γ ▹{κ} A ⊢ P ≈ P' : Propₘ.
Proof.
  intros * H.
  assert (Γ ⊢ ∀ₚ{κ} A P : Propₘ /\ Γ ⊢ ∀ₚ{κ'} A' P' : Propₘ) as [H1 H2] by (gen_presups; split; assumption).
  destruct (wf_all_inversion _ _ _ _ _ _ _ H1) as [SA HSA HA0 HP _].
  destruct (wf_all_inversion _ _ _ _ _ _ _ H2) as [SA' HSA' HA0' HP' _].
  destruct (completeness_ty_sort type_sort_prop H) as (W & W' & [ρ a Hi Ha Hr] & [ρ' a' Hi' Ha' Hr'] & HE).
  functional_initial_env_rewrite_clear.
  inversion Ha; subst; inversion Ha'; subst.
  inversion Hr; subst; inversion Hr'; subst.
  apply nf_pi_upto_proofs_inv in HE as (Hκ & _ & HEA & HEP); subst κ'.
  split; [ reflexivity |].
  destruct (sort_kind_common HSA HSA' HA0 HA0') as (i & HA & HA').
  pose proof (sort_kind_abs_kind_sort κ i) as HSk.
  pose proof (sort_kind_type_sort _ _ HSk) as HS.
  assert (HAA : Γ ⊢ A ≈ A' : abs_kind_sort κ Typeω@i)
    by (eapply exp_eq_of_nbe_ty_same; [ exact HS | exact HA | exact HA' | econstructor; eassumption | econstructor; eassumption | exact HEA ]).
  split; [ exists i; exact HAA |].
  (** The bodies, in the left domain's context *)
  assert (HId : Γ ▹{κ} A ⊢ˢ Id : Γ ▹{κ} A') by exact (sub_id_extend_of_exp_eq HSk HAA).
  assert (HP'A : Γ ▹{κ} A ⊢ P' : Propₘ) by (eapply ctxsub_exp; [ exact HId | exact HP' ]).
  match goal with
  | HeP : ⟦ P ⟧ ρ ↦ ⇑! ?a0 (length Γ) ⦂ _ ↘ ?b, HrP : Rtyp ?b in Datatypes.S (length Γ) ↘ ?WP,
    HeP' : ⟦ P' ⟧ ρ ↦ ⇑! ?a0' (length Γ) ⦂ _ ↘ ?b', HrP' : Rtyp ?b' in Datatypes.S (length Γ) ↘ ?WP' |- _ =>
      assert (HnP : nbe_ty_f (Γ ▹{κ} A) P WP) by (econstructor; [ econstructor; eassumption | eassumption | exact HrP ]);
      assert (HnP' : nbe_ty_f (Γ ▹{κ} A') P' WP') by (econstructor; [ econstructor; eassumption | eassumption | exact HrP' ])
  end.
  destruct (normalization HP'A) as (WP'' & HnP''0).
  pose proof (nbe_prop_to_nbe_ty HnP''0) as HnP''.
  assert (HsΓA : ctx_scoped 0 (Γ ▹{κ} A)) by (gen_presups; eapply wf_ctx_scoped; eassumption).
  assert (Hsem : ⊨ Γ ▹{κ} A' ≈ Γ ▹{κ} A) by (apply (ctx_extend_sem_eq HS); symmetry; exact HAA).
  pose proof (ctxeq_nbe_ty_eq_sort type_sort_prop HP' Hsem HsΓA HnP' HnP'') as HE'.
  eapply exp_eq_of_nbe_ty_same; [ apply type_sort_prop | exact HP | exact HP'A | exact HnP | exact HnP'' | etransitivity; eassumption ].
Qed.

(** ** The Parameters of an Inductive Type

    The normal form of an inductive type is the type former at normal
    forms of its parameters, each equal, up to proofs, to the normal form
    of its parameter at the parameter's instance type
    ([nbe_params_at_telescope]); so equal inductive types have equal
    parameters. *)
Lemma nbe_ty_ind_params : forall Γ p D k Mk Ms W, ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> ⊢ Γ ->
    List.length Ms = im_np D Mk ->
    (forall j P T, List.nth_error Ms j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id Ms) j = Some T -> Γ ⊢ P : T) ->
    nbe_ty_f Γ (apps (a_ind p k) Ms) W ->
    exists Rs, W = nf_indty p k Rs /\ List.length Rs = im_np D Mk /\
      forall j P T R V, List.nth_error Ms j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id Ms) j = Some T ->
        List.nth_error Rs j = Some R -> nbe_f Γ P T V -> nf_eq_upto_proofs V R.
Proof.
  intros * Hl Hk HΓ HMl HMt [ρ a Hρ Ha Hr].
  destruct (eval_ind_apps_args _ _ _ _ _ Ha) as (vs & Hvs & ->).
  inversion Hr; subst.
  match goal with H1 : ind_lookup _ _ _ = Some _, H2 : ind_member _ _ = Some _,
                  H3 : Rps _ at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Ps |- _ =>
    rewrite Hl in H1; injection H1 as <-; rewrite Hk in H2; injection H2 as <-; rename H3 into Hps; exists Ps end.
  split; [ reflexivity | split ].
  - rewrite (read_ps_length_nf _ _ _ _ _ Hps), (read_ps_length _ _ _ _ _ Hps), List.length_rev, length_im_params; reflexivity.
  - exact (nbe_params_at_telescope _ _ _ _ _ _ (ind_evaluated_params_telescope _ _ _ _ _ HΓ Hl Hk)
             ltac:(rewrite length_im_params; exact HMl) HMt Hρ Hvs Hps).
Qed.

(** A type whose normal form is an inductive type is equal to the type
    former at typed parameters, equal to the normal form's
    ([glu_nfs_eq_at]): the gluing of the inductive type at the identity. *)
Lemma typ_ind_shape : forall Γ T i p k Rs, Γ ⊢ T : Typeω@i -> nbe_ty_f Γ T (nf_indty p k Rs) ->
    exists D Mk Ps, ind_lookup gc_deps gc_stack p = Some D /\ ind_member D k = Some Mk /\ List.length Ps = im_np D Mk /\
      (forall j P A, List.nth_error Ps j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id Ps) j = Some A -> Γ ⊢ P : A) /\
      Γ ⊢ T ≈ apps (a_ind p k) Ps : Typeω@i /\ exps_eq_at Γ (im_params D Mk) Ps (List.map nf_to_exp Rs).
Proof.
  intros * HT HW.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  inversion HW as [ρ a Hinit Ea HRa]; subst.
  inversion HRa; subst.
  destruct (soundness_fundamental_ctx _ HΓ) as [Sb HSb].
  pose proof (initial_env_glu_rel_exp Hinit HSb) as Hσ.
  destruct (Soundness.Inductives.Args.glu_rel_typ_at _ _ _ _ _ _ _ HSb (soundness_fundamental_exp _ _ _ HT) Hσ) as (_ & a' & Ea' & Hpa & HPa).
  assert (a' = d_ind p k as') as -> by (eapply functional_eval_exp; eassumption).
  destruct (per_univ_glu_univ_elem _ _ Hpa) as (P & El & Hg).
  pose proof (HPa P El Hg) as HP; rewrite exp_sub_id in HP.
  invert_glu_univ_elem Hg.
  match goal with H : _ <∙> ind_glu_typ_pred _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => apply H in HP end.
  destruct HP as (Ps & Heq & HK).
  assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
  destruct (HK Γ wk_id Hid) as [Htop _ _ _].
  rewrite map_wk_id in Htop.
  match goal with H : ind_lookup _ _ p = Some ?D0, H' : ind_lookup _ _ p = Some ?D1 |- _ =>
    assert (D0 = D1) as -> by congruence end.
  match goal with H : ind_member _ k = Some ?M0, H' : ind_member _ k = Some ?M1 |- _ =>
    assert (M0 = M1) as -> by congruence end.
  destruct Htop as [HPl HPt Hrb].
  eexists _, _, Ps; split; [ eassumption | split; [ eassumption | split; [ exact HPl | split; [ exact HPt | split; [ exact Heq |] ] ] ] ].
  (** The parameters' readback, the normal form's ([glu_params_top]) *)
  match goal with Hr : Rps _ at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ Rs |- _ => pose proof (Hrb Γ wk_id Rs Hid Hr) as H' end.
  rewrite map_wk_id in H'; exact H'.
Qed.

(** Two instances [X], [Y] of a closed telescope [C] whose terms have
    normal forms equal, up to proofs, to the same list (two lists equal
    up to proofs) are equal instances.  Position by position: once the
    terms before [j] are equal, the instance types at [j] are equal
    ([tele_insts_cong], at [Y]'s terms before [j] and [X]'s after), so
    [Y_j] is of [X]'s instance type, where it reads back as at its own
    ([completeness_at_equal_types]), and [soundness_upto_proofs] makes it
    equal to [X_j]. *)
Lemma exps_eq_at_of_params_up_to_proofs : forall Γ C X Y Rs Rs', all_assumptions C -> ⊢ (C ++ Γ)%list ->
    List.length X = List.length C -> List.length Y = List.length C ->
    (forall j P T, List.nth_error X j = Some P -> List.nth_error (tele_insts C Id X) j = Some T -> Γ ⊢ P : T) ->
    (forall j P T, List.nth_error Y j = Some P -> List.nth_error (tele_insts C Id Y) j = Some T -> Γ ⊢ P : T) ->
    (forall j P T R V, List.nth_error X j = Some P -> List.nth_error (tele_insts C Id X) j = Some T ->
       List.nth_error Rs j = Some R -> nbe_f Γ P T V -> nf_eq_upto_proofs V R) ->
    (forall j P T R V, List.nth_error Y j = Some P -> List.nth_error (tele_insts C Id Y) j = Some T ->
       List.nth_error Rs' j = Some R -> nbe_f Γ P T V -> nf_eq_upto_proofs V R) ->
    List.length Rs = List.length C -> nfs_eq_upto_proofs Rs Rs' ->
    exps_eq_at Γ C X Y.
Proof.
  intros * HCa HCΓ HXl HYl HXt HYt HX HY HRl HE.
  split; [ congruence |].
  enough (Hn : forall n j P Q A, j < n -> List.nth_error X j = Some P -> List.nth_error Y j = Some Q ->
                 List.nth_error (tele_insts C Id X) j = Some A -> Γ ⊢ P ≈ Q : A)
    by (intros j P Q A HP HQ HA; exact (Hn (S j) j P Q A ltac:(lia) HP HQ HA)).
  induction n as [| n IH]; intros j P Q A Hjn' HP HQ HA; [ lia |].
  destruct (PeanoNat.Nat.lt_ge_cases j n) as [Hjn | Hjn]; [ exact (IH _ _ _ _ Hjn HP HQ HA) |].
  assert (n = j) as -> by lia.
  assert (HΓ : ⊢ Γ) by (eapply ctx_app_wf_tail; exact HCΓ).
  assert (Hj : j < List.length C) by (rewrite <- HXl; apply List.nth_error_Some; congruence).
  (** [Y]'s terms before [j], [X]'s from [j] on *)
  set (Y' := (List.firstn j Y ++ List.skipn j X)%list).
  assert (HY'l : List.length Y' = List.length C)
    by (unfold Y'; rewrite List.length_app, List.length_firstn, List.length_skipn; lia).
  assert (HY'n : forall k N, List.nth_error Y' k = Some N ->
             (k < j /\ List.nth_error Y k = Some N) \/ (j <= k /\ List.nth_error X k = Some N)).
  { intros k N HN; unfold Y' in HN.
    destruct (PeanoNat.Nat.lt_ge_cases k j) as [Hk | Hk].
    - left; rewrite List.nth_error_app1 in HN by (rewrite List.length_firstn; lia).
      rewrite nth_error_firstn_lt in HN by exact Hk; split; assumption.
    - right; rewrite List.nth_error_app2 in HN by (rewrite List.length_firstn; lia).
      rewrite List.length_firstn, List.nth_error_skipn in HN; replace (j + (k - Init.Nat.min j (List.length Y))) with k in HN by lia.
      split; assumption. }
  assert (HXY' : forall k N N' T, List.nth_error X k = Some N -> List.nth_error Y' k = Some N' ->
             List.nth_error (tele_insts C Id X) k = Some T -> Γ ⊢ N ≈ N' : T).
  { intros k N N' T HN HN' HT.
    destruct (HY'n _ _ HN') as [[Hk HN'Y] | [Hk HN'X]].
    - exact (IH _ _ _ _ Hk HN HN'Y HT).
    - rewrite HN in HN'X; injection HN'X as <-; apply wf_exp_eq_refl; exact (HXt _ _ _ HN HT). }
  (** The instance types at [j] are equal *)
  destruct (nth_error_lt_some (tele_insts C Id Y') j) as [T' HT']; [ rewrite length_tele_insts by exact HCa; lia |].
  destruct (tele_insts_cong C Γ Γ Id Id X Y' HCa HCΓ ltac:(apply wf_sub_eq_refl; mauto 3) ltac:(lia) HY'l HXY' _ _ _ HA HT')
    as (S & HS & HAT').
  destruct (nth_error_lt_some (tele_insts C Id Y) j) as [B HB]; [ rewrite length_tele_insts by exact HCa; lia |].
  assert (EB : B = T').
  { destruct (tele_insts_nth _ _ _ _ _ HB) as (κ1 & A1 & HA1 & ->).
    destruct (tele_insts_nth _ _ _ _ _ HT') as (κ2 & A2 & HA2 & ->).
    rewrite HA1 in HA2; injection HA2 as _ <-.
    unfold Y'; rewrite List.firstn_app, List.firstn_firstn, List.length_firstn.
    replace (j - Init.Nat.min j (List.length Y)) with 0 by lia; rewrite List.firstn_O, List.app_nil_r.
    replace (Init.Nat.min j j) with j by lia; reflexivity. }
  subst T'.
  (** So [Y_j] is of [X]'s instance type; the three normal forms agree *)
  pose proof (HXt _ _ _ HP HA) as HPt.
  pose proof (HYt _ _ _ HQ HB) as HQB.
  assert (HQA : Γ ⊢ Q : A) by (eapply wf_conv_sort; [ exact HQB | exact (presup_exp_eq_left HAT') | exact HS | symmetry; exact HAT' ]).
  destruct (nth_error_lt_some Rs j) as [R HR]; [ lia |].
  destruct (nfs_eq_upto_proofs_nth _ _ _ _ HE HR) as (R' & HR'' & E4).
  destruct (normalization HPt) as [V1 HV1].
  destruct (normalization HQB) as [V2 HV2].
  destruct (normalization HQA) as [V3 HV3].
  pose proof (HX _ _ _ _ _ HP HA HR HV1) as E1.
  pose proof (HY _ _ _ _ _ HQ HB HR'' HV2) as E2.
  pose proof (completeness_at_equal_types HS (wf_exp_eq_refl HQA) HAT' HV3 HV2) as E3.
  (** [V1 ≈ R ≈ R' ≈ V2 ≈ V3] *)
  eapply soundness_upto_proofs; [ exact HPt | exact HQA | exact HV1 | exact HV3 |].
  etransitivity; [ exact E1 |]; etransitivity; [ exact E4 |]; etransitivity; [ symmetry; exact E2 | symmetry; exact E3 ].
Qed.

Corollary exp_eq_ind_apps_inv : forall Γ p D k Mk X Y i, ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk ->
    Γ ⊢ apps (a_ind p k) X ≈ apps (a_ind p k) Y : Typeω@i ->
    List.length X = im_np D Mk -> List.length Y = im_np D Mk ->
    (forall j P T, List.nth_error X j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id X) j = Some T -> Γ ⊢ P : T) ->
    (forall j P T, List.nth_error Y j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id Y) j = Some T -> Γ ⊢ P : T) ->
    exps_eq_at Γ (im_params D Mk) X Y.
Proof.
  intros * Hl Hk H HXl HYl HXt HYt.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct (ind_evaluated_params_telescope _ _ _ _ _ HΓ Hl Hk) as [HCa _ _ HCΓ].
  destruct (completeness_ty H) as (W & W' & HWX & HWY & HE).
  destruct (nbe_ty_ind_params _ _ _ _ _ _ _ Hl Hk HΓ HXl HXt HWX) as (Rs & -> & HRl & HX).
  destruct (nbe_ty_ind_params _ _ _ _ _ _ _ Hl Hk HΓ HYl HYt HWY) as (Rs' & -> & _ & HY).
  apply nf_indty_upto_proofs_inv in HE as (_ & _ & HE).
  eapply exps_eq_at_of_params_up_to_proofs; try eassumption; rewrite ?length_im_params; assumption.
Qed.

Lemma nf_of_pi : forall {Γ κ M A B},
    Γ ⊢ M : Π{κ} A B ->
    exists W1 W2, nbe_f Γ M (Π{κ} A B) (λⁿ W1 W2).
Proof.
  intros * HM; destruct (soundness HM) as [W [Hn _]].
  pose proof Hn as Hn0.
  destruct Hn as [ρ a Hi Ha Hr].
  inversion Ha; subst.
  (** A function is relevant, and read back as a [λ] *)
  destruct Hr as [Hp | m w Hrel Hm Hw]; [ cbn in Hp; discriminate |].
  inversion Hw; subst; try (cbn in *; discriminate).
  do 2 eexists; exact Hn0.
Qed.
Hint Resolve nf_of_pi : mctt.

Theorem canonical_form_of_pi : forall {κ M A B},
    ⋅ ⊢ M : Π{κ} A B ->
    exists W1 W2, nbe_f ⋅ M (Π{κ} A B) (λⁿ W1 W2).
Proof. mauto 3. Qed.
Hint Resolve canonical_form_of_pi : mctt.

(** ** Small Universes Are Injective

    Two small universes are equal only at equal levels: their values are
    related, so their levels are ([per_univ_elem_core_suniv]), so the two
    level terms have the same normal form, and soundness turns that into an
    equation. *)
Lemma exp_eq_suniv_tm_inj : forall {Γ t t' k},
    Γ ⊢ Type⟨t⟩ ≈ Type⟨t'⟩ : Typeω@k ->
    exists n, Γ ⊢ t ≈ t' : Level@n.
Proof.
  intros * H.
  assert (exists n, Γ ⊢ t : Level@n) as [n1 Ht] by (gen_presups; eapply wf_univ_lvl_inversion; eassumption).
  assert (exists n, Γ ⊢ t' : Level@n) as [n2 Ht'] by (gen_presups; eapply wf_univ_lvl_inversion; eassumption).
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  (** Both level terms move to the larger of their two sorts, where the
      equation is stated. *)
  assert (Γ ⊢ t : Level@(Nat.max n1 n2))
    by (eapply wf_exp_subtyp'; [ exact Ht | apply wf_subtyp_level; [ lia | exact HΓ ] ]).
  assert (Γ ⊢ t' : Level@(Nat.max n1 n2))
    by (eapply wf_exp_subtyp'; [ exact Ht' | apply wf_subtyp_level; [ lia | exact HΓ ] ]).
  exists (Nat.max n1 n2).
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq H) Hsem) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
  match goal with Hl : per_lvl ?l ?l' |- _ => destruct (per_lvl_reads _ _ Hl (length Γ)) as (L & HW & HW' & _) end.
  (** The two level terms have the same normal form *)
  eapply soundness_upto_proofs; [ eassumption | eassumption | | | reflexivity ];
    (eapply nbe_evaluated_intro; [ eassumption | apply eval_exp_level | eassumption
                                 | eapply read_nf_level_sort; eassumption | constructor ]).
Qed.

(** ** Subtyping of Universe Terms and Level Types

    The three universe rules and the rule for the types of levels, as a
    relation on universe terms and level types: large below large by the
    order on levels, small below small by the order on level terms, small
    below large, and [Level@m] below [Level@n] by the order on sorts. *)
Inductive univ_sub (Γ : ctx) : exp -> exp -> Prop :=
| univ_sub_large : forall i j, i <= j -> univ_sub Γ Typeω@i Typeω@j
| univ_sub_small : forall t t' n,
    Γ ⊢ t : Level@n ->
    Γ ⊢ t' : Level@n ->
    Γ ⊢ maxl t t' ≈ t' : Level@n ->
    univ_sub Γ Type⟨t⟩ Type⟨t'⟩
| univ_sub_small_large : forall t j n,
    Γ ⊢ t : Level@n ->
    univ_sub Γ Type⟨t⟩ Typeω@j
| univ_sub_level : forall m n, m <= n -> univ_sub Γ Level@m Level@n.
Hint Constructors univ_sub : mctt.

(** The two sides of [univ_sub]: a universe term or a type of levels. *)
Inductive sort_term : exp -> Prop :=
| sort_term_univ : forall U, univ_term U -> sort_term U
| sort_term_level : forall n, sort_term Level@n.
Hint Constructors sort_term : mctt.

Lemma univ_sub_sort_term : forall {Γ U V},
    univ_sub Γ U V -> sort_term U /\ sort_term V.
Proof. intros * []; split; first [ apply sort_term_level | apply sort_term_univ; constructor ]. Qed.

(** The types of levels are distinct from the universes and from [Π], and
    [Level@n] determines its sort: in each case the two values are related
    by [per_univ_elem] at the initial environment, which only relates values
    with the same head and, for the types of levels, the same sort. *)
Lemma exp_eq_level_typ_absurd : forall {Γ m i k},
    Γ ⊢ Level@m ≈ Typeω@i : Typeω@k ->
    False.
Proof.
  intros * H0; pose proof (completeness_fundamental_exp_eq _ _ _ _ H0) as H.
  destruct (rel_typ_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq H0) H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
Qed.

Lemma exp_eq_level_suniv_absurd : forall {Γ m t k},
    Γ ⊢ Level@m ≈ Type⟨t⟩ : Typeω@k ->
    False.
Proof.
  intros * H0; pose proof (completeness_fundamental_exp_eq _ _ _ _ H0) as H.
  destruct (rel_typ_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq H0) H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
Qed.

Lemma exp_eq_level_pi_absurd : forall {Γ m κ A B k},
    Γ ⊢ Level@m ≈ Π{κ} A B : Typeω@k ->
    False.
Proof.
  intros * H0; pose proof (completeness_fundamental_exp_eq _ _ _ _ H0) as H.
  destruct (rel_typ_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq H0) H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
Qed.

Lemma exp_eq_level_inj : forall {Γ m n k},
    Γ ⊢ Level@m ≈ Level@n : Typeω@k ->
    m = n.
Proof.
  intros * H0; pose proof (completeness_fundamental_exp_eq _ _ _ _ H0) as H.
  destruct (rel_typ_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq H0) H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  inversion Ha; subst; inversion Ha'; subst.
  invert_per_univ_elem HR.
  reflexivity.
Qed.

(** A [Π] is neither a universe term nor a type of levels. *)
Lemma pi_sort_term_absurd : forall {Γ κ A B U k},
    sort_term U ->
    Γ ⊢ Π{κ} A B ≈ U : Typeω@k ->
    False.
Proof.
  intros * [U' HU | n] H.
  - eapply pi_univ_term_absurd; eassumption.
  - eapply exp_eq_level_pi_absurd; symmetry; exact H.
Qed.

(** Two universe or level-type subtypings compose through an equation
    between the middle ones: the two tiers and the types of levels are
    distinct, the large tier is injective on levels, the small one on level
    terms and the types of levels on sorts. *)
Lemma univ_sub_trans_eq : forall {Γ U V U' W k},
    univ_sub Γ U V ->
    Γ ⊢ V ≈ U' : Typeω@k ->
    univ_sub Γ U' W ->
    univ_sub Γ U W.
Proof.
  intros * H1 Heq H2.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct H1 as [i j Hij | t1 t2 n Ht1 Ht2 H12 | t1 j n Ht1 | m1 m2 Hm12],
           H2 as [i' j' Hij' | t3 t4 n' Ht3 Ht4 H34 | t3 j' n' Ht3 | m3 m4 Hm34].
  (** The middle universes or level types have different heads: impossible. *)
  all: try solve [ exfalso;
                   (eapply exp_eq_typ_suniv_absurd + eapply exp_eq_level_typ_absurd
                    + eapply exp_eq_level_suniv_absurd);
                   (exact Heq + (symmetry; exact Heq)) ].
  - assert (j = i') as -> by mauto 3; constructor; lia.
  - (** The order on level terms through the equation of the middle ones:
        [t1 ≤ t2 ≈ t3 ≤ t4]. *)
    (** The two orders and the equation of the middle terms are at three
        sorts; all four terms move to the largest, where they compose. *)
    destruct (exp_eq_suniv_tm_inj Heq) as [m Heqt].
    set (N := Nat.max (Nat.max n n') m).
    assert (Hup : forall k M, k <= N -> Γ ⊢ M : Level@k -> Γ ⊢ M : Level@N)
      by (intros * ? ?; eapply wf_exp_subtyp'; [ eassumption | apply wf_subtyp_level; assumption ]).
    assert (HupE : forall k M M', k <= N -> Γ ⊢ M ≈ M' : Level@k -> Γ ⊢ M ≈ M' : Level@N)
      by (intros * ? ?; eapply wf_exp_eq_subtyp'; [ eassumption | apply wf_subtyp_level; assumption ]).
    assert (Ht1N : Γ ⊢ t1 : Level@N) by (apply (Hup n); [ subst N; lia | exact Ht1 ]).
    assert (Ht2N : Γ ⊢ t2 : Level@N) by (apply (Hup n); [ subst N; lia | exact Ht2 ]).
    assert (Ht3N : Γ ⊢ t3 : Level@N) by (apply (Hup n'); [ subst N; lia | exact Ht3 ]).
    assert (Ht4N : Γ ⊢ t4 : Level@N) by (apply (Hup n'); [ subst N; lia | exact Ht4 ]).
    assert (H12N : @lvl_sub gc_deps gc_stack N Γ t1 t2)
      by (apply (HupE n); [ subst N; lia | exact H12 ]).
    assert (H34N : @lvl_sub gc_deps gc_stack N Γ t3 t4)
      by (apply (HupE n'); [ subst N; lia | exact H34 ]).
    assert (HeqtN : Γ ⊢ t2 ≈ t3 : Level@N) by (apply (HupE m); [ subst N; lia | exact Heqt ]).
    assert (H23 : @lvl_sub gc_deps gc_stack N Γ t2 t3).
    { unfold lvl_sub.
      transitivity (maxl t3 t3);
        [ apply wf_exp_eq_maxl_cong; [ exact HeqtN | apply wf_exp_eq_refl; exact Ht3N ]
        | apply wf_exp_eq_maxl_idem; exact Ht3N ]. }
    econstructor; [ exact Ht1N | exact Ht4N |].
    change (@lvl_sub gc_deps gc_stack N Γ t1 t4).
    eapply (lvl_sub_trans Ht1N Ht3N Ht4N); [| exact H34N ].
    eapply (lvl_sub_trans Ht1N Ht2N Ht3N); [ exact H12N | exact H23 ].
  - econstructor; eassumption.
  - econstructor; eassumption.
  - assert (m2 = m3) as -> by (eapply exp_eq_level_inj; exact Heq); constructor; lia.
Qed.

(** [A] is below [B] among the types of levels other than [Π]s
    ([wf_subtyp_level]): [Level@m] below [Level@n], [m <= n], up to
    equations at [LevelSort].  A [Π] between types of levels is in the [Π]
    disjunct of [subtyp_spec]. *)
Definition level_sub_spec (Γ : ctx) (A B : typ) : Prop :=
  exists m n, m <= n /\ Γ ⊢ A ≈ Level@m : LevelSort /\ Γ ⊢ Level@n ≈ B : LevelSort.

(** A type of levels of another sort is of [LevelSort]. *)
Lemma level_type_sort_unique : forall {Γ M S}, type_sort S -> Γ ⊢ M : LevelSort -> Γ ⊢ M : S -> S = LevelSort.
Proof.
  intros * [k | |] HL HS; [ exfalso; exact (level_type_not_large HL HS) | exfalso; exact (level_type_not_prop HL HS) | reflexivity ].
Qed.

(** An equation at a sort next to a type of the sort of an evaluated kind
    [κc] is at that sort, at some index: a large universe for a relevant
    [κc] ([exp_eq_sort_large]), [LevelSort] for the kind of levels
    ([level_type_sort_unique]). *)
Lemma exp_eq_kind_sort : forall {Γ A M S κc k},
    type_sort S -> evaluated_kind κc -> Γ ⊢ A ≈ M : S ->
    Γ ⊢ A : abs_kind_sort κc Typeω@k \/ Γ ⊢ M : abs_kind_sort κc Typeω@k ->
    exists k', Γ ⊢ A ≈ M : abs_kind_sort κc Typeω@k'.
Proof.
  intros * HS [] H Hk; cbn [abs_kind_sort] in *; [ exact (exp_eq_sort_large HS H Hk) |].
  exists 0; assert (Γ ⊢ A : S /\ Γ ⊢ M : S) as [HA HM] by (gen_presups; split; assumption).
  destruct Hk as [Hk | Hk]; [ rewrite <- (level_type_sort_unique HS Hk HA) | rewrite <- (level_type_sort_unique HS Hk HM) ];
    exact H.
Qed.

(** Transitivity at the sort of an evaluated kind, at the larger index. *)
Lemma exp_eq_trans_kind_max : forall {Γ A A' A'' κc i i'},
    evaluated_kind κc ->
    Γ ⊢ A ≈ A' : abs_kind_sort κc Typeω@i -> Γ ⊢ A' ≈ A'' : abs_kind_sort κc Typeω@i' ->
    Γ ⊢ A ≈ A'' : abs_kind_sort κc Typeω@(max i i').
Proof. intros * [] H1 H2; cbn [abs_kind_sort] in *; [ exact (exp_eq_trans_typ_max H1 H2) | etransitivity; eassumption ]. Qed.

(** [Π] is injective at the sort of an evaluated codomain kind. *)
Lemma exp_eq_pi_kind_inversion : forall {Γ κ κ' κc A B A' B' i},
    evaluated_kind κc ->
    Γ ⊢ a_pi κ κc A B ≈ a_pi κ' κc A' B' : abs_kind_sort κc Typeω@i ->
    κ = κ' /\ (exists S, sort_kind S κ /\ Γ ⊢ A ≈ A' : S) /\ Γ ▹{κ} A ⊢ B ≈ B' : abs_kind_sort κc Typeω@i.
Proof.
  intros * [] H; cbn [abs_kind_sort] in *.
  - destruct (exp_eq_pi_inversion H) as (<- & HA & HB).
    split; [ reflexivity | split; [ exists (abs_kind_sort κ Typeω@i); split; [ apply sort_kind_abs_kind_sort | exact HA ] | exact HB ] ].
  - (** the domain of a [Π] between types of levels is one ([pi_kinds]) *)
    destruct (exp_eq_pi_level_inversion H) as (<- & HA & HB).
    assert (exists C, Γ ⊢ a_pi κ ak_level A B : C) as [C HC] by (gen_presups; eexists; eassumption).
    destruct (wf_pi_inversion_at HC) as [U _ _ _ Hk _]; inversion Hk; subst.
    split; [ reflexivity | split; [ exists LevelSort; split; [ constructor | exact HA ] | exact HB ] ].
Qed.

(** The three universe rules and the level rule are one disjunct, on
    universe terms and level types: inside a tier it is the order on levels
    or on level terms, from the small tier to the large one it is
    [wf_subtyp_small_large], and between the types of levels other than
    [Π]s it is the order on sorts.  A [Π] into an evaluated kind, into a
    universe or between types of levels, is the [Π] disjunct, its
    equations at the sort of its codomain's kind.  An equation of types,
    and the equation of the domains of two [Π]s, is at a sort
    ([type_sort]): a domain may be a proposition. *)
Lemma subtyp_spec : forall {Γ A B},
    Γ ⊢ A ⊆ B ->
    (exists S, type_sort S /\ Γ ⊢ A ≈ B : S) \/
      (exists U V, (exists k, Γ ⊢ A ≈ U : Typeω@k) /\ (exists k, Γ ⊢ V ≈ B : Typeω@k) /\ univ_sub Γ U V) \/
      (exists κ κc A1 A2 B1 B2, evaluated_kind κc /\
         (exists k, Γ ⊢ A ≈ a_pi κ κc A1 A2 : abs_kind_sort κc Typeω@k) /\
         (exists k, Γ ⊢ a_pi κ κc B1 B2 ≈ B : abs_kind_sort κc Typeω@k) /\
         (exists S, sort_kind S κ /\ Γ ⊢ A1 ≈ B1 : S) /\ Γ ▹{κ} B1 ⊢ A2 ⊆ B2) \/
      level_sub_spec Γ A B.
Proof.
  (** The global context is an index of [wf_subtyp], so fix it for the induction. *)
  intros * H.
  remember gc_deps as Θ0 eqn:HΘ; remember gc_stack as Ξ0 eqn:HΞ.
  induction H; subst;
    repeat match goal with IH : ?x = ?x -> _ |- _ => specialize (IH eq_refl) end.
  - left; eexists; split; eassumption.
  - (** Transitivity: sixteen combinations of the four cases.  The middle
        type is of a large universe next to a universe, of [LevelSort] next
        to a type of levels, and of the sort of the codomain's kind next to
        a [Π]; a type of levels is of no large universe
        ([level_type_not_large]), which rules out the mixed combinations
        but [Π]s into levels next to types of levels, ruled out by the
        heads ([exp_eq_level_pi_level_absurd]).  An equation at a sort next
        to one of the other cases is at that case's sort
        ([exp_eq_sort_large], [exp_eq_kind_sort],
        [level_type_sort_unique]). *)
    destruct IHwf_subtyp1 as [(S1 & HS1 & E1) | [(u & v & [ku Hu] & [kv Hv] & Huv)
      | [(κ1 & κc1 & A1 & A2 & B1 & B2 & Hev1 & [ka Ha1] & [kb Hb1] & (S3 & HS3 & Hab1) & Hsub1) | (m1 & n1 & Hmn1 & Hl1 & Hr1)]]],
      IHwf_subtyp2 as [(S2 & HS2 & E2) | [(u' & v' & [ku' Hu'] & [kv' Hv'] & Hu'v')
      | [(κ2 & κc2 & C1 & C2 & D1 & D2 & Hev2 & [kc Hc2] & [kd Hd2] & (S4 & HS4 & Hcd2) & Hsub2) | (m2 & n2 & Hmn2 & Hl2 & Hr2)]]].
    (** [≈] then [≈]. *)
    + left; exact (exp_eq_trans_sort HS1 HS2 E1 E2).
    (** [≈] then a universe. *)
    + assert (exists k, Γ ⊢ M ≈ M' : Typeω@k) as [k E1']
        by (eapply exp_eq_sort_large; [ exact HS1 | exact E1 | right; gen_presups; eassumption ]).
      right; left; exists u', v'; repeat split; [| | exact Hu'v' ];
        eexists; [ eapply exp_eq_trans_typ_max; eassumption | eassumption ].
    (** [≈] then a [Π]. *)
    + assert (exists k, Γ ⊢ M ≈ M' : abs_kind_sort κc2 Typeω@k) as [k E1']
        by (eapply exp_eq_kind_sort; [ exact HS1 | exact Hev2 | exact E1 | right; gen_presups; eassumption ]).
      right; right; left; exists κ2, κc2, C1, C2, D1, D2;
        repeat split; [ exact Hev2 | | | exists S4; split; assumption | exact Hsub2 ];
        eexists; [ eapply exp_eq_trans_kind_max; eassumption | eassumption ].
    (** [≈] then a type of levels. *)
    + assert (HM'L : Γ ⊢ M' : LevelSort) by (gen_presups; assumption).
      assert (HM'S : Γ ⊢ M' : S1) by (gen_presups; assumption).
      rewrite (level_type_sort_unique HS1 HM'L HM'S) in E1.
      right; right; right; exists m2, n2; repeat split; [ exact Hmn2 | etransitivity; eassumption | exact Hr2 ].
    (** A universe then [≈]. *)
    + assert (exists k, Γ ⊢ M' ≈ M'' : Typeω@k) as [k E2']
        by (eapply exp_eq_sort_large; [ exact HS2 | exact E2 | left; gen_presups; eassumption ]).
      right; left; exists u, v; repeat split; [| | exact Huv ];
        eexists; [ eassumption | eapply exp_eq_trans_typ_max; eassumption ].
    (** A universe then a universe: the two middle universes are equal, so
        the two subtypings compose. *)
    + right; left; exists u, v'; repeat split;
        [ eexists; eassumption | eexists; eassumption
        | eapply univ_sub_trans_eq; [ exact Huv | eapply exp_eq_trans_typ_max; [ exact Hv | exact Hu' ] | exact Hu'v' ] ].
    (** A universe then a [Π]: impossible, a [Π] is not a universe term,
        and a [Π] into levels is of no large universe. *)
    + exfalso; destruct Hev2; cbn [abs_kind_sort] in *.
      * pose proof (univ_sub_sort_term Huv) as [_ Hvt].
        eapply (pi_sort_term_absurd Hvt), exp_eq_trans_typ_max; [ symmetry; exact Hc2 | symmetry; exact Hv ].
      * assert (Γ ⊢ M' : LevelSort) by (gen_presups; assumption).
        assert (Γ ⊢ M' : Typeω@kv) by (gen_presups; assumption).
        eapply level_type_not_large; eassumption.
    (** A universe then a type of levels: impossible. *)
    + exfalso; assert (Γ ⊢ M' : LevelSort) by (gen_presups; assumption).
      assert (Γ ⊢ M' : Typeω@kv) by (gen_presups; assumption).
      eapply level_type_not_large; eassumption.
    (** A [Π] then [≈]. *)
    + assert (exists k, Γ ⊢ M' ≈ M'' : abs_kind_sort κc1 Typeω@k) as [k E2']
        by (eapply exp_eq_kind_sort; [ exact HS2 | exact Hev1 | exact E2 | left; gen_presups; eassumption ]).
      right; right; left; exists κ1, κc1, A1, A2, B1, B2;
        repeat split; [ exact Hev1 | | | exists S3; split; assumption | exact Hsub1 ];
        eexists; [ eassumption | eapply exp_eq_trans_kind_max; eassumption ].
    (** A [Π] then a universe: impossible. *)
    + exfalso; destruct Hev1; cbn [abs_kind_sort] in *.
      * pose proof (univ_sub_sort_term Hu'v') as [Hu't _].
        eapply (pi_sort_term_absurd Hu't), exp_eq_trans_typ_max; [ exact Hb1 | exact Hu' ].
      * assert (Γ ⊢ M' : LevelSort) by (gen_presups; assumption).
        assert (Γ ⊢ M' : Typeω@ku') by (gen_presups; assumption).
        eapply level_type_not_large; eassumption.
    (** A [Π] then a [Π]: the codomain kinds agree (a type of levels is of
        no large universe), the two middle [Π]s are equal, so the
        development continues with the domain and codomain of the one we
        keep. *)
    + assert (κc1 = κc2) as <-.
      { destruct Hev1, Hev2; cbn [abs_kind_sort] in *; try reflexivity; exfalso;
          (assert (Γ ⊢ M' : LevelSort) by (gen_presups; assumption));
          (assert (exists k, Γ ⊢ M' : Typeω@k) as [? ?] by (gen_presups; eexists; eassumption));
          eapply level_type_not_large; eassumption. }
      destruct (exp_eq_pi_kind_inversion Hev1 (exp_eq_trans_kind_max Hev1 Hb1 Hc2)) as (<- & (S5 & HS5 & Hbc) & HB2).
      destruct (exp_eq_trans_sort_kind HS5 HS4 Hbc Hcd2) as (S6 & HS6 & Hbd).
      right; right; left.
      exists κ1, κc1, A1, A2, D1, D2; repeat split; [ exact Hev1 | eexists; eassumption | eexists; eassumption | |].
      * exact (exp_eq_trans_sort_kind HS3 HS6 Hab1 Hbd).
      * (** The two codomain refinements live in contexts extended by the three
            equal domains, so [ctxsub_subtyp] moves both into the one we chose. *)
        assert (HD : Γ ▹{κ1} D1 ⊢ˢ Id : Γ ▹{κ1} B1) by (eapply sub_id_extend_of_exp_eq; [ exact HS6 | symmetry; exact Hbd ]).
        etransitivity; [| exact Hsub2 ].
        etransitivity; eapply ctxsub_subtyp; [ exact HD | exact Hsub1 | exact HD |].
        eapply proj1, (wf_subtyp_of_exp_eq _ _ _ _ _ (abs_kind_sort κc1 Typeω@(Nat.max kb kc)));
          [ | | destruct Hev1; constructor | exact HB2 ]; gen_presups; eassumption.
    (** A [Π] then a type of levels: impossible, by the sorts or the heads. *)
    + exfalso; destruct Hev1; cbn [abs_kind_sort] in *.
      * assert (Γ ⊢ M' : LevelSort) by (gen_presups; assumption).
        assert (Γ ⊢ M' : Typeω@kb) by (gen_presups; assumption).
        eapply level_type_not_large; eassumption.
      * eapply exp_eq_level_pi_level_absurd; symmetry; etransitivity; eassumption.
    (** A type of levels then [≈]. *)
    + assert (HM'L : Γ ⊢ M' : LevelSort) by (gen_presups; assumption).
      assert (HM'S : Γ ⊢ M' : S2) by (gen_presups; assumption).
      rewrite (level_type_sort_unique HS2 HM'L HM'S) in E2.
      right; right; right; exists m1, n1; repeat split; [ exact Hmn1 | exact Hl1 | etransitivity; eassumption ].
    (** A type of levels then a universe: impossible. *)
    + exfalso; assert (Γ ⊢ M' : LevelSort) by (gen_presups; assumption).
      assert (Γ ⊢ M' : Typeω@ku') by (gen_presups; assumption).
      eapply level_type_not_large; eassumption.
    (** A type of levels then a [Π]: impossible, by the sorts or the heads. *)
    + exfalso; destruct Hev2; cbn [abs_kind_sort] in *.
      * assert (Γ ⊢ M' : LevelSort) by (gen_presups; assumption).
        assert (Γ ⊢ M' : Typeω@kc) by (gen_presups; assumption).
        eapply level_type_not_large; eassumption.
      * eapply exp_eq_level_pi_level_absurd; etransitivity; eassumption.
    (** A type of levels then a type of levels: the middle sorts agree
        ([exp_eq_level_inj_level_sort]). *)
    + assert (n1 = m2) as <- by (eapply exp_eq_level_inj_level_sort; etransitivity; eassumption).
      right; right; right; exists m1, n2; repeat split; [ lia | exact Hl1 | exact Hr2 ].
  (** The three universe rules and the level rule, at their own terms. *)
  - right; left; exists Typeω@i, Typeω@j;
      split; [| split ]; [ eexists; mauto 3 | eexists; mauto 3 | constructor; lia ].
  - right; left; exists Type⟨M⟩, Type⟨M'⟩;
      split; [| split ]; [ eexists; mauto 3 | eexists; mauto 3 | econstructor; eassumption ].
  - right; right; right; exists m, n; split; [ assumption | split; apply wf_exp_eq_refl; mauto 3 ].
  - right; left; exists Type⟨M⟩, Typeω@i;
      split; [| split ]; [ eexists; mauto 3 | eexists; mauto 3 | econstructor; eassumption ].
  - (** The [Π] rule, at its own domains and codomains, at the sort of its
        codomain's kind. *)
    assert (⊢ Γ) by (gen_presups; assumption).
    right; right; left; exists κd, κc, A, B, A', B'.
    match goal with Hev : evaluated_kind ?κc |- _ => pose proof Hev as Hev0; destruct Hev end.
    all: repeat split; first [ exact Hev0 | exists i | exists (abs_kind_sort κd Typeω@i); split; [ apply sort_kind_abs_kind_sort | eassumption ] | assumption ].
    all: apply wf_exp_eq_refl; eapply wf_pi with (U := Typeω@i); first [ eassumption | solve [ mauto 3 ] | constructor ].
Qed.

Hint Resolve subtyp_spec : mctt.

(** [subtyp_spec] where one side is of a large universe: an equation is at
    a large universe ([exp_eq_sort_large]). *)
Corollary subtyp_spec_large : forall {Γ A B k},
    Γ ⊢ A ⊆ B -> Γ ⊢ A : Typeω@k \/ Γ ⊢ B : Typeω@k ->
    (exists k, Γ ⊢ A ≈ B : Typeω@k) \/
      (exists U V, (exists k, Γ ⊢ A ≈ U : Typeω@k) /\ (exists k, Γ ⊢ V ≈ B : Typeω@k) /\ univ_sub Γ U V) \/
      (exists κ A1 A2 B1 B2, (exists k, Γ ⊢A ≈ Π{κ} A1 A2 : Typeω@k) /\ (exists k, Γ ⊢ Π{κ} B1 B2 ≈ B : Typeω@k) /\
         (exists S, sort_kind S κ /\ Γ ⊢ A1 ≈ B1 : S) /\ Γ ▹{κ} B1 ⊢ A2 ⊆ B2).
Proof.
  intros * H Hk.
  destruct (subtyp_spec H) as [(S & HS & Heq) | [Hr | [(κ & κc & A1 & A2 & B1 & B2 & Hev & [ka Ha] & [kb Hb] & Hd & Hc) | (m & n & _ & HAL & HBL)]]];
    [ left; exact (exp_eq_sort_large HS Heq Hk) | right; left; exact Hr | |].
  - (** A [Π] into levels is a type of levels, of no large universe. *)
    destruct Hev; cbn [abs_kind_sort] in *.
    + right; right; exists κ, A1, A2, B1, B2; repeat split; [ eexists; exact Ha | eexists; exact Hb | exact Hd | exact Hc ].
    + exfalso; destruct Hk as [Hk | Hk];
        [ assert (Γ ⊢ A : LevelSort) by (gen_presups; assumption) | assert (Γ ⊢ B : LevelSort) by (gen_presups; assumption) ];
        eapply level_type_not_large; eassumption.
  - (** Between types of levels, of no large universe *)
    exfalso; destruct Hk as [Hk | Hk];
      [ assert (Γ ⊢ A : LevelSort) by (gen_presups; assumption) | assert (Γ ⊢ B : LevelSort) by (gen_presups; assumption) ];
      eapply level_type_not_large; eassumption.
Qed.

(** The types of levels are ordered by their sorts. *)
Lemma subtyp_level_inv : forall {Γ m n},
    Γ ⊢ Level@m ⊆ Level@n ->
    m <= n.
Proof.
  intros * H.
  destruct (subtyp_at_initial_env H) as (ρ & a & a' & k & _ & Ha & Ha' & Hs).
  inversion Ha; subst; inversion Ha'; subst.
  inversion Hs; subst; try assumption.
  match goal with Hp : per_prop _ _ |- _ => destruct Hp as [Hp _ _]; cbn in Hp; discriminate end.
Qed.

(** An inductive type is neither a [Π] nor a universe nor a type of levels,
    and is below only an equal one. *)
Lemma exp_eq_ind_pi_absurd : forall {Γ p m X κ A B k},
    Γ ⊢ apps (a_ind p m) X ≈ Π{κ} A B : Typeω@k ->
    False.
Proof.
  intros * H0; pose proof (completeness_fundamental_exp_eq _ _ _ _ H0) as H.
  destruct (rel_typ_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq H0) H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  destruct (eval_ind_value _ _ _ _ _ Ha) as [? ->].
  inversion Ha'; subst.
  invert_per_univ_elem HR.
Qed.

Lemma exp_eq_ind_sort_absurd : forall {Γ p m X U k},
    sort_term U ->
    Γ ⊢ apps (a_ind p m) X ≈ U : Typeω@k ->
    False.
Proof.
  intros * HU H0; pose proof (completeness_fundamental_exp_eq _ _ _ _ H0) as H.
  destruct (rel_typ_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq H0) H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  destruct (eval_ind_value _ _ _ _ _ Ha) as [? ->].
  destruct HU as [U' HU' | n]; [ destruct HU' |]; inversion Ha'; subst; invert_per_univ_elem HR.
Qed.

(** An inductive type is below another of the same former only by an
    equation, at its sort: a universe, or [Prop] for a propositional
    one. *)
Lemma type_value_not_level : forall {Γ M}, Γ ⊢ M : LevelSort ->
    (forall ρ a, ⟦ M ⟧ ρ ↘ a -> ~ level_code a) -> False.
Proof.
  intros * H Hn.
  pose proof (completeness_fundamental_exp _ _ _ H) as Hs; pose proof Hs as [R HR _ _].
  pose proof (wf_ctx_scoped_exp H) as HsΓ.
  destruct (per_ctx_then_per_env_initial_env HR HsΓ HsΓ) as (ρ & ρ' & _ & _ & Hρ).
  destruct (rel_exp_of_level_sort_inversion_simple_at HR Hs _ _ Hρ) as (a & _ & Ha & _ & (Hl & _)).
  exact (Hn _ _ Ha Hl).
Qed.

(** An inductive type is no type of levels: its value is no type of
    levels ([level_code_head]). *)
Lemma ind_type_not_level : forall {Γ p m X}, Γ ⊢ apps (a_ind p m) X : LevelSort -> False.
Proof.
  intros * H; apply (type_value_not_level H); intros ρ a Ha Hl.
  destruct (eval_ind_value _ _ _ _ _ Ha) as [ms ->].
  destruct (level_code_head _ Hl) as [(? & [=]) | (? & ? & ? & [=])].
Qed.

(** Nor is a record type. *)
Lemma record_type_not_level : forall {Γ p X}, Γ ⊢ apps (a_record p) X : LevelSort -> False.
Proof.
  intros * H; apply (type_value_not_level H); intros ρ a Ha Hl.
  destruct (eval_record_value _ _ _ _ Ha) as [ms ->].
  destruct (level_code_head _ Hl) as [(? & [=]) | (? & ? & ? & [=])].
Qed.

Lemma subtyp_ind_inv : forall {Γ p m X Y},
    Γ ⊢ apps (a_ind p m) X ⊆ apps (a_ind p m) Y ->
    exists S, type_sort S /\ Γ ⊢ apps (a_ind p m) X ≈ apps (a_ind p m) Y : S.
Proof.
  intros * H.
  apply subtyp_spec in H as [Heq | [(U & V & [k1 HU] & [k2 HV] & Hs) | [(κ1 & κc & A1 & A2 & B1 & B2 & Hev & [k1 HA] & _) | (m1 & n1 & _ & HL & _)]]].
  - exact Heq.
  - exfalso; destruct (univ_sub_sort_term Hs) as [HUt _]; eapply exp_eq_ind_sort_absurd; [ exact HUt | exact HU ].
  - exfalso; destruct Hev; cbn [abs_kind_sort] in *; [ eapply exp_eq_ind_pi_absurd; exact HA |].
    eapply ind_type_not_level; gen_presups; eassumption.
  - exfalso; eapply ind_type_not_level; gen_presups; eassumption.
Qed.

(** A type below an inductive type normalises to an inductive type, at the
    normal forms of parameters equal to the ones below. *)
Lemma subtyp_ind_nf : forall {Γ T p m D Mm Ps W}, Γ ⊢ T ⊆ apps (a_ind p m) Ps -> ind_lookup gc_deps gc_stack p = Some D ->
    ind_member D m = Some Mm ->
    List.length Ps = im_np D Mm ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some A -> Γ ⊢ P : A) ->
    nbe_ty_f Γ T W ->
    exists Rs, W = nf_indty p m Rs /\ List.length Rs = im_np D Mm /\
      forall k P R A V, List.nth_error Ps k = Some P -> List.nth_error Rs k = Some R ->
        List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some A -> nbe_f Γ P A V -> nf_eq_upto_proofs V R.
Proof.
  intros * Hs Hl Hm HPl HPt HW.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  apply subtyp_spec in Hs as [(S & HS & Heq) | [(U & V & [k1 HU] & [k2 HV] & Hsu) | [(κ1 & κc & A1 & A2 & B1 & B2 & Hev & _ & [k2 Hb] & _) | (m1 & n1 & _ & _ & HL)]]].
  - (** [T] reads back as the inductive type does, up to proofs: at
        parameters equal up to proofs to the inductive type's *)
    destruct (completeness_ty_sort HS Heq) as (W1 & W2 & HW1 & HW2 & HE).
    pose proof (functional_nbe_ty _ _ _ _ HW HW1) as <-.
    destruct (nbe_ty_ind_params _ _ _ _ _ _ _ Hl Hm HΓ HPl HPt HW2) as (Rs2 & -> & HRl & HP).
    destruct W; try (unfold nf_eq_upto_proofs in HE; cbn in HE; discriminate).
    apply nf_indty_upto_proofs_inv in HE as (-> & -> & HE).
    match goal with |- exists Rs, nf_indty _ _ ?L = _ /\ _ => exists L end.
    split; [ reflexivity |]; split; [ rewrite (nfs_eq_upto_proofs_length _ _ HE); exact HRl |].
    intros k P R A V HPk HRk HAk HV.
    destruct (nfs_eq_upto_proofs_nth _ _ _ _ HE HRk) as (R2 & HR2 & ER).
    pose proof (HP _ _ _ _ _ HPk HAk HR2 HV) as E.
    etransitivity; [ exact E | symmetry; exact ER ].
  - exfalso; destruct (univ_sub_sort_term Hsu) as [_ HVt].
    eapply exp_eq_ind_sort_absurd; [ exact HVt | symmetry; exact HV ].
  - exfalso; destruct Hev; cbn [abs_kind_sort] in *; [ eapply exp_eq_ind_pi_absurd; symmetry; exact Hb |].
    eapply ind_type_not_level; gen_presups; eassumption.
  - exfalso; eapply ind_type_not_level; gen_presups; eassumption.
Qed.

(** ** The Parameters of a Record Type

    As for inductive types: the normal form of a record type is the type
    former at the normal forms of its parameters, each equal to its
    parameter; so equal record types have equal parameters, and a record
    type is neither a [Π] nor a universe nor a type of levels. *)

(** A record found from a well-formed context: typed, closed, and its
    parameters a telescope over the context. *)
Lemma record_params_facts : forall Γ p R, ⊢ Γ -> record_lookup gc_deps gc_stack p = Some R ->
    record_typed gc_deps gc_stack R /\ record_closed R /\ ⊢ record_params R ++ Γ.
Proof.
  intros * HΓ Hl.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  pose proof (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ Hl) as Ht.
  pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
  split; [ exact Ht | split; [ exact Hc |] ].
  pose proof (record_fctx_app_wf _ _ R 0 Γ ltac:(lia) Hc (typed_params_ass _ _ _ Ht)
                (record_typed_fctx_wf _ _ _ Ht _ (le_n _)) HΓ) as H.
  change (record_fctx R 0) with (@nil centry) in H; exact H.
Qed.

Lemma nbe_ty_record_params : forall Γ p R Ms W, record_lookup gc_deps gc_stack p = Some R -> ⊢ Γ ->
    List.length Ms = List.length (record_params R) ->
    (forall j P T, List.nth_error Ms j = Some P -> List.nth_error (tele_insts (record_params R) Id Ms) j = Some T -> Γ ⊢ P : T) ->
    nbe_ty_f Γ (apps (a_record p) Ms) W ->
    exists Rs, W = nf_record p Rs /\ List.length Rs = List.length (record_params R) /\
      forall j P T Q V, List.nth_error Ms j = Some P -> List.nth_error (tele_insts (record_params R) Id Ms) j = Some T ->
        List.nth_error Rs j = Some Q -> nbe_f Γ P T V -> nf_eq_upto_proofs V Q.
Proof.
  intros * Hl HΓ HMl HMt [ρ a Hρ Ha Hr].
  destruct (eval_record_apps_args _ _ _ _ Ha) as (vs & Hvs & ->).
  inversion Hr; subst.
  match goal with H1 : record_lookup _ _ _ = Some _, H3 : Rps _ at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Ps |- _ =>
    rewrite Hl in H1; injection H1 as <-; rename H3 into Hps; exists Ps end.
  split; [ reflexivity | split ].
  - rewrite (read_ps_length_nf _ _ _ _ _ Hps), (read_ps_length _ _ _ _ _ Hps), List.length_rev; reflexivity.
  - exact (nbe_params_at_telescope _ _ _ _ _ _ (record_evaluated_params_telescope _ _ _ HΓ Hl) HMl HMt Hρ Hvs Hps).
Qed.

(** A type whose normal form is a record type is equal to the type former
    at typed parameters, equal to the normal form's ([glu_nfs_eq_at]): the
    gluing of the record type at the identity. *)
Lemma typ_record_shape : forall Γ T i p Rs, Γ ⊢ T : Typeω@i -> nbe_ty_f Γ T (nf_record p Rs) ->
    exists R Ps, record_lookup gc_deps gc_stack p = Some R /\ List.length Ps = List.length (record_params R) /\
      (forall j P A, List.nth_error Ps j = Some P -> List.nth_error (tele_insts (record_params R) Id Ps) j = Some A -> Γ ⊢ P : A) /\
      Γ ⊢ T ≈ apps (a_record p) Ps : Typeω@i /\ exps_eq_at Γ (record_params R) Ps (List.map nf_to_exp Rs).
Proof.
  intros * HT HW.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  inversion HW as [ρ a Hinit Ea HRa]; subst.
  inversion HRa; subst.
  destruct (soundness_fundamental_ctx _ HΓ) as [Sb HSb].
  pose proof (initial_env_glu_rel_exp Hinit HSb) as Hσ.
  destruct (Soundness.Inductives.Args.glu_rel_typ_at _ _ _ _ _ _ _ HSb (soundness_fundamental_exp _ _ _ HT) Hσ) as (_ & a' & Ea' & Hpa & HPa).
  assert (a' = d_record p ns) as -> by (eapply functional_eval_exp; eassumption).
  destruct (per_univ_glu_univ_elem _ _ Hpa) as (P & El & Hg).
  pose proof (HPa P El Hg) as HP; rewrite exp_sub_id in HP.
  invert_glu_univ_elem Hg.
  match goal with H : _ <∙> record_glu_typ_pred _ _ _ _ _ _ |- _ => apply H in HP end.
  destruct HP as (Ps & [Heq HK]).
  assert (Hid : Γ ⊢ᵏ wk_id : Γ) by mauto 3.
  destruct (HK Γ wk_id Hid) as [Htop _ _].
  rewrite map_wk_id in Htop.
  destruct Htop as [HPl HPt Hrb].
  match goal with H : record_lookup _ _ p = Some ?R0, H' : record_lookup _ _ p = Some ?R1 |- _ =>
    assert (R0 = R1) as -> by congruence end.
  eexists _, Ps; split; [ eassumption | split; [ exact HPl | split; [ exact HPt | split; [ exact Heq |] ] ] ].
  (** The parameters' readback, the normal form's ([params_glu_top]) *)
  match goal with Hr : Rps _ at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ Rs |- _ => pose proof (Hrb Γ wk_id Rs Hid Hr) as H' end.
  rewrite map_wk_id in H'; exact H'.
Qed.

Corollary exp_eq_record_apps_inv : forall Γ p R X Y i, record_lookup gc_deps gc_stack p = Some R ->
    Γ ⊢ apps (a_record p) X ≈ apps (a_record p) Y : Typeω@i ->
    List.length X = List.length (record_params R) -> List.length Y = List.length (record_params R) ->
    (forall j P T, List.nth_error X j = Some P -> List.nth_error (tele_insts (record_params R) Id X) j = Some T -> Γ ⊢ P : T) ->
    (forall j P T, List.nth_error Y j = Some P -> List.nth_error (tele_insts (record_params R) Id Y) j = Some T -> Γ ⊢ P : T) ->
    exps_eq_at Γ (record_params R) X Y.
Proof.
  intros * Hl H HXl HYl HXt HYt.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct (record_evaluated_params_telescope _ _ _ HΓ Hl) as [HCa _ _ HCΓ].
  destruct (completeness_ty H) as (W & W' & HWX & HWY & HE).
  destruct (nbe_ty_record_params _ _ _ _ _ Hl HΓ HXl HXt HWX) as (Rs & -> & HRl & HX).
  destruct (nbe_ty_record_params _ _ _ _ _ Hl HΓ HYl HYt HWY) as (Rs' & -> & _ & HY).
  apply nf_record_upto_proofs_inv in HE as (_ & HE).
  eapply exps_eq_at_of_params_up_to_proofs; eassumption.
Qed.

Lemma exp_eq_record_pi_absurd : forall {Γ p X κ A B k},
    Γ ⊢ apps (a_record p) X ≈ Π{κ} A B : Typeω@k ->
    False.
Proof.
  intros * H0; pose proof (completeness_fundamental_exp_eq _ _ _ _ H0) as H.
  destruct (rel_typ_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq H0) H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  destruct (eval_record_value _ _ _ _ Ha) as [? ->].
  inversion Ha'; subst.
  invert_per_univ_elem HR.
Qed.

Lemma exp_eq_record_sort_absurd : forall {Γ p X U k},
    sort_term U ->
    Γ ⊢ apps (a_record p) X ≈ U : Typeω@k ->
    False.
Proof.
  intros * HU H0; pose proof (completeness_fundamental_exp_eq _ _ _ _ H0) as H.
  destruct (rel_typ_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq H0) H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  destruct (eval_record_value _ _ _ _ Ha) as [? ->].
  destruct HU as [U' HU' | n]; [ destruct HU' |]; inversion Ha'; subst; invert_per_univ_elem HR.
Qed.

(** A record type is below another of the same former only by an
    equation, at its sort, as for inductive types. *)
Lemma subtyp_record_inv : forall {Γ p X Y},
    Γ ⊢ apps (a_record p) X ⊆ apps (a_record p) Y ->
    exists S, type_sort S /\ Γ ⊢ apps (a_record p) X ≈ apps (a_record p) Y : S.
Proof.
  intros * H.
  apply subtyp_spec in H as [Heq | [(U & V & [k1 HU] & [k2 HV] & Hs) | [(κ1 & κc & A1 & A2 & B1 & B2 & Hev & [k1 HA] & _) | (m1 & n1 & _ & HL & _)]]].
  - exact Heq.
  - exfalso; destruct (univ_sub_sort_term Hs) as [HUt _]; eapply exp_eq_record_sort_absurd; [ exact HUt | exact HU ].
  - exfalso; destruct Hev; cbn [abs_kind_sort] in *; [ eapply exp_eq_record_pi_absurd; exact HA |].
    eapply record_type_not_level; gen_presups; eassumption.
  - exfalso; eapply record_type_not_level; gen_presups; eassumption.
Qed.

(** A type below a record type normalises to that record type, at the
    normal forms of parameters equal to the ones below. *)
Lemma subtyp_record_nf : forall {Γ T p R Ps W}, Γ ⊢ T ⊆ apps (a_record p) Ps -> record_lookup gc_deps gc_stack p = Some R ->
    List.length Ps = List.length (record_params R) ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (record_params R) Id Ps) k = Some A -> Γ ⊢ P : A) ->
    nbe_ty_f Γ T W ->
    exists Rs, W = nf_record p Rs /\ List.length Rs = List.length (record_params R) /\
      forall k P Q A V, List.nth_error Ps k = Some P -> List.nth_error Rs k = Some Q ->
        List.nth_error (tele_insts (record_params R) Id Ps) k = Some A -> nbe_f Γ P A V -> nf_eq_upto_proofs V Q.
Proof.
  intros * Hs Hl HPl HPt HW.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  apply subtyp_spec in Hs as [(S & HS & Heq) | [(U & V & [k1 HU] & [k2 HV] & Hsu) | [(κ1 & κc & A1 & A2 & B1 & B2 & Hev & _ & [k2 Hb] & _) | (m1 & n1 & _ & _ & HL)]]].
  - (** As for inductive types ([subtyp_ind_nf]) *)
    destruct (completeness_ty_sort HS Heq) as (W1 & W2 & HW1 & HW2 & HE).
    pose proof (functional_nbe_ty _ _ _ _ HW HW1) as <-.
    destruct (nbe_ty_record_params _ _ _ _ _ Hl HΓ HPl HPt HW2) as (Rs2 & -> & HRl & HP).
    destruct W; try (unfold nf_eq_upto_proofs in HE; cbn in HE; discriminate).
    apply nf_record_upto_proofs_inv in HE as (-> & HE).
    match goal with |- exists Rs, nf_record _ ?L = _ /\ _ => exists L end.
    split; [ reflexivity |]; split; [ rewrite (nfs_eq_upto_proofs_length _ _ HE); exact HRl |].
    intros k P Q A V HPk HQk HAk HV.
    destruct (nfs_eq_upto_proofs_nth _ _ _ _ HE HQk) as (Q2 & HQ2 & EQ).
    pose proof (HP _ _ _ _ _ HPk HAk HQ2 HV) as E.
    etransitivity; [ exact E | symmetry; exact EQ ].
  - exfalso; destruct (univ_sub_sort_term Hsu) as [_ HVt].
    eapply exp_eq_record_sort_absurd; [ exact HVt | symmetry; exact HV ].
  - exfalso; destruct Hev; cbn [abs_kind_sort] in *; [ eapply exp_eq_record_pi_absurd; symmetry; exact Hb |].
    eapply record_type_not_level; gen_presups; eassumption.
  - exfalso; eapply record_type_not_level; gen_presups; eassumption.
Qed.

(** A literal of type [Level@n] is of a tier at most [n], and so is the
    constant of a level of type [Level@n]. *)
Lemma wf_llit_sort : forall {Γ o n},
    Γ ⊢ 𝕃ᵒ o : Level@n ->
    fst o <= n.
Proof.
  intros * H; destruct (wf_llit_inversion_sort _ _ _ _ _ H) as (m & Hm & Hs).
  apply subtyp_level_inv in Hs; lia.
Qed.

Lemma lvl_fold_hd_sort : forall {Γ} (l : list (nat * exp)) hd n,
    Γ ⊢ lvl_fold hd l : Level@n ->
    Γ ⊢ hd : Level@n.
Proof.
  intros Γ l; induction l as [| [k a] r IH]; cbn; intros hd n H; [ exact H |].
  apply IH in H; apply wf_maxl_inversion in H as (m & Hhd & _ & Hs).
  eapply wf_exp_subtyp'; [ exact Hhd | exact Hs ].
Qed.

Lemma lvl_exp_of_const_sort : forall {Γ c} {l : list (nat * exp)} {n},
    Γ ⊢ lvl_exp_of c l : Level@n ->
    fst c <= n.
Proof.
  intros * H.
  destruct l as [| [k a] r]; cbn in H; [ exact (wf_llit_sort H) |].
  destruct c as [[| c1] [| c2]]; try (cbn; lia);
    apply lvl_fold_hd_sort in H; apply wf_maxl_inversion in H as (m & Hc & _ & Hs);
    apply subtyp_level_inv in Hs; apply wf_llit_sort in Hc; cbn in *; lia.
Qed.

(** The large tier is never below the small one. *)
Lemma subtyp_large_small_absurd : forall {Γ i t},
    Γ ⊢ Typeω@i ⊆ Type⟨t⟩ ->
    False.
Proof.
  intros * H.
  assert (⊢ Γ) by (gen_presups; assumption).
  apply (subtyp_spec_large (k := S i)) in H as [[k Heq] | [(U & V & [k1 HU] & [k2 HV] & Hs) | (κ1 & A1 & A2 & B1 & B2 & [k1 HA] & _)]];
    [| | | left; mauto 3 ].
  - eapply exp_eq_typ_suniv_absurd; exact Heq.
  - destruct Hs; solve [ eapply exp_eq_typ_suniv_absurd; eassumption | eapply exp_eq_level_suniv_absurd; eassumption ].
  - eapply pi_univ_term_absurd; [ apply univ_term_typ | symmetry; exact HA ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve idempotent_nbe_ty : mctt.
#[export]
Hint Resolve nf_of_pi : mctt.
#[export]
Hint Resolve canonical_form_of_pi : mctt.
#[export]
Hint Resolve subtyp_spec : mctt.

(** ** Propositions Against Relevant Types *)

Section Proposition_Kinds.
  Context {GC : GCtx}.

(** A proposition is below no inductive type: at an environment of the
    context the proposition's value is propositional, the inductive type's
    relevant, and a subtyping keeps the kind ([per_subtyp_kind]). *)
Lemma subtyp_prop_ind_absurd : forall {Γ A p k Ps},
    Γ ⊢ A ⊆ apps (a_ind p k) Ps -> Γ ⊢ A : Propₘ -> False.
Proof.
  intros * Hs HA.
  pose proof (completeness_fundamental_subtyp _ _ _ Hs) as [R HR k' Hsub].
  pose proof (completeness_fundamental_exp _ _ _ HA) as HAs.
  pose proof (wf_ctx_scoped_exp HA) as HsΓ.
  pose proof (per_ctx_then_per_env_initial_env HR HsΓ HsΓ) as [ρ [ρ' [_ [_ Hρ]]]].
  assert (HPR : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρρ : R ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  destruct (eval_sub_id_rel HR Hρρ) as [Hid Hid'].
  destruct (Hsub _ _ HR _ _ (rel_sub_id (ex_intro _ _ HR)) _ _ _ _ Hρρ Hid Hid')
    as [aσ a a'σ' a' _ Ha _ Ha' _ _ Hsa].
  pose proof (per_subtyp_kind _ _ _ Hsa) as Hr.
  destruct (eval_ind_value _ _ _ _ _ Ha') as [ms ->].
  destruct (rel_type_kind_of_sort_kind sort_kind_prop HAs _ HR _ _ (per_ctx_env_retag HR _ _ Hρρ)) as (x' & Hx' & Hl).
  functional_eval_rewrite_clear.
  rewrite Hl in Hr; discriminate Hr.
Qed.

(** A type of levels is below no inductive type, as a proposition is
    not: a subtyping keeps the kind ([per_subtyp_kind]). *)
Lemma subtyp_level_ind_absurd : forall {Γ A p k Ps},
    Γ ⊢ A ⊆ apps (a_ind p k) Ps -> Γ ⊢ A : LevelSort -> False.
Proof.
  intros * Hs HA.
  pose proof (completeness_fundamental_subtyp _ _ _ Hs) as [R HR k' Hsub].
  pose proof (completeness_fundamental_exp _ _ _ HA) as HAs.
  pose proof (wf_ctx_scoped_exp HA) as HsΓ.
  pose proof (per_ctx_then_per_env_initial_env HR HsΓ HsΓ) as [ρ [ρ' [_ [_ Hρ]]]].
  assert (HPR : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρρ : R ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  destruct (eval_sub_id_rel HR Hρρ) as [Hid Hid'].
  destruct (Hsub _ _ HR _ _ (rel_sub_id (ex_intro _ _ HR)) _ _ _ _ Hρρ Hid Hid')
    as [aσ a a'σ' a' _ Ha _ Ha' _ _ Hsa].
  pose proof (per_subtyp_kind _ _ _ Hsa) as Hr.
  destruct (eval_ind_value _ _ _ _ _ Ha') as [ms ->].
  destruct (rel_type_kind_of_sort_kind sort_kind_level HAs _ HR _ _ (per_ctx_env_retag HR _ _ Hρρ)) as (x' & Hx' & Hl).
  functional_eval_rewrite_clear.
  rewrite Hl in Hr; discriminate Hr.
Qed.

(** A record type is no proposition: at an environment of the context its
    value is a record type, which is relevant. *)
Lemma typ_prop_record_absurd : forall {Γ p Ms}, Γ ⊢ apps (a_record p) Ms : Propₘ -> False.
Proof.
  intros * HA.
  pose proof (completeness_fundamental_exp _ _ _ HA) as HAs.
  destruct (rel_exp_of_prop_inversion HAs) as [R [HR _]].
  pose proof (wf_ctx_scoped_exp HA) as HsΓ.
  pose proof (per_ctx_then_per_env_initial_env HR HsΓ HsΓ) as [ρ [ρ' [_ [_ Hρ]]]].
  assert (HPR : PER R) by (eapply per_env_PER; exact HR).
  assert (Hρρ : R ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  destruct (rel_exp_of_prop_inversion_simple_at HR HAs _ _ Hρρ) as (x & _ & Hx & _ & [Hl _ _]).
  destruct (eval_record_value _ _ _ _ Hx) as [ms ->].
  discriminate Hl.
Qed.

End Proposition_Kinds.

