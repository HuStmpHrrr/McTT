(** * PER Lemmas: the Basic PERs

    The first part of [Core.Semantic.PER.Lemmas]: the morphisms of the
    evaluation relations; [per_bot], [per_top], the PERs of levels and of
    their order, [per_top_typ], [per_ne], [per_prop] and [per_proof] are
    PERs; the tactics rewriting along equivalent relations. *)
From Stdlib Require Import Equivalence Lia List Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.Chain PER.CoreTactics PER.Definitions PER.Tele.
Import Domain_Notations Fixed_Notations.
Import ListNotations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

Add Parametric Morphism R0 `(R0_morphism : Proper _ ((@relation_equivalence domain) ==> (@relation_equivalence domain)) R0) A ρ A' ρ' : (rel_mod_eval R0 A ρ A' ρ')
    with signature (@relation_equivalence domain) ==> iff as rel_mod_eval_morphism.
Proof.
  split; intros []; econstructor; try eassumption;
    [> eapply R0_morphism; [symmetry + idtac |]; eassumption ..].
Qed.

Add Parametric Morphism f a f' a' : (rel_mod_app f a f' a')
    with signature (@relation_equivalence domain) ==> iff as rel_mod_app_morphism.
Proof.
  intros * HRR'.
  split; intros []; econstructor; try eassumption;
    apply HRR'; eassumption.
Qed.

Lemma rel_mod_eval_proj1 : forall (P Q : relation domain -> domain -> domain -> Prop) A ρ A' ρ' R,
    rel_mod_eval (fun R x y => P R x y /\ Q R x y) A ρ A' ρ' R -> rel_mod_eval P A ρ A' ρ' R.
Proof. intros * [a a' Ha Ha' [HP _]]; econstructor; eassumption. Qed.

Lemma per_bot_sym : forall m n,
    Dom m ≈ n ∈ per_bot ->
    Dom n ≈ m ∈ per_bot.
Proof.
  intros * H s; destruct (H s) as [L L' HL HL' HE].
  exact (mk_neutral_reads_alike _ _ _ _ _ HL' HL (eq_sym HE)).
Qed.

Hint Resolve per_bot_sym : mctt.

Lemma per_bot_trans : forall m n l,
    Dom m ≈ n ∈ per_bot ->
    Dom n ≈ l ∈ per_bot ->
    Dom m ≈ l ∈ per_bot.
Proof.
  intros * Hmn Hnl s; destruct (Hmn s) as [L L1 HL HL1 HE]; destruct (Hnl s) as [L2 L' HL2 HL' HE'].
  pose proof (functional_read_ne _ _ _ _ HL1 HL2) as <-.
  exact (mk_neutral_reads_alike _ _ _ _ _ HL HL' (eq_trans HE HE')).
Qed.

Hint Resolve per_bot_trans : mctt.

#[local] Instance per_bot_PER : PER per_bot.
Proof.
  split.
  - eauto using per_bot_sym.
  - eauto using per_bot_trans.
Qed.

Lemma var_per_bot : forall {n},
    Dom #ᵈ n ≈ #ᵈ n ∈ per_bot.
Proof.
  intros ? ?. econstructor; [ constructor | constructor | reflexivity ].
Qed.

Hint Resolve var_per_bot : mctt.

(** Two neutrals reading back to the same neutral are related. *)
Lemma per_bot_of_reads : forall m n,
    (forall s, exists L, Rne m in s ↘ L /\ Rne n in s ↘ L) ->
    Dom m ≈ n ∈ per_bot.
Proof. intros * H s; destruct (H s) as (L & HL & HL'); exact (mk_neutral_reads_alike _ _ _ _ _ HL HL' eq_refl). Qed.

Lemma per_top_sym : forall m n,
    Dom m ≈ n ∈ per_top ->
    Dom n ≈ m ∈ per_top.
Proof.
  intros * H s; destruct (H s) as [L L' HL HL' HE].
  exact (mk_normal_reads_alike _ _ _ _ _ HL' HL (eq_sym HE)).
Qed.

Hint Resolve per_top_sym : mctt.

Lemma per_top_trans : forall m n l,
    Dom m ≈ n ∈ per_top ->
    Dom n ≈ l ∈ per_top ->
    Dom m ≈ l ∈ per_top.
Proof.
  intros * Hmn Hnl s; destruct (Hmn s) as [L L1 HL HL1 HE]; destruct (Hnl s) as [L2 L' HL2 HL' HE'].
  pose proof (functional_read_nf _ _ _ _ HL1 HL2) as <-.
  exact (mk_normal_reads_alike _ _ _ _ _ HL HL' (eq_trans HE HE')).
Qed.

(** Two values reading back to the same normal form are related. *)
Lemma per_top_of_reads : forall m n,
    (forall s, exists L, Rnf m in s ↘ L /\ Rnf n in s ↘ L) ->
    Dom m ≈ n ∈ per_top.
Proof. intros * H s; destruct (H s) as (L & HL & HL'); exact (mk_normal_reads_alike _ _ _ _ _ HL HL' eq_refl). Qed.

(** At [Level] related values read back to the same normal form: level
    normal forms are erased ([read_nf_level_erased]). *)
Lemma per_lvl_reads : forall m n,
    Dom ⇓ Levelᵈ m ≈ ⇓ Levelᵈ n ∈ per_top ->
    forall s, exists W, Rnf ⇓ Levelᵈ m in s ↘ W /\ Rnf ⇓ Levelᵈ n in s ↘ W.
Proof.
  intros * H s; destruct (H s) as [W W' HW HW' HE].
  rewrite (read_nf_level_erased _ _ _ _ HW), (read_nf_level_erased _ _ _ _ HW') in HE; subst W'.
  eauto.
Qed.

Hint Resolve per_top_trans : mctt.

#[local] Instance per_top_PER : PER per_top.
Proof.
  split.
  - eauto using per_top_sym.
  - eauto using per_top_trans.
Qed.

(** [per_lvl] is [per_top] at [Level], so it is a PER for the same reason. *)
Lemma per_lvl_then_per_top : forall m n,
    Dom m ≈ n ∈ per_lvl ->
    Dom ⇓ Levelᵈ m ≈ ⇓ Levelᵈ n ∈ per_top.
Proof. intros * H; exact H. Qed.

Hint Resolve per_lvl_then_per_top : mctt.

(** A literal level reads back as itself, so it is related to itself and the
    literals are ordered by their indices.  These are the only levels the
    universes at a [universe_index] use. *)
Lemma read_nf_domain_level_lit : forall n s,
    Rnf ⇓ Levelᵈ (domain_level_lit n) in s ↘ nf_lvl_of (lvl_lit n).
Proof.
  intros n s; rewrite <- (lvl_canon_lit n); apply read_nf_lvl; constructor.
Qed.

Hint Resolve read_nf_domain_level_lit : mctt.

Lemma per_lvl_lit : forall n, Dom domain_level_lit n ≈ domain_level_lit n ∈ per_lvl.
Proof.
  intros n; apply per_top_of_reads; intros s; eexists; split; apply read_nf_domain_level_lit.
Qed.

Hint Resolve per_lvl_lit : mctt.

Lemma per_sublvl_lit : forall n m,
    ordinal_le n m ->
    per_sublvl (domain_level_lit n) (domain_level_lit m).
Proof.
  intros n m Hle s; exists (lvl_lit n) (lvl_lit m); [ apply read_nf_domain_level_lit | apply read_nf_domain_level_lit |].
  apply lvl_le_lit; assumption.
Qed.

Hint Resolve per_sublvl_lit : mctt.

(** Related levels have the same realiser: readback preserves the offsets, so
    the realiser is the one of the canonical form both read back as. *)
Lemma per_lvl_real : forall m n,
    Dom m ≈ n ∈ per_lvl ->
    domain_level_real m = domain_level_real n.
Proof.
  intros * H; destruct (per_lvl_reads _ _ H 0) as [W [HW HW']].
  apply read_nf_level_real in HW as [L [-> HL]].
  apply read_nf_level_real in HW' as [L' [Heq HL']].
  apply nf_lvl_of_inj in Heq as <-; congruence.
Qed.

Hint Resolve per_lvl_real : mctt.

(** ** The Order on Levels

    [per_sublvl] relates two readable levels whose canonical forms are
    ordered.  It is reflexive on related levels, transitive, and refines the
    order on realisers — which is what makes a subtyping between two small
    universes hold at the index of the smaller one. *)
Lemma per_sublvl_left : forall l l',
    per_sublvl l l' ->
    Dom l ≈ l ∈ per_lvl.
Proof.
  intros * H; apply per_top_of_reads; intros s; destruct (H s) as [L L' HL HL' _]; eauto.
Qed.

Lemma per_sublvl_right : forall l l',
    per_sublvl l l' ->
    Dom l' ≈ l' ∈ per_lvl.
Proof.
  intros * H; apply per_top_of_reads; intros s; destruct (H s) as [L L' HL HL' _]; eauto.
Qed.

Hint Resolve per_sublvl_left per_sublvl_right : mctt.

Lemma per_sublvl_real : forall l l',
    per_sublvl l l' ->
    ordinal_le (domain_level_real l) (domain_level_real l').
Proof.
  intros * H; destruct (H 0) as [L L' HL HL' Hle].
  apply read_nf_level_real in HL as [L1 [HL1 <-]].
  apply read_nf_level_real in HL' as [L1' [HL1' <-]].
  apply nf_lvl_of_inj in HL1 as <-; apply nf_lvl_of_inj in HL1' as <-.
  apply lvl_le_real; assumption.
Qed.

Lemma per_sublvl_of_per_lvl : forall l l',
    Dom l ≈ l' ∈ per_lvl ->
    per_sublvl l l'.
Proof.
  intros * H s; destruct (per_lvl_reads _ _ H s) as [W [HW HW']].
  destruct (read_nf_level_real _ _ _ _ HW) as [L [-> _]].
  exists L L; [ assumption | assumption | apply lvl_le_refl ].
Qed.

Hint Resolve per_sublvl_of_per_lvl : mctt.

Lemma per_sublvl_trans : forall l l' l'',
    per_sublvl l l' ->
    per_sublvl l' l'' ->
    per_sublvl l l''.
Proof.
  intros * H H' s.
  destruct (H s) as [L L1 HL HL1 Hle].
  destruct (H' s) as [L1' L2 HL1' HL2 Hle'].
  assert (L1 = L1') as <-
      by (apply nf_lvl_of_inj; eapply functional_read_nf; eassumption).
  exists L L2; [ assumption | assumption | eapply lvl_le_trans; eassumption ].
Qed.

Hint Resolve per_sublvl_trans : mctt.

Lemma per_lvl_sym : forall m n,
    Dom m ≈ n ∈ per_lvl ->
    Dom n ≈ m ∈ per_lvl.
Proof. intros * H; apply per_top_sym; exact H. Qed.

Hint Resolve per_lvl_sym : mctt.

Lemma per_lvl_trans : forall m n l,
    Dom m ≈ n ∈ per_lvl ->
    Dom n ≈ l ∈ per_lvl ->
    Dom m ≈ l ∈ per_lvl.
Proof. intros * H H'; eapply per_top_trans; [ exact H | exact H' ]. Qed.

Hint Resolve per_lvl_trans : mctt.

#[local] Instance per_lvl_PER : PER per_lvl.
Proof.
  split.
  - eauto using per_lvl_sym.
  - eauto using per_lvl_trans.
Qed.

(** A neutral of type [Level@n] is a level: it reads back as the single atom
    at offset [0], of sort [n], which is canonical.  The sort is read off the
    neutral's type, so two neutrals are related levels only at types of one
    sort. *)
Lemma per_bot_then_per_lvl : forall m m' a a',
    domain_level_sort a = domain_level_sort a' ->
    Dom m ≈ m' ∈ per_bot ->
    Dom ⇑ a m ≈ ⇑ a' m' ∈ per_lvl.
Proof.
  intros * Ha H; apply per_top_of_reads; intros s.
  destruct (H s) as [M M' Hl Hr HE].
  exists (lvⁿ ordinal_zero (cons (mk_level_atom 0 (domain_level_sort a) (ne_erase M)) nil)); split;
    [| rewrite Ha, HE ]; econstructor; eassumption.
Qed.

Hint Resolve per_bot_then_per_lvl : mctt.

(** The levels of sort [n] form a PER, and a neutral of type [Level@n] is
    one. *)
Lemma per_lvl_at_lvl : forall n l l', Dom l ≈ l' ∈ per_lvl_at n -> Dom l ≈ l' ∈ per_lvl.
Proof. intros * H; apply per_top_of_reads; intros s; destruct (H s) as [L HL HL' _]; eexists; split; eassumption. Qed.

Lemma per_lvl_at_sym : forall n m m',
    Dom m ≈ m' ∈ per_lvl_at n ->
    Dom m' ≈ m ∈ per_lvl_at n.
Proof. intros * H s; destruct (H s) as [L HL HL' Hb]; exists L; assumption. Qed.

Lemma per_lvl_at_trans : forall n m m' m'',
    Dom m ≈ m' ∈ per_lvl_at n ->
    Dom m' ≈ m'' ∈ per_lvl_at n ->
    Dom m ≈ m'' ∈ per_lvl_at n.
Proof.
  intros * H H' s; destruct (H s) as [L HL HL' Hb], (H' s) as [L' HM HM' Hb'].
  assert (L' = L) as -> by (apply nf_lvl_of_inj; exact (functional_read_nf _ _ _ _ HM HL')).
  exists L; assumption.
Qed.

#[local] Instance per_lvl_at_PER n : PER (per_lvl_at n).
Proof.
  split.
  - intros ? ?; apply per_lvl_at_sym.
  - intros ? ? ?; apply per_lvl_at_trans.
Qed.

Lemma lvl_sort_bounded_mono : forall m n L, m <= n -> lvl_sort_bounded m L -> lvl_sort_bounded n L.
Proof. intros * Hmn [Hc Ha]; split; [ lia | intros; eapply Nat.le_trans; [ eapply Ha; eassumption | exact Hmn ] ]. Qed.

Lemma per_lvl_at_mono : forall m n l l', m <= n -> Dom l ≈ l' ∈ per_lvl_at m -> Dom l ≈ l' ∈ per_lvl_at n.
Proof.
  intros * Hmn H s; destruct (H s) as [L HL HL' Hb].
  exists L; [ assumption | assumption | eapply lvl_sort_bounded_mono; eassumption ].
Qed.

Lemma per_bot_then_per_lvl_at : forall n m m',
    Dom m ≈ m' ∈ per_bot ->
    Dom ⇑ (Levelᵈ@n) m ≈ ⇑ (Levelᵈ@n) m' ∈ per_lvl_at n.
Proof.
  intros * H s.
  destruct (H s) as [M M' Hl Hr HE].
  exists (ordinal_zero, cons (mk_level_atom 0 n (ne_erase M)) nil);
    [ econstructor; eassumption | rewrite HE; econstructor; eassumption | split; [ cbn; lia |] ].
  intros k t a Hin; cbn in Hin; destruct Hin as [(_ & -> & _) | []]; lia.
Qed.

Hint Resolve per_lvl_at_sym per_lvl_at_trans per_bot_then_per_lvl_at : mctt.

Lemma per_bot_then_per_top : forall m m' a a' b b' c c',
    evaluated_kind (domain_kind (⇑ a b)) ->
    evaluated_kind (domain_kind (⇑ a' b')) ->
    Dom m ≈ m' ∈ per_bot ->
    Dom ⇓ (⇑ a b) (⇑ c m) ≈ ⇓ (⇑ a' b') (⇑ c' m') ∈ per_top.
Proof.
  intros * Hr Hr' H s.
  destruct (H s) as [M M' Hl Hr0 HE].
  exists (nf_neut M) (nf_neut M'); [ apply read_nf_neut; assumption | apply read_nf_neut; assumption | cbn; f_equal; exact HE ].
Qed.

Hint Resolve per_bot_then_per_top : mctt.

Lemma per_top_typ_sym : forall m n,
    Dom m ≈ n ∈ per_top_typ ->
    Dom n ≈ m ∈ per_top_typ.
Proof.
  intros * H s; destruct (H s) as [L L' HL HL' HE].
  exact (mk_type_reads_alike _ _ _ _ _ HL' HL (eq_sym HE)).
Qed.

Hint Resolve per_top_typ_sym : mctt.

Lemma per_top_typ_trans : forall m n l,
    Dom m ≈ n ∈ per_top_typ ->
    Dom n ≈ l ∈ per_top_typ ->
    Dom m ≈ l ∈ per_top_typ.
Proof.
  intros * Hmn Hnl s; destruct (Hmn s) as [L L1 HL HL1 HE]; destruct (Hnl s) as [L2 L' HL2 HL' HE'].
  pose proof (functional_read_typ _ _ _ _ HL1 HL2) as <-.
  exact (mk_type_reads_alike _ _ _ _ _ HL HL' (eq_trans HE HE')).
Qed.

(** Two types reading back to the same normal form are related. *)
Lemma per_top_typ_of_reads : forall a b,
    (forall s, exists C, Rtyp a in s ↘ C /\ Rtyp b in s ↘ C) ->
    Dom a ≈ b ∈ per_top_typ.
Proof. intros * H s; destruct (H s) as (C & HC & HC'); exact (mk_type_reads_alike _ _ _ _ _ HC HC' eq_refl). Qed.

Hint Resolve per_top_typ_trans : mctt.

#[local] Instance per_top_typ_PER : PER per_top_typ.
Proof.
  split.
  - eauto using per_top_typ_sym.
  - eauto using per_top_typ_trans.
Qed.

Lemma per_ne_sym : forall m n,
    Dom m ≈ n ∈ per_ne ->
    Dom n ≈ m ∈ per_ne.
Proof.
  intros * [].
  econstructor; mautosolve.
Qed.

Hint Resolve per_ne_sym : mctt.

Lemma per_ne_trans : forall m n l,
    Dom m ≈ n ∈ per_ne ->
    Dom n ≈ l ∈ per_ne ->
    Dom m ≈ l ∈ per_ne.
Proof.
  intros * [].
  inversion_clear 1.
  econstructor; mautosolve.
Qed.

Hint Resolve per_ne_trans : mctt.

#[local] Instance per_ne_PER : PER per_ne.
Proof.
  split.
  - eauto using per_ne_sym.
  - eauto using per_ne_trans.
Qed.

Lemma per_prop_sym : forall a a', Dom a ≈ a' ∈ per_prop -> Dom a' ≈ a ∈ per_prop.
Proof. intros * []; constructor; eauto using per_top_typ_sym. Qed.

Lemma per_prop_trans : forall a a' a'', Dom a ≈ a' ∈ per_prop -> Dom a' ≈ a'' ∈ per_prop -> Dom a ≈ a'' ∈ per_prop.
Proof. intros * [] []; constructor; eauto using per_top_typ_trans. Qed.

Hint Resolve per_prop_sym per_prop_trans : mctt.

#[local] Instance per_prop_PER : PER per_prop.
Proof. split; [ exact per_prop_sym | exact per_prop_trans ]. Qed.

Lemma per_proof_sym : forall v v', Dom v ≈ v' ∈ per_proof -> Dom v' ≈ v ∈ per_proof.
Proof. intros * []; split; assumption. Qed.

Lemma per_proof_trans : forall v v' v'', Dom v ≈ v' ∈ per_proof -> Dom v' ≈ v'' ∈ per_proof -> Dom v ≈ v'' ∈ per_proof.
Proof. intros * [] []; split; assumption. Qed.

(** A proof that reads back is related to itself. *)
Lemma per_proof_refl : forall v, proof_readable v -> Dom v ≈ v ∈ per_proof.
Proof. intros * H; split; exact H. Qed.

Hint Resolve per_proof_sym per_proof_trans per_proof_refl : mctt.

#[local] Instance per_proof_PER : PER per_proof.
Proof. split; [ exact per_proof_sym | exact per_proof_trans ]. Qed.

(** An element of a component's type at one base reads back at the type
    evaluated at another base admissible beside it ([adm_nparam_types],
    [adm_arg_types]), as an entry stored at the type there. *)
Lemma component_elem_readable_at_admissible_base : forall A ρ ρ' R x x',
    rel_component_types A ρ ρ' R -> R x x' -> entry_readable (de_term x' (entry_type_closure A ρ')).
Proof.
  intros * [a a' Ea Ea' Ht He _] Hx s.
  destruct (Ht s) as [T T' _ HT' _]; destruct (He _ _ Hx s) as [W W' _ HW' _].
  eexists; eapply read_entry_term; [ eapply eval_entry_type_closure; exact Ea' | exact HT' | exact HW' ].
Qed.

(** And at the type at the first base. *)
Lemma component_elem_readable_at_base : forall A ρ ρ' R x x',
    rel_component_types A ρ ρ' R -> R x x' -> entry_readable (de_term x (entry_type_closure A ρ)).
Proof.
  intros * [a a' Ea Ea' Ht He _] Hx s.
  destruct (Ht s) as [T T' HT _ _]; destruct (He _ _ Hx s) as [W W' HW _ _].
  eexists; eapply read_entry_term; [ eapply eval_entry_type_closure; exact Ea | exact HT | exact HW ].
Qed.

(** The elements of a [Π] read the domains only through their sorts. *)
Lemma pi_elements_kind_irrel : forall a a' b b' in_rel out_rel,
    domain_kind a = domain_kind b ->
    domain_kind a' = domain_kind b' ->
    (pi_elements a a' in_rel out_rel <~> pi_elements b b' in_rel out_rel).
Proof. intros * Ha Ha' f f'; split; intros []; constructor; congruence + assumption. Qed.

Add Parametric Morphism i : (per_univ_elem i)
    with signature (@relation_equivalence domain) ==> eq ==> eq ==> iff as per_univ_elem_morphism_iff.
Proof.
  simpl.
  intros R R' HRR'.
  split; intros Horig; [gen R' | gen R];
    per_univ_elem_induction Horig.
  all: try solve [ basic_per_univ_elem_econstructor; eauto;
    try (etransitivity; [symmetry + idtac|]; eassumption);
    intros;
    destruct_rel_mod_eval;
    econstructor; mautosolve ].
  (** An inductive type, a record type: their relations are untouched. *)
  all: intros R0 HR0; basic_per_univ_elem_econstructor; try eassumption;
    unfold nparams_evals, args_evals, doms_evals, fields_evals in *;
    try (intros; eapply rel_mod_eval_proj1; match goal with H : _ |- _ => eapply H; eassumption end);
    try (etransitivity; [ symmetry + idtac | ]; eassumption).
Qed.

(** The morphism in forward form.  [apply -> per_univ_elem_morphism_iff] needs
    the level to be known, which is not the case when building a context PER:
    there the level of the head relation is fixed only by the witness supplied
    for it.  Taking the witness first leaves [<~>] as the only goal, and leaves
    the target relation implicit, so the caller never spells out the
    impredicative head relation. *)
Lemma per_univ_elem_resp_iff : forall {i R R' a a'},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    (R <~> R') ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R'.
Proof.
  intros * H HR.
  apply -> per_univ_elem_morphism_iff; [ eassumption | reflexivity | reflexivity | eassumption ].
Qed.

Add Parametric Morphism i : (per_univ_elem i)
    with signature (@relation_equivalence domain) ==> (@relation_equivalence domain) as per_univ_elem_morphism_relation_equivalence.
Proof with mautosolve.
  intros ** a b.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Add Parametric Morphism i A ρ A' ρ' : (rel_typ i A ρ A' ρ')
    with signature (@relation_equivalence domain) ==> iff as rel_typ_morphism.
Proof.
  intros * HRR'.
  split; intros []; econstructor; try eassumption;
    [setoid_rewrite <- HRR' | setoid_rewrite HRR']; eassumption.
Qed.

Lemma domain_app_per : forall f f' a a',
  Dom f ≈ f' ∈ per_bot ->
  Dom a ≈ a' ∈ per_top ->
  Dom f $ᵈ a ≈ f' $ᵈ a' ∈ per_bot.
Proof.
  intros * H H0 s.
  destruct (H s) as [L L' HL HL' HE].
  destruct (H0 s) as [N N' HN HN' HE'].
  exists (ne_app L N) (ne_app L' N'); [ econstructor; eassumption | econstructor; eassumption | cbn; f_equal; assumption ].
Qed.

End Fixed_GCtx.

#[export] Existing Instance rel_mod_eval_morphism_Proper.
#[export] Existing Instance rel_mod_app_morphism_Proper.
#[export]
Hint Resolve per_bot_sym : mctt.
#[export]
Hint Resolve per_bot_trans : mctt.
#[export] Existing Instance per_bot_PER.
#[export]
Hint Resolve var_per_bot : mctt.
#[export]
Hint Resolve per_top_sym : mctt.
#[export]
Hint Resolve per_top_trans : mctt.
#[export] Existing Instance per_top_PER.
#[export]
Hint Resolve per_bot_then_per_top : mctt.
#[export]
Hint Resolve per_top_typ_sym : mctt.
#[export]
Hint Resolve per_top_typ_trans : mctt.
#[export] Existing Instance per_top_typ_PER.
#[export]
Hint Resolve read_nf_domain_level_lit per_lvl_lit per_sublvl_lit : mctt.
#[export]
Hint Resolve per_lvl_real : mctt.
#[export]
Hint Resolve per_sublvl_left per_sublvl_right per_sublvl_of_per_lvl per_sublvl_trans : mctt.
#[export]
Hint Resolve per_lvl_then_per_top : mctt.
#[export]
Hint Resolve per_lvl_sym : mctt.
#[export]
Hint Resolve per_lvl_trans : mctt.
#[export] Existing Instance per_lvl_PER.
#[export] Existing Instance per_lvl_at_PER.
#[export]
Hint Resolve per_lvl_at_sym per_lvl_at_trans per_bot_then_per_lvl_at per_lvl_at_lvl : mctt.
#[export]
Hint Resolve per_bot_then_per_lvl : mctt.
#[export]
Hint Resolve per_ne_sym : mctt.
#[export]
Hint Resolve per_ne_trans : mctt.
#[export] Existing Instance per_ne_PER.
#[export]
Hint Resolve per_prop_sym per_prop_trans per_proof_sym per_proof_trans per_proof_refl : mctt.
#[export] Existing Instance per_prop_PER.
#[export] Existing Instance per_proof_PER.
#[export] Existing Instance per_univ_elem_morphism_iff_Proper.
#[export] Existing Instance per_univ_elem_morphism_relation_equivalence_Proper.
#[export] Existing Instance rel_typ_morphism_Proper.
Ltac rewrite_relation_equivalence_left :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        try setoid_rewrite H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac rewrite_relation_equivalence_right :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        try setoid_rewrite <- H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite <- H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac clear_relation_equivalence :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        (unify R1 R2; clear H) + (is_var R1; clear R1 H) + (is_var R2; clear R2 H)
    end.

Ltac apply_relation_equivalence :=
  clear_relation_equivalence;
  rewrite_relation_equivalence_right;
  clear_relation_equivalence;
  rewrite_relation_equivalence_left;
  clear_relation_equivalence.

Section Fixed_GCtx.
  Context {GC : GCtx}.


End Fixed_GCtx.

(** Closes [R1 x y] or [R2 x y] from [R1 <~> R2] directly.
    [apply_relation_equivalence] only rewrites, and [setoid_rewrite] leaves the
    conclusion untouched when both sides of [<~>] are applications, as the head
    relations [head_rel _ _ D] of a context PER are for two witnesses [D]. *)
Ltac use_relation_equivalence :=
  match goal with
  | H : ?R1 <~> ?R2 |- ?R1 _ _ => apply H
  | H : ?R1 <~> ?R2 |- ?R2 _ _ => apply H
  end.

(** Move every hypothesis across the equivalences in context, from left to
    right, where [apply_relation_equivalence] cannot rewrite (the
    relations are applied to dependent evidence). *)
Ltac move_by_relation_equivalence :=
  repeat match goal with
    | Heq : ?R1 <~> ?R2, H : ?R1 ?x ?y |- _ => apply Heq in H
    end.

Ltac move_goal_by_relation_equivalence :=
  try match goal with
    | Heq : ?R1 <~> ?R2 |- ?R1 _ _ => apply Heq
    end.
