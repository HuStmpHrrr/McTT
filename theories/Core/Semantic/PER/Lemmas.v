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
  intros * H s.
  pose proof H s.
  destruct_conjs; solve [eauto].
Qed.

Hint Resolve per_bot_sym : mctt.

Lemma per_bot_trans : forall m n l,
    Dom m ≈ n ∈ per_bot ->
    Dom n ≈ l ∈ per_bot ->
    Dom m ≈ l ∈ per_bot.
Proof.
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_conjs.
  functional_read_rewrite_clear; solve [eauto].
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
  intros ? ?. repeat econstructor.
Qed.

Hint Resolve var_per_bot : mctt.

Lemma per_top_sym : forall m n,
    Dom m ≈ n ∈ per_top ->
    Dom n ≈ m ∈ per_top.
Proof.
  intros * H s.
  pose proof H s.
  destruct_conjs; solve [eauto].
Qed.

Hint Resolve per_top_sym : mctt.

Lemma per_top_trans : forall m n l,
    Dom m ≈ n ∈ per_top ->
    Dom n ≈ l ∈ per_top ->
    Dom m ≈ l ∈ per_top.
Proof.
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_conjs.
  functional_read_rewrite_clear; solve [eauto].
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
    universes at a [uidx] use. *)
Lemma read_nf_dlvl_lit : forall n s,
    Rnf ⇓ Levelᵈ (dlvl_lit n) in s ↘ nf_lvl_of (lvl_lit n).
Proof.
  intros n s; rewrite <- (lvl_canon_lit n); apply read_nf_lvl; constructor.
Qed.

Hint Resolve read_nf_dlvl_lit : mctt.

Lemma per_lvl_lit : forall n, Dom dlvl_lit n ≈ dlvl_lit n ∈ per_lvl.
Proof.
  intros n s; eexists; split; apply read_nf_dlvl_lit.
Qed.

Hint Resolve per_lvl_lit : mctt.

Lemma per_sublvl_lit : forall n m,
    ole n m ->
    per_sublvl (dlvl_lit n) (dlvl_lit m).
Proof.
  intros n m Hle s; exists (lvl_lit n) (lvl_lit m); [ apply read_nf_dlvl_lit | apply read_nf_dlvl_lit |].
  apply lvl_le_lit; assumption.
Qed.

Hint Resolve per_sublvl_lit : mctt.

(** Related levels have the same realiser: readback preserves the offsets, so
    the realiser is the one of the canonical form both read back as. *)
Lemma per_lvl_real : forall m n,
    Dom m ≈ n ∈ per_lvl ->
    dlvl_real m = dlvl_real n.
Proof.
  intros * H; destruct (H 0) as [W [HW HW']].
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
  intros * H s; destruct (H s) as [L L' HL HL' _]; eauto.
Qed.

Lemma per_sublvl_right : forall l l',
    per_sublvl l l' ->
    Dom l' ≈ l' ∈ per_lvl.
Proof.
  intros * H s; destruct (H s) as [L L' HL HL' _]; eauto.
Qed.

Hint Resolve per_sublvl_left per_sublvl_right : mctt.

Lemma per_sublvl_real : forall l l',
    per_sublvl l l' ->
    ole (dlvl_real l) (dlvl_real l').
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
  intros * H s; destruct (H s) as [W [HW HW']].
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
    dsort a = dsort a' ->
    Dom m ≈ m' ∈ per_bot ->
    Dom ⇑ a m ≈ ⇑ a' m' ∈ per_lvl.
Proof.
  intros * Ha H s.
  destruct (H s) as [M [Hl Hr]].
  exists (lvⁿ oz (la_cons 0 (dsort a) M la_nil)); split; [| rewrite Ha ]; econstructor; eassumption.
Qed.

Hint Resolve per_bot_then_per_lvl : mctt.

(** The levels of sort [n] form a PER, and a neutral of type [Level@n] is
    one. *)
Lemma per_lvl_at_lvl : forall n l l', Dom l ≈ l' ∈ per_lvl_at n -> Dom l ≈ l' ∈ per_lvl.
Proof. intros * H s; destruct (H s) as [L HL HL' _]; eexists; split; eassumption. Qed.

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

Lemma lvl_bnd_mono : forall m n L, m <= n -> lvl_bnd m L -> lvl_bnd n L.
Proof. intros * Hmn [Hc Ha]; split; [ lia | intros; eapply Nat.le_trans; [ eapply Ha; eassumption | exact Hmn ] ]. Qed.

Lemma per_lvl_at_mono : forall m n l l', m <= n -> Dom l ≈ l' ∈ per_lvl_at m -> Dom l ≈ l' ∈ per_lvl_at n.
Proof.
  intros * Hmn H s; destruct (H s) as [L HL HL' Hb].
  exists L; [ assumption | assumption | eapply lvl_bnd_mono; eassumption ].
Qed.

Lemma per_bot_then_per_lvl_at : forall n m m',
    Dom m ≈ m' ∈ per_bot ->
    Dom ⇑ (Levelᵈ@n) m ≈ ⇑ (Levelᵈ@n) m' ∈ per_lvl_at n.
Proof.
  intros * H s.
  destruct (H s) as [M [Hl Hr]].
  exists (oz, la_cons 0 n M la_nil); [ econstructor; eassumption .. | split; [ cbn; lia |] ].
  intros k t a Hin; cbn in Hin; destruct Hin as [(_ & -> & _) | []]; lia.
Qed.

Hint Resolve per_lvl_at_sym per_lvl_at_trans per_bot_then_per_lvl_at : mctt.

Lemma per_bot_then_per_top : forall m m' a a' b b' c c',
    Dom m ≈ m' ∈ per_bot ->
    Dom ⇓ (⇑ a b) (⇑ c m) ≈ ⇓ (⇑ a' b') (⇑ c' m') ∈ per_top.
Proof.
  intros * H s.
  pose proof H s.
  destruct_conjs.
  eexists; split; constructor; eassumption.
Qed.

Hint Resolve per_bot_then_per_top : mctt.

Lemma per_top_typ_sym : forall m n,
    Dom m ≈ n ∈ per_top_typ ->
    Dom n ≈ m ∈ per_top_typ.
Proof.
  intros * H s.
  pose proof H s.
  destruct_conjs; solve [eauto].
Qed.

Hint Resolve per_top_typ_sym : mctt.

Lemma per_top_typ_trans : forall m n l,
    Dom m ≈ n ∈ per_top_typ ->
    Dom n ≈ l ∈ per_top_typ ->
    Dom m ≈ l ∈ per_top_typ.
Proof.
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_conjs.
  functional_read_rewrite_clear; solve [eauto].
Qed.

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
  (** An inductive type: its relations are untouched. *)
  all: intros R0 HR0; basic_per_univ_elem_econstructor; try eassumption;
    unfold nparams_evals, args_evals, doms_evals in *;
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
  intros. intros s.
  destruct (H s) as [? []].
  destruct (H0 s) as [? []].
  mauto.
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
Hint Resolve read_nf_dlvl_lit per_lvl_lit per_sublvl_lit : mctt.
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

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_univ_elem_right_irrel : forall i i' R a b R' b',
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    DF a ≈ b' ∈ per_univ_elem i' ↘ R' ->
    (R <~> R').
Proof.
  simpl.
  intros * Horig.
  remember a as a' in |- *.
  gen a' b' R'.
  per_univ_elem_induction Horig; intros * Heq Hright;
    subst; basic_invert_per_univ_elem Hright; unfold per_univ;
    intros;
    apply_relation_equivalence;
    try reflexivity.
  (** An inductive type: the telescope relations agree with those of the
      other derivation, and so do the elements. *)
  2: {
    assert (D0 = D) as -> by congruence.
    match goal with H1 : ind_member D k = Some ?M1, H2 : ind_member D k = Some ?M2 |- _ =>
      assert_fails constr_eq M1 M2; rewrite H1 in H2; injection H2 as <- end.
    destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
    rename H into Hl, H0 into Hass, H1 into HM, H2 into Hh, H6 into HnP, H7 into Hn, H8 into HnI, H9 into HaP, H10 into Ha,
      H11 into HaI, H12 into HdP, H13 into Hd, H14 into HdI, H17 into Hns.
    rename H26 into HnP0, H27 into Hn0, H28 into HnI0, H29 into HaP0, H30 into Ha0, H31 into HaI0, H32 into HdP0, H33 into Hd0,
      H34 into HdI0, H37 into Hns0.
    assert (Hnr : forall m Mm kk vs vs1 vs2, ind_member D m = Some Mm -> kk < List.length (List.rev (im_nparams Mm)) ->
                    tele_prefix_rel (nr m) kk vs vs1 -> tele_prefix_rel (nr0 m) kk vs vs2 -> (nr m kk vs <~> nr0 m kk vs)).
    { intros m Mm kk vs vs1 vs2 Hm Hk Hp1 Hp2.
      destruct (nparams_lt_ass D m Mm kk Hass Hm Hk) as [A HA].
      destruct (Hn _ _ _ _ _ _ Hm HA Hp1) as [a1 a1' E1 E1' [Hper Hmot]].
      destruct (Hn0 _ _ _ _ _ _ Hm HA Hp2) as [a2 a2' E2 E2' Hper2].
      functional_eval_rewrite_clear; exact (Hmot _ _ _ eq_refl Hper2). }
    assert (Har : forall m Mm ms ms1 ms2 c gs kk vs vs1 vs2, ind_member D m = Some Mm ->
               tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms1 -> tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms ms2 ->
               ind_con Mm c = Some gs -> kk < List.length (cargs_nonrec gs) ->
               tele_prefix_rel (ar m ms c) kk vs vs1 -> tele_prefix_rel (ar0 m ms c) kk vs vs2 ->
               (ar m ms c kk vs <~> ar0 m ms c kk vs)).
    { intros m Mm ms ms1 ms2 c gs kk vs vs1 vs2 Hm Hm1 Hm2 Hc Hk Hp1 Hp2.
      destruct (nth_error_lt_some' _ _ Hk) as [A HA].
      destruct (Ha _ _ _ _ _ _ _ _ _ _ Hm Hm1 Hc HA Hp1) as [a1 a1' E1 E1' [Hper Hmot]].
      destruct (Ha0 _ _ _ _ _ _ _ _ _ _ Hm Hm2 Hc HA Hp2) as [a2 a2' E2 E2' Hper2].
      functional_eval_rewrite_clear; exact (Hmot _ _ _ eq_refl Hper2). }
    assert (Hdr : forall m Mm ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 kk ys ys1 ys2, ind_member D m = Some Mm ->
               tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms1 -> tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms ms2 ->
               ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
               tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws1 ->
               tele_prefix_rel (ar0 m ms c) (List.length (cargs_nonrec gs1)) ws ws2 ->
               kk < List.length (ptyp_doms t) ->
               tele_prefix_rel (shape_doms_rel (dr m) ms ws (ptyp_doms t)) kk ys ys1 ->
               tele_prefix_rel (shape_doms_rel (dr0 m) ms ws (ptyp_doms t)) kk ys ys2 ->
               (shape_doms_rel (dr m) ms ws (ptyp_doms t) kk ys <~> shape_doms_rel (dr0 m) ms ws (ptyp_doms t) kk ys)).
    { intros m Mm ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 kk ys ys1 ys2 Hm Hm1 Hm2 Hc Heq Hw1 Hw2 Hk Hp1 Hp2.
      destruct (nth_error_lt_some' _ _ Hk) as [B HB].
      unfold shape_doms_rel at 1 2; rewrite (List.nth_error_nth _ _ _ HB).
      destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hm1 Hc Heq Hw1 HB Hp1) as [a1 a1' E1 E1' [Hper Hmot]].
      destruct (Hd0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hm2 Hc Heq Hw2 HB Hp2) as [a2 a2' E2 E2' Hper2].
      functional_eval_rewrite_clear; exact (Hmot _ _ _ eq_refl Hper2). }
    (** The elements: the relations, the admissible bases and indices
        change ([ind_rel_change]), the right index moves ([ind_rel_idx]),
        and a declared member's elements read no given base. *)
    assert (HnB : forall m Mm kk vs vs1 vs2, ind_member D m = Some Mm -> kk < List.length (List.rev (im_nparams Mm)) ->
                    tele_prefix_rel (nr0 m) kk vs vs1 -> tele_prefix_rel (nr m) kk vs vs2 -> (nr0 m kk vs <~> nr m kk vs))
      by (intros; symmetry; eapply Hnr; eassumption).
    assert (HaB : forall m Mm ms ms1 ms2 c gs kk vs vs1 vs2, ind_member D m = Some Mm ->
               tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms ms1 -> tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms2 ->
               ind_con Mm c = Some gs -> kk < List.length (cargs_nonrec gs) ->
               tele_prefix_rel (ar0 m ms c) kk vs vs1 -> tele_prefix_rel (ar m ms c) kk vs vs2 ->
               (ar0 m ms c kk vs <~> ar m ms c kk vs))
      by (intros; symmetry; eapply Har; eassumption).
    assert (HdB : forall m Mm ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 kk ys ys1 ys2, ind_member D m = Some Mm ->
               tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms ms1 -> tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms2 ->
               ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
               tele_prefix_rel (ar0 m ms c) (List.length (cargs_nonrec gs1)) ws ws1 ->
               tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws2 ->
               kk < List.length (ptyp_doms t) ->
               tele_prefix_rel (shape_doms_rel (dr0 m) ms ws (ptyp_doms t)) kk ys ys1 ->
               tele_prefix_rel (shape_doms_rel (dr m) ms ws (ptyp_doms t)) kk ys ys2 ->
               (shape_doms_rel (dr0 m) ms ws (ptyp_doms t) kk ys <~> shape_doms_rel (dr m) ms ws (ptyp_doms t) kk ys))
      by (intros; symmetry; eapply Hdr; eassumption).
    pose proof (tele_rel_nr_change p D ups nr nr0 ar ar0 dr dr0 Hnr Har Hdr _ _ HM _ _ Hns) as Hns'.
    pose proof (tele_rel_nr_change' p D ups nr nr0 ar ar0 dr dr0 Hnr Har Hdr _ _ HM _ _ Hns0) as Hns0'.
    unfold grp_rel; intros m m'; split; intro Hm.
    - eapply (proj1 (ind_rel_base_r p D ups nr0 ar0 dr0 Hass HnP0 HnI0 HaP0 HaI0 HdP0 HdI0 ups'0 H35 _ ups'
                       (adm_change p D ups nr nr0 ar ar0 dr dr0 Hnr Har Hdr ups' H15))); [| reflexivity ].
      eapply (ind_rel_idx p D ups nr0 ar0 dr0 Hass HnP0 HnI0 HaP0 HaI0 HdP0 HdI0 _ _ _ _ _ _ ns ns' _ _ _ _ HM);
        [ eapply (proj1 (ind_rel_change p D ups nr nr0 ar ar0 dr dr0 Hnr Har Hdr _ _ _ _
                           (grp_adm_change p D ups nr nr0 ar ar0 dr dr0 Hnr Har Hdr)
                           (okr_at_change p D ups nr nr0 ar ar0 dr dr0 Hnr Har Hdr)
                           (fun m Mm a b Hm H => nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm a b H)));
          exact Hm
        | exact (nparams_rel_refl_l p D ups nr0 ar0 dr0 Hass HnP0 HnI0 HaP0 HaI0 HdP0 HdI0 _ _ HM _ _ Hns0)
        | exact (nparams_rel_trans p D ups nr0 ar0 dr0 Hass HnP0 HnI0 HaP0 HaI0 HdP0 HdI0 _ _ HM _ _ _
                   (nparams_rel_sym p D ups nr0 ar0 dr0 Hass HnP0 HnI0 HaP0 HaI0 HdP0 HdI0 _ _ HM _ _ Hns') Hns0) ].
    - eapply (proj1 (ind_rel_base_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' H15 _ ups'0
                       (adm_change p D ups nr0 nr ar0 ar dr0 dr HnB HaB HdB ups'0 H35))); [| reflexivity ].
      eapply (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ ns ns'0 _ _ _ _ HM);
        [ eapply (proj1 (ind_rel_change p D ups nr0 nr ar0 ar dr0 dr HnB HaB HdB _ _ _ _
                           (grp_adm_change p D ups nr0 nr ar0 ar dr0 dr HnB HaB HdB)
                           (okr_at_change p D ups nr0 nr ar0 ar dr0 dr HnB HaB HdB)
                           (fun m Mm a b Hm H => nparams_rel_refl_r p D ups nr0 ar0 dr0 Hass HnP0 HnI0 HaP0 HaI0 HdP0 HdI0 m Mm Hm a b H)));
          exact Hm
        | exact (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ Hns)
        | exact (nparams_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ _
                   (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ Hns0') Hns) ]. }
  specialize (IHHorig _ _ _ eq_refl equiv_a_a').
  split; intros.
  - rename equiv_c_c' into equiv0_c_c'.
    assert (equiv_c_c' : in_rel c c') by firstorder;
    (destruct_rel_mod_eval; destruct_rel_mod_app; functional_eval_rewrite_clear;
     econstructor; intuition).
  - assert (equiv0_c_c' : in_rel0 c c') by firstorder;
      (destruct_rel_mod_eval; destruct_rel_mod_app; functional_eval_rewrite_clear;
       econstructor; intuition).
Qed.

End Fixed_GCtx.

#[local]
Ltac per_univ_elem_right_irrel_assert1 :=
  match goal with
  | H1 : (DF ?a ≈ ?b ∈ per_univ_elem ?i ↘ ?R1),
      H2 : DF ?a ≈ ?b' ∈ per_univ_elem ?i' ↘ ?R2 |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_right_irrel; [apply H1 | apply H2])
      end
  end.
#[local]
Ltac per_univ_elem_right_irrel_assert := repeat per_univ_elem_right_irrel_assert1.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_univ_elem_sym : forall i R a b,
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    DF b ≈ a ∈ per_univ_elem i ↘ R /\
      (forall m m',
          Dom m ≈ m' ∈ R ->
          Dom m' ≈ m ∈ R).
Proof.
  simpl.
  per_univ_elem_induction1; subst.
  - split.
    + apply per_univ_elem_core_univ'; firstorder.
    + intros.
      rewrite H1 in *.
      destruct_by_head per_univ.
      eexists.
      eapply proj1; mautosolve.
  - (** The two levels are related, hence have the same realiser, so the
        index of the elements is the same on both sides. *)
    assert (Heq : dlvl_real l = dlvl_real l') by (apply per_lvl_real; assumption).
    split.
    + apply per_univ_elem_core_suniv';
        [ apply per_lvl_sym; assumption | rewrite <- Heq | rewrite <- Heq ]; assumption.
    + intros.
      rewrite H1 in *.
      destruct_by_head per_univ.
      eexists.
      eapply proj1; mautosolve.
  - split; [basic_per_univ_elem_econstructor | intros; apply_relation_equivalence]; mautosolve.
  - split; [basic_per_univ_elem_econstructor | intros; apply_relation_equivalence]; mautosolve.
  - split; [basic_per_univ_elem_econstructor | intros; apply_relation_equivalence]; mautosolve.
  - destruct_conjs.
    split.
    + basic_per_univ_elem_econstructor; eauto.
      intros.
      assert (in_rel c' c) by eauto.
      assert (in_rel c c) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      functional_eval_rewrite_clear.
      econstructor; eauto.
      per_univ_elem_right_irrel_assert.
      apply_relation_equivalence.
      eassumption.
    + apply_relation_equivalence.
      intros.
      assert (in_rel c' c) by eauto.
      assert (in_rel c c) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      functional_eval_rewrite_clear.
      econstructor; eauto.
      per_univ_elem_right_irrel_assert.
      intuition.
  - split; [econstructor | intros; apply_relation_equivalence]; mautosolve.
  - (** An inductive type: the same relations serve the swapped type, by
        the invariance of [nr] and [ar] along related prefixes and the
        symmetry of their types; the elements are swapped by
        [ind_rel_sym_all], their indices exchanged by [ind_rel_idx], and the
        bases admissible beside [ups] are those admissible beside [ups']
        ([adm_iff]). *)
    rename H into Hl, H0 into Hass, H1 into HM, H2 into Hh, H3 into Hu, H4 into Hu', H5 into Hps, H6 into HnP, H7 into Hn,
      H8 into HnI, H9 into HaP, H10 into Ha, H11 into HaI,
      H12 into HdP, H13 into Hd, H14 into HdI, H15 into Hcl, H16 into Hcd, H17 into Hns,
      H18 into HE.
    pose proof (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ Hns) as Hsn.
    pose proof (adm_flip p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' Hcl Hcd) as Hfl.
    split.
    + basic_per_univ_elem_econstructor;
        [ exact Hl | exact Hass | exact HM | exact Hh | exact Hu' | exact Hu | exact (per_top_ps_sym _ _ _ Hps) | exact HnP | | exact HnI
        | exact HaP | | exact HaI | exact HdP | | exact HdI | exact Hfl
        | exact (adm_diag_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' Hcl) | exact Hsn |].
      * intros m Mm k0 A vs vs' Hm Hk Hp.
        assert (Hkl : k0 < List.length (List.rev (im_nparams Mm))) by (apply List.nth_error_Some; congruence).
        pose proof (nparams_prefix_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm k0 vs vs' ltac:(lia) Hp) as Hp'.
        destruct (Hn _ _ _ _ _ _ Hm Hk Hp') as [a a' Ea Ea' (_ & Hsym & _)].
        econstructor; [ exact Ea' | exact Ea |].
        eapply per_univ_elem_resp_iff; [ exact Hsym |]; symmetry; exact (HnI _ _ _ _ _ _ Hm Hk Hp).
      * intros m Mm ms ms' c gs k0 A vs vs' Hm0 Hm Hc Hk Hp.
        assert (Hkl : k0 < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        assert (Hp' : tele_prefix_rel (ar m ms' c) k0 vs' vs)
          by (eapply (args_prefix_rel_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0); [ exact Hm | exact Hc | lia |];
              eapply (args_prefix_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0);
                [ exact (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ Hm0 _ _ Hm) | exact Hc | lia | exact Hp ]).
        destruct (Ha _ _ _ _ _ _ _ _ _ _ Hm0 (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ Hm0 _ _ Hm) Hc Hk Hp')
          as [a a' Ea Ea' (_ & Hsym & _)].
        econstructor; [ exact Ea' | exact Ea |].
        eapply per_univ_elem_resp_iff; [ exact Hsym |]; symmetry; exact (HaI _ _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Hk Hp).
      * intros m Mm ms ms' c gs gs1 t gs2 ws ws' k0 B ys ys' Hm0 Hm Hc Heq Hp HB Hy.
        assert (Hk1 : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
          by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
        assert (Hkl : k0 < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
        pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ Hm0 _ _ Hm) as Hmm.
        assert (Hp' : tele_prefix_rel (ar m ms' c) (List.length (cargs_nonrec gs1)) ws' ws)
          by (eapply (args_prefix_rel_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0); [ exact Hm | exact Hc | exact Hk1 |];
              eapply (args_prefix_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0); [ exact Hmm | exact Hc | exact Hk1 | exact Hp ]).
        pose proof (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0 ms c gs Hmm Hc _ ws ws' Hk1 Hp) as Hww.
        assert (Hy' : tele_prefix_rel (shape_doms_rel (dr m) ms' ws' (ptyp_doms t)) k0 ys' ys).
        { eapply (doms_rel_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0);
            [ exact Hm | exact Hc | exact Heq | exact Hp | lia |].
          eapply (doms_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0 ms c gs gs1 t gs2 ws Hmm Hc Heq Hww);
            [ lia | exact Hy ]. }
        destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ Hm0 _ _ Hm)
                    Hc Heq Hp' HB Hy')
          as [a a' Ea Ea' (_ & Hsym & _)].
        econstructor; [ exact Ea' | exact Ea |].
        eapply per_univ_elem_resp_iff; [ exact Hsym |]; symmetry; exact (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Heq Hp HB Hy).
      * (** The elements: at the bases admissible beside [ups'], which are
            those beside [ups] ([adm_fresh_base], [ind_rel_okr_base]), at
            the exchanged indices. *)
        unfold grp_rel; intros m m'; split; intro Hm0.
        -- apply HE in Hm0; unfold grp_rel in Hm0.
           eapply (ind_rel_idx p D ups' nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ ns ns' _ _ _ _ HM); [| exact Hns | exact Hsn ].
           apply (proj1 (ind_rel_okr_base p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' Hcl _)).
           apply (ind_rel_bases p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ ups ups' _ _ _ _ _ _ Hcd Hcl Hcl Hcd).
           apply (proj1 (ind_rel_ok p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _
                           (grp_adm_base p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' Hcl) (fun _ _ _ _ H => H))).
           exact Hm0.
        -- apply HE; unfold grp_rel.
           eapply (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ ns' ns _ _ _ _ HM); [| exact Hsn | exact Hns ].
           apply (proj1 (ind_rel_okr_base p D ups' nr ar dr Hass HnP HnI HaP HaI HdP HdI ups Hfl _)).
           apply (ind_rel_bases p D ups' nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ ups' ups _ _ _ _ _ _
                    (adm_diag_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' Hcl) Hfl Hfl
                    (adm_diag_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' Hcl)).
           apply (proj1 (ind_rel_ok p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _
                           (grp_adm_base p D ups' nr ar dr Hass HnP HnI HaP HaI HdP HdI ups Hfl) (fun _ _ _ _ H => H))).
           exact Hm0.
    + intros m m' Hm0; apply HE in Hm0; apply HE; unfold grp_rel in *.
      pose proof (proj1 (ind_rel_sym_all p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _) _ _ _ _ _ _ _ Hm0) as Hm1.
      apply (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ ns' ns _ _ _ _ HM); [| exact Hsn | exact Hns ].
      exact (ind_rel_bases p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ ups' ups _ _ _ _ _ _ Hcl Hcd Hcd Hcl Hm1).
Qed.

Corollary per_univ_sym : forall i R a b,
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    DF b ≈ a ∈ per_univ_elem i ↘ R.
Proof.
  intros * ?%per_univ_elem_sym.
  firstorder.
Qed.

Corollary per_univ_sym' : forall i a b,
    Dom a ≈ b ∈ per_univ i ->
    Dom b ≈ a ∈ per_univ i.
Proof.
  intros * [? ?%per_univ_elem_sym].
  firstorder.
Qed.

Corollary per_elem_sym : forall i R a b m m',
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    Dom m ≈ m' ∈ R ->
    Dom m' ≈ m ∈ R.
Proof.
  intros * ?%per_univ_elem_sym.
  firstorder.
Qed.

Corollary per_univ_elem_left_irrel : forall i i' R a b R' a',
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    DF a' ≈ b ∈ per_univ_elem i' ↘ R' ->
    (R <~> R').
Proof.
  intros * ?%per_univ_sym ?%per_univ_sym.
  eauto using per_univ_elem_right_irrel.
Qed.

Corollary per_univ_elem_cross_irrel : forall i i' R a b R' b',
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    DF b' ≈ a ∈ per_univ_elem i' ↘ R' ->
    (R <~> R').
Proof.
  intros * ? ?%per_univ_sym.
  eauto using per_univ_elem_right_irrel.
Qed.

End Fixed_GCtx.

Ltac do_per_univ_elem_irrel_assert1 :=
  let tactic_error o1 o2 := fail 2 "per_univ_elem_irrel biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : (DF ?a ≈ _ ∈ per_univ_elem ?i ↘ ?R1),
      H2 : DF ?a ≈ _ ∈ per_univ_elem ?i' ↘ ?R2 |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : (DF _ ≈ ?b ∈ per_univ_elem ?i ↘ ?R1),
      H2 : DF _ ≈ ?b ∈ per_univ_elem ?i' ↘ ?R2 |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : (DF ?a ≈ _ ∈ per_univ_elem ?i ↘ ?R1),
      H2 : DF _ ≈ ?a ∈ per_univ_elem ?i' ↘ ?R2 |- _ =>
      (** Order matters less here, as [H1] and [H2] cannot be exchanged. *)
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_cross_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  end.

Ltac do_per_univ_elem_irrel_assert :=
  repeat do_per_univ_elem_irrel_assert1.

Ltac handle_per_univ_elem_irrel :=
  functional_eval_rewrite_clear;
  do_per_univ_elem_irrel_assert;
  apply_relation_equivalence;
  clear_dups.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_univ_elem_trans : forall i R a1 a2,
    per_univ_elem i R a1 a2 ->
    (forall j a3,
        per_univ_elem j R a2 a3 ->
        per_univ_elem i R a1 a3) /\
      (forall m1 m2 m3,
          R m1 m2 ->
          R m2 m3 ->
          R m1 m3).
Proof.
  per_univ_elem_induction1;
    [> split;
     [ intros * HT2; basic_invert_per_univ_elem HT2
     | intros * HTR1 HTR2; apply_relation_equivalence ] ..]; mauto.
  - (** The univ case. *)
    subst.
    destruct HTR1, HTR2.
    functional_eval_rewrite_clear.
    handle_per_univ_elem_irrel.
    eexists.
    specialize (H2 _ _ _ H0) as [].
    intuition.
  - (** The small univ case.  Unlike the large one there is no equation
        between the two levels to substitute, so the transitivity of the
        elements is taken from the first of the two derivations. *)
    destruct HTR1, HTR2.
    functional_eval_rewrite_clear.
    handle_per_univ_elem_irrel.
    eexists.
    match goal with
    | HA : per_univ_elem _ ?R ?a ?b, HB : per_univ_elem _ ?R ?b ?c |- per_univ_elem _ _ ?a ?c =>
        specialize (H2 _ _ _ HA) as []
    end.
    intuition.
  - (** The [Level] case. *)
    idtac; (basic_per_univ_elem_econstructor; mautosolve 4).
  - (** The [⊤] case. *)
    idtac; (basic_per_univ_elem_econstructor; mautosolve 4).
  - (** The [⊥] case. *)
    idtac; (basic_per_univ_elem_econstructor; mautosolve 4).
  - (** The pi case. *)
    destruct_conjs.
    basic_per_univ_elem_econstructor; eauto.
    + handle_per_univ_elem_irrel.
      intuition.
    + intros.
      handle_per_univ_elem_irrel.
      assert (in_rel c c') by firstorder.
      assert (in_rel c c) by intuition.
      assert (in_rel0 c c) by intuition.
      destruct_rel_mod_eval.
      functional_eval_rewrite_clear.
      handle_per_univ_elem_irrel; (basic_per_univ_elem_econstructor; mautosolve 4).
  - (** The function case. *)
    intros.
    assert (in_rel c c) by intuition.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    handle_per_univ_elem_irrel.
    econstructor; eauto.
    intuition.
  - (** The neut case. *)
    idtac; (basic_per_univ_elem_econstructor; mautosolve 4).
  - (** An inductive type.  The relations of the first derivation serve the
        composite: those of the second agree with them along related
        prefixes, as the relations of types with a common side. *)
    assert (D0 = D) as -> by congruence.
    assert (M0 = M) as -> by congruence.
    destruct (app_split_eq _ _ _ _ x ltac:(congruence)) as [-> ->].
    rename H into Hl, H0 into Hass, H1 into HM, H2 into Hh, H3 into Hu, H4 into Hu', H5 into Hps, H6 into HnP, H7 into Hn,
      H8 into HnI, H9 into HaP, H10 into Ha, H11 into HaI, H12 into HdP, H13 into Hd, H14 into HdI,
      H15 into Hcl, H16 into Hcd, H17 into Hns, H18 into HE.
    rename H23 into Hu2, H24 into Hu2', H25 into Hps2, H26 into HnP2, H27 into Hn2, H28 into HnI2,
      H29 into HaP2, H30 into Ha2, H31 into HaI2, H32 into HdP2, H33 into Hd2, H34 into HdI2,
      H35 into Hcl2, H37 into Hns2.
    assert (Hcr : forall m Mm k pa pb pc, ind_member D m = Some Mm -> k < List.length (List.rev (im_nparams Mm)) ->
              tele_prefix_rel (nr m) k pa pb -> tele_prefix_rel (nr0 m) k pb pc -> (nr m k pa <~> nr0 m k pb)).
    { intros m Mm k0 pa pb pc Hm Hk Hp1 Hp2.
      destruct (nparams_lt_ass D m Mm k0 Hass Hm Hk) as [A HA].
      destruct (Hn _ _ _ _ _ _ Hm HA Hp1) as [a a' Ea Ea' (Hper & _)].
      destruct (Hn2 _ _ _ _ _ _ Hm HA Hp2) as [b b' Eb Eb' Hper2].
      functional_eval_rewrite_clear.
      eapply per_univ_elem_left_irrel; [ exact Hper | apply per_univ_sym; exact Hper2 ]. }
    assert (Hacr : forall m Mm ms ms' ms'' c gs k pa pb pc, ind_member D m = Some Mm ->
              tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' -> tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms' ms'' ->
              ind_con Mm c = Some gs -> k < List.length (cargs_nonrec gs) ->
              tele_prefix_rel (ar m ms c) k pa pb -> tele_prefix_rel (ar0 m ms' c) k pb pc -> (ar m ms c k pa <~> ar0 m ms' c k pb)).
    { intros m Mm ms ms' ms'' c gs k0 pa pb pc Hm0 Hm1 Hm2 Hc Hk Hp1 Hp2.
      destruct (nth_error_lt_some' _ _ Hk) as [A HA].
      destruct (Ha _ _ _ _ _ _ _ _ _ _ Hm0 Hm1 Hc HA Hp1) as [a a' Ea Ea' (Hper & _)].
      destruct (Ha2 _ _ _ _ _ _ _ _ _ _ Hm0 Hm2 Hc HA Hp2) as [b b' Eb Eb' Hper2].
      functional_eval_rewrite_clear.
      eapply per_univ_elem_left_irrel; [ exact Hper | apply per_univ_sym; exact Hper2 ]. }
    assert (HnP0 : forall m Mm k vs vs', ind_member D m = Some Mm -> k < List.length (List.rev (im_nparams Mm)) ->
              tele_prefix_rel (nr0 m) k vs vs' -> PER (nr0 m k vs))
      by (intros m Mm k0 ? ? Hm Hk ?; destruct (nparams_lt_ass D m Mm k0 Hass Hm Hk) as [A HA]; eapply HnP2; eassumption).
    assert (HnP1 : forall m Mm k vs vs', ind_member D m = Some Mm -> k < List.length (List.rev (im_nparams Mm)) ->
              tele_prefix_rel (nr m) k vs vs' -> PER (nr m k vs))
      by (intros m Mm k0 ? ? Hm Hk ?; destruct (nparams_lt_ass D m Mm k0 Hass Hm Hk) as [A HA]; eapply HnP; eassumption).
    assert (Hrefl0 : forall m Mm ms ms'', ind_member D m = Some Mm -> tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms'' ->
              tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms'' ms'').
    { intros * Hm0 Hm; eapply (tele_rel_cross_refl _ (nr m) (nr0 m)); [ | exact (fun k0 vs vs' => HnP0 m Mm k0 vs vs' Hm0) | exact Hm ].
      intros k0 pa pb Hk Hp1 Hp2; exact (Hcr _ _ _ _ _ _ Hm0 Hk Hp1 Hp2). }
    assert (Hcomp : forall m Mm a b c, ind_member D m = Some Mm ->
              tele_rel (nr m) (List.rev (im_nparams Mm)) a b -> tele_rel (nr0 m) (List.rev (im_nparams Mm)) b c ->
              tele_rel (nr m) (List.rev (im_nparams Mm)) a c).
    { intros * Hm0 H1 H2; eapply (tele_rel_compose_cross _ (nr m) (nr0 m)); [ | exact (fun k0 vs vs' => HnP1 m Mm k0 vs vs' Hm0) | exact H1 | exact H2 ].
      intros k0 pa pb pc Hk Hp1 Hp2; exact (Hcr _ _ _ _ _ _ Hm0 Hk Hp1 Hp2). }
    assert (Haprefl : forall m Mm ms ms'' c gs k vs vs'', ind_member D m = Some Mm ->
              tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms'' ->
              ind_con Mm c = Some gs -> k <= List.length (cargs_nonrec gs) ->
              tele_prefix_rel (ar m ms c) k vs vs'' -> tele_prefix_rel (ar0 m ms'' c) k vs'' vs'').
    { intros * Hm0 Hm Hc Hk Hp.
      eapply (tele_prefix_rel_cross_refl (ar m ms c) (ar0 m ms'' c) (List.length (cargs_nonrec gs))); [ exact Hk | | | exact Hp ].
      - intros j0 pa pb Hj Hp1 Hp2; exact (Hacr _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm (Hrefl0 _ _ _ _ Hm0 Hm) Hc Hj Hp1 Hp2).
      - intros j0 ? ? Hj ?; destruct (nth_error_lt_some' _ _ Hj) as [A HA].
        eapply HaP2; [ exact Hm0 | exact (Hrefl0 _ _ _ _ Hm0 Hm) | exact Hc | exact HA | eassumption ]. }
    assert (Hdcr : forall m Mm ms ms' ms'' c gs gs1 t gs2 ws ws' ws'' k ys ys' ys'', ind_member D m = Some Mm ->
              tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' -> tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms' ms'' ->
              ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
              tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
              tele_prefix_rel (ar0 m ms' c) (List.length (cargs_nonrec gs1)) ws' ws'' ->
              k < List.length (ptyp_doms t) ->
              tele_prefix_rel (shape_doms_rel (dr m) ms ws (ptyp_doms t)) k ys ys' ->
              tele_prefix_rel (shape_doms_rel (dr0 m) ms' ws' (ptyp_doms t)) k ys' ys'' ->
              (shape_doms_rel (dr m) ms ws (ptyp_doms t) k ys <~> shape_doms_rel (dr0 m) ms' ws' (ptyp_doms t) k ys')).
    { intros * Hm0 Hm1 Hm2 Hc Heq Hw1 Hw2 Hk Hp1 Hp2.
      destruct (nth_error_lt_some' _ _ Hk) as [B HB].
      unfold shape_doms_rel at 1 2; rewrite (List.nth_error_nth _ _ _ HB).
      destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm1 Hc Heq Hw1 HB Hp1) as [a a' Ea Ea' (Hper & _)].
      destruct (Hd2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm2 Hc Heq Hw2 HB Hp2) as [b b' Eb Eb' Hper2].
      functional_eval_rewrite_clear.
      eapply per_univ_elem_left_irrel; [ exact Hper | apply per_univ_sym; exact Hper2 ]. }
    assert (Hdprefl : forall m Mm ms ms'' c gs gs1 t gs2 ws ws'' k ys ys'', ind_member D m = Some Mm ->
              tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms'' ->
              ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
              tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws'' -> k <= List.length (ptyp_doms t) ->
              tele_prefix_rel (shape_doms_rel (dr m) ms ws (ptyp_doms t)) k ys ys'' ->
              tele_prefix_rel (shape_doms_rel (dr0 m) ms'' ws'' (ptyp_doms t)) k ys'' ys'').
    { intros * Hm0 Hm Hc Heq Hw Hk Hp.
      assert (Hk1 : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      pose proof (Haprefl _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Hk1 Hw) as Hw2.
      eapply (tele_prefix_rel_cross_refl (shape_doms_rel (dr m) ms ws (ptyp_doms t)) (shape_doms_rel (dr0 m) ms'' ws'' (ptyp_doms t))
                (List.length (ptyp_doms t)));
        [ exact Hk | | | exact Hp ].
      - intros j0 pa pb Hj Hp1 Hp2.
        exact (Hdcr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm (Hrefl0 _ _ _ _ Hm0 Hm) Hc Heq Hw Hw2 Hj Hp1 Hp2).
      - intros j0 ? ? Hj ?; destruct (nth_error_lt_some' _ _ Hj) as [B HB].
        unfold shape_doms_rel at 1; rewrite (List.nth_error_nth _ _ _ HB).
        eapply HdP2; [ exact Hm0 | exact (Hrefl0 _ _ _ _ Hm0 Hm) | exact Hc | exact Heq | exact Hw2 | exact HB | eassumption ]. }
    (** The second's relations are the first's along prefixes related by
        the first. *)
    assert (HnC : forall m Mm k vs vs1 vs2, ind_member D m = Some Mm -> k < List.length (List.rev (im_nparams Mm)) ->
              tele_prefix_rel (nr0 m) k vs vs1 -> tele_prefix_rel (nr m) k vs vs2 -> (nr0 m k vs <~> nr m k vs)).
    { intros m Mm k0 vs vs1 vs2 Hm Hk Hp1 Hp2; symmetry; eapply Hcr; [ exact Hm | exact Hk | | exact Hp1 ].
      eapply (nparams_prefix_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm k0 vs vs2); [ lia | exact Hp2 ]. }
    assert (HaC : forall m Mm ms ms1 ms2 c gs k vs vs1 vs2, ind_member D m = Some Mm ->
              tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms ms1 -> tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms2 ->
              ind_con Mm c = Some gs -> k < List.length (cargs_nonrec gs) ->
              tele_prefix_rel (ar0 m ms c) k vs vs1 -> tele_prefix_rel (ar m ms c) k vs vs2 ->
              (ar0 m ms c k vs <~> ar m ms c k vs)).
    { intros m Mm ms ms1 ms2 c gs k0 vs vs1 vs2 Hm0 Hm1 Hm2 Hc Hk Hp1 Hp2; symmetry.
      pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0 _ _ Hm2) as Hmm.
      eapply (Hacr m Mm ms ms ms1); [ exact Hm0 | exact Hmm | exact Hm1 | exact Hc | exact Hk | | exact Hp1 ].
      eapply (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0 ms c gs Hmm Hc k0 vs vs2);
        [ lia | exact Hp2 ]. }
    assert (HdC : forall m Mm ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 k ys ys1 ys2, ind_member D m = Some Mm ->
              tele_rel (nr0 m) (List.rev (im_nparams Mm)) ms ms1 -> tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms2 ->
              ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
              tele_prefix_rel (ar0 m ms c) (List.length (cargs_nonrec gs1)) ws ws1 ->
              tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws2 ->
              k < List.length (ptyp_doms t) ->
              tele_prefix_rel (shape_doms_rel (dr0 m) ms ws (ptyp_doms t)) k ys ys1 ->
              tele_prefix_rel (shape_doms_rel (dr m) ms ws (ptyp_doms t)) k ys ys2 ->
              (shape_doms_rel (dr0 m) ms ws (ptyp_doms t) k ys <~> shape_doms_rel (dr m) ms ws (ptyp_doms t) k ys)).
    { intros m Mm ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 k0 ys ys1 ys2 Hm0 Hm1 Hm2 Hc Heq Hw1 Hw2 Hk Hp1 Hp2; symmetry.
      assert (Hk1 : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0 _ _ Hm2) as Hmm.
      pose proof (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0 ms c gs Hmm Hc _ ws ws2 Hk1 Hw2)
        as Hww.
      eapply (Hdcr m Mm ms ms ms1 c gs gs1 t gs2 ws ws ws1 k0 ys ys ys1);
        [ exact Hm0 | exact Hmm | exact Hm1 | exact Hc | exact Heq | exact Hww | exact Hw1 | exact Hk | | exact Hp1 ].
      eapply (doms_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm Hm0 ms c gs gs1 t gs2 ws Hmm Hc Heq Hww);
        [ lia | exact Hp2 ]. }
    pose proof (adm_flip p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' Hcl Hcd) as Hfl.
    basic_per_univ_elem_econstructor;
      [ exact Hl | exact Hass | exact HM | exact Hh | exact Hu | exact Hu2' | exact (per_top_ps_trans _ _ _ _ Hps Hps2)
      | exact HnP | | exact HnI | exact HaP | | exact HaI | exact HdP | | exact HdI | | exact Hcd
      | exact (Hcomp _ _ _ _ _ HM Hns Hns2) | ].
    + intros m Mm k0 A vs vs'' Hm Hk Hp.
      assert (Hkl : k0 < List.length (List.rev (im_nparams Mm))) by (apply List.nth_error_Some; congruence).
      assert (Hp2 : tele_prefix_rel (nr0 m) k0 vs'' vs'').
      { eapply (tele_prefix_rel_cross_refl (nr m) (nr0 m) (List.length (List.rev (im_nparams Mm))));
          [ lia | | exact (fun j0 vs1 vs2 => HnP0 m Mm j0 vs1 vs2 Hm) | exact Hp ].
        intros j0 pa pb Hj Hp1 Hp2; exact (Hcr _ _ _ _ _ _ Hm Hj Hp1 Hp2). }
      destruct (Hn _ _ _ _ _ _ Hm Hk Hp) as [a a' Ea Ea' (_ & Htr & _)].
      destruct (Hn2 _ _ _ _ _ _ Hm Hk Hp2) as [b b' Eb Eb' Hper2].
      functional_eval_rewrite_clear.
      econstructor; [ exact Ea | exact Eb' |].
      apply (Htr j); eapply per_univ_elem_resp_iff; [ exact Hper2 |]; symmetry; exact (Hcr _ _ _ _ _ _ Hm Hkl Hp Hp2).
    + intros m Mm ms ms'' c gs k0 A vs vs'' Hm0 Hm Hc Hk Hp.
      assert (Hkl : k0 < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
      pose proof (Haprefl m Mm ms ms'' c gs k0 vs vs'' Hm0 Hm Hc ltac:(lia) Hp) as Hp2.
      destruct (Ha _ _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Hk Hp) as [a a' Ea Ea' (_ & Htr & _)].
      destruct (Ha2 _ _ _ _ _ _ _ _ _ _ Hm0 (Hrefl0 _ _ _ _ Hm0 Hm) Hc Hk Hp2) as [b b' Eb Eb' Hper2].
      functional_eval_rewrite_clear.
      econstructor; [ exact Ea | exact Eb' |].
      apply (Htr j); eapply per_univ_elem_resp_iff; [ exact Hper2 |]; symmetry;
        exact (Hacr _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm (Hrefl0 _ _ _ _ Hm0 Hm) Hc Hkl Hp Hp2).
    + intros m Mm ms ms'' c gs gs1 t gs2 ws ws'' k0 B ys ys'' Hm0 Hm Hc Heq Hw HB Hy.
      assert (Hk1 : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      assert (Hkl : k0 < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
      pose proof (Haprefl _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Hk1 Hw) as Hw2.
      pose proof (Hdprefl m Mm ms ms'' c gs gs1 t gs2 ws ws'' k0 ys ys'' Hm0 Hm Hc Heq Hw ltac:(lia) Hy) as Hy2.
      destruct (Hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Heq Hw HB Hy) as [a a' Ea Ea' (_ & Htr & _)].
      destruct (Hd2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 (Hrefl0 _ _ _ _ Hm0 Hm) Hc Heq Hw2 HB Hy2) as [b b' Eb Eb' Hper2].
      pose proof (Hdcr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm (Hrefl0 _ _ _ _ Hm0 Hm) Hc Heq Hw Hw2 Hkl Hy Hy2) as Hdd.
      unfold shape_doms_rel in Hdd; rewrite (List.nth_error_nth _ _ _ HB) in Hdd.
      functional_eval_rewrite_clear.
      econstructor; [ exact Ea | exact Eb' |].
      apply (Htr j); eapply per_univ_elem_resp_iff; [ exact Hper2 |]; symmetry; exact Hdd.
    + apply (adm_compose p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups'); [ exact Hcl |].
      exact (adm_change p D ups' nr0 nr ar0 ar dr0 dr HnC HaC HdC _ Hcl2).
    + (** The elements: the right base moved to the composite's
          ([ind_rel_base_r]), at the composite's right index
          ([ind_rel_idx]). *)
      pose proof (Hcomp _ _ _ _ _ HM Hns Hns2) as Hns13.
      pose proof (nparams_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ _
                    (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ Hns) Hns13) as Hns3.
      pose proof (adm_compose p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' _ Hcl
                    (adm_change p D ups' nr0 nr ar0 ar dr0 dr HnC HaC HdC _ Hcl2)) as Hc3.
      pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ Hns) as Hnn.
      unfold grp_rel in *; intros m m'; split; intro Hm; [ apply HE in Hm | apply HE ].
      * eapply (proj1 (ind_rel_base_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups'0 Hc3 _ ups' Hcl)); [| reflexivity ].
        exact (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hnn Hns3).
      * eapply (proj1 (ind_rel_base_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ups' Hcl _ ups'0 Hc3)); [| reflexivity ].
        exact (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ HM Hm Hnn
                 (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ Hns3)).
  - (** Its elements: the second's left base moved to the first's
        right one ([ind_rel_bases]). *)
    unfold grp_rel in *.
    eapply (proj1 (ind_rel_trans_all p D ups nr ar dr H0 H6 H8 H9 H11 H12 H14 _ _)); [ exact HTR1 |].
    exact (ind_rel_bases p D ups nr ar dr H0 H6 H8 H9 H11 H12 H14 _ _ ups ups' _ _ _ _ _ _ H16 H15 H15 H15 HTR2).
Qed.

Corollary per_univ_trans : forall i j R a1 a2 a3,
    per_univ_elem i R a1 a2 ->
    per_univ_elem j R a2 a3 ->
    per_univ_elem i R a1 a3.
Proof.
  intros * ?%per_univ_elem_trans.
  firstorder.
Qed.

Corollary per_univ_trans' : forall i j a1 a2 a3,
    Dom a1 ≈ a2 ∈ per_univ i ->
    Dom a2 ≈ a3 ∈ per_univ j ->
    Dom a1 ≈ a3 ∈ per_univ i.
Proof.
  intros * [? ?] [? ?].
  handle_per_univ_elem_irrel.
  firstorder mauto using per_univ_trans.
Qed.

Corollary per_elem_trans : forall i R a1 a2 m1 m2 m3,
    per_univ_elem i R a1 a2 ->
    R m1 m2 ->
    R m2 m3 ->
    R m1 m3.
Proof.
  intros * ?% per_univ_elem_trans.
  firstorder.
Qed.

#[local] Instance per_univ_PER {i R} : PER (per_univ_elem i R).
Proof.
  split.
  - auto using per_univ_sym.
  - eauto using per_univ_trans.
Qed.

#[local] Instance per_univ_PER' {i} : PER (per_univ i).
Proof.
  split.
  - auto using per_univ_sym'.
  - eauto using per_univ_trans'.
Qed.

#[local] Instance per_elem_PER {i R a b} `(H : per_univ_elem i R a b) : PER R.
Proof.
  split.
  - pose proof (fun m m' => per_elem_sym _ _ _ _ m m' H). eauto.
  - pose proof (fun m0 m1 m2 => per_elem_trans _ _ _ _ m0 m1 m2 H); eauto.
Qed.

(** [per_elem_PER] from a chain, so that [solve_chain_PER] need not read a
    pair off it first. *)
#[local] Instance per_elem_chain_PER {i R l} `(H : rel_chain (per_univ_elem i R) l) : PER R.
Proof.
  destruct (rel_chain_shape _ _ H) as [a [b [l' ->]]].
  eapply per_elem_PER; pairwise.
Qed.

(** ** Chains of Types

    A semantic type judgment provides a chain in [per_univ i], each link with
    its own element PER.  What its consumer needs is the whole chain at one
    PER, namely the one the judgment's element chain lives in.
    [per_univ_chain_at_in] refines the chain to the PER of any one of its
    pairs; this is the only use of irrelevance in the completeness proof.

    The proof uses irrelevance twice, through the left value [x] of the given
    pair: first to the pair [(x, u)], which shares [x], then to [(u, v)],
    which shares [u]. *)
Lemma per_univ_chain_at_in : forall {i R l x y},
    rel_chain (per_univ i) l ->
    In x l ->
    In y l ->
    DF x ≈ y ∈ per_univ_elem i ↘ R ->
    rel_chain (per_univ_elem i R) l.
Proof.
  intros * Hchain Hx Hy HR.
  destruct (rel_chain_shape _ _ Hchain) as [a [b [l' ->]]].
  apply rel_chain_intro; intros u v Hu Hv.
  assert (Hxu : Dom x ≈ u ∈ per_univ i) by pairwise.
  destruct Hxu as [Rxu HRxu].
  assert (HRxu' : DF x ≈ u ∈ per_univ_elem i ↘ R)
    by (eapply per_univ_elem_resp_iff; [ exact HRxu |];
        eapply per_univ_elem_right_irrel; [ exact HRxu | exact HR ]).
  assert (Huv : Dom u ≈ v ∈ per_univ i) by pairwise.
  destruct Huv as [Ruv HRuv].
  eapply per_univ_elem_resp_iff; [ exact HRuv |].
  eapply per_univ_elem_cross_irrel; [ exact HRuv | exact HRxu' ].
Qed.

(** Weak functionality of [per_univ i]: a chain in it is a chain at one
    element PER, with no anchor needed.  This is the paper's [S ⊆_R ↘ R'];
    [per_univ_chain_at_in] is the case where the caller fixes [R'].  All the
    links' PERs are equivalent, so the first is taken. *)
Corollary per_univ_chain_functional : forall {i l},
    rel_chain (per_univ i) l ->
    exists R, rel_chain (per_univ_elem i R) l.
Proof.
  intros * Hchain.
  destruct (rel_chain_shape _ _ Hchain) as [a [b [l' ->]]].
  assert (Hab : Dom a ≈ b ∈ per_univ i) by pairwise.
  destruct Hab as [R HR].
  exists R.
  eapply per_univ_chain_at_in; [ exact Hchain | | | exact HR ]; solve_in.
Qed.

End Fixed_GCtx.

#[export] Existing Instance per_univ_PER.
#[export] Existing Instance per_univ_PER'.
#[export] Existing Instance per_elem_PER.
#[export] Existing Instance per_elem_chain_PER.
(** Names the element PER of a chain in [per_univ i] and refines the chain to
    it, in place.  Nothing is lost: every pair of the chain remains available
    at [R] through [pairwise]. *)
Ltac functionalize_per_univ_chain H R :=
  apply per_univ_chain_functional in H; destruct H as [R H].

Section Fixed_GCtx.
  Context {GC : GCtx}.


End Fixed_GCtx.

(** [pairwise] at a [per_univ i] goal, supplying the existential that the
    refined chain no longer carries. *)
Ltac pairwise_univ := first [ pairwise | eexists; pairwise ].

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** The other half of weak functionality: the output PER is unique, so
    [S ⊆_R ↘ R'] is well defined.  One value shared with any other element of
    the universe determines [R']: the chain is at a PER, so it is reflexive at
    that value, and irrelevance then needs no second value. *)
Lemma per_univ_chain_rel_irrel : forall {i j R R' l x y},
    rel_chain (per_univ_elem i R) l ->
    DF x ≈ y ∈ per_univ_elem j ↘ R' ->
    In x l ->
    R <~> R'.
Proof.
  intros * Hchain Hanchor Hx.
  assert (Hxx : DF x ≈ x ∈ per_univ_elem i ↘ R)
    by (eapply rel_chain_refl; first [ eassumption | solve_chain_PER ]).
  eapply per_univ_elem_right_irrel; [ exact Hxx | exact Hanchor ].
Qed.

End Fixed_GCtx.

(** [retype_rel_chain Htyp Hanchor H] moves [H] between the element PER of the
    type chain [Htyp] and the one [Hanchor] names.  The two need share only
    one value.  Only [H] determines the direction, so both are tried.  [H] may
    be a [rel_chain] (rewritten through [rel_chain_Proper]) or a bare pair,
    either at the relation itself or under the [per_head] of a type the anchor
    is about. *)
Ltac retype_rel_chain Htyp Hanchor H :=
  let Hiff := fresh "Hiff" in
  pose proof (per_univ_chain_rel_irrel Htyp Hanchor ltac:(solve_in)) as Hiff;
  first [ rewrite Hiff in H | rewrite <- Hiff in H ];
  clear Hiff.

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** The [per_univ_elem] rule for [Π] without its PER premise. *)
Lemma per_univ_elem_pi' :
  forall i a a' ρ B ρ' B'
    (in_rel : relation domain)
    (out_rel : forall {c c'} (equiv_c_c' : Dom c ≈ c' ∈ in_rel), relation domain)
    elem_rel,
    DF a ≈ a' ∈ per_univ_elem i ↘ in_rel ->
    (forall {c c'} (equiv_c_c' : Dom c ≈ c' ∈ in_rel),
        rel_mod_eval (per_univ_elem i) B (ρ ↦ c) B' (ρ' ↦ c') (out_rel equiv_c_c')) ->
    (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : Dom c ≈ c' ∈ in_rel), rel_mod_app f c f' c' (out_rel equiv_c_c')) ->
    DF Πᵈ a ρ B ≈ Πᵈ a' ρ' B' ∈ per_univ_elem i ↘ elem_rel.
Proof.
  intros.
  basic_per_univ_elem_econstructor; eauto.
  typeclasses eauto.
Qed.

End Fixed_GCtx.

Ltac per_univ_elem_econstructor :=
  (repeat intro; hnf; eapply per_univ_elem_pi') + basic_per_univ_elem_econstructor.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Hint Resolve per_univ_elem_pi' : mctt.

Lemma per_univ_elem_pi_clean_inversion : forall {i j a a' in_rel ρ ρ' B B' elem_rel},
    DF a ≈ a' ∈ per_univ_elem i ↘ in_rel ->
    DF Πᵈ a ρ B ≈ Πᵈ a' ρ' B' ∈ per_univ_elem j ↘ elem_rel ->
    exists (out_rel : forall {c c'} (equiv_c_c' : Dom c ≈ c' ∈ in_rel), relation domain),
      (forall c c' (equiv_c_c' : Dom c ≈ c' ∈ in_rel),
          rel_mod_eval (per_univ_elem j) B (ρ ↦ c) B' (ρ' ↦ c') (out_rel equiv_c_c')) /\
        (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : Dom c ≈ c' ∈ in_rel), rel_mod_app f c f' c' (out_rel equiv_c_c')).
Proof.
  intros * Ha HΠ.
  basic_invert_per_univ_elem HΠ.
  handle_per_univ_elem_irrel.
  eexists.
  split.
  - instantiate (1 := fun c c' (equiv_c_c' : in_rel c c') m m' =>
                        forall R,
                          rel_mod_eval (per_univ_elem j) B (ρ ↦ c) B' (ρ' ↦ c') R ->
                          R m m').
    intros.
    assert (in_rel0 c c') by intuition.
    (on_all_hyp: destruct_rel_by_assumption in_rel0).
    econstructor; eauto.
    apply -> per_univ_elem_morphism_iff; eauto.
    split; intuition.
    destruct_by_head rel_mod_eval.
    handle_per_univ_elem_irrel.
    intuition.
  - split; intros;
      [assert (in_rel0 c c') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel0)
      | assert (in_rel c c') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel)];
      econstructor; intuition.
    destruct_by_head rel_mod_eval.
    handle_per_univ_elem_irrel.
    intuition.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve per_univ_elem_pi' : mctt.
Ltac invert_per_univ_elem H :=
  (unshelve eapply (per_univ_elem_pi_clean_inversion _) in H; shelve_unifiable; [eassumption |]; destruct H as [? []])
  + basic_invert_per_univ_elem H.

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** Cumulativity, along the order of universe indices: in particular, a
    small universe is in every large one. *)
Lemma per_univ_elem_cumu_uidx : forall i a0 a1 R,
    DF a0 ≈ a1 ∈ per_univ_elem i ↘ R ->
    forall i', uidx_le i i' ->
    DF a0 ≈ a1 ∈ per_univ_elem i' ↘ R.
Proof.
  simpl.
  per_univ_elem_induction1; intros; subst;
    per_univ_elem_econstructor; eauto; try solve_uidx.
  1: intros; destruct_rel_mod_eval; econstructor; solve [eauto].
  (** An inductive type: its telescopes, lifted one by one. *)
  all: unfold nparams_evals, args_evals, doms_evals in *; intros;
    match goal with
    | H : forall m Mm, _ |- rel_mod_eval _ _ _ _ _ _ =>
        edestruct H as [a a' Ea Ea' [_ HIH]]; try eassumption;
        econstructor; [ exact Ea | exact Ea' | apply HIH; assumption ]
    end.
Qed.

Lemma per_univ_elem_cumu : forall (i : nat) a0 a1 R,
    DF a0 ≈ a1 ∈ per_univ_elem i ↘ R ->
    DF a0 ≈ a1 ∈ per_univ_elem (S i) ↘ R.
Proof.
  intros; eapply per_univ_elem_cumu_uidx; [ eassumption | cbn; lia ].
Qed.

Hint Resolve per_univ_elem_cumu : mctt.

Lemma per_univ_elem_cumu_ge : forall (i i' : nat) a0 a1 R,
    i <= i' ->
    DF a0 ≈ a1 ∈ per_univ_elem i ↘ R ->
    DF a0 ≈ a1 ∈ per_univ_elem i' ↘ R.
Proof.
  intros; eapply per_univ_elem_cumu_uidx; [ eassumption | cbn; lia ].
Qed.

Hint Resolve per_univ_elem_cumu_ge : mctt.

Lemma per_univ_elem_cumu_max_left : forall (i j : nat) a0 a1 R,
    DF a0 ≈ a1 ∈ per_univ_elem i ↘ R ->
    DF a0 ≈ a1 ∈ per_univ_elem (max i j) ↘ R.
Proof.
  intros.
  assert (i <= max i j) by lia; mautosolve.
Qed.

Lemma per_univ_elem_cumu_max_right : forall (i j : nat) a0 a1 R,
    DF a0 ≈ a1 ∈ per_univ_elem j ↘ R ->
    DF a0 ≈ a1 ∈ per_univ_elem (max i j) ↘ R.
Proof.
  intros.
  assert (j <= max i j) by lia; mautosolve.
Qed.


Lemma per_elem_subtyping : forall A B i,
    Sub A <: B at i ->
    forall R R' a b,
      DF A ≈ A ∈ per_univ_elem i ↘ R ->
      DF B ≈ B ∈ per_univ_elem i ↘ R' ->
      R a b ->
      R' a b.
Proof.
  induction 1; intros;
    handle_per_univ_elem_irrel;
    saturate_refl;
    (on_all_hyp: fun H => directed invert_per_univ_elem H);
    handle_per_univ_elem_irrel;
    clear_refl_eqs;
    trivial.
  (** The types of levels: the levels of a smaller sort are levels of the
      larger one. *)
  1: eapply per_lvl_at_mono; eassumption.
  - firstorder mauto.
  (** The three universe cases cumulate the elements of the smaller universe
      to the larger: inside the large tier along the order on levels, inside
      the small one along the order on the realisers, which [per_sublvl]
      bounds, and across the tiers immediately. *)
  -
    destruct_conjs; eexists; eapply per_univ_elem_cumu_uidx;
      [ eassumption
      | cbn; first [ apply per_sublvl_real; assumption | exact I | lia ] ].
  -
    destruct_conjs; eexists; eapply per_univ_elem_cumu_uidx;
      [ eassumption
      | cbn; first [ apply per_sublvl_real; assumption | exact I | lia ] ].
  - intros.
    handle_per_univ_elem_irrel.
    destruct_rel_mod_eval.
    saturate_refl_for per_univ_elem.
    destruct_rel_mod_app.
    simplify_evals.
    econstructor; eauto.
    intuition.
Qed.

Lemma per_subtyp_refl1 : forall a b i R,
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    Sub a <: b at i.
Proof.
  simpl; per_univ_elem_induction1;
    subst;
    (** A small universe is below another with a related level, at the index
        of the realiser both levels share. *)
    try (match goal with
         | H : per_lvl ?l ?l' |- per_subtyp ?i 𝕌@?l 𝕌@?l' =>
             apply per_subtyp_suniv;
               [ apply per_sublvl_of_per_lvl; exact H
               | rewrite <- (per_lvl_real _ _ H); assumption ]
         end);
    mauto;
    destruct_all.
  (** An inductive type: rebuilt without the induction hypotheses. *)
  2: { eapply per_subtyp_indty; basic_per_univ_elem_econstructor; try eassumption;
       unfold nparams_evals, args_evals, doms_evals in *; intros; eapply rel_mod_eval_proj1;
       match goal with H : forall m Mm, _ |- _ => eapply H; eassumption end. }
  assert (DF Πᵈ a ρ B ≈ Πᵈ a' ρ' B' ∈ per_univ_elem i ↘ elem_rel)
    by (eapply per_univ_elem_pi'; eauto; intros; destruct_rel_mod_eval; mauto).
  saturate_refl.
  econstructor; eauto.
  intros;
    destruct_rel_mod_eval;
    functional_eval_rewrite_clear;
    trivial.
Qed.

Hint Resolve per_subtyp_refl1 : mctt.

Lemma per_subtyp_refl2 : forall a b i R,
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    Sub b <: a at i.
Proof.
  intros.
  symmetry in H.
  eauto using per_subtyp_refl1.
Qed.

Hint Resolve per_subtyp_refl2 : mctt.

Lemma per_subtyp_trans : forall a1 a2 i,
    Sub a1 <: a2 at i ->
    forall a3,
      Sub a2 <: a3 at i ->
      Sub a1 <: a3 at i.
Proof.
  induction 1; intros ? Hsub; simpl in *.
  1-8: progressive_inversion; mauto.
  all: try solve [ econstructor; solve [ lia | solve_uidx ] ].
  - (** A small universe below a small one, which is in turn below either a
        small or a large one: the first composes by the transitivity of the
        order on levels, the second needs only that the left level is
        readable. *)
    inversion Hsub; subst;
      [ eapply per_subtyp_suniv; [ eapply per_sublvl_trans; eassumption | eassumption ]
      | eapply per_subtyp_small_large; [ eapply per_sublvl_left; eassumption | eassumption ] ].
  - dependent destruction Hsub.
    handle_per_univ_elem_irrel.
    econstructor; eauto.
    + etransitivity; [ exact H | eassumption ].
    + intros.
      saturate_refl.
      (on_all_hyp: fun H => directed invert_per_univ_elem H).
      destruct_rel_mod_eval.
      handle_per_univ_elem_irrel.
      intuition.
  - (** Inductive types: their equalities compose. *)
    inversion Hsub as [| | | | | | | | ? ? ? ? ? R' HR']; subst.
    match goal with H : per_univ_elem _ ?R (d_ind _ _ _) (d_ind _ _ _) |- _ =>
      assert (HRR : R <~> R') by (eapply per_univ_elem_left_irrel; [ exact H | apply per_univ_sym; exact HR' ]);
      eapply per_subtyp_indty; eapply per_univ_trans; [ exact H | eapply per_univ_elem_resp_iff; [ exact HR' | symmetry; exact HRR ] ]
    end.
Qed.

Hint Resolve per_subtyp_trans : mctt.

#[local] Instance per_subtyp_trans_ins i : Transitive (per_subtyp i).
Proof.
  eauto using per_subtyp_trans.
Qed.

Lemma per_subtyp_transp : forall a b i a' b' R R',
    Sub a <: b at i ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    DF b ≈ b' ∈ per_univ_elem i ↘ R' ->
    Sub a' <: b' at i.
Proof.
  mauto using per_subtyp_refl1, per_subtyp_refl2.
Qed.

Lemma per_subtyp_cumu_uidx : forall a1 a2 i,
    Sub a1 <: a2 at i ->
    forall j,
      uidx_le i j ->
      Sub a1 <: a2 at j.
Proof.
  induction 1; intros; econstructor; eauto using per_univ_elem_cumu_uidx; solve_uidx.
Qed.

Lemma per_subtyp_cumu : forall a1 a2 (i : nat),
    Sub a1 <: a2 at i ->
    forall (j : nat),
      i <= j ->
      Sub a1 <: a2 at j.
Proof.
  intros; eapply per_subtyp_cumu_uidx; [ eassumption | cbn; lia ].
Qed.

Hint Resolve per_subtyp_cumu : mctt.

Lemma per_subtyp_cumu_left : forall a1 a2 (i j : nat),
    Sub a1 <: a2 at i ->
    Sub a1 <: a2 at max i j.
Proof.
  intros. eapply per_subtyp_cumu; try eassumption.
  lia.
Qed.

Lemma per_subtyp_cumu_right : forall a1 a2 (i j : nat),
    Sub a1 <: a2 at i ->
    Sub a1 <: a2 at max j i.
Proof.
  intros. eapply per_subtyp_cumu; try eassumption.
  lia.
Qed.

(** * The Module PER is a PER *)

(** ** Related Types, Seen from Either Side *)

Lemma rel_typ_sym : forall {i A ρ A' ρ' R},
    rel_typ i A ρ A' ρ' R ->
    rel_typ i A' ρ' A ρ R /\ (forall m m', R m m' -> R m' m).
Proof.
  intros * [a a' Ha Ha' HR]; pose proof (per_univ_elem_sym _ _ _ _ HR) as [HR' Hs].
  split; [ econstructor; eassumption | exact Hs ].
Qed.

Lemma rel_typ_trans : forall {i j A1 ρ1 A2 ρ2 A3 ρ3 R R'},
    rel_typ i A1 ρ1 A2 ρ2 R ->
    rel_typ j A2 ρ2 A3 ρ3 R' ->
    (R <~> R') /\ rel_typ i A1 ρ1 A3 ρ3 R /\ (forall m1 m2 m3, R m1 m2 -> R m2 m3 -> R m1 m3).
Proof.
  intros * [a1 a2 H1 H2 HR] [a2' a3 H2' H3 HR'].
  functional_eval_rewrite_clear.
  assert (HRR' : R <~> R') by first [ symmetry; eapply per_univ_elem_cross_irrel; [ exact HR' | exact HR ]
                                     | eapply per_univ_elem_cross_irrel; [ exact HR | exact HR' ] ].
  split; [ exact HRR' | split ].
  - econstructor; [ eassumption | eassumption |].
    eapply per_univ_trans; [ exact HR |].
    eapply per_univ_elem_resp_iff; [ exact HR' | symmetry; exact HRR' ].
  - intros; eapply per_elem_trans; eassumption.
Qed.

Lemma rel_elem_sym : forall {i A ρ A' ρ' R M M'},
    rel_typ i A ρ A' ρ' R ->
    rel_elem M ρ M' ρ' R -> rel_elem M' ρ' M ρ R.
Proof.
  intros * HT [m m' Hm Hm' HR]; destruct (rel_typ_sym HT) as [_ Hs].
  econstructor; [ eassumption | eassumption | apply Hs; exact HR ].
Qed.

Lemma rel_elem_trans : forall {i j A1 ρ1 A2 ρ2 A3 ρ3 R R' M1 M2 M3},
    rel_typ i A1 ρ1 A2 ρ2 R ->
    rel_typ j A2 ρ2 A3 ρ3 R' ->
    rel_elem M1 ρ1 M2 ρ2 R -> rel_elem M2 ρ2 M3 ρ3 R' -> rel_elem M1 ρ1 M3 ρ3 R.
Proof.
  intros * HT HT' [m1 m2 H1 H2 HR] [m2' m3 H2' H3 HR'].
  functional_eval_rewrite_clear.
  destruct (rel_typ_trans HT HT') as (HRR' & _ & Ht).
  econstructor; [ eassumption | eassumption |].
  eapply Ht; [ exact HR | apply HRR'; exact HR' ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve per_univ_elem_cumu : mctt.
#[export]
Hint Resolve per_univ_elem_cumu_ge : mctt.
#[export]
Hint Resolve per_subtyp_refl1 : mctt.
#[export]
Hint Resolve per_subtyp_refl2 : mctt.
#[export]
Hint Resolve per_subtyp_trans : mctt.
#[export] Existing Instance per_subtyp_trans_ins.
#[export]
Hint Resolve per_subtyp_cumu : mctt.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Module Values *)

Lemma functional_eval_appm : forall h n r1 r2,
    $ᵐ| h & n | gc_deps ⍮ gc_stack ↘ r1 -> $ᵐ| h & n | gc_deps ⍮ gc_stack ↘ r2 -> r1 = r2.
Proof. intros * H1 H2; pose proof (@functional_eval gc_deps gc_stack) as Hf; destruct_all; eauto. Qed.

Lemma functional_eval_close : forall Δ D ρ h1 h2,
    ⟦ Δ ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ h1 -> ⟦ Δ ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ h2 -> h1 = h2.
Proof. intros * H1 H2; pose proof (@functional_eval gc_deps gc_stack) as Hf; destruct_all; eauto. Qed.

Lemma nextparam_functional : forall h a1, nextparam h a1 -> forall a2, nextparam h a2 -> a1 = a2.
Proof.
  induction 1; intros a2 H2; inversion H2; subst; auto.
  - match goal with H : _ ++ _ :: nil = _ ++ _ :: nil |- _ => apply app_inj_tail in H as [<- [= <-]] end.
    eapply functional_eval_exp; eassumption.
  - match goal with H1 : gc_loc _ _ ?p = Some _, H2 : gc_loc _ _ ?p = Some _ |- _ => rewrite H1 in H2; injection H2 as <- <- end.
    match goal with H1 : nth_error ?l ?n = Some _, H2 : nth_error ?l ?n = Some _ |- _ => rewrite H1 in H2; injection H2 as -> end.
    eapply functional_eval_exp; eassumption.
Qed.

(** A saturated value lacks no parameter. *)
Lemma nextparam_global_sat : forall p T Φ args a,
    gc_loc gc_deps gc_stack p = Some (T, Φ) -> List.length args = List.length T ->
    nextparam (dm_global p args) a -> False.
Proof.
  intros * Hm Hl Hn; inversion Hn; subst.
  match goal with H1 : gc_loc _ _ ?p = Some _ |- _ => rewrite Hm in H1; injection H1 as <- <- end.
  match goal with Hx : nth_error _ _ = Some _ |- _ =>
    assert (Hx' : nth_error (rev T) (length args) <> None) by congruence end.
  apply nth_error_Some in Hx'; rewrite length_rev in Hx'; lia.
Qed.

Lemma nextparam_body_nil : forall sm Φ ρ a, nextparam (dm_local nil (md_body sm Φ) ρ) a -> False.
Proof. intros * Hn; inversion Hn; subst; destruct Δ; discriminate. Qed.

Lemma per_gargs_len_eq : forall ts ρ ρ' args args', per_gargs ts ρ ρ' args args' -> length args = length args'.
Proof. induction 1; cbn; congruence. Qed.

(** The expansion and environment of one body read twice are one. *)
Ltac solve_mid_body :=
  repeat match goal with
    | H1 : kbody _ _ ?ρ ?Φ ?Φ1, H2 : kbody _ _ ?ρ ?Φ ?Φ2 |- _ =>
        assert_fails (constr_eq Φ1 Φ2); pose proof (functional_kbody _ _ _ _ H1 H2); subst Φ2
    | H1 : eval_benv _ _ ?ρ ?Φ ?r1, H2 : eval_benv _ _ ?ρ ?Φ ?r2 |- _ =>
        assert_fails (constr_eq r1 r2); assert (r1 = r2) by (eapply functional_eval_benv; eassumption); subst r2
    end.

(** ** Symmetry *)

Lemma per_dmod_sym_all :
  (forall m m', per_dmod m m' -> per_dmod m' m) /\
  (forall ts ρ ρ' args args', per_gargs ts ρ ρ' args args' -> per_gargs ts ρ' ρ args' args) /\
  (forall ρ Φ ρ' Φ', per_body ρ Φ ρ' Φ' -> per_body ρ' Φ' ρ Φ).
Proof.
  apply per_dmod_mut_ind_all; intros;
    try match goal with Hr : rel_typ _ _ _ _ _ _ |- _ => destruct (rel_typ_sym Hr) as [? Hs] end;
    try solve [ econstructor; eauto using rel_elem_sym ].
  - assert (Hl : length args = length args') by (eapply per_gargs_len_eq; eassumption).
    econstructor; [ eassumption | congruence | assumption ].
  - (* a missing parameter *)
    match goal with Hu : per_univ_elem _ _ _ _ |- _ => destruct (per_univ_elem_sym _ _ _ _ Hu) as [Hu' Hs] end.
    eapply per_dmod_fun; [ eassumption | eassumption | exact Hu' | | |].
    1,2: intros c c' Hc; apply Hs in Hc; eauto.
    intros c c' hc hc' Hc Hh Hh'.
    match goal with IH : forall c c' hc hc', R c c' -> _ -> _ -> per_dmod hc' hc |- _ => apply (IH c' c hc' hc) end;
      [ apply Hs, Hc | assumption | assumption ].
Qed.

Corollary per_dmod_sym : forall m m', per_dmod m m' -> per_dmod m' m.
Proof. exact (proj1 per_dmod_sym_all). Qed.

Corollary per_body_sym : forall ρ Φ ρ' Φ', per_body ρ Φ ρ' Φ' -> per_body ρ' Φ' ρ Φ.
Proof. exact (proj2 (proj2 per_dmod_sym_all)). Qed.

(** ** Transitivity *)

Lemma per_dmod_trans_all :
  (forall m1 m2, per_dmod m1 m2 -> forall m3, per_dmod m2 m3 -> per_dmod m1 m3) /\
  (forall ts ρ1 ρ2 a1 a2, per_gargs ts ρ1 ρ2 a1 a2 ->
     forall ρ3 a3, per_gargs ts ρ2 ρ3 a2 a3 -> per_gargs ts ρ1 ρ3 a1 a3) /\
  (forall ρ1 Φ1 ρ2 Φ2, per_body ρ1 Φ1 ρ2 Φ2 -> forall ρ3 Φ3, per_body ρ2 Φ2 ρ3 Φ3 -> per_body ρ1 Φ1 ρ3 Φ3).
Proof.
  apply per_dmod_mut_ind_all; intros.
  - (* global *)
    match goal with H : per_dmod _ _ |- _ => inversion H; subst; clear H end.
    + match goal with H1 : gc_loc _ _ ?p = Some _, H2 : gc_loc _ _ ?p = Some _ |- _ =>
        rewrite H1 in H2; injection H2 as <- <- end.
      econstructor; eauto.
    + match goal with HL : List.length ?args = _, HG : per_gargs _ _ _ ?args ?args' |- _ =>
        exfalso; eapply nextparam_global_sat; [ eassumption | | eassumption ];
        rewrite <- HL; symmetry; eapply per_gargs_len_eq; exact HG end.
  - (* bodies *)
    match goal with H : per_dmod _ _ |- _ => inversion H; subst; clear H end.
    + econstructor; eauto.
    + exfalso; eapply nextparam_body_nil; eassumption.
  - (* a missing parameter: the middle side is quantified against itself *)
    match goal with H : per_dmod _ _ |- _ => inversion H; subst; clear H end.
    + exfalso; eapply nextparam_global_sat; eassumption.
    + exfalso; eapply nextparam_body_nil; eassumption.
    + match goal with H1 : nextparam ?h ?a1, H2 : nextparam ?h ?a2 |- _ =>
        pose proof (nextparam_functional _ _ H1 _ H2) as <-; clear H2 end.
      match goal with H1 : per_univ_elem ?i ?R ?a ?a', H2 : per_univ_elem ?j ?R' ?a' ?a'' |- _ =>
        rename H1 into Hu1; rename H2 into Hu2 end.
      destruct (per_univ_elem_sym _ _ _ _ Hu1) as [Hu1s Hs1].
      pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hu1s Hu2) as Eq.
      assert (Hu2' : per_univ_elem _ R _ _) by (eapply per_univ_elem_resp_iff; [ exact Hu2 | symmetry; exact Eq ]).
      destruct (per_univ_elem_trans _ _ _ _ Hu1) as [Ht Htr].
      eapply per_dmod_fun; [ eassumption | eassumption | exact (Ht _ _ Hu2') | | |].
      { intros c c3 Hc; assert (Hcc : R c c) by (eapply Htr; [ exact Hc | apply Hs1; exact Hc ]).
        match goal with E : forall c c', R c c' -> exists hc, eval_appm _ _ h c hc |- _ => exact (E _ _ Hcc) end. }
      { intros c c3 Hc; assert (Hc3 : R c3 c3) by (eapply Htr; [ apply Hs1; exact Hc | exact Hc ]).
        match goal with |- exists hc', eval_appm _ _ ?h3 c3 hc' =>
          match goal with E : forall c c', ?R2 c c' -> exists hc', eval_appm _ _ h3 c' hc' |- _ =>
            exact (E _ _ (ltac:(apply Eq; exact Hc3))) end end. }
      intros c c3 hc hc3 Hc Hh Hh3.
      assert (Hc3 : R c3 c3) by (eapply Htr; [ apply Hs1; exact Hc | exact Hc ]).
      match goal with Hex : forall c c', R c c' -> exists hc', eval_appm _ _ ?h2 c' hc', Hh3' : eval_appm _ _ ?h3 c3 hc3,
                      H2 : forall c c' hc hc', _ -> eval_appm _ _ ?h2 c hc -> eval_appm _ _ ?h3 c' hc' -> per_dmod hc hc' |- _ =>
        destruct (Hex c3 c3 Hc3) as (hc2 & Hh2);
        assert (Hm23 : per_dmod hc2 hc3) by (apply (H2 c3 c3); [ apply Eq; exact Hc3 | exact Hh2 | exact Hh3' ]) end.
      match goal with IH : forall c c' hc hc', R c c' -> _ -> _ -> forall m3, per_dmod hc' m3 -> per_dmod hc m3 |- _ =>
        exact (IH c c3 hc hc2 Hc Hh Hh2 _ Hm23) end.
  - (* global arguments *)
    match goal with H : per_gargs _ _ _ _ _ |- _ => inversion H; subst; clear H end; constructor.
  - match goal with H : per_gargs _ _ _ (_ :: _) _ |- _ => inversion H; subst; clear H end.
    match goal with H1 : rel_typ _ _ _ _ _ _, H2 : rel_typ _ _ _ _ _ _ |- _ =>
      destruct (rel_typ_trans H1 H2) as (HRR & HT & Ht) end.
    econstructor; [ exact HT | eapply Ht; [ eassumption | apply HRR; eassumption ] | eauto ].
  - match goal with H : per_body _ _ _ _ |- _ => inversion H; subst; clear H end; constructor.
  - (* a definition: the middle expansion and environment are one *)
    match goal with H : per_body _ (gm_ext _ _ _) _ _ |- _ => inversion H; subst; clear H end.
    solve_mid_body.
    match goal with H1 : rel_typ _ _ _ _ _ _, H2 : rel_typ _ _ _ _ _ _ |- _ =>
      destruct (rel_typ_trans H1 H2) as (HRR & HT & Ht) end.
    econstructor; eauto using rel_elem_trans.
  - (* a module: the middle closure is one value *)
    match goal with H : per_body _ (gm_ext _ _ _) _ _ |- _ => inversion H; subst; clear H end.
    solve_mid_body.
    match goal with H1 : eval_close _ _ ?Δ ?D ?ρ ?h1, H2 : eval_close _ _ ?Δ ?D ?ρ ?h2 |- _ =>
      assert_fails (constr_eq h1 h2); assert (h1 = h2) by (eapply functional_eval_close; eassumption); subst end.
    econstructor; eauto.
  - (* an open: the middle target is one value *)
    match goal with H : per_body _ (gm_open _ _ _) _ _ |- _ => inversion H; subst; clear H end.
    solve_mid_body.
    match goal with H1 : eval_modexp _ _ ?H ?ρ ?h1, H2 : eval_modexp _ _ ?H ?ρ ?h2 |- _ =>
      assert_fails (constr_eq h1 h2); assert (h1 = h2) by (eapply functional_eval_modexp; eassumption); subst end.
    econstructor; eauto.
Qed.

Corollary per_dmod_trans : forall m1 m2 m3, per_dmod m1 m2 -> per_dmod m2 m3 -> per_dmod m1 m3.
Proof. intros; eapply (proj1 per_dmod_trans_all); eassumption. Qed.

Corollary per_body_trans : forall ρ1 Φ1 ρ2 Φ2 ρ3 Φ3, per_body ρ1 Φ1 ρ2 Φ2 -> per_body ρ2 Φ2 ρ3 Φ3 -> per_body ρ1 Φ1 ρ3 Φ3.
Proof. intros; eapply (proj2 (proj2 per_dmod_trans_all)); eassumption. Qed.

#[export] Instance per_dmod_PER : PER per_dmod.
Proof. split; [ exact per_dmod_sym | exact per_dmod_trans ]. Qed.

(** ** Module Expressions Evaluating to Related Values *)

Lemma rel_mexp_sym : forall H ρ H' ρ', rel_mexp H ρ H' ρ' -> rel_mexp H' ρ' H ρ.
Proof. intros * [h h' Hh Hh' Hr]; exists h' h; [ exact Hh' | exact Hh | apply per_dmod_sym, Hr ]. Qed.

Lemma rel_mexp_trans : forall H1 ρ1 H2 ρ2 H3 ρ3, rel_mexp H1 ρ1 H2 ρ2 -> rel_mexp H2 ρ2 H3 ρ3 -> rel_mexp H1 ρ1 H3 ρ3.
Proof.
  intros * [h1 h2 Hh1 Hh2 Hr] [h2' h3 Hh2' Hh3 Hr'].
  pose proof (functional_eval_modexp _ _ _ _ Hh2 Hh2') as <-.
  exists h1 h3; [ exact Hh1 | exact Hh3 | eapply per_dmod_trans; eassumption ].
Qed.

Lemma tie_mod_move : forall m H ρ H' ρ', tie_mod m H ρ -> rel_mexp H ρ H' ρ' -> tie_mod m H' ρ'.
Proof.
  intros * (h & Hh & Hm) [h1 h' Hh1 Hh' Hr].
  pose proof (functional_eval_modexp _ _ _ _ Hh Hh1) as <-.
  exists h'; split; [ exact Hh' | eapply per_dmod_trans; eassumption ].
Qed.

Lemma tie_mod_rel : forall m H ρ m' H' ρ', tie_mod m H ρ -> tie_mod m' H' ρ' -> rel_mexp H ρ H' ρ' -> per_dmod m m'.
Proof.
  intros * (h & Hh & Hm) (h' & Hh' & Hm') [h1 h1' Hh1 Hh1' Hr].
  pose proof (functional_eval_modexp _ _ _ _ Hh Hh1) as <-; pose proof (functional_eval_modexp _ _ _ _ Hh' Hh1') as <-.
  eapply per_dmod_trans; [ exact Hm | eapply per_dmod_trans; [ exact Hr | apply per_dmod_sym, Hm' ] ].
Qed.

(** The values of two module expressions related over related tails, read
    at two related tails in either combination. *)
Lemma rel_mexp_move : forall (T : relation env) H H' ρ1 ρ2,
    PER T -> T ρ1 ρ2 ->
    (forall ρ ρ', T ρ ρ' -> rel_mexp H ρ H' ρ') ->
    rel_mexp H ρ1 H ρ2 /\ rel_mexp H ρ1 H' ρ2 /\ rel_mexp H' ρ1 H ρ2 /\ rel_mexp H' ρ1 H' ρ2.
Proof.
  intros * HT H12 HP.
  assert (H11 : T ρ1 ρ1) by (etransitivity; [ exact H12 | symmetry; exact H12 ]).
  assert (H22 : T ρ2 ρ2) by (etransitivity; [ symmetry; exact H12 | exact H12 ]).
  pose proof (HP _ _ H12) as A; pose proof (HP _ _ H11) as B; pose proof (HP _ _ H22) as C.
  assert (D1 : rel_mexp H ρ1 H ρ2) by (eapply rel_mexp_trans; [ exact A | apply rel_mexp_sym; exact C ]).
  split; [ exact D1 | split; [ exact A | split ] ].
  - eapply rel_mexp_trans; [ apply rel_mexp_sym; exact B | exact D1 ].
  - eapply rel_mexp_trans; [ apply rel_mexp_sym; exact B | exact A ].
Qed.

Add Parametric Morphism : per_ctx_env
    with signature (@relation_equivalence env) ==> eq ==> eq ==> iff as per_ctx_env_morphism_iff.
Proof.
  intros R R' HRR'.
  split; intro Horig; [gen R' | gen R];
    induction Horig; econstructor;
    apply_relation_equivalence; try reflexivity; mautosolve.
Qed.

Add Parametric Morphism : per_ctx_env
    with signature (@relation_equivalence env) ==> (@relation_equivalence ctx) as per_ctx_env_morphism_relation_equivalence.
Proof.
  intros * HRR' Γ Γ'.
  simpl.
  rewrite HRR'.
  reflexivity.
Qed.

(** ** Closures *)

(** A closure given its outermost argument is the closure of the rest over
    the environment extended by it. *)
Lemma appm_local_inv : forall Δ A D ρ c hc h,
    $ᵐ| dm_local (Δ ++ ce_ass A :: nil) D ρ & c | gc_deps ⍮ gc_stack ↘ hc ->
    ⟦ Δ ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↦ c ↘ h -> hc = h.
Proof.
  intros * Ha Hc; inversion Ha; subst.
  match goal with H : _ ++ _ :: nil = _ ++ _ :: nil |- _ => apply app_inj_tail in H as [<- _] end.
  eapply functional_eval_close; eassumption.
Qed.

(** Two closures lacking their outermost parameter are related when, at
    every related pair of arguments, the closures of the rest over the
    environments extended by them evaluate to related values. *)
Lemma per_dmod_closure_step : forall ρ ρ' Δ Δ' A A' D D' i R a a',
    ⟦ A ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ a -> ⟦ A' ⟧ gc_deps ⍮ gc_stack ⍮ ρ' ↘ a' -> per_univ_elem i R a a' ->
    (forall c c', R c c' -> exists h h', ⟦ Δ ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↦ c ↘ h /\
                                     ⟦ Δ' ⊢ D' ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ' ↦ c' ↘ h' /\ per_dmod h h') ->
    per_dmod (dm_local (Δ ++ ce_ass A :: nil) D ρ) (dm_local (Δ' ++ ce_ass A' :: nil) D' ρ').
Proof.
  intros * Ha Ha' HR HD.
  destruct (per_univ_elem_sym _ _ _ _ HR) as [_ Hs].
  destruct (per_univ_elem_trans _ _ _ _ HR) as [_ Htr].
  eapply per_dmod_fun; [ constructor; exact Ha | constructor; exact Ha' | exact HR | | |].
  - intros c c' Hc; destruct (HD _ _ Hc) as (h & _ & Hh & _); eexists; constructor; exact Hh.
  - intros c c' Hc; destruct (HD _ _ Hc) as (_ & h' & _ & Hh' & _); eexists; constructor; exact Hh'.
  - intros c c' hc hc' Hc Hh Hh'.
    destruct (HD _ _ Hc) as (h & h' & Hc1 & Hc2 & Hr).
    rewrite (appm_local_inv _ _ _ _ _ _ _ Hh Hc1), (appm_local_inv _ _ _ _ _ _ _ Hh' Hc2); exact Hr.
Qed.


End Fixed_GCtx.

#[export] Existing Instance per_ctx_env_morphism_iff_Proper.
#[export] Existing Instance per_ctx_env_morphism_relation_equivalence_Proper.

(** A head tied to the value of one module expression is tied to the value
    of any expression related to it over the same tail. *)
Ltac solve_tie :=
  match goal with
  | |- tie_mod ?m ?H2 ?r =>
      first [ assumption
            | match goal with
              | Ht : tie_mod m ?H1 ?r1, Hm : rel_mexp ?H1 ?r1 H2 r |- _ => exact (tie_mod_move _ _ _ _ _ Ht Hm)
              end
            | match goal with
              | Ht : tie_mod m ?H1 r, HU : forall ρ ρ', ?T ρ ρ' -> rel_mexp ?H1 ρ H2 ρ', Hr : ?T r r |- _ =>
                  exact (tie_mod_move _ _ _ _ _ Ht (HU _ _ Hr))
              end
            | match goal with
              | Ht : tie_mod m ?H1 r, HU : forall ρ ρ', ?T ρ ρ' -> rel_mexp H2 ρ ?H1 ρ', Hr : ?T r r |- _ =>
                  exact (tie_mod_move _ _ _ _ _ Ht (rel_mexp_sym _ _ _ _ (HU _ _ Hr)))
              end ]
  end.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma per_ctx_env_right_irrel : forall Γ Δ Δ' R R',
    DF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    DF Γ ≈ Δ' ∈ per_ctx_env ↘ R' ->
    R <~> R'.
Proof.
  intros * Horig; gen Δ' R'.
  induction Horig; intros * Hright;
    inversion Hright; subst;
    apply_relation_equivalence;
    try reflexivity.
  specialize (IHHorig _ _ equiv_Γ_Γ'0).
  intros ρ ρ'.
  split; intros [].
  - assert (Dom ρ↯ ≈ ρ'↯ ∈ tail_rel0) by intuition;
      (destruct_rel_typ; handle_per_univ_elem_irrel; eexists; intuition).
  - assert (Dom ρ↯ ≈ ρ'↯ ∈ tail_rel) by intuition;
      (destruct_rel_typ; handle_per_univ_elem_irrel; eexists; intuition).
  - (** A definition: the heads are tied to the bodies, which are related
        across the two right-hand contexts through the left body. *)
    specialize (IHHorig _ _ equiv_Γ_Γ'0).
    intros ρ ρ'.
    split; intros [Ht ?];
      [ assert (Ht0 : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel0) by intuition
      | assert (Ht0 : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel) by intuition ];
      exists Ht0; destruct_conjs;
      (** The bodies are read at each tail against itself, too. *)
      assert (Dom ρ↯ ≈ ρ↯ ∈ tail_rel) by (etransitivity; [| symmetry]; intuition);
      assert (Dom ρ'↯ ≈ ρ'↯ ∈ tail_rel) by (etransitivity; [symmetry |]; intuition);
      assert (Dom ρ↯ ≈ ρ↯ ∈ tail_rel0) by (etransitivity; [| symmetry]; intuition);
      assert (Dom ρ'↯ ≈ ρ'↯ ∈ tail_rel0) by (etransitivity; [symmetry |]; intuition);
      destruct_rel_typ; handle_per_univ_elem_irrel;
      match goal with H : per_univ_elem _ _ _ _ |- _ => pose proof (per_elem_PER H) end;
      move_by_relation_equivalence;
      repeat split; try (move_goal_by_relation_equivalence; solve_per);
      eexists; split; try eassumption; move_goal_by_relation_equivalence; solve_per.
  - (** A slot: the heads are tied to the closures of the left unit, which
        are related to the closures of either right unit. *)
    specialize (IHHorig _ _ equiv_Γ_Γ'0).
    intros ρ ρ'.
    split; intros (Ht & ? & ? & ? & ?);
      [ assert (Ht0 : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel0) by intuition
      | assert (Ht0 : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel) by intuition ];
      assert (Dom ρ↯ ≈ ρ↯ ∈ tail_rel) by (etransitivity; [| symmetry]; intuition);
      assert (Dom ρ'↯ ≈ ρ'↯ ∈ tail_rel) by (etransitivity; [symmetry |]; intuition);
      assert (Dom ρ↯ ≈ ρ↯ ∈ tail_rel0) by (etransitivity; [| symmetry]; intuition);
      assert (Dom ρ'↯ ≈ ρ'↯ ∈ tail_rel0) by (etransitivity; [symmetry |]; intuition);
      repeat split; try assumption; solve_tie.
Qed.

Lemma per_ctx_env_sym : forall Γ Δ R,
    DF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    DF Δ ≈ Γ ∈ per_ctx_env ↘ R /\
      (forall ρ ρ',
          Dom ρ ≈ ρ' ∈ R ->
          Dom ρ' ≈ ρ ∈ R).
Proof.
  simpl.
  induction 1.
  1,2: split; simpl in *; destruct_conjs; try econstructor; intuition;
    pose proof (@relation_equivalence_pointwise env).
  - assert (tail_rel ρ' ρ) by eauto.
    assert (tail_rel ρ ρ) by (etransitivity; eassumption).
    destruct_rel_mod_eval.
    handle_per_univ_elem_irrel.
    econstructor; eauto.
    symmetry; solve [intuition].
  - apply_relation_equivalence.
    destruct_conjs.
    assert (tail_rel ρ'↯ ρ↯) by eauto.
    assert (tail_rel ρ↯ ρ↯) by (etransitivity; eassumption).
    destruct_rel_mod_eval.
    eexists; symmetry; handle_per_univ_elem_irrel; intuition.
  - (** A definition.  The swapped context has the same head relation, and its
        environment relation lists the same four ties in another order. *)
    simpl in *; destruct_conjs.
    split.
    + eapply per_ctx_env_cons_def with (head_rel := head_rel); [ eassumption | eassumption | | |].
      * intros ρ ρ' Hρ.
        assert (tail_rel ρ' ρ) by eauto.
        assert (tail_rel ρ ρ) by (etransitivity; eassumption).
        destruct_rel_mod_eval.
        handle_per_univ_elem_irrel.
        econstructor; eauto.
        symmetry; solve [intuition].
      * intros ρ ρ' Hρ.
        assert (tail_rel ρ' ρ) by eauto.
        assert (tail_rel ρ ρ) by (etransitivity; eassumption).
        destruct_rel_mod_eval.
        handle_per_univ_elem_irrel.
        match goal with H : per_univ_elem _ _ _ _ |- _ => pose proof (per_elem_PER H) end.
        move_by_relation_equivalence.
        econstructor; try eassumption.
        move_goal_by_relation_equivalence; solve_per.
      * intros ρ ρ'; split; intros Hρ;
          [ apply H2 in Hρ | apply H2 ]; destruct Hρ as [e Hρ]; exists e; tauto.
    + intros ρ ρ' Hρ.
      apply H2 in Hρ; apply H2.
      destruct Hρ as [e ?]; destruct_conjs.
      assert (Ht : tail_rel ρ'↯ ρ↯) by eauto.
      exists Ht.
      assert (tail_rel ρ↯ ρ↯) by (etransitivity; eassumption).
      assert (tail_rel ρ'↯ ρ'↯) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      handle_per_univ_elem_irrel.
      match goal with H : per_univ_elem _ _ _ _ |- _ => pose proof (per_elem_PER H) end.
      move_by_relation_equivalence.
      repeat split; try (move_goal_by_relation_equivalence; solve_per);
        eexists; split; try eassumption; move_goal_by_relation_equivalence; solve_per.
  - (** A slot.  The swapped context ties the heads to the same closures. *)
    simpl in *; destruct_conjs.
    match goal with
    | HU : forall ρ ρ', tail_rel ρ ρ' -> rel_mexp _ _ _ _,
      HE : env_rel <~> _, Hs : forall ρ ρ', tail_rel ρ ρ' -> tail_rel ρ' ρ |- _ =>
        split;
        [ eapply per_ctx_env_cons_mod; [ eassumption | eassumption | | ];
          [ intros ρ ρ' Hρ; apply rel_mexp_sym, HU, Hs, Hρ
          | intros ρ ρ'; split; intros Hρ; [ apply HE in Hρ | apply HE ]; destruct_conjs; repeat split; assumption ]
        | intros ρ ρ' Hρ; apply HE in Hρ; apply HE; destruct_conjs; repeat split; eauto ]
    end.
Qed.

Corollary per_ctx_sym : forall Γ Δ R,
    DF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    DF Δ ≈ Γ ∈ per_ctx_env ↘ R.
Proof.
  intros * ?%per_ctx_env_sym.
  firstorder.
Qed.

Corollary per_env_sym : forall Γ Δ R ρ ρ',
    DF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    Dom ρ ≈ ρ' ∈ R ->
    Dom ρ' ≈ ρ ∈ R.
Proof.
  intros * ?%per_ctx_env_sym.
  firstorder.
Qed.

Corollary per_ctx_env_left_irrel : forall Γ Γ' Δ R R',
    DF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    DF Γ' ≈ Δ ∈ per_ctx_env ↘ R' ->
    R <~> R'.
Proof.
  intros * ?%per_ctx_sym ?%per_ctx_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Corollary per_ctx_env_cross_irrel : forall Γ Δ Δ' R R',
    DF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    DF Δ' ≈ Γ ∈ per_ctx_env ↘ R' ->
    R <~> R'.
Proof.
  intros * ? ?%per_ctx_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

End Fixed_GCtx.


(** The ties of a definition entry, closed from the instances of the type and
    body premises at the tails in context: the head relations of one type
    value coincide, and the ties follow by symmetry and transitivity. *)
Ltac solve_def_heads :=
  destruct_rel_typ; handle_per_univ_elem_irrel;
  match goal with H : per_univ_elem _ _ _ _ |- _ => pose proof (per_elem_PER H) end;
  move_by_relation_equivalence;
  repeat split; try (move_goal_by_relation_equivalence; solve_per);
  try (eexists; split; [ eassumption | move_goal_by_relation_equivalence; solve_per ]).

Ltac do_per_ctx_env_irrel_assert1 :=
  let tactic_error o1 o2 := fail 3 "per_ctx_env_irrel equality between" o1 "and" o2 "cannot be solved" in
  match goal with
    | H1 : (DF ?Γ ≈ _ ∈ per_ctx_env ↘ ?R1),
        H2 : DF ?Γ ≈ _ ∈ per_ctx_env ↘ ?R2 |- _ =>
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    | H1 : (DF _ ≈ ?Δ ∈ per_ctx_env ↘ ?R1),
        H2 : DF _ ≈ ?Δ ∈ per_ctx_env ↘ ?R2 |- _ =>
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    | H1 : (DF ?Γ ≈ _ ∈ per_ctx_env ↘ ?R1),
        H2 : DF _ ≈ ?Γ ∈ per_ctx_env ↘ ?R2 |- _ =>
        (** Order matters less here, as [H1] and [H2] cannot be exchanged. *)
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_cross_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    end.

Ltac do_per_ctx_env_irrel_assert :=
  repeat do_per_ctx_env_irrel_assert1.

Ltac handle_per_ctx_env_irrel :=
  functional_eval_rewrite_clear;
  do_per_ctx_env_irrel_assert;
  apply_relation_equivalence;
  clear_dups.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_ctx_env_trans : forall Γ1 Γ2 R,
    DF Γ1 ≈ Γ2 ∈ per_ctx_env ↘ R ->
    (forall Γ3,
        DF Γ2 ≈ Γ3 ∈ per_ctx_env ↘ R ->
        DF Γ1 ≈ Γ3 ∈ per_ctx_env ↘ R) /\
      (forall ρ1 ρ2 ρ3,
          Dom ρ1 ≈ ρ2 ∈ R ->
          Dom ρ2 ≈ ρ3 ∈ R ->
          Dom ρ1 ≈ ρ3 ∈ R).
Proof with solve [eauto using per_univ_trans].
  simpl.
  induction 1; subst;
    [> split;
     [ inversion 1; subst; eauto
     | intros; destruct_conjs; eauto] ..];
    pose proof (@relation_equivalence_pointwise env);
    handle_per_ctx_env_irrel;
    try solve [intuition].
  - econstructor; only 4: reflexivity; eauto.
    + apply_relation_equivalence. intuition.
    + intros.
      assert (tail_rel ρ ρ) by intuition.
      assert (tail_rel0 ρ ρ') by intuition.
      destruct_rel_typ.
      handle_per_univ_elem_irrel.
      econstructor; intuition.
      (** This cannot be [etransitivity], as the two levels [i] differ. *)
      eapply per_univ_trans; [| eassumption]; eassumption.
  - destruct_conjs.
    assert (tail_rel ρ1↯ ρ3↯) by eauto.
    destruct_rel_typ.
    handle_per_univ_elem_irrel.
    eexists.
    apply_relation_equivalence.
    etransitivity; intuition.
  - (** A definition: the right body is moved across the middle one. *)
    destruct IHper_ctx_env as [IHctx IHenv].
    eapply per_ctx_env_cons_def with (head_rel := head_rel); [ eauto | eassumption | | |].
    + intros.
      assert (tail_rel ρ ρ) by intuition.
      assert (tail_rel0 ρ ρ') by intuition.
      destruct_rel_typ.
      handle_per_univ_elem_irrel.
      econstructor; intuition.
      eapply per_univ_trans; [| eassumption]; eassumption.
    + intros.
      assert (tail_rel ρ ρ) by intuition.
      assert (tail_rel0 ρ ρ') by intuition.
      assert (tail_rel0 ρ ρ) by intuition.
      destruct_rel_typ; handle_per_univ_elem_irrel.
      econstructor; try eassumption.
      solve_def_heads.
    + intros ρ ρ'; split; intros [Ht ?]; destruct_conjs; exists Ht;
        assert (tail_rel ρ↯ ρ↯) by (etransitivity; [| symmetry]; eassumption);
        assert (tail_rel ρ'↯ ρ'↯) by (etransitivity; [symmetry |]; eassumption);
        assert (tail_rel0 ρ↯ ρ↯) by intuition;
        assert (tail_rel0 ρ'↯ ρ'↯) by intuition;
        assert (tail_rel0 ρ↯ ρ'↯) by intuition;
        solve_def_heads.
  - cbn beta in *; destruct_conjs.
    assert (Ht : tail_rel ρ1↯ ρ3↯) by eauto.
    exists Ht.
    assert (tail_rel ρ1↯ ρ1↯) by (etransitivity; [| symmetry]; eassumption).
    assert (tail_rel ρ3↯ ρ3↯) by (etransitivity; [symmetry |]; eassumption).
    solve_def_heads.
  - (** A slot: the closures of the first unit are related to those of the
        last through the middle unit. *)
    destruct IHper_ctx_env as [IHctx IHenv].
    match goal with
    | HU1 : forall ρ ρ', ?T ρ ρ' -> rel_mexp (me_lit ?U1) ρ (me_lit ?U2) ρ',
      HU2 : forall ρ ρ', ?T ρ ρ' -> rel_mexp (me_lit ?U2) ρ (me_lit ?U3) ρ',
      HE : _ <~> _, HT : PER ?T, Hc : per_ctx_env ?T ?Γ2 ?Γ3 |- per_ctx_env _ (?Γ1 ▹ₘ ?U1) (?Γ3 ▹ₘ ?U3) =>
        eapply per_ctx_env_cons_mod with (tail_rel := T);
        [ apply IHctx; exact Hc | exact HT
        | intros ρ ρ' Hρ; eapply rel_mexp_trans;
          [ apply HU1, Hρ | apply HU2; etransitivity; [ symmetry |]; exact Hρ ]
        | intros ρ ρ'; split; intros Hρ;
          [ pose proof (proj2 (HE ρ ρ') Hρ) as Hρ'; destruct Hρ' as (Ht & ? & ? & ? & ?);
            destruct Hρ as (_ & ? & ? & ? & ?); repeat split; assumption
          | destruct Hρ as (Ht & ? & ? & ? & ?);
            assert (T ρ↯ ρ↯) by (etransitivity; [| symmetry ]; exact Ht);
            assert (T ρ'↯ ρ'↯) by (etransitivity; [ symmetry |]; exact Ht);
            repeat split; try assumption; solve_tie ] ]
    end.
Qed.

Corollary per_ctx_trans : forall Γ1 Γ2 Γ3 R,
    DF Γ1 ≈ Γ2 ∈ per_ctx_env ↘ R ->
    DF Γ2 ≈ Γ3 ∈ per_ctx_env ↘ R ->
    DF Γ1 ≈ Γ3 ∈ per_ctx_env ↘ R.
Proof.
  intros * ?% per_ctx_env_trans.
  firstorder.
Qed.

Corollary per_env_trans : forall Γ1 Γ2 R ρ1 ρ2 ρ3,
    DF Γ1 ≈ Γ2 ∈ per_ctx_env ↘ R ->
    Dom ρ1 ≈ ρ2 ∈ R ->
    Dom ρ2 ≈ ρ3 ∈ R ->
    Dom ρ1 ≈ ρ3 ∈ R.
Proof.
  intros * ?% per_ctx_env_trans.
  firstorder.
Qed.

#[local] Instance per_ctx_PER {R} : PER (per_ctx_env R).
Proof.
  split.
  - auto using per_ctx_sym.
  - eauto using per_ctx_trans.
Qed.

#[local] Instance per_env_PER {R Γ Δ} (H : per_ctx_env R Γ Δ) : PER R.
Proof.
  split.
  - pose proof (fun ρ ρ' => per_env_sym _ _ _ ρ ρ' H); auto.
  - pose proof (fun ρ0 ρ1 ρ2 => per_env_trans _ _ _ ρ0 ρ1 ρ2 H); eauto.
Qed.

(** [per_ctx_env_cons] without its PER premise. *)
Lemma per_ctx_env_cons' : forall {Γ Γ' i A A' tail_rel}
                             (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), relation domain)
                             env_rel,
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel ->
    (forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel),
        rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
    (env_rel <~> fun ρ ρ' =>
         exists (equiv_ρ_drop_ρ'_drop : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel),
           Dom (ρ 0) ≈ (ρ' 0) ∈ head_rel equiv_ρ_drop_ρ'_drop) ->
    EF Γ ▹ A ≈ Γ' ▹ A' ∈ per_ctx_env ↘ env_rel.
Proof.
  intros.
  econstructor; eauto.
  typeclasses eauto.
Qed.

Hint Resolve per_ctx_env_cons' : mctt.

End Fixed_GCtx.

#[export] Existing Instance per_ctx_PER.
#[export] Existing Instance per_env_PER.
#[export]
Hint Resolve per_ctx_env_cons' : mctt.
Ltac per_ctx_env_econstructor :=
  (repeat intro; hnf; eapply per_ctx_env_cons') + econstructor.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_ctx_env_cons_clean_inversion : forall {Γ Γ' env_relΓ A A' env_relΓA},
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ env_relΓ ->
    EF Γ ▹ A ≈ Γ' ▹ A' ∈ per_ctx_env ↘ env_relΓA -> 
    exists i (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ env_relΓ), relation domain),
      (forall ρ ρ' (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ env_relΓ),
          rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) /\
        (env_relΓA <~> fun ρ ρ' =>
             exists (equiv_ρ_drop_ρ'_drop : Dom ρ↯ ≈ ρ'↯ ∈ env_relΓ),
               Dom (ρ 0) ≈ (ρ' 0) ∈ head_rel equiv_ρ_drop_ρ'_drop).
Proof.
  intros * HΓ HΓA.
  inversion HΓA; subst.
  handle_per_ctx_env_irrel.
  eexists.
  eexists.
  split; intros.
  - instantiate (1 := fun ρ ρ' (equiv_ρ_ρ' : env_relΓ ρ ρ') m m' =>
                        forall R,
                          rel_typ i A ρ A' ρ' R ->
                          Dom m ≈ m' ∈ R).
    assert (tail_rel ρ ρ') by intuition.
    (on_all_hyp: destruct_rel_by_assumption tail_rel).
    econstructor; eauto.
    apply -> per_univ_elem_morphism_iff; eauto.
    split; intros; intuition.
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel; intuition.
  - intros ρ ρ'.
    split; intros; destruct_conjs;
      assert (Dom ρ↯ ≈ ρ'↯ ∈ tail_rel) by intuition;
      (on_all_hyp: destruct_rel_by_assumption tail_rel);
      unshelve eexists; intros; intuition.
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel; intuition.
Qed.

End Fixed_GCtx.

Ltac invert_per_ctx_env H :=
  (unshelve eapply (per_ctx_env_cons_clean_inversion _) in H; [eassumption | |]; destruct H as [? [? []]])
  + (inversion H; subst).

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** ** A Canonical Extended Context PER

    [per_ctx_env_cons] leaves the head relation of an extended context
    existentially quantified and indexed by the evidence relating the tails.
    The completeness cases for substitutions build the context PER of
    [Δ ▹ S] and relate four environments in it, so they would have to produce
    the head evidence once per link of the chain.

    [per_head] names the head relation once, impredicatively:
    [per_head S S' ρ ρ'] relates what every [per_univ_elem] relating the
    values of [S] and [S'] in [ρ] and [ρ'] relates.  [per_ctx_extend] makes
    the same choice.  [per_head] does not mention the tail evidence, so the
    extended PER [per_env_extend] is a conjunction rather than a dependent
    pair. *)

Definition per_head (S S' : typ) (ρ ρ' : env) : relation domain :=
  fun m m' =>
    forall i R a a',
      ⟦ S ⟧ ρ ↘ a ->
      ⟦ S' ⟧ ρ' ↘ a' ->
      DF a ≈ a' ∈ per_univ_elem i ↘ R ->
      Dom m ≈ m' ∈ R.

Definition per_env_extend (S S' : typ) (R : relation env) : relation env :=
  fun ρ ρ' =>
    Dom ρ↯ ≈ ρ'↯ ∈ R /\
      Dom (ρ 0) ≈ (ρ' 0) ∈ per_head S S' ρ↯ ρ'↯.

(** [per_head] is the PER the types denote, because evaluation is functional
    and [per_univ_elem] is irrelevant in its relation argument.  This direction
    has the content, and it is the one completeness needs: a [per_head] from
    an element PER already at hand. *)
Lemma per_head_of : forall {S S' ρ ρ' i R a a' m m'},
    ⟦ S ⟧ ρ ↘ a ->
    ⟦ S' ⟧ ρ' ↘ a' ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    Dom m ≈ m' ∈ R ->
    Dom m ≈ m' ∈ per_head S S' ρ ρ'.
Proof.
  intros * Ha Ha' HR Hm.
  hnf; intros * Ha0 Ha0' HR0.
  functional_eval_rewrite_clear.
  handle_per_univ_elem_irrel.
  eassumption.
Qed.

(** The converse instantiates the universal quantification at the witness. *)
Corollary per_head_iff : forall {S S' ρ ρ' i R a a'},
    ⟦ S ⟧ ρ ↘ a ->
    ⟦ S' ⟧ ρ' ↘ a' ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    R <~> per_head S S' ρ ρ'.
Proof.
  intros * Ha Ha' HR m m'; split.
  - intros Hm. eapply per_head_of; eassumption.
  - intros Hm. eapply Hm; eassumption.
Qed.

(** Hence any related pair of type values is a [per_univ_elem] at the head PER
    of the expressions they came from.  A type judgment reports a level and an
    anonymous element PER, whereas a semantic recursion needs its motive at the
    head PER; this lemma keeps the level and replaces the PER. *)
Corollary per_univ_elem_at_head : forall {S S' ρ ρ' i a a'},
    ⟦ S ⟧ ρ ↘ a ->
    ⟦ S' ⟧ ρ' ↘ a' ->
    Dom a ≈ a' ∈ per_univ i ->
    DF a ≈ a' ∈ per_univ_elem i ↘ (per_head S S' ρ ρ').
Proof.
  intros * Ha Ha' [R HR].
  eapply per_univ_elem_resp_iff; [ exact HR |].
  eapply per_head_iff; eassumption.
Qed.

(** The head PER of a type does not depend on which environments of a related
    family it is read in: any two evaluations of [S] and [S'] whose four values
    form a chain give the same relation.  This lets a judgment proved at one
    pair of environments be used at another, as in every rule whose type is an
    instantiated codomain. *)
Lemma per_head_resp : forall {S S' ρ1 ρ2 ρ3 ρ4 i a1 a2 a3 a4},
    ⟦ S ⟧ ρ1 ↘ a1 ->
    ⟦ S' ⟧ ρ2 ↘ a2 ->
    ⟦ S ⟧ ρ3 ↘ a3 ->
    ⟦ S' ⟧ ρ4 ↘ a4 ->
    rel_chain (per_univ i) ([a1; a2; a3; a4]) ->
    per_head S S' ρ1 ρ2 <~> per_head S S' ρ3 ρ4.
Proof.
  intros * Ha1 Ha2 Ha3 Ha4 Hchain.
  assert (H12 : Dom a1 ≈ a2 ∈ per_univ i) by pairwise.
  destruct H12 as [R HR].
  (** Refining the chain to [R] identifies the two head PERs: each is [R] by
      [per_head_iff], at its own pair of type values. *)
  assert (HchainR : rel_chain (per_univ_elem i R) ([a1; a2; a3; a4]))
    by (eapply per_univ_chain_at_in; [ exact Hchain | | | exact HR ]; solve_in).
  assert (H34 : DF a3 ≈ a4 ∈ per_univ_elem i ↘ R) by pairwise.
  etransitivity; [ symmetry; eapply per_head_iff; [ exact Ha1 | exact Ha2 | exact HR ] |].
  eapply per_head_iff; [ exact Ha3 | exact Ha4 | exact H34 ].
Qed.

(** [per_head_resp] for an elimination rule, where the two pairs of
    environments differ only in their heads.  There the codomain judgment is
    available at any related pair of arguments, and each link of the chain is
    an instance of it; the middle one is at the crossing pair [(u, y)].  That
    relatedness is a premise rather than derived: [RN] is a PER at every use,
    but requiring it would oblige every caller to provide the instance. *)
Lemma per_head_of_args : forall {i B ρ ρ' RN},
    (forall x y,
        Dom x ≈ y ∈ RN ->
        exists b b',
          ⟦ B ⟧ ρ ↦ x ↘ b /\ ⟦ B ⟧ ρ' ↦ y ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
    forall x y u v,
      Dom x ≈ y ∈ RN ->
      Dom u ≈ v ∈ RN ->
      Dom u ≈ y ∈ RN ->
      per_head B B (ρ ↦ x) (ρ' ↦ y) <~> per_head B B (ρ ↦ u) (ρ' ↦ v).
Proof.
  intros * Hcod * Hxy Huv Huy.
  destruct (Hcod _ _ Hxy) as [bx [by0 [Hbx [Hby0 Hb_xy]]]].
  destruct (Hcod _ _ Huv) as [bu [bv [Hbu [Hbv Hb_uv]]]].
  destruct (Hcod _ _ Huy) as [bu0 [by1 [Hbu0 [Hby1 Hb_uy]]]].
  assert (bu0 = bu) as -> by (eapply functional_eval_exp; eassumption).
  assert (by1 = by0) as -> by (eapply functional_eval_exp; eassumption).
  eapply per_head_resp; [ exact Hbx | exact Hby0 | exact Hbu | exact Hbv |].
  apply rel_chain_4; [ exact Hb_xy | symmetry; exact Hb_uy | exact Hb_uv ].
Qed.

(** The codomain at one argument pair, as a [per_univ_elem] at the head PER of
    another pair.  This is how an element PER provided by a judgment is
    identified with the canonical one: irrelevance needs a shared type value,
    which is the codomain's value at the pair the judgment was read at, while
    the PER wanted is the one at the pair the goal names. *)
Corollary per_head_anchor : forall {i B ρ ρ' RN},
    (forall x y,
        Dom x ≈ y ∈ RN ->
        exists b b',
          ⟦ B ⟧ ρ ↦ x ↘ b /\ ⟦ B ⟧ ρ' ↦ y ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
    forall x y u v,
      Dom x ≈ y ∈ RN ->
      Dom u ≈ v ∈ RN ->
      Dom u ≈ y ∈ RN ->
      exists b b',
        ⟦ B ⟧ ρ ↦ x ↘ b /\ ⟦ B ⟧ ρ' ↦ y ↘ b' /\
          DF b ≈ b' ∈ per_univ_elem i
               ↘ (per_head B B (ρ ↦ u) (ρ' ↦ v)).
Proof.
  intros * Hcod * Hxy Huv Huy.
  destruct (Hcod _ _ Hxy) as [b [b' [Hb [Hb' [R HR]]]]].
  exists b, b'.
  do 2 (split; [ eassumption |]).
  eapply per_univ_elem_resp_iff; [ exact HR |].
  etransitivity;
    [ eapply per_head_iff; [ exact Hb | exact Hb' | exact HR ]
    | eapply per_head_of_args; eassumption ].
Qed.

(** The premise of [per_ctx_env_cons], at the canonical head relation.  Its
    own premise has the shape that [rel_exp_of_typ_inversion_simple]
    provides. *)
Lemma per_ctx_env_extend : forall {Δ Δ' S S' env_relΔ} {i : nat},
    EF Δ ≈ Δ' ∈ per_ctx_env ↘ env_relΔ ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ env_relΔ ->
        exists a a',
          ⟦ S ⟧ ρ ↘ a /\ ⟦ S' ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    EF Δ ▹ S ≈ Δ' ▹ S' ∈ per_ctx_env ↘ per_env_extend S S' env_relΔ.
Proof.
  intros * HΔ HS.
  eapply (per_ctx_env_cons' (i := i) (fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ env_relΔ) => per_head S S' ρ ρ'));
    [ eassumption | | ].
  - intros ρ ρ' Hρ.
    destruct (HS _ _ Hρ) as [a [a' [Ha [Ha' [R HR]]]]].
    econstructor; try eassumption.
    eapply per_univ_elem_resp_iff; [ eassumption |].
    eapply per_head_iff; eassumption.
  - intros ρ ρ'; split.
    + intros [? ?]; eexists; eassumption.
    + intros [? ?]; split; eassumption.
Qed.

(** The introduction rule of [per_env_extend].  Since the extended PER is a
    conjunction, this is [split], and it applies to any pair of environments,
    not only to literal extensions.  Completeness needs this generality: it
    places both [⟪q ψ⟫ ρ] and [⟦σ ,, M⟧s ρ] in an extended context PER, and
    only the latter is a literal [ρ ↦ m]. *)
Lemma per_env_extend_intro : forall {S S' R ρ ρ'},
    Dom ρ↯ ≈ ρ'↯ ∈ R ->
    Dom (ρ 0) ≈ (ρ' 0) ∈ per_head S S' ρ↯ ρ'↯ ->
    Dom ρ ≈ ρ' ∈ per_env_extend S S' R.
Proof.
  intros * ? ?; split; assumption.
Qed.

(** [per_env_extend_intro] for a literal extension [ρ ↦ m].  The premises of
    the general rule mention [(ρ ↦ m) ↯] and [(ρ ↦ m) 0]; these are convertible
    to [ρ] and [m], but the tactics that discharge head obligations match
    syntactically. *)
Corollary per_env_extend_intro' : forall {S S' R ρ ρ' m m'},
    Dom ρ ≈ ρ' ∈ R ->
    Dom m ≈ m' ∈ per_head S S' ρ ρ' ->
    Dom ρ ↦ m ≈ ρ' ↦ m' ∈ per_env_extend S S' R.
Proof.
  intros * ? ?; apply per_env_extend_intro; assumption.
Qed.

(** ** A Canonical Context PER for a Definition Entry

    [def_tie S M ρ] says that the head of [ρ] is the value of [M] in the tail
    of [ρ], up to the head PER of [S].  Two environments are related at
    [Δ ▸ S ≔ M] when they are related at [Δ ▹ S] and each satisfies the
    tie. *)
Definition def_tie (S : typ) (M : exp) (ρ : env) : Prop :=
  exists m, ⟦ M ⟧ ρ↯ ↘ m /\ Dom m ≈ (ρ 0) ∈ per_head S S ρ↯ ρ↯.

Record per_env_extend_def (S : typ) (M : exp) (R : relation env) (ρ ρ' : env) : Prop := mk_per_env_extend_def
  { ped_ext : Dom ρ ≈ ρ' ∈ per_env_extend S S R
  ; ped_tie_left : def_tie S M ρ
  ; ped_tie_right : def_tie S M ρ' }.

(** The head PER of a type is the same at any two related pairs of tails. *)
Lemma per_head_resp_simple : forall {S R i},
    PER R ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ R ->
        exists a a', ⟦ S ⟧ ρ ↘ a /\ ⟦ S ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    forall ρ1 ρ2 ρ3 ρ4,
      rel_chain R ([ρ1; ρ2; ρ3; ρ4]) ->
      per_head S S ρ1 ρ2 <~> per_head S S ρ3 ρ4.
Proof.
  intros * HPER HS * Hchain.
  assert (H12 : Dom ρ1 ≈ ρ2 ∈ R) by pairwise.
  assert (H32 : Dom ρ3 ≈ ρ2 ∈ R) by pairwise.
  assert (H34 : Dom ρ3 ≈ ρ4 ∈ R) by pairwise.
  destruct (HS _ _ H12) as [a1 [a2 [Ha1 [Ha2 Ha12]]]].
  destruct (HS _ _ H32) as [a3 [a2' [Ha3 [Ha2' Ha32]]]].
  destruct (HS _ _ H34) as [a3' [a4 [Ha3' [Ha4 Ha34]]]].
  assert (a2' = a2) as -> by (eapply functional_eval_exp; eassumption).
  assert (a3' = a3) as -> by (eapply functional_eval_exp; eassumption).
  eapply per_head_resp; [ exact Ha1 | exact Ha2 | exact Ha3 | exact Ha4 |].
  apply rel_chain_4; [ exact Ha12 | symmetry; exact Ha32 | exact Ha34 ].
Qed.

(** The premise [per_ctx_env_cons_def] asks for, at the canonical relation. *)
Lemma per_ctx_env_extend_def : forall {Δ S M env_relΔ} {i : nat},
    EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ env_relΔ ->
        exists a a', ⟦ S ⟧ ρ ↘ a /\ ⟦ S ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ env_relΔ ->
        exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head S S ρ ρ') ->
    EF Δ ▸ S ≔ M ≈ Δ ▸ S ≔ M ∈ per_ctx_env ↘ per_env_extend_def S M env_relΔ.
Proof.
  intros * HΔ HS HM.
  assert (HPER : PER env_relΔ) by (eapply per_env_PER; eassumption).
  eapply per_ctx_env_cons_def
    with (head_rel := fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ env_relΔ) => per_head S S ρ ρ');
    [ eassumption | eassumption | | |].
  - intros ρ ρ' Hρ.
    destruct (HS _ _ Hρ) as [a [a' [Ha [Ha' [R HR]]]]].
    econstructor; try eassumption.
    eapply per_univ_elem_resp_iff; [ eassumption |].
    eapply per_head_iff; eassumption.
  - intros ρ ρ' Hρ.
    destruct (HM _ _ Hρ) as [m [m' [Hm [Hm' Hmm']]]].
    econstructor; eassumption.
  - intros ρ ρ'.
    (** A tie at a single environment and a tie read across the related pair
        are the same, since the head PER does not depend on the tails. *)
    assert (Hmove : forall ρ1 ρ2,
               Dom ρ1 ≈ ρ2 ∈ env_relΔ ->
               (per_head S S ρ1 ρ1 <~> per_head S S ρ1 ρ2) /\
                 (per_head S S ρ2 ρ2 <~> per_head S S ρ1 ρ2)).
    { intros ρ1 ρ2 H12.
      assert (H11 : Dom ρ1 ≈ ρ1 ∈ env_relΔ) by solve_per.
      assert (H22 : Dom ρ2 ≈ ρ2 ∈ env_relΔ) by solve_per.
      split; eapply (per_head_resp_simple HPER HS); apply rel_chain_4; solve_per. }
    split.
    + intros [[Ht Hh] [m [Hm Htie]] [m' [Hm' Htie']]].
      destruct (Hmove _ _ Ht) as [H1 H2].
      exists Ht.
      repeat split; try eassumption.
      * eexists; split; [ eassumption | apply H1; eassumption ].
      * eexists; split; [ eassumption | apply H1; eassumption ].
      * eexists; split; [ eassumption | apply H2; eassumption ].
      * eexists; split; [ eassumption | apply H2; eassumption ].
    + intros [Ht [Hh [[m [Hm Htie]] [_ [[m' [Hm' Htie']] _]]]]].
      destruct (Hmove _ _ Ht) as [H1 H2].
      repeat split; try eassumption.
      * eexists; split; [ eassumption | apply H1; eassumption ].
      * eexists; split; [ eassumption | apply H2; eassumption ].
Qed.

(** The tie propagates along the relation of an assumption entry, and from a
    body to a related one.  So it is enough to establish it at one environment
    of a chain. *)
Lemma def_tie_resp : forall {S M M' R i ρ ρ'},
    PER R ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ R ->
        exists a a', ⟦ S ⟧ ρ ↘ a /\ ⟦ S ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ R ->
        exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M' ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head S S ρ ρ') ->
    Dom ρ ≈ ρ' ∈ per_env_extend S S R ->
    def_tie S M ρ ->
    def_tie S M' ρ'.
Proof.
  intros * HPER HS HM [Ht Hh] [m [Hm Htie]].
  assert (H11 : Dom ρ↯ ≈ ρ↯ ∈ R) by solve_per.
  assert (H22 : Dom ρ'↯ ≈ ρ'↯ ∈ R) by solve_per.
  destruct (HM _ _ Ht) as [m1 [m2 [Hm1 [Hm2 Hm12]]]].
  assert (m1 = m) as -> by (eapply functional_eval_exp; eassumption).
  exists m2; split; [ eassumption |].
  assert (E1 : per_head S S ρ↯ ρ↯ <~> per_head S S ρ↯ ρ'↯)
    by (eapply (per_head_resp_simple HPER HS); apply rel_chain_4; solve_per).
  assert (E2 : per_head S S ρ'↯ ρ'↯ <~> per_head S S ρ↯ ρ'↯)
    by (eapply (per_head_resp_simple HPER HS); apply rel_chain_4; solve_per).
  apply E2; apply E1 in Htie.
  destruct (HS _ _ Ht) as [a [a' [Ha [Ha' [R' HR']]]]].
  pose proof (per_head_iff Ha Ha' HR') as E3.
  assert (PER R') by (eapply per_elem_PER; eassumption).
  apply E3; apply E3 in Htie, Hh, Hm12.
  solve_per.
Qed.

(** Transporting a [per_head] to another pair of environments, the bridging
    step of the completeness proofs.  The two head relations are equal because
    their types are related in [per_univ]: the first two evaluations and the
    PER describe the source types, the next two evaluations the target types,
    and the last premise relates the two left types.  That suffices because
    [per_univ_elem] is irrelevant on either side. *)
Lemma per_head_bridge : forall {S S' ρ ρ' T T' u u' i R a a' b b' m m'},
    Dom m ≈ m' ∈ per_head S S' ρ ρ' ->
    ⟦ S ⟧ ρ ↘ a ->
    ⟦ S' ⟧ ρ' ↘ a' ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    ⟦ T ⟧ u ↘ b ->
    ⟦ T' ⟧ u' ↘ b' ->
    Dom a ≈ b ∈ per_univ i ->
    Dom m ≈ m' ∈ per_head T T' u u'.
Proof.
  intros * Hm Ha Ha' HR Hb Hb' [? Hab].
  assert (Hmm : Dom m ≈ m' ∈ R) by (eapply Hm; eassumption).
  hnf; intros * Hb0 Hb0' HR0.
  functional_eval_rewrite_clear.
  handle_per_univ_elem_irrel.
  eassumption.
Qed.

(** ** A Canonical Function PER

    The same construction one level down.  [per_univ_elem_core_pi] leaves the
    codomain family [out_rel] existentially quantified and indexed by the
    evidence relating the two arguments, so a Π-value's element PER is
    determined only up to that choice.  The four-value pattern of a Π-type
    compares Π-values whose codomain expressions and environments all differ
    ([B[q σ]] at [ρ], [B] at [⟦σ⟧ρ], …), yet all its links must be at one
    element PER.

    [per_pi] names the family canonically, with [per_head] as the codomain
    relation: the PER the codomain denotes at [ρ ↦ c] and [ρ' ↦ c'] is a head
    PER.  It is independent of the evidence and of the level, so one [per_pi]
    serves every link. *)

Definition per_pi (in_rel : relation domain) (B : typ) (ρ : env) (B' : typ) (ρ' : env) : relation domain :=
  fun f f' =>
    forall c c' (equiv_c_c' : Dom c ≈ c' ∈ in_rel),
      rel_mod_app f c f' c' (per_head B B' (ρ ↦ c) (ρ' ↦ c')).

(** Building a Π-value at [per_pi].  The codomain premise has the element PER
    existentially quantified, which is the shape a four-value chain provides
    after [destruct_per_univ_chain]; [per_head_iff] turns any such PER into the
    canonical one. *)
Lemma per_univ_elem_pi_canonical : forall {i a a' in_rel ρ B ρ' B'},
    DF a ≈ a' ∈ per_univ_elem i ↘ in_rel ->
    (forall c c',
        Dom c ≈ c' ∈ in_rel ->
        exists b b' R,
          ⟦ B ⟧ ρ ↦ c ↘ b /\
          ⟦ B' ⟧ ρ' ↦ c' ↘ b' /\
          DF b ≈ b' ∈ per_univ_elem i ↘ R) ->
    DF Πᵈ a ρ B ≈ Πᵈ a' ρ' B' ∈ per_univ_elem i ↘ (per_pi in_rel B ρ B' ρ').
Proof.
  intros * Ha HB.
  eapply (per_univ_elem_pi' _ _ _ _ _ _ _ in_rel
            (fun c c' (_ : Dom c ≈ c' ∈ in_rel) =>
               per_head B B' (ρ ↦ c) (ρ' ↦ c')));
    [ eassumption | | reflexivity ].
  intros c c' equiv_c_c'.
  destruct (HB _ _ equiv_c_c') as [b [b' [R [Hb [Hb' HR]]]]].
  econstructor; try eassumption.
  eapply per_univ_elem_resp_iff; [ eassumption |].
  eapply per_head_iff; eassumption.
Qed.

(** Whatever PER a Π-value carries, it is [per_pi]; this justifies
    application.  The two levels are unrelated, since [per_univ_elem]
    irrelevance is cross-level, so a Π-type from one judgment and a domain from
    another need no lifting. *)
Corollary per_pi_iff : forall {i j a a' in_rel ρ B ρ' B' R},
    DF a ≈ a' ∈ per_univ_elem i ↘ in_rel ->
    DF Πᵈ a ρ B ≈ Πᵈ a' ρ' B' ∈ per_univ_elem j ↘ R ->
    R <~> per_pi in_rel B ρ B' ρ'.
Proof.
  intros * Ha HΠ.
  invert_per_univ_elem HΠ.
  rename x into out_rel; rename H into Hout; rename H0 into HR.
  (** [HR] identifies [R] with the family-indexed relation; it remains to show
      the family is pointwise the canonical head PER.  Transitivity of
      [relation_equivalence] must be used before introducing the two values:
      afterwards the goal is a [pointwise_lifting], where neither [rewrite] nor
      [etransitivity] applies. *)
  etransitivity; [ exact HR |].
  intros f f'; split; intros Hf c c' equiv_c_c';
    specialize (Hf _ _ equiv_c_c');
    destruct (Hout _ _ equiv_c_c') as [b b' Hb Hb' Hbb'].
  - rewrite <- (per_head_iff Hb Hb' Hbb'); exact Hf.
  - rewrite (per_head_iff Hb Hb' Hbb'); exact Hf.
Qed.

(** The four-value pattern of a Π-type at one element PER, as required by
    every semantic judgment whose type is a Π.  Each link is built by
    [per_univ_elem_pi_canonical] at its own codomain pair and so carries its
    own [per_pi]; the three agree by irrelevance, since consecutive links share
    a Π-value.  The chain is stated at the inner link's PER: the only link
    whose sides are both unsubstituted, and the one an application reads its
    output PER from.

    The domain is a four-value pattern already at [in_rel], which by weak
    functionality is what a semantic type judgment provides
    ([functionalize_per_univ_chain]).  The three codomain premises are, in
    order, the three obligations produced by [rel_exp_of_typ_under_ctx_q]. *)
Lemma per_univ_elem_pi_chain : forall {i in_rel a1 a2 a3 a4 B1 ρ1 B2 ρ2 B3 ρ3 B4 ρ4},
    rel_chain (per_univ_elem i in_rel) ([a1; a2; a3; a4]) ->
    (forall c c',
        Dom c ≈ c' ∈ in_rel ->
        exists b b', ⟦ B1 ⟧ ρ1 ↦ c ↘ b /\ ⟦ B2 ⟧ ρ2 ↦ c' ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
    (forall c c',
        Dom c ≈ c' ∈ in_rel ->
        exists b b', ⟦ B2 ⟧ ρ2 ↦ c ↘ b /\ ⟦ B3 ⟧ ρ3 ↦ c' ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
    (forall c c',
        Dom c ≈ c' ∈ in_rel ->
        exists b b', ⟦ B3 ⟧ ρ3 ↦ c ↘ b /\ ⟦ B4 ⟧ ρ4 ↦ c' ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
    rel_chain (per_univ_elem i (per_pi in_rel B2 ρ2 B3 ρ3))
      ([Πᵈ a1 ρ1 B1; Πᵈ a2 ρ2 B2; Πᵈ a3 ρ3 B3; Πᵈ a4 ρ4 B4]).
Proof.
  intros * Hchain HB12 HB23 HB34.
  assert (H12 : DF a1 ≈ a2 ∈ per_univ_elem i ↘ in_rel) by pairwise.
  assert (H23 : DF a2 ≈ a3 ∈ per_univ_elem i ↘ in_rel) by pairwise.
  assert (H34 : DF a3 ≈ a4 ∈ per_univ_elem i ↘ in_rel) by pairwise.
  (** One [per_univ_elem_pi_canonical] per link, adapting the premise's
      [per_univ] to the [exists R] the lemma wants. *)
  assert (Hlink : forall B ρ B' ρ' a a',
             DF a ≈ a' ∈ per_univ_elem i ↘ in_rel ->
             (forall c c',
                 Dom c ≈ c' ∈ in_rel ->
                 exists b b', ⟦ B ⟧ ρ ↦ c ↘ b /\ ⟦ B' ⟧ ρ' ↦ c' ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
             DF Πᵈ a ρ B ≈ Πᵈ a' ρ' B' ∈ per_univ_elem i ↘ (per_pi in_rel B ρ B' ρ')).
  { intros * Ha HB.
    apply per_univ_elem_pi_canonical; [ eassumption |].
    intros c c' Hc.
    destruct (HB _ _ Hc) as [b [b' [Hb [Hb' [R HR]]]]].
    exists b, b', R; repeat split; eassumption. }
  pose proof (Hlink _ _ _ _ _ _ H12 HB12) as HL1.
  pose proof (Hlink _ _ _ _ _ _ H23 HB23) as HL2.
  pose proof (Hlink _ _ _ _ _ _ H34 HB34) as HL3.
  (** The three links are a chain in [per_univ i], so weak functionality puts
      them at one PER, and uniqueness, with [HL2] as anchor, makes it the inner
      link's.  [handle_per_univ_elem_irrel] would keep an unpredictable one of
      the three [per_pi]s. *)
  assert (Hpi : rel_chain (per_univ i)
                  ([Πᵈ a1 ρ1 B1; Πᵈ a2 ρ2 B2;
                   Πᵈ a3 ρ3 B3; Πᵈ a4 ρ4 B4]))
    by (apply rel_chain_4; eexists; eassumption).
  functionalize_per_univ_chain Hpi R.
  retype_rel_chain Hpi HL2 Hpi.
  exact Hpi.
Qed.

(** ** Closing an Extended Context PER Goal

    Every completeness proof in an extended context ends the same way, with
    these three tactics.

    - [destruct_per_univ_chain] turns a four-value chain in [per_univ i] into
      the three [per_univ_elem] hypotheses that [handle_per_univ_elem_irrel]
      works on.  It goes through [per_univ_chain_functional], so the three are
      at one element PER rather than three independent ones.
    - [solve_per_head] discharges a [per_head] goal.  [per_head] quantifies
      over an arbitrary [per_univ_elem] relating the two type values, so the
      proof is always the same: introduce it, identify its two values with
      known ones, let irrelevance identify its PER with that of the term
      chain, and read the pair off that chain.
    - [solve_per_env_extend_chain] relates a chain of extended environments in
      an extended context PER.  [per_env_extend_intro'] splits each link into
      a tail and a head; the tails come from the chain of the underlying
      substitution, and the heads are bridged.  The chain may have any length:
      substitution cases need four environments, while rules with a premise in
      an extended context need every extension of the four tails by either of
      the two heads. *)
End Fixed_GCtx.

Ltac destruct_per_univ_chain H :=
  apply per_univ_chain_functional in H;
  destruct H as [? H];
  destruct H as [? [? ?]].

Ltac solve_per_head :=
  hnf; intros ? ? ? ? ? ? ?;
  functional_eval_rewrite_clear;
  handle_per_univ_elem_irrel;
  pairwise.

Section Fixed_GCtx.
  Context {GC : GCtx}.


End Fixed_GCtx.

(** The links are peeled by matching the goal's shape rather than with
    [first]: [rel_chain R [x; y]] is convertible to [R x y], so an unguarded
    [apply rel_chain_of_pair] would also fire on a link goal, and an unguarded
    [apply rel_chain_cons] would peel past the last link. *)
Ltac solve_per_env_extend_chain :=
  repeat
    match goal with
    | |- rel_chain _ ([_; _]) => apply rel_chain_of_pair
    | |- rel_chain _ (_ :: _ :: _) => apply rel_chain_cons
    end;
  apply per_env_extend_intro'; first [ pairwise | solve_per_head ].

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_ctx_respects_length : forall {Γ Γ'},
    Exp Γ ≈ Γ' ∈ per_ctx ->
    length Γ = length Γ'.
Proof.
  intros * [? H].
  induction H; simpl; congruence.
Qed.

Lemma per_ctx_subtyp_to_env : forall Γ Δ,
    SubE Γ <: Δ ->
    exists R R',
      EF Γ ≈ Γ ∈ per_ctx_env ↘ R /\
        EF Δ ≈ Δ ∈ per_ctx_env ↘ R'.
Proof.
  destruct 1; destruct_all.
  1: repeat eexists; econstructor; apply Equivalence_Reflexive.
  all: eauto.
Qed.

(** An inclusion of context PERs holds for any other names of them. *)
Lemma per_ctx_env_incl_irrel : forall Γ Δ R R1 R' R2 ρ ρ',
    (forall ρ ρ', R1 ρ ρ' -> R2 ρ ρ') ->
    R ρ ρ' ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R1 ->
    EF Δ ≈ Δ ∈ per_ctx_env ↘ R' ->
    EF Δ ≈ Δ ∈ per_ctx_env ↘ R2 ->
    R' ρ ρ'.
Proof.
  intros * Hinc Hρ HR HR1 HR' HR2.
  apply (per_ctx_env_right_irrel _ _ _ _ _ HR' HR2), Hinc, (per_ctx_env_right_irrel _ _ _ _ _ HR HR1), Hρ.
Qed.

Lemma per_ctx_env_subtyping : forall Γ Δ,
    SubE Γ <: Δ ->
    forall R R' ρ ρ',
      EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
      EF Δ ≈ Δ ∈ per_ctx_env ↘ R' ->
      R ρ ρ' ->
      R' ρ ρ'.
Proof.
  induction 1; intros;
    try solve [ eapply per_ctx_env_incl_irrel; eassumption ];
    handle_per_ctx_env_irrel;
    (on_all_hyp: fun H => directed invert_per_ctx_env H);
    apply_relation_equivalence;
    trivial.

  destruct_all.
  assert (Dom ρ↯ ≈ ρ'↯ ∈ tail_rel0) by intuition.
  unshelve eexists; [eassumption |].
  destruct_rel_typ.
  eapply per_elem_subtyping with (i := max x (max i0 i)); try eassumption.
  - eauto using per_subtyp_cumu_right.
  - saturate_refl.
    eauto using per_univ_elem_cumu_max_left.
  - saturate_refl.
    eauto using per_univ_elem_cumu_max_left, per_univ_elem_cumu_max_right.
Qed.

Lemma per_ctx_subtyp_trans : forall Γ1 Γ2,
    SubE Γ1 <: Γ2 ->
    forall Γ3,
      SubE Γ2 <: Γ3 ->
      SubE Γ1 <: Γ3.
Proof.
  induction 1; intros;
    (on_all_hyp: fun H => directed invert_per_ctx_env H);
    mauto 1;
    clear_PER.

  1: handle_per_ctx_env_irrel.
  1: econstructor; try eassumption.
  - firstorder.
  - instantiate (1 := max i i0).
    intros.
    assert (Dom ρ ≈ ρ' ∈ tail_rel0) by (eapply per_ctx_env_subtyping; revgoals; eassumption).
    saturate_refl_for tail_rel.
    destruct_rel_typ.
    handle_per_univ_elem_irrel.
    etransitivity.
    + intuition mauto using per_subtyp_cumu_left.
    + intuition mauto using per_subtyp_cumu_right.
  - econstructor; intuition.
    + typeclasses eauto.
    + solve_refl.
  - (** A definition: the inclusions of environments compose. *)
    match goal with HS : SubE (e :: Γ') <: ?Γ3 |- _ =>
      destruct (per_ctx_subtyp_to_env _ _ HS) as [R2 [R3 [HR2 HR3]]];
      destruct Γ3 as [| e3 Γ3']; [ inversion HS |];
      assert (SubE Γ' <: Γ3') by (inversion HS; assumption);
      eapply per_ctx_subtyp_def with (env_rel' := R3); [ eauto | eassumption | eassumption |];
      intros ρ ρ' Hρ;
      eapply per_ctx_env_subtyping; [ exact HS | eassumption | eassumption | ];
      handle_per_ctx_env_irrel; eauto
    end.
  - (** A slot: the inclusions compose. *)
    match goal with HS : SubE (?Γ'' ▹ₘ ?U'') <: ?Γ3 |- _ =>
      destruct (per_ctx_subtyp_to_env _ _ HS) as [R2 [R3 [HR2 HR3]]];
      inversion HS; subst;
      eapply per_ctx_subtyp_mod with (env_rel' := R3); [ eauto | eassumption | eassumption |];
      intros ρ ρ' Hρ;
      eapply per_ctx_env_subtyping; [ exact HS | eassumption | eassumption | ];
      handle_per_ctx_env_irrel; eauto
    end.
Qed.

Hint Resolve per_ctx_subtyp_trans : mctt.

#[local] Instance per_ctx_subtyp_trans_ins : Transitive per_ctx_subtyp.
Proof.
  eauto using per_ctx_subtyp_trans.
Qed.

(** * Context PERs Respect Pointwise Equality of Environments

    Evaluating a substitution determines its result only up to [env_eq]
    ([functional_eval_sub]), so every use of a context PER in the completeness
    proof needs this lemma.  It does not follow from evaluation respecting
    [env_eq], which is false because a closure captures its environment.  It
    holds because a context PER inspects an environment only pointwise, and
    its head relations at pointwise-equal environments coincide up to [<~>] by
    irrelevance. *)
Lemma per_ctx_env_resp_env_eq : forall {Γ Δ R},
    EF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    forall ρ1 ρ2 ρ1' ρ2',
      env_eq ρ1 ρ2 ->
      env_eq ρ1' ρ2' ->
      Dom ρ1 ≈ ρ1' ∈ R ->
      Dom ρ2 ≈ ρ2' ∈ R.
Proof.
  intros * H.
  induction H; intros * Heq Heq' HR; apply_relation_equivalence; [ trivial | | | ].
  3: { (** A slot: the heads are the same, and the closures over the new
         tails are related to those over the old ones. *)
    destruct HR as (Dtail1 & T1 & T2 & T3 & T4).
    assert (Hd : env_eq ρ1↯ ρ2↯) by (now rewrite Heq).
    assert (Hd' : env_eq ρ1'↯ ρ2'↯) by (now rewrite Heq').
    assert (Dtail2 : Dom ρ2↯ ≈ ρ2'↯ ∈ tail_rel) by (eapply IHper_ctx_env; eassumption).
    assert (D11 : Dom ρ1↯ ≈ ρ1↯ ∈ tail_rel) by solve_per.
    assert (D11' : Dom ρ1'↯ ≈ ρ1'↯ ∈ tail_rel) by solve_per.
    assert (D12 : Dom ρ1↯ ≈ ρ2↯ ∈ tail_rel) by (eapply IHper_ctx_env; [ reflexivity | eassumption | exact D11 ]).
    assert (D12' : Dom ρ1'↯ ≈ ρ2'↯ ∈ tail_rel) by (eapply IHper_ctx_env; [ reflexivity | eassumption | exact D11' ]).
    destruct (rel_mexp_move _ _ _ _ _ _ D12 H0) as (M1 & M2 & M3 & M4).
    destruct (rel_mexp_move _ _ _ _ _ _ D12' H0) as (M1' & M2' & M3' & M4').
    rewrite <- (env_eq_mod _ _ Heq 0), <- (env_eq_mod _ _ Heq' 0).
    repeat split; [ exact Dtail2 | .. ]; solve_tie. }
  all: destruct HR as [Dtail1 Hhead1];
    assert (Hd : env_eq ρ1↯ ρ2↯) by (now rewrite Heq);
    assert (Hd' : env_eq ρ1'↯ ρ2'↯) by (now rewrite Heq');
    assert (Dmix : Dom ρ1↯ ≈ ρ2'↯ ∈ tail_rel) by (eapply IHper_ctx_env; [ reflexivity | eassumption | eassumption ]);
    assert (Dtail2 : Dom ρ2↯ ≈ ρ2'↯ ∈ tail_rel) by (eapply IHper_ctx_env; eassumption);
    unshelve eexists; try exact Dtail2;
    rewrite <- (env_eq_var _ _ Heq 0), <- (env_eq_var _ _ Heq' 0).
  - pose proof (H0 _ _ Dtail1).
    pose proof (H0 _ _ Dmix).
    pose proof (H0 _ _ Dtail2).
    destruct_rel_typ.
    handle_per_univ_elem_irrel.
    first [ eassumption | use_relation_equivalence; eassumption ].
  - (** A definition: the bodies at the new tails are related to the old
        heads through the other side's body. *)
    destruct_conjs.
    assert (Dom ρ2↯ ≈ ρ2↯ ∈ tail_rel) by solve_per.
    assert (Dom ρ2'↯ ≈ ρ2'↯ ∈ tail_rel) by solve_per.
    assert (Dom ρ1'↯ ≈ ρ2'↯ ∈ tail_rel) by solve_per.
    solve_def_heads.
Qed.

#[local] Instance per_ctx_env_Proper {Γ Δ R} (H : EF Γ ≈ Δ ∈ per_ctx_env ↘ R) :
  Proper (env_eq ==> env_eq ==> iff) R.
Proof.
  intros ρ1 ρ2 Heq ρ1' ρ2' Heq'.
  split; intros; eapply per_ctx_env_resp_env_eq;
    try eassumption; symmetry; eassumption.
Qed.

(** Cumulativity on [per_univ], along the order of indices. *)
Corollary per_univ_cumu_uidx : forall {u v a a'},
    uidx_le u v ->
    Dom a ≈ a' ∈ per_univ u ->
    Dom a ≈ a' ∈ per_univ v.
Proof. intros * ? [R ?]; eexists; eapply per_univ_elem_cumu_uidx; eassumption. Qed.

(** The universe at an index is in every universe above it, at either tier,
    with its own elements as the relation. *)
Lemma per_univ_elem_ulvl_val : forall u i,
    uidx_lt u i ->
    DF ulvl_val u ≈ ulvl_val u ∈ per_univ_elem i ↘ per_univ u.
Proof.
  intros [n | n] * Hlt; cbn.
  - (** The small universe at [n] is the one at the literal level [n], whose
        realiser is [n]. *)
    assert (Hr : dlvl_real (d_lvl n nil) = n) by apply dlvl_real_lit.
    apply per_univ_elem_core_suniv'; rewrite ?Hr;
      [ apply per_lvl_lit | assumption | reflexivity ].
  - apply per_univ_elem_core_univ'; solve [ assumption | reflexivity ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve per_ctx_subtyp_trans : mctt.
#[export] Existing Instance per_ctx_subtyp_trans_ins.
#[export] Existing Instance per_ctx_env_Proper.

#[export]
Hint Resolve per_univ_elem_ulvl_val : mctt.
