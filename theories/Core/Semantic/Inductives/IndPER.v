(** * Inductive Types in the PER Model, Canonically

    The clause of [per_univ_elem_core] for inductive types takes the
    relations of its telescopes as arguments.  Here they are fixed: the
    relation at a position is the head PER of the type there, read in the
    environment of the left values ([per_head], on the diagonal), which the
    PER model determines.  [per_univ_elem_indty_canon] builds the clause from
    the relatedness of the types alone. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export PER Realizability.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

  (** The type at a position of a telescope, and of a constructor's
      non-recursive arguments. *)
  Definition nth_ctyp (T : list centry) (k : nat) : typ :=
    match List.nth_error T k with Some (ce_ass A) => A | _ => a_True end.

  Definition nth_atyp (D : ind_decl) (c : String.string) (k : nat) : typ :=
    match ind_con D c with Some gs => List.nth k (cargs_nonrec gs) a_True | None => a_True end.

  Definition canon_nparams_rel (D : ind_decl) (ups : list domain) : nat -> list domain -> relation domain :=
    fun k vs => per_head (nth_ctyp (List.rev (ind_nparams D)) k) (nth_ctyp (List.rev (ind_nparams D)) k)
                  (env_args nil (ups ++ vs)) (env_args nil (ups ++ vs)).

  Definition canon_args_rel (D : ind_decl) (ups : list domain) : list domain -> String.string -> nat -> list domain -> relation domain :=
    fun ms c k vs => per_head (nth_atyp D c k) (nth_atyp D c k)
                       (env_args nil (ups ++ ms ++ vs)) (env_args nil (ups ++ ms ++ vs)).

  (** The relation of a domain of a shape, after the values [pre] of its
      components: the head PER of the domain there. *)
  Definition canon_doms_rel (ups : list domain) : list domain -> exp -> relation domain :=
    fun pre B => per_head B B (env_args nil (ups ++ pre)) (env_args nil (ups ++ pre)).

  Lemma nth_ctyp_eq : forall T k A, List.nth_error T k = Some (ce_ass A) -> nth_ctyp T k = A.
  Proof. intros * H; unfold nth_ctyp; rewrite H; reflexivity. Qed.

  Lemma nth_atyp_eq : forall D c gs k A, ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
      nth_atyp D c k = A.
  Proof. intros * Hc H; unfold nth_atyp; rewrite Hc; apply List.nth_error_nth; exact H. Qed.

  (** The head PER on the diagonal is the relation of a type related to any
      other. *)
  Lemma per_head_diag : forall {S ρ i a a' R},
      ⟦ S ⟧ ρ ↘ a -> DF a ≈ a' ∈ per_univ_elem i ↘ R ->
      DF a ≈ a' ∈ per_univ_elem i ↘ (per_head S S ρ ρ).
  Proof.
    intros * Ha HR.
    assert (HRaa : DF a ≈ a ∈ per_univ_elem i ↘ R) by (eapply per_univ_trans; [ exact HR | apply per_univ_sym; exact HR ]).
    eapply per_univ_elem_resp_iff; [ exact HR |].
    eapply per_head_iff; eassumption.
  Qed.

  Section Canon.
    Variable (u : uidx) (p : qname) (D : ind_decl) (ups ups' : list domain).
    Let T := List.rev (ind_nparams D).
    Let nr := canon_nparams_rel D ups.
    Let ar := canon_args_rel D ups.
    Let dr := canon_doms_rel ups.
    Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (Hass : tele_ass (ind_params D)).
    Hypothesis (Hu : List.length ups = ind_nu D) (Hu' : List.length ups' = ind_nu D).
    Hypothesis (Hps : per_top_ps (List.rev (ind_uparams D)) ups ups').
    Hypothesis (Hn : forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_prefix_rel nr k vs vs' ->
                   exists a a', ⟦ A ⟧ env_args nil (ups ++ vs) ↘ a /\ ⟦ A ⟧ env_args nil (ups' ++ vs') ↘ a' /\
                     Dom a ≈ a' ∈ per_univ u).
    Hypothesis (Ha : forall ms ms' c gs k A vs vs', tele_rel nr T ms ms' -> ind_con D c = Some gs ->
                   List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (ar ms c) k vs vs' ->
                   exists a a', ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ a /\ ⟦ A ⟧ env_args nil (ups' ++ ms' ++ vs') ↘ a' /\
                     Dom a ≈ a' ∈ per_univ u).
    Hypothesis (Hnd : forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_prefix_rel nr k vs vs' ->
                   exists a a', ⟦ A ⟧ env_args nil (ups ++ vs) ↘ a /\ ⟦ A ⟧ env_args nil (ups ++ vs') ↘ a' /\
                     Dom a ≈ a' ∈ per_univ u).
    Hypothesis (Had : forall ms ms' c gs k A vs vs', tele_rel nr T ms ms' -> ind_con D c = Some gs ->
                   List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (ar ms c) k vs vs' ->
                   exists a a', ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ a /\ ⟦ A ⟧ env_args nil (ups ++ ms' ++ vs') ↘ a' /\
                     Dom a ≈ a' ∈ per_univ u).
    Hypothesis (Hdm : forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_rel nr T ms ms' ->
                   ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                   tele_prefix_rel (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
                   List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel dr ms ws (ptyp_doms t)) k ys ys' ->
                   exists a a', ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ a /\
                     ⟦ B ⟧ env_args nil (ups' ++ ms' ++ ws' ++ ys') ↘ a' /\ Dom a ≈ a' ∈ per_univ u).
    Hypothesis (Hdmd : forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_rel nr T ms ms' ->
                   ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                   tele_prefix_rel (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
                   List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel dr ms ws (ptyp_doms t)) k ys ys' ->
                   exists a a', ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ a /\
                     ⟦ B ⟧ env_args nil (ups ++ ms' ++ ws' ++ ys') ↘ a' /\ Dom a ≈ a' ∈ per_univ u).
    Hypothesis (Hcl : forall ms ms' c gs gs1 t gs2 ws ws' ys ys', tele_rel nr T ms ms' ->
                   ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                   tele_prefix_rel (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
                   tele_rel (shape_doms_rel dr ms ws (ptyp_doms t)) (ptyp_doms t) ys ys' ->
                   rel_evals (ptyp_ps t) (env_args nil (ups ++ ms ++ ws ++ ys)) (env_args nil (ups' ++ ms' ++ ws' ++ ys'))
                     (tele_rel nr T)).
    Hypothesis (Hcd : forall ms ms' c gs gs1 t gs2 ws ws' ys ys', tele_rel nr T ms ms' ->
                   ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                   tele_prefix_rel (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
                   tele_rel (shape_doms_rel dr ms ws (ptyp_doms t)) (ptyp_doms t) ys ys' ->
                   rel_evals (ptyp_ps t) (env_args nil (ups ++ ms ++ ws ++ ys)) (env_args nil (ups ++ ms' ++ ws' ++ ys'))
                     (tele_rel nr T)).

    (** The evidence at a position, at the head PER. *)
    Lemma canon_nparams_evals : forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_prefix_rel nr k vs vs' ->
        rel_mod_eval (per_univ_elem u) A (env_args nil (ups ++ vs)) A (env_args nil (ups' ++ vs')) (nr k vs).
    Proof.
      intros * Hk Hp; destruct (Hn _ _ _ _ Hk Hp) as (a & a' & Ea & Ea' & [R HR]).
      econstructor; [ exact Ea | exact Ea' |].
      unfold T in Hk; unfold nr, canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ Hk); exact (per_head_diag Ea HR).
    Qed.

    Lemma canon_nparams_per : forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_prefix_rel nr k vs vs' -> PER (nr k vs).
    Proof.
      intros * Hk Hp; destruct (canon_nparams_evals _ _ _ _ Hk Hp) as [a a' _ _ HR].
      eapply per_elem_PER; exact HR.
    Qed.

    (** Invariance, by induction on the position: the prefixes on the right
        are related to themselves, by the positions before. *)
    Lemma canon_nparams_invariant_all : forall k, k <= List.length T ->
        (forall j vs vs', j < k -> tele_prefix_rel nr j vs vs' -> (nr j vs <~> nr j vs')).
    Proof.
      induction k as [| k IH]; intros Hk j vs vs' Hj Hp; [ lia |].
      destruct (Nat.lt_ge_cases j k) as [Hjk | Hjk]; [ apply IH; [ lia | exact Hjk | exact Hp ] |].
      assert (j = k) as -> by lia.
      destruct (nparams_lt_ass D k Hass ltac:(unfold T in Hk; lia)) as [A HA].
      assert (HP : forall j vs vs', j < k -> tele_prefix_rel nr j vs vs' -> PER (nr j vs)).
      { intros j0 ? ? Hj0 Hp0; destruct (nparams_lt_ass D j0 Hass ltac:(unfold T in Hk; lia)) as [A0 HA0].
        eapply canon_nparams_per; eassumption. }
      pose proof (tele_prefix_rel_refl_r k nr HP (IH ltac:(lia)) k vs vs' (le_n _) Hp) as Hp'.
      destruct (canon_nparams_evals _ _ _ _ HA Hp) as [a a' Ea Ea' HR1].
      destruct (canon_nparams_evals _ _ _ _ HA Hp') as [b b' Eb Eb' HR2].
      functional_eval_rewrite_clear.
      eapply per_univ_elem_left_irrel; [ exact HR1 | exact HR2 ].
    Qed.

    Lemma canon_nparams_invariant : forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_prefix_rel nr k vs vs' -> (nr k vs <~> nr k vs').
    Proof.
      intros * Hk Hp; assert (Hkl : k < List.length T) by (apply List.nth_error_Some; congruence).
      exact (canon_nparams_invariant_all (List.length T) (le_n _) k vs vs' Hkl Hp).
    Qed.

    Lemma canon_nparams_per' : forall k vs vs', k < List.length T -> tele_prefix_rel nr k vs vs' -> PER (nr k vs).
    Proof. intros * Hk Hp; destruct (nparams_lt_ass D k Hass Hk) as [A HA]; eapply canon_nparams_per; eassumption. Qed.

    Lemma canon_nparams_invariant' : forall k vs vs', k < List.length T -> tele_prefix_rel nr k vs vs' -> (nr k vs <~> nr k vs').
    Proof. intros * Hk Hp; destruct (nparams_lt_ass D k Hass Hk) as [A HA]; eapply canon_nparams_invariant; eassumption. Qed.

    Lemma canon_nparams_rel_refl_r : forall a b, tele_rel nr T a b -> tele_rel nr T b b.
    Proof. intros; eapply (tele_rel_refl_r (List.length T) nr canon_nparams_per' canon_nparams_invariant'); [ lia | eassumption ]. Qed.

    Lemma canon_args_evals : forall ms ms' c gs k A vs vs', tele_rel nr T ms ms' -> ind_con D c = Some gs ->
        List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (ar ms c) k vs vs' ->
        rel_mod_eval (per_univ_elem u) A (env_args nil (ups ++ ms ++ vs)) A (env_args nil (ups' ++ ms' ++ vs')) (ar ms c k vs).
    Proof.
      intros * Hm Hc Hk Hp; destruct (Ha _ _ _ _ _ _ _ _ Hm Hc Hk Hp) as (a & a' & Ea & Ea' & [R HR]).
      econstructor; [ exact Ea | exact Ea' |].
      unfold ar, canon_args_rel; rewrite (nth_atyp_eq _ _ _ _ _ Hc Hk); exact (per_head_diag Ea HR).
    Qed.

    Lemma canon_args_per : forall ms ms' c gs k A vs vs', tele_rel nr T ms ms' -> ind_con D c = Some gs ->
        List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (ar ms c) k vs vs' -> PER (ar ms c k vs).
    Proof.
      intros * Hm Hc Hk Hp; destruct (canon_args_evals _ _ _ _ _ _ _ _ Hm Hc Hk Hp) as [a a' _ _ HR].
      eapply per_elem_PER; exact HR.
    Qed.

    Lemma canon_args_invariant_all : forall ms ms' c gs, tele_rel nr T ms ms' -> ind_con D c = Some gs ->
        forall k, k <= List.length (cargs_nonrec gs) ->
        forall j vs vs', j < k -> tele_prefix_rel (ar ms c) j vs vs' -> (ar ms c j vs <~> ar ms' c j vs').
    Proof.
      intros ms ms' c gs Hm Hc.
      pose proof (canon_nparams_rel_refl_r _ _ Hm) as Hm'.
      induction k as [| k IH]; intros Hk j vs vs' Hj Hp; [ lia |].
      destruct (Nat.lt_ge_cases j k) as [Hjk | Hjk]; [ apply IH; [ lia | exact Hjk | exact Hp ] |].
      assert (j = k) as -> by lia.
      destruct (nth_error_lt_some' (cargs_nonrec gs) k ltac:(lia)) as [A HA].
      assert (Hp' : tele_prefix_rel (ar ms' c) k vs' vs').
      { eapply (tele_prefix_rel_cross_refl (ar ms c) (ar ms' c) k k); [ lia | | | exact Hp ].
        - intros j0 pa pb Hj0 Hp1 _; exact (IH ltac:(lia) j0 pa pb Hj0 Hp1).
        - intros j0 ? ? Hj0 Hp0; destruct (nth_error_lt_some' (cargs_nonrec gs) j0 ltac:(lia)) as [A0 HA0].
          eapply canon_args_per; [ exact Hm' | exact Hc | exact HA0 | exact Hp0 ]. }
      destruct (canon_args_evals _ _ _ _ _ _ _ _ Hm Hc HA Hp) as [a a' Ea Ea' HR1].
      destruct (canon_args_evals _ _ _ _ _ _ _ _ Hm' Hc HA Hp') as [b b' Eb Eb' HR2].
      functional_eval_rewrite_clear.
      eapply per_univ_elem_left_irrel; [ exact HR1 | exact HR2 ].
    Qed.

    Lemma canon_args_invariant : forall ms ms' c gs k A vs vs', tele_rel nr T ms ms' -> ind_con D c = Some gs ->
        List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (ar ms c) k vs vs' -> (ar ms c k vs <~> ar ms' c k vs').
    Proof.
      intros * Hm Hc Hk Hp; assert (Hkl : k < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
      exact (canon_args_invariant_all _ _ _ _ Hm Hc _ (le_n _) k vs vs' Hkl Hp).
    Qed.

    Lemma canon_args_rel_refl_r : forall ms ms' c gs k ws ws', tele_rel nr T ms ms' -> ind_con D c = Some gs ->
        k <= List.length (cargs_nonrec gs) -> tele_prefix_rel (ar ms c) k ws ws' -> tele_prefix_rel (ar ms' c) k ws' ws'.
    Proof.
      intros * Hm Hc Hk Hp.
      pose proof (canon_nparams_rel_refl_r _ _ Hm) as Hm'.
      eapply (tele_prefix_rel_cross_refl (ar ms c) (ar ms' c) (List.length (cargs_nonrec gs))); [ exact Hk | | | exact Hp ].
      - intros j0 pa pb Hj0 Hp1 _; destruct (nth_error_lt_some' (cargs_nonrec gs) j0 Hj0) as [A0 HA0].
        eapply canon_args_invariant; eassumption.
      - intros j0 ? ? Hj0 Hp0; destruct (nth_error_lt_some' (cargs_nonrec gs) j0 Hj0) as [A0 HA0].
        eapply canon_args_per; [ exact Hm' | exact Hc | exact HA0 | exact Hp0 ].
    Qed.

    (** The domains of the shapes, likewise. *)
    Lemma canon_doms_evals : forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_rel nr T ms ms' ->
        ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        tele_prefix_rel (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
        List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel dr ms ws (ptyp_doms t)) k ys ys' ->
        rel_mod_eval (per_univ_elem u) B (env_args nil (ups ++ ms ++ ws ++ ys)) B (env_args nil (ups' ++ ms' ++ ws' ++ ys'))
          (dr (ms ++ ws ++ ys) B).
    Proof.
      intros * Hm Hc Heq Hw HB Hy; destruct (Hdm _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw HB Hy) as (a & a' & Ea & Ea' & [R HR]).
      econstructor; [ exact Ea | exact Ea' |].
      unfold dr, canon_doms_rel; exact (per_head_diag Ea HR).
    Qed.

    Lemma canon_doms_per : forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_rel nr T ms ms' ->
        ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        tele_prefix_rel (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
        List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel dr ms ws (ptyp_doms t)) k ys ys' ->
        PER (dr (ms ++ ws ++ ys) B).
    Proof.
      intros * Hm Hc Heq Hw HB Hy; destruct (canon_doms_evals _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw HB Hy) as [a a' _ _ HR].
      eapply per_elem_PER; exact HR.
    Qed.

    Lemma canon_doms_invariant_all : forall ms ms' c gs gs1 t gs2 ws ws', tele_rel nr T ms ms' ->
        ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        tele_prefix_rel (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
        forall k, k <= List.length (ptyp_doms t) ->
        forall j B ys ys', j < k -> List.nth_error (ptyp_doms t) j = Some B ->
          tele_prefix_rel (shape_doms_rel dr ms ws (ptyp_doms t)) j ys ys' ->
          (dr (ms ++ ws ++ ys) B <~> dr (ms' ++ ws' ++ ys') B).
    Proof.
      intros ms ms' c gs gs1 t gs2 ws ws' Hm Hc Heq Hw.
      pose proof (canon_nparams_rel_refl_r _ _ Hm) as Hm'.
      assert (Hk1 : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      pose proof (canon_args_rel_refl_r _ _ _ _ _ _ _ Hm Hc Hk1 Hw) as Hw'.
      induction k as [| k IH]; intros Hk j B ys ys' Hj HB Hp; [ lia |].
      destruct (Nat.lt_ge_cases j k) as [Hjk | Hjk]; [ eapply IH; [ lia | exact Hjk | exact HB | exact Hp ] |].
      assert (j = k) as -> by lia.
      assert (Hp' : tele_prefix_rel (shape_doms_rel dr ms' ws' (ptyp_doms t)) k ys' ys').
      { eapply (tele_prefix_rel_cross_refl (shape_doms_rel dr ms ws (ptyp_doms t)) (shape_doms_rel dr ms' ws' (ptyp_doms t)) k k); [ lia | | | exact Hp ].
        - intros j0 pa pb Hj0 Hp1 _.
          destruct (nth_error_lt_some' (ptyp_doms t) j0 ltac:(lia)) as [B0 HB0].
          unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB0).
          exact (IH ltac:(lia) j0 B0 pa pb Hj0 HB0 Hp1).
        - intros j0 ? ? Hj0 Hp0; destruct (nth_error_lt_some' (ptyp_doms t) j0 ltac:(lia)) as [B0 HB0].
          unfold shape_doms_rel at 1; rewrite (List.nth_error_nth _ _ _ HB0).
          eapply canon_doms_per; [ exact Hm' | exact Hc | exact Heq | exact Hw' | exact HB0 | exact Hp0 ]. }
      destruct (canon_doms_evals _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw HB Hp) as [a a' Ea Ea' HR1].
      destruct (canon_doms_evals _ _ _ _ _ _ _ _ _ _ _ _ _ Hm' Hc Heq Hw' HB Hp') as [b b' Eb Eb' HR2].
      functional_eval_rewrite_clear.
      eapply per_univ_elem_left_irrel; [ exact HR1 | exact HR2 ].
    Qed.

    Lemma canon_doms_invariant : forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_rel nr T ms ms' ->
        ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        tele_prefix_rel (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
        List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel dr ms ws (ptyp_doms t)) k ys ys' ->
        (dr (ms ++ ws ++ ys) B <~> dr (ms' ++ ws' ++ ys') B).
    Proof.
      intros * Hm Hc Heq Hw HB Hy; assert (Hkl : k < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
      exact (canon_doms_invariant_all _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw _ (le_n _) k B ys ys' Hkl HB Hy).
    Qed.

    (** Uniform parameters whose types' values are related to those at
        [ups] are admissible: a variable of a type is related to one of a
        related type, and an element of a related type reads back alike. *)
    Lemma canon_adm : forall u2,
        (forall k A vs vs', List.nth_error T k = Some (ce_ass A) -> tele_prefix_rel nr k vs vs' ->
           exists a a', ⟦ A ⟧ env_args nil (ups ++ vs) ↘ a /\ ⟦ A ⟧ env_args nil (u2 ++ vs') ↘ a' /\
             Dom a ≈ a' ∈ per_univ u) ->
        (forall ms ms' c gs k A vs vs', tele_rel nr T ms ms' -> ind_con D c = Some gs ->
           List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (ar ms c) k vs vs' ->
           exists a a', ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ a /\ ⟦ A ⟧ env_args nil (u2 ++ ms' ++ vs') ↘ a' /\
             Dom a ≈ a' ∈ per_univ u) ->
        (forall ms ms' c gs gs1 t gs2 ws ws' ys ys', tele_rel nr T ms ms' ->
           ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
           tele_prefix_rel (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
           tele_rel (shape_doms_rel dr ms ws (ptyp_doms t)) (ptyp_doms t) ys ys' ->
           rel_evals (ptyp_ps t) (env_args nil (ups ++ ms ++ ws ++ ys)) (env_args nil (u2 ++ ms' ++ ws' ++ ys')) (tele_rel nr T)) ->
        (forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_rel nr T ms ms' ->
           ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
           tele_prefix_rel (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
           List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel dr ms ws (ptyp_doms t)) k ys ys' ->
           exists a a', ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ a /\
             ⟦ B ⟧ env_args nil (u2 ++ ms' ++ ws' ++ ys') ↘ a' /\ Dom a ≈ a' ∈ per_univ u) ->
        adm_uparams D ups nr ar dr u2.
    Proof.
      intros u2 Hn2 Ha2 Hc2 Hd2; constructor; [ | | exact Hc2 | ].
      - intros k A vs vs' s Hk Hp; destruct (Hn2 _ _ _ _ Hk Hp) as (a & a' & Ea & Ea' & [R HR]).
        exists a a'; [ exact Ea | exact Ea' |].
        unfold T in Hk; unfold nr, canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ Hk).
        eapply per_head_of; [ exact Ea | exact Ea | | exact (var_per_elem s HR) ].
        eapply per_univ_trans; [ exact HR | apply per_univ_sym; exact HR ].
      - intros ms ms' c gs k A vs vs' s Hm Hc Hk Hp; destruct (Ha2 _ _ _ _ _ _ _ _ Hm Hc Hk Hp) as (a & a' & Ea & Ea' & [R HR]).
        exists a a'; [ exact Ea | exact Ea' |].
        unfold ar, canon_args_rel; rewrite (nth_atyp_eq _ _ _ _ _ Hc Hk).
        eapply per_head_of; [ exact Ea | exact Ea | | exact (var_per_elem s HR) ].
        eapply per_univ_trans; [ exact HR | apply per_univ_sym; exact HR ].
      - intros ms ms' c gs gs1 t gs2 ws ws' k B ys ys' Hm Hc Heq Hw HB Hy.
        destruct (Hd2 _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw HB Hy) as (a & a' & Ea & Ea' & [R HR]).
        exists a a'; [ exact Ea | exact Ea' |].
        pose proof (per_head_diag Ea HR) as HR'.
        destruct (realize_per_univ_elem_gen HR') as (_ & _ & Hrb).
        intros x x' Hx; apply Hrb; exact Hx.
    Qed.

    (** The clause. *)
    Lemma per_univ_elem_indty_canon : forall ns ns', tele_rel nr T ns ns' ->
        DF d_ind p (ups ++ ns) ≈ d_ind p (ups' ++ ns') ∈ per_univ_elem u ↘ (ind_rel p D (adm_uparams D ups nr ar dr) nr ar dr ns ns').
    Proof.
      intros * Hns.
      basic_per_univ_elem_econstructor;
        [ exact Hl | exact Hass | exact Hu | exact Hu' | exact Hps | exact canon_nparams_per | | exact canon_nparams_invariant
        | exact canon_args_per | | exact canon_args_invariant | exact canon_doms_per | | exact canon_doms_invariant
        | exact (canon_adm ups' Hn Ha Hcl Hdm) | exact (canon_adm ups Hnd Had Hcd Hdmd)
        | exact Hns | reflexivity ].
      - intros; eapply canon_nparams_evals; eassumption.
      - intros; eapply canon_args_evals; eassumption.
      - intros; eapply canon_doms_evals; eassumption.
    Qed.
  End Canon.

  (** Inverting the relation of a recursive argument by its shape. *)
Lemma rec_arg_self_inv : forall p D Ok nr ar dr u u' pre pre' k Ps v v',
    rec_arg_rel p D Ok nr ar dr u u' pre pre' (pt_self k Ps) v v' ->
    exists bs bs', ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (u ++ pre) ↘ bs /\
      ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (u' ++ pre') ↘ bs' /\ ind_rel p D Ok nr ar dr bs bs' v v'.
Proof. intros * H; inversion H; subst; eauto 6. Qed.

Lemma rec_arg_pi_inv : forall p D Ok nr ar dr u u' pre pre' B t f f',
    rec_arg_rel p D Ok nr ar dr u u' pre pre' (pt_pi B t) f f' ->
    forall c c', dr pre B c c' ->
      exists r r', $| f & c | gc_deps ⍮ gc_stack ↘ r /\ $| f' & c' | gc_deps ⍮ gc_stack ↘ r' /\
        rec_arg_rel p D Ok nr ar dr u u' (pre ++ c :: nil) (pre' ++ c' :: nil) t r r'.
Proof.
  intros * H c c' Hc; inversion H; subst.
  match goal with Hf : forall c c', dr _ _ c c' -> _ |- _ => pose proof (Hf c c' Hc) as Happ end.
  inversion Happ; subst; eauto.
Qed.

End Fixed_GCtx.
