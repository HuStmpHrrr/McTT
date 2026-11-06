(** * PER Lemmas: Context PERs

    The fifth part of [Core.Semantic.PER.Lemmas]: the tactics on the
    heads of context PERs, the environments of definition entries, and
    [per_ctx_env] is right irrelevant and a PER. *)
From Stdlib Require Import Equivalence Lia List Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.Chain PER.CoreTactics PER.Definitions PER.Tele.
From Mctt.Core.Semantic.PER.Lemmas Require Export ModuleValues.
Import Domain_Notations Fixed_Notations.
Import ListNotations.

(** A head tied to the value of one module expression is tied to the value
    of any expression related to it over the same tail. *)
(** The kind of a head entry, a field of the context PERs' records: an
    entry stored at some type and unit, as a hypothesis has it, possibly
    with its witnesses taken apart. *)
Ltac solve_entry_kind :=
  match goal with
  | |- exists t U0, _ = de_dm _ _ _ _ => first [ assumption | do 2 eexists; eassumption | do 2 eexists; reflexivity ]
  | |- exists U0, _ = de_mod _ _ => first [ assumption | eexists; eassumption | eexists; reflexivity ]
  end.

Ltac solve_tie :=
  match goal with
  | |- tie_mod ?m ?H2 ?r =>
      first [ assumption
            | match goal with
              | Ht : tie_mod m ?H1 ?r1, Hm : rel_modexp_evals ?H1 ?r1 H2 r |- _ => exact (tie_mod_move _ _ _ _ _ Ht Hm)
              end
            | match goal with
              | Ht : tie_mod m ?H1 r, HU : forall ρ ρ', ?T ρ ρ' -> rel_modexp_evals ?H1 ρ H2 ρ', Hr : ?T r r |- _ =>
                  exact (tie_mod_move _ _ _ _ _ Ht (HU _ _ Hr))
              end
            | match goal with
              | Ht : tie_mod m ?H1 r, HU : forall ρ ρ', ?T ρ ρ' -> rel_modexp_evals H2 ρ ?H1 ρ', Hr : ?T r r |- _ =>
                  exact (tie_mod_move _ _ _ _ _ Ht (rel_modexp_evals_sym _ _ _ _ (HU _ _ Hr)))
              end ]
  end.

(** The heads of a definition entry related across chains of tails: the
    hypotheses saturated once ([solve_def_heads_pre]), then each part of
    the goal closed ([solve_def_heads_post]).  A goal of many parts, such
    as [per_ctx_env_dm_rel]'s, is split between the two, so that the
    saturation is not run once per part. *)
Ltac solve_def_heads_pre :=
  destruct_rel_typ; handle_per_univ_elem_irrel;
  match goal with H : per_univ_elem _ _ _ _ |- _ => pose proof (per_elem_PER H) end;
  move_by_relation_equivalence.

(** A field that a hypothesis states, such as a [head_readable] one, is
    taken before it is split. *)
Ltac solve_def_heads_post :=
  repeat (first [ assumption | solve_entry_kind | split ]); try (move_goal_by_relation_equivalence; solve_per);
  try (eexists; split; [ eassumption | move_goal_by_relation_equivalence; solve_per ]).

Ltac solve_def_heads := solve_def_heads_pre; solve_def_heads_post.

(** Two derivations of a definition entry give its type one sort, read at
    a tail related in both; then the sort is taken apart: at a relevant
    type the bodies are related and the heads tied to them, as before
    propositions, at a proposition nothing is. *)
Ltac same_def_sort :=
  repeat match goal with
    | Hs1 : context [rel_typ_kind ?A _ ?r1], Hs2 : context [rel_typ_kind ?A _ ?r2] |- _ =>
        assert_fails constr_eq r1 r2; is_var r2;
        match goal with
        | He1 : _ ?x _, He2 : _ ?x _ |- _ =>
            let E := fresh "E" in
            assert (E : r2 = r1) by exact (rel_typ_kind_unique _ _ _ _ (Hs2 _ _ He2) (Hs1 _ _ He1));
            subst r2
        end
    end;
  (** The kind is a variable unless it is fixed, as a definition with a
      module part's is, at [ak_relevant]. *)
  try match goal with H : context [rel_typ_kind _ _ ?r] |- _ => is_var r; destruct r end;
  cbn [def_heads_at def_bodies_at] in *;
  repeat match goal with H : def_heads _ _ _ _ _ |- _ => destruct H end;
  destruct_conjs.

(** The term-head field of an extended context PER at a proposition, from
    the one at hand: the type at the goal's tail is a proposition exactly
    when the type of the field at hand is one at its tail, as the two are
    related ([rel_typ_propositional_right], [_left]) at related tails. *)
Ltac solve_prop_head :=
  let Hp := fresh "Hp" in
  intros Hp;
  match goal with
  | H : rel_typ_propositional _ _ -> ?g |- ?g =>
      apply H;
      first
        [ exact Hp
        | match goal with
          | H1 : forall ρ ρ' (_ : ?T1 ρ ρ'), rel_mod_eval (per_univ_elem _) _ ρ _ ρ' _, e1 : ?T1 _ _ |- _ =>
              first
                [ exact (rel_typ_propositional_right (H1 _ _ e1) Hp)
                | exact (rel_typ_propositional_left (H1 _ _ e1) Hp) ]
          | H1 : forall ρ ρ' (_ : ?T1 ρ ρ'), rel_typ _ _ ρ _ ρ' _, e1 : ?T1 _ _ |- _ =>
              first
                [ exact (rel_typ_propositional_right (H1 _ _ e1) Hp)
                | exact (rel_typ_propositional_left (H1 _ _ e1) Hp) ]
          end
        | match goal with
          | H1 : forall ρ ρ' (_ : ?T1 ρ ρ'), rel_mod_eval (per_univ_elem _) _ ρ _ ρ' _, e1 : ?T1 _ _, e2 : ?T1 _ _ |- _ =>
              first
                [ exact (rel_typ_propositional_right (H1 _ _ e1) (rel_typ_propositional_left (H1 _ _ e2) Hp))
                | exact (rel_typ_propositional_left (H1 _ _ e1) (rel_typ_propositional_right (H1 _ _ e2) Hp)) ]
          | H1 : forall ρ ρ' (_ : ?T1 ρ ρ'), rel_typ _ _ ρ _ ρ' _, e1 : ?T1 _ _, e2 : ?T1 _ _ |- _ =>
              first
                [ exact (rel_typ_propositional_right (H1 _ _ e1) (rel_typ_propositional_left (H1 _ _ e2) Hp))
                | exact (rel_typ_propositional_left (H1 _ _ e1) (rel_typ_propositional_right (H1 _ _ e2) Hp)) ]
          end
        | match goal with
          | H1 : forall ρ ρ' (_ : ?T1 ρ ρ'), rel_mod_eval (per_univ_elem _) _ ρ _ ρ' _, e1 : ?T1 _ _,
            H2 : forall ρ ρ' (_ : ?T2 ρ ρ'), rel_mod_eval (per_univ_elem _) _ ρ _ ρ' _, e2 : ?T2 _ _ |- _ =>
              first
                [ exact (rel_typ_propositional_right (H1 _ _ e1) Hp)
                | exact (rel_typ_propositional_left (H1 _ _ e1) Hp)
                | exact (rel_typ_propositional_right (H1 _ _ e1) (rel_typ_propositional_left (H2 _ _ e2) Hp))
                | exact (rel_typ_propositional_left (H1 _ _ e1) (rel_typ_propositional_right (H2 _ _ e2) Hp)) ]
          | H1 : forall ρ ρ' (_ : ?T1 ρ ρ'), rel_typ _ _ ρ _ ρ' _, e1 : ?T1 _ _,
            H2 : forall ρ ρ' (_ : ?T2 ρ ρ'), rel_typ _ _ ρ _ ρ' _, e2 : ?T2 _ _ |- _ =>
              first
                [ exact (rel_typ_propositional_right (H1 _ _ e1) Hp)
                | exact (rel_typ_propositional_left (H1 _ _ e1) Hp)
                | exact (rel_typ_propositional_right (H1 _ _ e1) (rel_typ_propositional_left (H2 _ _ e2) Hp))
                | exact (rel_typ_propositional_left (H1 _ _ e1) (rel_typ_propositional_right (H2 _ _ e2) Hp)) ]
          end ]
  end.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The environments of a definition entry from the head relation and the
    bodies' ties taken together, as one goal. *)
Lemma mk_per_ctx_env_def_rel' : forall tail_rel
    (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), relation domain) A A' r M M' ρ ρ'
    (Ht : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel),
    Dom (ρ 0) ≈ (ρ' 0) ∈ head_rel Ht /\ def_heads_at r (head_rel Ht) M M' ρ ρ' ->
    (rel_typ_propositional A ρ↯ -> exists t, env_entry ρ 0 = de_term (ρ 0) t) ->
    (rel_typ_propositional A' ρ'↯ -> exists t, env_entry ρ' 0 = de_term (ρ' 0) t) ->
    head_readable 0 (env_entry ρ 0) ->
    head_readable 0 (env_entry ρ' 0) ->
    per_ctx_env_def_rel tail_rel (@head_rel) A A' r M M' ρ ρ'.
Proof. intros * [Hh Hd] Hl Hr Hrl Hrr; exact (mk_per_ctx_env_def_rel _ _ _ _ _ _ _ _ _ Ht Hh Hd Hl Hr Hrl Hrr). Qed.

(** Related contexts have as many entries. *)
Lemma per_ctx_env_length : forall {Γ Δ R}, EF Γ ≈ Δ ∈ per_ctx_env ↘ R -> List.length Γ = List.length Δ.
Proof. induction 1; cbn [List.length]; congruence. Qed.

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
  split; intros [Ht Hh Hl Hr Hrl Hrr].
  - assert (Ht0 : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel0) by intuition;
      apply (mk_per_ctx_env_cons_rel _ _ _ _ _ _ Ht0); [| assumption | solve_prop_head | assumption | assumption ];
      destruct_rel_typ; handle_per_univ_elem_irrel; intuition.
  - assert (Ht0 : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel) by intuition;
      apply (mk_per_ctx_env_cons_rel _ _ _ _ _ _ Ht0); [| assumption | solve_prop_head | assumption | assumption ];
      destruct_rel_typ; handle_per_univ_elem_irrel; intuition.
  - (** A definition: the heads are tied to the bodies, which are related
        across the two right-hand contexts through the left body. *)
    specialize (IHHorig _ _ equiv_Γ_Γ'0).
    intros ρ ρ'.
    (** The bodies are read at the target's tails: its related pair and
        each side against itself. *)
    split; intros [Ht ? ? Hl Hr Hrl Hrr];
      [ assert (Ht0 : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel0) by (apply IHHorig; exact Ht);
        assert (Dom ρ↯ ≈ ρ↯ ∈ tail_rel0) by (etransitivity; [ exact Ht0 | symmetry; exact Ht0 ]);
        assert (Dom ρ'↯ ≈ ρ'↯ ∈ tail_rel0) by (etransitivity; [ symmetry; exact Ht0 | exact Ht0 ])
      | assert (Ht0 : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel) by (apply IHHorig; exact Ht);
        assert (Dom ρ↯ ≈ ρ↯ ∈ tail_rel) by (etransitivity; [ exact Ht0 | symmetry; exact Ht0 ]);
        assert (Dom ρ'↯ ≈ ρ'↯ ∈ tail_rel) by (etransitivity; [ symmetry; exact Ht0 | exact Ht0 ]) ];
      (** The two derivations give the type one sort, at a related tail. *)
      same_def_sort; apply (mk_per_ctx_env_def_rel _ _ _ _ _ _ _ _ _ Ht0); try exact Hl; try exact Hrl; try exact Hrr;
      try solve_prop_head; cbn [def_heads_at]; first [ exact I | solve_def_heads ].
  - (** A slot: the heads are tied to the closures of the left unit, which
        are related to the closures of either right unit. *)
    specialize (IHHorig _ _ equiv_Γ_Γ'0).
    intros ρ ρ'.
    split; intros [Ht ? ? ? ? ? ?];
      [ assert (Ht0 : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel0) by intuition
      | assert (Ht0 : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel) by intuition ];
      assert (Dom ρ↯ ≈ ρ↯ ∈ tail_rel) by (etransitivity; [| symmetry]; intuition);
      assert (Dom ρ'↯ ≈ ρ'↯ ∈ tail_rel) by (etransitivity; [symmetry |]; intuition);
      assert (Dom ρ↯ ≈ ρ↯ ∈ tail_rel0) by (etransitivity; [| symmetry]; intuition);
      assert (Dom ρ'↯ ≈ ρ'↯ ∈ tail_rel0) by (etransitivity; [symmetry |]; intuition);
      repeat (first [ assumption | split ]); solve_tie.
  - (** A definition with a module part: the term part as a definition, the
        unit as a slot.  In each direction the tails the heads are read at
        are the target's: its related pair and each side against itself.
        The hypotheses are saturated once ([solve_def_heads_pre]), before
        the relation is split into its fields. *)
    specialize (IHHorig _ _ equiv_Γ_Γ'0).
    intros ρ ρ'.
    split; intros [Ht Hh Hterms Hul Hul' Hur Hur' Hrl Hrr].
    + assert (Ht0 : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel0) by (apply IHHorig; exact Ht).
      assert (Dom ρ↯ ≈ ρ↯ ∈ tail_rel0) by (etransitivity; [ exact Ht0 | symmetry; exact Ht0 ]).
      assert (Dom ρ'↯ ≈ ρ'↯ ∈ tail_rel0) by (etransitivity; [ symmetry; exact Ht0 | exact Ht0 ]).
      same_def_sort; solve_def_heads_pre.
      all: apply (mk_per_ctx_env_dm_rel _ _ _ _ _ _ _ _ _ Ht0); try exact Hrl; try exact Hrr; solve_def_heads_post; solve_tie.
    + assert (Ht0 : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel) by (apply IHHorig; exact Ht).
      assert (Dom ρ↯ ≈ ρ↯ ∈ tail_rel) by (etransitivity; [ exact Ht0 | symmetry; exact Ht0 ]).
      assert (Dom ρ'↯ ≈ ρ'↯ ∈ tail_rel) by (etransitivity; [ symmetry; exact Ht0 | exact Ht0 ]).
      same_def_sort; solve_def_heads_pre.
      (** The units' relations are stated over the other right-hand
          context's tails, which the ties are read at too. *)
      all: assert (Dom ρ↯ ≈ ρ↯ ∈ tail_rel0) by (etransitivity; [ exact Ht | symmetry; exact Ht ]).
      all: assert (Dom ρ'↯ ≈ ρ'↯ ∈ tail_rel0) by (etransitivity; [ symmetry; exact Ht | exact Ht ]).
      all: apply (mk_per_ctx_env_dm_rel _ _ _ _ _ _ _ _ _ Ht0); try exact Hrl; try exact Hrr; solve_def_heads_post; solve_tie.
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
  - (** The swapped type is not [LevelSort] either: it is related to the
        original one at the swapped tails. *)
    assert (Hρ' : tail_rel ρ' ρ) by eauto.
    match goal with
    | HT : forall ρ0 ρ'0 (e : tail_rel ρ0 ρ'0), rel_mod_eval _ A _ A' _ _,
      HN : forall ρ0 ρ'0, tail_rel ρ0 ρ'0 -> value_not_level_sort A _ |- _ =>
        exact (rel_mod_eval_not_level_sort _ _ _ _ _ _ (fun _ _ _ H => per_univ_elem_not_level_sort_iff _ _ _ _ H)
                 (HT _ _ Hρ') (HN _ _ Hρ'))
    end.
  - (** The swapped assumption relates the same environments: its types are
        related to the original ones at each tail against itself. *)
    match goal with HE : env_rel <~> _ |- _ => rename HE into HE0 end.
    intros ρ ρ'; split; intros Hρ; [ apply HE0 in Hρ | apply HE0 ]; destruct Hρ as [Ht Hh Hl Hr Hrl Hrr];
      assert (tail_rel ρ↯ ρ↯) by (etransitivity; [ exact Ht | symmetry; exact Ht ]);
      assert (tail_rel ρ'↯ ρ'↯) by (etransitivity; [ symmetry; exact Ht | exact Ht ]);
      (apply (mk_per_ctx_env_cons_rel _ _ _ _ _ _ Ht); [ exact Hh | solve_prop_head | solve_prop_head | assumption | assumption ]).
  - apply_relation_equivalence.
    match goal with H : per_ctx_env_cons_rel _ _ _ _ _ _ |- _ => destruct H as [Ht Hh Hl Hr Hrl Hrr] end.
    assert (Ht' : tail_rel ρ'↯ ρ↯) by eauto.
    assert (tail_rel ρ↯ ρ↯) by (etransitivity; eassumption).
    assert (tail_rel ρ'↯ ρ'↯) by (etransitivity; eassumption).
    apply (mk_per_ctx_env_cons_rel _ _ _ _ _ _ Ht'); [| solve_prop_head | solve_prop_head | assumption | assumption ].
    destruct_rel_mod_eval.
    symmetry; handle_per_univ_elem_irrel; intuition.
  - (** A definition.  The swapped context has the same head relation and
        sort, and its environment relation lists the same four ties in
        another order. *)
    simpl in *; destruct_conjs.
    match goal with HE : env_rel <~> _ |- _ => rename HE into HE0 end.
    split.
    + eapply per_ctx_env_cons_def with (head_rel := head_rel) (r := r); [ eassumption | eassumption | | | |].
      * intros ρ ρ' Hρ.
        assert (tail_rel ρ' ρ) by eauto.
        assert (tail_rel ρ ρ) by (etransitivity; eassumption).
        destruct_rel_mod_eval.
        handle_per_univ_elem_irrel.
        econstructor; eauto.
        symmetry; solve [intuition].
      * intros ρ ρ' Hρ.
        assert (Hρ' : tail_rel ρ' ρ) by eauto.
        match goal with
        | HT : forall ρ ρ' (e : tail_rel ρ ρ'), rel_mod_eval _ _ ρ _ ρ' _,
          HS : forall ρ ρ' (e : tail_rel ρ ρ'), rel_typ_kind _ ρ _ |- _ =>
            exact (rel_typ_kind_right (HT _ _ Hρ') (HS _ _ Hρ'))
        end.
      * intros ρ ρ' Hρ.
        (** At a proposition nothing is asked of the bodies. *)
        destruct r; cbn [def_bodies_at rel_elem] in *; [| exact I |].
        all: assert (tail_rel ρ' ρ) by eauto.
        all: assert (tail_rel ρ ρ) by (etransitivity; eassumption).
        all: destruct_rel_mod_eval.
        all: handle_per_univ_elem_irrel.
        all: match goal with H : per_univ_elem _ _ _ _ |- _ => pose proof (per_elem_PER H) end.
        all: move_by_relation_equivalence.
        all: econstructor; try eassumption.
        all: move_goal_by_relation_equivalence; solve_per.
      * intros ρ ρ'; split; intros Hρ;
          [ apply HE0 in Hρ | apply HE0 ]; destruct Hρ as [e Hh Hd Hl Hr Hrl Hrr];
          assert (tail_rel ρ↯ ρ↯) by (etransitivity; [ exact e | symmetry; exact e ]);
          assert (tail_rel ρ'↯ ρ'↯) by (etransitivity; [ symmetry; exact e | exact e ]);
          (apply (mk_per_ctx_env_def_rel _ _ _ _ _ _ _ _ _ e);
           [ exact Hh | apply def_heads_at_swap; exact Hd | solve_prop_head | solve_prop_head | assumption | assumption ]).
    + intros ρ ρ' Hρ.
      apply HE0 in Hρ; apply HE0.
      destruct Hρ as [e ? Hd Hl Hr Hrl Hrr].
      assert (Ht : tail_rel ρ'↯ ρ↯) by eauto.
      assert (tail_rel ρ↯ ρ↯) by (etransitivity; eassumption).
      assert (tail_rel ρ'↯ ρ'↯) by (etransitivity; eassumption).
      destruct r; cbn [def_heads_at def_bodies_at rel_elem] in *; [ destruct Hd; destruct_conjs | | destruct Hd; destruct_conjs ].
      all: apply (mk_per_ctx_env_def_rel _ _ _ _ _ _ _ _ _ Ht); try exact Hrl; try exact Hrr; try solve_prop_head; cbn [def_heads_at].
      all: destruct_rel_mod_eval.
      all: handle_per_univ_elem_irrel.
      all: match goal with H : per_univ_elem _ _ _ _ |- _ => pose proof (per_elem_PER H) end.
      all: move_by_relation_equivalence.
      all: repeat split; try (move_goal_by_relation_equivalence; solve_per);
        eexists; split; try eassumption; move_goal_by_relation_equivalence; solve_per.
  - (** A slot.  The swapped context ties the heads to the same closures. *)
    simpl in *; destruct_conjs.
    match goal with
    | HU : forall ρ ρ', tail_rel ρ ρ' -> rel_modexp_evals _ _ _ _,
      HE : env_rel <~> _, Hs : forall ρ ρ', tail_rel ρ ρ' -> tail_rel ρ' ρ,
      Hc : per_ctx_env tail_rel ?Γ1 ?Γ2 |- _ =>
        (** The swapped context's tail has as many entries. *)
        pose proof (per_ctx_env_length Hc) as Hlen;
        split;
        [ eapply per_ctx_env_cons_mod; [ eassumption | eassumption | eassumption | eassumption | | ];
          [ intros ρ ρ' Hρ; apply rel_modexp_evals_sym, HU, Hs, Hρ
          | intros ρ ρ'; split; intros Hρ; [ apply HE in Hρ | apply HE ]; destruct Hρ;
            constructor; first [ assumption | rewrite Hlen in *; assumption | rewrite <- Hlen in *; assumption ] ]
        | intros ρ ρ' Hρ; apply HE in Hρ; apply HE; destruct Hρ; constructor; eauto ]
    end.
  - (** A definition with a module part: the term part as a definition, the
        unit as a slot. *)
    simpl in *; destruct_conjs.
    match goal with
    | HU : forall ρ ρ', tail_rel ρ ρ' -> rel_modexp_evals _ _ _ _,
      HE : env_rel <~> _, Hs : forall ρ ρ', tail_rel ρ ρ' -> tail_rel ρ' ρ |- _ =>
        rename HU into HU0; rename HE into HE0; rename Hs into Hs0
    end.
    split.
    + eapply per_ctx_env_cons_dm with (head_rel := head_rel) (r := r); [ eassumption | eassumption | | | | | | assumption ].
      * intros ρ ρ' Hρ.
        assert (tail_rel ρ' ρ) by eauto.
        assert (tail_rel ρ ρ) by (etransitivity; eassumption).
        destruct_rel_mod_eval.
        handle_per_univ_elem_irrel.
        econstructor; eauto.
        symmetry; solve [intuition].
      * intros ρ ρ' Hρ.
        assert (Hρ' : tail_rel ρ' ρ) by eauto.
        match goal with
        | HT : forall ρ ρ' (e : tail_rel ρ ρ'), rel_mod_eval _ _ ρ _ ρ' _,
          HS : forall ρ ρ' (e : tail_rel ρ ρ'), rel_typ_kind _ ρ _ |- _ =>
            exact (rel_typ_kind_right (HT _ _ Hρ') (HS _ _ Hρ'))
        end.
      * cbn [rel_elem] in *.
        intros ρ ρ' Hρ.
        assert (tail_rel ρ' ρ) by eauto.
        assert (tail_rel ρ ρ) by (etransitivity; eassumption).
        destruct_rel_mod_eval.
        handle_per_univ_elem_irrel.
        match goal with H : per_univ_elem _ _ _ _ |- _ => pose proof (per_elem_PER H) end.
        move_by_relation_equivalence.
        econstructor; try eassumption.
        move_goal_by_relation_equivalence; solve_per.
      * intros ρ ρ' Hρ; apply rel_modexp_evals_sym, HU0, Hs0, Hρ.
      * intros ρ ρ'; split; intros Hρ;
          [ apply HE0 in Hρ | apply HE0 ]; destruct Hρ as [Ht Hh Hd ? ? ? ? ? ?];
          (apply (mk_per_ctx_env_dm_rel _ _ _ _ _ _ _ _ _ Ht); try assumption; apply def_heads_at_swap; assumption).
    + intros ρ ρ' Hρ.
      apply HE0 in Hρ; apply HE0.
      destruct Hρ as [e Hh Hd Hul Hul' Hur Hur' Hrl Hrr].
      assert (Ht : tail_rel ρ'↯ ρ↯) by eauto.
      assert (tail_rel ρ↯ ρ↯) by (etransitivity; eassumption).
      assert (tail_rel ρ'↯ ρ'↯) by (etransitivity; eassumption).
      destruct r; cbn [def_heads_at def_bodies_at rel_elem] in *; [ destruct Hd; destruct_conjs | | destruct Hd; destruct_conjs ].
      (** Saturated once, before the relation is split into its fields. *)
      all: destruct_rel_mod_eval.
      all: handle_per_univ_elem_irrel.
      all: match goal with H : per_univ_elem _ _ _ _ |- _ => pose proof (per_elem_PER H) end.
      all: move_by_relation_equivalence.
      all: apply (mk_per_ctx_env_dm_rel _ _ _ _ _ _ _ _ _ Ht);
        try assumption; try solve_entry_kind; try (move_goal_by_relation_equivalence; solve_per); try exact I;
        constructor; eexists; split; try eassumption; move_goal_by_relation_equivalence; solve_per.
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
(** The environments a definition with a module part relates, taken apart
    into their tails, heads and ties. *)
Ltac destruct_dm_rels :=
  repeat match goal with H : per_ctx_env_dm_rel _ _ _ _ _ _ _ _ _ |- _ => destruct H end.

(** Those an assumption and a definition relate, likewise. *)
Ltac destruct_cons_rels :=
  repeat match goal with H : per_ctx_env_cons_rel _ _ _ _ _ _ |- _ => destruct H end.

Ltac destruct_def_rels :=
  repeat match goal with H : per_ctx_env_def_rel _ _ _ _ _ _ _ _ _ |- _ => destruct H end.

(** Those a module entry relates, likewise. *)
Ltac destruct_mod_rels :=
  repeat match goal with H : per_ctx_env_mod_rel _ _ _ _ _ _ |- _ => destruct H end.

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

(** The sorts two derivations of a definition entry give its left and its
    right type agree: at a tail related in the first, the left type's sort
    is the right type's, at the second's. *)
Ltac trans_def_sort :=
  try match goal with
    | HS : context [rel_typ_kind ?A _ ?r], HS0 : context [rel_typ_kind ?A' _ ?r0],
      HT : context [rel_typ _ ?A _ ?A' _ _] |- _ =>
        assert_fails constr_eq r r0; is_var r0;
        match goal with
        | Hp : _ ?x ?y, Hp0 : _ ?y _ |- _ =>
            assert (r0 = r) by exact (rel_typ_kind_unique _ _ _ _ (HS0 _ _ Hp0) (rel_typ_kind_right (HT _ _ Hp) (HS _ _ Hp)))
        end;
        subst r0
    | HS : context [rel_typ_kind ?A _ ?r], HS0 : context [rel_typ_kind ?A' _ ?r0],
      HT : context [rel_mod_eval _ ?A _ ?A' _ _] |- _ =>
        assert_fails constr_eq r r0; is_var r0;
        match goal with
        | Hp : _ ?x ?y, Hp0 : _ ?y _ |- _ =>
            assert (r0 = r) by exact (rel_typ_kind_unique _ _ _ _ (HS0 _ _ Hp0) (rel_typ_kind_right (HT _ _ Hp) (HS _ _ Hp)))
        end;
        subst r0
    end.

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
  - (** The right type of the composite is the last one; the right term-head
        field moves to it at the right tail against itself. *)
    econstructor;
      only 5: (match goal with HT : ?T0 <~> tail_rel |- per_ctx_env_cons_rel _ _ _ _ <~> _ =>
                 intros ρ ρ'; split; intros [Ht Hh Hl Hr Hrl Hrr];
                 assert (T0 ρ'↯ ρ'↯) by (apply HT; etransitivity; [ symmetry; exact Ht | exact Ht ]);
                 (apply (mk_per_ctx_env_cons_rel _ _ _ _ _ _ Ht); [ exact Hh | exact Hl | solve_prop_head | exact Hrl | exact Hrr ])
               end);
      eauto.
    + apply_relation_equivalence. intuition.
    + intros.
      assert (tail_rel ρ ρ) by intuition.
      assert (tail_rel0 ρ ρ') by intuition.
      destruct_rel_typ.
      handle_per_univ_elem_irrel.
      econstructor; intuition.
      (** This cannot be [etransitivity], as the two levels [i] differ. *)
      eapply per_univ_trans; [| eassumption]; eassumption.
  - match goal with H2 : per_ctx_env_cons_rel _ _ _ _ ?ρ1 ?ρ2, H3 : per_ctx_env_cons_rel _ _ _ _ ?ρ2 ?ρ3 |- _ =>
      destruct H2 as [Ht1 Hh1 Hl1 Hr1 Hrl1 Hrr1], H3 as [Ht2 Hh2 Hl2 Hr2 Hrl2 Hrr2] end.
    assert (Ht : tail_rel ρ1↯ ρ3↯) by eauto.
    apply (mk_per_ctx_env_cons_rel _ _ _ _ _ _ Ht);
      [| first [ exact Hl1 | solve_prop_head ] | first [ exact Hr2 | solve_prop_head ] | exact Hrl1 | exact Hrr2 ].
    destruct_rel_typ.
    handle_per_univ_elem_irrel.
    apply_relation_equivalence.
    etransitivity; intuition.
  - (** A definition: the right body is moved across the middle one.  The
        two derivations give the middle type one sort, at any related
        tail ([trans_def_sort]). *)
    destruct IHper_ctx_env as [IHctx IHenv].
    eapply per_ctx_env_cons_def with (head_rel := head_rel) (r := r); [ eauto | eassumption | | | |].
    + intros.
      assert (tail_rel ρ ρ) by intuition.
      assert (tail_rel0 ρ ρ') by intuition.
      destruct_rel_typ.
      handle_per_univ_elem_irrel.
      econstructor; intuition.
      eapply per_univ_trans; [| eassumption]; eassumption.
    + eassumption.
    + intros.
      assert (tail_rel ρ ρ) by intuition.
      assert (tail_rel ρ' ρ') by intuition.
      assert (tail_rel0 ρ ρ') by intuition.
      assert (tail_rel0 ρ ρ) by intuition.
      assert (tail_rel0 ρ' ρ') by intuition.
      trans_def_sort.
      (** At a proposition nothing is asked of the bodies. *)
      destruct r; cbn [def_bodies_at] in *; [| exact I |].
      all: destruct_rel_typ; handle_per_univ_elem_irrel.
      all: econstructor; try eassumption.
      all: solve_def_heads.
    + (** The right bodies are related at each tail against itself, in
          the right context's tail relation, which is the left one's. *)
      intros ρ ρ'; split; intros [Ht ? ? Hl Hr Hrl Hrr];
        assert (tail_rel ρ↯ ρ↯) by (etransitivity; [ exact Ht | symmetry; exact Ht ]);
        assert (tail_rel ρ'↯ ρ'↯) by (etransitivity; [ symmetry; exact Ht | exact Ht ]);
        match goal with HE : ?T0 <~> tail_rel |- _ =>
          assert (T0 ρ↯ ρ↯) by (apply HE; assumption);
          assert (T0 ρ'↯ ρ'↯) by (apply HE; assumption)
        end;
        trans_def_sort;
        destruct r; cbn [def_heads_at def_bodies_at] in *;
        repeat match goal with H : def_heads _ _ _ _ _ |- _ => destruct H end; destruct_conjs;
        apply (mk_per_ctx_env_def_rel _ _ _ _ _ _ _ _ _ Ht); try exact Hl; try exact Hr; try exact Hrl; try exact Hrr;
        try solve_prop_head; cbn [def_heads_at]; first [ exact I | solve_def_heads ].
  - cbn beta in *; destruct_conjs; destruct_def_rels.
    assert (Ht : tail_rel ρ1↯ ρ3↯) by eauto.
    assert (tail_rel ρ1↯ ρ1↯) by (etransitivity; [| symmetry]; eassumption).
    assert (tail_rel ρ3↯ ρ3↯) by (etransitivity; [symmetry |]; eassumption).
    apply (mk_per_ctx_env_def_rel _ _ _ _ _ _ _ _ _ Ht); try assumption; try solve_prop_head.
    all: destruct r; cbn [def_heads_at def_bodies_at] in *;
      repeat match goal with H : def_heads _ _ _ _ _ |- _ => destruct H end; destruct_conjs;
      first [ exact I | solve_def_heads ].
  - (** A slot: the closures of the first unit are related to those of the
        last through the middle unit. *)
    destruct IHper_ctx_env as [IHctx IHenv].
    match goal with
    | HU1 : forall ρ ρ', ?T ρ ρ' -> rel_modexp_evals (me_lit ?U1) ρ (me_lit ?U2) ρ',
      HU2 : forall ρ ρ', ?T ρ ρ' -> rel_modexp_evals (me_lit ?U2) ρ (me_lit ?U3) ρ',
      HE : _ <~> _, HT : PER ?T, Hc : per_ctx_env ?T ?Γ2 ?Γ3 |- per_ctx_env _ (?Γ1 ▹ₘ ?U1) (?Γ3 ▹ₘ ?U3) =>
        eapply per_ctx_env_cons_mod with (tail_rel := T);
        [ apply IHctx; exact Hc | exact HT | eassumption | eassumption
        | intros ρ ρ' Hρ; eapply rel_modexp_evals_trans;
          [ apply HU1, Hρ | apply HU2; etransitivity; [ symmetry |]; exact Hρ ]
        | intros ρ ρ'; split; intros Hρ;
          [ pose proof (proj2 (HE ρ ρ') Hρ) as Hρ'; destruct Hρ' as [? ? ? ? ? ? ?];
            destruct Hρ as [? ? ? ? ? ? ?]; constructor; assumption
          | destruct Hρ as [Ht ? ? ? ? ? ?];
            assert (T ρ↯ ρ↯) by (etransitivity; [| symmetry ]; exact Ht);
            assert (T ρ'↯ ρ'↯) by (etransitivity; [ symmetry |]; exact Ht);
            repeat (first [ assumption | split ]); solve_tie ] ]
    end.
  - (** A slot's environments: the outer ones' ties and readable heads, the
        tails by the tails' transitivity. *)
    match goal with H1 : per_ctx_env_mod_rel _ _ _ _ ?ρ1 ?ρ2, H2 : per_ctx_env_mod_rel _ _ _ _ ?ρ2 ?ρ3 |- _ =>
      destruct H1, H2 end.
    constructor; try assumption; eauto.
  - (** A definition with a module part: the right term part as a
        definition, the right unit as a slot, each moved across the middle
        one. *)
    destruct IHper_ctx_env as [IHctx IHenv].
    eapply per_ctx_env_cons_dm with (head_rel := head_rel) (r := ak_relevant); [ eauto | eassumption | | | | | | reflexivity ].
    + intros.
      assert (tail_rel ρ ρ) by intuition.
      assert (tail_rel0 ρ ρ') by intuition.
      destruct_rel_typ.
      handle_per_univ_elem_irrel.
      econstructor; intuition.
      eapply per_univ_trans; [| eassumption]; eassumption.
    + eassumption.
    + intros.
      assert (tail_rel ρ ρ) by intuition.
      assert (tail_rel ρ' ρ') by intuition.
      assert (tail_rel0 ρ ρ') by intuition.
      assert (tail_rel0 ρ ρ) by intuition.
      assert (tail_rel0 ρ' ρ') by intuition.
      destruct_rel_typ; handle_per_univ_elem_irrel.
      econstructor; try eassumption.
      solve_def_heads.
    + intros ρ ρ' Hρ.
      assert (tail_rel ρ' ρ') by (etransitivity; [ symmetry |]; exact Hρ).
      assert (tail_rel0 ρ' ρ') by intuition.
      eapply rel_modexp_evals_trans; eauto.
    + (** As for a definition, and the right unit's ties as a slot's. *)
      intros ρ ρ'; split; intros [Ht ?]; destruct_conjs;
        assert (tail_rel ρ↯ ρ↯) by (etransitivity; [ exact Ht | symmetry; exact Ht ]);
        assert (tail_rel ρ'↯ ρ'↯) by (etransitivity; [ symmetry; exact Ht | exact Ht ]);
        match goal with HE : ?T0 <~> tail_rel |- _ =>
          assert (T0 ρ↯ ρ↯) by (apply HE; assumption);
          assert (T0 ρ'↯ ρ'↯) by (apply HE; assumption)
        end;
        cbn [def_heads_at def_bodies_at] in *;
        repeat match goal with H : def_heads _ _ _ _ _ |- _ => destruct H end; destruct_conjs;
        solve_def_heads_pre; exists Ht; try assumption; solve_def_heads_post; solve_tie.
  - cbn beta in *; destruct_conjs; destruct_dm_rels.
    assert (Ht : tail_rel ρ1↯ ρ3↯) by eauto.
    assert (tail_rel ρ1↯ ρ1↯) by (etransitivity; [| symmetry]; eassumption).
    assert (tail_rel ρ3↯ ρ3↯) by (etransitivity; [symmetry |]; eassumption).
    cbn [def_heads_at def_bodies_at] in *;
      repeat match goal with H : def_heads _ _ _ _ _ |- _ => destruct H end; destruct_conjs;
      solve_def_heads_pre; exists Ht; solve_def_heads_post; assumption.
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
Lemma per_ctx_env_cons' : forall {Γ Γ' i κ A A' tail_rel}
                             (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), relation domain)
                             env_rel,
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel ->
    (forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel),
        rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
    (forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), value_not_level_sort A ρ) ->
    (env_rel <~> per_ctx_env_cons_rel tail_rel (@head_rel) A A') ->
    EF Γ ▹{κ} A ≈ Γ' ▹{κ} A' ∈ per_ctx_env ↘ env_rel.
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

