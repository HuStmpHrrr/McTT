From Stdlib Require Import Lia PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.Definitions.
Import Domain_Notations Fixed_Notations.

Ltac destruct_rel_by_assumption in_rel H :=
  repeat
    match goal with
    | H' : Dom ?c ≈ ?c' ∈ ?in_rel0 |- _ =>
        unify in_rel0 in_rel;
        lazymatch type of (H _ _ H') with
        | rel_mod_eval _ _ _ _ _ _ => let Hr := fresh "Hr" in pose proof (H _ _ H') as Hr; destruct_anon Hr
        | rel_typ _ _ _ _ _ _ => let Hr := fresh "Hr" in pose proof (H _ _ H') as Hr; destruct_anon Hr
        | rel_elem _ _ _ _ _ => let Hr := fresh "Hr" in pose proof (H _ _ H') as Hr; destruct_anon Hr
        | rel_mod_app _ _ _ _ _ => let Hr := fresh "Hr" in pose proof (H _ _ H') as Hr; destruct_anon Hr
        (** The bodies of a definition, unless its type is a proposition:
            one case each *)
        | rel_typ_propositional _ _ \/ rel_elem _ _ _ _ _ =>
            let Hr := fresh "Hr" in destruct (H _ _ H') as [Hr | Hr]; [| destruct_anon Hr ]
        | _ => destruct (H _ _ H') as []
        end;
        destruct_all;
        mark_with H' 1
    end;
  unmark_all_with 1.
Ltac destruct_rel_mod_eval :=
  repeat
    match goal with
    | H : (forall c c' (equiv_c_c' : Dom c ≈ c' ∈ ?in_rel), rel_mod_eval _ _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    | H : rel_mod_eval _ _ _ _ _ _ |- _ =>
        destruct_anon H
    end;
  unmark_all.
Ltac destruct_rel_mod_app :=
  repeat
    match goal with
    | H : (forall c c' (equiv_c_c' : Dom c ≈ c' ∈ ?in_rel), rel_mod_app _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    | H : rel_mod_app _ _ _ _ _ |- _ =>
        destruct_anon H
    end;
  unmark_all.
Ltac destruct_rel_typ :=
  repeat
    match goal with
    | H : (forall c c' (equiv_c_c' : Dom c ≈ c' ∈ ?in_rel), rel_typ _ _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    | H : rel_typ _ _ _ _ _ _ |- _ =>
        destruct_anon H
    (** The bodies of a definition entry come with the types. *)
    | H : (forall c c' (equiv_c_c' : Dom c ≈ c' ∈ ?in_rel), rel_elem _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    | H : rel_elem _ _ _ _ _ |- _ =>
        destruct_anon H
    | H : (forall c c' (equiv_c_c' : Dom c ≈ c' ∈ ?in_rel), rel_typ_propositional _ _ \/ rel_elem _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    end;
  unmark_all.

(** Helper tactics for the universe/element PER. *)

(** State the universes below a level, [per_univ_below i j], by
    [per_univ_below_spec], wherever [universe_index_lt j i] is known, or
    [j] is small and [i] large ([universe_index_large]). *)
Ltac rewrite_per_univ_below :=
  repeat match goal with
    | H : context [per_univ_below ?i ?j] |- _ =>
        rewrite (per_univ_below_spec i j) in H
          by first [ solve_universe_index | apply universe_index_large_above_small; assumption ]
    | |- context [per_univ_below ?i ?j] =>
        rewrite (per_univ_below_spec i j)
          by first [ solve_universe_index | apply universe_index_large_above_small; assumption ]
    end.

(** A case of an inversion whose kind premise is false of a value with a
    known head: a proposition clause at a head of an evaluated kind, the
    neutral clause at a neutral proposition, neutrals of different kinds. *)
Ltac clear_wrong_kind :=
  repeat match goal with Hp : per_prop _ _ |- _ => destruct Hp end;
  match goal with
  | H1 : domain_kind ?x = ak_propositional, H2 : evaluated_kind (domain_kind ?x) |- _ =>
      rewrite H1 in H2; inversion H2
  | H1 : domain_kind ?y = ak_propositional, E : domain_kind ?x = domain_kind ?y, H2 : evaluated_kind (domain_kind ?x) |- _ =>
      rewrite E, H1 in H2; inversion H2
  | H1 : domain_kind ?y = ak_propositional, E : domain_kind ?y = domain_kind ?x, H2 : evaluated_kind (domain_kind ?x) |- _ =>
      rewrite <- E, H1 in H2; inversion H2
  | H1 : domain_kind ?x = ?k1, H2 : domain_kind ?x = ?k2 |- _ =>
      assert_fails constr_eq k1 k2; rewrite H1 in H2; discriminate H2
  | Hr : domain_kind _ = _ |- _ =>
      progress cbn in Hr;
      first [ discriminate Hr
            | subst; match goal with He : evaluated_kind ak_propositional |- _ => inversion He end ]
  | Hr : evaluated_kind (domain_kind _) |- _ => progress cbn in Hr; solve [ inversion Hr ]
  end.

Ltac basic_invert_per_univ_elem H :=
  progress simp per_univ_elem in H;
  unmark_vars;
  dependent destruction H;
  try solve [ clear_wrong_kind ];
  rewrite_per_univ_below;
  try rewrite <- per_univ_elem_equation_1 in *.

Ltac basic_per_univ_elem_econstructor :=
  progress simp per_univ_elem;
  econstructor;
  rewrite_per_univ_below;
  try rewrite <- per_univ_elem_equation_1 in *.
