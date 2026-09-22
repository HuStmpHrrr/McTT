From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations.

Generalizable All Variables.

(** * Global Contexts

    Two levels, spelled differently in the surface language and represented
    differently here.  [X::Y::Z] names a *unit*, and units are not declared
    inside one another, so the [::] level is flat.  [X.W] names an internal
    module of one unit, and internal modules nest inside that unit's
    declarations, so the [.] level is a module.

    The [::] level is not one flat list but a list of *dependency levels*: a
    unit's level is [1 + max] of the levels of the units it imports, [0] when it
    imports nothing.  Levels are most recent first, as frames are in a [gstack],
    so a unit is filed above exactly the levels it may depend on.  The structure
    is what grants cycle freedom, so nothing here states it as a proposition; the
    command layer files a unit at the level its imports force.

    A member's type and body are stored *open*: they live in the telescope of the
    modules enclosing them, and resolution accumulates that telescope so that a
    use site can generalize with [ctx_pi]/[ctx_fn].  The telescope in [ge_mod] is
    therefore needed to read a member, not only to type a module application. *)

Reserved Notation "Φ ∋ ip ⇒ Δ ⍮ E" (at level 70, ip at level 69, Δ at level 69, E at level 69).
Reserved Notation "Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ E" (at level 70, Ξ at level 69, p at level 69, Δ at level 69, E at level 69).

(** ** Modules

    A module is a sequence of definitions, in declaration order, whose entries
    are either terms or nested modules.  [ge_def b A B]: [b] says whether the
    definition is transparent, and [B] is [None] for an axiom.  [ge_mod Δ Φ]: the
    parameters [Δ] the nested module adds to the ones it is already under. *)
Inductive gentry : Set :=
| ge_def : bool -> typ -> option exp -> gentry
| ge_mod : ctx -> gmod -> gentry
with gmod : Set :=
| gm_nil : gmod
| gm_ext : gmod -> string -> gentry -> gmod.

Module GlobalCtx_Notations.

  Notation "⋄" := gm_nil.
  Notation "Φ ⊳ x ↦ E" := (gm_ext Φ x E) (at level 50, x at level 0).

End GlobalCtx_Notations.

Import GlobalCtx_Notations.

(** The names [Φ] declares, outermost last, and a name not among them.  As for
    [gd_fresh], freshness is a non-membership; [gm_fresh_ext] is how the one
    interesting case is taken apart. *)
Fixpoint gm_names (Φ : gmod) : list string :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ' x _ => x :: gm_names Φ'
  end.

Definition gm_fresh (x : string) (Φ : gmod) : Prop :=
  ~ List.In x (gm_names Φ).

Lemma gm_fresh_ext : forall x Φ y E,
    gm_fresh x (gm_ext Φ y E) <-> x <> y /\ gm_fresh x Φ.
Proof.
  unfold gm_fresh; simpl; intros *; split; [ intuition | intuition congruence ].
Qed.

(** Names are unique, at every depth: the condition resolution's determinism is
    stated with.  It is a consequence of well-formedness ([wf_gmod_canon]), not a
    separate obligation. *)
Fixpoint ge_canon (E : gentry) : Prop :=
  match E with
  | ge_def _ _ _ => True
  | ge_mod _ Φ => gm_canon Φ
  end
with gm_canon (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ' x E => gm_canon Φ' /\ gm_fresh x Φ' /\ ge_canon E
  end.

(** Resolution of a member chain, accumulating the telescope crossed on the way
    in.  A later declaration shadows nothing — [gml_old] does not ask [x <> y],
    so determinism comes from [gm_canon] instead. *)
Inductive gm_lookup : gmod -> list string -> ctx -> gentry -> Prop :=
| gml_last :
  `( gm_ext Φ x E ∋ x :: nil ⇒ ⋅ ⍮ E )
| gml_in :
  `( Φ' ∋ ip ⇒ Δ ⍮ E ->
     gm_ext Φ x (ge_mod Δ' Φ') ∋ x :: ip ⇒ Δ ++ Δ' ⍮ E )
| gml_old :
  `( Φ ∋ ip ⇒ Δ ⍮ E ->
     gm_ext Φ y E' ∋ ip ⇒ Δ ⍮ E )
where "Φ ∋ ip ⇒ Δ ⍮ E" := (gm_lookup Φ ip Δ E) : type_scope.

#[export]
Hint Constructors gm_lookup : mctt.

(** ** Units

    A unit is a parameterized module in full: the parameters it abstracts over,
    and the module it declares.  Units do not nest. *)
Record gunit : Set := gu_mk
  { gu_params : ctx
  ; gu_mod : gmod }.

Definition path_eq_dec := List.list_eq_dec String.string_dec.

Definition path_beq (fp fq : list string) : bool :=
  if path_eq_dec fp fq then true else false.

(** ** Dependency Levels

    One [gdep] is the units of a single level, keyed by absolute path; [gdeps] is
    the levels, highest first, so that consing a level files it above the ones it
    depends on. *)
Definition gdep : Set := list (list string * gunit).
Definition gdeps : Set := list gdep.

Definition gd_lookup (d : gdep) (fp : list string) : option gunit :=
  option_map snd (List.find (fun fU => path_beq fp (fst fU)) d).

(** Resolution across the levels.  A function, not a relation: the levels are
    searched in order, so a path resolves at most one way whatever the data
    looks like.  Searching them in order is searching their concatenation, and
    the level is not resolution's business anyway — a use site of [a_glob] reads
    the unit and nothing else. *)
Definition gds_lookup (Θ : gdeps) (fp : list string) : option gunit :=
  gd_lookup (List.concat Θ) fp.

(** A path not yet filed in one level, and one not yet filed at any level.  As
    for [gm_fresh], these are premises of the rules that file a unit, so name
    uniqueness across the whole of [gdeps] is part of well-formedness.

    Stated as a non-membership of the keys, in the same shape [gds_lookup] has: a
    level is searched as a list of pairs, and the levels as their concatenation,
    so the stdlib's [in_map_iff]/[in_app_iff]/[in_concat] are what these are
    reasoned about with. *)
Definition gd_fresh (fp : list string) (d : gdep) : Prop :=
  ~ List.In fp (List.map fst d).

Definition gds_fresh (fp : list string) (Θ : gdeps) : Prop :=
  gd_fresh fp (List.concat Θ).

(** Modules are canonical, pointwise; as for [gm_canon], a consequence of
    well-formedness ([wf_gdeps_canon]) rather than an obligation. *)
Definition gds_mods_canon (Θ : gdeps) : Prop :=
  List.Forall (List.Forall (fun fU => gm_canon (gu_mod (snd fU)))) Θ.

(** ** The Definition Stack

    The unit being elaborated, innermost frame first: its members are not yet
    entries of anything, so they are named by [qu_rel].  A frame is a [gunit] in
    the same sense a filed one is — its parameters are its *whole* telescope, so
    entering a parameterized module pushes a frame recording the accumulated
    parameters rather than only the ones it adds.  Nothing accumulates across
    frames here, which is what makes [qu_rel] and [qu_abs] read a unit the same
    way. *)
Definition gstack : Set := list gunit.

Definition gs_canon (Ξ : gstack) : Prop :=
  List.Forall (fun U => gm_canon (gu_mod U)) Ξ.

(** ** Resolution of a Path

    The levels and the stack are kept apart rather than bundled into one global
    context: they are read by different qualifiers, they grow differently, and
    well-formedness of each is relative to its own component.

    The two qualifiers reach a [gunit] differently and then read the member chain
    the same way.  The telescope handed back is the one the entry is well formed
    in, and it is the unit's own parameters in both cases: a unit is checked in
    the empty telescope whether it was filed or is still open. *)
Inductive gc_lookup (Θ : gdeps) (Ξ : gstack) : path -> ctx -> gentry -> Prop :=
| gcl_rel :
  `( List.nth_error Ξ n = Some U ->
     gu_mod U ∋ ip ⇒ Δ ⍮ E ->
     Θ ⍮ Ξ ∋ᵍ p_rel n ip ⇒ Δ ++ gu_params U ⍮ E )
| gcl_abs :
  `( gds_lookup Θ fp = Some U ->
     gu_mod U ∋ ip ⇒ Δ ⍮ E ->
     Θ ⍮ Ξ ∋ᵍ p_abs fp ip ⇒ Δ ++ gu_params U ⍮ E )
where "Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ E" := (gc_lookup Θ Ξ p Δ E) : type_scope.

#[export]
Hint Constructors gc_lookup : mctt.

(** [p_abs]/[p_rel] are record literals, so inverting a rule keyed on one yields
    equations about the fields; this reduces them to equations about the parts. *)
Ltac path_inj :=
  repeat match goal with
    | H : {| p_qual := _; p_mems := _ |} = {| p_qual := _; p_mems := _ |} |- _ =>
        injection H as ? ?; subst
    | H : qu_abs _ = qu_abs _ |- _ => injection H as ?; subst
    | H : qu_rel _ = qu_rel _ |- _ => injection H as ?; subst
    | H : qu_abs _ = qu_rel _ |- _ => discriminate H
    | H : qu_rel _ = qu_abs _ |- _ => discriminate H
    end.

(** ** Basic Facts about Resolution *)

(** No rule produces the empty chain, which is how [gml_last] and [gml_in] stay
    apart: [x] and [x.ip] cannot both resolve. *)
Lemma gm_lookup_nonnil : forall Φ ip Δ E,
    Φ ∋ ip ⇒ Δ ⍮ E ->
    ip <> nil.
Proof.
  induction 1; congruence.
Qed.

Lemma gm_fresh_no_lookup : forall Φ x Δ E ip,
    gm_fresh x Φ ->
    Φ ∋ ip ⇒ Δ ⍮ E ->
    List.hd_error ip <> Some x.
Proof.
  intros * Hfresh Hlk; induction Hlk;
    apply gm_fresh_ext in Hfresh as [? ?]; simpl;
    solve [congruence | eauto].
Qed.

Lemma gm_lookup_det : forall Φ ip Δ E,
    Φ ∋ ip ⇒ Δ ⍮ E ->
    gm_canon Φ ->
    forall Δ' E', Φ ∋ ip ⇒ Δ' ⍮ E' -> Δ = Δ' /\ E = E'.
Proof.
  induction 1; intros Hcanon * Hlk; simpl in Hcanon; destruct_all;
    inversion Hlk; subst;
    (* [x] against [x.ip] would need the inner chain to be empty; a lookup that
       skipped a declared name contradicts its freshness. *)
    try solve [exfalso;
               match goal with
               | H : _ ∋ nil ⇒ _ ⍮ _ |- _ => exact (gm_lookup_nonnil _ _ _ _ H eq_refl)
               end];
    try solve [exfalso;
               match goal with
               | Hf : gm_fresh ?x _, H : _ ∋ _ ⇒ _ ⍮ _ |- _ =>
                   apply (gm_fresh_no_lookup _ x _ _ _ Hf H); reflexivity
               end];
    (* the two that recurse agree by the induction hypothesis; the other side's
       lookup is the one whose entry the goal compares against. *)
    try match goal with
        | H : _ ∋ _ ⇒ _ ⍮ ?E0 |- _ /\ _ = ?E0 =>
            destruct (IHgm_lookup ltac:(eassumption) _ _ H) as [-> ->]
        end;
    split; reflexivity.
Qed.

Corollary gm_lookup_det_tele : forall Φ ip Δ E Δ' E',
    gm_canon Φ ->
    Φ ∋ ip ⇒ Δ ⍮ E ->
    Φ ∋ ip ⇒ Δ' ⍮ E' ->
    Δ = Δ'.
Proof.
  intros * Hc H1 H2; destruct (gm_lookup_det _ _ _ _ H1 Hc _ _ H2); assumption.
Qed.

Corollary gm_lookup_det_entry : forall Φ ip Δ E Δ' E',
    gm_canon Φ ->
    Φ ∋ ip ⇒ Δ ⍮ E ->
    Φ ∋ ip ⇒ Δ' ⍮ E' ->
    E = E'.
Proof.
  intros * Hc H1 H2; destruct (gm_lookup_det _ _ _ _ H1 Hc _ _ H2); assumption.
Qed.

Lemma gs_canon_nth : forall Ξ n U,
    gs_canon Ξ ->
    List.nth_error Ξ n = Some U ->
    gm_canon (gu_mod U).
Proof.
  unfold gs_canon; intros * HΞ; induction HΞ in n |- *; intros Hn;
    [ destruct n; discriminate |].
  destruct n; simpl in Hn; [ injection Hn as -> |]; eauto.
Qed.

Lemma gd_lookup_in : forall d fp U,
    gd_lookup d fp = Some U ->
    List.In (fp, U) d.
Proof.
  unfold gd_lookup, path_beq; intros * Heq.
  destruct (List.find _ d) as [[fq V] |] eqn:Hf; [| discriminate ].
  injection Heq as <-; apply List.find_some in Hf as [Hin Hb]; simpl in Hb.
  destruct (path_eq_dec fp fq) as [<- |]; [ assumption | discriminate ].
Qed.

Lemma gds_lookup_in : forall Θ fp U,
    gds_lookup Θ fp = Some U ->
    exists d, List.In d Θ /\ List.In (fp, U) d.
Proof.
  unfold gds_lookup; intros * Heq.
  apply (proj1 (List.in_concat _ _)), gd_lookup_in, Heq.
Qed.

Lemma gds_lookup_canon : forall Θ fp U,
    gds_mods_canon Θ ->
    gds_lookup Θ fp = Some U ->
    gm_canon (gu_mod U).
Proof.
  unfold gds_mods_canon; intros * Hcanon Heq.
  destruct (gds_lookup_in _ _ _ Heq) as [d [Hd Hin]].
  rewrite List.Forall_forall in Hcanon; specialize (Hcanon _ Hd).
  rewrite List.Forall_forall in Hcanon; exact (Hcanon _ Hin).
Qed.

(** ** Freshness and Growth of the Levels

    [List.find] returns the *first* match, so a hit in a prefix is the same hit
    in the whole: filing more levels never changes what an already filed path
    resolves to.  This is what lets a unit checked against the levels below it be
    used in the full context. *)

Lemma gd_lookup_app : forall d d' fp U,
    gd_lookup d fp = Some U ->
    gd_lookup (d ++ d') fp = Some U.
Proof.
  unfold gd_lookup; induction d as [| fV d IH]; simpl; intros * Heq;
    [ discriminate |].
  destruct (path_beq fp (fst fV)); [ assumption | now apply IH ].
Qed.

Lemma gd_lookup_app_inv : forall d d' fp U,
    gd_lookup (d ++ d') fp = Some U ->
    gd_lookup d fp = Some U \/ gd_lookup d' fp = Some U.
Proof.
  unfold gd_lookup; induction d as [| fV d IH]; simpl; intros * Heq;
    [ now right |].
  destruct (path_beq fp (fst fV)); [ now left | now apply IH ].
Qed.

Lemma gds_lookup_app : forall Θ Θ' fp U,
    gds_lookup Θ fp = Some U ->
    gds_lookup (Θ ++ Θ') fp = Some U.
Proof.
  unfold gds_lookup; intros *; rewrite List.concat_app; apply gd_lookup_app.
Qed.

Lemma gd_fresh_app : forall fp d d',
    gd_fresh fp (d ++ d') <-> gd_fresh fp d /\ gd_fresh fp d'.
Proof.
  unfold gd_fresh; intros *; rewrite List.map_app, List.in_app_iff; tauto.
Qed.

Lemma gds_fresh_app : forall fp Θ Θ',
    gds_fresh fp (Θ ++ Θ') <-> gds_fresh fp Θ /\ gds_fresh fp Θ'.
Proof.
  unfold gds_fresh; intros *; rewrite List.concat_app; apply gd_fresh_app.
Qed.

(** A fresh path resolves nowhere, which is how freshness bounds [gd_lookup]. *)
Lemma gd_fresh_no_lookup : forall fp d,
    gd_fresh fp d ->
    gd_lookup d fp = None.
Proof.
  unfold gd_fresh, gd_lookup, path_beq; intros * Hfresh.
  destruct (List.find _ d) as [[fq V] |] eqn:Hf; [| reflexivity ].
  exfalso; apply List.find_some in Hf as [Hin Hb]; simpl in Hb.
  destruct (path_eq_dec fp fq) as [<- |]; [| discriminate ].
  exact (Hfresh (List.in_map fst _ _ Hin)).
Qed.

Corollary gds_fresh_no_lookup : forall fp Θ,
    gds_fresh fp Θ ->
    gds_lookup Θ fp = None.
Proof.
  unfold gds_fresh, gds_lookup; auto using gd_fresh_no_lookup.
Qed.

Corollary gc_lookup_det : forall Θ Ξ p Δ E Δ' E',
    gs_canon Ξ ->
    gds_mods_canon Θ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ E ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ' ⍮ E' ->
    Δ = Δ' /\ E = E'.
Proof.
  intros * Hs Hd Hlk Hlk'; inversion Hlk; inversion Hlk'; subst; path_inj;
    [ match goal with
      | H : List.nth_error _ _ = Some _, H' : List.nth_error _ _ = Some _ |- _ =>
          rewrite H in H'; injection H' as <-
      end
    | match goal with
      | H : gds_lookup _ _ = Some _, H' : gds_lookup _ _ = Some _ |- _ =>
          rewrite H in H'; injection H' as <-
      end ];
    match goal with
    | H1 : _ ∋ _ ⇒ _ ⍮ ?A, H2 : _ ∋ _ ⇒ _ ⍮ ?B |- _ /\ ?A = ?B =>
        destruct (gm_lookup_det _ _ _ _ H1
                    ltac:(eauto using gs_canon_nth, gds_lookup_canon) _ _ H2) as [-> ->]
    end;
    split; reflexivity.
Qed.
