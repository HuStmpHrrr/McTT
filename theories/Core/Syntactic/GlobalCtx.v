From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations Wk_Notations.

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
    are either terms or nested modules.  [ge_def b pv A B]: [b] says whether the
    definition is transparent, [pv] whether it is private, and [B] is [None] for
    an axiom.  [pv] is for the elaborator only: no judgment reads it, since
    whether a name may be written down has nothing to do with what it means.  [ge_mod Δ Φ]: the
    parameters [Δ] the nested module adds to the ones it is already under. *)
Inductive gentry : Set :=
| ge_def : bool -> bool -> typ -> option exp -> gentry
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
  | ge_def _ _ _ _ => True
  | ge_mod _ Φ => gm_canon Φ
  end
with gm_canon (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ' x E => gm_canon Φ' /\ gm_fresh x Φ' /\ ge_canon E
  end.

(** Resolution of a member chain to a definition, accumulating the parameters of
    the nested modules crossed on the way in, innermost first.

    What a nested module contains was checked with that module as the innermost
    frame, so each step out re-expresses it through [p_rel 0 [x]]: an index into
    the nested module becomes a member path through [x], and every other index
    moves in by one.  The parameters [Δ'] of [x] were checked in the enclosing
    frame already, so they are not opened.

    A later declaration shadows nothing — [gml_old] does not ask [x <> y], so
    determinism comes from [gm_canon] instead. *)
Inductive gm_lookup : gmod -> list string -> ctx -> gentry -> Prop :=
| gml_last :
  `( gm_ext Φ x (ge_def b pv A B) ∋ x :: nil ⇒ ⋅ ⍮ ge_def b pv A B )
(** Read out through the nested module [x], which is closed from here: its
    parameters [Δ'] become λ-bound, below those already collected, and its
    members are applied to them. *)
| gml_in :
  `( Φ' ∋ ip ⇒ Δ ⍮ ge_def b pv A B ->
     gm_ext Φ x (ge_mod Δ' Φ') ∋ x :: ip
       ⇒ Δ[close (p_rel 0 (x :: nil)) (List.length Δ')]ᵐ ++ Δ'
       ⍮ ge_def b pv A[ms_close (p_rel 0 (x :: nil)) (List.length Δ') (List.length Δ)]ᵐ
                  B[ms_close (p_rel 0 (x :: nil)) (List.length Δ') (List.length Δ)]ᵐ )
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

(** One [gdeps] is below another when everything filed in it is filed, the
    same, in the other: what filing more units, or merging, preserves. *)
Definition gds_sub (Θ Θ' : gdeps) : Prop :=
  forall fp U, gds_lookup Θ fp = Some U -> gds_lookup Θ' fp = Some U.

Notation "Θ ⊑ Θ'" := (gds_sub Θ Θ') (at level 70) : type_scope.

Lemma gds_sub_refl : forall Θ, gds_sub Θ Θ.
Proof. intros ? ? ? H; exact H. Qed.

Lemma gds_sub_trans : forall Θ1 Θ2 Θ3, gds_sub Θ1 Θ2 -> gds_sub Θ2 Θ3 -> gds_sub Θ1 Θ3.
Proof. intros * H12 H23 ? ? H; apply H23, H12, H. Qed.

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

    The modules open around the point being checked, innermost first.  Their
    members are not yet entries of anything, so they are named by [qu_rel], and
    their parameters are in scope as [$[n, k]]: frame [n], parameter [k]. *)
Definition gstack : Set := list gunit.

Definition gs_canon (Ξ : gstack) : Prop :=
  List.Forall (fun U => gm_canon (gu_mod U)) Ξ.

(** ** Resolution of a Path

    The levels and the stack are kept apart rather than bundled into one global
    context: they are read by different qualifiers, they grow differently, and
    well-formedness of each is relative to its own component.

    A definition is handed back generalized over *every* parameter in scope where
    it was declared: those of the nested modules on its member chain, then those
    of the frame it was found in and of every frame outside that.  Its type is
    therefore closed, which is what lets it be used anywhere, and what makes
    reading it out a renaming of paths and nothing more — no parameter of a
    module it is read out of is left free in it.

    For [qu_rel n] the definition sits in frame [n], so everything found is
    re-expressed at the use site by shifting [n] frames.  For [qu_abs fp] it sits
    in a filed unit, which was checked as the only frame of an empty stack. *)
Inductive gc_lookup (Θ : gdeps) (Ξ : gstack) : path -> ctx -> gentry -> Prop :=
(** A frame on the stack is open: its members are handed back as they are,
    moved [n] frames in. *)
| gcl_rel :
  `( List.nth_error Ξ n = Some U ->
     gu_mod U ∋ ip ⇒ Δ ⍮ ge_def b pv A B ->
     Θ ⍮ Ξ ∋ᵍ p_rel n ip ⇒ Δ[↑ₘ n]ᵐ ⍮ ge_def b pv A[↑ₘ n]ᵐ B[↑ₘ n]ᵐ )
(** A filed unit is closed: its parameters become λ-bound, below those of the
    nested modules on the way in. *)
| gcl_abs :
  `( gds_lookup Θ fp = Some U ->
     gu_mod U ∋ ip ⇒ Δ ⍮ ge_def b pv A B ->
     Θ ⍮ Ξ ∋ᵍ p_abs fp ip
       ⇒ Δ[close (p_abs fp nil) (List.length (gu_params U))]ᵐ ++ gu_params U
       ⍮ ge_def b pv A[ms_close (p_abs fp nil) (List.length (gu_params U)) (List.length Δ)]ᵐ
                  B[ms_close (p_abs fp nil) (List.length (gu_params U)) (List.length Δ)]ᵐ )
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
    (* the two that recurse agree by the induction hypothesis, and [gml_in]
       re-expresses the same definition the same way. *)
    try match goal with
        | IH : gm_canon ?Φ -> _, Hc : gm_canon ?Φ, H : ?Φ ∋ _ ⇒ _ ⍮ _ |- _ =>
            destruct (IH Hc _ _ H) as [-> Heq]; try injection Heq as -> -> ->
        end; subst; auto.
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

Lemma gd_lookup_app_inv : forall d d' fp U,
    gd_lookup (d ++ d') fp = Some U ->
    gd_lookup d fp = Some U \/ gd_lookup d' fp = Some U.
Proof.
  unfold gd_lookup; induction d as [| fV d IH]; simpl; intros * Heq;
    [ now right |].
  destruct (path_beq fp (fst fV)); [ now left | now apply IH ].
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
    | H1 : gu_mod ?U ∋ _ ⇒ _ ⍮ _, H2 : gu_mod ?U ∋ _ ⇒ _ ⍮ _ |- _ =>
        destruct (gm_lookup_det _ _ _ _ H1
                    ltac:(eauto using gs_canon_nth, gds_lookup_canon) _ _ H2) as [-> [= -> -> -> ->]]
    end;
    split; reflexivity.
Qed.

(** ** Resolution as a Function

    What evaluation uses: the newest entry of a name wins, which in a canonical
    context is the only one, so the function agrees with [gc_lookup]
    ([gc_resolve_sound], [gc_resolve_complete]). *)

(** A definition read out through the nested module [x] with parameters [Δ']. *)
Definition gm_resolve_in (x : string) (Δ' : ctx) (r : option (ctx * gentry)) : option (ctx * gentry) :=
  match r with
  | Some (Δ, ge_def b pv A B) =>
      Some (Δ[close (p_rel 0 (x :: nil)) (List.length Δ')]ᵐ ++ Δ',
            ge_def b pv A[ms_close (p_rel 0 (x :: nil)) (List.length Δ') (List.length Δ)]ᵐ
                     B[ms_close (p_rel 0 (x :: nil)) (List.length Δ') (List.length Δ)]ᵐ)
  | _ => None
  end.

Fixpoint gm_resolve (Φ : gmod) (ip : list string) : option (ctx * gentry) :=
  match Φ with
  | gm_nil => None
  | gm_ext Φ y E =>
      match ip with
      | x :: ip' =>
          if String.eqb x y
          then match ip', E with
               | nil, ge_def _ _ _ _ => Some (nil, E)
               | _ :: _, ge_mod Δ' Φ' => gm_resolve_in x Δ' (gm_resolve Φ' ip')
               | _, _ => gm_resolve Φ ip
               end
          else gm_resolve Φ ip
      | nil => None
      end
  end.

(** Reading a definition out of an open frame [n] frames out, and out of a
    filed unit. *)
Definition ge_read_rel (n : nat) (r : option (ctx * gentry)) : option (ctx * gentry) :=
  match r with
  | Some (Δ, ge_def b pv A B) => Some (Δ[↑ₘ n]ᵐ, ge_def b pv A[↑ₘ n]ᵐ B[↑ₘ n]ᵐ)
  | _ => None
  end.

Definition ge_read_abs (fp : list string) (T : ctx) (r : option (ctx * gentry)) : option (ctx * gentry) :=
  match r with
  | Some (Δ, ge_def b pv A B) =>
      Some (Δ[close (p_abs fp nil) (List.length T)]ᵐ ++ T,
            ge_def b pv A[ms_close (p_abs fp nil) (List.length T) (List.length Δ)]ᵐ
                     B[ms_close (p_abs fp nil) (List.length T) (List.length Δ)]ᵐ)
  | _ => None
  end.

Definition gc_resolve (Θ : gdeps) (Ξ : gstack) (p : path) : option (ctx * gentry) :=
  match p_qual p with
  | qu_rel n =>
      match List.nth_error Ξ n with
      | Some U => ge_read_rel n (gm_resolve (gu_mod U) (p_mems p))
      | None => None
      end
  | qu_abs fp =>
      match gds_lookup Θ fp with
      | Some U => ge_read_abs fp (gu_params U) (gm_resolve (gu_mod U) (p_mems p))
      | None => None
      end
  end.

Lemma gm_resolve_sound : forall Φ ip Δ E,
    gm_resolve Φ ip = Some (Δ, E) -> Φ ∋ ip ⇒ Δ ⍮ E.
Proof.
  fix IH 1; intros [| Φ y E] ip Δ E0 H; cbn in H; [ discriminate |].
  destruct ip as [| x ip']; [ discriminate |].
  destruct (String.eqb_spec x y) as [-> |]; [| apply gml_old; eapply IH; exact H ].
  destruct ip' as [| z ip''], E as [b A B | Δ' Φ'].
  - injection H as <- <-; apply gml_last.
  - apply gml_old; eapply IH; exact H.
  - apply gml_old; eapply IH; exact H.
  - unfold gm_resolve_in in H.
    destruct (gm_resolve Φ' (z :: ip'')) as [[Δ1 [b A B | ]] |] eqn:E1; try discriminate.
    injection H as <- <-; apply gml_in; eapply IH; exact E1.
Qed.

Lemma gc_resolve_sound : forall Θ Ξ p Δ E,
    gc_resolve Θ Ξ p = Some (Δ, E) -> Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ E.
Proof.
  intros Θ Ξ [[fp | n] ip] Δ E H; unfold gc_resolve in H; cbn [p_qual p_mems] in H.
  - destruct (gds_lookup Θ fp) as [U |] eqn:Hf; [| discriminate ].
    unfold ge_read_abs in H.
    destruct (gm_resolve (gu_mod U) ip) as [[Δ0 [b A B |]] |] eqn:E0; try discriminate.
    injection H as <- <-; econstructor; [ eassumption | apply gm_resolve_sound; exact E0 ].
  - destruct (List.nth_error Ξ n) as [U |] eqn:Hn; [| discriminate ].
    unfold ge_read_rel in H.
    destruct (gm_resolve (gu_mod U) ip) as [[Δ0 [b A B |]] |] eqn:E0; try discriminate.
    injection H as <- <-; econstructor; [ eassumption | apply gm_resolve_sound; exact E0 ].
Qed.

Lemma gm_resolve_complete : forall Φ ip Δ E,
    Φ ∋ ip ⇒ Δ ⍮ E -> gm_canon Φ -> gm_resolve Φ ip = Some (Δ, E).
Proof.
  induction 1; intros Hc; cbn in Hc |- *; destruct_all.
  - rewrite String.eqb_refl; reflexivity.
  - rewrite String.eqb_refl.
    destruct ip as [| z ip]; [ exfalso; exact (gm_lookup_nonnil _ _ _ _ H eq_refl) |].
    rewrite IHgm_lookup by assumption; reflexivity.
  (* an older entry: canonicity says the newer name is not its head *)
  - destruct ip as [| z ip]; [ exfalso; exact (gm_lookup_nonnil _ _ _ _ H eq_refl) |].
    destruct (String.eqb_spec z y) as [-> |]; [| auto ].
    exfalso; eapply (gm_fresh_no_lookup _ y); [ eassumption | eassumption | reflexivity ].
Qed.

Lemma gc_resolve_complete : forall Θ Ξ p Δ E,
    gs_canon Ξ -> gds_mods_canon Θ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ E -> gc_resolve Θ Ξ p = Some (Δ, E).
Proof.
  intros * Hs Hd Hlk; inversion Hlk; subst; unfold gc_resolve; cbn [p_qual p_mems].
  - match goal with Hn : List.nth_error _ _ = Some _ |- _ => rewrite Hn end.
    rewrite (gm_resolve_complete _ _ _ _ ltac:(eassumption) ltac:(eauto using gs_canon_nth));
      reflexivity.
  - match goal with Hn : gds_lookup _ _ = Some _ |- _ => rewrite Hn end.
    rewrite (gm_resolve_complete _ _ _ _ ltac:(eassumption) ltac:(eauto using gds_lookup_canon));
      reflexivity.
Qed.

(** ** Insertion Order

    A module is built one member at a time, nested members included, and each
    member was checked against the module as it stood just before it: that is
    the [gm_prefix] it was inserted at.  [gm_ins] is [gm_lookup] recording that
    prefix; it is what lets a property of every member be proved in the order
    the members were inserted, each from the ones before it. *)

Fixpoint ge_count (E : gentry) : nat :=
  match E with
  | ge_def _ _ _ _ => 1
  | ge_mod _ Φ => gm_count Φ
  end
with gm_count (Φ : gmod) : nat :=
  match Φ with
  | gm_nil => 0
  | gm_ext Φ' _ E => gm_count Φ' + ge_count E
  end.

(** [Φp] is [Φ] as it stood at some earlier point: later entries dropped, and
    the last nested module possibly still being filled. *)
Inductive gm_prefix : gmod -> gmod -> Prop :=
| gmp_refl : `( gm_prefix Φ Φ )
| gmp_old : `( gm_prefix Φp Φ -> gm_prefix Φp (Φ ⊳ y ↦ E) )
| gmp_in : `( gm_prefix Φp' Φ' -> gm_prefix (Φ ⊳ x ↦ ge_mod Δ' Φp') (Φ ⊳ x ↦ ge_mod Δ' Φ') ).

#[export]
Hint Constructors gm_prefix : mctt.

Inductive gm_ins : gmod -> gmod -> list string -> ctx -> gentry -> Prop :=
| gmi_last :
  `( gm_ins (Φ ⊳ x ↦ ge_def b pv A B) Φ (x :: nil) ⋅ (ge_def b pv A B) )
| gmi_in :
  `( gm_ins Φ' Φp' ip Δ (ge_def b pv A B) ->
     gm_ins (Φ ⊳ x ↦ ge_mod Δ' Φ') (Φ ⊳ x ↦ ge_mod Δ' Φp') (x :: ip)
       (Δ[close (p_rel 0 (x :: nil)) (List.length Δ')]ᵐ ++ Δ')
       (ge_def b pv A[ms_close (p_rel 0 (x :: nil)) (List.length Δ') (List.length Δ)]ᵐ
                 B[ms_close (p_rel 0 (x :: nil)) (List.length Δ') (List.length Δ)]ᵐ) )
| gmi_old :
  `( gm_ins Φ Φp ip Δ E ->
     gm_ins (Φ ⊳ y ↦ E') Φp ip Δ E ).

#[export]
Hint Constructors gm_ins : mctt.

Lemma gm_lookup_ins : forall Φ ip Δ E, Φ ∋ ip ⇒ Δ ⍮ E -> exists Φp, gm_ins Φ Φp ip Δ E.
Proof. induction 1; destruct_all; eexists; econstructor; eassumption. Qed.

Lemma gm_ins_prefix : forall Φ Φp ip Δ E, gm_ins Φ Φp ip Δ E -> gm_prefix Φp Φ.
Proof. induction 1; eauto with mctt. Qed.

Lemma gm_ins_count : forall Φ Φp ip Δ E, gm_ins Φ Φp ip Δ E -> gm_count Φp < gm_count Φ.
Proof.
  induction 1; cbn [gm_count ge_count]; lia.
Qed.

Lemma gm_prefix_lookup : forall Φp Φ ip Δ E, gm_prefix Φp Φ -> Φp ∋ ip ⇒ Δ ⍮ E -> Φ ∋ ip ⇒ Δ ⍮ E.
Proof.
  intros until 1; revert ip Δ E; induction H; intros * Hl; [ assumption | econstructor; auto |].
  inversion Hl; subst; [ eapply gml_in | eapply gml_old ]; auto.
Qed.

Lemma gm_prefix_ins : forall Φp Φ Φq ip Δ E,
    gm_prefix Φp Φ -> gm_ins Φp Φq ip Δ E -> gm_ins Φ Φq ip Δ E.
Proof.
  intros until 1; revert Φq ip Δ E; induction H; intros * Hi; [ assumption | econstructor; auto |].
  inversion Hi; subst; [ eapply gmi_in | eapply gmi_old ]; auto.
Qed.

Lemma gm_prefix_trans : forall Φ1 Φ2 Φ3, gm_prefix Φ1 Φ2 -> gm_prefix Φ2 Φ3 -> gm_prefix Φ1 Φ3.
Proof.
  intros * H12 H23; revert Φ1 H12; induction H23; intros; eauto with mctt.
  inversion H12; subst; eauto with mctt.
Qed.

(** ** Parameters as a Function

    What evaluation uses for [$[n, k]]: the [k]th parameter of frame [n],
    weakened past the ones after it, at the type [wf_param] gives it. *)
Fixpoint ctx_get (Γ : ctx) (k : nat) : option typ :=
  match Γ, k with
  | nil, _ => None
  | A :: _, 0 => Some A[↑]ʷ
  | _ :: Γ', S k' => option_map (fun T => T[↑]ʷ) (ctx_get Γ' k')
  end.

Definition gs_param (Ξ : gstack) (lp : lpath) : option typ :=
  match List.nth_error Ξ (lp_mod lp) with
  | Some U => option_map (fun T => T[↑ₘ (S (lp_mod lp))]ᵐ[sb_params (lp_mod lp)]) (ctx_get (gu_params U) (lp_param lp))
  | None => None
  end.

(** ** Transparent Global Contexts

    Every definition is transparent and has a body, and no open frame has
    parameters: then no global and no parameter is a neutral, which is what
    canonicity and consistency need.  A filed unit or a nested module may have
    parameters, since its members are resolved abstracted over them. *)

Fixpoint ge_transparent (E : gentry) : Prop :=
  match E with
  | ge_def b _ _ B => b = true /\ B <> None
  | ge_mod _ Φ => gm_transparent Φ
  end
with gm_transparent (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ _ E => gm_transparent Φ /\ ge_transparent E
  end.

Definition gc_transparent (Θ : gdeps) (Ξ : gstack) : Prop :=
  (forall fp U, List.In (fp, U) (List.concat Θ) -> gm_transparent (gu_mod U)) /\
  (forall U, List.In U Ξ -> gu_params U = nil /\ gm_transparent (gu_mod U)).

Lemma gm_transparent_lookup' : forall Φ ip Δ E,
    gm_transparent Φ -> Φ ∋ ip ⇒ Δ ⍮ E -> ge_transparent E.
Proof.
  induction 2; cbn in *; destruct_all; auto.
  destruct (IHgm_lookup ltac:(assumption)) as [-> HB].
  split; [ reflexivity | destruct B; cbn in *; congruence ].
Qed.

Lemma gm_transparent_lookup : forall Φ ip Δ b pv A B,
    gm_transparent Φ ->
    Φ ∋ ip ⇒ Δ ⍮ ge_def b pv A B ->
    b = true /\ B <> None.
Proof. intros * HΦ Hl; exact (gm_transparent_lookup' _ _ _ _ HΦ Hl). Qed.

Lemma gc_transparent_lookup : forall Θ Ξ p Δ b pv A B,
    gc_transparent Θ Ξ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
    b = true /\ B <> None.
Proof.
  intros * [HΘ HΞ] Hl; inversion Hl; subst;
    match goal with Hm : gu_mod ?U ∋ _ ⇒ _ ⍮ ge_def _ _ _ ?B0 |- _ =>
      assert (HU : gm_transparent (gu_mod U))
        by first [ eapply HΞ, List.nth_error_In; eassumption
                 | eapply HΘ, gd_lookup_in; eassumption ];
      destruct (gm_transparent_lookup _ _ _ _ _ _ _ HU Hm) as [-> HB];
      split; [ reflexivity | destruct B0; cbn in *; congruence ]
    end.
Qed.

Lemma gc_transparent_param : forall Θ Ξ lp, gc_transparent Θ Ξ -> gs_param Ξ lp = None.
Proof.
  intros * [_ HΞ]; unfold gs_param.
  destruct (List.nth_error Ξ (lp_mod lp)) as [U |] eqn:Hn; [| reflexivity ].
  destruct (HΞ _ (List.nth_error_In _ _ Hn)) as [-> _]; reflexivity.
Qed.

(** ** A Fixed Global Context

    The semantic model and the two metatheorems about NbE are stated for one
    global context at a time.  Found by instance resolution, it keeps their
    judgments in the short forms of [Core.Semantic.Fixed]. *)
Class GCtx : Set := gc_mk
  { gc_deps : gdeps
  ; gc_stack : gstack }.
