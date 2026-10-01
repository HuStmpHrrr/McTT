From Stdlib Require Import Lia List String PeanoNat.

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

    *Every name is absolute, and every entry is stored as it is used.*  An open
    frame is named by its level ([qu_rel L], [$[L, k]]), which pushing a frame
    inside it does not change, so a member of an open frame is stored as it was
    checked and read back as it is.  Closing a frame — when a nested module
    ends, or when a unit is filed — is the one place a member changes form: its
    frame's parameters become λ-bound and the frame's members are read out of
    the closed module.  That is done *once*, by the judgments, to what they
    store ([gm_close], [gu_close]); so a closed module holds its members
    generalized and closed, and resolution only looks them up. *)

Reserved Notation "Φ ∋ ip ⇒ E" (at level 70, ip at level 69, E at level 69).
Reserved Notation "Θ ⍮ Ξ ∋ᵍ p ⇒ E" (at level 70, Ξ at level 69, p at level 69, E at level 69).

(** ** Modules

    A module is a sequence of definitions, in declaration order, whose entries
    are either terms or nested modules.  [ge_def b pv A B]: [b] says whether the
    definition is transparent, [pv] whether it is private, and [B] is [None] for
    an axiom.  [pv] is for the elaborator only: no judgment reads it, since
    whether a name may be written down has nothing to do with what it means.
    [ge_mod Δ Φ]: a nested module, *closed*: [Φ]'s members are generalized over
    the parameters [Δ] the module was declared with (which are recorded, but
    read by nothing). *)
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

(** Resolution of a member chain to a definition: a lookup and nothing more.
    A nested module is closed, so what it holds is already what its members
    mean from outside it.

    A later declaration shadows nothing — [gml_old] does not ask [x <> y], so
    determinism comes from [gm_canon] instead. *)
Inductive gm_lookup : gmod -> list string -> gentry -> Prop :=
| gml_last :
  `( gm_ext Φ x (ge_def b pv A B) ∋ x :: nil ⇒ ge_def b pv A B )
| gml_in :
  `( Φ' ∋ ip ⇒ ge_def b pv A B ->
     gm_ext Φ x (ge_mod Δ' Φ') ∋ x :: ip ⇒ ge_def b pv A B )
| gml_old :
  `( Φ ∋ ip ⇒ E ->
     gm_ext Φ y E' ∋ ip ⇒ E )
where "Φ ∋ ip ⇒ E" := (gm_lookup Φ ip E) : type_scope.

#[export]
Hint Constructors gm_lookup : mctt.

(** ** Units and Frames

    A unit is a parameterized module in full: the parameters it abstracts over,
    and the module it declares.  Units do not nest.  The same record is a frame
    of the definition stack, where the parameters are in scope as [$[L, k]];
    [gu_ptys] then holds their types as the parameters themselves see them
    (the [k]-th mentioning the parameters before it as [$[L, _]]), which is
    what evaluating a parameter reads.  It is determined by [gu_params] and the
    frame's level ([ctx_ptys]), and the judgments ask exactly that; a filed
    unit has no use for it. *)
Record gunit : Set := gu_mk
  { gu_params : ctx
  ; gu_ptys : list typ
  ; gu_mod : gmod }.

Definition path_eq_dec := List.list_eq_dec String.string_dec.

Definition path_beq (fp fq : list string) : bool :=
  if path_eq_dec fp fq then true else false.

(** ** Dependency Levels

    One [gdep] is the units of a single level, keyed by absolute path; [gdeps] is
    the levels, highest first, so that consing a level files it above the ones it
    depends on.  A filed unit is closed ([gu_close]). *)
Definition gdep : Set := list (list string * gunit).
Definition gdeps : Set := list gdep.

Definition gd_lookup (d : gdep) (fp : list string) : option gunit :=
  option_map snd (List.find (fun fU => path_beq fp (fst fU)) d).

(** Resolution across the levels.  A function, not a relation: the levels are
    searched in order, so a path resolves at most one way whatever the data
    looks like. *)
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

(** A path not yet filed in one level, and one not yet filed at any level. *)
Definition gd_fresh (fp : list string) (d : gdep) : Prop :=
  ~ List.In fp (List.map fst d).

Definition gds_fresh (fp : list string) (Θ : gdeps) : Prop :=
  gd_fresh fp (List.concat Θ).

(** Modules are canonical, pointwise; as for [gm_canon], a consequence of
    well-formedness ([wf_gdeps_canon]) rather than an obligation. *)
Definition gds_mods_canon (Θ : gdeps) : Prop :=
  List.Forall (List.Forall (fun fU => gm_canon (gu_mod (snd fU)))) Θ.

(** ** The Definition Stack

    The modules open around the point being checked, innermost first, and
    *addressed by level*: the frame at level [L] is the [L]-th from the
    outside, so pushing a frame changes no frame's name. *)
Definition gstack : Set := list gunit.

Definition gs_canon (Ξ : gstack) : Prop :=
  List.Forall (fun U => gm_canon (gu_mod U)) Ξ.

Definition gs_frame (Ξ : gstack) (L : nat) : option gunit := List.nth_error (List.rev Ξ) L.

Lemma gs_frame_lt : forall Ξ L U, gs_frame Ξ L = Some U -> L < List.length Ξ.
Proof.
  unfold gs_frame; intros * H.
  rewrite <- List.length_rev; apply List.nth_error_Some; congruence.
Qed.

Lemma gs_frame_top : forall U Ξ, gs_frame (U :: Ξ) (List.length Ξ) = Some U.
Proof.
  unfold gs_frame; intros; cbn.
  rewrite List.nth_error_app2 by (rewrite List.length_rev; lia).
  rewrite List.length_rev, Nat.sub_diag; reflexivity.
Qed.

Lemma gs_frame_push : forall U Ξ L, L < List.length Ξ -> gs_frame (U :: Ξ) L = gs_frame Ξ L.
Proof.
  unfold gs_frame; intros; cbn.
  rewrite List.nth_error_app1 by (rewrite List.length_rev; lia); reflexivity.
Qed.

Lemma gs_frame_push_some : forall U Ξ L V, gs_frame Ξ L = Some V -> gs_frame (U :: Ξ) L = Some V.
Proof.
  intros * H; rewrite gs_frame_push; [ exact H | eapply gs_frame_lt; exact H ].
Qed.

Lemma gs_frame_cons_inv : forall U Ξ L V,
    gs_frame (U :: Ξ) L = Some V ->
    (L = List.length Ξ /\ V = U) \/ (L < List.length Ξ /\ gs_frame Ξ L = Some V).
Proof.
  intros * H.
  pose proof (gs_frame_lt _ _ _ H) as Hlt; cbn in Hlt.
  destruct (Nat.eq_dec L (List.length Ξ)) as [-> |].
  - rewrite gs_frame_top in H; injection H as <-; left; auto.
  - right; rewrite gs_frame_push in H by lia; split; [ lia | exact H ].
Qed.

Lemma gs_frame_In : forall Ξ L U, gs_frame Ξ L = Some U -> List.In U Ξ.
Proof.
  unfold gs_frame; intros * H; apply List.in_rev, List.nth_error_In with (n := L); exact H.
Qed.

(** The frames below level [L] are those of a suffix of the stack. *)
Lemma gs_frame_app : forall Ξa Ξb L, L < List.length Ξb -> gs_frame (Ξa ++ Ξb) L = gs_frame Ξb L.
Proof.
  unfold gs_frame; intros; rewrite List.rev_app_distr, List.nth_error_app1
    by (rewrite List.length_rev; lia); reflexivity.
Qed.

Lemma gs_frame_split : forall Ξ L U,
    gs_frame Ξ L = Some U ->
    exists Ξa Ξb, Ξ = Ξa ++ U :: Ξb /\ List.length Ξb = L.
Proof.
  unfold gs_frame; intros * H.
  destruct (List.nth_error_split _ _ H) as (Ra & Rb & HR & Hlen).
  exists (List.rev Rb), (List.rev Ra); split.
  - rewrite <- (List.rev_involutive Ξ), HR, List.rev_app_distr; cbn; rewrite <- List.app_assoc; reflexivity.
  - rewrite List.length_rev; exact Hlen.
Qed.

(** ** Resolution of a Path

    The levels and the stack are kept apart rather than bundled into one global
    context: they are read by different qualifiers, they grow differently, and
    well-formedness of each is relative to its own component.  Either way the
    entry found is handed back as it is stored. *)
Inductive gc_lookup (Θ : gdeps) (Ξ : gstack) : path -> gentry -> Prop :=
| gcl_rel :
  `( gs_frame Ξ n = Some U ->
     gu_mod U ∋ ip ⇒ ge_def b pv A B ->
     Θ ⍮ Ξ ∋ᵍ p_rel n ip ⇒ ge_def b pv A B )
| gcl_abs :
  `( gds_lookup Θ fp = Some U ->
     gu_mod U ∋ ip ⇒ ge_def b pv A B ->
     Θ ⍮ Ξ ∋ᵍ p_abs fp ip ⇒ ge_def b pv A B )
where "Θ ⍮ Ξ ∋ᵍ p ⇒ E" := (gc_lookup Θ Ξ p E) : type_scope.

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
Lemma gm_lookup_nonnil : forall Φ ip E,
    Φ ∋ ip ⇒ E ->
    ip <> nil.
Proof.
  induction 1; congruence.
Qed.

Lemma gm_lookup_def : forall Φ ip E, Φ ∋ ip ⇒ E -> exists b pv A B, E = ge_def b pv A B.
Proof. induction 1; eauto. Qed.

Lemma gm_fresh_no_lookup : forall Φ x E ip,
    gm_fresh x Φ ->
    Φ ∋ ip ⇒ E ->
    List.hd_error ip <> Some x.
Proof.
  intros * Hfresh Hlk; induction Hlk;
    apply gm_fresh_ext in Hfresh as [? ?]; simpl;
    solve [congruence | eauto].
Qed.

Lemma gm_lookup_det : forall Φ ip E,
    Φ ∋ ip ⇒ E ->
    gm_canon Φ ->
    forall E', Φ ∋ ip ⇒ E' -> E = E'.
Proof.
  induction 1; intros Hcanon * Hlk; simpl in Hcanon; destruct_all;
    inversion Hlk; subst;
    try solve [exfalso;
               match goal with
               | H : _ ∋ nil ⇒ _ |- _ => exact (gm_lookup_nonnil _ _ _ H eq_refl)
               end];
    try solve [exfalso;
               match goal with
               | Hf : gm_fresh ?x _, H : _ ∋ _ ⇒ _ |- _ =>
                   apply (gm_fresh_no_lookup _ x _ _ Hf H); reflexivity
               end];
    try match goal with
        | IH : gm_canon ?Φ -> _, Hc : gm_canon ?Φ, H : ?Φ ∋ _ ⇒ _ |- _ =>
            exact (IH Hc _ H)
        end; reflexivity.
Qed.

Lemma gs_canon_frame : forall Ξ n U,
    gs_canon Ξ ->
    gs_frame Ξ n = Some U ->
    gm_canon (gu_mod U).
Proof.
  unfold gs_canon; intros * HΞ Hn.
  rewrite List.Forall_forall in HΞ; apply HΞ; eapply gs_frame_In; eassumption.
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

(** ** Freshness and Growth of the Levels *)

Lemma gd_lookup_app_inv : forall d d' fp U,
    gd_lookup (d ++ d') fp = Some U ->
    gd_lookup d fp = Some U \/ gd_lookup d' fp = Some U.
Proof.
  unfold gd_lookup; induction d as [| fV d IH]; simpl; intros * Heq;
    [ now right |].
  destruct (path_beq fp (fst fV)); [ now left | now apply IH ].
Qed.

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

Corollary gc_lookup_det : forall Θ Ξ p E E',
    gs_canon Ξ ->
    gds_mods_canon Θ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ E ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ E' ->
    E = E'.
Proof.
  intros * Hs Hd Hlk Hlk'; inversion Hlk; inversion Hlk'; subst; path_inj;
    [ match goal with
      | H : gs_frame _ _ = Some _, H' : gs_frame _ _ = Some _ |- _ =>
          rewrite H in H'; injection H' as <-
      end
    | match goal with
      | H : gds_lookup _ _ = Some _, H' : gds_lookup _ _ = Some _ |- _ =>
          rewrite H in H'; injection H' as <-
      end ];
    match goal with
    | H1 : gu_mod ?U ∋ _ ⇒ _, H2 : gu_mod ?U ∋ _ ⇒ _ |- _ =>
        exact (gm_lookup_det _ _ _ H1
                 ltac:(eauto using gs_canon_frame, gds_lookup_canon) _ H2)
    end.
Qed.

(** ** Resolution as a Function

    What evaluation uses: the newest entry of a name wins, which in a canonical
    context is the only one, so the function agrees with [gc_lookup]
    ([gc_resolve_sound], [gc_resolve_complete]).  It follows names only: a
    frame by its level, a unit by its path, a member by its name. *)

Fixpoint gm_resolve (Φ : gmod) (ip : list string) : option gentry :=
  match Φ with
  | gm_nil => None
  | gm_ext Φ y E =>
      match ip with
      | x :: ip' =>
          if String.eqb x y
          then match ip', E with
               | nil, ge_def _ _ _ _ => Some E
               | _ :: _, ge_mod _ Φ' => gm_resolve Φ' ip'
               | _, _ => gm_resolve Φ ip
               end
          else gm_resolve Φ ip
      | nil => None
      end
  end.

Definition gc_resolve (Θ : gdeps) (Ξ : gstack) (p : path) : option gentry :=
  match p_qual p with
  | qu_rel n =>
      match gs_frame Ξ n with
      | Some U => gm_resolve (gu_mod U) (p_mems p)
      | None => None
      end
  | qu_abs fp =>
      match gds_lookup Θ fp with
      | Some U => gm_resolve (gu_mod U) (p_mems p)
      | None => None
      end
  end.

Lemma gm_resolve_def : forall Φ ip E, gm_resolve Φ ip = Some E -> exists b pv A B, E = ge_def b pv A B.
Proof.
  fix IH 1; intros [| Φ y E] ip E0 H; cbn in H; [ discriminate |].
  destruct ip as [| x ip']; [ discriminate |].
  destruct (String.eqb x y); [| eapply IH; exact H ].
  destruct ip' as [| z ip''], E as [b pv A B | Δ' Φ'];
    try solve [ eapply IH; exact H ].
  injection H as <-; eauto.
Qed.

Lemma gm_resolve_sound : forall Φ ip E,
    gm_resolve Φ ip = Some E -> Φ ∋ ip ⇒ E.
Proof.
  fix IH 1; intros [| Φ y E] ip E0 H; cbn in H; [ discriminate |].
  destruct ip as [| x ip']; [ discriminate |].
  destruct (String.eqb_spec x y) as [-> |]; [| apply gml_old; eapply IH; exact H ].
  destruct ip' as [| z ip''], E as [b pv A B | Δ' Φ'].
  - injection H as <-; apply gml_last.
  - apply gml_old; eapply IH; exact H.
  - apply gml_old; eapply IH; exact H.
  - destruct (gm_resolve_def _ _ _ H) as (b & pv & A & B & ->).
    apply gml_in; eapply IH; exact H.
Qed.

Lemma gc_resolve_sound : forall Θ Ξ p E,
    gc_resolve Θ Ξ p = Some E -> Θ ⍮ Ξ ∋ᵍ p ⇒ E.
Proof.
  intros Θ Ξ [[fp | n] ip] E H; unfold gc_resolve in H; cbn [p_qual p_mems] in H.
  - destruct (gds_lookup Θ fp) as [U |] eqn:Hf; [| discriminate ].
    destruct (gm_resolve_def _ _ _ H) as (b & pv & A & B & ->).
    econstructor; [ eassumption | apply gm_resolve_sound; exact H ].
  - destruct (gs_frame Ξ n) as [U |] eqn:Hn; [| discriminate ].
    destruct (gm_resolve_def _ _ _ H) as (b & pv & A & B & ->).
    econstructor; [ eassumption | apply gm_resolve_sound; exact H ].
Qed.

Lemma gm_resolve_complete : forall Φ ip E,
    Φ ∋ ip ⇒ E -> gm_canon Φ -> gm_resolve Φ ip = Some E.
Proof.
  induction 1; intros Hc; cbn in Hc |- *; destruct_all.
  - rewrite String.eqb_refl; reflexivity.
  - rewrite String.eqb_refl.
    destruct ip as [| z ip]; [ exfalso; exact (gm_lookup_nonnil _ _ _ H eq_refl) |].
    apply IHgm_lookup; assumption.
  (* an older entry: canonicity says the newer name is not its head *)
  - destruct ip as [| z ip]; [ exfalso; exact (gm_lookup_nonnil _ _ _ H eq_refl) |].
    destruct (String.eqb_spec z y) as [-> |]; [| auto ].
    exfalso; eapply (gm_fresh_no_lookup _ y); [ eassumption | eassumption | reflexivity ].
Qed.

Lemma gc_resolve_complete : forall Θ Ξ p E,
    gs_canon Ξ -> gds_mods_canon Θ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ E -> gc_resolve Θ Ξ p = Some E.
Proof.
  intros * Hs Hd Hlk; inversion Hlk; subst; unfold gc_resolve; cbn [p_qual p_mems].
  - match goal with Hn : gs_frame _ _ = Some _ |- _ => rewrite Hn end.
    apply gm_resolve_complete; [ eassumption | eauto using gs_canon_frame ].
  - match goal with Hn : gds_lookup _ _ = Some _ |- _ => rewrite Hn end.
    apply gm_resolve_complete; [ eassumption | eauto using gds_lookup_canon ].
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

Inductive gm_ins : gmod -> gmod -> list string -> gentry -> Prop :=
| gmi_last :
  `( gm_ins (Φ ⊳ x ↦ ge_def b pv A B) Φ (x :: nil) (ge_def b pv A B) )
| gmi_in :
  `( gm_ins Φ' Φp' ip (ge_def b pv A B) ->
     gm_ins (Φ ⊳ x ↦ ge_mod Δ' Φ') (Φ ⊳ x ↦ ge_mod Δ' Φp') (x :: ip) (ge_def b pv A B) )
| gmi_old :
  `( gm_ins Φ Φp ip E ->
     gm_ins (Φ ⊳ y ↦ E') Φp ip E ).

#[export]
Hint Constructors gm_ins : mctt.

Lemma gm_lookup_ins : forall Φ ip E, Φ ∋ ip ⇒ E -> exists Φp, gm_ins Φ Φp ip E.
Proof. induction 1; destruct_all; eexists; econstructor; eassumption. Qed.

Lemma gm_ins_lookup : forall Φ Φp ip E, gm_ins Φ Φp ip E -> Φ ∋ ip ⇒ E.
Proof. induction 1; econstructor; eassumption. Qed.

Lemma gm_ins_prefix : forall Φ Φp ip E, gm_ins Φ Φp ip E -> gm_prefix Φp Φ.
Proof. induction 1; eauto with mctt. Qed.

Lemma gm_ins_count : forall Φ Φp ip E, gm_ins Φ Φp ip E -> gm_count Φp < gm_count Φ.
Proof.
  induction 1; cbn [gm_count ge_count]; lia.
Qed.

Lemma gm_prefix_lookup : forall Φp Φ ip E, gm_prefix Φp Φ -> Φp ∋ ip ⇒ E -> Φ ∋ ip ⇒ E.
Proof.
  intros until 1; revert ip E; induction H; intros * Hl; [ assumption | econstructor; auto |].
  inversion Hl; subst; [ eapply gml_in | eapply gml_old ]; auto.
Qed.

Lemma gm_prefix_ins : forall Φp Φ Φq ip E,
    gm_prefix Φp Φ -> gm_ins Φp Φq ip E -> gm_ins Φ Φq ip E.
Proof.
  intros until 1; revert Φq ip E; induction H; intros * Hi; [ assumption | econstructor; auto |].
  inversion Hi; subst; [ eapply gmi_in | eapply gmi_old ]; auto.
Qed.

Lemma gm_prefix_trans : forall Φ1 Φ2 Φ3, gm_prefix Φ1 Φ2 -> gm_prefix Φ2 Φ3 -> gm_prefix Φ1 Φ3.
Proof.
  intros * H12 H23; revert Φ1 H12; induction H23; intros; eauto with mctt.
  inversion H12; subst; eauto with mctt.
Qed.

(** ** Closing a Frame

    What a closed module stores: each member of the frame at level [L], filed
    as [mp] with parameters [Δ], generalized over [Δ] and with the frame's
    parameters and members read as [ms_close] says.  A nested module that was
    closed already is closed once more, member by member. *)

Fixpoint ge_close (L : nat) (mp : path) (Δ : ctx) (E : gentry) : gentry :=
  match E with
  | ge_def b pv A B =>
      ge_def b pv (ctx_pi Δ A[close L mp (List.length Δ)]ᵐ)
        (option_map (fun M => ctx_fn Δ M[close L mp (List.length Δ)]ᵐ) B)
  | ge_mod Δ' Φ => ge_mod Δ' (gm_close L mp Δ Φ)
  end
with gm_close (L : nat) (mp : path) (Δ : ctx) (Φ : gmod) : gmod :=
  match Φ with
  | gm_nil => gm_nil
  | gm_ext Φ x E => gm_ext (gm_close L mp Δ Φ) x (ge_close L mp Δ E)
  end.

(** A unit, closed as it is filed under [fp]: it was checked as the only frame,
    at level [0]. *)
Definition gu_close (fp : list string) (U : gunit) : gunit :=
  gu_mk (gu_params U) nil (gm_close 0 (p_abs fp nil) (gu_params U) (gu_mod U)).

Section Close.
  Variables (L : nat) (mp : path) (Δ : ctx).

  #[local] Notation cl := (close L mp (List.length Δ)).

  Definition def_close (b pv : bool) (A : typ) (B : option exp) : gentry :=
    ge_def b pv (ctx_pi Δ A[cl]ᵐ) (option_map (fun M => ctx_fn Δ M[cl]ᵐ) B).

  Lemma gm_close_names : forall Φ, gm_names (gm_close L mp Δ Φ) = gm_names Φ.
  Proof. induction Φ; cbn; congruence. Qed.

  Lemma gm_close_fresh : forall x Φ, gm_fresh x Φ -> gm_fresh x (gm_close L mp Δ Φ).
  Proof. unfold gm_fresh; intros; rewrite gm_close_names; assumption. Qed.

  Lemma gm_close_canon : forall Φ, gm_canon Φ -> gm_canon (gm_close L mp Δ Φ).
  Proof.
    fix IH 1; intros [| Φ x E] H; cbn in *; [ exact I |]; destruct_all.
    repeat split; auto using gm_close_fresh.
    destruct E; cbn in *; auto.
  Qed.

  Lemma gm_close_lookup : forall Φ ip b pv A B,
      Φ ∋ ip ⇒ ge_def b pv A B -> gm_close L mp Δ Φ ∋ ip ⇒ def_close b pv A B.
  Proof.
    intros * H; remember (ge_def b pv A B) as E eqn:HE; revert b pv A B HE.
    induction H; intros * HE; inversion HE; subst; cbn; econstructor; eauto.
  Qed.

  Lemma gm_close_lookup_inv : forall Φc ip E,
      Φc ∋ ip ⇒ E -> forall Φ, Φc = gm_close L mp Δ Φ ->
      exists b pv A B, Φ ∋ ip ⇒ ge_def b pv A B /\ E = def_close b pv A B.
  Proof.
    induction 1; intros [| Φ0 y0 E0] HΦ; cbn in HΦ; try discriminate; injection HΦ as -> -> HE.
    - destruct E0; cbn in HE; [| discriminate ]; injection HE as -> -> -> ->.
      do 4 eexists; split; [ constructor | reflexivity ].
    - destruct E0 as [| Δ0 Φ0']; cbn in HE; [ discriminate |]; injection HE as -> HE.
      destruct (IHgm_lookup _ HE) as (b' & pv' & A' & B' & Hl & Heq).
      do 4 eexists; split; [ constructor; exact Hl | exact Heq ].
    - destruct (IHgm_lookup _ eq_refl) as (b' & pv' & A' & B' & Hl & Heq).
      do 4 eexists; split; [ constructor; exact Hl | exact Heq ].
  Qed.

  Lemma gm_close_prefix : forall Φq Φ, gm_prefix Φq Φ -> gm_prefix (gm_close L mp Δ Φq) (gm_close L mp Δ Φ).
  Proof. induction 1; cbn; eauto with mctt. Qed.

  Lemma gm_close_prefix_inv : forall Φp Φc,
      gm_prefix Φp Φc -> forall Φ, Φc = gm_close L mp Δ Φ ->
      exists Φq, Φp = gm_close L mp Δ Φq /\ gm_prefix Φq Φ.
  Proof.
    induction 1; intros Φ0 HΦ.
    - subst; exists Φ0; split; [ reflexivity | constructor ].
    - destruct Φ0 as [| Φ1 y1 E1]; cbn in HΦ; [ discriminate |]; injection HΦ as -> -> ->.
      destruct (IHgm_prefix _ eq_refl) as (Φq & -> & Hq); exists Φq; split; [ reflexivity | auto with mctt ].
    - destruct Φ0 as [| Φ1 y1 E1]; cbn in HΦ; [ discriminate |]; injection HΦ as -> -> HE.
      destruct E1 as [| Δ1 Φ1']; cbn in HE; [ discriminate |]; injection HE as -> HE.
      destruct (IHgm_prefix _ HE) as (Φq & -> & Hq).
      exists (Φ1 ⊳ y1 ↦ ge_mod Δ1 Φq); split; [ reflexivity | auto with mctt ].
  Qed.

  Lemma gm_close_ins : forall Φ Φq ip b pv A B,
      gm_ins Φ Φq ip (ge_def b pv A B) ->
      gm_ins (gm_close L mp Δ Φ) (gm_close L mp Δ Φq) ip (def_close b pv A B).
  Proof.
    intros * H; remember (ge_def b pv A B) as E eqn:HE; revert b pv A B HE.
    induction H; intros * HE; inversion HE; subst; cbn; econstructor; eauto.
  Qed.

  Lemma gm_close_ins_inv : forall Φc Φp ip E,
      gm_ins Φc Φp ip E -> forall Φ, Φc = gm_close L mp Δ Φ ->
      exists Φq b pv A B, Φp = gm_close L mp Δ Φq /\ E = def_close b pv A B /\
        gm_ins Φ Φq ip (ge_def b pv A B).
  Proof.
    induction 1; intros [| Φ0 y0 E0] HΦ; cbn in HΦ; try discriminate; injection HΦ as -> -> HE.
    - destruct E0; cbn in HE; [| discriminate ]; injection HE as -> -> -> ->.
      exists Φ0; do 4 eexists; split; [ reflexivity | split; [ reflexivity | constructor ] ].
    - destruct E0 as [| Δ0 Φ0']; cbn in HE; [ discriminate |]; injection HE as -> HE.
      destruct (IHgm_ins _ HE) as (Φq & b' & pv' & A' & B' & -> & Heq & Hi).
      exists (Φ0 ⊳ y0 ↦ ge_mod Δ0 Φq), b', pv', A', B'; split; [ reflexivity |].
      split; [ exact Heq | constructor; exact Hi ].
    - destruct (IHgm_ins _ eq_refl) as (Φq & b' & pv' & A' & B' & -> & -> & Hi).
      exists Φq, b', pv', A', B'; split; [ reflexivity | split; [ reflexivity | constructor; exact Hi ] ].
  Qed.
End Close.

(** ** Parameters as a Function

    What evaluation uses for [$[L, k]]: the [k]-th stored parameter type of the
    frame at level [L], a lookup. *)
Definition gs_param (Ξ : gstack) (lp : lpath) : option typ :=
  match gs_frame Ξ (lp_mod lp) with
  | Some U => List.nth_error (gu_ptys U) (lp_param lp)
  | None => None
  end.

(** ** Transparent Global Contexts

    Every definition is transparent and has a body, and no open frame has
    parameters: then no global and no parameter is a neutral, which is what
    canonicity and consistency need.  A filed unit or a nested module may have
    parameters, since its members are stored abstracted over them. *)

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
  (forall U, List.In U Ξ -> gu_params U = nil /\ gu_ptys U = nil /\ gm_transparent (gu_mod U)).

Lemma gm_transparent_lookup' : forall Φ ip E,
    gm_transparent Φ -> Φ ∋ ip ⇒ E -> ge_transparent E.
Proof.
  induction 2; cbn in *; destruct_all; auto.
Qed.

Lemma gm_transparent_lookup : forall Φ ip b pv A B,
    gm_transparent Φ ->
    Φ ∋ ip ⇒ ge_def b pv A B ->
    b = true /\ B <> None.
Proof. intros * HΦ Hl; exact (gm_transparent_lookup' _ _ _ HΦ Hl). Qed.

Lemma gc_transparent_lookup : forall Θ Ξ p b pv A B,
    gc_transparent Θ Ξ ->
    Θ ⍮ Ξ ∋ᵍ p ⇒ ge_def b pv A B ->
    b = true /\ B <> None.
Proof.
  intros * [HΘ HΞ] Hl; inversion Hl; subst;
    match goal with Hm : gu_mod ?U ∋ _ ⇒ ge_def _ _ _ ?B0 |- _ =>
      assert (HU : gm_transparent (gu_mod U))
        by first [ eapply HΞ, gs_frame_In; eassumption
                 | eapply HΘ, gd_lookup_in; eassumption ];
      exact (gm_transparent_lookup _ _ _ _ _ _ HU Hm)
    end.
Qed.

Lemma gc_transparent_param : forall Θ Ξ lp, gc_transparent Θ Ξ -> gs_param Ξ lp = None.
Proof.
  intros * [_ HΞ]; unfold gs_param.
  destruct (gs_frame Ξ (lp_mod lp)) as [U |] eqn:Hn; [| reflexivity ].
  destruct (HΞ _ (gs_frame_In _ _ _ Hn)) as (_ & -> & _); destruct (lp_param lp); reflexivity.
Qed.

(** ** A Fixed Global Context

    The semantic model and the two metatheorems about NbE are stated for one
    global context at a time.  Found by instance resolution, it keeps their
    judgments in the short forms of [Core.Semantic.Fixed]. *)
Class GCtx : Set := gc_mk
  { gc_deps : gdeps
  ; gc_stack : gstack }.
