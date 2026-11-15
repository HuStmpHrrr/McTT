(** * Equal Modules Show the Same Along Paths

    Two equal units, and two equal module expressions, under two equal
    substitutions, show the same along every path of selections and of
    applications to equal arguments ([modexp_conv], [modexp_conv_all]):
    what each side reaches has convertible types, δ-reducts, outermost
    parameters and units.  Before any selection the module parts are
    compared, not the whole descriptions: [wf_me_delta_sel] equates a
    selection, which may have a term part, with the unit its module part
    stands for, which has none. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Consequences Require Import Inversions.
From Mctt.Core.Syntactic Require Import Presup.
From Mctt.Core.Syntactic.System Require Import Structural SlotConversion.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas DescTyping Presup Paths LookupSound NoLevelReflect.
From Mctt.Core.Syntactic.System.Inductives Require Import UniformParams.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Mutual Subtypes Are Equal

    Two types each a subtype of the other are equal: their normal forms
    are equal up to proofs ([nbe_ty_of_mutual_subtyp]), and equal up to
    proofs is equal ([soundness_upto_proofs]). *)
Lemma mutual_subtyp_eq : forall Θ Ξ Γ A A' S, type_sort S -> Θ ⍮ Ξ ⍮ Γ ⊢ A : S -> Θ ⍮ Ξ ⍮ Γ ⊢ A' : S ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ ⍮ Ξ ⍮ Γ ⊢ A' ⊆ A -> Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : S.
Proof.
  intros * HS HA HA' H1 H2.
  destruct (@nbe_ty_of_mutual_subtyp (gc_mk Θ Ξ) Γ A A' H1 H2) as (W & W' & HW & HW' & Hup).
  exact (soundness_upto_proofs HA HA' (nbe_ty_to_nbe_at_sort _ _ _ _ HS HW) (nbe_ty_to_nbe_at_sort _ _ _ _ HS HW') Hup).
Qed.

(** ** Module Parts

    A description and its module part are read alike: a selection reads
    the module part on both, and an application gives descriptions with
    one module part ([mdesc_at_mod_part]). *)

(** The module part of a module part is itself. *)
Lemma mdesc_mod_idem : forall R Rm, mdesc_mod R = Some Rm -> mdesc_mod Rm = Some Rm.
Proof. intros * H; apply mdesc_is_mod_mod; exact (mdesc_mod_is_mod _ _ H). Qed.

(** A module is of the relevant kind and has no term part. *)
Lemma mdesc_is_mod_parts : forall R, mdesc_is_mod R -> mdesc_kind R = ak_relevant /\ mdesc_type R = None /\ mdesc_reduct R = None.
Proof. intros [] H; cbn in H; try contradiction; repeat split. Qed.

(** An application to a description and to its module part: both
    defined or neither, with one module part. *)
Lemma mdesc_at_mod_part : forall R Rm N, mdesc_mod R = Some Rm ->
    (forall R1, mdesc_at R N = Some R1 -> exists Rm1, mdesc_at Rm N = Some Rm1 /\ mdesc_mod R1 = Some Rm1) /\
    (forall Rm1, mdesc_at Rm N = Some Rm1 -> exists R1, mdesc_at R N = Some R1 /\ mdesc_mod R1 = Some Rm1).
Proof.
  induction R as [r A om | Δ Φ Φx | Θ0 p T Φ Ns | Θd A M Rm0 IH]; intros Rm N Hm; cbn in Hm; try discriminate.
  - injection Hm as <-; split; intros X HX; exists X; split; try exact HX;
      apply mdesc_is_mod_mod; eapply mdesc_at_is_mod; try exact HX; exact I.
  - injection Hm as <-; split; intros X HX; exists X; split; try exact HX;
      apply mdesc_is_mod_mod; eapply mdesc_at_is_mod; try exact HX; exact I.
  - destruct (IH _ N Hm) as [IH1 IH2]; split.
    + intros R1 HR1; cbn in HR1.
      destruct (mdesc_at Rm0 N) as [Rm0' |] eqn:E; [| discriminate ].
      destruct (IH1 _ eq_refl) as (Rm1 & HRm1 & Hmd1); exists Rm1; split; [ exact HRm1 |].
      destruct (tele_split (rev Θd)) as [[[? ?] ?] |]; injection HR1 as <-; exact Hmd1.
    + intros Rm1 HRm1; destruct (IH2 _ HRm1) as (Rm0' & HRm0' & Hmd0); cbn; rewrite HRm0'.
      destruct (tele_split (rev Θd)) as [[[? ?] ?] |]; eexists; (split; [ reflexivity | exact Hmd0 ]).
Qed.

(** The telescope a description takes as a module is its module part's. *)
Lemma mdesc_mod_tele_mod_part : forall R Rm, mdesc_mod R = Some Rm -> mdesc_mod_tele Rm = mdesc_mod_tele R.
Proof. intros * H; unfold mdesc_mod_tele; rewrite (mdesc_mod_idem _ _ H), H; reflexivity. Qed.

(** The leaves of two descriptions show the same of their module parts. *)
Lemma leaf_conv_mod_part : forall Θ Ξ Γ Y Y' X X', leaf_conv Θ Ξ Γ Y Y' -> mdesc_mod Y = Some X -> mdesc_mod Y' = Some X' ->
    leaf_conv Θ Ξ Γ X X'.
Proof.
  intros * [Hk Ht Hr Hu Hh Hf Hn] HY HY'.
  destruct (mdesc_is_mod_parts _ (mdesc_mod_is_mod _ _ HY)) as (Hk1 & Ht1 & Hr1).
  destruct (mdesc_is_mod_parts _ (mdesc_mod_is_mod _ _ HY')) as (Hk2 & Ht2 & Hr2).
  constructor.
  - congruence.
  - rewrite Ht1, Ht2; exact I.
  - intros A HA; congruence.
  - rewrite (mdesc_mod_idem _ _ HY), (mdesc_mod_idem _ _ HY'); rewrite HY, HY' in Hu; exact Hu.
  - unfold mdesc_head in *; rewrite (mdesc_mod_tele_mod_part _ _ HY), (mdesc_mod_tele_mod_part _ _ HY'); exact Hh.
  - unfold desc_reads_frame in *; rewrite (mdesc_mod_idem _ _ HY), (mdesc_mod_idem _ _ HY'); rewrite HY, HY' in Hf; exact Hf.
  - rewrite <- (no_level_mod_iff _ _ _ _ _ HY), <- (no_level_mod_iff _ _ _ _ _ HY'); exact Hn.
Qed.

(** [leaf_core Θ Ξ Γ R R']: [leaf_conv] but for the units: the leaves show
    the same of their term parts, frames and outermost parameters, and have
    module parts on both sides or on neither. *)
Record leaf_core (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (R R' : mdesc) : Prop := mk_leaf_core
  { (** The term parts are of one kind *)
    core_kind : mdesc_kind R = mdesc_kind R'
    (** Term parts on both sides or on neither, of convertible types *)
  ; core_type : opt_rel (fun A A' => exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : abs_kind_sort (mdesc_kind R) Typeω@i)
                  (mdesc_type R) (mdesc_type R')
    (** δ-reducts on both sides or on neither, convertible *)
  ; core_reduct : forall A, mdesc_type R = Some A ->
      opt_rel (fun M M' => Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A) (mdesc_reduct R) (mdesc_reduct R')
    (** Module parts on both sides or on neither *)
  ; core_mod : opt_rel (fun _ _ => True) (mdesc_mod R) (mdesc_mod R')
    (** Outermost parameters on both sides or on neither, each a
        refinement of the other *)
  ; core_head : opt_rel (fun B B' => Θ ⍮ Ξ ⍮ Γ ⊢ B ⊆ B' /\ Θ ⍮ Ξ ⍮ Γ ⊢ B' ⊆ B) (mdesc_head R) (mdesc_head R')
    (** Stored at an open frame on both sides or on neither *)
  ; core_frame : desc_reads_frame Ξ R <-> desc_reads_frame Ξ R'
    (** With no member of a type of levels on both sides or on neither,
        as for [leaf_nl] *)
  ; core_nl : Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ R <-> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ R' }.

(** A [leaf_core] with units equal is a [leaf_conv]. *)
Lemma leaf_conv_of_core : forall Θ Ξ Γ R R', leaf_core Θ Ξ Γ R R' ->
    opt_rel (fun Rm Rm' => Θ ⍮ Ξ ⍮ Γ ⊢ᵐ mdesc_unit Rm ≈ mdesc_unit Rm') (mdesc_mod R) (mdesc_mod R') ->
    leaf_conv Θ Ξ Γ R R'.
Proof. intros * [] Hu; constructor; assumption. Qed.

(** A [leaf_conv] is a [leaf_core]. *)
Lemma leaf_core_of_conv : forall Θ Ξ Γ R R', leaf_conv Θ Ξ Γ R R' -> leaf_core Θ Ξ Γ R R'.
Proof.
  intros * [Hk Ht Hr Hu Hh Hf Hn]; constructor; try assumption.
  destruct (mdesc_mod R), (mdesc_mod R'); cbn in *; tauto.
Qed.

(** ** Paths

    Two module expressions are compared along paths: sequences of
    selections and of applications to two equal arguments, one for each
    side.  A path is a module expression, so what it denotes needs no
    observation of a description, and selections through open frames are
    read like any other. *)

(** One step of a path: a selection, or an application to two equal
    arguments, the first for the left side, the second for the right. *)
Inductive path_step : Set :=
(** The selection of the entry [y] *)
| ps_mem (y : String.string)
(** The application to [N] on the left and to [N'] on the right *)
| ps_app (N N' : exp).

(** The left side of a path from [P]. *)
Fixpoint path_left (P : modexp) (s : list path_step) : modexp :=
  match s with
  | nil => P
  | ps_mem y :: s' => path_left (me_mem P y) s'
  | ps_app N _ :: s' => path_left (me_app P N) s'
  end.

(** The right side of a path from [P']. *)
Fixpoint path_right (P' : modexp) (s : list path_step) : modexp :=
  match s with
  | nil => P'
  | ps_mem y :: s' => path_right (me_mem P' y) s'
  | ps_app _ N' :: s' => path_right (me_app P' N') s'
  end.

(** [path_pairs Θ Ξ Δ P s]: each application of the path [s] from [P] is
    to two arguments equal at the outermost parameter of what the left
    side denotes there. *)
Inductive path_pairs (Θ : gdeps) (Ξ : gstack) (Δ : ctx) : modexp -> list path_step -> Prop :=
(** No step *)
| path_pairs_nil : forall P, path_pairs Θ Ξ Δ P nil
(** A selection, then the rest *)
| path_pairs_mem : forall P y s, path_pairs Θ Ξ Δ (me_mem P y) s -> path_pairs Θ Ξ Δ P (ps_mem y :: s)
(** An application to two equal arguments of the outermost parameter,
    then the rest *)
| path_pairs_app : forall P R T B T1 N N' s,
    mdenote Θ Ξ Δ P R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) ->
    Θ ⍮ Ξ ⍮ Δ ⊢ N ≈ N' : B -> path_pairs Θ Ξ Δ (me_app P N) s -> path_pairs Θ Ξ Δ P (ps_app N N' :: s).

#[export]
Hint Constructors path_pairs : mctt.

(** Whether a path has no selection. *)
Fixpoint path_all_apps (s : list path_step) : bool :=
  match s with
  | nil => true
  | ps_app _ _ :: s' => path_all_apps s'
  | ps_mem _ :: _ => false
  end.

(** [path_leaf Θ Ξ Δ s X X']: what the path [s] reaches on the two sides
    shows the same: as modules, by their module parts, before any
    selection, since two module expressions are compared as modules; as
    members, wholly, after one. *)
Definition path_leaf (Θ : gdeps) (Ξ : gstack) (Δ : ctx) (s : list path_step) (X X' : mdesc) : Prop :=
  if path_all_apps s then opt_rel (leaf_conv Θ Ξ Δ) (mdesc_mod X) (mdesc_mod X') else leaf_conv Θ Ξ Δ X X'.

(** [paths_rel Θ Ξ Δ L P P']: along every path [s], the left side from
    [P] denotes exactly when the right side from [P'] does, the two
    related by the leaf relation [L s].  The comparisons below are its
    instances at three leaf relations: wholly ([paths_conv]), up to the
    units of the leaves ([paths_core]), and up to the units at the root
    only ([paths_conv_m]). *)
Definition paths_rel (Θ : gdeps) (Ξ : gstack) (Δ : ctx) (L : list path_step -> mdesc -> mdesc -> Prop)
    (P P' : modexp) : Prop :=
  forall s, path_pairs Θ Ξ Δ P s ->
    (forall X, mdenote Θ Ξ Δ (path_left P s) X -> exists X', mdenote Θ Ξ Δ (path_right P' s) X' /\ L s X X') /\
    (forall X', mdenote Θ Ξ Δ (path_right P' s) X' -> exists X, mdenote Θ Ξ Δ (path_left P s) X /\ L s X X').

(** [paths_conv Θ Ξ Δ P P']: [paths_rel] at the leaves showing the same
    ([path_leaf]). *)
Definition paths_conv (Θ : gdeps) (Ξ : gstack) (Δ : ctx) : modexp -> modexp -> Prop :=
  paths_rel Θ Ξ Δ (path_leaf Θ Ξ Δ).

(** [path_leaf] the other way round. *)
Lemma path_leaf_sym : forall Θ Ξ Δ s X X', path_leaf Θ Ξ Δ s X X' -> path_leaf Θ Ξ Δ s X' X.
Proof.
  unfold path_leaf; intros * H; destruct (path_all_apps s); [| exact (leaf_conv_sym _ _ _ _ _ H) ].
  eapply opt_rel_sym; [| exact H ]; intros; apply leaf_conv_sym; assumption.
Qed.

(** [path_leaf] chained. *)
Lemma path_leaf_trans : forall Θ Ξ Δ s X X' X'', path_leaf Θ Ξ Δ s X X' -> path_leaf Θ Ξ Δ s X' X'' -> path_leaf Θ Ξ Δ s X X''.
Proof.
  unfold path_leaf; intros * H1 H2; destruct (path_all_apps s); [| exact (leaf_conv_trans _ _ _ _ _ _ H1 H2) ].
  eapply opt_rel_trans; [| exact H1 | exact H2 ]; intros; eapply leaf_conv_trans; eassumption.
Qed.

(** [modexp_conv Θ Ξ Γ H H']: [H] and [H'] are compared along paths under
    every two equal substitutions into [Γ], one for each side. *)
Definition modexp_conv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (H H' : modexp) : Prop :=
  forall Δ σ σ', Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ ≈ σ' : Γ -> paths_conv Θ Ξ Δ H[σ]ᵐ H'[σ']ᵐ.

(** *** Composing Paths *)

(** Paths from a selection are paths from the selected expression. *)
Lemma leaf_conv_mod_opt : forall Θ Ξ Δ X X', leaf_conv Θ Ξ Δ X X' -> opt_rel (leaf_conv Θ Ξ Δ) (mdesc_mod X) (mdesc_mod X').
Proof.
  intros * Hl; pose proof (leaf_unit _ _ _ _ _ Hl) as Hu.
  destruct (mdesc_mod X) as [Xm |] eqn:E; destruct (mdesc_mod X') as [Xm' |] eqn:E'; cbn in Hu |- *; try contradiction; [| exact I ].
  exact (leaf_conv_mod_part _ _ _ _ _ _ _ Hl E E').
Qed.

(** A whole leaf relation gives the module one. *)
Lemma path_leaf_mem : forall Θ Ξ Δ y s X X', path_leaf Θ Ξ Δ (ps_mem y :: s) X X' -> path_leaf Θ Ξ Δ s X X'.
Proof.
  intros * Hl; unfold path_leaf in *; cbn in Hl; destruct (path_all_apps s); [ exact (leaf_conv_mod_opt _ _ _ _ _ Hl) | exact Hl ].
Qed.

(** Paths from two selections of one member are paths from the selected
    expressions. *)
Lemma paths_conv_mem : forall Θ Ξ Δ P P' y, paths_conv Θ Ξ Δ P P' -> paths_conv Θ Ξ Δ (me_mem P y) (me_mem P' y).
Proof.
  intros * H s Hs; destruct (H (ps_mem y :: s) (path_pairs_mem _ _ _ _ _ _ Hs)) as [H1 H2]; cbn [path_left path_right] in H1, H2; split.
  - intros X HX; destruct (H1 _ HX) as (X' & HX' & Hl); exists X'; split; [ exact HX' | exact (path_leaf_mem _ _ _ _ _ _ _ Hl) ].
  - intros X' HX'; destruct (H2 _ HX') as (X & HX & Hl); exists X; split; [ exact HX | exact (path_leaf_mem _ _ _ _ _ _ _ Hl) ].
Qed.

(** Paths from two applications to equal arguments are paths from the
    applied expressions. *)
Lemma paths_conv_app : forall Θ Ξ Δ P P' R T B T1 N N',
    paths_conv Θ Ξ Δ P P' -> mdenote Θ Ξ Δ P R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) ->
    Θ ⍮ Ξ ⍮ Δ ⊢ N ≈ N' : B -> paths_conv Θ Ξ Δ (me_app P N) (me_app P' N').
Proof. intros * H Hm Ht Hv HN s Hs; exact (H (ps_app N N' :: s) (path_pairs_app _ _ _ _ _ _ _ _ _ _ _ Hm Ht Hv HN Hs)). Qed.

(** A path with both arguments of each application the left one. *)
Fixpoint path_diag (s : list path_step) : list path_step :=
  match s with
  | nil => nil
  | ps_mem y :: s' => ps_mem y :: path_diag s'
  | ps_app N _ :: s' => ps_app N N :: path_diag s'
  end.

(** A path with the arguments of each application swapped. *)
Fixpoint path_swap (s : list path_step) : list path_step :=
  match s with
  | nil => nil
  | ps_mem y :: s' => ps_mem y :: path_swap s'
  | ps_app N N' :: s' => ps_app N' N :: path_swap s'
  end.

(** The diagonal path reads the left arguments on both sides. *)
Lemma path_diag_sides : forall s P, path_left P (path_diag s) = path_left P s /\ path_right P (path_diag s) = path_left P s.
Proof. induction s as [| [y | N N'] s IH]; intros P; cbn; [ split; reflexivity | apply IH | apply IH ]. Qed.

(** The swapped path exchanges the sides. *)
Lemma path_swap_sides : forall s P, path_left P (path_swap s) = path_right P s /\ path_right P (path_swap s) = path_left P s.
Proof. induction s as [| [y | N N'] s IH]; intros P; cbn; [ split; reflexivity | apply IH | split; apply IH ]. Qed.

(** Swapping the arguments keeps whether a path has a selection. *)
Lemma path_all_apps_swap : forall s, path_all_apps (path_swap s) = path_all_apps s.
Proof. induction s as [| [] s IH]; cbn; auto. Qed.

(** The same for the diagonal path. *)
Lemma path_all_apps_diag : forall s, path_all_apps (path_diag s) = path_all_apps s.
Proof. induction s as [| [] s IH]; cbn; auto. Qed.

(** [path_leaf] read at the swapped path. *)
Lemma path_leaf_swap : forall Θ Ξ Δ s X X', path_leaf Θ Ξ Δ (path_swap s) X X' <-> path_leaf Θ Ξ Δ s X X'.
Proof. intros; unfold path_leaf; rewrite path_all_apps_swap; reflexivity. Qed.

(** [path_leaf] read at the diagonal path. *)
Lemma path_leaf_diag : forall Θ Ξ Δ s X X', path_leaf Θ Ξ Δ (path_diag s) X X' <-> path_leaf Θ Ξ Δ s X X'.
Proof. intros; unfold path_leaf; rewrite path_all_apps_diag; reflexivity. Qed.

(** The outermost parameter of a description, as an equation. *)
Lemma mdesc_head_of : forall R T B T1, mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) -> mdesc_head R = Some B.
Proof. intros * Ht Hv; unfold mdesc_head; rewrite Ht, Hv; reflexivity. Qed.

(** A description with an outermost parameter has a telescope that
    views it. *)
Lemma mdesc_head_inv : forall R B, mdesc_head R = Some B -> exists T T1, mdesc_mod_tele R = Some T /\ tele_view T = Some (B, T1).
Proof.
  intros * H; unfold mdesc_head in H; destruct (mdesc_mod_tele R) as [T |]; [| discriminate ].
  destruct (tele_view T) as [[B0 T1] |] eqn:Ev; cbn in H; [ injection H as <-; eauto | discriminate ].
Qed.

(** Arguments equal at a parameter are equal at a parameter refining
    it both ways. *)
Lemma head_conv_arg : forall Θ Ξ Δ R R' T B T1 N N', leaf_conv Θ Ξ Δ R R' ->
    mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) -> Θ ⍮ Ξ ⍮ Δ ⊢ N ≈ N' : B ->
    exists T' B' T1', mdesc_mod_tele R' = Some T' /\ tele_view T' = Some (B', T1') /\ Θ ⍮ Ξ ⍮ Δ ⊢ N ≈ N' : B' /\
      Θ ⍮ Ξ ⍮ Δ ⊢ B ⊆ B' /\ Θ ⍮ Ξ ⍮ Δ ⊢ B' ⊆ B.
Proof.
  intros * Hl Ht Hv HN; pose proof (leaf_head _ _ _ _ _ Hl) as Hh; rewrite (mdesc_head_of _ _ _ _ Ht Hv) in Hh.
  destruct (mdesc_head R') as [B' |] eqn:EB'; cbn in Hh; [| contradiction ]; destruct Hh as [H1 H2].
  destruct (mdesc_head_inv _ _ EB') as (T' & T1' & Ht' & Hv').
  exists T', B', T1'; repeat split; try assumption; exact (wf_exp_eq_subtyp' _ _ _ _ _ _ _ HN H1).
Qed.

(** The same for the module parts of two descriptions. *)
Lemma head_conv_arg_mod : forall Θ Ξ Δ R R' T B T1 N N', opt_rel (leaf_conv Θ Ξ Δ) (mdesc_mod R) (mdesc_mod R') ->
    mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) -> Θ ⍮ Ξ ⍮ Δ ⊢ N ≈ N' : B ->
    exists T' B' T1', mdesc_mod_tele R' = Some T' /\ tele_view T' = Some (B', T1') /\ Θ ⍮ Ξ ⍮ Δ ⊢ N ≈ N' : B' /\
      Θ ⍮ Ξ ⍮ Δ ⊢ B ⊆ B' /\ Θ ⍮ Ξ ⍮ Δ ⊢ B' ⊆ B.
Proof.
  intros * Hl Ht Hv HN.
  destruct (mdesc_mod R) as [Rm |] eqn:Em; [| unfold mdesc_mod_tele in Ht; rewrite Em in Ht; discriminate ].
  destruct (mdesc_mod R') as [Rm' |] eqn:Em'; cbn in Hl; [| contradiction ].
  rewrite <- (mdesc_mod_tele_mod_part _ _ Em) in Ht; rewrite <- (mdesc_mod_tele_mod_part _ _ Em').
  exact (head_conv_arg _ _ _ _ _ _ _ _ _ _ Hl Ht Hv HN).
Qed.

(** Paths of the left expression with equal arguments are paths of the
    right one, at the left arguments. *)
Lemma paths_conv_pairs_left : forall Θ Ξ Δ P s, path_pairs Θ Ξ Δ P s -> forall P', paths_conv Θ Ξ Δ P P' -> path_pairs Θ Ξ Δ P' s.
Proof.
  induction 1 as [P | P y s Hs IH | P R T B T1 N N' s Hm Ht Hv HN Hs IH]; intros P' HP.
  - constructor.
  - constructor; apply IH; apply paths_conv_mem; exact HP.
  - destruct (proj1 (HP nil (path_pairs_nil _ _ _ _)) _ Hm) as (R' & Hm' & Hl).
    destruct (head_conv_arg_mod _ _ _ _ _ _ _ _ _ _ Hl Ht Hv HN) as (T' & B' & T1' & Ht' & Hv' & HN' & _).
    econstructor; [ exact Hm' | exact Ht' | exact Hv' | exact HN' |].
    apply IH; eapply paths_conv_app; [ exact HP | exact Hm | exact Ht | exact Hv | exact (wf_exp_eq_refl (presup_exp_eq_left HN)) ].
Qed.

(** Paths of the right expression are paths of the left one, with the
    arguments swapped. *)
Lemma paths_conv_pairs_swap : forall Θ Ξ Δ P' s, path_pairs Θ Ξ Δ P' s -> forall P, paths_conv Θ Ξ Δ P P' ->
    path_pairs Θ Ξ Δ P (path_swap s).
Proof.
  induction 1 as [P' | P' y s Hs IH | P' R' T' B' T1' N N' s Hm' Ht' Hv' HN Hs IH]; intros P HP; cbn.
  - constructor.
  - constructor; apply IH; apply paths_conv_mem; exact HP.
  - destruct (proj2 (HP nil (path_pairs_nil _ _ _ _)) _ Hm') as (R & Hm & Hl).
    destruct (head_conv_arg_mod _ _ _ _ _ _ _ _ _ _ (path_leaf_sym _ _ _ _ _ _ Hl) Ht' Hv' HN) as (T & B & T1 & Ht & Hv & HN0 & _).
    econstructor; [ exact Hm | exact Ht | exact Hv | exact (wf_exp_eq_sym _ _ _ _ _ _ HN0) |].
    apply IH; eapply paths_conv_app; [ exact HP | exact Hm | exact Ht | exact Hv | exact (wf_exp_eq_sym _ _ _ _ _ _ HN0) ].
Qed.

(** Equal arguments are equal to themselves. *)
Lemma path_pairs_diag : forall Θ Ξ Δ P s, path_pairs Θ Ξ Δ P s -> path_pairs Θ Ξ Δ P (path_diag s).
Proof.
  induction 1; cbn; econstructor; try eassumption.
  apply wf_exp_eq_refl; eapply presup_exp_eq_left; eassumption.
Qed.

(** [paths_conv] the other way round. *)
Lemma paths_conv_sym : forall Θ Ξ Δ P P', paths_conv Θ Ξ Δ P P' -> paths_conv Θ Ξ Δ P' P.
Proof.
  intros * HP s Hs; pose proof (paths_conv_pairs_swap _ _ _ _ _ Hs _ HP) as Hs'.
  destruct (path_swap_sides s P) as [EL ER]; destruct (path_swap_sides s P') as [EL' ER'].
  destruct (HP _ Hs') as [H1 H2]; rewrite EL, ER' in *; split.
  - intros X' HX'; destruct (H2 _ HX') as (X & HX & Hl); exists X; split; [ exact HX |].
    apply path_leaf_sym; apply (proj1 (path_leaf_swap _ _ _ _ _ _)); exact Hl.
  - intros X HX; destruct (H1 _ HX) as (X' & HX' & Hl); exists X'; split; [ exact HX' |].
    apply path_leaf_sym; apply (proj1 (path_leaf_swap _ _ _ _ _ _)); exact Hl.
Qed.

(** [paths_conv] chained. *)
Lemma paths_conv_trans : forall Θ Ξ Δ P P' P'', paths_conv Θ Ξ Δ P P' -> paths_conv Θ Ξ Δ P' P'' -> paths_conv Θ Ξ Δ P P''.
Proof.
  intros * H1 H2 s Hs.
  pose proof (path_pairs_diag _ _ _ _ _ Hs) as Hd; pose proof (paths_conv_pairs_left _ _ _ _ _ Hs _ H1) as Hs'.
  destruct (path_diag_sides s P) as [EL _]; destruct (path_diag_sides s P') as [_ ER'].
  destruct (H1 _ Hd) as [H1a H1b]; destruct (H2 _ Hs') as [H2a H2b]; rewrite EL, ER' in *; split.
  - intros X HX; destruct (H1a _ HX) as (X1 & HX1 & Hl1); destruct (H2a _ HX1) as (X2 & HX2 & Hl2).
    exists X2; split; [ exact HX2 |]; apply (proj1 (path_leaf_diag _ _ _ _ _ _)) in Hl1.
    exact (path_leaf_trans _ _ _ _ _ _ _ Hl1 Hl2).
  - intros X2 HX2; destruct (H2b _ HX2) as (X1 & HX1 & Hl2); destruct (H1b _ HX1) as (X & HX & Hl1).
    exists X; split; [ exact HX |]; apply (proj1 (path_leaf_diag _ _ _ _ _ _)) in Hl1.
    exact (path_leaf_trans _ _ _ _ _ _ _ Hl1 Hl2).
Qed.

(** *** Paths from Expressions that Are No Path Names

    A module expression that names no path ([mod_qname]) is read through
    what it denotes only: each step of a path from it is read from the
    description before, so two such expressions of one description have
    paths of one description. *)

(** One step on the left. *)
Definition step_left (P : modexp) (st : path_step) : modexp :=
  match st with
  | ps_mem y => me_mem P y
  | ps_app N _ => me_app P N
  end.

(** A step from an expression naming no path is read from what the
    expression denotes. *)
Lemma step_left_inv : forall Θ Ξ Δ P st X, mod_qname P = None -> mdenote Θ Ξ Δ (step_left P st) X ->
    exists R, mdenote Θ Ξ Δ P R /\ forall P', mdenote Θ Ξ Δ P' R -> mdenote Θ Ξ Δ (step_left P' st) X.
Proof.
  intros Θ Ξ Δ P [y | N N'] X Hq Hm; cbn in Hm.
  - inversion Hm; subst; try (cbn in *; rewrite Hq in *; discriminate).
    eexists; split; [ eassumption | intros P' HP'; econstructor; eassumption ].
  - inversion Hm; subst; try (cbn in *; discriminate).
    eexists; split; [ eassumption | intros P' HP'; econstructor; eassumption ].
Qed.

(** [frame_free_path Ξ p]: [p] names no open frame. *)
Definition frame_free_path (Ξ : gstack) (p : qname) : Prop := forall U T, gs_find_tele Ξ p <> Some (U, nil, T).

(** A member of a module that is no open frame is no open frame. *)
Lemma frame_free_path_in : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p y, frame_free_path Ξ p -> frame_free_path Ξ (qname_in p y).
Proof.
  intros * Hg * Hp U T Ht; destruct (frame_parent _ _ Hg _ _ _ _ Ht) as (T' & Φ' & Hf & _).
  unfold gc_frame in Hf; destruct (gs_find_tele Ξ p) as [[[[Δ0 [[|] Φ0 | E0]] [| ? ?]] T0] |] eqn:E; try discriminate.
  exact (Hp _ _ E).
Qed.

(** Every open frame holds a closed body. *)
Lemma wf_gstack_units : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall mp K U, List.In (mp, K, U) Ξ -> exists Δ Φ, U = gu_body Δ Φ.
Proof.
  induction 1; intros * Hin; cbn in Hin; try contradiction.
  destruct Hin as [[= <- <- <-] | Hin]; [ eauto | eauto ].
Qed.

(** A path whose description reads no open frame names no open frame. *)
Lemma frame_free_of_desc : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ E R p, mod_qname E = Some p -> mdenote Θ Ξ Γ E R ->
    ~ desc_reads_frame Ξ R -> frame_free_path Ξ p.
Proof.
  intros * Hg * Hq Hm Hn U T Ht; apply Hn.
  destruct (gs_find_tele_own _ _ _ _ Ht) as [K HK]; destruct (wf_gstack_units _ _ Hg _ _ _ HK) as (Δ & Φ & ->).
  destruct (frame_denote_unique _ _ Hg _ _ _ _ Hq Hm) as (Hu & Hi & Hr).
  destruct (gs_find_ind Ξ p) as [[[pq k] D] |] eqn:Ek.
  - destruct (frame_ind_loc _ _ Hg _ _ _ _ Ek) as (U0 & T0 & T1 & Φ1 & Mk & _ & Hf & Hl & HMk).
    rewrite (Hi _ _ _ _ _ _ eq_refl HMk Hl); exists nil, p, T1, Φ1, nil; split; [ reflexivity | rewrite Hf; discriminate ].
  - destruct (gs_find_record Ξ p) as [Rr |] eqn:Er.
    + destruct (frame_record_loc _ _ Hg _ _ Er) as (U0 & T0 & T1 & Φ1 & _ & Hf & Hl).
      rewrite (Hr _ _ _ eq_refl Hl); exists nil, p, T1, Φ1, nil; split; [ reflexivity | rewrite Hf; discriminate ].
    + assert (Hgu : gc_unit Θ Ξ E = Some (Δ ++ T, Φ)) by (unfold gc_unit; rewrite Hq, Ht, Ek, Er; reflexivity).
      rewrite (Hu _ _ Hgu); exists nil, p, (Δ ++ T), Φ, nil; split; [ reflexivity |].
      unfold gc_frame; rewrite Ht; discriminate.
Qed.

(** [obs_root Θ Ξ P]: every step from [P] is read from what [P]
    denotes: [P] names no path, or a path of no open frame. *)
Definition obs_root (Ξ : gstack) (P : modexp) : Prop :=
  mod_qname P = None \/ exists p, mod_qname P = Some p /\ frame_free_path Ξ p.

(** The selection of a member of a path of no open frame is read from
    what the path denotes. *)
Lemma path_mem_inv : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ P p y X, mod_qname P = Some p -> frame_free_path Ξ p ->
    mdenote Θ Ξ Δ (me_mem P y) X ->
    exists R, mdenote Θ Ξ Δ P R /\ forall P', mdenote Θ Ξ Δ P' R -> mdenote Θ Ξ Δ (me_mem P' y) X.
Proof.
  intros * Hg * Hq Hp Hm.
  pose proof (frame_free_path_in _ _ Hg _ y Hp) as Hpy.
  assert (Hqy : mod_qname (me_mem P y) = Some (qname_in p y)) by (cbn; rewrite Hq; reflexivity).
  inversion Hm as [? ? ? ? ? Hq1 Hu | ? ? ? ? ? ? ? ? ? Hq1 Hk | | | | | ? ? ? ? ? ? Hq1 Hk]; subst.
  - exfalso; unfold gc_unit in Hu; rewrite Hqy in Hu.
    destruct (gs_find_tele Ξ (qname_in p y)) as [[[U0 [| ? ?]] T0] |] eqn:Et; try discriminate.
    + exact (Hpy _ _ Et).
    + cbn in Hu; destruct (q_chain p); discriminate.
  - exfalso; rewrite Hqy in Hq1; injection Hq1 as <-.
    destruct (gs_find_ind_tele _ _ _ Hk) as (U0 & T0 & Ht); exact (Hpy _ _ Ht).
  - eexists; split; [ eassumption | intros P' HP'; econstructor; eassumption ].
  - exfalso; rewrite Hqy in Hq1; injection Hq1 as <-.
    destruct (gs_find_record_tele _ _ _ Hk) as (U0 & T0 & Ht); exact (Hpy _ _ Ht).
Qed.

(** A step from an expression read from what it denotes. *)
Lemma step_left_obs : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ P st X, obs_root Ξ P -> mdenote Θ Ξ Δ (step_left P st) X ->
    exists R, mdenote Θ Ξ Δ P R /\ forall P', mdenote Θ Ξ Δ P' R -> mdenote Θ Ξ Δ (step_left P' st) X.
Proof.
  intros * Hg * [Hq | (p & Hq & Hp)] Hm; [ exact (step_left_inv _ _ _ _ _ _ Hq Hm) |].
  destruct st as [y | N N']; [ exact (path_mem_inv _ _ Hg _ _ _ _ _ Hq Hp Hm) |].
  cbn in Hm; inversion Hm; subst; try (cbn in *; discriminate).
  eexists; split; [ eassumption | intros P' HP'; econstructor; eassumption ].
Qed.

(** A step from such an expression is such an expression. *)
Lemma obs_root_step : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall P st, obs_root Ξ P -> obs_root Ξ (step_left P st).
Proof.
  intros * Hg P [y | N N'] [Hq | (p & Hq & Hp)]; unfold obs_root; cbn [step_left mod_qname].
  - left; rewrite Hq; reflexivity.
  - right; exists (qname_in p y); rewrite Hq; split; [ reflexivity | exact (frame_free_path_in _ _ Hg _ _ Hp) ].
  - left; reflexivity.
  - left; reflexivity.
Qed.

(** [same_denote Θ Ξ Δ P P']: [P] and [P'] denote the same. *)
Definition same_denote (Θ : gdeps) (Ξ : gstack) (Δ : ctx) (P P' : modexp) : Prop :=
  forall X, mdenote Θ Ξ Δ P X <-> mdenote Θ Ξ Δ P' X.

(** Two expressions of one description denote the same. *)
Lemma same_denote_of : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ P P' R, mdenote Θ Ξ Δ P R -> mdenote Θ Ξ Δ P' R -> same_denote Θ Ξ Δ P P'.
Proof.
  intros * Hg * Hm Hm' X; split; intros HX.
  - rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HX _ Hm); exact Hm'.
  - rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HX _ Hm'); exact Hm.
Qed.

(** One step from two expressions read through what they denote, which
    denote the same. *)
Lemma same_denote_step : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ P P' st, obs_root Ξ P -> obs_root Ξ P' ->
    same_denote Θ Ξ Δ P P' -> same_denote Θ Ξ Δ (step_left P st) (step_left P' st).
Proof.
  intros * Hg * Hq Hq' H X; split; intros HX.
  - destruct (step_left_obs _ _ Hg _ _ _ _ Hq HX) as (R & HR & Hs); exact (Hs _ (proj1 (H _) HR)).
  - destruct (step_left_obs _ _ Hg _ _ _ _ Hq' HX) as (R & HR & Hs); exact (Hs _ (proj2 (H _) HR)).
Qed.

(** Every path from two such expressions. *)
Lemma same_denote_path : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ s P P', obs_root Ξ P -> obs_root Ξ P' -> same_denote Θ Ξ Δ P P' ->
    same_denote Θ Ξ Δ (path_left P s) (path_left P' s) /\ same_denote Θ Ξ Δ (path_right P s) (path_right P' s).
Proof.
  intros Θ Ξ Hg Δ s; induction s as [| [y | N N'] s IH]; intros * Hq Hq' H; cbn; [ split; exact H | |].
  - apply IH; [ exact (obs_root_step _ _ Hg _ (ps_mem y) Hq) | exact (obs_root_step _ _ Hg _ (ps_mem y) Hq') |].
    exact (same_denote_step _ _ Hg _ _ _ (ps_mem y) Hq Hq' H).
  - split; [ apply (IH (me_app P N) (me_app P' N)) | apply (IH (me_app P N') (me_app P' N')) ];
      first [ left; reflexivity | exact (same_denote_step _ _ Hg _ _ _ (ps_app N N) Hq Hq' H)
            | exact (same_denote_step _ _ Hg _ _ _ (ps_app N' N') Hq Hq' H) ].
Qed.

(** Paths with equal arguments of one of them are of the other. *)
Lemma path_pairs_same : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ P s, path_pairs Θ Ξ Δ P s -> forall P', obs_root Ξ P -> obs_root Ξ P' ->
    same_denote Θ Ξ Δ P P' -> path_pairs Θ Ξ Δ P' s.
Proof.
  intros Θ Ξ Hg Δ; induction 1 as [P | P y s Hs IH | P R T B T1 N N' s Hm Ht Hv HN Hs IH]; intros P' Hq Hq' H; [ constructor | |].
  - constructor; apply IH; [ exact (obs_root_step _ _ Hg _ (ps_mem y) Hq) | exact (obs_root_step _ _ Hg _ (ps_mem y) Hq') |].
    exact (same_denote_step _ _ Hg _ _ _ (ps_mem y) Hq Hq' H).
  - econstructor; [ exact (proj1 (H _) Hm) | exact Ht | exact Hv | exact HN |].
    apply IH; [ left; reflexivity | left; reflexivity | exact (same_denote_step _ _ Hg _ _ _ (ps_app N N) Hq Hq' H) ].
Qed.

(** Paths compared from one side compare from any expression read
    through what it denotes that denotes the same, on the left. *)
Lemma paths_conv_same_left : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ P P' Q, obs_root Ξ P -> obs_root Ξ P' ->
    same_denote Θ Ξ Δ P P' -> paths_conv Θ Ξ Δ P Q -> paths_conv Θ Ξ Δ P' Q.
Proof.
  intros * Hg * Hq Hq' H HP s Hs.
  pose proof (path_pairs_same _ _ Hg _ _ _ Hs _ Hq' Hq (fun X => iff_sym (H X))) as Hs0.
  pose proof (proj1 (same_denote_path _ _ Hg _ s _ _ Hq Hq' H)) as Hl.
  destruct (HP _ Hs0) as [H1 H2]; split.
  - intros X HX; exact (H1 _ (proj2 (Hl X) HX)).
  - intros X' HX'; destruct (H2 _ HX') as (X & HX & Hle); exists X; split; [ exact (proj1 (Hl X) HX) | exact Hle ].
Qed.

(** [mod_sim Θ Ξ Δ P P']: [P] and [P'] denote descriptions of one module
    part. *)
Definition mod_sim (Θ : gdeps) (Ξ : gstack) (Δ : ctx) (P P' : modexp) : Prop :=
  (forall X, mdenote Θ Ξ Δ P X -> exists X', mdenote Θ Ξ Δ P' X' /\ mdesc_mod X = mdesc_mod X') /\
  (forall X', mdenote Θ Ξ Δ P' X' -> exists X, mdenote Θ Ξ Δ P X /\ mdesc_mod X = mdesc_mod X').

(** An application is read from what the applied expression denotes. *)
Lemma mdenote_app_inv : forall Θ Ξ Δ P N X, mdenote Θ Ξ Δ (me_app P N) X -> exists R, mdenote Θ Ξ Δ P R /\ mdesc_at R N = Some X.
Proof. intros * H; inversion H; subst; try (cbn in *; discriminate); eauto. Qed.

(** A selection from an expression read through what it denotes is read
    from the module part of what it denotes. *)
Lemma mdenote_mem_obs_inv : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ P y X, obs_root Ξ P -> mdenote Θ Ξ Δ (me_mem P y) X ->
    exists R Rm Γy E rd R1, mdenote Θ Ξ Δ P R /\ mdesc_mod R = Some Rm /\ mdesc_entry Rm y = Some (Γy, E, rd) /\
      edenote Θ Ξ (Γy ++ Δ) (mdesc_entry_path Rm y) E R1 /\ mdesc_read rd R1 = Some X.
Proof.
  intros * Hg * Hq Hm; destruct (step_left_obs _ _ Hg _ _ (ps_mem y) _ Hq Hm) as (R & HR & _).
  assert (Hq0 : mod_qname (me_mem P y) = None \/ exists p, mod_qname (me_mem P y) = Some p /\ frame_free_path Ξ p)
    by exact (obs_root_step _ _ Hg _ (ps_mem y) Hq).
  inversion Hm as [? ? ? ? ? Hq1 Hu | ? ? ? ? ? ? ? ? ? Hq1 Hk | | | | ? ? ? R0 R0m Γy E rd R1 ? Hm0 Hmd He Hed Hr
                  | ? ? ? ? ? ? Hq1 Hk]; subst.
  - exfalso; destruct Hq0 as [Hn | (p0 & Hp0 & Hf)]; [ rewrite Hq1 in Hn; discriminate |].
    rewrite Hq1 in Hp0; injection Hp0 as <-; unfold gc_unit in Hu; rewrite Hq1 in Hu.
    destruct (gs_find_tele Ξ p) as [[[U0 [| ? ?]] T0] |] eqn:Et; try discriminate; [ exact (Hf _ _ Et) |].
    destruct Hq as [Hq | (p1 & Hq & _)]; cbn in Hq1; rewrite Hq in Hq1; [ discriminate |].
    injection Hq1 as <-; cbn in Hu; destruct (q_chain p1); discriminate.
  - exfalso; destruct Hq0 as [Hn | (p0 & Hp0 & Hf)]; [ rewrite Hq1 in Hn; discriminate |].
    rewrite Hq1 in Hp0; injection Hp0 as <-; destruct (gs_find_ind_tele _ _ _ Hk) as (U0 & T0 & Ht); exact (Hf _ _ Ht).
  - do 6 eexists; repeat split; eassumption.
  - exfalso; destruct Hq0 as [Hn | (p0 & Hp0 & Hf)]; [ rewrite Hq1 in Hn; discriminate |].
    rewrite Hq1 in Hp0; injection Hp0 as <-; destruct (gs_find_record_tele _ _ _ Hk) as (U0 & T0 & Ht); exact (Hf _ _ Ht).
Qed.

(** Selections of one member from two expressions of one module part,
    read through what they denote, denote the same. *)
Lemma mod_sim_mem : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ P P' y, obs_root Ξ P -> obs_root Ξ P' ->
    mod_sim Θ Ξ Δ P P' -> same_denote Θ Ξ Δ (me_mem P y) (me_mem P' y).
Proof.
  intros * Hg * Hq Hq' [H1 H2] X; split; intros HX.
  - destruct (mdenote_mem_obs_inv _ _ Hg _ _ _ _ Hq HX) as (R & Rm & Γy & E & rd & R1 & HR & Hmd & He & Hed & Hr).
    destruct (H1 _ HR) as (R' & HR' & Hmd'); econstructor; [ exact HR' | rewrite <- Hmd'; exact Hmd | exact He | exact Hed | exact Hr ].
  - destruct (mdenote_mem_obs_inv _ _ Hg _ _ _ _ Hq' HX) as (R' & Rm & Γy & E & rd & R1 & HR' & Hmd & He & Hed & Hr).
    destruct (H2 _ HR') as (R & HR & Hmd'); econstructor; [ exact HR | rewrite Hmd'; exact Hmd | exact He | exact Hed | exact Hr ].
Qed.

(** Applications of two expressions of one module part to one argument
    are of one module part, when the module part is there. *)
Lemma mod_sim_app : forall Θ Ξ Δ P P' N, mod_sim Θ Ξ Δ P P' ->
    (forall X, mdenote Θ Ξ Δ P X -> exists Xm, mdesc_mod X = Some Xm) -> mod_sim Θ Ξ Δ (me_app P N) (me_app P' N).
Proof.
  intros * [H1 H2] Hmod; split; intros X HX; destruct (mdenote_app_inv _ _ _ _ _ _ HX) as (R0 & Hm & Ha).
  - destruct (H1 _ Hm) as (R' & HR' & Hmd); destruct (Hmod _ Hm) as [Rm Em].
    destruct (proj1 (mdesc_at_mod_part _ _ N Em) _ Ha) as (Rm1 & Ha1 & Hm1).
    rewrite Em in Hmd; symmetry in Hmd; destruct (proj2 (mdesc_at_mod_part _ _ N Hmd) _ Ha1) as (X' & Ha' & Hm').
    exists X'; split; [ econstructor; eassumption | congruence ].
  - destruct (H2 _ Hm) as (R & HR & Hmd); destruct (Hmod _ HR) as [Rm Em].
    rewrite Em in Hmd; symmetry in Hmd; destruct (proj1 (mdesc_at_mod_part _ _ N Hmd) _ Ha) as (Rm1 & Ha1 & Hm1).
    destruct (proj2 (mdesc_at_mod_part _ _ N Em) _ Ha1) as (X0 & Ha0 & Hm0).
    exists X0; split; [ econstructor; eassumption | congruence ].
Qed.

(** Two descriptions of one expression have the module part one has. *)
Lemma mod_of_denote : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ P R Rm, mdenote Θ Ξ Δ P R -> mdesc_mod R = Some Rm ->
    forall X, mdenote Θ Ξ Δ P X -> exists Xm, mdesc_mod X = Some Xm.
Proof. intros * Hg * Hm Hmd X HX; rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HX _ Hm); eauto. Qed.

(** A description with a telescope has a module part. *)
Lemma mod_of_tele : forall R T, mdesc_mod_tele R = Some T -> exists Rm, mdesc_mod R = Some Rm.
Proof. intros * H; unfold mdesc_mod_tele in H; destruct (mdesc_mod R); [ eauto | discriminate ]. Qed.

(** Left paths from two expressions of one module part, read through what
    they denote: of one module part before any selection, denoting the
    same after one. *)
Lemma mod_sim_path_left : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ P s, path_pairs Θ Ξ Δ P s -> forall P', obs_root Ξ P -> obs_root Ξ P' ->
    mod_sim Θ Ξ Δ P P' ->
    (path_all_apps s = true -> mod_sim Θ Ξ Δ (path_left P s) (path_left P' s)) /\
    (path_all_apps s = false -> same_denote Θ Ξ Δ (path_left P s) (path_left P' s)).
Proof.
  intros Θ Ξ Hg Δ; induction 1 as [P | P y s Hs IH | P R T B T1 N N' s Hm Ht Hv HN Hs IH]; intros P' Hq Hq' H; cbn.
  - split; [ intros _; exact H | discriminate ].
  - split; [ discriminate | intros _ ].
    exact (proj1 (same_denote_path _ _ Hg _ s _ _ (obs_root_step _ _ Hg _ (ps_mem y) Hq) (obs_root_step _ _ Hg _ (ps_mem y) Hq')
                    (mod_sim_mem _ _ Hg _ _ _ _ Hq Hq' H))).
  - destruct (mod_of_tele _ _ Ht) as [Rm Hmd].
    apply IH; [ left; reflexivity | left; reflexivity |].
    exact (mod_sim_app _ _ _ _ _ _ H (mod_of_denote _ _ Hg _ _ _ _ Hm Hmd)).
Qed.

(** Paths with equal arguments of one of two expressions of one module
    part, read through what they denote, are of the other. *)
Lemma path_pairs_mod_sim : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ P s, path_pairs Θ Ξ Δ P s -> forall P', obs_root Ξ P -> obs_root Ξ P' ->
    mod_sim Θ Ξ Δ P P' -> path_pairs Θ Ξ Δ P' s.
Proof.
  intros Θ Ξ Hg Δ; induction 1 as [P | P y s Hs IH | P R T B T1 N N' s Hm Ht Hv HN Hs IH]; intros P' Hq Hq' H; [ constructor | |].
  - constructor; eapply path_pairs_same; [ exact Hg | exact Hs | exact (obs_root_step _ _ Hg _ (ps_mem y) Hq)
                                      | exact (obs_root_step _ _ Hg _ (ps_mem y) Hq') | exact (mod_sim_mem _ _ Hg _ _ _ _ Hq Hq' H) ].
  - destruct (proj1 H _ Hm) as (R' & Hm' & Hmd).
    econstructor; [ exact Hm' | unfold mdesc_mod_tele in *; rewrite <- Hmd; exact Ht | exact Hv | exact HN |].
    destruct (mod_of_tele _ _ Ht) as [Rm Hmd0].
    apply IH; [ left; reflexivity | left; reflexivity |].
    exact (mod_sim_app _ _ _ _ _ _ H (mod_of_denote _ _ Hg _ _ _ _ Hm Hmd0)).
Qed.

(** [mod_sim] the other way round. *)
Lemma mod_sim_sym : forall Θ Ξ Δ P P', mod_sim Θ Ξ Δ P P' -> mod_sim Θ Ξ Δ P' P.
Proof.
  intros * [H1 H2]; split; intros X HX; [ destruct (H2 _ HX) as (Y & HY & E) | destruct (H1 _ HX) as (Y & HY & E) ];
    exists Y; split; auto.
Qed.

(** Paths compared from one side compare from an expression of one
    module part, both read through what they denote, on the left. *)
Lemma paths_conv_mod_sim_left : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ P P' Q, obs_root Ξ P -> obs_root Ξ P' ->
    mod_sim Θ Ξ Δ P P' -> paths_conv Θ Ξ Δ P Q -> paths_conv Θ Ξ Δ P' Q.
Proof.
  intros * Hg * Hq Hq' H HP s Hs.
  pose proof (path_pairs_mod_sim _ _ Hg _ _ _ Hs _ Hq' Hq (mod_sim_sym _ _ _ _ _ H)) as Hs0.
  pose proof (mod_sim_path_left _ _ Hg _ _ _ Hs0 _ Hq Hq' H) as [Ha Hn].
  destruct (HP _ Hs0) as [H1 H2]; unfold path_leaf in *; split.
  - intros X' HX'; destruct (path_all_apps s) eqn:Es.
    + destruct (proj2 (Ha eq_refl) _ HX') as (X & HX & Hmd); destruct (H1 _ HX) as (X'' & HX'' & Hle).
      exists X''; split; [ exact HX'' | rewrite <- Hmd; exact Hle ].
    + exact (H1 _ (proj2 (Hn eq_refl X') HX')).
  - intros X'' HX''; destruct (H2 _ HX'') as (X & HX & Hle); destruct (path_all_apps s) eqn:Es.
    + destruct (proj1 (Ha eq_refl) _ HX) as (X' & HX' & Hmd).
      exists X'; split; [ exact HX' | rewrite <- Hmd; exact Hle ].
    + exists X; split; [ exact (proj1 (Hn eq_refl X) HX) | exact Hle ].
Qed.

(** The parent of a path naming an open frame denotes. *)
Lemma path_parent_denotes : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ Q y p U T0, mod_qname (me_mem Q y) = Some p ->
    gs_find_tele Ξ p = Some (U, nil, T0) -> exists R, mdenote Θ Ξ Δ Q R.
Proof.
  intros * Hg * Hq Ht; cbn in Hq; destruct (mod_qname Q) as [mq |] eqn:Hq0; [ injection Hq as <- | discriminate ].
  change {| q_unit := q_unit mq; q_chain := q_chain mq ++ y :: nil |} with (qname_in mq y) in Ht.
  destruct (frame_parent _ _ Hg _ _ _ _ Ht) as (T' & Φ' & Hf & _).
  destruct (qname_mod_denote _ _ Hg mq T' Φ' Δ (or_introl Hf)) as (R & HR & _).
  rewrite (mod_qname_inv _ _ Hq0); eauto.
Qed.

(** What the parent of a path naming an open frame denotes has a module
    part. *)
Lemma path_parent_mod : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ Q y p U T0 R, mod_qname (me_mem Q y) = Some p ->
    gs_find_tele Ξ p = Some (U, nil, T0) -> mdenote Θ Ξ Δ Q R -> exists Rm, mdesc_mod R = Some Rm.
Proof.
  intros * Hg * Hq Ht HR; cbn in Hq; destruct (mod_qname Q) as [mq |] eqn:Hq0; [ injection Hq as <- | discriminate ].
  change {| q_unit := q_unit mq; q_chain := q_chain mq ++ y :: nil |} with (qname_in mq y) in Ht.
  destruct (frame_parent _ _ Hg _ _ _ _ Ht) as (T' & Φ' & Hf & _).
  destruct (qname_mod_denote _ _ Hg mq T' Φ' Δ (or_introl Hf)) as (R' & HR' & Hsh).
  rewrite <- (mod_qname_inv _ _ Hq0) in HR'; rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR _ HR').
  destruct Hsh as [-> | (A & M & ->)]; cbn; eauto.
Qed.

(** What a selection reads from has a module part. *)
Lemma step_mem_mod : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ Q y X R, mdenote Θ Ξ Δ (me_mem Q y) X -> mdenote Θ Ξ Δ Q R ->
    exists Rm, mdesc_mod R = Some Rm.
Proof.
  intros * Hg * Hm HR.
  inversion Hm as [? ? p T Φ Hq Hu | ? ? p pq k D Mk Tm Φm Hq Hk HMk Hl | | | | ? ? ? R0 R0m Γy E rd R1 ? Hm0 Hd0 He Hed Hrd
                  | ? ? p Rr Tm Φm Hq Hk Hl]; subst.
  - unfold gc_unit in Hu; rewrite Hq in Hu.
    destruct (gs_find_tele Ξ p) as [[[U0 [| ? ?]] T0] |] eqn:Et; try discriminate.
    + exact (path_parent_mod _ _ Hg _ _ _ _ _ _ _ Hq Et HR).
    + exfalso; cbn in Hq; destruct (mod_qname Q); [| discriminate ]; injection Hq as <-; cbn in Hu; destruct (q_chain _); discriminate.
  - destruct (gs_find_ind_tele _ _ _ Hk) as (U0 & T0 & Ht); exact (path_parent_mod _ _ Hg _ _ _ _ _ _ _ Hq Ht HR).
  - rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR _ Hm0); eauto.
  - destruct (gs_find_record_tele _ _ _ Hk) as (U0 & T0 & Ht); exact (path_parent_mod _ _ Hg _ _ _ _ _ _ _ Hq Ht HR).
Qed.
(** What a step reads denotes. *)
Lemma step_left_back : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ Q st X, mdenote Θ Ξ Δ (step_left Q st) X -> exists R, mdenote Θ Ξ Δ Q R.
Proof.
  intros * Hg * Hm; destruct st as [y | N N']; cbn in Hm.
  - inversion Hm as [? ? p T Φ Hq Hu | ? ? p pq k D Mk Tm Φm Hq Hk HMk Hl | | | | ? ? ? R0 R0m Γy E rd R1 ? Hm0 Hd0 He Hed Hrd
                    | ? ? p Rr Tm Φm Hq Hk Hl]; subst.
    + unfold gc_unit in Hu; rewrite Hq in Hu.
      destruct (gs_find_tele Ξ p) as [[[U0 [| ? ?]] T0] |] eqn:Et; try discriminate.
      * exact (path_parent_denotes _ _ Hg _ _ _ _ _ _ Hq Et).
      * exfalso; cbn in Hq; destruct (mod_qname Q); [| discriminate ]; injection Hq as <-; cbn in Hu; destruct (q_chain _); discriminate.
    + destruct (gs_find_ind_tele _ _ _ Hk) as (U0 & T0 & Ht); exact (path_parent_denotes _ _ Hg _ _ _ _ _ _ Hq Ht).
    + eauto.
    + destruct (gs_find_record_tele _ _ _ Hk) as (U0 & T0 & Ht); exact (path_parent_denotes _ _ Hg _ _ _ _ _ _ Hq Ht).
  - destruct (mdenote_app_inv _ _ _ _ _ _ Hm) as (R & HR & _); eauto.
Qed.

(** What a path reads from denotes. *)
Lemma path_left_back : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ s Q X, mdenote Θ Ξ Δ (path_left Q s) X -> exists R, mdenote Θ Ξ Δ Q R.
Proof.
  intros Θ Ξ Hg Δ s; induction s as [| [y | N N'] s IH]; intros Q X Hm; cbn in Hm; [ eauto | |].
  - destruct (IH _ _ Hm) as (R1 & HR1); exact (step_left_back _ _ Hg _ _ (ps_mem y) _ HR1).
  - destruct (IH _ _ Hm) as (R1 & HR1); exact (step_left_back _ _ Hg _ _ (ps_app N N') _ HR1).
Qed.

(** The same on the right. *)
Lemma path_right_back : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ s Q X, mdenote Θ Ξ Δ (path_right Q s) X -> exists R, mdenote Θ Ξ Δ Q R.
Proof. intros * Hg * Hm; rewrite <- (proj1 (path_swap_sides s Q)) in Hm; exact (path_left_back _ _ Hg _ _ _ _ Hm). Qed.

(** A parameter typed at a universe or at the types of levels is typed at
    an evaluated sort. *)
Lemma param_typed_evaluated : forall Θ Ξ Γ B l, param_typed Θ Ξ Γ B l -> exists Srt, evaluated_sort Srt /\ Θ ⍮ Ξ ⍮ Γ ⊢ B : Srt.
Proof. intros * [H | H]; eexists; (split; [ constructor | exact H ]). Qed.

(** The outermost parameter of a typed module, read where it is, is
    typed at an evaluated sort. *)
Lemma desc_ok_head_evaluated : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ Rm T B T1, desc_ok Θ Ξ Γ Rm -> mdesc_canonical Θ Ξ Rm ->
    mdesc_tele Rm = Some T -> tele_view T = Some (B, T1) -> exists Srt, evaluated_sort Srt /\ Θ ⍮ Ξ ⍮ Γ ⊢ B : Srt.
Proof.
  intros * Hg * Hok Hc Ht Hv; pose proof (gctx_valid_syn _ _ Hg) as Hvs.
  destruct Hok as [| Γ Δ Φw Φ l HΦ _ _ HaΔ _ _ _ HRΔ _ _ | Γ Θ' T0 Φ Ns Θ0 Ξ0 p l _ _ _ HaT0 _ HT0 HΘ' Hargs HaΘ' HpΘ' _ _ |];
    cbn in Ht, Hc; try discriminate.
  - injection Ht as <-; destruct (tele_view_ass _ _ _ HaΔ Hv) as [κ ->].
    apply (param_typed_evaluated _ _ _ _ l); exact (HRΔ _ _ _ nil eq_refl).
  - destruct (Nat.leb (length Ns) (length T0)) eqn:Hle; [ injection Ht as <- | discriminate ].
    destruct (tele_view Θ') as [[B' Y1] |] eqn:Hv'.
    + destruct (tele_view_app_r (tele_sub (firstn (length T0 - length Ns) T0) (sb_of_list Id Ns)) _ _ _ Hv') as [Y1' Hv2].
      rewrite Hv in Hv2; injection Hv2 as <- _.
      destruct (tele_view_ass _ _ _ HaΘ' Hv') as [κ ->].
      apply (param_typed_evaluated _ _ _ _ l); exact (HpΘ' _ _ _ nil eq_refl).
    + pose proof (tele_view_none_ass _ HaΘ' Hv') as ->; rewrite List.app_nil_r in Hv; cbn [List.app] in Hargs.
      destruct Hargs as [T2 T3 -> Hl Ha Hs HT3 HN].
      rewrite List.length_app, <- Hl, Nat.add_sub, List.firstn_app, Nat.sub_diag, List.firstn_all, List.firstn_O,
        List.app_nil_r, tele_view_sub in Hv.
      destruct (tele_view T2) as [[B0 X1] |] eqn:Hv0; cbn in Hv; [ injection Hv as <- _ | discriminate ].
      destruct (proj1 (List.Forall_app _ _ _) HaT0) as [Ha2 _].
      destruct (tele_view_ass _ _ _ Ha2 Hv0) as [κ ->].
      destruct (loc_params_evaluated _ _ _ _ _ Hvs Hc) as [l' Hl'].
      destruct (param_typed_evaluated _ _ _ _ _ (Hl' X1 κ B0 T3 ltac:(rewrite <- List.app_assoc; reflexivity))) as (S & HS & HB0).
      assert (Hσ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Ns : T3 ++ nil).
      { eapply wf_sub_of_list; [ exact Ha | rewrite List.app_nil_r; exact (ctx_app_wf_right _ _ _ _ HT0)
                               | exact (wf_sub_to_nil _ _ _ HΘ') | symmetry; exact Hl | exact HN ]. }
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB0 Hσ) as HB.
      exists S; split; [ exact HS |]; inversion HS; subst; exact HB.
Qed.

(** *** Paths up to Units

    It is enough to compare paths up to the units of their leaves
    ([paths_core]) when the two expressions are equal: two leaves stand
    for the units of their paths ([lookup_sound]), and the paths are equal
    ([path_eq]). *)

(** [path_leaf] up to the units of the leaves. *)
Definition path_core (Θ : gdeps) (Ξ : gstack) (Δ : ctx) (s : list path_step) (X X' : mdesc) : Prop :=
  if path_all_apps s then opt_rel (leaf_core Θ Ξ Δ) (mdesc_mod X) (mdesc_mod X') else leaf_core Θ Ξ Δ X X'.

(** [paths_rel] up to the units of the leaves. *)
Definition paths_core (Θ : gdeps) (Ξ : gstack) (Δ : ctx) : modexp -> modexp -> Prop :=
  paths_rel Θ Ξ Δ (path_core Θ Ξ Δ).

(** The leaves of two descriptions show the same of their module parts,
    up to units. *)
Lemma leaf_core_mod_opt : forall Θ Ξ Δ X X', leaf_core Θ Ξ Δ X X' -> opt_rel (leaf_core Θ Ξ Δ) (mdesc_mod X) (mdesc_mod X').
Proof.
  intros * [Hk Ht Hr Hm Hh Hf Hn].
  destruct (mdesc_mod X) as [Xm |] eqn:E; destruct (mdesc_mod X') as [Xm' |] eqn:E'; cbn in Hm |- *; try contradiction; [| exact I ].
  destruct (mdesc_is_mod_parts _ (mdesc_mod_is_mod _ _ E)) as (Hk1 & Ht1 & Hr1).
  destruct (mdesc_is_mod_parts _ (mdesc_mod_is_mod _ _ E')) as (Hk2 & Ht2 & Hr2).
  constructor.
  - congruence.
  - rewrite Ht1, Ht2; exact I.
  - intros A HA; congruence.
  - rewrite (mdesc_mod_idem _ _ E), (mdesc_mod_idem _ _ E'); exact I.
  - unfold mdesc_head in *; rewrite (mdesc_mod_tele_mod_part _ _ E), (mdesc_mod_tele_mod_part _ _ E'); exact Hh.
  - unfold desc_reads_frame in *; rewrite (mdesc_mod_idem _ _ E), (mdesc_mod_idem _ _ E'); rewrite E, E' in Hf; exact Hf.
  - rewrite <- (no_level_mod_iff _ _ _ _ _ E), <- (no_level_mod_iff _ _ _ _ _ E'); exact Hn.
Qed.

(** Paths from two selections of one member, up to units. *)
Lemma paths_core_mem : forall Θ Ξ Δ P P' y, paths_core Θ Ξ Δ P P' -> paths_core Θ Ξ Δ (me_mem P y) (me_mem P' y).
Proof.
  intros * H s Hs; destruct (H (ps_mem y :: s) (path_pairs_mem _ _ _ _ _ _ Hs)) as [H1 H2]; cbn [path_left path_right] in H1, H2.
  unfold path_core in *; cbn [path_all_apps] in H1, H2; split.
  - intros X HX; destruct (H1 _ HX) as (X' & HX' & Hl); exists X'; split; [ exact HX' |].
    destruct (path_all_apps s); [ exact (leaf_core_mod_opt _ _ _ _ _ Hl) | exact Hl ].
  - intros X' HX'; destruct (H2 _ HX') as (X & HX & Hl); exists X; split; [ exact HX |].
    destruct (path_all_apps s); [ exact (leaf_core_mod_opt _ _ _ _ _ Hl) | exact Hl ].
Qed.

(** Paths from two applications to equal arguments, up to units. *)
Lemma paths_core_app : forall Θ Ξ Δ P P' R T B T1 N N',
    paths_core Θ Ξ Δ P P' -> mdenote Θ Ξ Δ P R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) ->
    Θ ⍮ Ξ ⍮ Δ ⊢ N ≈ N' : B -> paths_core Θ Ξ Δ (me_app P N) (me_app P' N').
Proof. intros * H Hm Ht Hv HN s Hs; exact (H (ps_app N N' :: s) (path_pairs_app _ _ _ _ _ _ _ _ _ _ _ Hm Ht Hv HN Hs)). Qed.

(** The heads of two module parts related up to units refine each other. *)
Lemma head_core_arg_mod : forall Θ Ξ Δ R R' T B T1 N N', opt_rel (leaf_core Θ Ξ Δ) (mdesc_mod R) (mdesc_mod R') ->
    mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) -> Θ ⍮ Ξ ⍮ Δ ⊢ N ≈ N' : B ->
    exists T' B' T1', mdesc_mod_tele R' = Some T' /\ tele_view T' = Some (B', T1') /\ Θ ⍮ Ξ ⍮ Δ ⊢ N ≈ N' : B' /\
      Θ ⍮ Ξ ⍮ Δ ⊢ B ⊆ B' /\ Θ ⍮ Ξ ⍮ Δ ⊢ B' ⊆ B.
Proof.
  intros * Hl Ht Hv HN.
  destruct (mdesc_mod R) as [Rm |] eqn:Em; [| unfold mdesc_mod_tele in Ht; rewrite Em in Ht; discriminate ].
  destruct (mdesc_mod R') as [Rm' |] eqn:Em'; cbn in Hl; [| contradiction ].
  rewrite <- (mdesc_mod_tele_mod_part _ _ Em) in Ht; rewrite <- (mdesc_mod_tele_mod_part _ _ Em').
  pose proof (core_head _ _ _ _ _ Hl) as Hh; rewrite (mdesc_head_of _ _ _ _ Ht Hv) in Hh.
  destruct (mdesc_head Rm') as [B' |] eqn:EB'; cbn in Hh; [| contradiction ]; destruct Hh as [H1 H2].
  destruct (mdesc_head_inv _ _ EB') as (T' & T1' & Ht' & Hv').
  exists T', B', T1'; repeat split; try assumption; exact (wf_exp_eq_subtyp' _ _ _ _ _ _ _ HN H1).
Qed.

(** The descriptions of a well-formed module expression's selections are
    typed. *)
Lemma sel_desc_ok : forall Θ Ξ Δ P P' y X, Θ ⍮ Ξ ⍮ Δ ⊢ᵐ P ≈ P' -> mdenote Θ Ξ Δ (me_mem P y) X -> desc_ok Θ Ξ Δ X.
Proof.
  intros * HP Hm; pose proof (presup_modexp_eq_ctx HP) as HΔ; pose proof (ctx_wf_gctx _ _ _ HΔ) as Hg.
  pose proof (gctx_valid_syn _ _ Hg) as Hv.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ HP Hv) as (_ & HR & _).
  exact (desc_ok_mem _ _ Hg Hv _ _ _ _ HΔ HR Hm).
Qed.

(** A typed module description has a telescope. *)
Lemma desc_ok_mod_tele : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ X Xm, desc_ok Θ Ξ Δ X -> mdesc_mod X = Some Xm ->
    exists T, mdesc_mod_tele X = Some T.
Proof.
  intros * Hg * Hok Hm; destruct (desc_ok_tele _ _ _ _ (desc_ok_mod _ _ Hg _ _ _ Hok Hm) (mdesc_mod_is_mod _ _ Hm)) as [T HT].
  exists T; unfold mdesc_mod_tele; rewrite Hm; exact HT.
Qed.

(** Two equal module expressions, followed along a path, are equal where
    the path reaches a module. *)
Lemma path_eq : forall Θ Ξ Δ P s, path_pairs Θ Ξ Δ P s -> forall P', Θ ⍮ Ξ ⍮ Δ ⊢ᵐ P ≈ P' -> paths_core Θ Ξ Δ P P' ->
    forall X X' Xm, mdenote Θ Ξ Δ (path_left P s) X -> mdenote Θ Ξ Δ (path_right P' s) X' -> mdesc_mod X = Some Xm ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵐ path_left P s ≈ path_right P' s.
Proof.
  induction 1 as [P | P y s Hs IH | P R T B T1 N N' s Hm Ht Hv HN Hs IH]; intros P' HP HC X X' Xm HX HX' HXm; cbn in HX, HX' |- *.
  - exact HP.
  - pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HP)) as Hg.
    destruct (path_left_back _ _ Hg _ _ _ _ HX) as (R1 & HR1).
    destruct (path_right_back _ _ Hg _ _ _ _ HX') as (R1' & HR1').
    (* both selections are modules *)
    assert (Hmod1 : exists R1m, mdesc_mod R1 = Some R1m).
    { destruct Hs as [| ? z s' Hs' | ? R2 T2 B2 T12 N2 N2' s' Hm2 Ht2 _ _ _]; cbn in HX.
      - rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR1 _ HX); eauto.
      - destruct (path_left_back _ _ Hg _ _ _ _ HX) as (R3 & HR3); exact (step_mem_mod _ _ Hg _ _ _ _ _ HR3 HR1).
      - rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR1 _ Hm2); exact (mod_of_tele _ _ Ht2). }
    destruct Hmod1 as [R1m Hd1].
    destruct (proj1 (HC (ps_mem y :: nil) (path_pairs_mem _ _ _ _ _ _ (path_pairs_nil _ _ _ _))) _ HR1) as (R1'' & HR1'' & Hl1).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR1'' _ HR1') in Hl1; cbn in Hl1.
    pose proof (core_mod _ _ _ _ _ Hl1) as Hmods; rewrite Hd1 in Hmods.
    destruct (mdesc_mod R1') as [R1m' |] eqn:Hd1'; cbn in Hmods; [| contradiction ].
    destruct (desc_ok_mod_tele _ _ Hg _ _ _ (sel_desc_ok _ _ _ _ _ _ _ HP HR1) Hd1) as [T1a HT1].
    destruct (desc_ok_mod_tele _ _ Hg _ _ _ (sel_desc_ok _ _ _ _ _ _ _ (wf_me_sym _ _ _ _ _ HP) HR1') Hd1') as [T1b HT1'].
    refine (IH (me_mem P' y) _ (paths_core_mem _ _ _ _ _ _ HC) _ _ _ HX HX' HXm).
    eapply wf_me_mem; [ exact HP | exact HR1 | exact HT1 | exact HR1' | exact HT1' ].
  - pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HP)) as Hg.
    destruct (proj1 (HC nil (path_pairs_nil _ _ _ _)) _ Hm) as (R' & HR' & Hl); cbn in Hl.
    destruct (head_core_arg_mod _ _ _ _ _ _ _ _ _ _ Hl Ht Hv HN) as (T' & B' & T1' & Ht' & Hv' & HN' & HBB & HB'B).
    destruct (desc_of_props _ _ _ _ (ex_intro _ _ (conj (wf_modexp_eq_refl_left HP) Hm))) as (_ & Hok & Hc & _).
    destruct (desc_of_props _ _ _ _ (ex_intro _ _ (conj (wf_modexp_eq_refl_right HP) HR'))) as (_ & Hok' & Hc' & _).
    destruct (mod_of_tele _ _ Ht) as [Rm HRm]; destruct (mod_of_tele _ _ Ht') as [Rm' HRm'].
    rewrite <- (mdesc_mod_tele_mod_part _ _ HRm) in Ht; rewrite <- (mdesc_mod_tele_mod_part _ _ HRm') in Ht'.
    unfold mdesc_mod_tele in Ht, Ht'; rewrite (mdesc_mod_idem _ _ HRm) in Ht; rewrite (mdesc_mod_idem _ _ HRm') in Ht'.
    destruct (desc_ok_head_evaluated _ _ Hg _ _ _ _ _ (desc_ok_mod _ _ Hg _ _ _ Hok HRm) (mdesc_canonical_mod _ _ _ _ Hc HRm) Ht Hv)
      as (S & HS & HB).
    destruct (desc_ok_head_evaluated _ _ Hg _ _ _ _ _ (desc_ok_mod _ _ Hg _ _ _ Hok' HRm') (mdesc_canonical_mod _ _ _ _ Hc' HRm') Ht' Hv')
      as (S' & HS' & HB').
    eapply (IH (me_app P' N')); [| exact (paths_core_app _ _ _ _ _ _ _ _ _ _ _ HC Hm
                                           ltac:(unfold mdesc_mod_tele; rewrite HRm; exact Ht) Hv HN)
                                 | exact HX | exact HX' | exact HXm ].
    eapply wf_me_app; [ exact HP | exact Hm | unfold mdesc_mod_tele; rewrite HRm; exact Ht | exact Hv | exact HB | exact HS
                      | exact (presup_exp_eq_left HN) | exact HN | exact HR' | unfold mdesc_mod_tele; rewrite HRm'; exact Ht' | exact Hv'
                      | exact HB' | exact HS' | exact (presup_exp_eq_right HN') ].
Qed.

(** Paths compared up to units are compared, from equal expressions. *)
Lemma paths_conv_of_core : forall Θ Ξ Δ P P', Θ ⍮ Ξ ⍮ Δ ⊢ᵐ P ≈ P' -> paths_core Θ Ξ Δ P P' -> paths_conv Θ Ξ Δ P P'.
Proof.
  intros * HP HC s Hs.
  assert (Hup : forall X X', mdenote Θ Ξ Δ (path_left P s) X -> mdenote Θ Ξ Δ (path_right P' s) X' ->
            opt_rel (fun _ _ => True) (mdesc_mod X) (mdesc_mod X') ->
            opt_rel (fun Rm Rm' => Θ ⍮ Ξ ⍮ Δ ⊢ᵐ mdesc_unit Rm ≈ mdesc_unit Rm') (mdesc_mod X) (mdesc_mod X')).
  { intros X X' HX HX' Hm; destruct (mdesc_mod X) as [Xm |] eqn:E; destruct (mdesc_mod X') as [Xm' |] eqn:E'; cbn in Hm |- *;
      try contradiction; [| exact I ].
    pose proof (path_eq _ _ _ _ _ Hs _ HP HC _ _ _ HX HX' E) as Heq.
    eapply wf_me_trans; [ apply wf_me_sym; exact (lookup_sound _ _ _ _ _ _ (wf_modexp_eq_refl_left Heq) HX E) |].
    eapply wf_me_trans; [ exact Heq | exact (lookup_sound _ _ _ _ _ _ (wf_modexp_eq_refl_right Heq) HX' E') ]. }
  assert (Hleaf : forall X X', mdenote Θ Ξ Δ (path_left P s) X -> mdenote Θ Ξ Δ (path_right P' s) X' ->
            path_core Θ Ξ Δ s X X' -> path_leaf Θ Ξ Δ s X X').
  { unfold path_core, path_leaf; intros X X' HX HX' Hl; destruct (path_all_apps s).
    - pose proof (Hup _ _ HX HX') as Hu.
      destruct (mdesc_mod X) as [Xm |] eqn:E; destruct (mdesc_mod X') as [Xm' |] eqn:E'; cbn in Hl |- *;
        try contradiction; [| exact I ].
      apply leaf_conv_of_core; [ exact Hl |]; rewrite (mdesc_mod_idem _ _ E), (mdesc_mod_idem _ _ E'); cbn.
      specialize (Hu I); cbn in Hu; exact Hu.
    - apply leaf_conv_of_core; [ exact Hl | exact (Hup _ _ HX HX' (core_mod _ _ _ _ _ Hl)) ]. }
  destruct (HC _ Hs) as [H1 H2]; split.
  - intros X HX; destruct (H1 _ HX) as (X' & HX' & Hl); exists X'; split; [ exact HX' | exact (Hleaf _ _ HX HX' Hl) ].
  - intros X' HX'; destruct (H2 _ HX') as (X & HX & Hl); exists X; split; [ exact HX | exact (Hleaf _ _ HX HX' Hl) ].
Qed.

(** *** Composing [modexp_conv] *)

(** [modexp_conv] the other way round. *)
Lemma modexp_conv_sym : forall Θ Ξ Γ H H', modexp_conv Θ Ξ Γ H H' -> modexp_conv Θ Ξ Γ H' H.
Proof. intros * HH Δ σ σ' Hσ; apply paths_conv_sym; exact (HH _ _ _ (wf_sub_eq_sym _ _ _ _ _ _ Hσ)). Qed.

(** [modexp_conv] chained. *)
Lemma modexp_conv_trans : forall Θ Ξ Γ H H' H'', modexp_conv Θ Ξ Γ H H' -> modexp_conv Θ Ξ Γ H' H'' -> modexp_conv Θ Ξ Γ H H''.
Proof.
  intros * H1 H2 Δ σ σ' Hσ; eapply paths_conv_trans; [ exact (H1 _ _ _ Hσ) |].
  exact (H2 _ _ _ (wf_sub_eq_refl _ _ _ _ _ (wf_sub_eq_right _ _ _ _ _ _ Hσ))).
Qed.

(** Two selections of one member. *)
Lemma modexp_conv_mem : forall Θ Ξ Γ H H' y, modexp_conv Θ Ξ Γ H H' -> modexp_conv Θ Ξ Γ (me_mem H y) (me_mem H' y).
Proof. intros * HH Δ σ σ' Hσ; cbn; apply paths_conv_mem; exact (HH _ _ _ Hσ). Qed.

(** Two applications to equal arguments of the outermost parameter. *)
Lemma modexp_conv_app : forall Θ Ξ Γ H H' R T B T1 N N', modexp_conv Θ Ξ Γ H H' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ H R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : B -> modexp_conv Θ Ξ Γ (me_app H N) (me_app H' N').
Proof.
  intros * HH Hw Hm Ht Hv HN Δ σ σ' Hσ; cbn.
  pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hσl.
  eapply paths_conv_app;
    [ exact (HH _ _ _ Hσ) | exact (wf_sub_mdenote _ _ _ _ _ _ _ _ Hw Hm Hσl)
    | exact (mdesc_mod_tele_sub _ _ σ _ (wf_mdenote_scoped _ _ _ _ _ _ Hw Hm) Ht)
    | rewrite tele_view_sub, Hv; reflexivity |].
  cbn [fst]; eapply wf_exp_eq_trans; [ exact (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HN Hσl) |].
  exact (sub_eq_preserves_exp _ _ _ _ _ (presup_exp_eq_right HN) _ _ _ Hσ).
Qed.

(** [modexp_conv] moved along a weakening. *)
Lemma modexp_conv_wk : forall Θ Ξ Γ Δ1 H H' φ, modexp_conv Θ Ξ Γ H H' -> Θ ⍮ Ξ ⍮ Δ1 ⊢ʷ φ : Γ ->
    modexp_conv Θ Ξ Δ1 (modexp_wk H φ) (modexp_wk H' φ).
Proof.
  intros * HH Hφ Δ σ σ' Hσ; rewrite !modexp_sub_wk; apply HH.
  eapply wf_sub_eq_compose_right; [ exact (wf_sub_of_wk _ _ _ _ _ Hφ) | exact Hσ ].
Qed.

(** [obs_sub Ξ Γ H]: [H] is read through what it denotes under any
    substitution into [Γ] ([obs_root]). *)
Definition obs_sub (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (H : modexp) : Prop :=
  forall Δ σ, Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ -> obs_root Ξ H[σ]ᵐ.

(** A slot names no path under a substitution. *)
Lemma obs_sub_var : forall Θ Ξ Γ x U, Γ ∋ #x ≔ₘ U -> obs_sub Θ Ξ Γ (me_var x).
Proof.
  intros * Hx Δ σ Hσ; left; cbn; destruct (wf_sub_apply_mod _ _ _ _ _ Hσ _ _ Hx) as [[-> _] | (y & -> & _)]; reflexivity.
Qed.

(** Neither does a literal. *)
Lemma obs_sub_lit : forall Θ Ξ Γ U, obs_sub Θ Ξ Γ (me_lit U).
Proof. intros * Δ σ Hσ; left; reflexivity. Qed.

(** Nor an application. *)
Lemma obs_sub_app : forall Θ Ξ Γ H N, obs_sub Θ Ξ Γ (me_app H N).
Proof. intros * Δ σ Hσ; left; reflexivity. Qed.

(** A path is moved by no substitution. *)
Lemma modexp_sub_path : forall H p σ, mod_qname H = Some p -> H[σ]ᵐ = H.
Proof.
  induction H as [fp | x | H IH y | H IH N | U]; intros p σ Hq; cbn in Hq |- *; try discriminate; [ reflexivity |].
  destruct (mod_qname H) as [q0 |] eqn:Eq; [| discriminate ]; rewrite (IH q0 σ eq_refl); reflexivity.
Qed.

(** A path of no open frame is read through what it denotes. *)
Lemma obs_sub_path : forall Θ Ξ Γ H p, mod_qname H = Some p -> frame_free_path Ξ p -> obs_sub Θ Ξ Γ H.
Proof. intros * Hq Hp Δ σ Hσ; right; exists p; rewrite (modexp_sub_path _ _ σ Hq); split; assumption. Qed.

(** An expression naming no path that denotes names no path under a
    substitution: its slots go to slots or literals. *)
Lemma nopath_sub_mod_qname : forall Θ Ξ Γ H R, mdenote Θ Ξ Γ H R -> mod_qname H = None ->
    forall Δ σ, Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ -> mod_qname H[σ]ᵐ = None.
Proof.
  intros * Hm; revert Hm; revert R; induction H as [fp | x | H IH y | H IH N | U]; intros R Hm Hq Δ σ Hσ;
    cbn in Hq |- *; try discriminate; try reflexivity.
  - inversion Hm; subst; try (cbn in *; discriminate).
    match goal with Hx : _ ∋ #x ≔ₘ _ |- _ =>
      destruct (wf_sub_apply_mod _ _ _ _ _ Hσ _ _ Hx) as [[-> _] | (z & -> & _)]; reflexivity end.
  - destruct (mod_qname H) eqn:Eq; [ discriminate |].
    inversion Hm; subst; try (cbn in *; rewrite Eq in *; discriminate).
    match goal with Hm0 : mdenote _ _ _ H _ |- _ => rewrite (IH _ Hm0 eq_refl _ _ Hσ); reflexivity end.
Qed.

(** An expression that denotes a description reading no open frame is
    read through what it denotes under any substitution. *)
Lemma obs_sub_of_frame_free : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ H R, mdenote Θ Ξ Γ H R -> ~ desc_reads_frame Ξ R ->
    obs_sub Θ Ξ Γ H.
Proof.
  intros * Hg * Hm Hn; destruct (mod_qname H) as [p |] eqn:Eq.
  - exact (obs_sub_path _ _ _ _ _ Eq (frame_free_of_desc _ _ Hg _ _ _ _ Eq Hm Hn)).
  - intros Δ σ Hσ; left; exact (nopath_sub_mod_qname _ _ _ _ _ Hm Eq _ _ Hσ).
Qed.

(** Two well-formed expressions of one description, read through what
    they denote, are interchangeable on the left of [modexp_conv]. *)
Lemma modexp_conv_replace_left : forall Θ Ξ Γ H1 H2 K R, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H1 ≈ H1 -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H2 ≈ H2 ->
    mdenote Θ Ξ Γ H1 R -> mdenote Θ Ξ Γ H2 R -> obs_sub Θ Ξ Γ H1 -> obs_sub Θ Ξ Γ H2 ->
    modexp_conv Θ Ξ Γ H1 K -> modexp_conv Θ Ξ Γ H2 K.
Proof.
  intros * Hw1 Hw2 Hm1 Hm2 Hq1 Hq2 HK Δ σ σ' Hσ; pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hσl.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx Hw1)) as Hg.
  eapply paths_conv_same_left; [ exact Hg | exact (Hq1 _ _ Hσl) | exact (Hq2 _ _ Hσl) | | exact (HK _ _ _ Hσ) ].
  eapply same_denote_of; [ exact Hg | exact (wf_sub_mdenote _ _ _ _ _ _ _ _ Hw1 Hm1 Hσl) | exact (wf_sub_mdenote _ _ _ _ _ _ _ _ Hw2 Hm2 Hσl) ].
Qed.

(** The same on the right. *)
Lemma modexp_conv_replace_right : forall Θ Ξ Γ H1 H2 K R, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H1 ≈ H1 -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H2 ≈ H2 ->
    mdenote Θ Ξ Γ H1 R -> mdenote Θ Ξ Γ H2 R -> obs_sub Θ Ξ Γ H1 -> obs_sub Θ Ξ Γ H2 ->
    modexp_conv Θ Ξ Γ K H1 -> modexp_conv Θ Ξ Γ K H2.
Proof.
  intros * Hw1 Hw2 Hm1 Hm2 Hq1 Hq2 HK; apply modexp_conv_sym; apply modexp_conv_sym in HK.
  exact (modexp_conv_replace_left _ _ _ _ _ _ _ Hw1 Hw2 Hm1 Hm2 Hq1 Hq2 HK).
Qed.

(** Two descriptions of one module part have one module part under a
    substitution. *)
Lemma mdesc_mod_sub_eq : forall R1 R2 σ, mdesc_mod R1 = mdesc_mod R2 -> mdesc_mod (mdesc_sub R1 σ) = mdesc_mod (mdesc_sub R2 σ).
Proof.
  intros * H; destruct (mdesc_mod R1) as [Rm |] eqn:E1.
  - rewrite (mdesc_mod_sub _ _ σ E1); symmetry in H; rewrite (mdesc_mod_sub _ _ σ H); reflexivity.
  - destruct (mdesc_mod (mdesc_sub R1 σ)) as [X1 |] eqn:F1;
      [ destruct (mdesc_mod_sub_inv _ _ _ F1) as (? & HX & _); congruence |].
    destruct (mdesc_mod (mdesc_sub R2 σ)) as [X2 |] eqn:F2;
      [ destruct (mdesc_mod_sub_inv _ _ _ F2) as (? & HX & _); congruence | reflexivity ].
Qed.

(** Two well-formed expressions of one module part, read through what
    they denote, are interchangeable on the left of [modexp_conv]. *)
Lemma modexp_conv_replace_mod_left : forall Θ Ξ Γ H1 H2 K R1 R2, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H1 ≈ H1 -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H2 ≈ H2 ->
    mdenote Θ Ξ Γ H1 R1 -> mdenote Θ Ξ Γ H2 R2 -> mdesc_mod R1 = mdesc_mod R2 -> obs_sub Θ Ξ Γ H1 -> obs_sub Θ Ξ Γ H2 ->
    modexp_conv Θ Ξ Γ H1 K -> modexp_conv Θ Ξ Γ H2 K.
Proof.
  intros * Hw1 Hw2 Hm1 Hm2 Hmd Hq1 Hq2 HK Δ σ σ' Hσ; pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hσl.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx Hw1)) as Hg.
  pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ Hw1 Hm1 Hσl) as Hm1σ; pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ Hw2 Hm2 Hσl) as Hm2σ.
  eapply paths_conv_mod_sim_left; [ exact Hg | exact (Hq1 _ _ Hσl) | exact (Hq2 _ _ Hσl) | | exact (HK _ _ _ Hσ) ].
  split; intros X HX.
  - rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HX _ Hm1σ); exists (mdesc_sub R2 σ); split; [ exact Hm2σ |].
    exact (mdesc_mod_sub_eq _ _ σ Hmd).
  - rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HX _ Hm2σ); exists (mdesc_sub R1 σ); split; [ exact Hm1σ |].
    exact (mdesc_mod_sub_eq _ _ σ Hmd).
Qed.

(** The same on the right. *)
Lemma modexp_conv_replace_mod_right : forall Θ Ξ Γ H1 H2 K R1 R2, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H1 ≈ H1 -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H2 ≈ H2 ->
    mdenote Θ Ξ Γ H1 R1 -> mdenote Θ Ξ Γ H2 R2 -> mdesc_mod R1 = mdesc_mod R2 -> obs_sub Θ Ξ Γ H1 -> obs_sub Θ Ξ Γ H2 ->
    modexp_conv Θ Ξ Γ K H1 -> modexp_conv Θ Ξ Γ K H2.
Proof.
  intros * Hw1 Hw2 Hm1 Hm2 Hmd Hq1 Hq2 HK; apply modexp_conv_sym; apply modexp_conv_sym in HK.
  exact (modexp_conv_replace_mod_left _ _ _ _ _ _ _ _ Hw1 Hw2 Hm1 Hm2 Hmd Hq1 Hq2 HK).
Qed.

(** A slot is compared with itself as its unit is. *)
Lemma modexp_conv_slot : forall Θ Ξ Γ x U, ⊢ Θ ⍮ Ξ ⍮ Γ -> Γ ∋ #x ≔ₘ U -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    modexp_conv Θ Ξ Γ (me_lit U) (me_lit U) -> modexp_conv Θ Ξ Γ (me_var x) (me_var x).
Proof.
  intros * HΓ Hx HU HUU.
  assert (Hv : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_var x ≈ me_var x) by (eapply wf_me_var; eassumption).
  assert (Hl : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_lit U ≈ me_lit U) by (apply wf_me_lit; exact HU).
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists))))))  _ _ _ _ _ Hv) as (_ & (R & Rm & HR & _) & _).
  assert (HRl : mdenote Θ Ξ Γ (me_lit U) R).
  { inversion HR; subst; try (cbn in *; discriminate).
    match goal with Hx' : _ ∋ #x ≔ₘ ?U', Hu : udenote _ _ _ _ ?U' R |- _ =>
      rewrite (ctx_lookup_mod_functional _ _ _ _ Hx Hx'); constructor; exact Hu end. }
  eapply modexp_conv_replace_left; [ exact Hl | exact Hv | exact HRl | exact HR | apply obs_sub_lit | eapply obs_sub_var; exact Hx |].
  eapply modexp_conv_replace_right; [ exact Hl | exact Hv | exact HRl | exact HR | apply obs_sub_lit | eapply obs_sub_var; exact Hx |].
  exact HUU.
Qed.

(** [slots_conv Θ Ξ Γ]: every module slot of [Γ] is compared with itself
    along paths. *)
Definition slots_conv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : Prop :=
  forall x U, Γ ∋ #x ≔ₘ U -> modexp_conv Θ Ξ Γ (me_var x) (me_var x).

(** No context has a slot. *)
Lemma slots_conv_nil : forall Θ Ξ, slots_conv Θ Ξ ⋅.
Proof. intros * x U Hx; inversion Hx. Qed.

(** The slots of a context grown by an entry: those of the context, and
    the entry's own if it has a module part, compared as its unit is. *)
Lemma slots_conv_cons : forall Θ Ξ Γ e, ⊢ Θ ⍮ Ξ ⍮ e :: Γ -> slots_conv Θ Ξ Γ ->
    (forall U, (e = ce_mod U \/ exists A M, e = ce_dm A M U) ->
       Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U /\ modexp_conv Θ Ξ Γ (me_lit U) (me_lit U)) ->
    slots_conv Θ Ξ (e :: Γ).
Proof.
  intros * HΓ HS He x U0 Hx; pose proof (wf_wk_shift _ _ _ _ HΓ) as Hφ.
  inversion Hx; subst.
  - destruct (He _ (or_introl eq_refl)) as [HU HUU].
    eapply modexp_conv_slot; [ exact HΓ | exact Hx | exact (wk_preserves_unit _ _ _ _ _ _ _ HU Hφ) |].
    exact (modexp_conv_wk _ _ _ _ _ _ _ HUU Hφ).
  - destruct (He _ (or_intror (ex_intro _ _ (ex_intro _ _ eq_refl)))) as [HU HUU].
    eapply modexp_conv_slot; [ exact HΓ | exact Hx | exact (wk_preserves_unit _ _ _ _ _ _ _ HU Hφ) |].
    exact (modexp_conv_wk _ _ _ _ _ _ _ HUU Hφ).
  - match goal with Hn : _ ∋ #_ ≔ₘ _ |- _ => exact (modexp_conv_wk _ _ _ _ _ _ _ (HS _ _ Hn) Hφ) end.
Qed.

(** *** Bodies Written Differently *)

(** [wb_rel X Y]: [X] and [Y] are one description, or two open ones
    differing only in the body as written. *)
Inductive wb_rel : mdesc -> mdesc -> Prop :=
(** One description *)
| wb_rel_same : forall X, wb_rel X X
(** Two open descriptions with one telescope and one expansion, the
    bodies as written possibly different *)
| wb_rel_written : forall Δ Φ1 Φ2 Φx, wb_rel (mdesc_open Δ Φ1 Φx) (mdesc_open Δ Φ2 Φx).

(** What a leaf shows but its unit does not see the body as written. *)
Lemma leaf_core_wb : forall Θ Ξ Δ A X Y, leaf_conv Θ Ξ Δ A X -> wb_rel X Y -> leaf_core Θ Ξ Δ A Y.
Proof.
  intros * Hl Hw; destruct Hw as [X | Δ1 Φ1 Φ2 Φx]; [ exact (leaf_core_of_conv _ _ _ _ _ Hl) |].
  destruct Hl as [Hk Ht Hr Hu Hh Hf Hn]; constructor; cbn in *; try assumption.
  - destruct (mdesc_mod A); cbn in *; tauto.
  - rewrite Hf; split; intros (? & ? & ? & ? & ? & Hc & _); cbn in Hc; discriminate.
  - rewrite Hn; split; apply no_level_open_written.
Qed.

(** One step from two such descriptions. *)
Lemma wb_rel_at : forall X Y N X1, wb_rel X Y -> mdesc_at X N = Some X1 -> exists Y1, mdesc_at Y N = Some Y1 /\ wb_rel X1 Y1.
Proof.
  intros * Hw Ha; destruct Hw as [X | Δ1 Φ1 Φ2 Φx]; [ exists X1; split; [ exact Ha | constructor ] |].
  cbn in Ha |- *; destruct (tele_split (rev Δ1)) as [[[B Δ'] τ] |]; [| discriminate ]; injection Ha as <-.
  eexists; split; [ reflexivity | constructor ].
Qed.

(** The other way round. *)
Lemma wb_rel_sym : forall X Y, wb_rel X Y -> wb_rel Y X.
Proof. intros * []; constructor. Qed.

(** Paths from two literals of such descriptions reach such descriptions. *)
Lemma wb_paths : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ s P1 P2, mod_qname P1 = None -> mod_qname P2 = None ->
    (forall X, mdenote Θ Ξ Δ P1 X -> exists Y, mdenote Θ Ξ Δ P2 Y /\ wb_rel X Y) ->
    (forall Y, mdenote Θ Ξ Δ P2 Y -> exists X, mdenote Θ Ξ Δ P1 X /\ wb_rel X Y) ->
    (forall X, mdenote Θ Ξ Δ (path_left P1 s) X -> exists Y, mdenote Θ Ξ Δ (path_left P2 s) Y /\ wb_rel X Y) /\
    (forall Y, mdenote Θ Ξ Δ (path_left P2 s) Y -> exists X, mdenote Θ Ξ Δ (path_left P1 s) X /\ wb_rel X Y).
Proof.
  intros Θ Ξ Hg Δ s; induction s as [| [y | N N'] s IH]; intros * Hq1 Hq2 H1 H2; cbn; [ split; assumption | |].
  - apply IH; [ cbn; rewrite Hq1; reflexivity | cbn; rewrite Hq2; reflexivity | |].
    + intros X1 HX1; destruct (mdenote_mem_obs_inv _ _ Hg _ _ _ _ (or_introl Hq1) HX1) as (X & Xm & Γy & E & rd & R1 & HX & Hd & He & Hed & Hr).
      destruct (H1 _ HX) as (Y & HY & Hw); exists X1; split; [| constructor ].
      inversion Hw as [| Δ1 Φ1 Φ2 Φx E1 E2]; subst; [ econstructor; eassumption |].
      cbn in Hd; injection Hd as <-; econstructor; [ exact HY | reflexivity | exact He | exact Hed | exact Hr ].
    + intros Y1 HY1; destruct (mdenote_mem_obs_inv _ _ Hg _ _ _ _ (or_introl Hq2) HY1) as (Y & Ym & Γy & E & rd & R1 & HY & Hd & He & Hed & Hr).
      destruct (H2 _ HY) as (X & HX & Hw); exists Y1; split; [| constructor ].
      inversion Hw as [| Δ1 Φ1 Φ2 Φx E1 E2]; subst; [ econstructor; eassumption |].
      cbn in Hd; injection Hd as <-; econstructor; [ exact HX | reflexivity | exact He | exact Hed | exact Hr ].
  - apply IH; [ reflexivity | reflexivity | |].
    + intros X1 HX1; destruct (mdenote_app_inv _ _ _ _ _ _ HX1) as (X & HX & Ha).
      destruct (H1 _ HX) as (Y & HY & Hw); destruct (wb_rel_at _ _ _ _ Hw Ha) as (Y1 & Ha' & Hw1).
      exists Y1; split; [ econstructor; eassumption | exact Hw1 ].
    + intros Y1 HY1; destruct (mdenote_app_inv _ _ _ _ _ _ HY1) as (Y & HY & Ha).
      destruct (H2 _ HY) as (X & HX & Hw); destruct (wb_rel_at _ _ _ _ (wb_rel_sym _ _ Hw) Ha) as (X1 & Ha' & Hw1).
      exists X1; split; [ econstructor; eassumption | exact (wb_rel_sym _ _ Hw1) ].
Qed.

(** A literal body and its expansion denote descriptions differing only
    in the body as written. *)
Lemma wb_expand_root : forall Θ Ξ Δ Δ1 Φ1, Θ ⍮ Ξ ⍮ Δ ⊢ᵐ me_lit (gu_open Δ1 Φ1) ≈ me_lit (gu_open Δ1 Φ1) ->
    (forall X, mdenote Θ Ξ Δ (me_lit (gu_open Δ1 Φ1)) X ->
       exists Y, mdenote Θ Ξ Δ (me_lit (gu_open Δ1 (gm_expand Φ1))) Y /\ wb_rel X Y) /\
    (forall Y, mdenote Θ Ξ Δ (me_lit (gu_open Δ1 (gm_expand Φ1))) Y ->
       exists X, mdenote Θ Ξ Δ (me_lit (gu_open Δ1 Φ1)) X /\ wb_rel X Y).
Proof.
  intros * HP.
  assert (HL : forall X, mdenote Θ Ξ Δ (me_lit (gu_open Δ1 Φ1)) X -> X = mdesc_open Δ1 Φ1 (gm_expand Φ1)).
  { intros X HX; pose proof (mdenote_lit_inv _ _ _ _ _ HX) as Hu; inversion Hu; subst.
    match goal with Hb : body_xp _ _ _ _ ?Φx, He : mdesc_body _ _ _ _ _ = Some X |- _ =>
      cbn in He; injection He as <-; rewrite (body_xp_expand _ _ _ _ _ Hb); reflexivity end. }
  assert (HR : mdenote Θ Ξ Δ (me_lit (gu_open Δ1 (gm_expand Φ1))) (mdesc_open Δ1 (gm_expand Φ1) (gm_expand Φ1))).
  { apply mdenote_lit; eapply udenote_body; [ apply body_xp_noopen; apply gm_noopen_expand | reflexivity ]. }
  split.
  - intros X HX; rewrite (HL _ HX); exists (mdesc_open Δ1 (gm_expand Φ1) (gm_expand Φ1)); split; [ exact HR |].
    constructor.
  - intros Y HY.
    pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HP)) as Hg.
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HY _ HR).
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HP) as (_ & (X & Xm & HX & _) & _).
    exists X; split; [ exact HX |]; rewrite (HL _ HX); constructor.
Qed.

(** The module parts of two such descriptions are such. *)
Lemma wb_rel_mod : forall X Y, wb_rel X Y -> opt_rel wb_rel (mdesc_mod X) (mdesc_mod Y).
Proof.
  intros X Y Hw; destruct Hw as [X0 | Δ1 Φ1 Φ2 Φx]; cbn; [ destruct (mdesc_mod X0); cbn; [ constructor | exact I ] |].
  constructor.
Qed.

(** Paths compared with one expression compare, up to units, with one
    whose descriptions differ only in the bodies as written. *)
Lemma paths_core_wb_right : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ P Q Q', paths_conv Θ Ξ Δ P Q ->
    mod_qname Q = None -> mod_qname Q' = None ->
    (forall X, mdenote Θ Ξ Δ Q X -> exists Y, mdenote Θ Ξ Δ Q' Y /\ wb_rel X Y) ->
    (forall Y, mdenote Θ Ξ Δ Q' Y -> exists X, mdenote Θ Ξ Δ Q X /\ wb_rel X Y) ->
    paths_core Θ Ξ Δ P Q'.
Proof.
  intros * Hg * HPQ Hq Hq' Hw1 Hw2 s Hs; destruct (HPQ _ Hs) as [H1 H2].
  destruct (wb_paths _ _ Hg _ (path_swap s) _ _ Hq Hq' Hw1 Hw2) as [Hp1 Hp2]; rewrite !(proj1 (path_swap_sides s _)) in Hp1, Hp2.
  assert (Hleaf : forall X XR Y, path_leaf Θ Ξ Δ s X XR -> wb_rel XR Y -> path_core Θ Ξ Δ s X Y).
  { unfold path_leaf, path_core; intros X XR Y Hl Hw; destruct (path_all_apps s).
    - eapply opt_rel_trans; [| exact Hl | exact (wb_rel_mod _ _ Hw) ]; intros; eapply leaf_core_wb; eassumption.
    - exact (leaf_core_wb _ _ _ _ _ _ Hl Hw). }
  split.
  - intros X HX; destruct (H1 _ HX) as (XR & HXR & Hl); destruct (Hp1 _ HXR) as (Y & HY & Hw).
    exists Y; split; [ exact HY | exact (Hleaf _ _ _ Hl Hw) ].
  - intros Y HY; destruct (Hp2 _ HY) as (XR & HXR & Hw); destruct (H2 _ HXR) as (X & HX & Hl).
    exists X; split; [ exact HX | exact (Hleaf _ _ _ Hl Hw) ].
Qed.

(** A literal body and its expansion. *)
Lemma modexp_conv_expand : forall Θ Ξ Γ Δ Φ, Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ Φ ->
    modexp_conv Θ Ξ Γ (me_lit (gu_open Δ Φ)) (me_lit (gu_open Δ Φ)) ->
    modexp_conv Θ Ξ Γ (me_lit (gu_open Δ Φ)) (me_lit (gu_open Δ (gm_expand Φ))).
Proof.
  intros * HU HUU Δ0 σ σ' Hσ.
  pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hσl; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hσ) as Hσr.
  pose proof (ctx_wf_gctx _ _ _ (presup_unit_eq_ctx HU)) as Hg.
  assert (HUe : Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ (gm_expand Φ)) by (apply wf_unit_eq_expand; exact HU).
  assert (Heq : Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ (me_lit (gu_open Δ Φ))[σ]ᵐ ≈ (me_lit (gu_open Δ (gm_expand Φ)))[σ']ᵐ).
  { eapply wf_me_trans; [ exact (sub_preserves_modexp _ _ _ _ _ _ _ (wf_me_lit _ _ _ _ _ HUe) Hσl) |].
    exact (sub_eq_preserves_modexp _ _ _ _ _ (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_right HUe)) _ _ _ Hσ). }
  apply paths_conv_of_core; [ exact Heq |].
  assert (HP1 : Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ (me_lit (gu_open Δ Φ))[σ']ᵐ ≈ (me_lit (gu_open Δ Φ))[σ']ᵐ)
    by exact (sub_preserves_modexp _ _ _ _ _ _ _ (wf_me_lit _ _ _ _ _ HU) Hσr).
  cbn [modexp_sub] in HP1 |- *; rewrite gunit_sub_mk in HP1 |- *; rewrite gunit_sub_mk; cbn [moddef_sub] in HP1 |- *.
  rewrite <- gm_expand_sub.
  destruct (wb_expand_root _ _ _ _ _ HP1) as [Hw1 Hw2].
  pose proof (HUU _ _ _ Hσ) as HC; cbn [modexp_sub] in HC; rewrite !gunit_sub_mk in HC; cbn [moddef_sub] in HC.
  apply (fun Hq Hq' => paths_core_wb_right _ _ Hg _ _ _ _ HC Hq Hq' Hw1 Hw2); reflexivity.
Qed.

(** ** Cases of the Comparison *)

(** A slot and its unit denote one description. *)
Lemma slot_lit_desc : forall Θ Ξ Γ x U, ⊢ Θ ⍮ Ξ ⍮ Γ -> Γ ∋ #x ≔ₘ U ->
    exists R, mdenote Θ Ξ Γ (me_var x) R /\ mdenote Θ Ξ Γ (me_lit U) R.
Proof.
  intros * HΓ Hx.
  assert (Hv : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_var x ≈ me_var x) by (eapply wf_me_var; eassumption).
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists))))))  _ _ _ _ _ Hv) as (_ & (R & Rm & HR & _) & _).
  exists R; split; [ exact HR |].
  inversion HR; subst; try (cbn in *; discriminate).
  match goal with Hx' : _ ∋ #x ≔ₘ ?U', Hu : udenote _ _ _ _ ?U' R |- _ =>
    rewrite (ctx_lookup_mod_functional _ _ _ _ Hx Hx'); constructor; exact Hu end.
Qed.

(** [δ] for a slot. *)
Lemma modexp_conv_delta_slot : forall Θ Ξ Γ x U, ⊢ Θ ⍮ Ξ ⍮ Γ -> Γ ∋ #x ≔ₘ U -> slots_conv Θ Ξ Γ ->
    modexp_conv Θ Ξ Γ (me_var x) (me_lit U).
Proof.
  intros * HΓ Hx HS.
  assert (Hd : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_var x ≈ me_lit U) by (eapply wf_me_delta_slot; eassumption).
  destruct (slot_lit_desc _ _ _ _ _ HΓ Hx) as (R & HRv & HRl).
  eapply modexp_conv_replace_right;
    [ exact (wf_modexp_eq_refl_left Hd) | exact (wf_modexp_eq_refl_right Hd) | exact HRv | exact HRl
    | eapply obs_sub_var; exact Hx | apply obs_sub_lit | exact (HS _ _ Hx) ].
Qed.

(** [β] for a literal: the application and the instantiated literal. *)
Lemma modexp_conv_beta : forall Θ Ξ Γ Δ κ X D N,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass κ X :: nil) D ≈ gu_mk (Δ ++ ce_ass κ X :: nil) D ->
    modexp_conv Θ Ξ Γ (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) N ≈ me_lit (gu_mk Δ D)[Id,,N]ᵘ ->
    modexp_conv Θ Ξ Γ (me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) N) (me_lit (gu_mk Δ D)[Id,,N]ᵘ).
Proof.
  intros * HU HUU HN Hb.
  assert (Hl : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D) ≈ me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D))
    by (apply wf_me_lit; exact HU).
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & (R & Hu) & _).
  destruct (mdenote_beta _ _ _ _ _ _ _ N HU _ Hu) as (R' & Hma & Hml & _).
  destruct (udenote_last _ _ _ _ _ _ _ _ Hu) as (R1 & Hu1 & ->).
  pose proof (ctx_wf_gctx _ _ _ (presup_unit_eq_ctx HU)) as Hg.
  destruct (desc_of_props _ _ _ _ (ex_intro _ _ (conj Hl (mdenote_lit _ _ _ _ _ Hu)))) as (_ & Hok & _).
  pose proof (udenote_is_mod _ _ _ _ _ _ Hu1) as Him.
  destruct (desc_ok_tele _ _ _ _ Hok (mdesc_is_mod_up _ _ Him)) as [T HT].
  assert (HT1 : exists T1, mdesc_tele R1 = Some T1).
  { destruct R1; cbn in Him |- *; try contradiction; [ eauto |].
    cbn in HT; destruct (Nat.leb _ _); [ eauto | discriminate ]. }
  destruct HT1 as [T1 HT1].
  pose proof (mdesc_tele_up (ce_ass κ X :: nil) _ _ HT1) as HTu.
  eapply modexp_conv_replace_right;
    [ exact (wf_modexp_eq_refl_left Hb) | exact (wf_modexp_eq_refl_right Hb) | exact Hma | exact Hml
    | apply obs_sub_app | apply obs_sub_lit |].
  eapply modexp_conv_app;
    [ exact HUU | exact Hl | apply mdenote_lit; exact Hu
    | unfold mdesc_mod_tele; rewrite (mdesc_is_mod_mod _ (mdesc_is_mod_up _ _ Him)); exact HTu
    | apply tele_view_last | apply wf_exp_eq_refl; exact HN ].
Qed.

(** Whether a description reads an open frame. *)
Lemma desc_reads_frame_dec : forall Ξ R, desc_reads_frame Ξ R \/ ~ desc_reads_frame Ξ R.
Proof.
  intros Ξ R; unfold desc_reads_frame.
  destruct (mdesc_mod R) as [[| | Θ' p T Φ Ns |] |].
  all: try (right; intros (? & ? & ? & ? & ? & [=] & _); fail).
  destruct (gc_frame Ξ p) as [TΦ |] eqn:Ef.
  - left; exists Θ', p, T, Φ, Ns; split; [ reflexivity | rewrite Ef; discriminate ].
  - right; intros (? & ? & ? & ? & ? & [= <- <- <- <- <-] & Hf); contradiction.
Qed.

(** An entry read from what a well-formed module expression denotes reads
    no open frame ([entry_open_frame_free], [desc_ok_entry_closed_read]). *)
Lemma entry_read_frame_free : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ H H' R0 Rm y Γy E rd R1 R,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ H R0 -> mdesc_mod R0 = Some Rm -> mdesc_entry Rm y = Some (Γy, E, rd) ->
    edenote Θ Ξ (Γy ++ Γ) (mdesc_entry_path Rm y) E R1 -> mdesc_read rd R1 = Some R -> ~ desc_reads_frame Ξ R.
Proof.
  intros * Hg * HH Hm0 Hd He Hed Hr; pose proof (gctx_valid_syn _ _ Hg) as Hv.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ HH Hv) as (_ & HR & _).
  pose proof (desc_ok_mod _ _ Hg _ _ _ (HR _ Hm0) Hd) as Hok.
  destruct Rm; try (cbn in He; discriminate).
  - eapply entry_open_frame_free; eassumption.
  - cbn [mdesc_entry_path] in Hed.
    destruct (desc_ok_entry_closed_read _ _ Hg Hv _ _ _ _ _ _ _ _ _ _ _ _ Hok He Hed Hr) as (Rn & [-> _ _ _ HFr]).
    intros Hr2; apply (proj1 (desc_reads_frame_up _ _ _)) in Hr2; exact (HFr Hr2).
Qed.

(** [ζ] for an alias with no parameter: the literal and its target. *)
Lemma modexp_conv_beta_alias0 : forall Θ Ξ Γ E, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E -> frame_free_target Θ Ξ Γ E ->
    modexp_conv Θ Ξ Γ E E -> modexp_conv Θ Ξ Γ (me_lit (gu_mk nil (md_alias E))) E.
Proof.
  intros * HE Hff HEE.
  assert (Hb : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_lit (gu_mk nil (md_alias E)) ≈ E) by (eapply wf_me_beta_alias0; eassumption).
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HE)) as Hg.
  destruct Hff as (RE & HmE & Hn).
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ Hb) as (_ & (RL & RLm & HmL & HmdL) & _).
  assert (Hmd : mdesc_mod RL = mdesc_mod RE).
  { pose proof (mdenote_lit_inv _ _ _ _ _ HmL) as Hu; inversion Hu; subst.
    match goal with Hm : mdenote _ _ _ E ?R0, Hd : mdesc_mod ?R0 = Some ?R' |- _ =>
      rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm _ HmE) in Hd; rewrite Hd end.
    rewrite mdesc_up_nil; exact (mdesc_mod_idem _ _ ltac:(eassumption)). }
  eapply modexp_conv_replace_mod_left;
    [ exact HE | exact (wf_modexp_eq_refl_left Hb) | exact HmE | exact HmL | symmetry; exact Hmd
    | exact (obs_sub_of_frame_free _ _ Hg _ _ _ HmE Hn) | apply obs_sub_lit | exact HEE ].
Qed.

(** [δ] for a selected module: the selection and the unit its module
    part stands for. *)
Lemma modexp_conv_delta_sel : forall Θ Ξ Γ H y R Rm, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_mem H y ≈ me_mem H y ->
    mdenote Θ Ξ Γ (me_mem H y) R -> mdesc_mod R = Some Rm -> modexp_conv Θ Ξ Γ (me_mem H y) (me_mem H y) ->
    modexp_conv Θ Ξ Γ (me_mem H y) (mdesc_unit Rm).
Proof.
  intros * HH Hm Hmd HHH.
  assert (Hd : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_mem H y ≈ mdesc_unit Rm)
    by (eapply wf_me_delta_sel; [ eassumption | eassumption | eassumption
                                | eapply wf_me_delta_sel_unit_refl; eassumption ]).
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ Hd) as (_ & _ & (RU & RUm & HmU & HmdU)).
  destruct (desc_of_props _ _ _ _ (ex_intro _ _ (conj HH Hm))) as (_ & _ & Hc & Hx & _).
  destruct (mdesc_unit_denote _ _ _ Hg (mdesc_canonical_mod _ _ _ _ Hc Hmd) (mdesc_mod_is_mod _ _ Hmd) _
              (mdesc_xp_mod _ _ _ _ _ Hx Hmd)) as (RU' & HmU' & HmdU').
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HmU _ HmU') in HmdU; clear HmU RU; rename RU' into RU.
  destruct (desc_reads_frame_dec Ξ R) as [Hr | Hn].
  - (* a path naming an open frame: the unit is the path itself *)
    pose proof (proj1 (modexp_gen _ _ _ _ _ HH)) as HH0; cbn [gen_m] in HH0.
    inversion Hm as [? ? p T Φ Hq Hu | ? ? p pq k D Mk Tm Φm Hq Hk HMk Hl | | | | ? ? ? R0 R0m Γy E rd R1 ? Hm0 Hd0 He Hed Hrd
                    | ? ? p Rr Tm Φm Hq Hk Hl]; subst.
    + cbn in Hmd; injection Hmd as <-; cbn [mdesc_unit me_apps]; rewrite <- (mod_qname_inv _ _ Hq); exact HHH.
    + cbn in Hmd; injection Hmd as <-; cbn [mdesc_unit me_apps]; rewrite <- (mod_qname_inv _ _ Hq); exact HHH.
    + exfalso; exact (entry_read_frame_free _ _ Hg _ _ _ _ _ _ _ _ _ _ _ HH0 Hm0 Hd0 He Hed Hrd Hr).
    + cbn in Hmd; injection Hmd as <-; cbn [mdesc_unit me_apps]; rewrite <- (mod_qname_inv _ _ Hq); exact HHH.
  - assert (HnU : ~ desc_reads_frame Ξ RU).
    { intros Hr; apply Hn; unfold desc_reads_frame in *; rewrite Hmd; rewrite HmdU' in Hr; exact Hr. }
    eapply modexp_conv_replace_mod_right;
      [ exact HH | exact (wf_modexp_eq_refl_right Hd) | exact Hm | exact HmU' | rewrite Hmd, HmdU'; reflexivity
      | exact (obs_sub_of_frame_free _ _ Hg _ _ _ Hm Hn) | exact (obs_sub_of_frame_free _ _ Hg _ _ _ HmU' HnU) | exact HHH ].
Qed.

(** ** Abstraction

    A literal over parameters is compared through its target, or its
    body, under the parameters: each application fills the outermost
    parameter, and each selection reads the target's member abstracted
    over the parameters left. *)

(** *** Reading Under Other Assumptions *)

(** [slots_agree Γ Γ']: the two contexts have the same module slots. *)
Definition slots_agree (Γ Γ' : ctx) : Prop := forall x, ctx_find_mod Γ x = ctx_find_mod Γ' x.

(** Contexts with the same slots, extended alike. *)
Lemma slots_agree_app : forall Δ Γ Γ', slots_agree Γ Γ' -> slots_agree (Δ ++ Γ) (Δ ++ Γ').
Proof.
  induction Δ as [| e Δ IH]; intros * H x; cbn; [ exact (H x) |].
  destruct x as [| y]; [ reflexivity | rewrite (IH _ _ H y); reflexivity ].
Qed.

(** Two telescopes of assumptions of one length over one context have the
    same slots. *)
Lemma slots_agree_ass : forall A A' Γ, all_assumptions A -> all_assumptions A' -> List.length A = List.length A' ->
    slots_agree (A ++ Γ) (A' ++ Γ).
Proof.
  induction A as [| e A IH]; intros [| e' A'] Γ Ha Ha' Hl; cbn in Hl; try discriminate; [ intros x; reflexivity |].
  apply List.Forall_cons_iff in Ha as [(κ & B & ->) Ha]; apply List.Forall_cons_iff in Ha' as [(κ' & B' & ->) Ha'].
  intros [| y]; cbn; [ reflexivity | rewrite (IH A' Γ Ha Ha' ltac:(lia) y); reflexivity ].
Qed.

(** What a module expression denotes reads only the module slots of its
    context. *)
Lemma mdenote_slots_agree : forall Θ Ξ,
    (forall Γ H R, mdenote Θ Ξ Γ H R -> forall Γ', slots_agree Γ Γ' -> mdenote Θ Ξ Γ' H R) /\
    (forall Γ o U R, udenote Θ Ξ Γ o U R -> forall Γ', slots_agree Γ Γ' -> udenote Θ Ξ Γ' o U R) /\
    (forall Γ o E R, edenote Θ Ξ Γ o E R -> forall Γ', slots_agree Γ Γ' -> edenote Θ Ξ Γ' o E R) /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> forall Γ', slots_agree Γ Γ' -> body_xp Θ Ξ Γ' Φ Φx) /\
    (forall Γ H its gs, items_gen Θ Ξ Γ H its gs -> forall Γ', slots_agree Γ Γ' -> items_gen Θ Ξ Γ' H its gs).
Proof.
  intros Θ Ξ; apply mdenote_all_ind; intros; try solve [ econstructor; eauto using slots_agree_app ].
  econstructor; [| eauto ]; apply ctx_find_mod_spec; match goal with H : slots_agree _ _ |- _ => rewrite <- H end;
    apply ctx_find_mod_spec; assumption.
Qed.

(** [modexp_conv] moved along two equal substitutions. *)
Lemma modexp_conv_sub : forall Θ Ξ Γ H H' Δ τ τ', modexp_conv Θ Ξ Γ H H' -> Θ ⍮ Ξ ⍮ Δ ⊢ˢ τ ≈ τ' : Γ ->
    modexp_conv Θ Ξ Δ H[τ]ᵐ H'[τ']ᵐ.
Proof.
  intros * HH Hτ Ψ ρ ρ' Hρ; rewrite !modexp_sub_sub; apply HH.
  eapply wf_sub_eq_trans; [ exact (wf_sub_eq_compose_left _ _ _ _ _ _ _ _ Hτ (wf_sub_eq_left _ _ _ _ _ _ Hρ)) |].
  exact (wf_sub_eq_compose_right _ _ _ _ _ _ _ _ (wf_sub_eq_right _ _ _ _ _ _ Hτ) Hρ).
Qed.

(** *** Equal Telescopes of Assumptions *)

(** The heads of two equal telescopes of assumptions are equal at one
    sort: they are each below the other ([mutual_subtyp_eq]). *)
Lemma ext_heads_equal : forall Θ Ξ Γ Ψ Ψ' κ A A', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ▹{κ} A ≈ Ψ' ▹{κ} A' -> all_assumptions Ψ ->
    @telescope_heads_eq Θ Ξ Γ Ψ Ψ' κ A A'.
Proof.
  intros * H Ha; destruct (ext_eq_ass_inv _ _ _ _ _ _ _ _ H) as [S1 HS1 S2 HS2 Ht HA HA' H12 H21].
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HA' (ctxsub_ext_rev _ _ _ _ _ Ht Ha)) as HA'l; rewrite !exp_sub_id in HA'l.
  destruct HS1 as [i | |]; inversion HS2; subst.
  - pose proof (lift_exp_max_left _ _ _ _ _ i0 HA) as HA1; pose proof (lift_exp_max_right _ _ _ _ i _ HA'l) as HA2.
    apply (mk_telescope_heads_eq _ _ _ _ _ _ (Typeω@(max i i0))); [ constructor | exact Ht | exact HA1 | | exact (lift_exp_max_right _ _ _ _ i _ HA') ].
    apply mutual_subtyp_eq; [ constructor | exact HA1 | exact HA2 | exact H12 | exact H21 ].
  - apply (mk_telescope_heads_eq _ _ _ _ _ _ Propₘ); [ constructor | exact Ht | exact HA | | exact HA' ].
    apply mutual_subtyp_eq; [ constructor | exact HA | exact HA'l | exact H12 | exact H21 ].
  - apply (mk_telescope_heads_eq _ _ _ _ _ _ LevelSort); [ constructor | exact Ht | exact HA | | exact HA' ].
    apply mutual_subtyp_eq; [ constructor | exact HA | exact HA'l | exact H12 | exact H21 ].
Qed.

(** The [Π]s at [r] over two equal telescopes of assumptions of two
    types equal under the left one, each parameter abstractable at [r]. *)
Lemma ctx_pi_at_tele_eq : forall Θ Ξ r D Ψ D' A A' i, all_assumptions D -> all_assumptions D' -> Θ ⍮ Ξ ⍮ Ψ ⊢ˣ D ≈ D' ->
    (forall Δ1 κ B Δ2, D = Δ1 ++ ce_ass κ B :: Δ2 -> pi_kinds κ r) ->
    Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ A ≈ A' : abs_kind_sort r Typeω@i ->
    exists j, Θ ⍮ Ξ ⍮ Ψ ⊢ ctx_pi_at r D A ≈ ctx_pi_at r D' A' : abs_kind_sort r Typeω@j.
Proof.
  intros Θ Ξ r; induction D as [| e D IH]; intros Ψ D' A A' i Ha Ha' HD Hk HA.
  - destruct D'; [| apply ext_eq_length in HD; discriminate ]; exists i; exact HA.
  - destruct D' as [| e' D']; [ apply ext_eq_length in HD; discriminate |].
    apply List.Forall_cons_iff in Ha as [(κ & B & ->) Ha]; apply List.Forall_cons_iff in Ha' as [(κ' & B' & ->) Ha'].
    assert (κ' = κ) as -> by (inversion HD; subst; reflexivity).
    destruct (ext_heads_equal _ _ _ _ _ _ _ _ HD Ha) as [S HS Ht HB HBB _].
    assert (Hk1 : pi_kinds κ r) by exact (Hk nil κ B D eq_refl).
    assert (HPi : exists j, Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ a_pi κ r B A ≈ a_pi κ r B' A' : abs_kind_sort r Typeω@j).
    { destruct r eqn:Er.
      - exact (wf_exp_eq_pi_sort_at _ _ _ _ _ _ _ _ _ _ _ HB HS HBB HA ltac:(discriminate)).
      - exact (wf_exp_eq_pi_sort_at _ _ _ _ _ _ _ _ _ _ _ HB HS HBB HA ltac:(discriminate)).
      - inversion Hk1; subst; inversion HS; subst; exists 0.
        eapply wf_exp_eq_pi_cong with (U := Typeω@0) (κd := ak_level) (κc := ak_level);
          [ apply wf_is_univ_large; eapply presup_exp_ctx, HB | exact HB | exact HBB | exact HA | constructor ]. }
    destruct HPi as [j Hj]; cbn [ctx_pi_at].
    refine (IH _ _ _ _ _ Ha Ha' Ht _ Hj).
    intros Δ1 κ0 B0 Δ2 ->; exact (Hk (ce_ass κ B :: Δ1) κ0 B0 Δ2 eq_refl).
Qed.

(** The [λ]s over two equal telescopes of assumptions of two terms equal
    under the left one. *)
Lemma ctx_fn_tele_eq : forall Θ Ξ r D Ψ D' A M M' i, all_assumptions D -> all_assumptions D' -> Θ ⍮ Ξ ⍮ Ψ ⊢ˣ D ≈ D' ->
    (forall Δ1 κ B Δ2, D = Δ1 ++ ce_ass κ B :: Δ2 -> pi_kinds κ r) ->
    Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ A : abs_kind_sort r Typeω@i -> Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ ctx_fn D M ≈ ctx_fn D' M' : ctx_pi_at r D A.
Proof.
  intros Θ Ξ r; induction D as [| e D IH]; intros Ψ D' A M M' i Ha Ha' HD Hk HA HM.
  - destruct D'; [| apply ext_eq_length in HD; discriminate ]; exact HM.
  - destruct D' as [| e' D']; [ apply ext_eq_length in HD; discriminate |].
    apply List.Forall_cons_iff in Ha as [(κ & B & ->) Ha]; apply List.Forall_cons_iff in Ha' as [(κ' & B' & ->) Ha'].
    assert (κ' = κ) as -> by (inversion HD; subst; reflexivity).
    destruct (ext_heads_equal _ _ _ _ _ _ _ _ HD Ha) as [S HS Ht HB HBB _].
    assert (Hk1 : pi_kinds κ r) by exact (Hk nil κ B D eq_refl).
    assert (HPi : exists j, Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ a_pi κ r B A : abs_kind_sort r Typeω@j).
    { destruct r eqn:Er.
      - exact (wf_pi_sort_at _ _ _ _ _ _ _ _ _ HB HS HA ltac:(discriminate)).
      - exact (wf_pi_sort_at _ _ _ _ _ _ _ _ _ HB HS HA ltac:(discriminate)).
      - inversion Hk1; subst; inversion HS; subst; exists 0.
        eapply wf_pi with (U := Typeω@0) (κd := ak_level) (κc := ak_level);
          [ apply wf_is_univ_large; eapply presup_exp_ctx, HB | exact HB | exact HA | constructor ]. }
    destruct HPi as [j Hj]; cbn [ctx_pi_at ctx_fn].
    refine (IH _ _ _ _ _ j Ha Ha' Ht _ Hj _); [ intros Δ1 κ0 B0 Δ2 ->; exact (Hk (ce_ass κ B :: Δ1) κ0 B0 Δ2 eq_refl) |].
    eapply wf_exp_eq_fn_cong with (i := i); [ exact HB | exact HS | exact HBB | exact HA | exact Hk1 | exact HM ].
Qed.

(** The outermost parameters of two equal telescopes of assumptions are of
    one kind, each below the other. *)
Lemma ext_eq_last : forall Θ Ξ Ψ D1 D1' κ κ' B B', Θ ⍮ Ξ ⍮ Ψ ⊢ˣ D1 ++ ce_ass κ B :: nil ≈ D1' ++ ce_ass κ' B' :: nil ->
    κ = κ' /\ Θ ⍮ Ξ ⍮ Ψ ⊢ B ⊆ B' /\ Θ ⍮ Ξ ⍮ Ψ ⊢ B' ⊆ B.
Proof.
  induction D1 as [| e D1 IH]; intros [| e' D1'] * H; cbn [List.app] in H.
  - assert (κ' = κ) as -> by (inversion H; subst; reflexivity).
    destruct (ext_eq_ass_inv _ _ _ _ _ _ _ _ H) as [_ _ _ _ _ _ _ H12 H21]; cbn in H12, H21; auto.
  - apply ext_eq_length in H; cbn in H; rewrite List.length_app in H; cbn in H; lia.
  - apply ext_eq_length in H; cbn in H; rewrite List.length_app in H; cbn in H; lia.
  - inversion H; subst; eauto.
Qed.

(** The outermost parameters of two equal telescopes of assumptions, as
    the heads of telescopes over no tail. *)
Lemma ext_eq_last_head : forall Θ Ξ Ψ D1 D1' κ κ' B B', Θ ⍮ Ξ ⍮ Ψ ⊢ˣ D1 ++ ce_ass κ B :: nil ≈ D1' ++ ce_ass κ' B' :: nil ->
    κ = κ' /\ ext_eq_ass_head Θ Ξ Ψ nil nil κ B B'.
Proof.
  induction D1 as [| e D1 IH]; intros [| e' D1'] * H; cbn [List.app] in H.
  - assert (κ' = κ) as -> by (inversion H; subst; reflexivity).
    split; [ reflexivity | exact (ext_eq_ass_inv _ _ _ _ _ _ _ _ H) ].
  - apply ext_eq_length in H; cbn in H; rewrite List.length_app in H; cbn in H; lia.
  - apply ext_eq_length in H; cbn in H; rewrite List.length_app in H; cbn in H; lia.
  - inversion H; subst; eauto.
Qed.

(** Two equal telescopes of assumptions, their outermost parameters
    instantiated by two equal arguments. *)
Lemma ext_eq_inst : forall Θ Ξ Ψ D1 D1' κ B B' N N', all_assumptions D1 -> all_assumptions D1' ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˣ D1 ++ ce_ass κ B :: nil ≈ D1' ++ ce_ass κ B' :: nil -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : B ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˣ tele_sub D1 (Id,,N) ≈ tele_sub D1' (Id,,N').
Proof.
  intros Θ Ξ Ψ D1; induction D1 as [| e D1 IH]; intros [| e' D1'] * Ha Ha' HD HN.
  - cbn; constructor; exact (presup_exp_eq_ctx HN).
  - apply ext_eq_length in HD; cbn in HD; rewrite List.length_app in HD; cbn in HD; lia.
  - apply ext_eq_length in HD; cbn in HD; rewrite List.length_app in HD; cbn in HD; lia.
  - apply List.Forall_cons_iff in Ha as [(κ1 & C & ->) Ha]; apply List.Forall_cons_iff in Ha' as [(κ1' & C' & ->) Ha'].
    cbn [List.app] in HD; assert (κ1' = κ1) as -> by (inversion HD; subst; reflexivity).
    assert (Hab : all_assumptions (D1 ++ ce_ass κ B :: nil)) by (apply List.Forall_app; split; [ exact Ha | constructor; [ eauto | constructor ] ]).
    assert (Hab' : all_assumptions (D1' ++ ce_ass κ B' :: nil)) by (apply List.Forall_app; split; [ exact Ha' | constructor; [ eauto | constructor ] ]).
    destruct (ext_heads_equal _ _ _ _ _ _ _ _ HD Hab) as [S HS Ht HC HCC HC'].
    pose proof (IH _ _ _ _ _ _ Ha Ha' Ht HN) as HIH.
    destruct (ext_eq_last_head _ _ _ _ _ _ _ _ _ Ht) as (_ & [S1 HS1 S2 HS2 _ HB HB' HBB _]); cbn [List.app] in HB, HB', HBB.
    pose proof (presup_exp_eq_left HN) as HN1; pose proof (presup_exp_eq_right HN) as HN2.
    assert (HN2' : Θ ⍮ Ξ ⍮ Ψ ⊢ N' : B') by (eapply wf_exp_subtyp'; eassumption).
    pose proof (wf_sub_eq_id_extend _ _ _ _ _ _ _ _ HB HS1 HN1 HN2 HN) as Hσ.
    pose proof (wf_sub_eq_id_extend _ _ _ _ _ _ _ _ HB' HS2 HN2' HN2' (wf_exp_eq_refl HN2')) as Hσ'.
    rewrite <- List.app_assoc in HC, HCC, HC'; cbn [List.app] in HC, HCC, HC'.
    pose proof (sb_qn_eq_ext _ _ _ _ _ Ha (presup_exp_ctx HC) Hσ) as Hq.
    pose proof (sb_qn_eq_ext _ _ _ _ _ Ha' (presup_exp_ctx HC') Hσ') as Hq'.
    pose proof (sort_kind_type_sort _ _ HS) as HSt.
    pose proof (ctxsub_ext_rev _ _ _ _ _ Ht Hab) as HId; rewrite <- !List.app_assoc in HId; cbn [List.app] in HId.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HC' HId) as HC'l; rewrite !exp_sub_id in HC'l.
    cbn [tele_sub centry_sub].
    assert (Hl : length D1' = length D1) by (apply ext_eq_length in Ht; rewrite !List.length_app in Ht; cbn in Ht; lia).
    rewrite Hl.
    assert (HCσ : Θ ⍮ Ξ ⍮ tele_sub D1 (Id,,N) ++ Ψ ⊢ C[sb_qn (length D1) (Id,,N)] : S)
      by (rewrite <- (type_sort_sub _ (sb_qn (length D1) (Id,,N)) HSt); exact (sub_preserves_exp _ _ _ _ _ _ _ HC (wf_sub_eq_left _ _ _ _ _ _ Hq))).
    assert (HCCσ : Θ ⍮ Ξ ⍮ tele_sub D1 (Id,,N) ++ Ψ ⊢ C[sb_qn (length D1) (Id,,N)] ≈ C'[sb_qn (length D1) (Id,,N')] : S).
    { eapply wf_exp_eq_trans.
      - rewrite <- (type_sort_sub _ (sb_qn (length D1) (Id,,N)) HSt); exact (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HCC (wf_sub_eq_left _ _ _ _ _ _ Hq)).
      - rewrite <- (type_sort_sub _ (sb_qn (length D1) (Id,,N)) HSt); exact (sub_eq_preserves_exp _ _ _ _ _ HC'l _ _ _ Hq). }
    eapply wf_ext_eq_ass_eq; [ exact HIH | exact HCσ | exact HS | exact HCCσ | exact (presup_exp_eq_right HCCσ) |].
    rewrite <- Hl, <- (type_sort_sub _ (sb_qn (length D1') (Id,,N')) HSt); exact (sub_preserves_exp _ _ _ _ _ _ _ HC' (wf_sub_eq_left _ _ _ _ _ _ Hq')).
Qed.

(** *** Abstracted Leaves *)

(** The term part of an abstracted description is the [Π] over the
    parameters of the term part. *)
Lemma mdesc_type_up_opt : forall D X, mdesc_type (mdesc_up D X) = option_map (ctx_pi_at (mdesc_kind X) D) (mdesc_type X).
Proof.
  intros; destruct (mdesc_type X) as [A |] eqn:E; cbn; [ exact (mdesc_type_up _ _ _ E) |].
  destruct (mdesc_type (mdesc_up D X)) as [A |] eqn:E'; [| reflexivity ].
  destruct (mdesc_type_up_inv _ _ _ E') as (A0 & HA0 & _); congruence.
Qed.

(** A module abstracted over parameters takes the outermost of them
    first. *)
Lemma mdesc_head_up_last : forall D1 κ B X T, mdesc_mod_tele X = Some T ->
    mdesc_head (mdesc_up (D1 ++ ce_ass κ B :: nil) X) = Some B.
Proof.
  intros * Ht; unfold mdesc_head, mdesc_mod_tele in *; rewrite mdesc_mod_up.
  destruct (mdesc_mod X) as [Xm |]; [| discriminate ]; cbn [option_map].
  rewrite (mdesc_tele_up _ _ _ Ht), List.app_assoc, tele_view_last; reflexivity.
Qed.

(** What is no module, abstracted, takes no argument. *)
Lemma mdesc_head_up_none : forall D X, mdesc_mod X = None -> mdesc_head (mdesc_up D X) = None.
Proof. intros * Hm; unfold mdesc_head, mdesc_mod_tele; rewrite mdesc_mod_up, Hm; reflexivity. Qed.

(** No member of a type of levels, under equal telescopes of assumptions:
    along the identity, from one to the other ([ctxsub_ext]). *)
Lemma no_level_ctx_conv : forall Θ Ξ Ψ D D' X, all_assumptions D -> Θ ⍮ Ξ ⍮ Ψ ⊢ˣ D ≈ D' ->
    Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ⁿˡ X -> Θ ⍮ Ξ ⍮ D' ++ Ψ ⊢ⁿˡ X.
Proof.
  intros * Ha HD H; pose proof (sub_preserves_no_level _ _ _ _ _ _ H (ctxsub_ext _ _ _ _ _ HD Ha)) as X0.
  rewrite mdesc_sub_id in X0; exact X0.
Qed.

(** Two descriptions with no member of a type of levels together, under
    equal telescopes of assumptions, abstracted over them. *)
Lemma no_level_up_conv : forall Θ Ξ Ψ D D' X X', all_assumptions D -> all_assumptions D' -> Θ ⍮ Ξ ⍮ Ψ ⊢ˣ D ≈ D' ->
    (Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ⁿˡ X <-> Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ⁿˡ X') ->
    (Θ ⍮ Ξ ⍮ Ψ ⊢ⁿˡ mdesc_up D X <-> Θ ⍮ Ξ ⍮ Ψ ⊢ⁿˡ mdesc_up D' X').
Proof.
  intros * Ha Ha' HD Hn; rewrite <- !no_level_up_iff; split; intros H.
  - exact (no_level_ctx_conv _ _ _ _ _ _ Ha HD (proj1 Hn H)).
  - exact (proj2 Hn (no_level_ctx_conv _ _ _ _ _ _ Ha' (ext_eq_sym_ass _ _ _ _ _ Ha HD) H)).
Qed.

(** Two leaves compared under two equal telescopes of assumptions,
    abstracted over them. *)
Lemma leaf_core_up : forall Θ Ξ Ψ D D' X X', all_assumptions D -> all_assumptions D' -> Θ ⍮ Ξ ⍮ Ψ ⊢ˣ D ≈ D' ->
    leaf_core Θ Ξ (D ++ Ψ) X X' ->
    (forall A, mdesc_type X = Some A -> forall Δ1 κ B Δ2, D = Δ1 ++ ce_ass κ B :: Δ2 -> pi_kinds κ (mdesc_kind X)) ->
    (forall A, mdesc_type X = Some A -> exists i, Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ A : abs_kind_sort (mdesc_kind X) Typeω@i) ->
    (forall Xm, mdesc_mod X = Some Xm -> exists T, mdesc_mod_tele X = Some T) ->
    (forall Xm', mdesc_mod X' = Some Xm' -> exists T, mdesc_mod_tele X' = Some T) ->
    leaf_core Θ Ξ Ψ (mdesc_up D X) (mdesc_up D' X').
Proof.
  intros * Ha Ha' HD [Hk Ht Hr Hm Hh Hf Hn] Hpk HA HT HT'.
  pose proof (no_level_up_conv _ _ _ _ _ _ _ Ha Ha' HD Hn) as Hnu.
  destruct D as [| e D0] using List.rev_ind.
  - destruct D'; [| apply ext_eq_length in HD; discriminate ]; rewrite !mdesc_up_nil; constructor; assumption.
  - clear IHD0; destruct D' as [| e' D0'] using List.rev_ind; [ apply ext_eq_length in HD; rewrite List.length_app in HD; cbn in HD; lia |].
    clear IHD0'.
    apply List.Forall_app in Ha as [Ha0 Hae]; apply List.Forall_app in Ha' as [Ha0' Hae'].
    inversion Hae as [| ? ? (κ & B & ->) _]; inversion Hae' as [| ? ? (κ' & B' & ->) _]; subst.
    destruct (ext_eq_last _ _ _ _ _ _ _ _ _ HD) as (<- & HBB & HB'B).
    constructor.
    + rewrite !mdesc_kind_up; exact Hk.
    + rewrite !mdesc_type_up_opt, !mdesc_kind_up.
      destruct (mdesc_type X) as [A |] eqn:EA; destruct (mdesc_type X') as [A' |] eqn:EA'; cbn in Ht |- *; try contradiction; [| exact I ].
      destruct Ht as [i Hi]; rewrite Hk in Hi.
      rewrite <- Hk in Hi |- *; apply (ctx_pi_at_tele_eq _ _ _ _ _ _ _ _ i); try assumption; try exact (Hpk _ eq_refl).
      * apply List.Forall_app; split; [ exact Ha0 | constructor; [ eauto | constructor ] ].
      * apply List.Forall_app; split; [ exact Ha0' | constructor; [ eauto | constructor ] ].
    + intros A0 HA0; rewrite mdesc_type_up_opt in HA0; rewrite !mdesc_reduct_up.
      destruct (mdesc_type X) as [A |] eqn:EA; cbn in HA0; [ injection HA0 as <- | discriminate ].
      specialize (Hr _ eq_refl).
      destruct (mdesc_reduct X) as [M |]; destruct (mdesc_reduct X') as [M' |]; cbn in Hr |- *; try contradiction; [| exact I ].
      destruct (HA _ eq_refl) as [i Hi].
      eapply ctx_fn_tele_eq; [ | | exact HD | exact (Hpk _ eq_refl) | exact Hi | exact Hr ].
      * apply List.Forall_app; split; [ exact Ha0 | constructor; [ eauto | constructor ] ].
      * apply List.Forall_app; split; [ exact Ha0' | constructor; [ eauto | constructor ] ].
    + rewrite !mdesc_mod_up; destruct (mdesc_mod X); destruct (mdesc_mod X'); cbn in Hm |- *; exact Hm.
    + destruct (mdesc_mod X) as [Xm |] eqn:Em; destruct (mdesc_mod X') as [Xm' |] eqn:Em'; cbn in Hm; try contradiction.
      * destruct (HT _ eq_refl) as [T1 HT1]; destruct (HT' _ eq_refl) as [T1' HT1'].
        rewrite (mdesc_head_up_last _ _ _ _ _ HT1), (mdesc_head_up_last _ _ _ _ _ HT1'); cbn; split; assumption.
      * rewrite !mdesc_head_up_none by assumption; exact I.
    + rewrite !desc_reads_frame_up; exact Hf.
    + exact Hnu.
Qed.

(** *** Selections from Abstracted Modules *)

(** How an entry of a module abstracted over [D] is read: as the entry of
    the module, abstracted over [D] too. *)
Definition reader_up (D : ctx) (rd : reader) : reader :=
  match rd with
  | reader_open Δ Φ' => reader_open (Δ ++ D) Φ'
  | reader_closed Θ Ns M => reader_closed (Θ ++ D) Ns M
  end.

(** What reading through [reader_up D rd] adds to reading through [rd]:
    a member of a closed module read bare, at no outside parameter and no
    argument, is read as its name once there are outside parameters
    ([mdesc_named]). *)
Definition reader_named (D : ctx) (rd : reader) (X : mdesc) : mdesc :=
  match rd with
  | reader_closed nil nil M => mdesc_named D nil M X
  | _ => X
  end.

(** The entries of an abstracted module are its entries, abstracted. *)
Lemma mdesc_entry_up : forall D Rm y, mdesc_entry (mdesc_up D Rm) y =
    option_map (fun '(Γy, E, rd) => (match Rm with mdesc_open _ _ _ => Γy ++ D | _ => Γy end, E, reader_up D rd)) (mdesc_entry Rm y).
Proof.
  intros D [r A om | Δ0 Φ Φx | Θ0 p T Φ Ns | Θd A M Rm]; intros y; cbn [mdesc_up mdesc_entry]; try reflexivity.
  - destruct (gm_prefix_upto Φx y) as [[| Φ' z E | Φ' H its] |]; try reflexivity.
    destruct E as [[|] ? ? ? [] | | | |]; cbn; rewrite ?List.app_assoc; reflexivity.
  - destruct (gm_prefix_upto Φ y) as [[| Φ' z E | Φ' H its] |]; reflexivity.
Qed.

(** An abstracted module's entries are stored where its entries are. *)
Lemma mdesc_entry_path_up : forall D Rm y, mdesc_entry_path (mdesc_up D Rm) y = mdesc_entry_path Rm y.
Proof. intros D [] y; reflexivity. Qed.

(** An entry read abstracted is read, then abstracted. *)
Lemma mdesc_read_up : forall D rd R1, mdesc_read (reader_up D rd) R1 =
    option_map (fun XQ => mdesc_up D (reader_named D rd XQ)) (mdesc_read rd R1).
Proof.
  intros D [Δ Φ' | Θ Ns M] R1; cbn [reader_up mdesc_read reader_named].
  - destruct (gm_fill Φ'); cbn; [ rewrite mdesc_up_cat |]; reflexivity.
  - destruct (mdesc_ats_read R1 Ns) as [R1' |] eqn:E; cbn; [| reflexivity ].
    rewrite mdesc_up_cat; f_equal; f_equal.
    destruct Θ as [| e Θ]; destruct Ns as [| N Ns]; cbn [List.app]; try reflexivity.
    + rewrite !mdesc_up_nil, !mdesc_named_nil; reflexivity.
    + unfold mdesc_named; destruct D; reflexivity.
Qed.

(** A closed module a well-formed module expression denotes is stored
    closed. *)
Lemma mod_closed_unit_closed : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ Q RQ Θ0 p T Φ Ns, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ Q ≈ Q -> mdenote Θ Ξ Γ Q RQ ->
    mdesc_mod RQ = Some (mdesc_closed Θ0 p T Φ Ns) -> unit_closed T Φ.
Proof.
  intros * Hg * HQ Hm Hmd; pose proof (gctx_valid_syn _ _ Hg) as Hv.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ HQ Hv) as (_ & HR & _).
  pose proof (desc_ok_mod _ _ Hg _ _ _ (HR _ Hm) Hmd) as Hok.
  inversion Hok as [| | Γ0 Θa T0 Φ1 Ns0 Θ1 Ξ1 p0 lΘ Hg0 Hsub Hloc |]; subst.
  exact (loc_closed _ _ Hg0 _ _ _ Hloc).
Qed.

(** A closed entry denotes the same in every context. *)
Lemma edenote_closed_ctx : forall Θ Ξ, gctx_closed Θ Ξ -> forall Δ Γ o E R, entry_sc 0 E -> edenote Θ Ξ Δ o E R -> edenote Θ Ξ Γ o E R.
Proof.
  intros * Hc * HE Hd.
  pose proof (proj1 (proj2 (proj2 (mdenote_sub_lt_all _ _ Hc))) _ _ _ _ Hd 0 ltac:(intros ? ? Hx; lia) HE Γ Id ltac:(intros ? ? Hx; lia)) as Hd'.
  rewrite mdesc_sub_id in Hd'; exact (edenote_closed_any _ _ _ _ _ _ _ HE Hd').
Qed.

(** [up_sim Θ Ξ Ψ D P Q]: the module part of what [P] denotes, in [Ψ], is
    that of what [Q] denotes under [D], abstracted over [D]. *)
Definition up_sim (Θ : gdeps) (Ξ : gstack) (Ψ D : ctx) (P Q : modexp) : Prop :=
  (forall R, mdenote Θ Ξ Ψ P R -> exists RQ, mdenote Θ Ξ (D ++ Ψ) Q RQ /\ mdesc_mod R = option_map (mdesc_up D) (mdesc_mod RQ)) /\
  (forall RQ, mdenote Θ Ξ (D ++ Ψ) Q RQ -> exists R, mdenote Θ Ξ Ψ P R /\ mdesc_mod R = option_map (mdesc_up D) (mdesc_mod RQ)).

(** [named_read Θ Ξ Ψ D Q y XQ X]: [X] is the member [XQ] of [Q] selected
    under [D], abstracted over [D]: as it is, or, for a member of a closed
    module read bare, read as its name ([mdesc_named]). *)
Inductive named_read (Θ : gdeps) (Ξ : gstack) (Ψ D : ctx) (Q : modexp) (y : String.string) (XQ : mdesc) : mdesc -> Prop :=
(** The member as it is, abstracted: a term with no δ-reduct only under
    no parameter *)
| named_read_plain : (forall r A, XQ = mdesc_term r A None -> D = nil) -> named_read Θ Ξ Ψ D Q y XQ (mdesc_up D XQ)
(** The member of the closed module [p], read bare, as its name, abstracted *)
| named_read_name : forall RQ p T Φ, mdenote Θ Ξ (D ++ Ψ) Q RQ -> mdesc_mod RQ = Some (mdesc_closed nil p T Φ nil) ->
    named_read Θ Ξ Ψ D Q y XQ (mdesc_up D (mdesc_named D nil (a_mem (qname_mod p) y) XQ)).

(** What reading through [reader_up] adds is [named_read]. *)
Lemma reader_named_cases : forall Θ Ξ Ψ D Q y RQ RQm Γy E rd Γ' o R1 XQ, mdenote Θ Ξ (D ++ Ψ) Q RQ -> mdesc_mod RQ = Some RQm ->
    mdesc_entry RQm y = Some (Γy, E, rd) -> edenote Θ Ξ Γ' o E R1 -> mdesc_read rd R1 = Some XQ ->
    (forall Θ0 p T Φ Ns, RQm = mdesc_closed Θ0 p T Φ Ns -> unit_closed T Φ) ->
    named_read Θ Ξ Ψ D Q y XQ (mdesc_up D (reader_named D rd XQ)).
Proof.
  intros * Hm Hmd He Hed Hr Hc.
  destruct RQm as [| Δ0 Φ Φx | Θ0 p T Φ Ns |]; try (cbn in He; discriminate).
  - cbn in He; destruct (gm_prefix_upto Φx y) as [[| Φ' z E0 | ] |]; try discriminate.
    destruct E0 as [[|] ? ? ? [] | | | |]; try discriminate; injection He as <- <- <-; cbn [reader_named]; apply named_read_plain;
      intros r0 A0 ->; cbn in Hr; destruct (gm_fill Φ') as [σ |]; cbn in Hr; try discriminate; injection Hr as Hr;
      inversion Hed; subst.
    + cbn in Hr; discriminate.
    + match goal with Hu : udenote _ _ _ _ _ ?R |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Him;
        destruct R; cbn in Him, Hr; first [ contradiction | discriminate ] end.
    + cbn in Hr; discriminate.
  - destruct (mdesc_entry_closed _ _ _ _ _ _ _ _ _ (Hc _ _ _ _ _ eq_refl) He) as (-> & _ & ->).
    destruct Θ0 as [| e Θ0]; destruct Ns as [| N Ns]; cbn [reader_named apps].
    + eapply named_read_name; eassumption.
    + apply named_read_plain; intros r0 A0 ->; cbn in Hr; destruct (mdesc_ats_read R1 _) as [R1' |]; cbn in Hr; [| discriminate ].
      injection Hr as Hr; unfold mdesc_named in Hr; destruct R1' as [? ? [] | | |]; cbn in Hr; discriminate.
    + apply named_read_plain; intros r0 A0 ->; cbn in Hr; destruct (mdesc_ats_read R1 _) as [R1' |]; cbn in Hr; [| discriminate ].
      injection Hr as Hr; unfold mdesc_named in Hr; destruct R1' as [? ? [] | | |]; cbn in Hr; discriminate.
    + apply named_read_plain; intros r0 A0 ->; cbn in Hr; destruct (mdesc_ats_read R1 _) as [R1' |]; cbn in Hr; [| discriminate ].
      injection Hr as Hr; unfold mdesc_named in Hr; destruct R1' as [? ? [] | | |]; cbn in Hr; discriminate.
Qed.

(** A selection from an expression whose module part is that of [Q]
    abstracted over [D] is the selection from [Q], abstracted
    ([named_read]). *)
Lemma mem_up : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ D P Q y, obs_root Ξ P -> obs_root Ξ Q -> Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ᵐ Q ≈ Q ->
    up_sim Θ Ξ Ψ D P Q ->
    (forall X, mdenote Θ Ξ Ψ (me_mem P y) X -> exists XQ, mdenote Θ Ξ (D ++ Ψ) (me_mem Q y) XQ /\ named_read Θ Ξ Ψ D Q y XQ X) /\
    (forall XQ, mdenote Θ Ξ (D ++ Ψ) (me_mem Q y) XQ -> exists X, mdenote Θ Ξ Ψ (me_mem P y) X /\ named_read Θ Ξ Ψ D Q y XQ X).
Proof.
  intros * Hg * HP HQ HQQ [H1 H2]; pose proof (wf_gstack_closed _ _ Hg) as Hc; split.
  - intros X HX; destruct (mdenote_mem_obs_inv _ _ Hg _ _ _ _ HP HX) as (R & Rm & Γy & E & rd & R1 & HR & Hmd & He & Hed & Hr).
    destruct (H1 _ HR) as (RQ & HRQ & HmdQ); rewrite Hmd in HmdQ.
    destruct (mdesc_mod RQ) as [RQm |] eqn:EQ; cbn in HmdQ; [ injection HmdQ as -> | discriminate ].
    rewrite mdesc_entry_up in He; destruct (mdesc_entry RQm y) as [[[Γy0 E0] rd0] |] eqn:He0; cbn in He; [| discriminate ].
    injection He as <- <- <-.
    rewrite mdesc_read_up in Hr; destruct (mdesc_read rd0 R1) as [XQ |] eqn:Hr0; cbn in Hr; [ injection Hr as <- | discriminate ].
    assert (HcQ : forall Θ0 p T Φ Ns, RQm = mdesc_closed Θ0 p T Φ Ns -> unit_closed T Φ)
      by (intros * ->; exact (mod_closed_unit_closed _ _ Hg _ _ _ _ _ _ _ _ HQQ HRQ EQ)).
    assert (Hed0 : edenote Θ Ξ (Γy0 ++ D ++ Ψ) (mdesc_entry_path RQm y) E0 R1).
    { rewrite mdesc_entry_path_up in Hed.
      destruct RQm as [| Δ0 Φ Φx | Θ0 p T Φ Ns |]; try (cbn in He0; discriminate).
      + rewrite <- List.app_assoc in Hed; exact Hed.
      + destruct (mdesc_entry_closed _ _ _ _ _ _ _ _ _ (HcQ _ _ _ _ _ eq_refl) He0) as (-> & HE & _).
        exact (edenote_closed_ctx _ _ Hc _ _ _ _ _ HE Hed). }
    exists XQ; split; [ econstructor; [ exact HRQ | exact EQ | exact He0 | exact Hed0 | exact Hr0 ] |].
    exact (reader_named_cases _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRQ EQ He0 Hed0 Hr0 HcQ).
  - intros XQ HX; destruct (mdenote_mem_obs_inv _ _ Hg _ _ _ _ HQ HX) as (RQ & RQm & Γy & E & rd & R1 & HRQ & EQ & He & Hed & Hr).
    destruct (H2 _ HRQ) as (R & HR & Hmd); rewrite EQ in Hmd; cbn in Hmd.
    assert (HcQ : forall Θ0 p T Φ Ns, RQm = mdesc_closed Θ0 p T Φ Ns -> unit_closed T Φ)
      by (intros * ->; exact (mod_closed_unit_closed _ _ Hg _ _ _ _ _ _ _ _ HQQ HRQ EQ)).
    exists (mdesc_up D (reader_named D rd XQ)); split; [| exact (reader_named_cases _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRQ EQ He Hed Hr HcQ) ].
    econstructor; [ exact HR | exact Hmd | rewrite mdesc_entry_up, He; reflexivity | | rewrite mdesc_read_up, Hr; reflexivity ].
    rewrite mdesc_entry_path_up.
    destruct RQm as [| Δ0 Φ Φx | Θ0 p T Φ Ns |]; try (cbn in He; discriminate).
    + rewrite <- List.app_assoc; exact Hed.
    + destruct (mdesc_entry_closed _ _ _ _ _ _ _ _ _ (HcQ _ _ _ _ _ eq_refl) He) as (-> & HE & _).
      exact (edenote_closed_ctx _ _ Hc _ _ _ _ _ HE Hed).
Qed.

(** *** Paths from Abstracted Modules *)

(** A well-formed module expression whose descriptions read no open frame
    is read through what it denotes. *)
Lemma obs_root_of_frame_free : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ F F0, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ F ≈ F0 ->
    (forall R, mdenote Θ Ξ Γ F R -> ~ desc_reads_frame Ξ R) -> obs_root Ξ F.
Proof.
  intros * Hg * HFF HFr.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HFF) as (_ & (RF & _ & HRF & _) & _).
  pose proof (obs_sub_of_frame_free _ _ Hg _ _ _ HRF (HFr _ HRF) _ _ (wf_sub_id _ _ _ (presup_modexp_eq_ctx HFF))) as Hq.
  rewrite modexp_sub_id in Hq; exact Hq.
Qed.

(** *** Paths Past a Selection

    Paths compared from a selected member compare its leaves wholly, even
    with no further selection: [path_leaf_m false]. *)

(** [path_leaf], comparing the leaves of paths of no selection by their
    module parts only when [m]. *)
Definition path_full_m (m : bool) (Θ : gdeps) (Ξ : gstack) (Δ : ctx) (s : list path_step) (X X' : mdesc) : Prop :=
  if andb m (path_all_apps s) then opt_rel (leaf_conv Θ Ξ Δ) (mdesc_mod X) (mdesc_mod X') else leaf_conv Θ Ξ Δ X X'.

(** [path_full_m], up to units at the root: the root's units are not read
    here, and the root of a body module with no parameter stands for a unit
    not compared ([modexp_conv_body]). *)
Definition path_leaf_m (m : bool) (Θ : gdeps) (Ξ : gstack) (Δ : ctx) (s : list path_step) (X X' : mdesc) : Prop :=
  match s with
  | nil => if m then opt_rel (leaf_core Θ Ξ Δ) (mdesc_mod X) (mdesc_mod X') else leaf_core Θ Ξ Δ X X'
  | _ :: _ => path_full_m m Θ Ξ Δ s X X'
  end.

(** A whole comparison is one up to units at the root. *)
Lemma path_leaf_m_of_full : forall m Θ Ξ Δ s X X', path_full_m m Θ Ξ Δ s X X' -> path_leaf_m m Θ Ξ Δ s X X'.
Proof.
  intros [|] * H; destruct s as [| st s]; try exact H; unfold path_full_m in H; cbn in H |- *.
  - destruct (mdesc_mod X); destruct (mdesc_mod X'); cbn in H |- *; try contradiction; [ exact (leaf_core_of_conv _ _ _ _ _ H) | exact I ].
  - exact (leaf_core_of_conv _ _ _ _ _ H).
Qed.

(** Two modules compared wholly stand for equal units. *)
Lemma unit_of_full : forall m Θ Ξ Γ s X X' Rm Rm', path_full_m m Θ Ξ Γ s X X' -> mdesc_mod X = Some Rm -> mdesc_mod X' = Some Rm' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ mdesc_unit Rm ≈ mdesc_unit Rm'.
Proof.
  intros * Hl E E'; unfold path_full_m in Hl; destruct (andb m (path_all_apps s)).
  - rewrite E, E' in Hl; cbn in Hl; pose proof (leaf_unit _ _ _ _ _ Hl) as Hu.
    rewrite (mdesc_mod_idem _ _ E), (mdesc_mod_idem _ _ E') in Hu; exact Hu.
  - pose proof (leaf_unit _ _ _ _ _ Hl) as Hu; rewrite E, E' in Hu; exact Hu.
Qed.

(** [paths_rel] at [path_leaf_m m]. *)
Definition paths_conv_m (m : bool) (Θ : gdeps) (Ξ : gstack) (Δ : ctx) : modexp -> modexp -> Prop :=
  paths_rel Θ Ξ Δ (path_leaf_m m Θ Ξ Δ).

(** [modexp_conv] with [path_leaf_m m]. *)
Definition modexp_conv_m (m : bool) (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (H H' : modexp) : Prop :=
  forall Δ σ σ', Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ ≈ σ' : Γ -> paths_conv_m m Θ Ξ Δ H[σ]ᵐ H'[σ']ᵐ.

(** At [true], it follows from [modexp_conv]. *)
Lemma modexp_conv_m_true : forall Θ Ξ Γ H H', modexp_conv Θ Ξ Γ H H' -> modexp_conv_m true Θ Ξ Γ H H'.
Proof.
  intros * HH Δ σ σ' Hσ s Hs; destruct (HH _ _ _ Hσ s Hs) as [H1 H2]; split.
  - intros X HX; destruct (H1 _ HX) as (X' & HX' & Hl); exists X'; split; [ exact HX' | exact (path_leaf_m_of_full true _ _ _ _ _ _ Hl) ].
  - intros X' HX'; destruct (H2 _ HX') as (X & HX & Hl); exists X; split; [ exact HX | exact (path_leaf_m_of_full true _ _ _ _ _ _ Hl) ].
Qed.

(** Two selections of one member compare their leaves wholly. *)
Lemma modexp_conv_m_mem : forall m Θ Ξ Γ H H' y, modexp_conv_m m Θ Ξ Γ H H' -> modexp_conv_m false Θ Ξ Γ (me_mem H y) (me_mem H' y).
Proof.
  intros * HH Δ σ σ' Hσ s Hs; cbn [modexp_sub].
  destruct (HH _ _ _ Hσ (ps_mem y :: s) (path_pairs_mem _ _ _ _ _ _ Hs)) as [H1 H2]; cbn [path_left path_right path_leaf_m] in H1, H2.
  unfold path_full_m in H1, H2; cbn [path_all_apps] in H1, H2; rewrite Bool.andb_false_r in H1, H2; split.
  - intros X HX; destruct (H1 _ HX) as (X' & HX' & Hl); exists X'; split; [ exact HX' | apply path_leaf_m_of_full; exact Hl ].
  - intros X' HX'; destruct (H2 _ HX') as (X & HX & Hl); exists X; split; [ exact HX | apply path_leaf_m_of_full; exact Hl ].
Qed.

(** [modexp_conv_m] moved along two equal substitutions. *)
Lemma modexp_conv_m_sub : forall m Θ Ξ Γ H H' Δ τ τ', modexp_conv_m m Θ Ξ Γ H H' -> Θ ⍮ Ξ ⍮ Δ ⊢ˢ τ ≈ τ' : Γ ->
    modexp_conv_m m Θ Ξ Δ H[τ]ᵐ H'[τ']ᵐ.
Proof.
  intros * HH Hτ Ψ ρ ρ' Hρ; rewrite !modexp_sub_sub; apply HH.
  eapply wf_sub_eq_trans; [ exact (wf_sub_eq_compose_left _ _ _ _ _ _ _ _ Hτ (wf_sub_eq_left _ _ _ _ _ _ Hρ)) |].
  exact (wf_sub_eq_compose_right _ _ _ _ _ _ _ _ (wf_sub_eq_right _ _ _ _ _ _ Hτ) Hρ).
Qed.

(** Two applications to equal arguments of the outermost parameter. *)
Lemma modexp_conv_m_app : forall m Θ Ξ Γ H H' R T B T1 N N', modexp_conv_m m Θ Ξ Γ H H' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θ Ξ Γ H R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : B -> modexp_conv_m m Θ Ξ Γ (me_app H N) (me_app H' N').
Proof.
  intros * HH Hw Hm Ht Hv HN Δ σ σ' Hσ; cbn.
  pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hσl.
  intros s Hs.
  assert (Hs' : path_pairs Θ Ξ Δ H[σ]ᵐ (ps_app N[σ] N'[σ'] :: s)).
  { eapply path_pairs_app;
      [ exact (wf_sub_mdenote _ _ _ _ _ _ _ _ Hw Hm Hσl)
      | exact (mdesc_mod_tele_sub _ _ σ _ (wf_mdenote_scoped _ _ _ _ _ _ Hw Hm) Ht)
      | rewrite tele_view_sub, Hv; reflexivity | | exact Hs ].
    cbn [fst]; eapply wf_exp_eq_trans; [ exact (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HN Hσl) |].
    exact (sub_eq_preserves_exp _ _ _ _ _ (presup_exp_eq_right HN) _ _ _ Hσ). }
  destruct (HH _ _ _ Hσ _ Hs') as [H1 H2]; cbn [path_left path_right path_leaf_m] in H1, H2.
  unfold path_full_m in H1, H2; cbn [path_all_apps] in H1, H2; split.
  - intros X HX; destruct (H1 _ HX) as (X' & HX' & Hl); exists X'; split; [ exact HX' | apply path_leaf_m_of_full; exact Hl ].
  - intros X' HX'; destruct (H2 _ HX') as (X & HX & Hl); exists X; split; [ exact HX | apply path_leaf_m_of_full; exact Hl ].
Qed.

(** [modexp_conv_m] at the root, in its own context. *)
Lemma inner_root_conv_m : forall m Θ Ξ Γ F F', modexp_conv_m m Θ Ξ Γ F F' -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    (forall RQ, mdenote Θ Ξ Γ F RQ -> exists RQ', mdenote Θ Ξ Γ F' RQ' /\ path_leaf_m m Θ Ξ Γ nil RQ RQ') /\
    (forall RQ', mdenote Θ Ξ Γ F' RQ' -> exists RQ, mdenote Θ Ξ Γ F RQ /\ path_leaf_m m Θ Ξ Γ nil RQ RQ').
Proof.
  intros * HC HΓ; pose proof (HC _ _ _ (wf_sub_eq_refl _ _ _ _ _ (wf_sub_id _ _ _ HΓ))) as HC0; rewrite !modexp_sub_id in HC0.
  exact (HC0 nil (path_pairs_nil _ _ _ _)).
Qed.

(** [modexp_conv_m] at one selection, in its own context. *)
Lemma inner_mem_conv_m : forall m Θ Ξ Γ F F' y, modexp_conv_m m Θ Ξ Γ F F' -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    (forall XQ, mdenote Θ Ξ Γ (me_mem F y) XQ -> exists XQ', mdenote Θ Ξ Γ (me_mem F' y) XQ' /\ leaf_conv Θ Ξ Γ XQ XQ') /\
    (forall XQ', mdenote Θ Ξ Γ (me_mem F' y) XQ' -> exists XQ, mdenote Θ Ξ Γ (me_mem F y) XQ /\ leaf_conv Θ Ξ Γ XQ XQ').
Proof.
  intros * HC HΓ; pose proof (HC _ _ _ (wf_sub_eq_refl _ _ _ _ _ (wf_sub_id _ _ _ HΓ))) as HC0; rewrite !modexp_sub_id in HC0.
  pose proof (HC0 (ps_mem y :: nil) (path_pairs_mem _ _ _ _ _ _ (path_pairs_nil _ _ _ _))) as H0.
  unfold path_leaf_m, path_full_m in H0; cbn [path_all_apps path_left path_right] in H0; rewrite Bool.andb_false_r in H0; exact H0.
Qed.

(** [modexp_conv_m] at one application, in its own context. *)
Lemma inner_app_conv_m : forall m Θ Ξ Γ F F' R T B T1 N N', modexp_conv_m m Θ Ξ Γ F F' -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    mdenote Θ Ξ Γ F R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) -> Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : B ->
    forall X, mdenote Θ Ξ Γ (me_app F N) X -> exists X', mdenote Θ Ξ Γ (me_app F' N') X' /\ path_full_m m Θ Ξ Γ (ps_app N N' :: nil) X X'.
Proof.
  intros * HC HΓ Hm Ht Hv HN; pose proof (HC _ _ _ (wf_sub_eq_refl _ _ _ _ _ (wf_sub_id _ _ _ HΓ))) as HC0; rewrite !modexp_sub_id in HC0.
  exact (proj1 (HC0 (ps_app N N' :: nil) (path_pairs_app _ _ _ _ _ _ _ _ _ _ _ Hm Ht Hv HN (path_pairs_nil _ _ _ _)))).
Qed.

(** [up_whole Θ Ξ Ψ D P F]: what [P] denotes, in [Ψ], is wholly what [F]
    denotes under [D], abstracted over [D]. *)
Definition up_whole (Θ : gdeps) (Ξ : gstack) (Ψ D : ctx) (P F : modexp) : Prop :=
  (forall X, mdenote Θ Ξ Ψ P X -> exists XQ, mdenote Θ Ξ (D ++ Ψ) F XQ /\ X = mdesc_up D XQ) /\
  (forall XQ, mdenote Θ Ξ (D ++ Ψ) F XQ -> exists X, mdenote Θ Ξ Ψ P X /\ X = mdesc_up D XQ).

(** [abs_setting m Θ Ξ Ψ D D' P P' F F']: [P] and [P'], in [Ψ], are [F] and
    [F'] abstracted over the equal telescopes [D] and [D'] — wholly, past a
    selection ([m = false]). *)
Record abs_setting (m : bool) (Θ : gdeps) (Ξ : gstack) (Ψ D D' : ctx) (P P' F F' : modexp) : Prop := mk_abs_setting
  { (** The left parameters are assumptions *)
    abs_ass : all_assumptions D
    (** and so are the right ones *)
  ; abs_ass' : all_assumptions D'
    (** The parameters are equal *)
  ; abs_tele : Θ ⍮ Ξ ⍮ Ψ ⊢ˣ D ≈ D'
    (** The left expression is read through what it denotes *)
  ; abs_root : obs_root Ξ P
    (** and so is the right one *)
  ; abs_root' : obs_root Ξ P'
    (** The left expression is well formed *)
  ; abs_typed : Θ ⍮ Ξ ⍮ Ψ ⊢ᵐ P ≈ P
    (** The left abstracted expression is well formed under the left
        parameters *)
  ; abs_inner_eq : Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ᵐ F ≈ F
    (** The right one is well formed under the right parameters *)
  ; abs_inner_typed' : Θ ⍮ Ξ ⍮ D' ++ Ψ ⊢ᵐ F' ≈ F'
    (** The left expression is the left abstracted one, abstracted *)
  ; abs_sim : up_sim Θ Ξ Ψ D P F
    (** and the right one the right one *)
  ; abs_sim' : up_sim Θ Ξ Ψ D' P' F'
    (** Past a selection, the left expression is wholly the left
        abstracted one, abstracted *)
  ; abs_whole : m = false -> up_whole Θ Ξ Ψ D P F
    (** and the right one the right one *)
  ; abs_whole' : m = false -> up_whole Θ Ξ Ψ D' P' F'
    (** The abstracted expressions are compared along paths *)
  ; abs_conv : modexp_conv_m m Θ Ξ (D ++ Ψ) F F'
    (** The left abstracted expression denotes no open frame *)
  ; abs_frame_free : forall R, mdenote Θ Ξ (D ++ Ψ) F R -> ~ desc_reads_frame Ξ R
    (** and neither does the right one *)
  ; abs_frame_free' : forall R, mdenote Θ Ξ (D' ++ Ψ) F' R -> ~ desc_reads_frame Ξ R
    (** The right abstracted expression is well formed under the left
        parameters too *)
  ; abs_inner_typed_left' : Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ᵐ F' ≈ F'
    (** Where the abstracted expressions denote closed modules at no
        argument, their paths name equal modules *)
  ; abs_root_units : forall RQ RQ' p T Φ p' T' Φ', mdenote Θ Ξ (D ++ Ψ) F RQ -> mdenote Θ Ξ (D ++ Ψ) F' RQ' ->
      mdesc_mod RQ = Some (mdesc_closed nil p T Φ nil) -> mdesc_mod RQ' = Some (mdesc_closed nil p' T' Φ' nil) ->
      Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ᵐ qname_mod p ≈ qname_mod p' }.

(** A member read abstracted has the module part of the member,
    abstracted. *)
Lemma named_read_mod : forall Θ Ξ Ψ D Q y XQ X, named_read Θ Ξ Ψ D Q y XQ X -> mdesc_mod X = option_map (mdesc_up D) (mdesc_mod XQ).
Proof. intros * []; intros; rewrite mdesc_mod_up; [| rewrite Soundness.Modules.Sel.mdesc_mod_named ]; reflexivity. Qed.

(** A member selected from a well-formed module expression read through
    what it denotes reads no open frame. *)
Lemma sel_frame_free : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ F F' y R, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ F ≈ F' -> obs_root Ξ F ->
    mdenote Θ Ξ Γ (me_mem F y) R -> ~ desc_reads_frame Ξ R.
Proof.
  intros * Hg * HF HQ Hm; destruct (mdenote_mem_obs_inv _ _ Hg _ _ _ _ HQ Hm) as (R0 & Rm & Γy & E & rd & R1 & HR0 & Hd & He & Hed & Hr).
  exact (entry_read_frame_free _ _ Hg _ _ _ _ _ _ _ _ _ _ _ HF HR0 Hd He Hed Hr).
Qed.

(** A module expression denotes the same under two telescopes of
    assumptions of one length. *)
Lemma mdenote_ass_swap : forall Θ Ξ D D' Ψ H R, all_assumptions D -> all_assumptions D' -> length D = length D' ->
    mdenote Θ Ξ (D ++ Ψ) H R -> mdenote Θ Ξ (D' ++ Ψ) H R.
Proof. intros * Ha Ha' Hl Hm; exact (proj1 (mdenote_slots_agree Θ Ξ) _ _ _ Hm _ (slots_agree_ass _ _ _ Ha Ha' Hl)). Qed.

(** A closed module at no argument and no outside parameter is one before
    a substitution. *)
Lemma closed_bare_sub_back : forall R σ p T Φ, mdesc_mod (mdesc_sub R σ) = Some (mdesc_closed nil p T Φ nil) ->
    mdesc_mod R = Some (mdesc_closed nil p T Φ nil).
Proof.
  intros * H; destruct (mdesc_mod_sub_inv _ _ _ H) as (R' & HR' & E); rewrite HR'.
  destruct R' as [| | Θ0 p0 T0 Φ0 Ns |]; cbn in E; try discriminate.
  injection E as E1 <- <- <- E2.
  destruct Θ0; cbn in E1; [| discriminate ]; destruct Ns; cbn in E2; [ reflexivity | discriminate ].
Qed.

(** A member read abstracted is the member abstracted, or, read bare from
    a closed module under parameters, its name abstracted. *)
Lemma named_read_cases : forall Θ Ξ Ψ D Q y XQ X, named_read Θ Ξ Ψ D Q y XQ X ->
    (X = mdesc_up D XQ /\ (forall r A, XQ = mdesc_term r A None -> D = nil)) \/
    (D <> nil /\ exists RQ p T Φ r A, mdenote Θ Ξ (D ++ Ψ) Q RQ /\ mdesc_mod RQ = Some (mdesc_closed nil p T Φ nil) /\
       XQ = mdesc_term r A None /\ X = mdesc_up D (mdesc_term r A (Some (a_mem (qname_mod p) y)))).
Proof.
  intros * [Hn | RQ p T Φ HRQ HRQm].
  - left; split; [ reflexivity | exact Hn ].
  - destruct D as [| e D].
    + left; split; [ rewrite mdesc_named_nil; reflexivity | reflexivity ].
    + assert (E : mdesc_named (e :: D) nil (a_mem (qname_mod p) y) XQ = mdesc_self (a_mem (qname_mod p) y) XQ) by reflexivity.
      rewrite E; destruct XQ as [r A [M |] | | |]; cbn [mdesc_self];
        first [ right; split; [ discriminate | do 6 eexists; repeat split; eassumption ] | left; split; [ reflexivity | intros ? ? [=] ] ].
Qed.

(** A member with a module part read abstracted is the member, wholly,
    abstracted. *)
Lemma named_read_whole : forall Θ Ξ Ψ D Q y XQ X, named_read Θ Ξ Ψ D Q y XQ X -> mdesc_mod X <> None -> X = mdesc_up D XQ.
Proof.
  intros * Hn Hm; destruct (named_read_cases _ _ _ _ _ _ _ _ Hn) as [(-> & _) | (_ & RQ & p & T & Φ & r & A & _ & _ & -> & ->)];
    [ reflexivity | rewrite mdesc_mod_up in Hm; contradiction ].
Qed.

(** A selection of a module from abstractions is an abstraction of the
    selections, wholly. *)
Lemma abs_mem : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall m Ψ D D' P P' F F' y, abs_setting m Θ Ξ Ψ D D' P P' F F' ->
    ((exists X Xm, mdenote Θ Ξ Ψ (me_mem P y) X /\ mdesc_mod X = Some Xm) \/
     (exists X' Xm', mdenote Θ Ξ Ψ (me_mem P' y) X' /\ mdesc_mod X' = Some Xm')) ->
    abs_setting false Θ Ξ Ψ D D' (me_mem P y) (me_mem P' y) (me_mem F y) (me_mem F' y).
Proof.
  intros * Hg * HA Hex; destruct HA as [Ha Ha' HD HP HP' HPP HFF HFF' HS HS' _ _ HC HFr HFr' HF'F' _].
  pose proof (ext_eq_length _ _ _ _ _ HD) as Hl.
  pose proof (presup_modexp_eq_ctx HFF) as HΓ.
  pose proof (obs_root_of_frame_free _ _ Hg _ _ _ HFF HFr) as HQ.
  pose proof (obs_root_of_frame_free _ _ Hg _ _ _ HFF' HFr') as HQ'.
  pose proof (mem_up _ _ Hg _ _ _ _ y HP HQ HFF HS) as [Hu1 Hu2].
  pose proof (mem_up _ _ Hg _ _ _ _ y HP' HQ' HFF' HS') as [Hu1' Hu2'].
  destruct (inner_mem_conv_m _ _ _ _ _ _ y HC HΓ) as [Hi1 Hi2].
  (** The inner selections, both modules *)
  assert (Hin : exists XQ XQm XQ' XQm', mdenote Θ Ξ (D ++ Ψ) (me_mem F y) XQ /\ mdesc_mod XQ = Some XQm /\
                 mdenote Θ Ξ (D ++ Ψ) (me_mem F' y) XQ' /\ mdesc_mod XQ' = Some XQm').
  { destruct Hex as [(X & Xm & HX & HXm) | (X' & Xm' & HX' & HXm')].
    - destruct (Hu1 _ HX) as (XQ & HXQ & Hn); rewrite (named_read_mod _ _ _ _ _ _ _ _ Hn) in HXm.
      destruct (mdesc_mod XQ) as [XQm |] eqn:EXQ; [| discriminate ].
      destruct (Hi1 _ HXQ) as (XQ' & HXQ' & Hlc); pose proof (leaf_unit _ _ _ _ _ Hlc) as Hlu; rewrite EXQ in Hlu.
      destruct (mdesc_mod XQ') as [XQm' |] eqn:EXQ'; cbn in Hlu; [| contradiction ]; eauto 10.
    - destruct (Hu1' _ HX') as (XQ' & HXQ' & Hn); rewrite (named_read_mod _ _ _ _ _ _ _ _ Hn) in HXm'.
      destruct (mdesc_mod XQ') as [XQm' |] eqn:EXQ'; [| discriminate ].
      pose proof (mdenote_ass_swap _ _ _ _ _ _ _ Ha' Ha (eq_sym Hl) HXQ') as HXQ'l.
      destruct (Hi2 _ HXQ'l) as (XQ & HXQ & Hlc); pose proof (leaf_unit _ _ _ _ _ Hlc) as Hlu; rewrite EXQ' in Hlu.
      destruct (mdesc_mod XQ) as [XQm |] eqn:EXQ; cbn in Hlu; [ eauto 10 | contradiction ]. }
  destruct Hin as (XQ & XQm & XQ' & XQm' & HXQ & EXQ & HXQ' & EXQ').
  destruct (desc_ok_mod_tele _ _ Hg _ _ _ (sel_desc_ok _ _ _ _ _ _ _ HFF HXQ) EXQ) as [TQ HTQ].
  destruct (desc_ok_mod_tele _ _ Hg _ _ _ (sel_desc_ok _ _ _ _ _ _ _ HF'F' HXQ') EXQ') as [TQ' HTQ'].
  pose proof (mdenote_ass_swap _ _ _ _ _ _ _ Ha Ha' Hl HXQ') as HXQ'r.
  destruct (Hu2 _ HXQ) as (X & HX & Hn).
  destruct (Hu2' _ HXQ'r) as (X' & HX' & Hn').
  pose proof (named_read_mod _ _ _ _ _ _ _ _ Hn) as EX; rewrite EXQ in EX.
  pose proof (named_read_mod _ _ _ _ _ _ _ _ Hn') as EX'; rewrite EXQ' in EX'.
  destruct (desc_ok_mod_tele _ _ Hg _ _ _ (sel_desc_ok _ _ _ _ _ _ _ HPP HX) EX) as [T HT].
  constructor; try assumption.
  - exact (obs_root_step _ _ Hg _ (ps_mem y) HP).
  - exact (obs_root_step _ _ Hg _ (ps_mem y) HP').
  - eapply wf_me_mem; eassumption.
  - eapply wf_me_mem; eassumption.
  - eapply wf_me_mem; eassumption.
  - split.
    + intros X1 HX1; destruct (Hu1 _ HX1) as (XQ1 & HXQ1 & Hn1); exists XQ1; split; [ exact HXQ1 | exact (named_read_mod _ _ _ _ _ _ _ _ Hn1) ].
    + intros XQ1 HXQ1; destruct (Hu2 _ HXQ1) as (X1 & HX1 & Hn1); exists X1; split; [ exact HX1 | exact (named_read_mod _ _ _ _ _ _ _ _ Hn1) ].
  - split.
    + intros X1 HX1; destruct (Hu1' _ HX1) as (XQ1 & HXQ1 & Hn1); exists XQ1; split; [ exact HXQ1 | exact (named_read_mod _ _ _ _ _ _ _ _ Hn1) ].
    + intros XQ1 HXQ1; destruct (Hu2' _ HXQ1) as (X1 & HX1 & Hn1); exists X1; split; [ exact HX1 | exact (named_read_mod _ _ _ _ _ _ _ _ Hn1) ].
  - intros _; split.
    + intros X1 HX1; destruct (Hu1 _ HX1) as (XQ1 & HXQ1 & Hn1); exists XQ1; split; [ exact HXQ1 |].
      apply (named_read_whole _ _ _ _ _ _ _ _ Hn1); rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HX1 _ HX), EX; discriminate.
    + intros XQ1 HXQ1; destruct (Hu2 _ HXQ1) as (X1 & HX1 & Hn1); exists X1; split; [ exact HX1 |].
      apply (named_read_whole _ _ _ _ _ _ _ _ Hn1).
      rewrite (named_read_mod _ _ _ _ _ _ _ _ Hn1), (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HXQ1 _ HXQ), EXQ; discriminate.
  - intros _; split.
    + intros X1 HX1; destruct (Hu1' _ HX1) as (XQ1 & HXQ1 & Hn1); exists XQ1; split; [ exact HXQ1 |].
      apply (named_read_whole _ _ _ _ _ _ _ _ Hn1); rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HX1 _ HX'), EX'; discriminate.
    + intros XQ1 HXQ1; destruct (Hu2' _ HXQ1) as (X1 & HX1 & Hn1); exists X1; split; [ exact HX1 |].
      apply (named_read_whole _ _ _ _ _ _ _ _ Hn1).
      rewrite (named_read_mod _ _ _ _ _ _ _ _ Hn1), (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HXQ1 _ HXQ'r), EXQ'; discriminate.
  - exact (modexp_conv_m_mem _ _ _ _ _ _ _ HC).
  - intros R HR; exact (sel_frame_free _ _ Hg _ _ _ _ _ HFF HQ HR).
  - intros R HR; exact (sel_frame_free _ _ Hg _ _ _ _ _ HFF' HQ' HR).
  - eapply wf_me_mem; [ exact HF'F' | exact HXQ' | exact HTQ' | exact HXQ' | exact HTQ' ].
  - intros RQ1 RQ1' q1 Tq Φq q1' Tq' Φq' HR1 HR1' E1 E1'.
    destruct (Hi1 _ HR1) as (R2 & HR2 & Hl2); rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR2 _ HR1') in Hl2.
    pose proof (leaf_unit _ _ _ _ _ Hl2) as Hu; rewrite E1, E1' in Hu; exact Hu.
Qed.

(** The outermost parameter of an abstraction is the outermost one it is
    abstracted over. *)
Lemma up_head : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ D P F F0 R T B0 T1 D1 κ B, up_sim Θ Ξ Ψ D P F -> Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ᵐ F ≈ F0 ->
    mdenote Θ Ξ Ψ P R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B0, T1) -> D = D1 ++ ce_ass κ B :: nil -> B0 = B.
Proof.
  intros * Hg * [H1 _] HFF Hm Ht Hv ->.
  destruct (H1 _ Hm) as (RQ & HRQ & Hmd).
  destruct (mod_of_tele _ _ Ht) as [Rm HRm]; rewrite HRm in Hmd.
  destruct (mdesc_mod RQ) as [RQm |] eqn:EQ; cbn in Hmd; [ injection Hmd as -> | discriminate ].
  pose proof (gctx_valid_syn _ _ Hg) as Hvs.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ HFF Hvs) as (_ & HR & _).
  destruct (desc_ok_mod_tele _ _ Hg _ _ _ (HR _ HRQ) EQ) as [TQ HTQ]; unfold mdesc_mod_tele in HTQ, Ht; rewrite EQ in HTQ; rewrite HRm in Ht.
  rewrite (mdesc_tele_up _ _ _ HTQ) in Ht; injection Ht as <-.
  rewrite List.app_assoc, tele_view_last in Hv; injection Hv as <- _; reflexivity.
Qed.

(** An abstraction applied to an argument is the abstraction of what it
    abstracts, the outermost parameter instantiated. *)
Lemma up_sim_app : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ D1 κ B P F F0 R Rm N Ψ1 τ, up_sim Θ Ξ Ψ (D1 ++ ce_ass κ B :: nil) P F ->
    Θ ⍮ Ξ ⍮ D1 ++ ce_ass κ B :: Ψ ⊢ᵐ F ≈ F0 -> mdenote Θ Ξ Ψ P R -> mdesc_mod R = Some Rm ->
    τ = sb_qn (length D1) (Id,,N) -> Θ ⍮ Ξ ⍮ Ψ1 ⊢ˢ τ : D1 ++ ce_ass κ B :: Ψ -> Ψ1 = tele_sub D1 (Id,,N) ++ Ψ ->
    up_sim Θ Ξ Ψ (tele_sub D1 (Id,,N)) (me_app P N) F[τ]ᵐ.
Proof.
  intros * Hg * [H1 H2] HFF Hm Hmd -> Hτ ->; rewrite <- List.app_assoc in H1, H2; cbn [List.app] in H1, H2.
  (** Every description of [P] is [R] *)
  assert (HR : forall R0, mdenote Θ Ξ Ψ P R0 -> R0 = R) by (intros; eapply (proj1 (mdenote_functional_all _ _ Hg)); eassumption).
  assert (Hrel : forall RQ, mdenote Θ Ξ (D1 ++ ce_ass κ B :: Ψ) F RQ -> exists RQm, mdesc_mod RQ = Some RQm /\ Rm = mdesc_up (D1 ++ ce_ass κ B :: nil) RQm).
  { intros RQ HRQ; destruct (H2 _ HRQ) as (R0 & HR0 & E); rewrite (HR _ HR0), Hmd in E.
    destruct (mdesc_mod RQ) as [RQm |]; cbn in E; [ injection E as ->; eauto | discriminate ]. }
  split.
  - intros X HX; destruct (mdenote_app_inv _ _ _ _ _ _ HX) as (R0 & HR0 & Ha); rewrite (HR _ HR0) in Ha.
    destruct (H1 _ Hm) as (RQ & HRQ & _); destruct (Hrel _ HRQ) as (RQm & EQ & ->).
    exists (mdesc_sub RQ (sb_qn (length D1) (Id,,N))); split; [ exact (wf_sub_mdenote _ _ _ _ _ _ _ _ HFF HRQ Hτ) |].
    rewrite (mdesc_mod_sub _ _ _ EQ); cbn [option_map].
    destruct (proj1 (mdesc_at_mod_part _ _ N Hmd) _ Ha) as (Xm & Ha' & HXm); rewrite mdesc_at_up in Ha'; injection Ha' as <-; exact HXm.
  - intros RQ1 HRQ1.
    destruct (H1 _ Hm) as (RQ & HRQ & _); destruct (Hrel _ HRQ) as (RQm & EQ & ERm).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HRQ1 _ (wf_sub_mdenote _ _ _ _ _ _ _ _ HFF HRQ Hτ)).
    pose proof (mdesc_at_up D1 κ B RQm N) as Hat; rewrite <- ERm in Hat.
    destruct (proj2 (mdesc_at_mod_part _ _ N Hmd) _ Hat) as (X & Ha & HXm).
    exists X; split; [ econstructor; eassumption |].
    rewrite HXm, (mdesc_mod_sub _ _ _ EQ); reflexivity.
Qed.

(** The outermost parameter of a well-formed module is of an evaluated
    sort. *)
Lemma head_evaluated_of : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ P P0 R T B T1, Θ ⍮ Ξ ⍮ Ψ ⊢ᵐ P ≈ P0 -> mdenote Θ Ξ Ψ P R ->
    mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) -> exists Srt, evaluated_sort Srt /\ Θ ⍮ Ξ ⍮ Ψ ⊢ B : Srt.
Proof.
  intros * Hg * HP Hm Ht Hv.
  destruct (desc_of_props _ _ _ _ (ex_intro _ _ (conj (wf_modexp_eq_refl_left HP) Hm))) as (_ & Hok & Hc & _).
  destruct (mod_of_tele _ _ Ht) as [Rm HRm].
  rewrite <- (mdesc_mod_tele_mod_part _ _ HRm) in Ht; unfold mdesc_mod_tele in Ht; rewrite (mdesc_mod_idem _ _ HRm) in Ht.
  exact (desc_ok_head_evaluated _ _ Hg _ _ _ _ _ (desc_ok_mod _ _ Hg _ _ _ Hok HRm) (mdesc_canonical_mod _ _ _ _ Hc HRm) Ht Hv).
Qed.

(** An abstraction of a well-formed module expression denotes a module. *)
Lemma up_exists : forall Θ Ξ Ψ D P F F0, up_sim Θ Ξ Ψ D P F -> Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ᵐ F ≈ F0 ->
    exists R Rm, mdenote Θ Ξ Ψ P R /\ mdesc_mod R = Some Rm.
Proof.
  intros * [_ H2] HFF.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HFF) as (_ & (RF & RFm & HRF & Hmd) & _).
  destruct (H2 _ HRF) as (R & HR & E); rewrite Hmd in E; eauto.
Qed.

(** An abstraction takes the parameters it is abstracted over last. *)
Lemma up_tele : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ D P F F0 R Rm, up_sim Θ Ξ Ψ D P F -> Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ᵐ F ≈ F0 ->
    mdenote Θ Ξ Ψ P R -> mdesc_mod R = Some Rm -> exists TQ, mdesc_mod_tele R = Some (TQ ++ D).
Proof.
  intros * Hg * [H1 _] HFF Hm HRm.
  destruct (H1 _ Hm) as (RQ & HRQ & Hmd); rewrite HRm in Hmd.
  destruct (mdesc_mod RQ) as [RQm |] eqn:EQ; cbn in Hmd; [ injection Hmd as -> | discriminate ].
  pose proof (gctx_valid_syn _ _ Hg) as Hvs.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ HFF Hvs) as (_ & HR & _).
  destruct (desc_ok_mod_tele _ _ Hg _ _ _ (HR _ HRQ) EQ) as [TQ HTQ]; unfold mdesc_mod_tele in HTQ |- *; rewrite EQ in HTQ; rewrite HRm.
  exists TQ; exact (mdesc_tele_up _ _ _ HTQ).
Qed.

(** [up_sim_app], wholly. *)
Lemma up_whole_app : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ D1 κ B P F F0 N Ψ1 τ, up_whole Θ Ξ Ψ (D1 ++ ce_ass κ B :: nil) P F ->
    Θ ⍮ Ξ ⍮ D1 ++ ce_ass κ B :: Ψ ⊢ᵐ F ≈ F0 ->
    τ = sb_qn (length D1) (Id,,N) -> Θ ⍮ Ξ ⍮ Ψ1 ⊢ˢ τ : D1 ++ ce_ass κ B :: Ψ -> Ψ1 = tele_sub D1 (Id,,N) ++ Ψ ->
    up_whole Θ Ξ Ψ (tele_sub D1 (Id,,N)) (me_app P N) F[τ]ᵐ.
Proof.
  intros * Hg * [W1 W2] HFF -> Hτ ->; rewrite <- List.app_assoc in W1, W2; cbn [List.app] in W1, W2.
  split.
  - intros X1 HX1; destruct (mdenote_app_inv _ _ _ _ _ _ HX1) as (X0 & HX0 & Ha0).
    destruct (W1 _ HX0) as (XQ0 & HXQ0 & ->); rewrite mdesc_at_up in Ha0; injection Ha0 as <-.
    eexists; split; [ exact (wf_sub_mdenote _ _ _ _ _ _ _ _ HFF HXQ0 Hτ) | reflexivity ].
  - intros XQ1 HXQ1.
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HFF) as (_ & (XQ0 & _ & HXQ0 & _) & _).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HXQ1 _ (wf_sub_mdenote _ _ _ _ _ _ _ _ HFF HXQ0 Hτ)).
    destruct (W2 _ HXQ0) as (X0 & HX0 & ->).
    eexists; split; [ econstructor; [ exact HX0 | apply mdesc_at_up ] | reflexivity ].
Qed.

(** Abstractions applied to two equal arguments are abstractions, over the
    rest of the parameters, of what they abstract with the outermost
    parameter instantiated. *)
Lemma abs_app_cons : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall m Ψ D D' P P' F F' R T B0 T1 N N', abs_setting m Θ Ξ Ψ D D' P P' F F' -> D <> nil ->
    mdenote Θ Ξ Ψ P R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B0, T1) -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : B0 ->
    exists D1 D1' F1 F1', abs_setting m Θ Ξ Ψ D1 D1' (me_app P N) (me_app P' N') F1 F1'.
Proof.
  intros * Hg * HA Hn Hm Ht Hv HN; destruct HA as [Ha Ha' HD HP HP' HPP HFF HFF' HS HS' HW HW' HC HFr HFr' HFl' HUn].
  destruct D as [| e D1] using List.rev_ind; [ contradiction | clear IHD1 ].
  destruct D' as [| e' D1'] using List.rev_ind; [ apply ext_eq_length in HD; rewrite List.length_app in HD; cbn in HD; lia | clear IHD1' ].
  apply List.Forall_app in Ha as [Ha1 Hae]; apply List.Forall_app in Ha' as [Ha1' Hae'].
  inversion Hae as [| ? ? (κ & B & ->) _]; inversion Hae' as [| ? ? (κ' & B' & ->) _]; subst.
  destruct (ext_eq_last_head _ _ _ _ _ _ _ _ _ HD) as (<- & [S1 HS1 S2 HS2 _ HB HB' HBB HB'B]); cbn [List.app] in HB, HB', HBB, HB'B.
  pose proof (up_head _ _ Hg _ _ _ _ _ _ _ _ _ _ _ _ HS HFF Hm Ht Hv eq_refl) as ->.
  assert (Hl : length D1' = length D1) by (apply ext_eq_length in HD; rewrite !List.length_app in HD; cbn in HD; lia).
  pose proof (presup_exp_eq_left HN) as HN1; pose proof (presup_exp_eq_right HN) as HN2.
  assert (HN2' : Θ ⍮ Ξ ⍮ Ψ ⊢ N' : B') by (eapply wf_exp_subtyp'; eassumption).
  pose proof (wf_sub_eq_id_extend _ _ _ _ _ _ _ _ HB HS1 HN1 HN2 HN) as Hσ.
  pose proof (wf_sub_eq_id_extend _ _ _ _ _ _ _ _ HB' HS2 HN2' HN2' (wf_exp_eq_refl HN2')) as Hσ'.
  pose proof HFF as HFF0; pose proof HFF' as HFF0'; pose proof HC as HC0; pose proof HFr as HFr0; pose proof HFr' as HFr0'.
  pose proof HFl' as HFl0'; pose proof HUn as HUn0.
  rewrite <- List.app_assoc in HFF0, HFF0', HC0, HFr0, HFr0', HFl0', HUn0; cbn [List.app] in HFF0, HFF0', HC0, HFr0, HFr0', HFl0', HUn0.
  pose proof (sb_qn_eq_ext _ _ _ _ _ Ha1 (presup_modexp_eq_ctx HFF0) Hσ) as Hq.
  pose proof (sb_qn_eq_ext _ _ _ _ _ Ha1' (presup_modexp_eq_ctx HFF0') Hσ') as Hq'.
  destruct (mod_of_tele _ _ Ht) as [Rm HRm].
  destruct (up_exists _ _ _ _ _ _ _ HS' HFF') as (R' & Rm' & Hm' & HRm').
  destruct (up_tele _ _ Hg _ _ _ _ _ _ _ HS' HFF' Hm' HRm') as [TQ' Ht'].
  assert (Hv' : tele_view (TQ' ++ D1' ++ ce_ass κ B' :: nil) = Some (B', TQ' ++ D1')) by (rewrite List.app_assoc; apply tele_view_last).
  destruct (head_evaluated_of _ _ Hg _ _ _ _ _ _ _ HPP Hm Ht Hv) as (Sv & HSv & HBv).
  exists (tele_sub D1 (Id,,N)), (tele_sub D1' (Id,,N')), F[sb_qn (length D1) (Id,,N)]ᵐ, F'[sb_qn (length D1') (Id,,N')]ᵐ.
  constructor.
  - exact (all_assumptions_sub _ _ Ha1).
  - exact (all_assumptions_sub _ _ Ha1').
  - exact (ext_eq_inst _ _ _ _ _ _ _ _ _ _ Ha1 Ha1' HD HN).
  - left; reflexivity.
  - left; reflexivity.
  - eapply wf_me_app; [ exact HPP | exact Hm | exact Ht | exact Hv | exact HBv | exact HSv | exact HN1 | exact (wf_exp_eq_refl HN1)
                      | exact Hm | exact Ht | exact Hv | exact HBv | exact HSv | exact HN1 ].
  - exact (sub_preserves_modexp _ _ _ _ _ _ _ HFF0 (wf_sub_eq_left _ _ _ _ _ _ Hq)).
  - exact (sub_preserves_modexp _ _ _ _ _ _ _ HFF0' (wf_sub_eq_left _ _ _ _ _ _ Hq')).
  - exact (up_sim_app _ _ Hg _ _ _ _ _ _ _ _ _ _ _ _ HS HFF0 Hm HRm eq_refl (wf_sub_eq_left _ _ _ _ _ _ Hq) eq_refl).
  - exact (up_sim_app _ _ Hg _ _ _ _ _ _ _ _ _ _ _ _ HS' HFF0' Hm' HRm' eq_refl (wf_sub_eq_left _ _ _ _ _ _ Hq') eq_refl).
  - intros Hm0; exact (up_whole_app _ _ Hg _ _ _ _ _ _ _ _ _ _ (HW Hm0) HFF0 eq_refl (wf_sub_eq_left _ _ _ _ _ _ Hq) eq_refl).
  - intros Hm0; exact (up_whole_app _ _ Hg _ _ _ _ _ _ _ _ _ _ (HW' Hm0) HFF0' eq_refl (wf_sub_eq_left _ _ _ _ _ _ Hq') eq_refl).
  - rewrite Hl; exact (modexp_conv_m_sub _ _ _ _ _ _ _ _ _ HC0 Hq).
  - intros R1 HR1 Hr.
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HFF0) as (_ & (RQ0 & _ & HRQ0 & _) & _).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR1 _ (wf_sub_mdenote _ _ _ _ _ _ _ _ HFF0 HRQ0 (wf_sub_eq_left _ _ _ _ _ _ Hq))) in Hr.
    exact (HFr0 _ HRQ0 (desc_reads_frame_sub _ _ _ Hr)).
  - intros R1 HR1 Hr.
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HFF0') as (_ & (RQ0 & _ & HRQ0 & _) & _).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR1 _ (wf_sub_mdenote _ _ _ _ _ _ _ _ HFF0' HRQ0 (wf_sub_eq_left _ _ _ _ _ _ Hq'))) in Hr.
    exact (HFr0' _ HRQ0 (desc_reads_frame_sub _ _ _ Hr)).
  - rewrite Hl; exact (sub_preserves_modexp _ _ _ _ _ _ _ HFl0' (wf_sub_eq_right _ _ _ _ _ _ Hq)).
  - rewrite Hl; intros RQ1 RQ1' q1 Tq Φq q1' Tq' Φq' HR1 HR1' E1 E1'.
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HFF0) as (_ & (RQ0 & _ & HRQ0 & _) & _).
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HFl0') as (_ & (RQ0' & _ & HRQ0' & _) & _).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR1 _ (wf_sub_mdenote _ _ _ _ _ _ _ _ HFF0 HRQ0 (wf_sub_eq_left _ _ _ _ _ _ Hq))) in E1.
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR1' _ (wf_sub_mdenote _ _ _ _ _ _ _ _ HFl0' HRQ0' (wf_sub_eq_right _ _ _ _ _ _ Hq))) in E1'.
    pose proof (HUn0 _ _ _ _ _ _ _ _ HRQ0 HRQ0' (closed_bare_sub_back _ _ _ _ _ E1) (closed_bare_sub_back _ _ _ _ _ E1')) as Hu.
    pose proof (sub_preserves_modexp _ _ _ _ _ _ _ Hu (wf_sub_eq_left _ _ _ _ _ _ Hq)) as Hu'; rewrite !qname_mod_sub in Hu'; exact Hu'.
Qed.

(** Under no parameter, [up_sim] survives an application. *)
Lemma up_sim_nil_app : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ P F R Rm N, up_sim Θ Ξ Ψ nil P F -> mdenote Θ Ξ Ψ P R -> mdesc_mod R = Some Rm ->
    up_sim Θ Ξ Ψ nil (me_app P N) (me_app F N).
Proof.
  intros * Hg * [H1 H2] Hm Hmd; cbn [List.app] in *.
  assert (HR : forall R0, mdenote Θ Ξ Ψ P R0 -> R0 = R) by (intros; eapply (proj1 (mdenote_functional_all _ _ Hg)); eassumption).
  split; cbn [List.app].
  - intros X1 HX1; destruct (mdenote_app_inv _ _ _ _ _ _ HX1) as (X0 & HX0 & Ha0); rewrite (HR _ HX0) in Ha0.
    destruct (H1 _ Hm) as (RQ & HRQ & E); rewrite Hmd in E.
    destruct (mdesc_mod RQ) as [RQm |] eqn:EQ; cbn in E; [ injection E as E; rewrite mdesc_up_nil in E; subst RQm | discriminate ].
    destruct (proj1 (mdesc_at_mod_part _ _ N Hmd) _ Ha0) as (Xm & Ha' & HXm).
    destruct (proj2 (mdesc_at_mod_part _ _ N EQ) _ Ha') as (XQ1 & Ha1 & HXQm).
    exists XQ1; split; [ eapply mdenote_app; eassumption | rewrite HXm, HXQm; cbn; rewrite mdesc_up_nil; reflexivity ].
  - intros XQ1 HXQ1; destruct (mdenote_app_inv _ _ _ _ _ _ HXQ1) as (RQ & HRQ & Ha1).
    destruct (H2 _ HRQ) as (R0 & HR0 & E); rewrite (HR _ HR0), Hmd in E.
    destruct (mdesc_mod RQ) as [RQm |] eqn:EQ; cbn in E; [ injection E as E; rewrite mdesc_up_nil in E; subst RQm | discriminate ].
    destruct (proj1 (mdesc_at_mod_part _ _ N EQ) _ Ha1) as (Xm & Ha' & HXm).
    destruct (proj2 (mdesc_at_mod_part _ _ N Hmd) _ Ha') as (X1 & Ha0 & HX1m).
    exists X1; split; [ eapply mdenote_app; [ exact Hm | exact Ha0 ] | rewrite HX1m, HXm; cbn; rewrite mdesc_up_nil; reflexivity ].
Qed.

(** Under no parameter, [up_whole] survives an application. *)
Lemma up_whole_nil_app : forall Θ Ξ Ψ P F N, up_whole Θ Ξ Ψ nil P F -> up_whole Θ Ξ Ψ nil (me_app P N) (me_app F N).
Proof.
  intros * [W1 W2]; cbn [List.app] in *; split; cbn [List.app].
  - intros X1 HX1; destruct (mdenote_app_inv _ _ _ _ _ _ HX1) as (X0 & HX0 & Ha0).
    destruct (W1 _ HX0) as (XQ0 & HXQ0 & ->); rewrite mdesc_up_nil in Ha0.
    exists X1; split; [ eapply mdenote_app; [ exact HXQ0 | exact Ha0 ] | rewrite mdesc_up_nil; reflexivity ].
  - intros XQ1 HXQ1; destruct (mdenote_app_inv _ _ _ _ _ _ HXQ1) as (XQ0 & HXQ0 & Ha0).
    destruct (W2 _ HXQ0) as (X0 & HX0 & ->).
    exists XQ1; split; [ eapply mdenote_app; [ exact HX0 | rewrite mdesc_up_nil; exact Ha0 ] | rewrite mdesc_up_nil; reflexivity ].
Qed.

(** Two modules compared at the root are compared up to units. *)
Lemma root_core_of_leaf : forall m Θ Ξ Γ RQ RQ', path_leaf_m m Θ Ξ Γ nil RQ RQ' -> opt_rel (leaf_core Θ Ξ Γ) (mdesc_mod RQ) (mdesc_mod RQ').
Proof.
  intros [|] * Hl; cbn in Hl; [ exact Hl | exact (leaf_core_mod_opt _ _ _ _ _ Hl) ].
Qed.

(** Abstractions over no parameter applied to two equal arguments are the
    applications of what they abstract. *)
Lemma abs_app_nil : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall m Ψ P P' F F' R T B T1 N N', abs_setting m Θ Ξ Ψ nil nil P P' F F' ->
    mdenote Θ Ξ Ψ P R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : B ->
    abs_setting m Θ Ξ Ψ nil nil (me_app P N) (me_app P' N') (me_app F N) (me_app F' N').
Proof.
  intros * Hg * HA Hm Ht Hv HN; destruct HA as [Ha Ha' HD HP HP' HPP HFF HFF' HS HS' HW HW' HC HFr HFr' HF'F' _]; cbn [List.app] in *.
  destruct (mod_of_tele _ _ Ht) as [Rm HRm].
  destruct (proj1 HS _ Hm) as (RQ & HRQ & E); rewrite HRm in E.
  destruct (mdesc_mod RQ) as [RQm |] eqn:EQ; cbn in E; [ injection E as E; rewrite mdesc_up_nil in E; subst RQm | discriminate ].
  assert (HtQ : mdesc_mod_tele RQ = Some T) by (unfold mdesc_mod_tele in *; rewrite EQ; rewrite HRm in Ht; exact Ht).
  destruct (inner_root_conv_m _ _ _ _ _ _ HC (presup_modexp_eq_ctx HFF)) as [Hi1 _].
  destruct (Hi1 _ HRQ) as (RQ' & HRQ' & Hlc).
  destruct (head_core_arg_mod _ _ _ _ _ _ _ _ _ _ (root_core_of_leaf _ _ _ _ _ _ Hlc) HtQ Hv HN) as (T' & B' & T1' & Ht' & Hv' & HN' & HBB & HB'B).
  destruct (proj2 HS' _ HRQ') as (R' & Hm' & E'); cbn [List.app] in Hm'.
  assert (HtR' : mdesc_mod_tele R' = Some T').
  { unfold mdesc_mod_tele in *; rewrite E'; destruct (mdesc_mod RQ') as [RQm' |]; cbn; [ rewrite mdesc_up_nil; exact Ht' | discriminate ]. }
  assert (HRm' : exists Rm', mdesc_mod R' = Some Rm') by exact (mod_of_tele _ _ HtR'); destruct HRm' as [Rm' HRm'].
  pose proof (presup_exp_eq_left HN) as HN1; pose proof (presup_exp_eq_right HN') as HN2'.
  destruct (head_evaluated_of _ _ Hg _ _ _ _ _ _ _ HPP Hm Ht Hv) as (Sv & HSv & HBv).
  destruct (head_evaluated_of _ _ Hg _ _ _ _ _ _ _ HFF' HRQ' Ht' Hv') as (Sv' & HSv' & HBv').
  constructor; cbn [List.app]; try assumption.
  - left; reflexivity.
  - left; reflexivity.
  - eapply wf_me_app; [ exact HPP | exact Hm | exact Ht | exact Hv | exact HBv | exact HSv | exact HN1 | exact (wf_exp_eq_refl HN1)
                      | exact Hm | exact Ht | exact Hv | exact HBv | exact HSv | exact HN1 ].
  - eapply wf_me_app; [ exact HFF | exact HRQ | exact HtQ | exact Hv | exact HBv | exact HSv | exact HN1 | exact (wf_exp_eq_refl HN1)
                      | exact HRQ | exact HtQ | exact Hv | exact HBv | exact HSv | exact HN1 ].
  - eapply wf_me_app; [ exact HFF' | exact HRQ' | exact Ht' | exact Hv' | exact HBv' | exact HSv' | exact HN2' | exact (wf_exp_eq_refl HN2')
                      | exact HRQ' | exact Ht' | exact Hv' | exact HBv' | exact HSv' | exact HN2' ].
  - exact (up_sim_nil_app _ _ Hg _ _ _ _ _ N HS Hm HRm).
  - exact (up_sim_nil_app _ _ Hg _ _ _ _ _ N' HS' Hm' HRm').
  - intros Hm0; exact (up_whole_nil_app _ _ _ _ _ N (HW Hm0)).
  - intros Hm0; exact (up_whole_nil_app _ _ _ _ _ N' (HW' Hm0)).
  - exact (modexp_conv_m_app _ _ _ _ _ _ _ _ _ _ _ _ HC (wf_modexp_eq_refl_left HFF) HRQ HtQ Hv HN).
  - intros R1 HR1 Hr; destruct (mdenote_app_inv _ _ _ _ _ _ HR1) as (R0 & HR0 & Ha0); exact (HFr _ HR0 (desc_reads_frame_at _ _ _ _ Ha0 Hr)).
  - intros R1 HR1 Hr; destruct (mdenote_app_inv _ _ _ _ _ _ HR1) as (R0 & HR0 & Ha0); exact (HFr' _ HR0 (desc_reads_frame_at _ _ _ _ Ha0 Hr)).
  - eapply wf_me_app; [ exact HF'F' | exact HRQ' | exact Ht' | exact Hv' | exact HBv' | exact HSv' | exact HN2' | exact (wf_exp_eq_refl HN2')
                      | exact HRQ' | exact Ht' | exact Hv' | exact HBv' | exact HSv' | exact HN2' ].
  - intros RQ1 RQ1' q1 Tq Φq q1' Tq' Φq' HR1 HR1' E1 E1'.
    destruct (inner_app_conv_m _ _ _ _ _ _ _ _ _ _ _ _ HC (presup_modexp_eq_ctx HFF) HRQ HtQ Hv HN _ HR1) as (X2 & HX2 & Hl2).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HX2 _ HR1') in Hl2.
    exact (unit_of_full _ _ _ _ _ _ _ _ _ Hl2 E1 E1').
Qed.

(** Abstractions applied to two equal arguments are abstractions. *)
Lemma abs_app : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall m Ψ D D' P P' F F' R T B T1 N N', abs_setting m Θ Ξ Ψ D D' P P' F F' ->
    mdenote Θ Ξ Ψ P R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : B ->
    exists D1 D1' F1 F1', abs_setting m Θ Ξ Ψ D1 D1' (me_app P N) (me_app P' N') F1 F1'.
Proof.
  intros * Hg * HA Hm Ht Hv HN; destruct D as [| d D0].
  - pose proof (abs_tele _ _ _ _ _ _ _ _ _ _ HA) as HD; destruct D'; [| apply ext_eq_length in HD; discriminate ].
    exists nil, nil, (me_app F N), (me_app F' N'); exact (abs_app_nil _ _ Hg _ _ _ _ _ _ _ _ _ _ _ _ HA Hm Ht Hv HN).
  - exact (abs_app_cons _ _ Hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ HA ltac:(discriminate) Hm Ht Hv HN).
Qed.

(** The module part of what a well-formed module expression denotes has a
    telescope. *)
Lemma mod_tele_of_typed : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ F F0 R Rm, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ F ≈ F0 -> mdenote Θ Ξ Γ F R -> mdesc_mod R = Some Rm ->
    forall Xm, mdesc_mod Rm = Some Xm -> exists T, mdesc_mod_tele Rm = Some T.
Proof.
  intros * Hg * HFF Hm Hmd Xm _; pose proof (gctx_valid_syn _ _ Hg) as Hvs.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ HFF Hvs) as (_ & HR & _).
  destruct (desc_ok_mod_tele _ _ Hg _ _ _ (HR _ Hm) Hmd) as [T HT]; exists T; rewrite (mdesc_mod_tele_mod_part _ _ Hmd); exact HT.
Qed.

(** The module parts of two well-formed module expressions under equal
    telescopes, compared, abstracted. *)
Lemma leaf_core_up_mods : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ D D' F F1 F' F1' RQ RQ' RQm RQm', all_assumptions D -> all_assumptions D' ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˣ D ≈ D' -> Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ᵐ F ≈ F1 -> Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ᵐ F' ≈ F1' ->
    mdenote Θ Ξ (D ++ Ψ) F RQ -> mdenote Θ Ξ (D ++ Ψ) F' RQ' -> mdesc_mod RQ = Some RQm -> mdesc_mod RQ' = Some RQm' ->
    leaf_core Θ Ξ (D ++ Ψ) RQm RQm' -> leaf_core Θ Ξ Ψ (mdesc_up D RQm) (mdesc_up D' RQm').
Proof.
  intros * Hg * Ha Ha' HD HF HF' Hm Hm' E E' Hl.
  destruct (mdesc_is_mod_parts _ (mdesc_mod_is_mod _ _ E)) as (_ & Ht & _).
  apply leaf_core_up; try assumption.
  - intros A HA; rewrite Ht in HA; discriminate.
  - intros A HA; rewrite Ht in HA; discriminate.
  - exact (mod_tele_of_typed _ _ Hg _ _ _ _ _ HF Hm E).
  - exact (mod_tele_of_typed _ _ Hg _ _ _ _ _ HF' Hm' E').
Qed.

(** The leaves of abstractions at no step, before any selection. *)
Lemma abs_leaf_root_mod : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ D D' P P' F F', abs_setting true Θ Ξ Ψ D D' P P' F F' ->
    (forall X, mdenote Θ Ξ Ψ P X -> exists X', mdenote Θ Ξ Ψ P' X' /\ opt_rel (leaf_core Θ Ξ Ψ) (mdesc_mod X) (mdesc_mod X')) /\
    (forall X', mdenote Θ Ξ Ψ P' X' -> exists X, mdenote Θ Ξ Ψ P X /\ opt_rel (leaf_core Θ Ξ Ψ) (mdesc_mod X) (mdesc_mod X')).
Proof.
  intros * Hg * [Ha Ha' HD _ _ _ HFF HFF' [HS1 HS2] [HS1' HS2'] _ _ HC _ _ HF'F' _].
  pose proof (ext_eq_length _ _ _ _ _ HD) as Hl.
  destruct (inner_root_conv_m _ _ _ _ _ _ HC (presup_modexp_eq_ctx HFF)) as [Hi1 Hi2]; unfold path_leaf_m in Hi1, Hi2; cbn in Hi1, Hi2.
  split.
  - intros X HX; destruct (HS1 _ HX) as (RQ & HRQ & EX).
    destruct (Hi1 _ HRQ) as (RQ' & HRQ' & Hlc).
    destruct (HS2' _ (mdenote_ass_swap _ _ _ _ _ _ _ Ha Ha' Hl HRQ')) as (X' & HX' & EX').
    exists X'; split; [ exact HX' |]; rewrite EX, EX'.
    destruct (mdesc_mod RQ) as [RQm |] eqn:E; destruct (mdesc_mod RQ') as [RQm' |] eqn:E'; cbn in Hlc |- *; try contradiction; [| exact I ].
    exact (leaf_core_up_mods _ _ Hg _ _ _ _ _ _ _ _ _ _ _ Ha Ha' HD HFF HF'F' HRQ HRQ' E E' Hlc).
  - intros X' HX'; destruct (HS1' _ HX') as (RQ' & HRQ' & EX').
    destruct (Hi2 _ (mdenote_ass_swap _ _ _ _ _ _ _ Ha' Ha (eq_sym Hl) HRQ')) as (RQ & HRQ & Hlc).
    destruct (HS2 _ HRQ) as (X & HX & EX).
    exists X; split; [ exact HX |]; rewrite EX, EX'.
    destruct (mdesc_mod RQ) as [RQm |] eqn:E; destruct (mdesc_mod RQ') as [RQm' |] eqn:E'; cbn in Hlc |- *; try contradiction; [| exact I ].
    exact (leaf_core_up_mods _ _ Hg _ _ _ _ _ _ _ _ _ _ _ Ha Ha' HD HFF HF'F' HRQ (mdenote_ass_swap _ _ _ _ _ _ _ Ha' Ha (eq_sym Hl) HRQ') E E' Hlc).
Qed.

(** The term part of a typed description is of the sort of its kind. *)
Lemma desc_ok_type_kind : forall Θ Ξ Γ X A, desc_ok Θ Ξ Γ X -> mdesc_type X = Some A ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : abs_kind_sort (mdesc_kind X) Typeω@i.
Proof.
  intros * Hok HA; inversion Hok; subst; cbn in HA |- *; try discriminate; injection HA as <-; [ eauto |].
  match goal with H : _ ⍮ _ ⍮ ?Θd ++ ?Γ0 ⊢ ?A0 : Typeω@?i |- _ =>
    destruct (ctx_pi_wf _ _ _ _ _ _ ltac:(eassumption) H) as [j Hj]; exists j; exact Hj end.
Qed.

(** A selection from a well-formed module expression denoting the closed
    module [p], bare, is the selection from [p]. *)
Lemma qname_sel : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ F F0 RQ p T Φ y X, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ F ≈ F0 -> mdenote Θ Ξ Γ F RQ ->
    mdesc_mod RQ = Some (mdesc_closed nil p T Φ nil) -> ~ desc_reads_frame Ξ RQ -> obs_root Ξ F ->
    mdenote Θ Ξ Γ (me_mem F y) X -> mdenote Θ Ξ Γ (me_mem (qname_mod p) y) X /\ Θ ⍮ Ξ ⍮ Γ ⊢ᵐ qname_mod p ≈ qname_mod p.
Proof.
  intros * Hg * HF Hm Hmd Hn HQ HX; pose proof (wf_modexp_eq_refl_left HF) as HFF.
  destruct (desc_of_props _ _ _ _ (ex_intro _ _ (conj HFF Hm))) as (_ & _ & Hc & Hx & _).
  destruct (mdesc_unit_denote _ _ _ Hg (mdesc_canonical_mod _ _ _ _ Hc Hmd) (mdesc_mod_is_mod _ _ Hmd) _
              (mdesc_xp_mod _ _ _ _ _ Hx Hmd)) as (RU & HmU & HmdU); cbn [mdesc_unit me_apps] in HmU.
  pose proof (lookup_sound _ _ _ _ _ _ HFF Hm Hmd) as Hls; cbn [mdesc_unit me_apps] in Hls.
  split; [| exact (wf_modexp_eq_refl_right Hls) ].
  assert (HnU : ~ desc_reads_frame Ξ RU) by (unfold desc_reads_frame in *; rewrite HmdU; rewrite Hmd in Hn; exact Hn).
  assert (Hqp : obs_root Ξ (qname_mod p))
    by (right; exists p; split; [ apply qname_mod_qname | exact (frame_free_of_desc _ _ Hg _ _ _ _ (qname_mod_qname p) HmU HnU) ]).
  assert (Hs : mod_sim Θ Ξ Γ F (qname_mod p)).
  { split; intros X1 HX1.
    - rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HX1 _ Hm); exists RU; split; [ exact HmU | rewrite Hmd, HmdU; reflexivity ].
    - rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HX1 _ HmU); exists RQ; split; [ exact Hm | rewrite Hmd, HmdU; reflexivity ]. }
  exact (proj1 (mod_sim_mem _ _ Hg _ _ _ y HQ Hqp Hs X) HX).
Qed.

(** The names of two members with no δ-reduct, read bare from closed
    modules that two compared expressions denote, are equal. *)
Lemma special_names_eq : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ F F' RQ RQ' p T Φ p' T' Φ' y r A A' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ F ≈ F -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ F' ≈ F' -> obs_root Ξ F -> obs_root Ξ F' ->
    mdenote Θ Ξ Γ F RQ -> mdesc_mod RQ = Some (mdesc_closed nil p T Φ nil) -> ~ desc_reads_frame Ξ RQ ->
    mdenote Θ Ξ Γ F' RQ' -> mdesc_mod RQ' = Some (mdesc_closed nil p' T' Φ' nil) -> ~ desc_reads_frame Ξ RQ' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ mdesc_unit (mdesc_closed nil p T Φ nil) ≈ mdesc_unit (mdesc_closed nil p' T' Φ' nil) ->
    mdenote Θ Ξ Γ (me_mem F y) (mdesc_term r A None) -> mdenote Θ Ξ Γ (me_mem F' y) (mdesc_term r A' None) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : abs_kind_sort r Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_mem (qname_mod p) y ≈ a_mem (qname_mod p') y : A.
Proof.
  intros * Hg * HF HF' HQ HQ' Hm Hmd Hn Hm' Hmd' Hn' Hu HX HX' HA; cbn in Hu.
  destruct (qname_sel _ _ Hg _ _ _ _ _ _ _ _ _ HF Hm Hmd Hn HQ HX) as [Hp Hpp].
  destruct (qname_sel _ _ Hg _ _ _ _ _ _ _ _ _ HF' Hm' Hmd' Hn' HQ' HX') as [Hp' Hpp'].
  pose proof (presup_exp_eq_left HA) as HA1; pose proof (presup_exp_eq_right HA) as HA2.
  assert (HS : type_sort (abs_kind_sort r Typeω@i)) by (apply type_sort_abs_kind; constructor).
  destruct (wf_subtyp_of_exp_eq _ _ _ _ _ _ HA1 HA2 HS HA) as [_ HA'A].
  assert (Hty' : Θ ⍮ Ξ ⍮ Γ ⊢ a_mem (qname_mod p') y : A').
  { eapply wf_mem; [ exact Hpp' | exact Hp' | reflexivity | exact HA2 | exact HS | intros M0 [=] ]. }
  eapply wf_exp_eq_mem_cong; [ exact Hu | exact Hp | reflexivity | exact Hp' | reflexivity |].
  eapply wf_exp_subtyp'; [ exact Hty' | exact HA'A ].
Qed.

(** What a well-formed module expression denotes is typed. *)
Lemma desc_ok_of_typed : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ P P0 X, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ P ≈ P0 -> mdenote Θ Ξ Γ P X -> desc_ok Θ Ξ Γ X.
Proof.
  intros * Hg * HP Hm; pose proof (gctx_valid_syn _ _ Hg) as Hv.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ HP Hv) as (_ & HR & _); exact (HR _ Hm).
Qed.

(** Each parameter of a typed abstraction of a term may be abstracted at
    the term's kind. *)
Lemma pk_of_outer : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ D X, desc_ok Θ Ξ Ψ (mdesc_up D X) -> all_assumptions D ->
    forall A, mdesc_type X = Some A -> forall Δ1 κ B Δ2, D = Δ1 ++ ce_ass κ B :: Δ2 -> pi_kinds κ (mdesc_kind X).
Proof.
  intros * Hg * Hok Ha A HA; pose proof (gctx_valid_syn _ _ Hg) as Hv.
  destruct (desc_ok_ty_sorted _ _ Hv _ _ _ Hok (mdesc_type_up _ _ _ HA)) as [(S & _ & HT) _].
  exact (ctx_pi_at_pi_kinds _ _ _ _ _ _ _ Ha HT).
Qed.

(** What shows the same as a term with no δ-reduct is one. *)
Lemma term_none_of_leaf : forall Θ Ξ Γ X X' r' A', leaf_conv Θ Ξ Γ X X' -> X' = mdesc_term r' A' None ->
    exists r A, X = mdesc_term r A None.
Proof.
  intros * Hl ->; pose proof (leaf_type _ _ _ _ _ Hl) as Ht; pose proof (leaf_reduct _ _ _ _ _ Hl) as Hr.
  destruct X as [r A [M |] | | | Θd A M Rm]; cbn in Ht, Hr |- *; try contradiction; eauto.
  - specialize (Hr _ eq_refl); exact (False_ind _ Hr).
  - specialize (Hr _ eq_refl); exact (False_ind _ Hr).
Qed.

(** [path_core], comparing the leaves of paths of no selection by their
    module parts only when [m]. *)
Definition path_core_m (m : bool) (Θ : gdeps) (Ξ : gstack) (Δ : ctx) (s : list path_step) (X X' : mdesc) : Prop :=
  if andb m (path_all_apps s) then opt_rel (leaf_core Θ Ξ Δ) (mdesc_mod X) (mdesc_mod X') else leaf_core Θ Ξ Δ X X'.

(** Wholly abstracted leaves, compared. *)
Lemma abs_leaf_whole : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ D D' P P' F F' XQ XQ', abs_setting false Θ Ξ Ψ D D' P P' F F' ->
    mdenote Θ Ξ (D ++ Ψ) F XQ -> mdenote Θ Ξ (D ++ Ψ) F' XQ' -> leaf_core Θ Ξ (D ++ Ψ) XQ XQ' ->
    mdenote Θ Ξ Ψ P (mdesc_up D XQ) -> leaf_core Θ Ξ Ψ (mdesc_up D XQ) (mdesc_up D' XQ').
Proof.
  intros * Hg * HA HXQ HXQ' Hlc HX; destruct HA as [Ha Ha' HD _ _ HPP HFF _ _ _ _ _ _ _ _ HF'F' _].
  pose proof (desc_ok_of_typed _ _ Hg _ _ _ _ HFF HXQ) as HXQok.
  pose proof (desc_ok_of_typed _ _ Hg _ _ _ _ HF'F' HXQ') as HXQ'ok.
  apply leaf_core_up; try assumption.
  - exact (pk_of_outer _ _ Hg _ _ _ (desc_ok_of_typed _ _ Hg _ _ _ _ HPP HX) Ha).
  - intros A HA; exact (desc_ok_type_kind _ _ _ _ _ HXQok HA).
  - intros Xm HXm; exact (desc_ok_mod_tele _ _ Hg _ _ _ HXQok HXm).
  - intros Xm HXm; exact (desc_ok_mod_tele _ _ Hg _ _ _ HXQ'ok HXm).
Qed.

(** The leaves of abstractions at no step. *)
Lemma abs_leaf_root : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall m Ψ D D' P P' F F', abs_setting m Θ Ξ Ψ D D' P P' F F' ->
    (forall X, mdenote Θ Ξ Ψ P X -> exists X', mdenote Θ Ξ Ψ P' X' /\ path_core_m m Θ Ξ Ψ nil X X') /\
    (forall X', mdenote Θ Ξ Ψ P' X' -> exists X, mdenote Θ Ξ Ψ P X /\ path_core_m m Θ Ξ Ψ nil X X').
Proof.
  intros * Hg [|] * HA; unfold path_core_m; cbn [path_all_apps andb].
  - exact (abs_leaf_root_mod _ _ Hg _ _ _ _ _ _ _ HA).
  - pose proof HA as HA0; destruct HA0 as [Ha Ha' HD _ _ _ HFF HFF' _ _ HW HW' HC _ _ _ _].
    destruct (HW eq_refl) as [W1 W2]; destruct (HW' eq_refl) as [W1' W2'].
    pose proof (ext_eq_length _ _ _ _ _ HD) as Hl.
    destruct (inner_root_conv_m _ _ _ _ _ _ HC (presup_modexp_eq_ctx HFF)) as [Hi1 Hi2]; unfold path_leaf_m in Hi1, Hi2; cbn in Hi1, Hi2.
    split.
    + intros X HX; destruct (W1 _ HX) as (XQ & HXQ & ->).
      destruct (Hi1 _ HXQ) as (XQ' & HXQ' & Hlc).
      destruct (W2' _ (mdenote_ass_swap _ _ _ _ _ _ _ Ha Ha' Hl HXQ')) as (X' & HX' & ->).
      exists (mdesc_up D' XQ'); split; [ exact HX' | exact (abs_leaf_whole _ _ Hg _ _ _ _ _ _ _ _ _ HA HXQ HXQ' Hlc HX) ].
    + intros X' HX'; destruct (W1' _ HX') as (XQ' & HXQ' & ->).
      pose proof (mdenote_ass_swap _ _ _ _ _ _ _ Ha' Ha (eq_sym Hl) HXQ') as HXQ'l.
      destruct (Hi2 _ HXQ'l) as (XQ & HXQ & Hlc).
      destruct (W2 _ HXQ) as (X & HX & ->).
      exists (mdesc_up D XQ); split; [ exact HX | exact (abs_leaf_whole _ _ Hg _ _ _ _ _ _ _ _ _ HA HXQ HXQ'l Hlc HX) ].
Qed.

(** Two members selected from abstractions, compared. *)
Lemma pair_leaf : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall m Ψ D D' P P' F F' y XQ XQ' X X', abs_setting m Θ Ξ Ψ D D' P P' F F' ->
    mdenote Θ Ξ (D ++ Ψ) (me_mem F y) XQ -> mdenote Θ Ξ (D ++ Ψ) (me_mem F' y) XQ' -> leaf_conv Θ Ξ (D ++ Ψ) XQ XQ' ->
    mdenote Θ Ξ Ψ (me_mem P y) X -> mdenote Θ Ξ Ψ (me_mem P' y) X' ->
    named_read Θ Ξ Ψ D F y XQ X -> named_read Θ Ξ Ψ D' F' y XQ' X' -> leaf_core Θ Ξ Ψ X X'.
Proof.
  intros * Hg * HA HXQ HXQ' Hlc HX HX' Hn Hn'.
  destruct HA as [Ha Ha' HD HP HP' HPP HFF HFF' HS HS' _ _ HC HFr HFr' HF'F' HUn].
  pose proof (ext_eq_length _ _ _ _ _ HD) as Hl.
  pose proof (sel_desc_ok _ _ _ _ _ _ _ HPP HX) as HXok.
  pose proof (sel_desc_ok _ _ _ _ _ _ _ HFF HXQ) as HXQok; pose proof (sel_desc_ok _ _ _ _ _ _ _ HF'F' HXQ') as HXQ'ok.
  destruct (named_read_cases _ _ _ _ _ _ _ _ Hn) as [(-> & Hs) | (HnD & RQ & p & T & Φ & r & A & HRQ & HRQm & -> & ->)];
  destruct (named_read_cases _ _ _ _ _ _ _ _ Hn') as [(-> & Hs') | (HnD' & RQ' & p' & T' & Φ' & r' & A' & HRQ' & HRQm' & -> & ->)].
  - apply leaf_core_up; try assumption.
    + exact (leaf_core_of_conv _ _ _ _ _ Hlc).
    + exact (pk_of_outer _ _ Hg _ _ _ HXok Ha).
    + intros A HA; exact (desc_ok_type_kind _ _ _ _ _ HXQok HA).
    + intros Xm HXm; exact (desc_ok_mod_tele _ _ Hg _ _ _ HXQok HXm).
    + intros Xm HXm; exact (desc_ok_mod_tele _ _ Hg _ _ _ HXQ'ok HXm).
  - exfalso; destruct (term_none_of_leaf _ _ _ _ _ _ _ Hlc eq_refl) as (r0 & A0 & E).
    pose proof (Hs _ _ E) as ->; destruct D'; [ exact (HnD' eq_refl) | cbn in Hl; discriminate ].
  - exfalso; destruct (term_none_of_leaf _ _ _ _ _ _ _ (leaf_conv_sym _ _ _ _ _ Hlc) eq_refl) as (r0 & A0 & E).
    pose proof (Hs' _ _ E) as ->; destruct D; [ exact (HnD eq_refl) | cbn in Hl; discriminate ].
  - (** Members of closed modules read bare, under parameters: their names *)
    pose proof (leaf_kind _ _ _ _ _ Hlc) as Hk; cbn in Hk; subst r'.
    pose proof (leaf_type _ _ _ _ _ Hlc) as Ht; cbn in Ht; destruct Ht as [i Hi].
    pose proof (mdenote_ass_swap _ _ _ _ _ _ _ Ha' Ha (eq_sym Hl) HRQ') as HRQ'l.
    assert (HFr'l : forall R, mdenote Θ Ξ (D ++ Ψ) F' R -> ~ desc_reads_frame Ξ R)
      by (intros R HR; exact (HFr' _ (mdenote_ass_swap _ _ _ _ _ _ _ Ha Ha' Hl HR))).
    pose proof (HUn _ _ _ _ _ _ _ _ HRQ HRQ'l HRQm HRQm') as Hu.
    pose proof (special_names_eq _ _ Hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HFF HF'F'
                  (obs_root_of_frame_free _ _ Hg _ _ _ HFF HFr) (obs_root_of_frame_free _ _ Hg _ _ _ HF'F' HFr'l)
                  HRQ HRQm (HFr _ HRQ) HRQ'l HRQm' (HFr'l _ HRQ'l) Hu HXQ HXQ' Hi) as HMM.
    apply leaf_core_up; try assumption.
    + constructor; cbn.
      * reflexivity.
      * exists i; exact Hi.
      * intros A0 [= <-]; exact HMM.
      * exact I.
      * exact I.
      * unfold desc_reads_frame; cbn; split; intros (? & ? & ? & ? & ? & [=] & _).
      * apply no_level_term_iff.
    + exact (pk_of_outer _ _ Hg _ _ _ HXok Ha).
    + intros A0 HA0; exact (desc_ok_type_kind _ _ _ _ _ HXQok HA0).
    + intros Xm [=].
    + intros Xm [=].
Qed.

(** The leaves of abstractions at one selection. *)
Lemma abs_leaf_mem : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall m Ψ D D' P P' F F' y, abs_setting m Θ Ξ Ψ D D' P P' F F' ->
    (forall X, mdenote Θ Ξ Ψ (me_mem P y) X -> exists X', mdenote Θ Ξ Ψ (me_mem P' y) X' /\ leaf_core Θ Ξ Ψ X X') /\
    (forall X', mdenote Θ Ξ Ψ (me_mem P' y) X' -> exists X, mdenote Θ Ξ Ψ (me_mem P y) X /\ leaf_core Θ Ξ Ψ X X').
Proof.
  intros * Hg * HA; pose proof HA as HA0; destruct HA0 as [Ha Ha' HD HP HP' _ HFF HFF' HS HS' _ _ HC HFr HFr' _ _].
  pose proof (ext_eq_length _ _ _ _ _ HD) as Hl.
  pose proof (obs_root_of_frame_free _ _ Hg _ _ _ HFF HFr) as HQ.
  pose proof (obs_root_of_frame_free _ _ Hg _ _ _ HFF' HFr') as HQ'.
  pose proof (mem_up _ _ Hg _ _ _ _ y HP HQ (wf_modexp_eq_refl_left HFF) HS) as [Hu1 Hu2].
  pose proof (mem_up _ _ Hg _ _ _ _ y HP' HQ' HFF' HS') as [Hu1' Hu2'].
  destruct (inner_mem_conv_m _ _ _ _ _ _ y HC (presup_modexp_eq_ctx HFF)) as [Hi1 Hi2].
  split.
  - intros X HX; destruct (Hu1 _ HX) as (XQ & HXQ & Hn).
    destruct (Hi1 _ HXQ) as (XQ' & HXQ' & Hlc).
    destruct (Hu2' _ (mdenote_ass_swap _ _ _ _ _ _ _ Ha Ha' Hl HXQ')) as (X' & HX' & Hn').
    exists X'; split; [ exact HX' | exact (pair_leaf _ _ Hg _ _ _ _ _ _ _ _ _ _ _ _ _ HA HXQ HXQ' Hlc HX HX' Hn Hn') ].
  - intros X' HX'; destruct (Hu1' _ HX') as (XQ' & HXQ' & Hn').
    pose proof (mdenote_ass_swap _ _ _ _ _ _ _ Ha' Ha (eq_sym Hl) HXQ') as HXQ'l.
    destruct (Hi2 _ HXQ'l) as (XQ & HXQ & Hlc).
    destruct (Hu2 _ HXQ) as (X & HX & Hn).
    exists X; split; [ exact HX | exact (pair_leaf _ _ Hg _ _ _ _ _ _ _ _ _ _ _ _ _ HA HXQ HXQ'l Hlc HX HX' Hn Hn') ].
Qed.

(** What a selection is read from has a module part. *)
Lemma sel_mod_of_step : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ Q z R2, mdenote Θ Ξ Δ (me_mem Q z) R2 ->
    exists R Rm, mdenote Θ Ξ Δ Q R /\ mdesc_mod R = Some Rm.
Proof.
  intros * Hg * HR2.
  destruct (step_left_back _ _ Hg _ _ (ps_mem z) _ HR2) as (R1 & HR1).
  destruct (step_mem_mod _ _ Hg _ _ _ _ _ HR2 HR1) as [Rm HRm]; eauto.
Qed.

(** Paths from abstractions compare, up to units. *)
Lemma paths_core_abs : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall s m Ψ D D' P P' F F', abs_setting m Θ Ξ Ψ D D' P P' F F' ->
    path_pairs Θ Ξ Ψ P s ->
    (forall X, mdenote Θ Ξ Ψ (path_left P s) X -> exists X', mdenote Θ Ξ Ψ (path_right P' s) X' /\ path_core_m m Θ Ξ Ψ s X X') /\
    (forall X', mdenote Θ Ξ Ψ (path_right P' s) X' -> exists X, mdenote Θ Ξ Ψ (path_left P s) X /\ path_core_m m Θ Ξ Ψ s X X').
Proof.
  intros Θ Ξ Hg s; induction s as [| st s IH]; intros * HA Hs; [ exact (abs_leaf_root _ _ Hg _ _ _ _ _ _ _ _ HA) |].
  destruct st as [y | N N'].
  - inversion Hs as [| ? ? ? Hs1 | ]; subst; cbn [path_left path_right].
    assert (Hcore : forall X X', path_core_m false Θ Ξ Ψ s X X' -> path_core_m m Θ Ξ Ψ (ps_mem y :: s) X X').
    { unfold path_core_m; cbn [path_all_apps]; rewrite Bool.andb_false_r; intros X X' Hc; exact Hc. }
    destruct s as [| [z | N N'] s2].
    + unfold path_core_m; cbn [path_all_apps]; rewrite Bool.andb_false_r; exact (abs_leaf_mem _ _ Hg _ _ _ _ _ _ _ _ y HA).
    + split.
      * intros X HX; pose proof HX as HX0; cbn [path_left] in HX0.
        destruct (path_left_back _ _ Hg _ _ _ _ HX0) as (R2 & HR2).
        destruct (sel_mod_of_step _ _ Hg _ _ _ _ HR2) as (R & Rm & HR & HRm).
        pose proof (abs_mem _ _ Hg _ _ _ _ _ _ _ _ y HA (or_introl (ex_intro _ R (ex_intro _ Rm (conj HR HRm))))) as HA1.
        destruct (proj1 (IH _ _ _ _ _ _ _ _ HA1 Hs1) _ HX) as (X' & HX' & Hc); eauto.
      * intros X' HX'; pose proof HX' as HX0; cbn [path_right] in HX0.
        destruct (path_right_back _ _ Hg _ _ _ _ HX0) as (R2 & HR2).
        destruct (sel_mod_of_step _ _ Hg _ _ _ _ HR2) as (R & Rm & HR & HRm).
        pose proof (abs_mem _ _ Hg _ _ _ _ _ _ _ _ y HA (or_intror (ex_intro _ R (ex_intro _ Rm (conj HR HRm))))) as HA1.
        destruct (proj2 (IH _ _ _ _ _ _ _ _ HA1 Hs1) _ HX') as (X & HX & Hc); eauto.
    + inversion Hs1 as [| | ? R T B T1 ? ? ? Hm Ht Hv HN Hs2]; subst.
      destruct (mod_of_tele _ _ Ht) as [Rm HRm].
      pose proof (abs_mem _ _ Hg _ _ _ _ _ _ _ _ y HA (or_introl (ex_intro _ R (ex_intro _ Rm (conj Hm HRm))))) as HA1.
      destruct (IH _ _ _ _ _ _ _ _ HA1 Hs1) as [H1 H2]; split.
      * intros X HX; destruct (H1 _ HX) as (X' & HX' & Hc); eauto.
      * intros X' HX'; destruct (H2 _ HX') as (X & HX & Hc); eauto.
  - inversion Hs as [| | ? R T B T1 ? ? ? Hm Ht Hv HN Hs1]; subst; cbn [path_left path_right].
    destruct (abs_app _ _ Hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ HA Hm Ht Hv HN) as (D1 & D1' & F1 & F1' & HA1).
    exact (IH _ _ _ _ _ _ _ _ HA1 Hs1).
Qed.

(** *** Aliases *)

(** An alias literal abstracts its target. *)
Lemma lit_alias_up_sim : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ D F F0, Θ ⍮ Ξ ⍮ D ++ Ψ ⊢ᵐ F ≈ F0 ->
    up_sim Θ Ξ Ψ D (me_lit (gu_mk D (md_alias F))) F.
Proof.
  intros * Hg * HFF; split.
  - intros X HX; pose proof (mdenote_lit_inv _ _ _ _ _ HX) as Hu; inversion Hu; subst.
    eexists; split; [ eassumption |].
    match goal with H : mdesc_mod ?R = Some ?R' |- _ => rewrite H, mdesc_mod_up, (mdesc_mod_idem _ _ H); reflexivity end.
  - intros RQ HRQ.
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HFF) as (_ & (R0 & R0m & HR0 & Hmd) & _).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HRQ _ HR0), Hmd.
    exists (mdesc_up D R0m); split; [ apply mdenote_lit; econstructor; eassumption |].
    rewrite mdesc_mod_up, (mdesc_mod_idem _ _ Hmd); reflexivity.
Qed.

(** A target that is no module still being defined is none under a
    substitution. *)
Lemma frame_free_sub : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ E E0 Δ τ, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E0 -> frame_free_target Θ Ξ Γ E -> Θ ⍮ Ξ ⍮ Δ ⊢ˢ τ : Γ ->
    forall R, mdenote Θ Ξ Δ E[τ]ᵐ R -> ~ desc_reads_frame Ξ R.
Proof.
  intros * Hg * HE (RE & HmE & Hn) Hτ R HR Hr.
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR _ (wf_sub_mdenote _ _ _ _ _ _ _ _ HE HmE Hτ)) in Hr.
  exact (Hn (desc_reads_frame_sub _ _ _ Hr)).
Qed.

(** Two equal aliases are compared along paths ([wf_unit_eq_alias]). *)
Lemma modexp_conv_alias : forall Θ Ξ Γ Δ Δ' E E', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' -> all_assumptions Δ -> all_assumptions Δ' ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ E ≈ E' -> Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊢ᵐ E' ≈ E' ->
    frame_free_target Θ Ξ (Δ ++ Γ) E -> frame_free_target Θ Ξ (Δ' ++ Γ) E' -> modexp_conv Θ Ξ (Δ ++ Γ) E E' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E') ->
    modexp_conv Θ Ξ Γ (me_lit (gu_mk Δ (md_alias E))) (me_lit (gu_mk Δ' (md_alias E'))).
Proof.
  intros * HD Ha Ha' HE HE' Hf Hf' HC HU Ψ σ σ' Hσ.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HE)) as Hg.
  pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hσl; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hσ) as Hσr.
  pose proof (wf_me_lit _ _ _ _ _ HU) as HL.
  assert (HLL : Θ ⍮ Ξ ⍮ Ψ ⊢ᵐ (me_lit (gu_mk Δ (md_alias E)))[σ]ᵐ ≈ (me_lit (gu_mk Δ' (md_alias E')))[σ']ᵐ).
  { eapply wf_me_trans; [ exact (sub_preserves_modexp _ _ _ _ _ _ _ HL Hσl) |].
    exact (sub_eq_preserves_modexp _ _ _ _ _ (wf_modexp_eq_refl_right HL) _ _ _ Hσ). }
  apply paths_conv_of_core; [ exact HLL |].
  cbn [modexp_sub]; rewrite !gunit_sub_mk; cbn [moddef_sub].
  cbn [modexp_sub] in HLL; rewrite !gunit_sub_mk in HLL; cbn [moddef_sub] in HLL.
  pose proof (sb_qn_eq_ext _ _ _ _ _ Ha (presup_modexp_eq_ctx HE) Hσ) as Hq.
  pose proof (sb_qn_eq_ext _ _ _ _ _ Ha' (presup_modexp_eq_ctx HE') (wf_sub_eq_refl _ _ _ _ _ Hσr)) as Hq'.
  pose proof (ext_eq_length _ _ _ _ _ HD) as Hl.
  intros s Hs.
  refine (paths_core_abs _ _ Hg s true Ψ (tele_sub Δ σ) (tele_sub Δ' σ') _ _ E[sb_qn (length Δ) σ]ᵐ E'[sb_qn (length Δ') σ']ᵐ _ Hs).
  constructor.
  - exact (all_assumptions_sub _ _ Ha).
  - exact (all_assumptions_sub _ _ Ha').
  - apply (ext_eq_trans_ass _ _ (tele_sub Δ σ') _ (all_assumptions_sub _ _ Ha) (all_assumptions_sub _ _ Ha)
             (tele_sub_eq_ext _ _ _ _ _ Ha (presup_modexp_eq_ctx HE) Hσ) (sub_preserves_ext _ _ _ _ _ _ _ HD Hσr)).
  - left; reflexivity.
  - left; reflexivity.
  - exact (wf_modexp_eq_refl_left HLL).
  - exact (sub_preserves_modexp _ _ _ _ _ _ _ (wf_modexp_eq_refl_left HE) (wf_sub_eq_left _ _ _ _ _ _ Hq)).
  - exact (sub_preserves_modexp _ _ _ _ _ _ _ HE' (wf_sub_eq_left _ _ _ _ _ _ Hq')).
  - exact (lit_alias_up_sim _ _ Hg _ _ _ _ (sub_preserves_modexp _ _ _ _ _ _ _ HE (wf_sub_eq_left _ _ _ _ _ _ Hq))).
  - exact (lit_alias_up_sim _ _ Hg _ _ _ _ (sub_preserves_modexp _ _ _ _ _ _ _ HE' (wf_sub_eq_left _ _ _ _ _ _ Hq'))).
  - intros [=].
  - intros [=].
  - rewrite <- Hl; exact (modexp_conv_m_true _ _ _ _ _ (modexp_conv_sub _ _ _ _ _ _ _ _ HC Hq)).
  - exact (frame_free_sub _ _ Hg _ _ _ _ _ HE Hf (wf_sub_eq_left _ _ _ _ _ _ Hq)).
  - exact (frame_free_sub _ _ Hg _ _ _ _ _ HE' Hf' (wf_sub_eq_left _ _ _ _ _ _ Hq')).
  - rewrite <- Hl; exact (sub_preserves_modexp _ _ _ _ _ _ _ (wf_modexp_eq_refl_right HE) (wf_sub_eq_right _ _ _ _ _ _ Hq)).
  - rewrite <- Hl; intros RQ1 RQ1' q1 Tq Φq q1' Tq' Φq' HR1 HR1' E1 E1'.
    pose proof (modexp_conv_sub _ _ _ _ _ _ _ _ HC Hq) as HC1.
    pose proof (HC1 _ _ _ (wf_sub_eq_refl _ _ _ _ _ (wf_sub_id _ _ _ (wf_sub_dom _ _ _ _ _ (wf_sub_eq_left _ _ _ _ _ _ Hq)))) nil
                  (path_pairs_nil _ _ _ _)) as [H1 _]; cbn [path_left path_right] in H1; rewrite !modexp_sub_id in H1.
    destruct (H1 _ HR1) as (X2 & HX2 & Hl2); rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HX2 _ HR1') in Hl2.
    exact (unit_of_full true _ _ _ nil _ _ _ _ Hl2 E1 E1').
Qed.

(** An alias of a literal and the literal over both telescopes have one
    module part. *)
Lemma flatten_same_mod : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ Δ Δ' D R1 R2,
    mdenote Θ Ξ Γ (me_lit (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))) R1 -> mdenote Θ Ξ Γ (me_lit (gu_mk (Δ' ++ Δ) D)) R2 ->
    mdesc_mod R1 = mdesc_mod R2.
Proof.
  intros * Hg * H1 H2; apply mdenote_lit_inv in H1, H2.
  inversion H1 as [| ? ? ? E0 R R' HE HRm]; subst; apply mdenote_lit_inv in HE.
  destruct D as [sm Φ | E0].
  - inversion HE as [? ? ? ? ? Φx Rb Hb Hd |]; subst; inversion H2 as [? ? ? ? ? Φx2 Rb2 Hb2 Hd2 |]; subst.
    rewrite <- List.app_assoc in Hb2; rewrite (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ Hb2 _ Hb) in Hd2.
    destruct sm; cbn in Hd, Hd2; [| discriminate ]; injection Hd as <-; injection Hd2 as <-; cbn in HRm |- *; injection HRm as <-; reflexivity.
  - inversion HE as [| ? ? ? ? RE REm HmE HREm]; subst; inversion H2 as [| ? ? ? ? RE2 REm2 HmE2 HREm2]; subst.
    rewrite <- List.app_assoc in HmE2; rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HmE2 _ HmE) in HREm2.
    rewrite HREm in HREm2; injection HREm2 as <-.
    rewrite mdesc_mod_up, (mdesc_mod_idem _ _ HREm) in HRm; cbn in HRm; injection HRm as <-.
    rewrite mdesc_up_cat; reflexivity.
Qed.

(** An alias of a literal and the literal over both telescopes
    ([wf_unit_eq_flatten]). *)
Lemma modexp_conv_flatten : forall Θ Ξ Γ Δ Δ' D, Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ≈ gu_mk (Δ' ++ Δ) D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ -> all_assumptions Δ -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵘ gu_mk Δ' D ≈ gu_mk Δ' D ->
    frame_free_target Θ Ξ (Δ ++ Γ) (me_lit (gu_mk Δ' D)) ->
    modexp_conv Θ Ξ (Δ ++ Γ) (me_lit (gu_mk Δ' D)) (me_lit (gu_mk Δ' D)) ->
    modexp_conv Θ Ξ Γ (me_lit (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))) (me_lit (gu_mk (Δ' ++ Δ) D)).
Proof.
  intros * Hfl HD Ha HU Hf HC.
  pose proof (ctx_wf_gctx _ _ _ (presup_unit_eq_ctx HU)) as Hg.
  pose proof (wf_me_lit _ _ _ _ _ HU) as HE.
  pose proof (modexp_conv_alias _ _ _ _ _ _ _ HD Ha Ha HE HE Hf Hf HC (wf_unit_eq_refl_left Hfl)) as HLL.
  pose proof (wf_me_lit _ _ _ _ _ Hfl) as Hm.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ Hm) as (_ & (R1 & _ & HR1 & _) & (R2 & _ & HR2 & _)).
  eapply modexp_conv_replace_mod_right;
    [ exact (wf_modexp_eq_refl_left Hm) | exact (wf_modexp_eq_refl_right Hm) | exact HR1 | exact HR2
    | exact (flatten_same_mod _ _ Hg _ _ _ _ _ _ HR1 HR2) | apply obs_sub_lit | apply obs_sub_lit | exact HLL ].
Qed.

(** *** Bodies *)

(** A body literal abstracts the literal of its body over no parameter. *)
Lemma lit_body_up_sim : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ D Φ, up_sim Θ Ξ Ψ D (me_lit (gu_open D Φ)) (me_lit (gu_open nil Φ)).
Proof.
  intros * Hg *; split.
  - intros X HX; pose proof (mdenote_lit_inv _ _ _ _ _ HX) as Hu; inversion Hu as [? ? ? ? ? Φx R Hb Hd |]; subst.
    cbn in Hd; injection Hd as <-.
    exists (mdesc_open nil Φ Φx); split; [ apply mdenote_lit; econstructor; [ exact Hb | reflexivity ] | reflexivity ].
  - intros RQ HRQ; pose proof (mdenote_lit_inv _ _ _ _ _ HRQ) as Hu; inversion Hu as [? ? ? ? ? Φx R Hb Hd |]; subst.
    cbn in Hd; injection Hd as <-; cbn [List.app] in Hb.
    exists (mdesc_open D Φ Φx); split; [ apply mdenote_lit; econstructor; [ exact Hb | reflexivity ] | reflexivity ].
Qed.

(** The body of a well-formed body unit is a well-formed unit under its
    parameters ([desc_ok_open]). *)
Lemma body_nil_typed : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ Δ Φ U0, Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ U0 ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ me_lit (gu_open nil Φ) ≈ me_lit (gu_open nil Φ).
Proof.
  intros * Hg * HU; pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_left HU)) as HL.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HL) as (_ & (R & _ & HR & _) & _).
  pose proof (desc_ok_of_typed _ _ Hg _ _ _ _ HL HR) as Hok.
  pose proof (mdenote_lit_inv _ _ _ _ _ HR) as Hu; inversion Hu as [? ? ? ? ? Φx R0 Hb Hd |]; subst.
  cbn in Hd; injection Hd as <-.
  inversion Hok; subst; apply wf_me_lit; assumption.
Qed.

(** A body literal denotes an open module. *)
Lemma lit_body_open : forall Θ Ξ Γ Δ Φ R, mdenote Θ Ξ Γ (me_lit (gu_open Δ Φ)) R -> exists Φx, R = mdesc_open Δ Φ Φx.
Proof. intros * H; pose proof (mdenote_lit_inv _ _ _ _ _ H) as Hu; inversion Hu as [? ? ? ? ? Φx R0 Hb Hd |]; subst; cbn in Hd; injection Hd as <-; eauto. Qed.

(** Two equal body units are compared along paths, given their bodies
    compared under the parameters. *)
Lemma modexp_conv_body_of_nil : forall Θ Ξ Γ Δ Δ' Φ Φ', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' -> all_assumptions Δ -> all_assumptions Δ' ->
    modexp_conv_m true Θ Ξ (Δ ++ Γ) (me_lit (gu_open nil Φ)) (me_lit (gu_open nil Φ')) ->
    modexp_conv Θ Ξ Γ (me_lit (gu_open Δ Φ)) (me_lit (gu_open Δ' Φ')).
Proof.
  intros * HU HD Ha Ha' HC Ψ σ σ' Hσ.
  pose proof (ctx_wf_gctx _ _ _ (presup_unit_eq_ctx HU)) as Hg.
  pose proof (body_nil_typed _ _ Hg _ _ _ _ HU) as HE.
  pose proof (body_nil_typed _ _ Hg _ _ _ _ (wf_unit_eq_sym _ _ _ _ _ HU)) as HE'.
  pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HE' (ctxsub_ext_rev _ _ _ _ _ HD Ha)) as HE'l; rewrite !modexp_sub_id in HE'l.
  pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hσl; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hσ) as Hσr.
  pose proof (wf_me_lit _ _ _ _ _ HU) as HL.
  assert (HLL : Θ ⍮ Ξ ⍮ Ψ ⊢ᵐ (me_lit (gu_open Δ Φ))[σ]ᵐ ≈ (me_lit (gu_open Δ' Φ'))[σ']ᵐ).
  { eapply wf_me_trans; [ exact (sub_preserves_modexp _ _ _ _ _ _ _ HL Hσl) |].
    exact (sub_eq_preserves_modexp _ _ _ _ _ (wf_modexp_eq_refl_right HL) _ _ _ Hσ). }
  apply paths_conv_of_core; [ exact HLL |].
  pose proof (sb_qn_eq_ext _ _ _ _ _ Ha (presup_modexp_eq_ctx HE) Hσ) as Hq.
  pose proof (sb_qn_eq_ext _ _ _ _ _ Ha' (presup_modexp_eq_ctx HE') (wf_sub_eq_refl _ _ _ _ _ Hσr)) as Hq'.
  pose proof (ext_eq_length _ _ _ _ _ HD) as Hl.
  cbn [modexp_sub] in HLL |- *; rewrite !gunit_sub_mk in HLL |- *; cbn [moddef_sub] in HLL |- *.
  intros s Hs.
  refine (paths_core_abs _ _ Hg s true Ψ (tele_sub Δ σ) (tele_sub Δ' σ') _ _
            (me_lit (gu_open nil Φ))[sb_qn (length Δ) σ]ᵐ (me_lit (gu_open nil Φ'))[sb_qn (length Δ') σ']ᵐ _ Hs).
  constructor.
  - exact (all_assumptions_sub _ _ Ha).
  - exact (all_assumptions_sub _ _ Ha').
  - apply (ext_eq_trans_ass _ _ (tele_sub Δ σ') _ (all_assumptions_sub _ _ Ha) (all_assumptions_sub _ _ Ha)
             (tele_sub_eq_ext _ _ _ _ _ Ha (presup_modexp_eq_ctx HE) Hσ) (sub_preserves_ext _ _ _ _ _ _ _ HD Hσr)).
  - left; reflexivity.
  - left; reflexivity.
  - exact (wf_modexp_eq_refl_left HLL).
  - exact (sub_preserves_modexp _ _ _ _ _ _ _ HE (wf_sub_eq_left _ _ _ _ _ _ Hq)).
  - exact (sub_preserves_modexp _ _ _ _ _ _ _ HE' (wf_sub_eq_left _ _ _ _ _ _ Hq')).
  - cbn [modexp_sub]; rewrite gunit_sub_mk; cbn [moddef_sub tele_sub]; apply lit_body_up_sim; exact Hg.
  - cbn [modexp_sub]; rewrite gunit_sub_mk; cbn [moddef_sub tele_sub]; apply lit_body_up_sim; exact Hg.
  - intros [=].
  - intros [=].
  - rewrite <- Hl; exact (modexp_conv_m_sub _ _ _ _ _ _ _ _ _ HC Hq).
  - intros R HR; cbn [modexp_sub] in HR; rewrite gunit_sub_mk in HR; destruct (lit_body_open _ _ _ _ _ _ HR) as [Φx ->].
    intros (? & ? & ? & ? & ? & [=] & _).
  - intros R HR; cbn [modexp_sub] in HR; rewrite gunit_sub_mk in HR; destruct (lit_body_open _ _ _ _ _ _ HR) as [Φx ->].
    intros (? & ? & ? & ? & ? & [=] & _).
  - rewrite <- Hl; exact (sub_preserves_modexp _ _ _ _ _ _ _ HE'l (wf_sub_eq_right _ _ _ _ _ _ Hq)).
  - intros RQ1 RQ1' q1 Tq Φq q1' Tq' Φq' HR1 HR1' E1 E1'; cbn [modexp_sub] in HR1; rewrite gunit_sub_mk in HR1.
    destruct (lit_body_open _ _ _ _ _ _ HR1) as [Φx ->]; discriminate.
Qed.

(** The entries a selection from a body reads: transparent definitions,
    modules and definitions with a module part. *)
Definition entry_readable (E : gentry) : Prop :=
  match E with
  | ge_def true _ _ _ (Some _) | ge_mod _ _ | ge_def_mod _ _ _ _ => True
  | _ => False
  end.

(** The entries an open description reads: readable entries of its
    expansion, in the context of the members before them over its
    parameters. *)
Lemma open_entry_iff : forall Δ Φw Φx y Γy E rd, mdesc_entry (mdesc_open Δ Φw Φx) y = Some (Γy, E, rd) <->
    exists Φ0, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) /\ entry_readable E /\ Γy = body_ctx Φ0 ++ Δ /\ rd = reader_open Δ Φ0.
Proof.
  intros; cbn [mdesc_entry]; split.
  - destruct (gm_prefix_upto Φx y) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
    pose proof (Kinds.Evaluation.gm_prefix_name _ _ _ _ _ Hp) as ->.
    destruct E0 as [[|] ? ? ? [] | | | |]; try discriminate; intros [= <- <- <-]; exists Φ'; cbn; auto.
  - intros (Φ0 & -> & HE & -> & ->); destruct E as [[|] ? ? ? [] | | | |]; cbn in HE; try contradiction; reflexivity.
Qed.

(** The entry of an open description with no parameters at [y]: a readable
    entry of the body, read in the context of the members before it. *)
Lemma body_entry_open : forall Φ Φx y Γy E rd, mdesc_entry (mdesc_open nil Φ Φx) y = Some (Γy, E, rd) <->
    exists Φ0, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) /\ entry_readable E /\ Γy = body_ctx Φ0 /\ rd = reader_open nil Φ0.
Proof. intros; rewrite open_entry_iff; setoid_rewrite List.app_nil_r; reflexivity. Qed.

(** A selection from a body literal denotes the entry it selects, read in the
    context of the members before it and filled with their values. *)
Lemma body_sel_iff : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall G Φ Φx y X, body_xp Θ Ξ G Φ Φx ->
    mdenote Θ Ξ G (me_mem (me_lit (gu_open nil Φ)) y) X <->
    exists Φ0 E τ R1, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) /\ entry_readable E /\ gm_fill Φ0 = Some τ /\
      edenote Θ Ξ (body_ctx Φ0 ++ G) None E R1 /\ X = mdesc_sub R1 τ.
Proof.
  intros * Hg * Hb.
  assert (HL : mdenote Θ Ξ G (me_lit (gu_open nil Φ)) (mdesc_open nil Φ Φx)) by (apply mdenote_lit; econstructor; [ exact Hb | reflexivity ]).
  split.
  - intros Hm; destruct (mdenote_mem_obs_inv _ _ Hg _ (me_lit (gu_open nil Φ)) _ _ (or_introl eq_refl) Hm) as (R0 & R0m & Γy & E & rd & R1 & HR0 & Hmd & He & Hed & Hr).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR0 _ HL) in Hmd; cbn in Hmd; injection Hmd as <-.
    destruct (proj1 (body_entry_open _ _ _ _ _ _) He) as (Φ0 & Hp & HE & -> & ->).
    cbn in Hr; destruct (gm_fill Φ0) as [τ |] eqn:Hf; cbn in Hr; [ injection Hr as <- | discriminate ].
    exists Φ0, E, τ, R1; split; [ exact Hp | split; [ exact HE | split; [ exact Hf | split; [ exact Hed | apply mdesc_up_nil ] ] ] ].
  - intros (Φ0 & E & τ & R1 & Hp & HE & Hf & Hed & ->).
    eapply mdenote_mem; [ exact HL | reflexivity | apply (proj2 (body_entry_open _ _ _ _ _ _)); exists Φ0; repeat split; eassumption
                       | exact Hed | cbn; rewrite Hf; cbn; rewrite mdesc_up_nil; reflexivity ].
Qed.

(** Two open modules of no parameter show the same, up to units, when
    they have members of types of levels together. *)
Lemma leaf_core_open_nil : forall Θ Ξ Ψ Φ1 Φx1 Φ2 Φx2,
    (Θ ⍮ Ξ ⍮ Ψ ⊢ⁿˡ mdesc_open nil Φ1 Φx1 <-> Θ ⍮ Ξ ⍮ Ψ ⊢ⁿˡ mdesc_open nil Φ2 Φx2) ->
    leaf_core Θ Ξ Ψ (mdesc_open nil Φ1 Φx1) (mdesc_open nil Φ2 Φx2).
Proof.
  intros * Hn; constructor; cbn; try reflexivity; try exact I; try (intros; discriminate); [| exact Hn ].
  unfold desc_reads_frame; split; intros (? & ? & ? & ? & ? & [=] & _).
Qed.

(** Entries of the same shape are of the same kind. *)
Lemma entry_shape_kind : forall E E', entry_shape E E' -> entry_kind E = entry_kind E'.
Proof. intros [? ? ? ? [] | | | | ] [? ? ? ? [] | | | | ] HS; cbn in *; try contradiction; try reflexivity; tauto. Qed.

(** The unit of a module entry of a well-formed body is well formed where
    the entry is. *)
Lemma body_entry_unit_wf : forall Θ Ξ G Φx y Φ0 E U, gm_noopen Φx -> ⊢ Θ ⍮ Ξ ⍮ body_ctx Φx ++ G ->
    gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
    ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ0 ++ G /\ Θ ⍮ Ξ ⍮ body_ctx Φ0 ++ G ⊢ᵘ U ≈ U.
Proof.
  intros * Hn HΦ Hp HU.
  destruct (gm_prefix_body_ctx _ _ _ Hn Hp) as (Ψ & HΨ); rewrite HΨ in HΦ.
  pose proof (ctx_app_wf_tail _ _ _ _ ltac:(rewrite <- List.app_assoc in HΦ; exact HΦ)) as HΦ0.
  exact (body_ext_unit_wf _ _ _ _ _ _ _ HΦ0 HU).
Qed.

(** A body unit with no parameter of the same shape as one with no member
    of a type of levels, its module entries compared along paths with the
    other's, filled in, has none: the entries' tags are the shape's, and
    each module entry has none, read back along its filling
    ([no_level_reflect]) from the other's, filled in, along the
    comparison's [leaf_nl]. *)
Lemma body_nl_transfer : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall G Φ Φx Φ' Φx',
    Θ ⍮ Ξ ⍮ G ⊢ᵐ me_lit (gu_open nil Φ) ≈ me_lit (gu_open nil Φ) ->
    mdenote Θ Ξ G (me_lit (gu_open nil Φ)) (mdesc_open nil Φ Φx) ->
    Θ ⍮ Ξ ⍮ G ⊢ᵐ me_lit (gu_open nil Φ') ≈ me_lit (gu_open nil Φ') ->
    mdenote Θ Ξ G (me_lit (gu_open nil Φ')) (mdesc_open nil Φ' Φx') ->
    body_shape Φx Φx' ->
    (forall y Φ0 E U Φ0' E' U' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> modexp_conv Θ Ξ G (me_lit U[σ]ᵘ) (me_lit U'[σ']ᵘ)) ->
    Θ ⍮ Ξ ⍮ G ⊢ⁿˡ mdesc_open nil Φ Φx -> Θ ⍮ Ξ ⍮ G ⊢ⁿˡ mdesc_open nil Φ' Φx'.
Proof.
  intros Θ Ξ Hg * HL HO HL' HO' Hsh HUc Hnl.
  pose proof (presup_modexp_eq_ctx HL) as HG.
  pose proof (desc_ok_of_typed _ _ Hg _ _ _ _ HL HO) as Hok.
  pose proof (desc_ok_of_typed _ _ Hg _ _ _ _ HL' HO') as Hok'.
  inversion Hok; subst.
  match goal with H1 : ⊢ _ ⍮ _ ⍮ body_ctx Φx ++ _, H2 : gm_noopen Φx |- _ => rename H1 into HΦ; rename H2 into Hn end.
  inversion Hok'; subst.
  match goal with H1 : ⊢ _ ⍮ _ ⍮ body_ctx Φx' ++ _, H2 : gm_noopen Φx',
                  H3 : forall y Φ0 E U, gm_prefix_upto Φx' y = _ -> _ -> forall R, udenote _ _ _ _ _ R -> desc_ok _ _ _ R |- _ =>
    rename H1 into HΦ'; rename H2 into Hn'; rename H3 into Hent' end.
  cbn [List.app] in HΦ, HΦ', Hent'.
  inversion Hnl as [| ? ? ? ? ? md ? ? ? Hk Hu Hl | |]; subst; cbn [List.app] in Hu, Hl.
  pose proof (gm_noopen_nopens _ Hn) as Hnx.
  destruct (prefix_choice Φx' (fun y Φy R => forall Φ0 E U, Φy = gm_ext Φ0 y E -> entry_unit E = Some U ->
                                 udenote Θ Ξ (body_ctx Φ0 ++ G) None U R)) as [md' Hmd'].
  { intros y Φy Hp; destruct (gm_prefix_entry _ _ _ Hp) as (Φ0 & E & -> & _).
    destruct (entry_unit E) as [U |] eqn:HE; [| exists (mdesc_open nil gm_nil gm_nil); intros * [= <- <-]; congruence ].
    destruct (body_entry_unit_wf _ _ _ _ _ _ _ _ Hn' HΦ' Hp HE) as [_ HU].
    destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & [R HR] & _).
    exists R; intros * [= <- <-] HE'; rewrite HE in HE'; injection HE' as <-; exact HR. }
  apply wf_no_level_open with (member_descs := md'); [ exact Hn' | | | |].
  - apply ext_of_ctx'; rewrite List.app_nil_r; exact HΦ'.
  - (* the tags are the shape's *)
    intros y Φ0' E' A' M' Hp' HE'.
    destruct (shape_prefix _ _ _ _ _ (body_shape_sym _ _ Hsh) Hp') as (Φ0 & E & Hp & _ & HS).
    destruct (entry_shape_tm _ _ _ _ HS HE') as (A & M & HE).
    rewrite (entry_shape_kind _ _ HS); exact (Hk _ _ _ _ _ Hp HE).
  - intros * Hp HE; cbn [List.app]; exact (Hmd' _ _ Hp _ _ _ eq_refl HE).
  - (* each module entry, by the other side's, filled in *)
    intros y Φ0' E' U' Hp' HE'; cbn [List.app].
    destruct (shape_prefix _ _ _ _ _ (body_shape_sym _ _ Hsh) Hp') as (Φ0 & E & Hp & Hsh0 & HS).
    destruct (entry_shape_unit _ _ _ HS HE') as (U & HE).
    destruct (body_shape_fill _ _ Hnx Hsh) as [Hf Hf'].
    destruct (fill_prefix _ _ _ _ Hf Hp) as (σ & Hσf).
    destruct (fill_prefix _ _ _ _ Hf' Hp') as (σ' & Hσf').
    pose proof (HUc _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hσf Hσf') as Hc.
    destruct (body_entry_unit_wf _ _ _ _ _ _ _ _ Hn HΦ Hp HE) as [HΦ0 HU].
    destruct (body_entry_unit_wf _ _ _ _ _ _ _ _ Hn' HΦ' Hp' HE') as [HΦ0' HU'].
    pose proof (wf_gm_fill _ _ _ _ _ HΦ0 Hσf) as Hσ.
    pose proof (wf_gm_fill _ _ _ _ _ HΦ0' Hσf') as Hσ'.
    pose proof (Hu _ _ _ _ Hp HE) as Hmd; pose proof (Hmd' _ _ Hp' _ _ _ eq_refl HE') as Hmd'y.
    pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ (wf_me_lit _ _ _ _ _ HU) (mdenote_lit _ _ _ _ _ Hmd) Hσ) as Hm1.
    pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ (wf_me_lit _ _ _ _ _ HU') (mdenote_lit _ _ _ _ _ Hmd'y) Hσ') as Hm2.
    cbn [modexp_sub] in Hm1, Hm2.
    pose proof (Hc _ _ _ (wf_sub_eq_refl _ _ _ _ _ (wf_sub_id _ _ _ HG))) as Hp0; rewrite !modexp_sub_id in Hp0.
    destruct (proj1 (Hp0 nil (path_pairs_nil _ _ _ _)) _ Hm1) as (X' & HX' & Hlf).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HX' _ Hm2) in Hlf.
    unfold path_leaf in Hlf; cbn in Hlf.
    rewrite !mdesc_is_mod_mod in Hlf
      by (apply mdesc_is_mod_sub; eapply udenote_is_mod; eassumption).
    pose proof (proj1 (leaf_nl _ _ _ _ _ Hlf) (sub_preserves_no_level _ _ _ _ _ _ (Hl _ _ _ _ Hp HE) Hσ)) as Hn2.
    exact (no_level_reflect _ _ Hg _ _ (Hent' _ _ _ _ Hp' HE' _ Hmd'y) _ _ Hσ' Hn2).
Qed.

(** Paths from two expressions denoting terms, compared wholly: no step
    leaves a term, so only the empty path reaches anything. *)
Lemma paths_full_terms : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ Pl Pr, obs_root Ξ Pl -> obs_root Ξ Pr ->
    (forall X, mdenote Θ Ξ Ψ Pl X -> mdesc_mod X = None) -> (forall X', mdenote Θ Ξ Ψ Pr X' -> mdesc_mod X' = None) ->
    (forall X, mdenote Θ Ξ Ψ Pl X -> exists X', mdenote Θ Ξ Ψ Pr X' /\ leaf_conv Θ Ξ Ψ X X') ->
    (forall X', mdenote Θ Ξ Ψ Pr X' -> exists X, mdenote Θ Ξ Ψ Pl X /\ leaf_conv Θ Ξ Ψ X X') ->
    forall s, path_pairs Θ Ξ Ψ Pl s ->
    (forall X, mdenote Θ Ξ Ψ (path_left Pl s) X -> exists X', mdenote Θ Ξ Ψ (path_right Pr s) X' /\ leaf_conv Θ Ξ Ψ X X') /\
    (forall X', mdenote Θ Ξ Ψ (path_right Pr s) X' -> exists X, mdenote Θ Ξ Ψ (path_left Pl s) X /\ leaf_conv Θ Ξ Ψ X X').
Proof.
  intros * Hg * Hq Hq' Hn Hn' H1 H2 s Hs.
  destruct Hs as [? | ? y s1 Hs1 | ? R T B T1 N N' s1 Hm Ht Hv HN Hs1]; cbn [path_left path_right].
  - split; assumption.
  - split; intros X HX; exfalso.
    + destruct (path_left_back _ _ Hg _ _ _ _ HX) as (R & HR).
      destruct (mdenote_mem_obs_inv _ _ Hg _ _ _ _ Hq HR) as (R0 & ? & ? & ? & ? & ? & HR0 & Hmd & _); rewrite (Hn _ HR0) in Hmd; discriminate.
    + destruct (path_right_back _ _ Hg _ _ _ _ HX) as (R & HR).
      destruct (mdenote_mem_obs_inv _ _ Hg _ _ _ _ Hq' HR) as (R0 & ? & ? & ? & ? & ? & HR0 & Hmd & _); rewrite (Hn' _ HR0) in Hmd; discriminate.
  - exfalso; unfold mdesc_mod_tele in Ht; rewrite (Hn _ Hm) in Ht; discriminate.
Qed.

(** Applications from an expression denoting modules denote modules. *)
Lemma path_apps_mod : forall Θ Ξ Ψ s, path_all_apps s = true -> forall P X, (forall R, mdenote Θ Ξ Ψ P R -> mdesc_is_mod R) ->
    (mdenote Θ Ξ Ψ (path_left P s) X -> mdesc_is_mod X) /\ (mdenote Θ Ξ Ψ (path_right P s) X -> mdesc_is_mod X).
Proof.
  induction s as [| [y | N N'] s IH]; intros Ha P X HP; cbn in Ha |- *; [ split; apply HP | discriminate |].
  split; intros HX.
  - refine (proj1 (IH Ha (me_app P N) X _) HX); intros R HR; destruct (mdenote_app_inv _ _ _ _ _ _ HR) as (R0 & HR0 & Hat).
    exact (mdesc_at_is_mod _ _ _ (HP _ HR0) Hat).
  - refine (proj2 (IH Ha (me_app P N') X _) HX); intros R HR; destruct (mdenote_app_inv _ _ _ _ _ _ HR) as (R0 & HR0 & Hat).
    exact (mdesc_at_is_mod _ _ _ (HP _ HR0) Hat).
Qed.

(** Paths compared, compared wholly: given the two roots compared wholly,
    and every application from either root a module. *)
Lemma paths_full_of_conv : forall Θ Ξ Ψ Pl Pr, paths_conv Θ Ξ Ψ Pl Pr ->
    (forall N R, mdenote Θ Ξ Ψ (me_app Pl N) R -> mdesc_is_mod R) -> (forall N R, mdenote Θ Ξ Ψ (me_app Pr N) R -> mdesc_is_mod R) ->
    (forall X X', mdenote Θ Ξ Ψ Pl X -> mdenote Θ Ξ Ψ Pr X' -> leaf_conv Θ Ξ Ψ X X') ->
    forall s, path_pairs Θ Ξ Ψ Pl s ->
    (forall X, mdenote Θ Ξ Ψ (path_left Pl s) X -> exists X', mdenote Θ Ξ Ψ (path_right Pr s) X' /\ leaf_conv Θ Ξ Ψ X X') /\
    (forall X', mdenote Θ Ξ Ψ (path_right Pr s) X' -> exists X, mdenote Θ Ξ Ψ (path_left Pl s) X /\ leaf_conv Θ Ξ Ψ X X').
Proof.
  intros * HC Ha Ha' Hl s Hs; destruct (HC _ Hs) as [H1 H2].
  assert (Hup : forall X X', mdenote Θ Ξ Ψ (path_left Pl s) X -> mdenote Θ Ξ Ψ (path_right Pr s) X' ->
            path_leaf Θ Ξ Ψ s X X' -> leaf_conv Θ Ξ Ψ X X').
  { intros X X' HX HX' Hle; destruct s as [| [y | N N'] s1].
    - exact (Hl _ _ HX HX').
    - exact Hle.
    - unfold path_leaf in Hle; cbn [path_all_apps] in Hle; destruct (path_all_apps s1) eqn:Ea; [| exact Hle ].
      cbn [path_left path_right] in HX, HX'.
      pose proof (proj1 (path_apps_mod _ _ _ s1 Ea (me_app Pl N) X (Ha N)) HX) as Hm.
      pose proof (proj2 (path_apps_mod _ _ _ s1 Ea (me_app Pr N') X' (Ha' N')) HX') as Hm'.
      rewrite (mdesc_is_mod_mod _ Hm), (mdesc_is_mod_mod _ Hm') in Hle; exact Hle. }
  split; [ intros X HX; destruct (H1 _ HX) as (X' & HX' & Hle) | intros X' HX'; destruct (H2 _ HX') as (X & HX & Hle) ];
    eauto.
Qed.

(** Two definitions with module parts have members of types of levels
    together when their module parts, on both sides or on neither, do. *)
Lemma no_level_dm_iff : forall Θ Ξ Ψ Θd A M Y Θd' A' M' Y', opt_rel (fun _ _ => True) (mdesc_mod Y) (mdesc_mod Y') ->
    (Θ ⍮ Ξ ⍮ Ψ ⊢ⁿˡ Y <-> Θ ⍮ Ξ ⍮ Ψ ⊢ⁿˡ Y') ->
    (Θ ⍮ Ξ ⍮ Ψ ⊢ⁿˡ mdesc_dm Θd A M Y <-> Θ ⍮ Ξ ⍮ Ψ ⊢ⁿˡ mdesc_dm Θd' A' M' Y').
Proof.
  intros * Hm Hn.
  destruct (mdesc_mod Y) as [Y0 |] eqn:E; destruct (mdesc_mod Y') as [Y0' |] eqn:E'; cbn in Hm; try contradiction.
  - rewrite (no_level_mod_iff _ _ _ _ _ E), (no_level_mod_iff _ _ _ _ _ E') in Hn.
    split; intros H; inversion H; subst; constructor; intros Rm' HRm'.
    + rewrite E' in HRm'; injection HRm' as <-; apply Hn; eauto.
    + rewrite E in HRm'; injection HRm' as <-; apply Hn; eauto.
  - split; intros _; constructor; intros Rm' HRm'; congruence.
Qed.

(** Two definitions with module parts of no parameter, compared wholly
    from their term parts and their module parts. *)
Lemma leaf_conv_dm_nil : forall Θ Ξ Ψ A M Y A' M' Y', leaf_conv Θ Ξ Ψ Y Y' ->
    (exists i, Θ ⍮ Ξ ⍮ Ψ ⊢ A ≈ A' : Typeω@i) -> Θ ⍮ Ξ ⍮ Ψ ⊢ M ≈ M' : A ->
    leaf_conv Θ Ξ Ψ (mdesc_dm nil A M Y) (mdesc_dm nil A' M' Y').
Proof.
  intros * [Hk Ht Hr Hu Hh Hf Hn] HA HM; constructor; cbn [mdesc_kind mdesc_type mdesc_reduct mdesc_mod ctx_pi ctx_fn].
  - reflexivity.
  - exact HA.
  - intros A0 [= <-]; exact HM.
  - exact Hu.
  - unfold mdesc_head, mdesc_mod_tele in *; cbn [mdesc_mod]; exact Hh.
  - unfold desc_reads_frame in *; cbn [mdesc_mod]; exact Hf.
  - apply no_level_dm_iff; [| exact Hn ].
    destruct (mdesc_mod Y), (mdesc_mod Y'); cbn in Hu |- *; tauto.
Qed.

(** Paths from two expressions [Pl] and [Pr] whose module parts are what
    [Ql] and [Qr] denote, compared wholly: from paths from [Ql] and [Qr]
    compared, every application from [Pl] or [Pr] a module, and the roots
    compared wholly once their module parts are. *)
Lemma paths_full_mod_part : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ Pl Pr Ql Qr Xl Xr Yl Yr,
    obs_root Ξ Pl -> obs_root Ξ Pr -> obs_root Ξ Ql -> obs_root Ξ Qr ->
    mdenote Θ Ξ Ψ Pl Xl -> mdenote Θ Ξ Ψ Pr Xr -> mdenote Θ Ξ Ψ Ql Yl -> mdenote Θ Ξ Ψ Qr Yr ->
    mdesc_is_mod Yl -> mdesc_is_mod Yr -> mdesc_mod Xl = Some Yl -> mdesc_mod Xr = Some Yr ->
    (forall N R, mdesc_at Xl N = Some R -> mdesc_is_mod R) -> (forall N R, mdesc_at Xr N = Some R -> mdesc_is_mod R) ->
    paths_conv Θ Ξ Ψ Ql Qr -> (leaf_conv Θ Ξ Ψ Yl Yr -> leaf_conv Θ Ξ Ψ Xl Xr) ->
    forall s, path_pairs Θ Ξ Ψ Pl s ->
    (forall X, mdenote Θ Ξ Ψ (path_left Pl s) X -> exists X', mdenote Θ Ξ Ψ (path_right Pr s) X' /\ leaf_conv Θ Ξ Ψ X X') /\
    (forall X', mdenote Θ Ξ Ψ (path_right Pr s) X' -> exists X, mdenote Θ Ξ Ψ (path_left Pl s) X /\ leaf_conv Θ Ξ Ψ X X').
Proof.
  intros * Hg * Hql Hqr HqQl HqQr HPl HPr HQl HQr HYl HYr HXl HXr Hal Har HC Hup.
  pose proof (proj1 (mdenote_functional_all _ _ Hg)) as Hf.
  assert (Hsim : forall P Q X Y, mdenote Θ Ξ Ψ P X -> mdenote Θ Ξ Ψ Q Y -> mdesc_is_mod Y -> mdesc_mod X = Some Y -> mod_sim Θ Ξ Ψ Q P).
  { intros * HP HQ HY HX; split.
    - intros Y0 HY0; rewrite (Hf _ _ _ HY0 _ HQ); exists X; split; [ exact HP | rewrite HX; exact (mdesc_is_mod_mod _ HY) ].
    - intros X0 HX0; rewrite (Hf _ _ _ HX0 _ HP); exists Y; split; [ exact HQ | rewrite HX; exact (mdesc_is_mod_mod _ HY) ]. }
  pose proof (paths_conv_mod_sim_left _ _ Hg _ _ _ _ HqQl Hql (Hsim _ _ _ _ HPl HQl HYl HXl) HC) as HC1.
  pose proof (paths_conv_sym _ _ _ _ _ (paths_conv_mod_sim_left _ _ Hg _ _ _ _ HqQr Hqr (Hsim _ _ _ _ HPr HQr HYr HXr)
                                          (paths_conv_sym _ _ _ _ _ HC1))) as HC2.
  apply paths_full_of_conv; [ exact HC2 | | |].
  - intros N R HR; destruct (mdenote_app_inv _ _ _ _ _ _ HR) as (R0 & HR0 & Hat); rewrite (Hf _ _ _ HR0 _ HPl) in Hat; exact (Hal _ _ Hat).
  - intros N R HR; destruct (mdenote_app_inv _ _ _ _ _ _ HR) as (R0 & HR0 & Hat); rewrite (Hf _ _ _ HR0 _ HPr) in Hat; exact (Har _ _ Hat).
  - intros X X' HX HX'; rewrite (Hf _ _ _ HX _ HPl), (Hf _ _ _ HX' _ HPr); apply Hup.
    destruct (proj1 (HC nil (path_pairs_nil _ _ _ _)) _ HQl) as (Y' & HY' & Hle); cbn [path_right] in HY'.
    rewrite (Hf _ _ _ HY' _ HQr) in Hle; unfold path_leaf in Hle; cbn [path_all_apps] in Hle.
    rewrite (mdesc_is_mod_mod _ HYl), (mdesc_is_mod_mod _ HYr) in Hle; exact Hle.
Qed.

(** A readable entry of a well-formed body denotes, in the context of the
    members before it. *)
Lemma entry_denotes_exists : forall Θ Ξ G Φx y Φ0 E, ⊢ Θ ⍮ Ξ ⍮ body_ctx Φx ++ G ->
    gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_readable E -> exists R1, edenote Θ Ξ (body_ctx Φ0 ++ G) None E R1.
Proof.
  intros * HC Hp HE.
  pose proof (body_prefix_wf _ _ G nil _ _ _ HC Hp) as HCy; cbn [List.app] in HCy.
  destruct E as [[|] pv r A [M |] | pv U | | pv A M U | ]; cbn in HE; try contradiction.
  - eexists; constructor.
  - destruct (body_ext_unit_wf _ _ _ _ _ _ _ HCy eq_refl) as [_ HU].
    destruct (proj1 (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU))) as (R & Hu).
    exists R; constructor; exact Hu.
  - destruct (body_ext_unit_wf _ _ _ _ _ _ _ HCy eq_refl) as [_ HU].
    cbn [body_ctx List.app] in HCy; destruct (ctx_decomp_dm_alias HCy) as [E1 ->].
    destruct (proj1 (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU))) as (R & Hu).
    eexists; constructor; exact Hu.
Qed.

(** A readable entry of a well-formed body, filled in, is what its
    selection from the body denotes. *)
Lemma body_sel_of_entry : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall G Φ Φx y Φ0 E τ, body_xp Θ Ξ G Φ Φx -> ⊢ Θ ⍮ Ξ ⍮ body_ctx Φx ++ G ->
    gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_readable E -> gm_fill Φ0 = Some τ ->
    exists R1, edenote Θ Ξ (body_ctx Φ0 ++ G) None E R1 /\ mdenote Θ Ξ G (me_mem (me_lit (gu_open nil Φ)) y) (mdesc_sub R1 τ).
Proof.
  intros * Hg * Hb HC Hp HE Hf.
  destruct (entry_denotes_exists _ _ _ _ _ _ _ HC Hp HE) as [R1 HR1]; exists R1; split; [ exact HR1 |].
  apply (proj2 (body_sel_iff _ _ Hg _ _ _ _ _ Hb)); exists Φ0, E, τ, R1; repeat split; assumption.
Qed.

(** Entries of one shape are both readable. *)
Lemma entry_shape_readable : forall E E', entry_shape E E' -> entry_readable E /\ entry_readable E'.
Proof. intros [[|] ? ? ? [] | | | | ] [[|] ? ? ? [] | | | | ]; cbn; intuition discriminate. Qed.

(** The module part of an entry of a well-formed body, filled in, denotes
    what it denotes before, filled in. *)
Lemma entry_unit_denote : forall Θ Ξ G Φ0 y E U τ R1, ⊢ Θ ⍮ Ξ ⍮ body_ctx (gm_ext Φ0 y E) ++ G -> entry_unit E = Some U ->
    gm_fill Φ0 = Some τ -> udenote Θ Ξ (body_ctx Φ0 ++ G) None U R1 -> mdenote Θ Ξ G (me_lit U[τ]ᵘ) (mdesc_sub R1 τ).
Proof.
  intros * HC HE Hf Hu; destruct (body_ext_unit_wf _ _ _ _ _ _ _ HC HE) as [HC0 HU].
  exact (wf_sub_mdenote _ _ _ _ _ _ _ _ (wf_me_lit _ _ _ _ _ HU) (mdenote_lit _ _ _ _ _ Hu) (wf_gm_fill _ _ _ _ _ HC0 Hf)).
Qed.

(** Two equal terms under two equal substitutions. *)
Lemma exp_eq_sub_both : forall Θ Ξ G Ψ M M' A σ σ', Θ ⍮ Ξ ⍮ G ⊢ M ≈ M' : A -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ ≈ σ' : G ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ M[σ] ≈ M'[σ'] : A[σ].
Proof.
  intros * HM Hσ; eapply wf_exp_eq_trans; [ exact (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HM (wf_sub_eq_left _ _ _ _ _ _ Hσ)) |].
  exact (sub_eq_preserves_exp _ _ _ _ _ (presup_exp_eq_right HM) _ _ _ Hσ).
Qed.

(** A body literal, moved, selects nothing its body has no entry for. *)
Lemma body_sel_none : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ Φ Φx σ y R,
    mdenote Θ Ξ Ψ (me_lit (gu_open nil Φ))[σ]ᵐ (mdesc_sub (mdesc_open nil Φ Φx) σ) ->
    (forall Φ0 E, gm_prefix_upto Φx y <> Some (gm_ext Φ0 y E)) ->
    ~ mdenote Θ Ξ Ψ (me_mem (me_lit (gu_open nil Φ))[σ]ᵐ y) R.
Proof.
  intros * Hg * HL Hn Hm.
  destruct (mdenote_mem_obs_inv _ _ Hg _ ((me_lit (gu_open nil Φ))[σ]ᵐ) _ _ (or_introl eq_refl) Hm) as (R0 & R0m & Γy & E & rd & R1 & HR0 & Hmd & He & _).
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR0 _ HL) in Hmd; cbn in Hmd; injection Hmd as <-.
  destruct (proj1 (body_entry_open _ _ _ _ _ _) He) as (Φ0 & Hp & _).
  destruct (gm_prefix_sub_inv _ _ _ _ _ Hp) as (Φ1 & E1 & Hp1 & _); exact (Hn _ _ Hp1).
Qed.

(** Two equal body units with no parameter, read in the left context, are
    compared along paths up to their units at the root: from the premises
    of [wf_unit_eq_body] and the comparison of the module parts. *)
Lemma body_nil_conv : forall Θ Ξ Γ Δ Δ' Φ Φx Φ' Φx' (entry_sort : String.string -> exp),
    body_xp Θ Ξ (Δ ++ Γ) Φ Φx -> body_xp Θ Ξ (Δ' ++ Γ) Φ' Φx' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' -> all_assumptions Δ -> all_assumptions Δ' ->
    ⊢ Θ ⍮ Ξ ⍮ body_ctx Φx ++ Δ ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ body_ctx Φx' ++ Δ' ++ Γ -> body_shape Φx Φx' ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ me_lit (gu_open nil Φ) ≈ me_lit (gu_open nil Φ) ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ me_lit (gu_open nil Φ') ≈ me_lit (gu_open nil Φ') ->
    (forall y Φ0 E A M, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       sort_kind (entry_sort y) (entry_kind E)) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A[σ] ≈ A'[σ'] : entry_sort y) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M[σ] ≈ M'[σ'] : A[σ]) ->
    (forall y Φ0 E U Φ0' E' U' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵘ U[σ]ᵘ ≈ U'[σ']ᵘ) ->
    (forall y Φ0 E U Φ0' E' U' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> modexp_conv Θ Ξ (Δ ++ Γ) (me_lit U[σ]ᵘ) (me_lit U'[σ']ᵘ)) ->
    modexp_conv_m true Θ Ξ (Δ ++ Γ) (me_lit (gu_open nil Φ)) (me_lit (gu_open nil Φ')).
Proof.
  intros * Hb Hb0' HD Ha Ha' HC HC' Hsh HL HL' Hk HA HM HU HUc.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HL)) as Hg.
  pose proof (proj1 (mdenote_functional_all _ _ Hg)) as Hf.
  assert (HsG : slots_agree (Δ' ++ Γ) (Δ ++ Γ)) by exact (slots_agree_ass _ _ _ Ha' Ha (eq_sym (ext_eq_length _ _ _ _ _ HD))).
  destruct (mdenote_slots_agree Θ Ξ) as (HtrM & HtrU & HtrE & HtrB & _).
  pose proof (HtrB _ _ _ Hb0' _ HsG) as Hb'.
  assert (HO : mdenote Θ Ξ (Δ ++ Γ) (me_lit (gu_open nil Φ)) (mdesc_open nil Φ Φx)) by (apply mdenote_lit; econstructor; [ exact Hb | reflexivity ]).
  assert (HO' : mdenote Θ Ξ (Δ ++ Γ) (me_lit (gu_open nil Φ')) (mdesc_open nil Φ' Φx')) by (apply mdenote_lit; econstructor; [ exact Hb' | reflexivity ]).
  intros Ψ σ σ' Hσ s Hs.
  pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hσl; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hσ) as Hσr.
  pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ HL HO Hσl) as HOs.
  pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ HL' HO' Hσr) as HOs'.
  (** members of types of levels together: each side read back to the
      unit, compared there entry by entry ([body_nl_transfer]) *)
  assert (Hnl : Θ ⍮ Ξ ⍮ Ψ ⊢ⁿˡ mdesc_sub (mdesc_open nil Φ Φx) σ <-> Θ ⍮ Ξ ⍮ Ψ ⊢ⁿˡ mdesc_sub (mdesc_open nil Φ' Φx') σ').
  { split; intros Hn0.
    - pose proof (no_level_reflect _ _ Hg _ _ (desc_ok_of_typed _ _ Hg _ _ _ _ HL HO) _ _ Hσl Hn0) as X.
      exact (sub_preserves_no_level _ _ _ _ _ _ (body_nl_transfer _ _ Hg _ _ _ _ _ HL HO HL' HO' Hsh HUc X) Hσr).
    - pose proof (no_level_reflect _ _ Hg _ _ (desc_ok_of_typed _ _ Hg _ _ _ _ HL' HO') _ _ Hσr Hn0) as X.
      refine (sub_preserves_no_level _ _ _ _ _ _ (body_nl_transfer _ _ Hg _ _ _ _ _ HL' HO' HL HO (body_shape_sym _ _ Hsh) _ X) Hσl).
      intros * Hp' HE' Hp HE Hf' Hf0; apply modexp_conv_sym; exact (HUc _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hf0 Hf'). }
  cbn [mdesc_sub tele_sub length sb_qn] in Hnl.
  destruct s as [| [y | N N'] s1].
  - cbn [path_left path_right path_leaf_m]; split.
    + intros X HX; rewrite (Hf _ _ _ HX _ HOs); eexists; split; [ exact HOs' | cbn; apply leaf_core_open_nil; exact Hnl ].
    + intros X HX; rewrite (Hf _ _ _ HX _ HOs'); eexists; split; [ exact HOs | cbn; apply leaf_core_open_nil; exact Hnl ].
  - inversion Hs as [| ? ? ? Hs1 |]; subst; clear Hs.
    cbn [path_left path_right path_leaf_m path_full_m path_all_apps andb].
    assert (Hdec : (exists Φ0 E, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E)) \/ (forall Φ0 E, gm_prefix_upto Φx y <> Some (gm_ext Φ0 y E))).
    { destruct (gm_prefix_upto Φx y) as [[| Φ0 z E | ] |] eqn:Hp; try (right; intros ? ? Hc; discriminate).
      left; pose proof (Kinds.Evaluation.gm_prefix_name _ _ _ _ _ Hp); subst; eauto. }
    destruct Hdec as [(Φ0 & E & Hp) | Hn].
    2: { (* no entry: neither side selects anything *)
         split; intros X HX; exfalso.
         - destruct (path_left_back _ _ Hg _ _ _ _ HX) as (R & HR); exact (body_sel_none _ _ Hg _ _ _ _ _ _ HOs Hn HR).
         - destruct (path_right_back _ _ Hg _ _ _ _ HX) as (R & HR); refine (body_sel_none _ _ Hg _ _ _ _ _ _ HOs' _ HR).
           intros Φ0' E' Hp'; destruct (shape_prefix _ _ _ _ _ (body_shape_sym _ _ Hsh) Hp') as (Φ0 & E & Hp & _); exact (Hn _ _ Hp). }
    destruct (shape_prefix _ _ _ _ _ Hsh Hp) as (Φ0' & E' & Hp' & Hsh0 & HshE).
    pose proof (gm_noopen_nopens _ (body_xp_result_noopen _ _ _ _ _ Hb)) as Hnop.
    destruct (body_shape_fill _ _ Hnop Hsh) as [Hfx Hfx'].
    destruct (fill_prefix _ _ _ _ Hfx Hp) as [τ Hτ]; destruct (fill_prefix _ _ _ _ Hfx' Hp') as [τ' Hτ'].
    destruct (entry_shape_readable _ _ HshE) as [HrE HrE'].
    destruct (body_sel_of_entry _ _ Hg _ _ _ _ _ _ _ Hb HC Hp HrE Hτ) as (R1 & HR1 & HX0).
    destruct (body_sel_of_entry _ _ Hg _ _ _ _ _ _ _ Hb0' HC' Hp' HrE' Hτ') as (R1' & HR1' & HX0'').
    pose proof (HtrM _ _ _ HX0'' _ HsG) as HX0'.
    pose proof (wf_sub_mdenote_mem _ _ _ _ _ _ _ _ _ HL HX0 Hσl) as HPl.
    pose proof (wf_sub_mdenote_mem _ _ _ _ _ _ _ _ _ HL' HX0' Hσr) as HPr.
    pose proof (body_prefix_wf _ _ (Δ ++ Γ) nil _ _ _ HC Hp) as HCy; cbn [List.app] in HCy.
    pose proof (body_prefix_wf _ _ (Δ' ++ Γ) nil _ _ _ HC' Hp') as HCy'; cbn [List.app] in HCy'.
    assert (Hq : forall U0 τ0, obs_root Ξ (me_mem (me_lit U0)[τ0]ᵐ y)) by (intros; left; reflexivity).
    assert (Hq0 : forall U0 τ0, obs_root Ξ (me_lit U0)[τ0]ᵐ) by (intros; left; reflexivity).
    clear HX0'' HtrB HtrE.
    destruct E as [[|] pv r A [M |] | pv U | | pv A M U | ]; destruct E' as [[|] pv' r' A' [M' |] | pv' U' | | pv' A' M' U' | ];
      cbn in HshE; try contradiction.
    + (* definitions: the term parts, compared at the empty path only *)
      destruct HshE as (_ & _ & <- & <-).
      inversion HR1; subst; clear HR1; inversion HR1'; subst; clear HR1'; cbn in HPl, HPr.
      pose proof (HA y Φ0 _ A M Φ0' _ A' M' τ τ' Hp eq_refl Hp' eq_refl Hτ Hτ') as HAeq.
      pose proof (HM y Φ0 _ A M Φ0' _ A' M' τ τ' Hp eq_refl Hp' eq_refl Hτ Hτ') as HMeq.
      destruct (sort_kind_abs_kind_sort_inv _ _ (Hk y Φ0 _ A M Hp eq_refl)) as [i Hi]; rewrite Hi in HAeq.
      assert (Hlf : leaf_conv Θ Ξ Ψ (mdesc_term r A[τ][σ] (Some M[τ][σ])) (mdesc_term r A'[τ'][σ'] (Some M'[τ'][σ']))).
      { constructor; cbn.
        - reflexivity.
        - exists i; pose proof (exp_eq_sub_both _ _ _ _ _ _ _ _ _ HAeq Hσ) as H; rewrite abs_kind_sort_sub in H; exact H.
        - intros A0 [= <-]; exact (exp_eq_sub_both _ _ _ _ _ _ _ _ _ HMeq Hσ).
        - exact I.
        - exact I.
        - unfold desc_reads_frame; cbn; split; intros (? & ? & ? & ? & ? & [=] & _).
        - apply no_level_term_iff. }
      refine (paths_full_terms _ _ Hg _ _ _ (Hq _ _) (Hq _ _) _ _ _ _ _ Hs1).
      * intros X HX; rewrite (Hf _ _ _ HX _ HPl); reflexivity.
      * intros X HX; rewrite (Hf _ _ _ HX _ HPr); reflexivity.
      * intros X HX; rewrite (Hf _ _ _ HX _ HPl); eexists; split; [ exact HPr | exact Hlf ].
      * intros X HX; rewrite (Hf _ _ _ HX _ HPr); eexists; split; [ exact HPl | exact Hlf ].
    + (* modules: through their units, filled in *)
      inversion HR1 as [| ? ? ? ? ? Hu1 | | | ]; subst; clear HR1; inversion HR1' as [| ? ? ? ? ? Hu1' | | | ]; subst; clear HR1'.
      pose proof (entry_unit_denote _ _ _ _ _ _ _ _ _ HCy eq_refl Hτ Hu1) as HQl0.
      pose proof (HtrM _ _ _ (entry_unit_denote _ _ _ _ _ _ _ _ _ HCy' eq_refl Hτ' Hu1') _ HsG) as HQr0.
      pose proof (HU y Φ0 _ U Φ0' _ U' τ τ' Hp eq_refl Hp' eq_refl Hτ Hτ') as HUeq.
      pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_left HUeq)) HQl0 Hσl) as HQl.
      pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_right HUeq)) HQr0 Hσr) as HQr.
      pose proof (HUc y Φ0 _ U Φ0' _ U' τ τ' Hp eq_refl Hp' eq_refl Hτ Hτ' Ψ σ σ' Hσ) as HCc.
      pose proof (udenote_is_mod _ _ _ _ _ _ (mdenote_lit_inv _ _ _ _ _ HQl)) as Him.
      pose proof (udenote_is_mod _ _ _ _ _ _ (mdenote_lit_inv _ _ _ _ _ HQr)) as Him'.
      exact (paths_full_mod_part _ _ Hg _ _ _ _ _ _ _ _ _ (Hq _ _) (Hq _ _) (Hq0 _ _) (Hq0 _ _) HPl HPr HQl HQr Him Him'
               (mdesc_is_mod_mod _ Him) (mdesc_is_mod_mod _ Him') (fun N R Hat => mdesc_at_is_mod _ _ _ Him Hat)
               (fun N R Hat => mdesc_at_is_mod _ _ _ Him' Hat) HCc (fun H => H) _ Hs1).
    + (* definitions with module parts: the term parts and the units *)
      inversion HR1 as [| | | ? ? ? ? ? Δu Eu Rm Hu1 | ]; subst; clear HR1; inversion HR1' as [| | | ? ? ? ? ? Δu' Eu' Rm' Hu1' | ]; subst; clear HR1'.
      cbn [mdesc_sub tele_sub sb_qn List.length] in HPl, HPr.
      pose proof (entry_unit_denote _ _ _ _ _ _ _ _ _ HCy eq_refl Hτ Hu1) as HQl0.
      pose proof (HtrM _ _ _ (entry_unit_denote _ _ _ _ _ _ _ _ _ HCy' eq_refl Hτ' Hu1') _ HsG) as HQr0.
      pose proof (HU y Φ0 _ _ Φ0' _ _ τ τ' Hp eq_refl Hp' eq_refl Hτ Hτ') as HUeq.
      pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_left HUeq)) HQl0 Hσl) as HQl.
      pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_right HUeq)) HQr0 Hσr) as HQr.
      pose proof (HUc y Φ0 _ _ Φ0' _ _ τ τ' Hp eq_refl Hp' eq_refl Hτ Hτ' Ψ σ σ' Hσ) as HCc.
      pose proof (udenote_is_mod _ _ _ _ _ _ (mdenote_lit_inv _ _ _ _ _ HQl)) as Him.
      pose proof (udenote_is_mod _ _ _ _ _ _ (mdenote_lit_inv _ _ _ _ _ HQr)) as Him'.
      pose proof (HA y Φ0 _ A M Φ0' _ A' M' τ τ' Hp eq_refl Hp' eq_refl Hτ Hτ') as HAeq.
      pose proof (HM y Φ0 _ A M Φ0' _ A' M' τ τ' Hp eq_refl Hp' eq_refl Hτ Hτ') as HMeq.
      destruct (sort_kind_abs_kind_sort_inv _ _ (Hk y Φ0 _ A M Hp eq_refl)) as [i Hi]; cbn in Hi; rewrite Hi in HAeq.
      assert (Hat : forall A0 M0 Y N R, mdesc_is_mod Y -> mdesc_at (mdesc_dm nil A0 M0 Y) N = Some R -> mdesc_is_mod R).
      { intros * HY HR; cbn in HR; destruct (mdesc_at Y N) eqn:EY; [ injection HR as <-; exact (mdesc_at_is_mod _ _ _ HY EY) | discriminate ]. }
      exact (paths_full_mod_part _ _ Hg _ _ _ _ _ _ _ _ _ (Hq _ _) (Hq _ _) (Hq0 _ _) (Hq0 _ _) HPl HPr HQl HQr Him Him'
               (mdesc_is_mod_mod _ Him) (mdesc_is_mod_mod _ Him') (fun N R => Hat _ _ _ N R Him) (fun N R => Hat _ _ _ N R Him') HCc
               (fun H => leaf_conv_dm_nil _ _ _ _ _ _ _ _ _ H (ex_intro _ i (exp_eq_sub_both _ _ _ _ _ _ _ _ _ HAeq Hσ))
                           (exp_eq_sub_both _ _ _ _ _ _ _ _ _ HMeq Hσ)) _ Hs1).
  - exfalso; inversion Hs as [| | ? R T B T1 ? ? ? Hm Ht Hv _ _]; subst.
    rewrite (Hf _ _ _ Hm _ HOs) in Ht; cbn in Ht; injection Ht as <-; discriminate.
Qed.

(** Two equal body units, from the premises of [wf_unit_eq_body]. *)
Lemma modexp_conv_body : forall Θ Ξ Γ Δ Δ' Φ Φx Φ' Φx' (entry_sort : String.string -> exp),
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' ->
    body_xp Θ Ξ (Δ ++ Γ) Φ Φx -> body_xp Θ Ξ (Δ' ++ Γ) Φ' Φx' -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx ++ Δ ≈ body_ctx Φx ++ Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx' ++ Δ' ≈ body_ctx Φx' ++ Δ' ->
    all_assumptions Δ -> all_assumptions Δ' -> body_shape Φx Φx' ->
    (forall y Φ0 E A M, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       sort_kind (entry_sort y) (entry_kind E)) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A[σ] ≈ A'[σ'] : entry_sort y) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M[σ] ≈ M'[σ'] : A[σ]) ->
    (forall y Φ0 E U Φ0' E' U' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵘ U[σ]ᵘ ≈ U'[σ']ᵘ) ->
    (forall y Φ0 E U Φ0' E' U' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       slots_conv Θ Ξ (Δ ++ Γ) /\ modexp_conv Θ Ξ (Δ ++ Γ) (me_lit U[σ]ᵘ) (me_lit U'[σ']ᵘ)) ->
    modexp_conv Θ Ξ Γ (me_lit (gu_open Δ Φ)) (me_lit (gu_open Δ' Φ')).
Proof.
  intros * HUe Hb Hb' HD HX HX' Ha Ha' Hsh Hk HA HM HU HUc.
  pose proof (ctx_wf_gctx _ _ _ (presup_unit_eq_ctx HUe)) as Hg.
  pose proof (body_nil_typed _ _ Hg _ _ _ _ HUe) as HE.
  pose proof (body_nil_typed _ _ Hg _ _ _ _ (wf_unit_eq_sym _ _ _ _ _ HUe)) as HE'.
  pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HE' (ctxsub_ext_rev _ _ _ _ _ HD Ha)) as HE'l; rewrite !modexp_sub_id in HE'l.
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- List.app_assoc in HC.
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX') as HC'; rewrite <- List.app_assoc in HC'.
  apply (modexp_conv_body_of_nil _ _ _ _ _ _ _ HUe HD Ha Ha').
  exact (body_nil_conv _ _ _ _ _ _ _ _ _ entry_sort Hb Hb' HD Ha Ha' HC HC' Hsh HE HE'l Hk HA HM HU
           (fun y Φ0 E U Φ0' E' U' σ σ' H1 H2 H3 H4 H5 H6 => proj2 (HUc y Φ0 E U Φ0' E' U' σ σ' H1 H2 H3 H4 H5 H6))).
Qed.

(** ** Global Units

    A stored unit applied to equal arguments: the two sides of a path from
    it are one generic path, from the unit applied to assumptions, moved
    by two equal substitutions. *)

(** The outermost parameter of a scoped description, moved. *)
Lemma mdesc_head_sub : forall R σ n, mdesc_scoped n R -> mdesc_head (mdesc_sub R σ) = option_map (fun B => B[σ]) (mdesc_head R).
Proof.
  intros * HR; unfold mdesc_head.
  destruct (mdesc_mod_tele R) as [T |] eqn:Ht.
  - rewrite (mdesc_mod_tele_sub _ _ σ n HR Ht), tele_view_sub; destruct (tele_view T) as [[B T1] |]; reflexivity.
  - unfold mdesc_mod_tele in *; destruct (mdesc_mod (mdesc_sub R σ)) eqn:E; [| reflexivity ].
    destruct (mdesc_mod_sub_inv _ _ _ E) as (R' & HR' & ->); rewrite HR' in Ht.
    destruct R'; cbn in Ht |- *; try reflexivity; try discriminate.
    rewrite List.length_map; destruct (Nat.leb _ _); [ discriminate | reflexivity ].
Qed.

(** A typed description moved by two equal substitutions shows the same on
    both sides, up to units. *)
Lemma leaf_core_sub_pair : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γg D Ψ ρ ρ', desc_ok Θ Ξ Γg D -> mdesc_scoped (length Γg) D ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ˢ ρ ≈ ρ' : Γg -> leaf_core Θ Ξ Ψ (mdesc_sub D ρ) (mdesc_sub D ρ').
Proof.
  intros * Hg * Hok Hsc Hρ; pose proof (gctx_valid_syn _ _ Hg) as Hv.
  assert (Htn : forall σ, mdesc_type D = None -> mdesc_type (mdesc_sub D σ) = None) by (intros σ H; destruct D; cbn in *; congruence).
  assert (Hrn : forall σ, mdesc_reduct D = None -> mdesc_reduct (mdesc_sub D σ) = None).
  { intros σ H; destruct (mdesc_reduct (mdesc_sub D σ)) eqn:E; [| reflexivity ].
    destruct (mdesc_reduct_sub_inv _ _ _ E) as (M0 & HM0 & _); congruence. }
  assert (Hmn : forall σ, mdesc_mod D = None -> mdesc_mod (mdesc_sub D σ) = None).
  { intros σ H; destruct (mdesc_mod (mdesc_sub D σ)) eqn:E; [| reflexivity ].
    destruct (mdesc_mod_sub_inv _ _ _ E) as (M0 & HM0 & _); congruence. }
  constructor.
  - rewrite !mdesc_kind_sub; reflexivity.
  - pose proof (Htn ρ) as Ht1; pose proof (Htn ρ') as Ht2.
    destruct (mdesc_type D) as [A |] eqn:Et; [| rewrite (Ht1 eq_refl), (Ht2 eq_refl); exact I ].
    rewrite (mdesc_type_sub _ _ ρ Et), (mdesc_type_sub _ _ ρ' Et); cbn.
    destruct (desc_ok_ty_at _ _ _ _ _ Hok Et) as [i HA]; exists i; rewrite mdesc_kind_sub.
    pose proof (sub_eq_preserves_exp _ _ _ _ _ HA _ _ _ Hρ) as H; rewrite abs_kind_sort_sub in H; exact H.
  - intros A0 HA0.
    pose proof (Htn ρ) as Ht1; pose proof (Hrn ρ) as Hr1; pose proof (Hrn ρ') as Hr2.
    destruct (mdesc_type D) as [A |] eqn:Et; [| rewrite (Ht1 eq_refl) in HA0; discriminate ].
    rewrite (mdesc_type_sub _ _ ρ Et) in HA0; injection HA0 as <-.
    destruct (mdesc_reduct D) as [M |] eqn:Er; [| rewrite (Hr1 eq_refl), (Hr2 eq_refl); exact I ].
    rewrite (mdesc_reduct_sub _ _ ρ Er), (mdesc_reduct_sub _ _ ρ' Er); cbn.
    exact (sub_eq_preserves_exp _ _ _ _ _ (proj2 (desc_ok_ty_sorted _ _ Hv _ _ _ Hok Et) _ Er) _ _ _ Hρ).
  - pose proof (Hmn ρ) as Hm1; pose proof (Hmn ρ') as Hm2.
    destruct (mdesc_mod D) as [Dm |] eqn:Em; [| rewrite (Hm1 eq_refl), (Hm2 eq_refl); exact I ].
    rewrite (mdesc_mod_sub _ _ ρ Em), (mdesc_mod_sub _ _ ρ' Em); exact I.
  - rewrite (mdesc_head_sub _ ρ _ Hsc), (mdesc_head_sub _ ρ' _ Hsc).
    unfold mdesc_head in *; destruct (mdesc_mod_tele D) as [T |] eqn:Ht; cbn; [| exact I ].
    destruct (tele_view T) as [[B T1] |] eqn:Ev; cbn; [| exact I ].
    destruct (mod_of_tele _ _ Ht) as [Dm Em].
    rewrite <- (mdesc_mod_tele_mod_part _ _ Em) in Ht; unfold mdesc_mod_tele in Ht; rewrite (mdesc_mod_idem _ _ Em) in Ht.
    destruct (desc_ok_head _ _ _ _ _ _ _ (desc_ok_mod _ _ Hg _ _ _ Hok Em) Ht Ev) as (S & HS & HB).
    pose proof (sub_eq_preserves_exp _ _ _ _ _ HB _ _ _ Hρ) as HBe.
    pose proof (presup_exp_eq_left HBe) as HB1; pose proof (presup_exp_eq_right HBe) as HB2.
    assert (HSs : type_sort S[ρ]) by (inversion HS; subst; constructor).
    split; eapply wf_subtyp_refl; [ exact HB2 | exact HSs | exact HBe | exact HB1 | exact HSs | apply wf_exp_eq_sym; exact HBe ].
  - assert (Hfr : forall σ, desc_reads_frame Ξ D -> desc_reads_frame Ξ (mdesc_sub D σ)).
    { intros σ (Θ' & p & T & Φ & Ns & Hm & Hf); unfold desc_reads_frame; rewrite (mdesc_mod_sub _ _ σ Hm); cbn;
        do 5 eexists; split; [ reflexivity | exact Hf ]. }
    split; intros H; apply Hfr; eapply desc_reads_frame_sub; exact H.
  - (* each side read back to [D] ([no_level_reflect]), then moved to the other *)
    pose proof (wf_sub_eq_left _ _ _ _ _ _ Hρ) as Hρl; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hρ) as Hρr.
    split; intros H.
    + exact (sub_preserves_no_level _ _ _ _ _ _ (no_level_reflect _ _ Hg _ _ Hok _ _ Hρl H) Hρr).
    + exact (sub_preserves_no_level _ _ _ _ _ _ (no_level_reflect _ _ Hg _ _ Hok _ _ Hρr H) Hρl).
Qed.

(** An entry of a typed closed description, denoted, can be read with the
    arguments recorded ([desc_ok_entry_closed_read], which reads it). *)
Lemma closed_entry_read_exists : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> valid_syn Θ Ξ ->
    forall Γ Θ' p T Φ Ns y Γy E rd R,
    desc_ok Θ Ξ Γ (mdesc_closed Θ' p T Φ Ns) -> mdesc_entry (mdesc_closed Θ' p T Φ Ns) y = Some (Γy, E, rd) ->
    edenote Θ Ξ (Γy ++ Γ) (Some (qname_in p y)) E R -> exists R', mdesc_read rd R = Some R'.
Proof.
  intros Θ Ξ Hg Hv * HR He Hed.
  inversion HR as [| | Γ0 Θa T0 Φ1 Ns0 Θ0 Ξ0 p0 lΘ Hg0 Hsub Hloc Ha HsT HT HΘ' Hargs HaΘ' HRΘ' HLΘ' |]; subst.
  cbn in He; destruct (gm_prefix_upto Φ y) as [[| Φ0 x E0 | ? ? ?] |] eqn:Hp; try discriminate.
  injection He as <- <- <-.
  destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & Hent).
  cbn [mdesc_read]; enough (Hx : exists R0, mdesc_ats_read R Ns = Some R0) by (destruct Hx as [R0 ->]; eexists; reflexivity).
  (* the entry as it is stored now, grown, is valid *)
  assert (Hloc' : exists Φ', loc Θ Ξ p T Φ').
  { destruct Hloc as [Hf | Hb].
    - destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hsub Hf) as (Φ' & [[Hf' _] | [Hb' _]]); exists Φ'; [ left | right ]; assumption.
    - destruct (gc_sub_body _ _ _ _ _ _ _ Hsub Hb) as (Φ' & Hb' & _); exists Φ'; right; exact Hb'. }
  destruct Hloc' as (Φ' & Hloc').
  pose proof (proj2 (loc_entry _ _ Hg0 _ _ _ Hloc _ _) Hent) as HeΘ0.
  destruct (gc_sub_entry _ _ _ _ _ _ Hsub HeΘ0) as (E1 & HeΘ & Hgr).
  pose proof (proj1 (loc_entry _ _ Hg _ _ _ Hloc' _ _) HeΘ) as Hent1.
  destruct (gm_entry_prefix _ _ _ (body_closed_noopen _ _ (proj2 (loc_closed _ _ Hg _ _ _ Hloc'))) Hent1) as (Φ0' & Hp1).
  destruct (loc_valid _ _ _ _ _ Hv Hloc') as [_ HvΦ].
  pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ HvΦ Hp1) as HE0.
  pose proof (gm_coherent_prefix _ _ _ _ _ (loc_coherent _ _ Hg0 _ _ _ Hloc) Hp) as HcE0.
  pose proof (loc_closed _ _ Hg0 _ _ _ Hloc) as [_ HcΦ].
  pose proof (body_closed_prefix _ _ _ _ HcΦ Hp) as HcE; cbn in HcE; destruct HcE as [_ HcE].
  pose proof (closed_tele_wf _ _ _ _ HsT HT HΘ') as HTΘ.
  destruct E0 as [b pv r A oM | pv [Δ [sm Φy | E'] ] | pv pq k D ΦD | pv Adm Mdm Udm | pv pr Rr ΦR ].
  - (* a definition: abstracted over the telescope *)
    cbn in Hgr; subst E1.
    cbn in HE0; destruct HE0 as (A0 & -> & [iA HLsrt HA0] & HM0).
    inversion Hed; subst; cbn [mdesc_ats_read].
    assert (Hom : exists om0, (if b then oM else None) = option_map (ctx_fn T) om0 /\ forall M0, om0 = Some M0 -> Θ ⍮ Ξ ⍮ T ⊢ M0 : A0).
    { destruct b; [| exists None; split; [ reflexivity | discriminate ] ].
      destruct oM as [M |]; [| exists None; split; [ reflexivity | discriminate ] ].
      destruct (HM0 M eq_refl) as (M0 & -> & HM); exists (Some M0); split; [ reflexivity | intros ? [= <-]; exact HM ]. }
    destruct Hom as (om0 & Hom & Hom0).
    rewrite Hom; change (mdesc_term r (ctx_pi_at r T A0) (option_map (ctx_fn T) om0)) with (mdesc_up T (mdesc_term r A0 om0)).
    pose proof (closed_tele_weaken_exp _ _ _ _ _ _ HsT HA0 HTΘ) as HA0Θ.
    destruct (ats_up_ok _ _ Hg Ns (Θ' ++ Γ) T (mdesc_term r A0 om0) 0 HTΘ Ha (args_ok_length _ _ _ _ _ Hargs) (args_ok_insts _ _ _ _ _ Hargs))
      as (R1 & HR1 & _).
    { eapply desc_ok_term; [ exact HA0Θ | intros M1 HM; exact (closed_tele_weaken_exp _ _ _ _ _ _ HsT (Hom0 _ HM) HTΘ) ]. }
    { eapply closed_term_levels_abstractable; [ exact HsT | exact HTΘ | exact HLsrt | exact HA0 ]. }
    exists R1; exact HR1.
  - (* a closed submodule: its body, at the arguments recorded *)
    destruct HcE as (-> & HsΔ & HcΦy).
    destruct E1 as [| pv1 [Δ1 [sm1 Φy1 | ?]] | | | ]; cbn in Hgr; try discriminate; destruct Hgr as (<- & <- & <-).
    cbn [ge_read] in Hed; inversion Hed; subst.
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
    match goal with Hx : body_xp _ _ _ Φy ?Φx |- _ =>
      pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ Hx _ (body_xp_noopen Θ Ξ _ _ (body_closed_noopen _ _ HcΦy))) as <- end.
    match goal with Hb : mdesc_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
    cbn [mdesc_ats_read]; rewrite mdesc_ats_closed_nil; eexists; reflexivity.
  - (* an alias: the module part of what its target denotes, abstracted *)
    cbn in Hgr; subst E1.
    cbn [ge_read] in Hed; inversion Hed; subst.
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
    cbn [List.app] in *.
    cbn [syn_V] in HE0; destruct HE0 as [HEw [HΔ [[lΔ HRΔ] [(lv & Rt & Hlv) Hcl]]]].
    rewrite gunit_scoped_mk in HcE; destruct HcE as [HsΔ HsE]; cbn [moddef_scoped] in HsE; rewrite Nat.add_0_r in HsE.
    destruct HcE0 as (Δ0 & -> & HaΔ0).
    pose proof (ctx_app_wf_tail _ _ _ _ HΘ') as HΓ.
    pose proof (closed_tele_wf _ _ _ _ HsΔ HΔ HΓ) as HΔΓ.
    pose proof (closed_tele_wf _ _ _ _ HsΔ HΔ (ctx_app_wf_tail _ _ _ _ HTΘ)) as HΔΘ.
    match goal with Hm : mdenote _ _ _ E' ?R1, Hmd : mdesc_mod ?R1 = Some ?R1m |- _ =>
      destruct (proj2 (Hcl _ HΔΓ) _ Hm) as (Hok1 & _ & HFr1);
      assert (HFr1m : ~ desc_reads_frame Ξ R1m) by (intros Hr; exact (HFr1 (desc_reads_frame_mod _ _ _ Hmd Hr)));
      pose proof (desc_ok_mod _ _ Hg _ _ _ Hok1 Hmd) as Hok1m;
      pose proof (proj1 (mdenote_scoped_all _ _ (wf_gstack_closed _ _ Hg)) _ _ _ Hm _
                    (slots_ok_app _ 0 _ ltac:(intros ? ? ?; lia) ltac:(exact HsΔ)) ltac:(rewrite Nat.add_0_r; exact HsE)) as HsR1;
      rewrite Nat.add_0_r in HsR1;
      pose proof (mdesc_mod_scoped _ _ _ HsR1 Hmd) as HsR1m;
      pose proof (desc_levels_abstractable_mod _ _ _ _ _ _
                    (levels_flag_abstractable _ _ _ _ _ _ _ (Θ' ++ Γ) _ HEw Hlv HΔΓ HΔΘ Hm) Hmd) as HLR1m end.
    pose proof (desc_ok_tele_weaken _ _ Hg _ Θ' _ _ HsΔ HΔΓ HΔΘ HsR1m Hok1m) as Hok2.
    assert (HaΔ : all_assumptions (Δ0 ++ T)) by (apply List.Forall_app; split; assumption).
    pose proof (args_ok_ext _ _ _ _ _ Δ0 Hargs) as Hargs'.
    destruct (ats_up_ok _ _ Hg Ns (Θ' ++ Γ) (Δ0 ++ T) _ lΔ HΔΘ HaΔ (args_ok_length _ _ _ _ _ Hargs') (args_ok_insts _ _ _ _ _ Hargs') Hok2
                (up_evaluated_of _ _ _ _ _ _ (params_evaluated_closed _ _ _ _ _ HsΔ HRΔ HΔΘ) HLR1m (fun _ => HFr1m))) as (R2 & HR2 & _).
    rewrite mdesc_ats_read_mod by (apply mdesc_is_mod_up; eapply mdesc_mod_is_mod; eassumption).
    exists R2; exact HR2.
  - (* an inductive type: its type former at the arguments *)
    destruct E1 as [| | pv1 pq1 k1 D1 ΦD1 | |]; cbn in Hgr; try discriminate; destruct Hgr as (<- & <- & <- & <-).
    cbn [ge_read] in Hed; inversion Hed as [| | ? ? ? ? ? ? ? Mk pm Tm Φm HMk Hpm Hlm | |]; subst.
    destruct HE0 as (_ & [HaU HU] & _).
    destruct HcE0 as ((Δ0 & HΔ0 & _) & _).
    destruct (gc_entry_ind _ _ _ _ _ _ _ _ HeΘ) as [_ Hml].
    destruct (ind_mlookup_selfpath _ _ Hg _ _ _ _ Hml) as [Hmp _ Hlt].
    pose proof (ind_mlookup_group _ _ Hg _ _ _ _ Hml) as Hl.
    pose proof (decl_closed_uparams _ (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl)) as HsU.
    pose proof (loc_child_ind _ _ Hg _ _ _ _ _ _ _ _ _ Hloc' Hent1) as Hbm.
    rewrite Hmp in Hpm; injection Hpm as <-.
    rewrite (gc_loc_of_loc _ _ Hg _ _ _ (or_intror Hbm)) in Hlm; injection Hlm as <- <-.
    assert (HargsU : args_ok Θ Ξ (Θ' ++ Γ) (ind_uparams D) Ns) by (rewrite HΔ0; apply args_ok_ext; exact Hargs).
    destruct (desc_ok_ind_former_at _ _ Hg Hv _ _ _ _ _ _ (qname_in p y) (ind_uparams D) ΦD1 Hl HMk Hlt HΘ' HargsU)
      as (R1 & HR1 & _).
    { eapply desc_ok_closed with (param_level := 0);
        [ exact Hg | apply gc_sub_refl | right; exact Hbm | exact HaU | exact HsU | exact HU | exact HΘ'
        | exact HargsU | constructor | apply params_evaluated_nil | apply desc_levels_abstractable_nil
        | let Hne := fresh "Hne" in intros Hne; contradiction (Hne eq_refl) ]. }
    exists R1; exact HR1.
  - (* a definition with a module part: both parts at the arguments *)
    cbn in Hgr; subst E1.
    cbn [ge_read] in Hed; inversion Hed; subst.
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
    cbn [List.app] in *.
    cbn [ge_valid syn_V] in HE0.
    destruct HE0 as ([HEw [HΔ [[lΔ HRΔ] [(lv & Rt & Hlv) Hcl]]]] & (A0 & -> & _ & HM0) & (A1 & i & HA1 & HA0)).
    pose proof (ctx_pi_at_ass_injective _ _ _ _ Ha HA1) as <-.
    destruct (HM0 _ eq_refl) as (M0 & -> & HM0').
    destruct HcE0 as (_ & Δ0 & E0' & HΔ0 & HaΔ0); injection HΔ0 as HΔ0 HE0'; subst.
    destruct HcE as (HsA & HsM & HsU).
    rewrite gunit_scoped_mk in HsU; destruct HsU as [HsΔ HsE]; cbn [moddef_scoped] in HsE; rewrite Nat.add_0_r in HsE.
    pose proof (ctx_app_wf_tail _ _ _ _ HΘ') as HΓ.
    pose proof (closed_tele_wf _ _ _ _ HsΔ HΔ HΓ) as HΔΓ.
    pose proof (closed_tele_wf _ _ _ _ HsΔ HΔ (ctx_app_wf_tail _ _ _ _ HTΘ)) as HΔΘ.
    match goal with Hm : mdenote _ _ _ ?E' ?R1, Hmd : mdesc_mod ?R1 = Some ?R1m |- _ =>
      destruct (proj2 (Hcl _ HΔΓ) _ Hm) as (Hok1 & _ & HFr1);
      assert (HFr1m : ~ desc_reads_frame Ξ R1m) by (intros Hr; exact (HFr1 (desc_reads_frame_mod _ _ _ Hmd Hr)));
      pose proof (desc_ok_mod _ _ Hg _ _ _ Hok1 Hmd) as Hok1m;
      pose proof (proj1 (mdenote_scoped_all _ _ (wf_gstack_closed _ _ Hg)) _ _ _ Hm _
                    (slots_ok_app _ 0 _ ltac:(intros ? ? ?; lia) ltac:(exact HsΔ)) ltac:(rewrite Nat.add_0_r; exact HsE)) as HsR1;
      rewrite Nat.add_0_r in HsR1;
      pose proof (mdesc_mod_scoped _ _ _ HsR1 Hmd) as HsR1m;
      pose proof (mdesc_mod_is_mod _ _ Hmd) as HmR1m;
      pose proof (desc_levels_abstractable_mod _ _ _ _ _ _
                    (levels_flag_abstractable _ _ _ _ _ _ _ (Θ' ++ Γ) _ HEw Hlv HΔΓ HΔΘ Hm) Hmd) as HLR1m end.
    pose proof (desc_ok_tele_weaken _ _ Hg _ Θ' _ _ HsΔ HΔΓ HΔΘ HsR1m Hok1m) as Hok2.
    assert (HaΔ : all_assumptions (Δ0 ++ T)) by (apply List.Forall_app; split; assumption).
    pose proof (args_ok_ext _ _ _ _ _ Δ0 Hargs) as Hargs'.
    destruct (ats_up_ok _ _ Hg Ns (Θ' ++ Γ) (Δ0 ++ T) _ lΔ HΔΘ HaΔ (args_ok_length _ _ _ _ _ Hargs') (args_ok_insts _ _ _ _ _ Hargs') Hok2
                (up_evaluated_of _ _ _ _ _ _ (params_evaluated_closed _ _ _ _ _ HsΔ HRΔ HΔΘ) HLR1m (fun _ => HFr1m))) as (R2 & HR2 & _).
    pose proof (closed_tele_weaken_exp _ _ _ _ _ _ HsT HA0 HTΘ) as HA0Θ.
    destruct (ats_up_ok _ _ Hg Ns (Θ' ++ Γ) T (mdesc_term ak_relevant A0 (Some M0)) 0 HTΘ Ha (args_ok_length _ _ _ _ _ Hargs)
                (args_ok_insts _ _ _ _ _ Hargs)) as (R3 & HR3 & _).
    { eapply (desc_ok_term _ _ _ ak_relevant); [ exact HA0Θ
                           | intros M1 [= <-]; exact (closed_tele_weaken_exp _ _ _ _ _ _ HsT HM0' HTΘ) ]. }
    { eapply (closed_term_levels_abstractable _ _ _ _ ak_relevant); [ exact HsT | exact HTΘ | discriminate | exact HA0 ]. }
    cbn [mdesc_up option_map] in HR3.
    destruct (mdesc_ats_some_red _ _ _ _ _ HR3) as (B & M' & ->).
    cbn [mdesc_ats_read]; rewrite (mdesc_term_part_ats_of_ats _ _ _ HR3), HR2; eexists; reflexivity.
  - (* a record type: its type former at the arguments *)
    destruct E1 as [| ? [? [? ?| ?]] | | | pv1 pr1 Rr1 ΦR1]; cbn in Hgr; try discriminate; try contradiction.
    destruct Hgr as (<- & <- & <-).
    cbn [ge_read] in Hed; inversion Hed as [| | | | ? ? ? ? ? ? Tm Φm Hlm]; subst.
    pose proof (gc_entry_record_selfpath _ _ Hg _ _ _ _ _ HeΘ) as ->.
    destruct HE0 as (_ & [HaU HU] & _).
    destruct HcE0 as ((Δ0 & HΔ0 & _) & _).
    destruct HcE as ((HF & _) & _).
    assert (Hrl : record_lookup Θ Ξ (qname_in p y) = Some Rr)
      by (unfold record_lookup; rewrite (gc_entry_record_frame_none _ _ _ _ HeΘ), HeΘ; reflexivity).
    pose proof (loc_child_record _ _ Hg _ _ _ _ _ _ _ _ Hloc' Hent1) as Hbm.
    rewrite (gc_loc_of_loc _ _ Hg _ _ _ (or_intror Hbm)) in Hlm; injection Hlm as <- <-.
    assert (HargsP : args_ok Θ Ξ (Θ' ++ Γ) (record_params Rr) Ns) by (rewrite HΔ0; apply args_ok_ext; exact Hargs).
    destruct (desc_ok_record_former_at _ _ Hg Hv _ _ _ _ (qname_in p y) (record_mod_tele (qname_in p y) Rr) ΦR1 Hrl HΘ' HargsP)
      as (R1 & HR1 & _).
    { eapply desc_ok_closed with (param_level := 0);
        [ exact Hg | apply gc_sub_refl | right; exact Hbm | exact HaU
        | exact (record_mod_tele_scoped _ _ (proj2 (proj1 (ctx_scoped_app_iff _ _) HF)))
        | exact HU | exact HΘ' | | constructor | apply params_evaluated_nil | apply desc_levels_abstractable_nil
        | let Hne := fresh "Hne" in intros Hne; contradiction (Hne eq_refl) ].
      unfold record_mod_tele; rewrite HΔ0.
      exact (args_ok_ext _ _ _ _ _ (ce_ass (sort_exp_kind (record_sort Rr)) (record_self (qname_in p y) Rr) :: Δ0) Hargs). }
    exists R1; exact HR1.
Qed.

(** An entry, moved, is readable exactly when it is. *)
Lemma entry_readable_sub : forall E σ, entry_readable (gentry_sub E σ) <-> entry_readable E.
Proof. intros [[|] ? ? ? [] | | | |] σ; cbn; tauto. Qed.

(** A selection from a well-formed module expression moved by a
    substitution, read through what it denotes, is one from the expression
    itself, moved. *)
Lemma generic_sel_reflect : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γg Qg Ψ σ y X, Θ ⍮ Ξ ⍮ Γg ⊢ᵐ Qg ≈ Qg -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : Γg ->
    obs_root Ξ Qg[σ]ᵐ -> mdenote Θ Ξ Ψ (me_mem Qg[σ]ᵐ y) X -> exists Xg, mdenote Θ Ξ Γg (me_mem Qg y) Xg.
Proof.
  intros * Hg * HQ Hσ Hobs HX.
  pose proof (gctx_valid_syn _ _ Hg) as Hv.
  destruct (me_denotes _ _ _ _ _ HQ) as (Rg & Rgm & HRg & HRgm).
  pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ HQ HRg Hσ) as HRgs.
  destruct (mdenote_mem_obs_inv _ _ Hg _ (Qg[σ]ᵐ) _ _ Hobs HX) as (R0 & R0m & Γy & E & rd & R1 & HR0 & Hmd & He & Hed & Hr).
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR0 _ HRgs), (mdesc_mod_sub _ _ σ HRgm) in Hmd; injection Hmd as <-.
  pose proof (desc_ok_mod _ _ Hg _ _ _ (me_desc_ok _ _ _ _ _ _ HQ HRg) HRgm) as Hok.
  pose proof (mdesc_mod_scoped _ _ _ (wf_mdenote_scoped _ _ _ _ _ _ HQ HRg) HRgm) as Hsc.
  destruct Rgm as [r A om | Δ Φw Φx | Θ' p T Φ Ns | Θd A M Rm];
    try (pose proof (mdesc_mod_is_mod _ _ HRgm) as Him; cbn in Him; contradiction).
  - (* an open module: the entry below the substitution, denoted by typing *)
    cbn [mdesc_sub] in He.
    destruct (proj1 (open_entry_iff _ _ _ _ _ _ _) He) as (Φ0w & Hp & HE & _ & _).
    destruct (gm_prefix_sub_inv _ _ _ _ _ Hp) as (Φ0 & E0 & Hp0 & _ & ->).
    apply entry_readable_sub in HE.
    inversion Hok as [| Γ0 Δ0 Φw0 Φx0 l HΦ Hno _ _ Hsh _ _ _ _ _ | |]; subst.
    destruct (entry_denotes_exists _ _ _ _ _ _ _ HΦ Hp0 HE) as (R1g & HR1g).
    destruct (body_shape_fill _ _ (gm_noopen_nopens _ Hno) Hsh) as [Hf _].
    destruct (fill_prefix _ _ _ _ Hf Hp0) as [τ Hτ].
    eexists; eapply mdenote_mem;
      [ exact HRg | exact HRgm | apply (proj2 (open_entry_iff _ _ _ _ _ _ _)); exists Φ0; repeat split; eassumption
      | rewrite <- List.app_assoc; exact HR1g | cbn; rewrite Hτ; reflexivity ].
  - (* a closed module: the same entry, closed, read at the arguments *)
    destruct Hsc as (_ & HU0 & _).
    pose proof He as He'; cbn in He'.
    destruct (gm_prefix_upto Φ y) as [[| Φ0 z E0 |] |] eqn:Hp; try discriminate; injection He' as <- <- <-.
    assert (Heg : mdesc_entry (mdesc_closed Θ' p T Φ Ns) y = Some (nil, ge_read T E0, reader_closed Θ' Ns (apps (a_mem (qname_mod p) y) Ns)))
      by (cbn; rewrite Hp; reflexivity).
    destruct (mdesc_entry_closed _ _ _ _ _ _ _ _ _ HU0 Heg) as (_ & HsE & _).
    cbn [mdesc_sub mdesc_entry_path] in Hed.
    pose proof (edenote_closed_ctx _ _ (wf_gstack_closed _ _ Hg) _ (nil ++ Γg) _ _ _ HsE Hed) as Hedg.
    destruct (closed_entry_read_exists _ _ Hg Hv Γg Θ' p T Φ Ns y nil _ _ R1 Hok Heg Hedg) as (R' & Hr').
    exists R'; eapply mdenote_mem; [ exact HRg | exact HRgm | exact Heg | exact Hedg | exact Hr' ].
Qed.

(** A well-formed module expression applied to a new assumption of its
    outermost parameter is well formed. *)
Lemma generic_app_wf : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γg Qg Rg Tg Bg T1g Srt κ, Θ ⍮ Ξ ⍮ Γg ⊢ᵐ Qg ≈ Qg -> mdenote Θ Ξ Γg Qg Rg ->
    mdesc_mod_tele Rg = Some Tg -> tele_view Tg = Some (Bg, T1g) -> Θ ⍮ Ξ ⍮ Γg ⊢ Bg : Srt -> evaluated_sort Srt -> sort_kind Srt κ ->
    Θ ⍮ Ξ ⍮ Γg ▹{κ} Bg ⊢ᵐ me_app Qg[Wk]ᵐ #0 ≈ me_app Qg[Wk]ᵐ #0.
Proof.
  intros * Hg * HQ HRg HTg Hvg HBg HSrt Hκ.
  pose proof (wf_mdenote_scoped _ _ _ _ _ _ HQ HRg) as Hsc.
  assert (HΓ' : ⊢ Θ ⍮ Ξ ⍮ Γg ▹{κ} Bg) by (eapply wf_ctx_extend; eassumption).
  pose proof (wf_sub_shift _ _ _ _ HΓ') as Hwk.
  pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HQ Hwk) as HQw.
  pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ HQ HRg Hwk) as HRw.
  pose proof (mdesc_mod_tele_sub _ _ Wk _ Hsc HTg) as HTw.
  assert (Hvw : tele_view (tele_sub Tg Wk) = Some (Bg[Wk], tele_sub T1g (q Wk))) by (rewrite tele_view_sub, Hvg; reflexivity).
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HBg Hwk) as HBw; rewrite (evaluated_sort_sub _ _ HSrt) in HBw.
  assert (H0 : Θ ⍮ Ξ ⍮ Γg ▹{κ} Bg ⊢ #0 : Bg[Wk]).
  { replace (Bg[Wk]) with (Bg[↑]ʷ) by (rewrite <- exp_sub_of_wk; reflexivity); apply wf_vlookup; [ exact HΓ' | constructor ]. }
  eapply wf_me_app; [ exact HQw | exact HRw | exact HTw | exact Hvw | exact HBw | exact HSrt | exact H0
                    | apply wf_exp_eq_refl; exact H0 | exact HRw | exact HTw | exact Hvw | exact HBw | exact HSrt | exact H0 ].
Qed.

(** The expression applied to the new assumption, moved by a substitution
    extended by an argument, is the moved expression applied to it. *)
Lemma generic_app_sub : forall Qg σ M, (me_app Qg[Wk]ᵐ #0)[σ,,M]ᵐ = me_app Qg[σ]ᵐ M.
Proof. intros; cbn [modexp_sub]; rewrite modexp_sub_sub, (modexp_sub_sb_eq _ _ _ (sb_shift_extend σ _)); reflexivity. Qed.

(** The sort of a module parameter is of a kind. *)
Lemma evaluated_sort_kind : forall Srt, evaluated_sort Srt -> exists κ, sort_kind Srt κ.
Proof. intros Srt []; eexists; constructor. Qed.

(** Paths from a well-formed module expression of no path, moved by two
    equal substitutions, one for each side, compare their leaves wholly up
    to units. *)
Lemma generic_paths : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ s Γg Qg ρ ρ',
    Θ ⍮ Ξ ⍮ Γg ⊢ᵐ Qg ≈ Qg -> (forall σ, mod_qname Qg[σ]ᵐ = None) -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ ρ ≈ ρ' : Γg ->
    path_pairs Θ Ξ Ψ Qg[ρ]ᵐ s ->
    (forall X, mdenote Θ Ξ Ψ (path_left Qg[ρ]ᵐ s) X -> exists X', mdenote Θ Ξ Ψ (path_right Qg[ρ']ᵐ s) X' /\ leaf_core Θ Ξ Ψ X X') /\
    (forall X', mdenote Θ Ξ Ψ (path_right Qg[ρ']ᵐ s) X' -> exists X, mdenote Θ Ξ Ψ (path_left Qg[ρ]ᵐ s) X /\ leaf_core Θ Ξ Ψ X X').
Proof.
  intros Θ Ξ Hg Ψ s; induction s as [| [y | N N'] s1 IH]; intros * HQ Hq Hρ Hs;
    pose proof (wf_sub_eq_left _ _ _ _ _ _ Hρ) as Hρl; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hρ) as Hρr;
    pose proof (proj1 (mdenote_functional_all _ _ Hg)) as Hf;
    destruct (me_denotes _ _ _ _ _ HQ) as (Rg & Rgm & HRg & HRgm);
    pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ HQ HRg Hρl) as HRl;
    pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ HQ HRg Hρr) as HRr.
  - pose proof (leaf_core_sub_pair _ _ Hg _ _ _ _ _ (me_desc_ok _ _ _ _ _ _ HQ HRg) (wf_mdenote_scoped _ _ _ _ _ _ HQ HRg) Hρ) as Hlc.
    cbn [path_left path_right]; split.
    + intros X HX; rewrite (Hf _ _ _ HX _ HRl); eexists; split; [ exact HRr | exact Hlc ].
    + intros X HX; rewrite (Hf _ _ _ HX _ HRr); eexists; split; [ exact HRl | exact Hlc ].
  - (* a selection: from the selection of the generic expression *)
    inversion Hs as [| ? ? ? Hs1 |]; subst; cbn [path_left path_right].
    assert (Hob : forall σ, obs_root Ξ Qg[σ]ᵐ) by (intros; left; apply Hq).
    assert (Hy : forall σ, mod_qname (me_mem Qg[σ]ᵐ y) = None) by (intros; cbn [mod_qname]; rewrite Hq; reflexivity).
    enough (Hmain : forall Xg, mdenote Θ Ξ Γg (me_mem Qg y) Xg ->
      (forall X, mdenote Θ Ξ Ψ (path_left (me_mem Qg[ρ]ᵐ y) s1) X ->
         exists X', mdenote Θ Ξ Ψ (path_right (me_mem Qg[ρ']ᵐ y) s1) X' /\ leaf_core Θ Ξ Ψ X X') /\
      (forall X', mdenote Θ Ξ Ψ (path_right (me_mem Qg[ρ']ᵐ y) s1) X' ->
         exists X, mdenote Θ Ξ Ψ (path_left (me_mem Qg[ρ]ᵐ y) s1) X /\ leaf_core Θ Ξ Ψ X X')).
    { split.
      - intros X HX; destruct (path_left_back _ _ Hg _ _ _ _ HX) as (R & HR).
        destruct (generic_sel_reflect _ _ Hg _ _ _ _ _ _ HQ Hρl (Hob ρ) HR) as (Xg & HXg).
        exact (proj1 (Hmain _ HXg) _ HX).
      - intros X HX; destruct (path_right_back _ _ Hg _ _ _ _ HX) as (R & HR).
        destruct (generic_sel_reflect _ _ Hg _ _ _ _ _ _ HQ Hρr (Hob ρ') HR) as (Xg & HXg).
        exact (proj2 (Hmain _ HXg) _ HX). }
    intros Xg HXg.
    pose proof (wf_sub_mdenote_mem _ _ _ _ _ _ _ _ _ HQ HXg Hρl) as HXl.
    pose proof (wf_sub_mdenote_mem _ _ _ _ _ _ _ _ _ HQ HXg Hρr) as HXr.
    pose proof (sel_desc_ok _ _ _ _ _ _ _ HQ HXg) as HokX.
    destruct (mdesc_mod Xg) as [Xgm |] eqn:Em.
    + (* a module: the generic selection is well formed *)
      destruct (desc_ok_mod_tele _ _ Hg _ _ _ HokX Em) as [Ty HTy].
      assert (HQy : Θ ⍮ Ξ ⍮ Γg ⊢ᵐ me_mem Qg y ≈ me_mem Qg y) by (eapply wf_me_mem; eassumption).
      exact (IH _ _ _ _ HQy Hy Hρ Hs1).
    + (* a term: no step past it *)
      assert (Hnm : forall σ, mdesc_mod (mdesc_sub Xg σ) = None).
      { intros σ; destruct (mdesc_mod (mdesc_sub Xg σ)) eqn:E; [| reflexivity ].
        destruct (mdesc_mod_sub_inv _ _ _ E) as (? & HE' & _); congruence. }
      destruct s1 as [| st s2].
      * pose proof (leaf_core_sub_pair _ _ Hg _ _ _ _ _ HokX (wf_mdenote_mem_scoped _ _ _ _ _ _ _ HQ HXg) Hρ) as Hlc.
        cbn [path_left path_right]; split.
        -- intros X HX; rewrite (Hf _ _ _ HX _ HXl); eexists; split; [ exact HXr | exact Hlc ].
        -- intros X HX; rewrite (Hf _ _ _ HX _ HXr); eexists; split; [ exact HXl | exact Hlc ].
      * destruct st as [z | M M'].
        -- split; intros X HX; exfalso; cbn [path_left path_right] in HX.
           ++ destruct (path_left_back _ _ Hg _ _ _ _ HX) as (R & HR).
              destruct (mdenote_mem_obs_inv _ _ Hg _ (me_mem Qg[ρ]ᵐ y) _ _ (or_introl (Hy ρ)) HR)
                as (R0 & R0m & _ & _ & _ & _ & HR0 & Hmd & _).
              rewrite (Hf _ _ _ HR0 _ HXl), Hnm in Hmd; discriminate.
           ++ destruct (path_right_back _ _ Hg _ _ _ _ HX) as (R & HR).
              destruct (mdenote_mem_obs_inv _ _ Hg _ (me_mem Qg[ρ']ᵐ y) _ _ (or_introl (Hy ρ')) HR)
                as (R0 & R0m & _ & _ & _ & _ & HR0 & Hmd & _).
              rewrite (Hf _ _ _ HR0 _ HXr), Hnm in Hmd; discriminate.
        -- exfalso; inversion Hs1 as [| | ? R T B T1 ? ? ? Hm Ht _ _ _]; subst.
           rewrite (Hf _ _ _ Hm _ HXl) in Ht; unfold mdesc_mod_tele in Ht; rewrite Hnm in Ht; discriminate.
  - (* an application: the generic expression applied to a new assumption *)
    inversion Hs as [| | ? R T B T1 ? ? ? Hm Ht Hv HN Hs1]; subst.
    pose proof (wf_mdenote_scoped _ _ _ _ _ _ HQ HRg) as Hsc.
    destruct (desc_ok_mod_tele _ _ Hg _ _ _ (me_desc_ok _ _ _ _ _ _ HQ HRg) HRgm) as [Tg HTg].
    rewrite (Hf _ _ _ Hm _ HRl), (mdesc_mod_tele_sub _ _ ρ _ Hsc HTg) in Ht; injection Ht as <-.
    rewrite tele_view_sub in Hv; destruct (tele_view Tg) as [[Bg T1g] |] eqn:Hvg; cbn in Hv; [ injection Hv as <- _ | discriminate ].
    destruct (head_evaluated_of _ _ Hg _ _ _ _ _ _ _ HQ HRg HTg Hvg) as (Srt & HSrt & HBg).
    destruct (evaluated_sort_kind _ HSrt) as [κ Hκ].
    pose proof (generic_app_wf _ _ Hg _ _ _ _ _ _ _ _ HQ HRg HTg Hvg HBg HSrt Hκ) as HQ'.
    destruct (sort_kind_abs_kind_sort_inv _ _ Hκ) as [l Hl].
    pose proof (sub_eq_preserves_exp _ _ _ _ _ HBg _ _ _ Hρ) as HBe; rewrite (evaluated_sort_sub _ _ HSrt) in HBe.
    assert (HN' : Θ ⍮ Ξ ⍮ Ψ ⊢ N' : Bg[ρ']) by (rewrite Hl in HBe; exact (wf_exp_conv_kind _ _ _ _ _ _ (presup_exp_eq_right HN) HBe)).
    pose proof (wf_sub_eq_extend _ _ _ _ _ _ _ _ _ _ _ Hρ HBg Hκ (presup_exp_eq_left HN) HN' HN) as Hρ1.
    destruct (IH _ _ _ _ HQ' (fun σ => eq_refl) Hρ1 ltac:(rewrite generic_app_sub; exact Hs1)) as [H1 H2].
    rewrite !generic_app_sub in H1, H2; cbn [path_left path_right]; split; assumption.
Qed.

(** Paths from a well-formed module expression, the same on both sides
    but for the arguments of their applications, compare their leaves
    wholly up to units: after the first application, both sides are one
    generic path moved ([generic_paths]). *)
Lemma typed_paths : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Ψ s P, Θ ⍮ Ξ ⍮ Ψ ⊢ᵐ P ≈ P -> path_pairs Θ Ξ Ψ P s ->
    (forall X, mdenote Θ Ξ Ψ (path_left P s) X -> exists X', mdenote Θ Ξ Ψ (path_right P s) X' /\ leaf_core Θ Ξ Ψ X X') /\
    (forall X', mdenote Θ Ξ Ψ (path_right P s) X' -> exists X, mdenote Θ Ξ Ψ (path_left P s) X /\ leaf_core Θ Ξ Ψ X X').
Proof.
  intros Θ Ξ Hg Ψ s; induction s as [| [y | N N'] s1 IH]; intros P HP Hs;
    pose proof (proj1 (mdenote_functional_all _ _ Hg)) as Hf;
    pose proof (wf_sub_eq_refl _ _ _ _ _ (wf_sub_id _ _ _ (presup_modexp_eq_ctx HP))) as HId.
  - assert (Hrefl : forall X, mdenote Θ Ξ Ψ P X -> leaf_core Θ Ξ Ψ X X).
    { intros X HX; pose proof (leaf_core_sub_pair _ _ Hg _ _ _ _ _ (me_desc_ok _ _ _ _ _ _ HP HX) (wf_mdenote_scoped _ _ _ _ _ _ HP HX) HId) as H.
      rewrite mdesc_sub_id in H; exact H. }
    cbn [path_left path_right]; split; intros X HX; exists X; split; first [ exact HX | exact (Hrefl _ HX) ].
  - (* a selection: the same on both sides *)
    inversion Hs as [| ? ? ? Hs1 |]; subst; cbn [path_left path_right].
    enough (Hmain : forall Xy, mdenote Θ Ξ Ψ (me_mem P y) Xy ->
      (forall X, mdenote Θ Ξ Ψ (path_left (me_mem P y) s1) X ->
         exists X', mdenote Θ Ξ Ψ (path_right (me_mem P y) s1) X' /\ leaf_core Θ Ξ Ψ X X') /\
      (forall X', mdenote Θ Ξ Ψ (path_right (me_mem P y) s1) X' ->
         exists X, mdenote Θ Ξ Ψ (path_left (me_mem P y) s1) X /\ leaf_core Θ Ξ Ψ X X')).
    { split; intros X HX.
      - destruct (path_left_back _ _ Hg _ _ _ _ HX) as (R & HR); exact (proj1 (Hmain _ HR) _ HX).
      - destruct (path_right_back _ _ Hg _ _ _ _ HX) as (R & HR); exact (proj2 (Hmain _ HR) _ HX). }
    intros Xy HXy; pose proof (sel_desc_ok _ _ _ _ _ _ _ HP HXy) as HokX.
    destruct (mdesc_mod Xy) as [Xm |] eqn:Em.
    + destruct (desc_ok_mod_tele _ _ Hg _ _ _ HokX Em) as [Ty HTy].
      apply IH; [ eapply wf_me_mem; eassumption | exact Hs1 ].
    + destruct s1 as [| st s2].
      * pose proof (leaf_core_sub_pair _ _ Hg _ _ _ _ _ HokX (wf_mdenote_mem_scoped _ _ _ _ _ _ _ HP HXy) HId) as Hlc.
        rewrite mdesc_sub_id in Hlc.
        cbn [path_left path_right]; split; intros X HX; rewrite (Hf _ _ _ HX _ HXy); exists Xy; split; first [ exact HXy | exact Hlc ].
      * destruct st as [z | M M'].
        -- split; intros X HX; exfalso; cbn [path_left path_right] in HX;
             [ destruct (path_left_back _ _ Hg _ _ _ _ HX) as (R & HR) | destruct (path_right_back _ _ Hg _ _ _ _ HX) as (R & HR) ];
             destruct (step_mem_mod _ _ Hg _ _ _ _ _ HR HXy) as (Rm & HRm); congruence.
        -- exfalso; inversion Hs1 as [| | ? R T B T1 ? ? ? Hm Ht _ _ _]; subst.
           rewrite (Hf _ _ _ Hm _ HXy) in Ht; unfold mdesc_mod_tele in Ht; rewrite Em in Ht; discriminate.
  - (* the first application: the expression applied to a new assumption *)
    inversion Hs as [| | ? R T B T1 ? ? ? Hm Ht Hv HN Hs1]; subst.
    destruct (head_evaluated_of _ _ Hg _ _ _ _ _ _ _ HP Hm Ht Hv) as (Srt & HSrt & HB).
    destruct (evaluated_sort_kind _ HSrt) as [κ Hκ].
    pose proof (generic_app_wf _ _ Hg _ _ _ _ _ _ _ _ HP Hm Ht Hv HB HSrt Hκ) as HQ'.
    assert (Hρ1 : Θ ⍮ Ξ ⍮ Ψ ⊢ˢ Id,,N ≈ Id,,N' : Ψ ▹{κ} B).
    { eapply wf_sub_eq_extend; [ exact HId | exact HB | exact Hκ | rewrite exp_sub_id; exact (presup_exp_eq_left HN)
                               | rewrite exp_sub_id; exact (presup_exp_eq_right HN) | rewrite exp_sub_id; exact HN ]. }
    assert (Heq : forall M0, (me_app P[Wk]ᵐ #0)[Id,,M0]ᵐ = me_app P M0) by (intros; rewrite generic_app_sub, modexp_sub_id; reflexivity).
    destruct (generic_paths _ _ Hg _ s1 _ _ _ _ HQ' (fun σ => eq_refl) Hρ1 ltac:(rewrite Heq; exact Hs1)) as [H1 H2].
    rewrite !Heq in H1, H2; cbn [path_left path_right]; split; assumption.
Qed.

(** A well-formed module expression no substitution moves, such as a
    global unit, is compared with itself. *)
Lemma modexp_conv_fixed : forall Θ Ξ Γ H, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> (forall σ, H[σ]ᵐ = H) -> modexp_conv Θ Ξ Γ H H.
Proof.
  intros * HH Hc Ψ σ σ' Hσ; rewrite !Hc.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
  pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HH (wf_sub_eq_left _ _ _ _ _ _ Hσ)) as HP; rewrite Hc in HP.
  apply paths_conv_of_core; [ exact HP |].
  intros s Hs; destruct (typed_paths _ _ Hg _ _ _ HP Hs) as [H1 H2].
  assert (Hc2 : forall X X', leaf_core Θ Ξ Ψ X X' -> path_core Θ Ξ Ψ s X X')
    by (intros X X' Hl; unfold path_core; destruct (path_all_apps s); [ exact (leaf_core_mod_opt _ _ _ _ _ Hl) | exact Hl ]).
  split; [ intros X HX; destruct (H1 _ HX) as (X' & HX' & Hl) | intros X' HX'; destruct (H2 _ HX') as (X & HX & Hl) ]; eauto.
Qed.

(** [ext_slots_conv Θ Ξ Γ Ψ Ψ']: the module slots of a context and of its
    two extensions are compared with their units. *)
Record ext_slots_conv (Θ : gdeps) (Ξ : gstack) (Γ Ψ Ψ' : ctx) : Prop := mk_ext_slots_conv
  { (** The slots of the context extended *)
    ext_slots_base : slots_conv Θ Ξ Γ
    (** those of the left extension *)
  ; ext_slots_left : slots_conv Θ Ξ (Ψ ++ Γ)
    (** and those of the right one *)
  ; ext_slots_right : slots_conv Θ Ξ (Ψ' ++ Γ) }.

(** Every judgment's context has its module slots compared with their
    units ([slots_conv]), and two equal units, and two equal module
    expressions, are compared along paths under every two equal
    substitutions ([modexp_conv]). *)
Theorem modexp_conv_all :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> slots_conv Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> slots_conv Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> slots_conv Θ Ξ Γ) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> slots_conv Θ Ξ Γ) /\
  (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> slots_conv Θ Ξ Γ) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> ext_slots_conv Θ Ξ Γ Ψ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> slots_conv Θ Ξ Γ /\ modexp_conv Θ Ξ Γ (me_lit U) (me_lit U')) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> slots_conv Θ Ξ Γ /\ modexp_conv Θ Ξ Γ H H').
Proof.
  apply syntactic_wf_mut_ind; intros; destruct_conjs.
  all: repeat match goal with H : ext_slots_conv _ _ _ _ _ |- _ => destruct H end.
  all: try match goal with |- ext_slots_conv _ _ _ _ _ => constructor end.
  (** The context of a judgment is the context of one of its premises *)
  all: try match goal with |- slots_conv _ _ ?G => solve [ assumption ] end.
  all: try solve [ apply slots_conv_nil ].
  (** Context extensions *)
  all: try solve [ apply slots_conv_cons; [ econstructor; eassumption | assumption | intros ? [Ha | (? & ? & Ha)]; inversion Ha; subst; split; assumption ] ].
  all: try match goal with |- slots_conv _ _ ?G /\ _ => split; [ assumption |] end.
  (** Extensions of extensions *)
  all: try solve [ cbn [List.app] in *; assumption ].
  all: try solve [ cbn [List.app]; apply slots_conv_cons; [ econstructor; eassumption | assumption | intros ? [Ha | (? & ? & Ha)]; inversion Ha; subst; split; assumption ] ].
  all: try solve [ cbn [List.app];
                   (apply slots_conv_cons;
                    [ first [ eapply wf_ctx_extend_mod | eapply wf_ctx_extend_dm ];
                      eauto using wf_unit_eq_refl_left, wf_unit_eq_refl_right
                    | assumption
                    | intros ? [Ha | (? & ? & Ha)]; inversion Ha; subst;
                      (split; first [ assumption | eapply wf_unit_eq_refl_left; eassumption
                                    | eapply modexp_conv_trans; [ eassumption | apply modexp_conv_sym; eassumption ] ]) ]) ].
  (** Congruence, symmetry and transitivity *)
  all: try solve [ eapply modexp_conv_sym; eassumption | eapply modexp_conv_trans; eassumption | eapply modexp_conv_mem; eassumption ].
  all: try solve [ eapply modexp_conv_app; eauto; eapply wf_modexp_eq_refl_left; eassumption ].
  (** Slots and literals *)
  all: try solve [ unfold slots_conv in *; eauto ].
  all: try solve [ assumption ].
  (** [δ] for a slot; [β] for a literal *)
  all: try solve [ eapply modexp_conv_delta_slot; eassumption ].
  all: try solve [
    match goal with
    | |- modexp_conv _ _ _ (me_app (me_lit (gu_mk (?Δ ++ ce_ass ?κ ?X :: nil) ?D)) ?N) (me_lit ?U2) =>
        replace U2 with ((gu_mk Δ D)[Id,,N]ᵘ) by (rewrite gunit_sub_mk; reflexivity);
        eapply modexp_conv_beta; [ eassumption | eassumption | eassumption |];
        rewrite gunit_sub_mk; cbn [moddef_sub]; first [ eapply wf_me_beta_body | eapply wf_me_beta_alias ]; eassumption
    end ].
  all: try solve [ eapply modexp_conv_beta_alias0; eassumption ].
  all: try solve [ eapply modexp_conv_delta_sel; eassumption ].
  all: try solve [ eapply modexp_conv_expand; eassumption ].
  all: try solve [ eapply modexp_conv_alias; try eassumption; eapply wf_unit_eq_alias; eassumption ].
  all: try solve [ eapply modexp_conv_flatten; try eassumption; eapply wf_unit_eq_flatten; eassumption ].
  all: try solve [ eapply modexp_conv_body; [ eapply wf_unit_eq_body; eassumption | eassumption .. ] ].
  (** A global unit *)
  all: eapply modexp_conv_fixed; [ eapply wf_me_unit; eassumption | intros; reflexivity ].
Qed.
