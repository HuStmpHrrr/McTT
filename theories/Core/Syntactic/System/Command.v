(** * The Static Semantics of Commands

    A command moves the global state: the filed units [Θ] and the stack [Ξ] of
    open frames.  [import] loads the unit it names, if it is not filed yet, by
    running that unit's own commands from nothing, and merges the units that
    run filed into [Θ]; the chain of units whose loading is in progress is what
    rules a cycle out.

    Resolution is lexical — a unit is named by its full path, and [use] lists
    the names it binds — so elaborating a unit needs none of the units it
    imports, which are only loaded while it runs. *)

From Stdlib Require Import List String PeanoNat Bool.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Command.
From Mctt.Core.Syntactic.System Require Import Definitions Lemmas Structural GlobalPresup.
Import Syntax_Notations GlobalCtx_Notations.

Reserved Notation "Θ ⍮ Ξ ⊢[ ch ] c ⇝ Θ' ⍮ Ξ'"
  (at level 70, Ξ at level 69, ch at level 69, c at level 69, Θ' at level 69, Ξ' at level 69).
Reserved Notation "Θ ⍮ Ξ ⊢[ ch ] cs ⇝* Θ' ⍮ Ξ'"
  (at level 70, Ξ at level 69, ch at level 69, cs at level 69, Θ' at level 69, Ξ' at level 69).

(** ** The Stack

    A frame is an unfinished unit or module, named by its (absolute) module
    path: parameters, and the members declared so far.  A member's type and
    body are checked in the telescope of all the frames' parameters,
    [gs_tele], and stored generalized over it. *)

Definition gs_path (Ξ : gstack) : path :=
  match Ξ with
  | (mp, _) :: _ => mp
  | nil => p_abs nil nil
  end.

Definition gs_push (mp : path) (Δ : ctx) (Ξ : gstack) : gstack := (mp, gu_mk Δ ⋄) :: Ξ.

Definition gs_add (x : string) (E : gentry) (Ξ : gstack) : gstack :=
  match Ξ with
  | (mp, U) :: Ξ' => (mp, gu_mk (gu_params U) (gu_mod U ⊳ x ↦ E)) :: Ξ'
  | nil => nil
  end.

Definition gs_fresh (x : string) (Ξ : gstack) : Prop :=
  match Ξ with
  | (_, U) :: _ => gm_fresh x (gu_mod U)
  | nil => False
  end.

(** A definition as it is filed: closed over the frames' parameters. *)
Definition gs_def (b pv : bool) (Ξ : gstack) (A M : exp) : gentry :=
  ge_def b pv (ctx_pi (gs_tele Ξ) A) (Some (ctx_fn (gs_tele Ξ) M)).

(** Filing puts a unit on a new level above everything filed so far, hence
    above every unit it imported. *)
Definition file (fp : fpath) (U : gunit) (Θ : gdeps) : gdeps := ((fp, U) :: nil) :: Θ.

(** ** Nested Modules

    What [import X::Y.M] names: the module at member path [M] of a unit. *)

Fixpoint gm_find_mod (Φ : gmod) (x : string) : option gmod :=
  match Φ with
  | ⋄ => None
  | Φ' ⊳ y ↦ E =>
      if String.eqb x y
      then match E with ge_mod _ Φx => Some Φx | ge_def _ _ _ _ => None end
      else gm_find_mod Φ' x
  end.

Fixpoint gm_has_mod (Φ : gmod) (ip : list string) : Prop :=
  match ip with
  | nil => True
  | x :: ip' => match gm_find_mod Φ x with Some Φx => gm_has_mod Φx ip' | None => False end
  end.

(** ** Merging Filed Units

    Loading starts from nothing, so a unit's level is the length of its longest
    import path, whoever imports it: levels are aligned from the bottom.  A
    path filed on both sides was loaded by two runs of the same file, so it is
    the same unit at the same level ([canon_agree]), and the left copy is kept. *)

Definition gd_mem (fp : fpath) (d : gdep) : bool := existsb (fun e => path_beq fp (fst e)) d.

Definition gd_union (d d' : gdep) : gdep :=
  List.app d (filter (fun e => negb (gd_mem (fst e) d)) d').

(** Bottom level first. *)
Fixpoint merge_up (r r' : list gdep) : list gdep :=
  match r, r' with
  | d :: r, d' :: r' => gd_union d d' :: merge_up r r'
  | nil, r' => r'
  | r, nil => r
  end.

Definition gds_merge (Θ Θ' : gdeps) : gdeps := rev (merge_up (rev Θ) (rev Θ')).

(** The level a path is filed at, counted from the bottom. *)
Fixpoint gds_level_up (fp : fpath) (r : list gdep) (k : nat) : option nat :=
  match r with
  | nil => None
  | d :: r => if gd_mem fp d then Some k else gds_level_up fp r (S k)
  end.

Definition gds_level (Θ : gdeps) (fp : fpath) : option nat := gds_level_up fp (rev Θ) 0.

Definition gds_agree (Θ Θ' : gdeps) : Prop :=
  forall fp U U', gds_lookup Θ fp = Some U -> gds_lookup Θ' fp = Some U' ->
    U = U' /\ gds_level Θ fp = gds_level Θ' fp.

(** ** Privacy

    REVISIT: privacy is checked by the elaborator only, which tracks what is
    visible in the current scope.  Nothing here reads [ge_def]'s privacy flag. *)

Section Semantics.
  (** File IO: the contents of the unit at a path, if there is one. *)
  Variable load_path : fpath -> option string.
  (** Lexing and parsing.  The lexer is OCaml, so this is a parameter too. *)
  Variable read : string -> option Cst.prog.
  (** Elaboration into core commands, which needs no filed unit. *)
  Variable to_core : Cst.prog -> option cunit.

  (** ** Running

      [Θ ⍮ Ξ ⊢[ch] c ⇝ Θ' ⍮ Ξ']: [ch] is the chain of units being loaded, the
      one running [c] first.  Only [rc_import_load] changes [Θ]; the premises
      of [rc_def] and [rc_mod] are those of [wf_gmod_ext] and [wf_gmod_nil]. *)

  Inductive run_cmd : list fpath -> gdeps -> gstack -> ccmd -> gdeps -> gstack -> Prop :=
  | rc_def : forall ch Θ Ξ x b pv A M,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
      gs_fresh x Ξ ->
      Θ ⍮ Ξ ⊢[ch] cc_def x b pv A M ⇝ Θ ⍮ gs_add x (gs_def b pv Ξ A M) Ξ
  (** The body ends on the frame it opened, the stack below as it was; that
      frame becomes the member [x] of the one below, as it is. *)
  | rc_mod : forall ch Θ Ξ x Δ cs Θ' mp U,
      ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
      gs_fresh x Ξ ->
      Θ ⍮ gs_push (path_in (gs_path Ξ) x) Δ Ξ ⊢[ch] cs ⇝* Θ' ⍮ (mp, U) :: Ξ ->
      Θ ⍮ Ξ ⊢[ch] cc_mod x Δ cs ⇝ Θ' ⍮ gs_add x (ge_mod Δ (gu_mod U)) Ξ
  (** Filed already, by an earlier import in any unit: shared, not reloaded. *)
  | rc_import_filed : forall ch Θ Ξ fp ip U,
      gds_lookup Θ fp = Some U ->
      gm_has_mod (gu_mod U) ip ->
      Θ ⍮ Ξ ⊢[ch] cc_import fp ip ⇝ Θ ⍮ Ξ
  (** Not filed: load it, run it from nothing with itself added to the chain,
      file it above what it filed, and merge that in.  A unit already in the
      chain is still being loaded, so importing it is a cycle, and no rule
      applies. *)
  | rc_import_load : forall ch Θ Ξ fp ip src prg u ΘU U,
      gds_lookup Θ fp = None ->
      ~ In fp ch ->
      load_path fp = Some src ->
      read src = Some prg ->
      prog_path prg = fp ->
      to_core prg = Some u ->
      run_unit (fp :: ch) u ΘU U ->
      gm_has_mod (gu_mod U) ip ->
      Θ ⍮ Ξ ⊢[ch] cc_import fp ip ⇝ gds_merge Θ (file fp U ΘU) ⍮ Ξ
  (** An [eval] changes nothing, but must type-check where it stands. *)
  | rc_eval_check : forall ch Θ Ξ M A,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
      Θ ⍮ Ξ ⊢[ch] cc_eval M (Some A) ⇝ Θ ⍮ Ξ
  | rc_eval_infer : forall ch Θ Ξ M A,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
      Θ ⍮ Ξ ⊢[ch] cc_eval M None ⇝ Θ ⍮ Ξ
  where "Θ ⍮ Ξ ⊢[ ch ] c ⇝ Θ' ⍮ Ξ'" := (run_cmd ch Θ Ξ c Θ' Ξ')

  with run_cmds : list fpath -> gdeps -> gstack -> list ccmd -> gdeps -> gstack -> Prop :=
  | rcs_nil : forall ch Θ Ξ, Θ ⍮ Ξ ⊢[ch] nil ⇝* Θ ⍮ Ξ
  | rcs_cons : forall ch Θ Ξ c cs Θ1 Ξ1 Θ2 Ξ2,
      Θ ⍮ Ξ ⊢[ch] c ⇝ Θ1 ⍮ Ξ1 ->
      Θ1 ⍮ Ξ1 ⊢[ch] cs ⇝* Θ2 ⍮ Ξ2 ->
      Θ ⍮ Ξ ⊢[ch] c :: cs ⇝* Θ2 ⍮ Ξ2
  where "Θ ⍮ Ξ ⊢[ ch ] cs ⇝* Θ' ⍮ Ξ'" := (run_cmds ch Θ Ξ cs Θ' Ξ')

  (** [run_unit (fp :: ch) u Θ U]: the unit [fp], at the head of the chain,
      runs from nothing filed.  Its leading imports run on the empty stack,
      then its parameters are checked against what they filed, then its body
      runs in its own frame, named [fp]; [Θ] is what it filed, [U] the unit. *)
  with run_unit : list fpath -> cunit -> gdeps -> gunit -> Prop :=
  | ru_intro : forall fp ch imps P cs Θ1 Θ2 mp U,
      nil ⍮ nil ⊢[fp :: ch] imps ⇝* Θ1 ⍮ nil ->
      ⊢ Θ1 ⍮ nil ⍮ P ->
      Θ1 ⍮ gs_push (p_abs fp nil) P nil ⊢[fp :: ch] cs ⇝* Θ2 ⍮ (mp, U) :: nil ->
      run_unit (fp :: ch) (imps, P, cs) Θ2 U.

  (** The unit given on the command line: run like an imported one, with
      itself as the whole chain. *)
  Definition prog_sem (prg : Cst.prog) (Θ : gdeps) (U : gunit) : Prop :=
    exists u, to_core prg = Some u /\ run_unit (prog_path prg :: nil) u Θ U.
End Semantics.


(** ** A Cycle Has No Meaning *)

Lemma import_acyclic : forall load_path read to_core ch Θ Ξ fp ip Θ' Ξ',
    In fp ch ->
    gds_lookup Θ fp = None ->
    ~ run_cmd load_path read to_core ch Θ Ξ (cc_import fp ip) Θ' Ξ'.
Proof.
  intros * Hin Hnone Hr; inversion Hr; subst; [ congruence | contradiction ].
Qed.

(** ** Running is Deterministic

    Every rule is a check, never a choice, and [load_path], [read] and [to_core]
    are functions; the chain only decides whether a run succeeds.  This is what
    makes a path filed by two runs the same unit, so the biased merge loses
    nothing. *)

Scheme run_cmd_mind := Minimality for run_cmd Sort Prop
with run_cmds_mind := Minimality for run_cmds Sort Prop
with run_unit_mind := Minimality for run_unit Sort Prop.
Combined Scheme run_mut_ind from run_cmd_mind, run_cmds_mind, run_unit_mind.

Section Determinism.
  Variables (load_path : fpath -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  #[local] Notation run_cmd := (run_cmd load_path read to_core).
  #[local] Notation run_cmds := (run_cmds load_path read to_core).
  #[local] Notation run_unit := (run_unit load_path read to_core).

  (** A unit runs in a frame named by the head of its chain, so two runs of it
      agree when their chains have the same head. *)
  Theorem run_functional :
    (forall ch Θ Ξ c Θ1 Ξ1, run_cmd ch Θ Ξ c Θ1 Ξ1 ->
       forall ch' Θ2 Ξ2, run_cmd ch' Θ Ξ c Θ2 Ξ2 -> Θ1 = Θ2 /\ Ξ1 = Ξ2) /\
    (forall ch Θ Ξ cs Θ1 Ξ1, run_cmds ch Θ Ξ cs Θ1 Ξ1 ->
       forall ch' Θ2 Ξ2, run_cmds ch' Θ Ξ cs Θ2 Ξ2 -> Θ1 = Θ2 /\ Ξ1 = Ξ2) /\
    (forall ch u Θ1 U1, run_unit ch u Θ1 U1 ->
       forall ch' Θ2 U2, hd nil ch = hd nil ch' -> run_unit ch' u Θ2 U2 -> Θ1 = Θ2 /\ U1 = U2).
  Proof.
    (* the second derivation is the last hypothesis *)
    apply run_mut_ind; intros; lazymatch goal with H2 : _ |- _ => inversion H2; subst end;
      try congruence; try (split; reflexivity).
    - (* a module: its body *)
      match goal with
      | IH : forall _ _ _, run_cmds _ _ _ _ _ _ -> _, H : run_cmds _ _ _ _ _ _ |- _ =>
          destruct (IH _ _ _ H) as [-> [= -> ->]]
      end; split; reflexivity.
    - (* a load: the same file, hence the same unit *)
      repeat match goal with
        | H1 : ?f ?x = Some ?a, H2 : ?f ?x = Some ?b |- _ =>
            rewrite H1 in H2; injection H2 as <-
        end.
      match goal with
      | IH : forall _ _ _, _ -> run_unit _ _ _ _ -> _, H : run_unit ?c _ _ _ |- _ =>
          destruct (IH c _ _ eq_refl H) as [-> ->]
      end; split; reflexivity.
    - (* a sequence: its head, then its tail from the same state *)
      match goal with
      | IH1 : forall _ _ _, run_cmd _ _ _ ?c _ _ -> _, H1 : run_cmd _ _ _ ?c _ _ |- _ =>
          destruct (IH1 _ _ _ H1); subst
      end; eauto.
    - (* a unit: its imports, then its body from what they filed *)
      cbn [hd] in *; subst.
      match goal with
      | IH1 : forall _ _ _, run_cmds _ nil nil ?is _ _ -> _, H1 : run_cmds _ nil nil ?is _ _ |- _ =>
          destruct (IH1 _ _ _ H1); subst
      end.
      match goal with
      | IH2 : forall _ _ _, run_cmds _ ?T (gs_push ?mp ?P nil) ?cs _ _ -> _,
        H2 : run_cmds _ ?T (gs_push ?mp ?P nil) ?cs _ _ |- _ =>
          destruct (IH2 _ _ _ H2) as [? Heq]; injection Heq; intros; subst
      end; split; reflexivity.
  Qed.
End Determinism.

(** ** Merging Keeps Both Sides

    Pure list reasoning.  [gds_merge] is read top down ([gds_merge_l],
    [gds_merge_r], [gds_merge_both]): the top level of the higher side, or both
    tops united, over the merge of what is below — the shape of
    [gds_merge_ind], which every proof here goes by. *)

Lemma gd_lookup_cons : forall fp fq V d,
    gd_lookup ((fq, V) :: d) fp = if path_beq fp fq then Some V else gd_lookup d fp.
Proof. unfold gd_lookup; intros; cbn; destruct (path_beq fp fq); reflexivity. Qed.

Lemma gd_lookup_app : forall d d' fp,
    gd_lookup (d ++ d') fp = match gd_lookup d fp with Some U => Some U | None => gd_lookup d' fp end.
Proof.
  induction d as [| [fq V] d IH]; intros; cbn [List.app]; [ reflexivity |].
  rewrite !gd_lookup_cons; destruct (path_beq fp fq); auto.
Qed.

Lemma gd_mem_lookup : forall fp d,
    gd_mem fp d = match gd_lookup d fp with Some _ => true | None => false end.
Proof.
  induction d as [| [fq V] d IH]; [ reflexivity |].
  rewrite gd_lookup_cons; unfold gd_mem in *; cbn; destruct (path_beq fp fq); auto.
Qed.

Lemma gd_lookup_in_some : forall d fp U, In (fp, U) d -> gd_lookup d fp <> None.
Proof.
  induction d as [| [fq V] d IH]; cbn [In]; intros * Hin; [ contradiction |].
  rewrite gd_lookup_cons; destruct Hin as [[= -> ->] | Hin].
  - rewrite path_beq_refl; discriminate.
  - destruct (path_beq fp fq); [ discriminate | eauto ].
Qed.

Lemma gd_lookup_union : forall d d' fp,
    gd_lookup (gd_union d d') fp = match gd_lookup d fp with Some U => Some U | None => gd_lookup d' fp end.
Proof.
  unfold gd_union; intros; rewrite gd_lookup_app.
  destruct (gd_lookup d fp) eqn:Hd; [ reflexivity |].
  induction d' as [| [fq V] d' IH]; cbn [filter]; [ reflexivity |].
  destruct (path_beq fp fq) eqn:Hb.
  - apply path_beq_true in Hb as <-; cbn [fst]; rewrite gd_mem_lookup, Hd; cbn.
    rewrite !gd_lookup_cons, path_beq_refl; reflexivity.
  - destruct (negb _); rewrite !gd_lookup_cons, Hb; exact IH.
Qed.

Lemma gd_mem_union : forall fp d d', gd_mem fp (gd_union d d') = gd_mem fp d || gd_mem fp d'.
Proof.
  intros; rewrite !gd_mem_lookup, gd_lookup_union; destruct (gd_lookup d fp); reflexivity.
Qed.

Lemma gds_lookup_cons : forall d Θ fp,
    gds_lookup (d :: Θ) fp = match gd_lookup d fp with Some U => Some U | None => gds_lookup Θ fp end.
Proof. intros; unfold gds_lookup at 1; cbn [concat]; apply gd_lookup_app. Qed.

Lemma gds_level_up_app : forall fp d r k,
    gds_level_up fp (r ++ d :: nil) k =
      match gds_level_up fp r k with Some j => Some j | None => if gd_mem fp d then Some (k + List.length r) else None end.
Proof.
  induction r as [| d' r IH]; intros; cbn.
  - rewrite Nat.add_0_r; reflexivity.
  - destruct (gd_mem fp d'); [ reflexivity |]; rewrite IH; cbn [List.length]; rewrite <- Nat.add_succ_comm; reflexivity.
Qed.

Lemma gds_level_cons : forall d Θ fp,
    gds_level (d :: Θ) fp =
      match gds_level Θ fp with Some k => Some k | None => if gd_mem fp d then Some (List.length Θ) else None end.
Proof. intros; unfold gds_level; cbn [rev]; rewrite gds_level_up_app, length_rev; reflexivity. Qed.

Lemma gds_level_lt : forall Θ fp k, gds_level Θ fp = Some k -> k < List.length Θ.
Proof.
  induction Θ as [| d Θ IH]; intros * H; [ discriminate |].
  rewrite gds_level_cons in H; cbn [List.length].
  destruct (gds_level Θ fp) eqn:Hl; [ injection H as <-; specialize (IH _ _ Hl); lia |].
  destruct (gd_mem fp d); [ injection H as <-; lia | discriminate ].
Qed.

Lemma gds_level_none : forall Θ fp, gds_level Θ fp = None <-> gds_lookup Θ fp = None.
Proof.
  induction Θ as [| d Θ IH]; intros; [ split; reflexivity |].
  rewrite gds_level_cons, gds_lookup_cons, gd_mem_lookup; specialize (IH fp).
  destruct (gd_lookup d fp), (gds_level Θ fp), (gds_lookup Θ fp); intuition discriminate.
Qed.

Lemma gds_level_lookup : forall Θ fp U, gds_lookup Θ fp = Some U -> exists k, gds_level Θ fp = Some k.
Proof.
  intros * H; destruct (gds_level Θ fp) eqn:Hl; [ eauto |].
  apply gds_level_none in Hl; congruence.
Qed.

Lemma gds_level_some : forall Θ fp k, gds_level Θ fp = Some k -> exists U, gds_lookup Θ fp = Some U.
Proof.
  intros * H; destruct (gds_lookup Θ fp) eqn:Hl; [ eauto |].
  apply gds_level_none in Hl; congruence.
Qed.

Lemma gds_fresh_iff : forall fp Θ, gds_fresh fp Θ <-> gds_lookup Θ fp = None.
Proof.
  intros; split; [ apply gds_fresh_no_lookup |].
  unfold gds_fresh, gd_fresh, gds_lookup; intros H Hin.
  apply in_map_iff in Hin as [[fq V] [<- Hin]]; exact (gd_lookup_in_some _ _ _ Hin H).
Qed.

(** ** Filing More Units Keeps an Open Stack Well Formed

    Each entry of each frame was checked against the units filed when the frame
    was open; resolution only grows along [Θ ⊑ Θ'] ([gc_sub_levels]), so its
    typing moves along an embedding.  A frame names its own unit, which must
    stay unfiled: that is the only thing [Θ'] has to grant. *)

Lemma levels_grow : forall Θ Θ' Ξ,
    Θ ⊑ Θ' -> ⊢ Θ' ⍮ Ξ ⍮ ⋅ ->
    (forall Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ' ⍮ Ξ ⍮ Γ) /\
    (forall Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ' ⍮ Ξ ⍮ Γ ⊢ M : A) /\
    (forall Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Θ' ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A) /\
    (forall Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ' ⍮ Ξ ⍮ Γ ⊢ A ⊆ A').
Proof.
  intros * Hs Hb; apply emb_preserves_wf; constructor;
    [ eapply ctx_wf_gctx; exact Hb | apply gc_sub_levels; exact Hs ].
Qed.

Lemma frame_fresh_grow : forall Θ Θ' Ξ mp,
    frame_fresh Θ Ξ mp -> gds_lookup Θ' (p_unit mp) = None -> frame_fresh Θ' Ξ mp.
Proof. intros * H Hn; destruct Ξ as [| [mq V] Ξ]; cbn in *; [ apply gds_fresh_iff; exact Hn | exact H ]. Qed.

Section GrowLevels.
  Variables (Θ Θ' : gdeps).
  Hypothesis Hsub : Θ ⊑ Θ'.

  Lemma global_levels_grow :
    (forall Θ0 Ξ mp E, Θ0 ⍮ Ξ ⍮ mp ⊢e E -> Θ0 = Θ -> ⊢g Θ' ⍮ Ξ ->
       gds_lookup Θ' (p_unit mp) = None -> Θ' ⍮ Ξ ⍮ mp ⊢e E) /\
    (forall Θ0 Ξ mp Δ Φ, Θ0 ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ -> Θ0 = Θ -> ⊢g Θ' ⍮ Ξ ->
       gds_lookup Θ' (p_unit mp) = None -> Θ' ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ).
  Proof.
    apply global_wf_mut_ind; intros; subst.
    all: try assert (Hb : ⊢ Θ' ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    all: try pose proof (levels_grow _ _ _ Hsub Hb) as (Hc & He & _).
    - econstructor; apply He; eassumption.
    - econstructor; apply He; eassumption.
    - econstructor; auto.
    - econstructor; apply Hc; assumption.
    - match goal with HE : Θ ⍮ _ ⍮ path_in _ _ ⊢e _ |- _ => pose proof (wf_gentry_gctx _ _ _ _ HE) as Hg0 end.
      inversion Hg0 as [? ? Hs0]; inversion Hs0 as [| ? ? ? ? ? ? Hff]; subst.
      assert (HΦ : Θ' ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ) by auto.
      econstructor; [ exact HΦ | | assumption ].
      match goal with IH : _ = _ -> ⊢g _ ⍮ (mp, gu_mk Δ Φ) :: Ξ -> _ |- _ => apply IH end;
        [ reflexivity | | assumption ].
      constructor; constructor; [ apply wf_gctx_stack; assumption | constructor; exact HΦ |].
      eapply frame_fresh_grow; eassumption.
  Qed.

  Lemma gstack_levels_grow : forall Ξ, ⊢g Θ ⍮ Ξ -> wf_gdeps Θ' ->
      (forall mp U, In (mp, U) Ξ -> gds_lookup Θ' (p_unit mp) = None) -> ⊢g Θ' ⍮ Ξ.
  Proof.
    induction Ξ as [| [mp U] Ξ IH]; intros HΞ HΘ' Hfr; [ constructor; constructor; exact HΘ' |].
    pose proof (wf_gctx_stack _ _ HΞ) as HΞs; inversion HΞs as [| ? ? ? ? HΞ0 HU Hff]; subst.
    assert (HΞ' : ⊢g Θ' ⍮ Ξ) by (apply IH; [ constructor; assumption | assumption | intros; eapply Hfr; right; eassumption ]).
    pose proof (Hfr mp U (or_introl eq_refl)) as Hn.
    inversion HU; subst.
    constructor; constructor; [ apply wf_gctx_stack; exact HΞ' | | eapply frame_fresh_grow; eassumption ].
    constructor; eapply (proj2 global_levels_grow); eauto.
  Qed.
End GrowLevels.



Lemma merge_up_snoc_l : forall r r' d, List.length r' <= List.length r ->
    merge_up (r ++ d :: nil) r' = merge_up r r' ++ d :: nil.
Proof.
  induction r as [| d0 r IH]; intros [| d' r'] d Hl; cbn in *; try lia; try reflexivity.
  rewrite IH by lia; reflexivity.
Qed.

Lemma merge_up_snoc_r : forall r r' d', List.length r <= List.length r' ->
    merge_up r (r' ++ d' :: nil) = merge_up r r' ++ d' :: nil.
Proof.
  induction r as [| d0 r IH]; intros [| d r'] d' Hl; cbn in *; try lia; try reflexivity.
  rewrite IH by lia; reflexivity.
Qed.

Lemma merge_up_snoc_both : forall r r' d d', List.length r = List.length r' ->
    merge_up (r ++ d :: nil) (r' ++ d' :: nil) = merge_up r r' ++ gd_union d d' :: nil.
Proof.
  induction r as [| d0 r IH]; intros [| d1 r'] d d' Hl; cbn in *; try lia; try reflexivity.
  rewrite IH by lia; reflexivity.
Qed.

Lemma length_merge_up : forall r r', List.length (merge_up r r') = Nat.max (List.length r) (List.length r').
Proof. induction r as [| d r IH]; intros [| d' r']; cbn; auto. Qed.

Lemma length_gds_merge : forall Θ Θ', List.length (gds_merge Θ Θ') = Nat.max (List.length Θ) (List.length Θ').
Proof. intros; unfold gds_merge; rewrite length_rev, length_merge_up, !length_rev; reflexivity. Qed.

Lemma gds_merge_l : forall d Θ Θ', List.length Θ' <= List.length Θ ->
    gds_merge (d :: Θ) Θ' = d :: gds_merge Θ Θ'.
Proof.
  intros; unfold gds_merge; cbn [rev].
  rewrite merge_up_snoc_l, rev_app_distr by (rewrite !length_rev; lia); reflexivity.
Qed.

Lemma gds_merge_r : forall Θ d' Θ', List.length Θ <= List.length Θ' ->
    gds_merge Θ (d' :: Θ') = d' :: gds_merge Θ Θ'.
Proof.
  intros; unfold gds_merge; cbn [rev].
  rewrite merge_up_snoc_r, rev_app_distr by (rewrite !length_rev; lia); reflexivity.
Qed.

Lemma gds_merge_both : forall d Θ d' Θ', List.length Θ = List.length Θ' ->
    gds_merge (d :: Θ) (d' :: Θ') = gd_union d d' :: gds_merge Θ Θ'.
Proof.
  intros; unfold gds_merge; cbn [rev].
  rewrite merge_up_snoc_both, rev_app_distr by (rewrite !length_rev; lia); reflexivity.
Qed.

Lemma gds_merge_ind (P : gdeps -> gdeps -> Prop) :
  P nil nil ->
  (forall d Θ Θ', List.length Θ' <= List.length Θ -> P Θ Θ' -> P (d :: Θ) Θ') ->
  (forall Θ d' Θ', List.length Θ <= List.length Θ' -> P Θ Θ' -> P Θ (d' :: Θ')) ->
  (forall d Θ d' Θ', List.length Θ = List.length Θ' -> P Θ Θ' -> P (d :: Θ) (d' :: Θ')) ->
  forall Θ Θ', P Θ Θ'.
Proof.
  intros Hnil Hl Hr Hb.
  assert (H : forall n Θ Θ', List.length Θ + List.length Θ' < n -> P Θ Θ').
  { induction n as [| n IH]; intros [| d Θ] [| d' Θ'] Hn; cbn in Hn; try lia; [ exact Hnil | | |].
    - apply Hr; [ cbn; lia | apply IH; cbn; lia ].
    - apply Hl; [ cbn; lia | apply IH; cbn; lia ].
    - destruct (Nat.lt_trichotomy (List.length Θ) (List.length Θ')) as [Hlt | [Heq | Hgt]].
      + apply Hr; [ cbn; lia | apply IH; cbn; lia ].
      + apply Hb; [ exact Heq | apply IH; lia ].
      + apply Hl; [ cbn; lia | apply IH; cbn; lia ]. }
  intros; apply (H (S (List.length Θ + List.length Θ'))); lia.
Qed.

Lemma merge_inv : forall Θ Θ' fp U,
    gds_lookup (gds_merge Θ Θ') fp = Some U ->
    gds_lookup Θ fp = Some U \/ gds_lookup Θ' fp = Some U.
Proof.
  intros Θ Θ'; induction Θ, Θ' as [| d Θ Θ' Hlen IH | Θ d' Θ' Hlen IH | d Θ d' Θ' Hlen IH] using gds_merge_ind;
    intros fp U; [ cbn; discriminate | | |];
    [ rewrite gds_merge_l | rewrite gds_merge_r | rewrite gds_merge_both ]; try exact Hlen;
    rewrite !gds_lookup_cons; rewrite ?gd_lookup_union.
  - destruct (gd_lookup d fp); auto.
  - destruct (gd_lookup d' fp); auto.
  - destruct (gd_lookup d fp); [ auto | destruct (gd_lookup d' fp); auto ].
Qed.

Lemma merge_left_at : forall Θ Θ' fp U,
    (forall U', gds_lookup Θ' fp = Some U' -> U = U') ->
    gds_lookup Θ fp = Some U ->
    gds_lookup (gds_merge Θ Θ') fp = Some U.
Proof.
  intros Θ Θ'; induction Θ, Θ' as [| d Θ Θ' Hlen IH | Θ d' Θ' Hlen IH | d Θ d' Θ' Hlen IH] using gds_merge_ind;
    intros fp U Hag HU; [ cbn in HU; discriminate | | |];
    [ rewrite gds_merge_l | rewrite gds_merge_r | rewrite gds_merge_both ]; try exact Hlen;
    rewrite !gds_lookup_cons in *; rewrite ?gd_lookup_union.
  - destruct (gd_lookup d fp); auto.
  - destruct (gd_lookup d' fp); [ rewrite (Hag _ eq_refl); reflexivity | auto ].
  - destruct (gd_lookup d fp); [ assumption |].
    destruct (gd_lookup d' fp); [ rewrite (Hag _ eq_refl); reflexivity | auto ].
Qed.

Lemma merge_right_at : forall Θ Θ' fp U',
    (forall U, gds_lookup Θ fp = Some U -> U = U') ->
    gds_lookup Θ' fp = Some U' ->
    gds_lookup (gds_merge Θ Θ') fp = Some U'.
Proof.
  intros Θ Θ'; induction Θ, Θ' as [| d Θ Θ' Hlen IH | Θ d' Θ' Hlen IH | d Θ d' Θ' Hlen IH] using gds_merge_ind;
    intros fp U' Hag HU; [ cbn in HU; discriminate | | |];
    [ rewrite gds_merge_l | rewrite gds_merge_r | rewrite gds_merge_both ]; try exact Hlen;
    rewrite !gds_lookup_cons in *; rewrite ?gd_lookup_union.
  - destruct (gd_lookup d fp); [ f_equal; auto | auto ].
  - destruct (gd_lookup d' fp); auto.
  - destruct (gd_lookup d fp); [ f_equal; auto |].
    destruct (gd_lookup d' fp); auto.
Qed.

(** Unlike [merge_right], [merge_left] needs agreement too: a higher level of
    the right side may file the same path again, and lookup finds it first. *)
Lemma merge_left : forall Θ Θ', gds_agree Θ Θ' -> Θ ⊑ gds_merge Θ Θ'.
Proof. intros * Hag fp U HU; apply merge_left_at; [ intros; eapply Hag; eassumption | exact HU ]. Qed.

Lemma merge_right : forall Θ Θ', gds_agree Θ Θ' -> Θ' ⊑ gds_merge Θ Θ'.
Proof. intros * Hag fp U HU; apply merge_right_at; [ intros; eapply Hag; eassumption | exact HU ]. Qed.

(** A path's level in the merge is the lower of its two levels. *)
Definition omin (a b : option nat) : option nat :=
  match a, b with
  | Some x, Some y => Some (Nat.min x y)
  | Some x, None => Some x
  | None, b => b
  end.

Local Ltac level_bounds :=
  repeat match goal with H : forall k, Some _ = Some k -> _ |- _ => specialize (H _ eq_refl) end.

Lemma gds_level_merge : forall Θ Θ' fp,
    gds_level (gds_merge Θ Θ') fp = omin (gds_level Θ fp) (gds_level Θ' fp).
Proof.
  intros Θ Θ'; induction Θ, Θ' as [| d Θ Θ' Hlen IH | Θ d' Θ' Hlen IH | d Θ d' Θ' Hlen IH] using gds_merge_ind;
    intros fp; [ reflexivity | | |];
    [ rewrite gds_merge_l | rewrite gds_merge_r | rewrite gds_merge_both ]; try exact Hlen;
    rewrite !gds_level_cons, IH, length_gds_merge; rewrite ?gd_mem_union;
    pose proof (gds_level_lt Θ fp); pose proof (gds_level_lt Θ' fp).
  - replace (Nat.max _ _) with (List.length Θ) by lia.
    destruct (gds_level Θ fp), (gds_level Θ' fp), (gd_mem fp d); cbn; f_equal;
      try reflexivity; level_bounds; lia.
  - replace (Nat.max _ _) with (List.length Θ') by lia.
    destruct (gds_level Θ fp), (gds_level Θ' fp), (gd_mem fp d'); cbn; f_equal;
      try reflexivity; level_bounds; lia.
  - replace (Nat.max _ _) with (List.length Θ') by lia.
    destruct (gds_level Θ fp), (gds_level Θ' fp), (gd_mem fp d), (gd_mem fp d'); cbn; f_equal;
      try reflexivity; level_bounds; lia.
Qed.

Lemma merge_level : forall Θ Θ' fp k,
    gds_agree Θ Θ' ->
    gds_level Θ fp = Some k \/ gds_level Θ' fp = Some k ->
    gds_level (gds_merge Θ Θ') fp = Some k.
Proof.
  intros * Hag Hk; rewrite gds_level_merge.
  destruct (gds_level Θ fp) as [a |] eqn:Ha, (gds_level Θ' fp) as [b |] eqn:Hb; cbn;
    destruct Hk as [Hk | Hk]; try discriminate; try exact Hk.
  all: destruct (gds_level_some _ _ _ Ha) as [U HU], (gds_level_some _ _ _ Hb) as [U' HU'].
  all: destruct (Hag _ _ _ HU HU') as [_ Hl]; rewrite Ha, Hb in Hl; injection Hl as <-;
    injection Hk as <-; rewrite Nat.min_id; reflexivity.
Qed.

(** ** Filing *)

Lemma file_lookup : forall fp U Θ fq,
    gds_lookup (file fp U Θ) fq = if path_beq fq fp then Some U else gds_lookup Θ fq.
Proof.
  intros; unfold file; rewrite gds_lookup_cons, gd_lookup_cons; destruct (path_beq fq fp); reflexivity.
Qed.

Lemma file_sub : forall fp U Θ, gds_lookup Θ fp = None -> Θ ⊑ file fp U Θ.
Proof.
  intros * Hn fq V H; rewrite file_lookup.
  destruct (path_beq fq fp) eqn:Hb; [ apply path_beq_true in Hb; congruence | exact H ].
Qed.

Lemma file_level : forall fp U Θ,
    gds_lookup Θ fp = None ->
    gds_level (file fp U Θ) fp = Some (List.length Θ).
Proof.
  intros * Hn; apply gds_level_none in Hn; unfold file.
  rewrite gds_level_cons, Hn; unfold gd_mem; cbn; rewrite path_beq_refl; reflexivity.
Qed.

Lemma file_level_old : forall fp U Θ fq k,
    gds_level Θ fq = Some k ->
    gds_level (file fp U Θ) fq = Some k.
Proof. intros * H; unfold file; rewrite gds_level_cons, H; reflexivity. Qed.

(** ** Merging Keeps Well-formedness *)

Lemma wf_gdep_iff : forall Θ d,
    wf_gdep Θ d <->
    wf_gdeps Θ /\ NoDup (map fst d) /\
    (forall fp U, In (fp, U) d -> Θ ⍮ nil ⍮ p_abs fp nil ⊢u U /\ gds_fresh fp Θ).
Proof.
  intros; split.
  - induction 1 as [| Θ d U fp Hd IH HU Hfr Hfr']; [ split; [ assumption | split; [ constructor | contradiction ] ] |].
    destruct IH as (HΘ & Hnd & Hu); split; [ assumption | split; [ constructor; assumption |] ].
    intros fq V [[= <- <-] | Hin]; auto.
  - induction d as [| [fp U] d IH]; intros (HΘ & Hnd & Hu); [ constructor; assumption |].
    inversion Hnd; subst; constructor; [ apply IH; split; [ assumption | split; [ assumption | intros; apply Hu; right; assumption ] ]
                                      | apply (Hu fp U); left; reflexivity | apply (Hu fp U); left; reflexivity | assumption ].
Qed.

Lemma wf_file : forall fp U Θ,
    wf_gdeps Θ -> gds_lookup Θ fp = None -> Θ ⍮ nil ⍮ p_abs fp nil ⊢u U -> wf_gdeps (file fp U Θ).
Proof.
  intros * HΘ Hn HU; constructor; [ assumption |].
  constructor; [ constructor; assumption | assumption | apply gds_fresh_iff; assumption | ].
  unfold gd_fresh; cbn; tauto.
Qed.

(** A unit of the top level is filed there only. *)
Lemma wf_top : forall d Θ fp U,
    wf_gdeps (d :: Θ) -> In (fp, U) d ->
    gds_lookup (d :: Θ) fp = Some U /\ gds_level (d :: Θ) fp = Some (List.length Θ) /\ gds_lookup Θ fp = None.
Proof.
  intros * Hwf Hin; inversion Hwf as [| ? ? HΘ Hd]; subst.
  pose proof (wf_gdep_lookup _ _ Hd _ _ Hin) as Hl.
  pose proof (proj1 (gds_fresh_iff _ _) (wf_gdep_fresh _ _ Hd _ _ Hin)) as Hn.
  rewrite gds_lookup_cons, gds_level_cons, Hl, (proj2 (gds_level_none _ _) Hn), gd_mem_lookup, Hl.
  repeat split; assumption.
Qed.

Lemma wf_below : forall d Θ fp U,
    wf_gdeps (d :: Θ) -> gds_lookup Θ fp = Some U ->
    gds_lookup (d :: Θ) fp = Some U /\ gds_level (d :: Θ) fp = gds_level Θ fp.
Proof.
  intros * Hwf HU; inversion Hwf as [| ? ? HΘ Hd]; subst; split.
  - apply gds_lookup_level; [| assumption ]; eapply wf_gdep_fresh; eassumption.
  - destruct (gds_level_lookup _ _ _ HU) as [k Hk]; rewrite gds_level_cons, Hk; reflexivity.
Qed.

Lemma gds_agree_sym : forall Θ Θ', gds_agree Θ Θ' -> gds_agree Θ' Θ.
Proof. intros * Hag fp U U' H H'; destruct (Hag _ _ _ H' H); split; congruence. Qed.

Lemma agree_pop_l : forall d Θ Θ', wf_gdeps (d :: Θ) -> gds_agree (d :: Θ) Θ' -> gds_agree Θ Θ'.
Proof.
  intros * Hwf Hag fp U U' H H'; destruct (wf_below _ _ _ _ Hwf H) as [Hl Hlv].
  rewrite <- Hlv; exact (Hag _ _ _ Hl H').
Qed.

Lemma agree_pop_r : forall d Θ Θ', wf_gdeps (d :: Θ') -> gds_agree Θ (d :: Θ') -> gds_agree Θ Θ'.
Proof. intros * Hwf Hag; apply gds_agree_sym, (agree_pop_l d); [| apply gds_agree_sym ]; assumption. Qed.

(** [global_levels_grow] for a filed unit, which sees no frame but its own,
    named by its path: that path must stay unfiled below it. *)
Lemma unit_levels_grow : forall Θ Θ' fp U,
    Θ ⊑ Θ' -> wf_gdeps Θ' -> gds_lookup Θ' fp = None ->
    Θ ⍮ nil ⍮ p_abs fp nil ⊢u U -> Θ' ⍮ nil ⍮ p_abs fp nil ⊢u U.
Proof.
  intros * Hsub HΘ' Hn HU; inversion HU; subst; constructor.
  eapply (proj2 (global_levels_grow _ _ Hsub));
    [ eassumption | reflexivity | constructor; constructor; exact HΘ' | exact Hn ].
Qed.

Lemma gd_union_keys : forall d d',
    map fst (gd_union d d') = map fst d ++ filter (fun k => negb (gd_mem k d)) (map fst d').
Proof.
  unfold gd_union; intros; rewrite map_app; f_equal.
  induction d' as [| e d' IH]; cbn; [ reflexivity |]; destruct (negb _); cbn; congruence.
Qed.

Lemma gd_union_in : forall d d' fp U,
    In (fp, U) (gd_union d d') -> In (fp, U) d \/ (In (fp, U) d' /\ gd_mem fp d = false).
Proof.
  unfold gd_union; intros * Hin; apply in_app_iff in Hin as [Hin | Hin]; [ auto |].
  apply filter_In in Hin as [Hin Hb]; apply negb_true_iff in Hb; auto.
Qed.

Lemma gd_mem_in : forall d fp U, In (fp, U) d -> gd_mem fp d = true.
Proof.
  intros * Hin; rewrite gd_mem_lookup; destruct (gd_lookup d fp) eqn:H; [ reflexivity |].
  exfalso; exact (gd_lookup_in_some _ _ _ Hin H).
Qed.

Lemma gd_union_nodup : forall d d',
    NoDup (map fst d) -> NoDup (map fst d') -> NoDup (map fst (gd_union d d')).
Proof.
  intros * Hd Hd'; rewrite gd_union_keys; apply NoDup_app; [ assumption | apply NoDup_filter; assumption |].
  intros fp Hin Hin'; apply filter_In in Hin' as [_ Hb]; apply negb_true_iff in Hb.
  apply in_map_iff in Hin as [[fq V] [<- Hin]]; cbn in Hb; rewrite (gd_mem_in _ _ _ Hin) in Hb; discriminate.
Qed.

(** A path of one side is not filed in the other below its level, as the two
    agree on its level. *)
Lemma agree_fresh : forall d Θ Θ' fp U,
    wf_gdeps (d :: Θ) -> gds_agree (d :: Θ) Θ' -> In (fp, U) d ->
    List.length Θ' <= List.length Θ -> gds_lookup Θ' fp = None.
Proof.
  intros * Hwf Hag Hin Hlen; destruct (wf_top _ _ _ _ Hwf Hin) as (Hl & Hlv & _).
  destruct (gds_lookup Θ' fp) as [U' |] eqn:H'; [ exfalso | reflexivity ].
  destruct (Hag _ _ _ Hl H') as [_ Heq]; rewrite Hlv in Heq; symmetry in Heq.
  pose proof (gds_level_lt _ _ _ Heq); lia.
Qed.

Lemma merge_fresh : forall Θ Θ' fp,
    gds_lookup Θ fp = None -> gds_lookup Θ' fp = None -> gds_fresh fp (gds_merge Θ Θ').
Proof.
  intros * H H'; apply gds_fresh_iff.
  destruct (gds_lookup (gds_merge Θ Θ') fp) eqn:E; [| reflexivity ].
  apply merge_inv in E as [E | E]; congruence.
Qed.

(** A unit of the merge was checked against the levels below it on its own
    side, which the merge's levels below it extend; its path is fresh there
    because the two sides agree on its level ([agree_fresh]). *)
Theorem merge_wf : forall Θ Θ',
    wf_gdeps Θ -> wf_gdeps Θ' -> gds_agree Θ Θ' -> wf_gdeps (gds_merge Θ Θ').
Proof.
  intros Θ Θ'; induction Θ, Θ' as [| d Θ Θ' Hlen IH | Θ d' Θ' Hlen IH | d Θ d' Θ' Hlen IH] using gds_merge_ind;
    intros Hwf Hwf' Hag; [ constructor | | |].
  - (* the left top is above everything on the right *)
    rewrite gds_merge_l by exact Hlen.
    pose proof (agree_pop_l _ _ _ Hwf Hag) as Hag0.
    inversion Hwf as [| ? ? HΘ Hd]; subst.
    assert (HM : wf_gdeps (gds_merge Θ Θ')) by auto.
    constructor; [ exact HM |].
    apply wf_gdep_iff in Hd as (_ & Hnd & Hu); apply wf_gdep_iff; split; [ exact HM | split; [ exact Hnd |] ].
    intros fp U Hin; destruct (Hu _ _ Hin) as [HU Hfr].
    assert (Hfr' : gds_fresh fp (gds_merge Θ Θ'))
      by (apply merge_fresh; [ apply gds_fresh_iff, Hfr | eapply agree_fresh; eassumption ]).
    split; [| exact Hfr' ].
    eapply unit_levels_grow; [ apply merge_left, Hag0 | exact HM | apply gds_fresh_iff, Hfr' | exact HU ].
  - (* the right top is above everything on the left *)
    rewrite gds_merge_r by exact Hlen.
    pose proof (agree_pop_r _ _ _ Hwf' Hag) as Hag0.
    inversion Hwf' as [| ? ? HΘ' Hd']; subst.
    assert (HM : wf_gdeps (gds_merge Θ Θ')) by auto.
    constructor; [ exact HM |].
    apply wf_gdep_iff in Hd' as (_ & Hnd & Hu); apply wf_gdep_iff; split; [ exact HM | split; [ exact Hnd |] ].
    intros fp U Hin; destruct (Hu _ _ Hin) as [HU Hfr].
    assert (Hfr' : gds_fresh fp (gds_merge Θ Θ'))
      by (apply merge_fresh; [ eapply agree_fresh; [ | apply gds_agree_sym | | ]; eassumption | apply gds_fresh_iff, Hfr ]).
    split; [| exact Hfr' ].
    eapply unit_levels_grow; [ apply merge_right, Hag0 | exact HM | apply gds_fresh_iff, Hfr' | exact HU ].
  - (* the two tops are united *)
    rewrite gds_merge_both by exact Hlen.
    pose proof (agree_pop_r _ _ _ Hwf' (agree_pop_l _ _ _ Hwf Hag)) as Hag0.
    pose proof (agree_pop_l _ _ _ Hwf Hag) as HagL.
    pose proof (agree_pop_r _ _ _ Hwf' Hag) as HagR.
    inversion Hwf as [| ? ? HΘ Hd]; inversion Hwf' as [| ? ? HΘ' Hd']; subst.
    assert (HM : wf_gdeps (gds_merge Θ Θ')) by auto.
    constructor; [ exact HM |].
    apply wf_gdep_iff in Hd as (_ & Hnd & Hu), Hd' as (_ & Hnd' & Hu').
    apply wf_gdep_iff; split; [ exact HM | split; [ apply gd_union_nodup; assumption |] ].
    intros fp U Hin; apply gd_union_in in Hin as [Hin | [Hin _]].
    + destruct (Hu _ _ Hin) as [HU Hfr].
      assert (Hfr' : gds_fresh fp (gds_merge Θ Θ'))
        by (apply merge_fresh; [ apply gds_fresh_iff, Hfr | apply (agree_fresh _ _ _ _ _ Hwf HagR Hin); lia ]).
      split; [| exact Hfr' ].
      eapply unit_levels_grow; [ apply merge_left, Hag0 | exact HM | apply gds_fresh_iff, Hfr' | exact HU ].
    + destruct (Hu' _ _ Hin) as [HU Hfr].
      assert (Hfr' : gds_fresh fp (gds_merge Θ Θ'))
        by (apply merge_fresh; [ apply (agree_fresh _ _ _ _ _ Hwf' (gds_agree_sym _ _ HagL) Hin); lia
                               | apply gds_fresh_iff, Hfr ]).
      split; [| exact Hfr' ].
      eapply unit_levels_grow; [ apply merge_right, Hag0 | exact HM | apply gds_fresh_iff, Hfr' | exact HU ].
Qed.

(** ** Running Keeps the State Well Formed

    The state stays canonical, not only well formed: that is what makes a
    loaded unit agree with what is filed already, so the merge is well formed.
    Loading files the derivation of the unit it ran, hence the dependent
    scheme. *)

Scheme run_cmd_dind := Induction for run_cmd Sort Prop
with run_cmds_dind := Induction for run_cmds Sort Prop
with run_unit_dind := Induction for run_unit Sort Prop.
Combined Scheme run_mut_dind from run_cmd_dind, run_cmds_dind, run_unit_dind.

(** What a run keeps of a stack: each frame's path and parameters. *)
Definition gs_shape (Ξ : gstack) : list (path * ctx) := map (fun f => (fst f, gu_params (snd f))) Ξ.

Lemma gs_add_params : forall x E Ξ, gs_shape (gs_add x E Ξ) = gs_shape Ξ.
Proof. intros ? ? [| [? ?] ?]; reflexivity. Qed.

(** The frames of a stack belong to units on the chain: the ones being
    loaded, so none a load files. *)
Definition stack_in (ch : list fpath) (Ξ : gstack) : Prop :=
  forall mp U, In (mp, U) Ξ -> In (p_unit mp) ch.

Lemma stack_in_add : forall ch x E Ξ, stack_in ch Ξ -> stack_in ch (gs_add x E Ξ).
Proof.
  intros * H mp U Hin; destruct Ξ as [| [mq V] Ξ]; [ contradiction |].
  destruct Hin as [[= <- <-] | Hin]; [ eapply H; left; reflexivity | eapply H; right; exact Hin ].
Qed.

Lemma stack_in_push : forall ch x Δ Ξ,
    stack_in ch Ξ -> gs_fresh x Ξ -> stack_in ch (gs_push (path_in (gs_path Ξ) x) Δ Ξ).
Proof.
  intros * H Hfr mp U [[= <- <-] | Hin]; [| eapply H; exact Hin ].
  destruct Ξ as [| [mq V] Ξ]; [ contradiction |]; cbn; eapply H; left; reflexivity.
Qed.

Section WellFormed.
  Variables (load_path : fpath -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  #[local] Notation run_cmd := (run_cmd load_path read to_core).
  #[local] Notation run_cmds := (run_cmds load_path read to_core).
  #[local] Notation run_unit := (run_unit load_path read to_core).

  Lemma run_chain_fresh :
    (forall ch Θ Ξ c Θ' Ξ', run_cmd ch Θ Ξ c Θ' Ξ' ->
       forall fq, In fq ch -> gds_lookup Θ fq = None -> gds_lookup Θ' fq = None) /\
    (forall ch Θ Ξ cs Θ' Ξ', run_cmds ch Θ Ξ cs Θ' Ξ' ->
       forall fq, In fq ch -> gds_lookup Θ fq = None -> gds_lookup Θ' fq = None) /\
    (forall ch u Θ U, run_unit ch u Θ U -> forall fq, In fq ch -> gds_lookup Θ fq = None).
  Proof.
    apply run_mut_ind; intros; eauto.
    - (* a load files what its unit filed, and the unit, which is not on the chain *)
      destruct (gds_lookup (gds_merge _ _) fq) eqn:E; [ exfalso | reflexivity ].
      apply merge_inv in E as [E | E]; [ congruence |].
      rewrite file_lookup in E; destruct (path_beq fq fp) eqn:Hb.
      + apply path_beq_true in Hb; subst; contradiction.
      + match goal with IH : forall _, In _ (fp :: ch) -> _ |- _ => rewrite (IH fq ltac:(right; assumption)) in E end.
        discriminate.
  Qed.

  (** A run keeps the parameters of every frame. *)
  Lemma run_params :
    (forall ch Θ Ξ c Θ' Ξ', run_cmd ch Θ Ξ c Θ' Ξ' -> gs_shape Ξ' = gs_shape Ξ) /\
    (forall ch Θ Ξ cs Θ' Ξ', run_cmds ch Θ Ξ cs Θ' Ξ' -> gs_shape Ξ' = gs_shape Ξ) /\
    (forall ch u Θ U, run_unit ch u Θ U -> True).
  Proof.
    apply run_mut_ind; intros; rewrite ?gs_add_params; solve [ congruence | exact I ].
  Qed.

  (** A filed unit is what loading its file yields, at the level that run
      filed below it. *)
  Definition canon (Θ : gdeps) : Prop :=
    forall fp U, gds_lookup Θ fp = Some U ->
      exists src prg u ch ΘU, load_path fp = Some src /\ read src = Some prg /\ to_core prg = Some u /\
        run_unit (fp :: ch) u ΘU U /\ gds_level Θ fp = Some (List.length ΘU).

  Lemma canon_agree : forall Θ1 Θ2, canon Θ1 -> canon Θ2 -> gds_agree Θ1 Θ2.
  Proof.
    intros * H1 H2 fp U1 U2 E1 E2.
    destruct (H1 _ _ E1) as (src & prg & u & ch & ΘU & Hl & Hr & Ht & Hu & Hlv).
    destruct (H2 _ _ E2) as (src' & prg' & u' & ch' & ΘU' & Hl' & Hr' & Ht' & Hu' & Hlv').
    rewrite Hl in Hl'; injection Hl' as <-; rewrite Hr in Hr'; injection Hr' as <-;
      rewrite Ht in Ht'; injection Ht' as <-.
    destruct (proj2 (proj2 (run_functional load_path read to_core)) _ _ _ _ Hu (fp :: ch') _ _ eq_refl Hu') as [<- <-].
    split; congruence.
  Qed.

  Lemma canon_nil : canon nil.
  Proof. intros ? ? H; discriminate H. Qed.

  Lemma canon_file : forall ch fp src prg u ΘU U,
      gds_lookup ΘU fp = None ->
      load_path fp = Some src -> read src = Some prg -> to_core prg = Some u ->
      run_unit (fp :: ch) u ΘU U -> canon ΘU -> canon (file fp U ΘU).
  Proof.
    intros * Hn Hl Hr Ht Hu Hc fq V HV; rewrite file_lookup in HV.
    destruct (path_beq fq fp) eqn:Hb.
    - apply path_beq_true in Hb as ->; injection HV as <-.
      exists src, prg, u, ch, ΘU; repeat split; try assumption; apply file_level, Hn.
    - destruct (Hc _ _ HV) as (src' & prg' & u' & ch' & ΘV & ? & ? & ? & ? & Hlv).
      exists src', prg', u', ch', ΘV; repeat split; try assumption; apply file_level_old, Hlv.
  Qed.

  Lemma canon_merge : forall Θ1 Θ2, canon Θ1 -> canon Θ2 -> canon (gds_merge Θ1 Θ2).
  Proof.
    intros * H1 H2 fp U HU; pose proof (canon_agree _ _ H1 H2) as Hag.
    apply merge_inv in HU as [HU | HU];
      [ destruct (H1 _ _ HU) as (src & prg & u & ch & ΘU & ? & ? & ? & ? & Hlv)
      | destruct (H2 _ _ HU) as (src & prg & u & ch & ΘU & ? & ? & ? & ? & Hlv) ];
      exists src, prg, u, ch, ΘU; repeat split; try assumption; apply merge_level; auto.
  Qed.

  Lemma stack_in_shape : forall ch Ξ Ξ', gs_shape Ξ' = gs_shape Ξ -> stack_in ch Ξ -> stack_in ch Ξ'.
  Proof.
    intros * Hs H mp U Hin.
    assert (Hin' : In (mp, gu_params U) (gs_shape Ξ')) by (apply (in_map (fun f => (fst f, gu_params (snd f))) _ _ Hin)).
    rewrite Hs in Hin'; apply in_map_iff in Hin' as ([mq V] & [= -> _] & HV); eapply H; exact HV.
  Qed.

  Theorem run_wf :
    (forall ch Θ Ξ c Θ' Ξ', run_cmd ch Θ Ξ c Θ' Ξ' ->
       ⊢g Θ ⍮ Ξ -> canon Θ -> stack_in ch Ξ -> ⊢g Θ' ⍮ Ξ' /\ canon Θ' /\ Θ ⊑ Θ') /\
    (forall ch Θ Ξ cs Θ' Ξ', run_cmds ch Θ Ξ cs Θ' Ξ' ->
       ⊢g Θ ⍮ Ξ -> canon Θ -> stack_in ch Ξ -> ⊢g Θ' ⍮ Ξ' /\ canon Θ' /\ Θ ⊑ Θ') /\
    (forall ch u Θ U, run_unit ch u Θ U ->
       wf_gdeps Θ /\ canon Θ /\ Θ ⍮ nil ⍮ p_abs (hd nil ch) nil ⊢u U).
  Proof.
    apply run_mut_dind.
    - (* a definition: the new member is checked against the frame so far *)
      intros ch Θ Ξ x b pv A M HM Hfr HΞ Hc Hst.
      destruct Ξ as [| [mp [P Φ]] Ξ]; [ contradiction |]; cbn in Hfr |- *.
      split; [| split; [ exact Hc | apply gds_sub_refl ] ].
      pose proof (wf_gctx_stack _ _ HΞ) as Hs; inversion Hs as [| ? ? ? ? Hs0 HU Hff]; subst.
      inversion HU; subst.
      constructor; constructor; [ exact Hs0 | | exact Hff ].
      constructor; cbn; econstructor; [ eassumption | unfold gs_def; constructor; exact HM | exact Hfr ].
    - (* a module: its body ends on a frame with the path and parameters it opened with *)
      intros ch Θ Ξ x Δ cs Θ' mp' U HΔ Hfr Hr IH HΞ Hc Hst.
      destruct Ξ as [| [mp [P Φ]] Ξ0]; [ contradiction |]; cbn [gs_fresh gs_path] in Hfr, Hr, IH |- *.
      assert (Hpush : ⊢g Θ ⍮ gs_push (path_in mp x) Δ ((mp, gu_mk P Φ) :: Ξ0)).
      { constructor; constructor; [ apply wf_gctx_stack, HΞ | constructor; constructor; exact HΔ |].
        cbn; exists x; split; [ reflexivity | exact Hfr ]. }
      destruct (IH Hpush Hc (stack_in_push _ x Δ _ Hst Hfr)) as (HΞ' & Hc' & Hsub).
      pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ Hr) as Hp; cbn in Hp; injection Hp as -> HP.
      split; [| split; assumption ].
      pose proof (wf_gctx_stack _ _ HΞ') as Hs; inversion Hs as [| ? ? ? ? Hs1 HU Hff1]; subst.
      inversion Hs1 as [| ? ? ? ? Hs0 HV Hff0]; subst.
      inversion HU; inversion HV; subst.
      constructor; constructor; [ exact Hs0 | | exact Hff0 ].
      constructor; cbn; econstructor; [ eassumption | constructor; eassumption | exact Hfr ].
    - intros; split; [| split ]; auto using gds_sub_refl.
    - (* a load: the unit is filed on its own, then merged in; the frames are
         of units on the chain, so it files none of them *)
      intros ch Θ Ξ fp ip src prg u ΘU U Hn Hnin Hl Hr Hp Ht Hu IH Hm HΞ Hc Hst.
      destruct IH as (HΘU & HcU & HU); cbn [hd] in HU.
      pose proof (proj2 (proj2 run_chain_fresh) _ _ _ _ Hu fp ltac:(left; reflexivity)) as HfU.
      assert (Hcf : canon (file fp U ΘU)) by (eapply canon_file; eassumption).
      assert (Hag : gds_agree Θ (file fp U ΘU)) by (apply canon_agree; assumption).
      assert (Hwf : wf_gdeps (gds_merge Θ (file fp U ΘU)))
        by (apply merge_wf; [ eapply wf_gctx_deps; eassumption | apply wf_file; assumption | exact Hag ]).
      split; [ eapply gstack_levels_grow; [ apply merge_left, Hag | exact HΞ | exact Hwf |] |].
      + intros mq V Hin; pose proof (Hst _ _ Hin) as Hch.
        destruct (gds_lookup (gds_merge _ _) (p_unit mq)) eqn:E; [ exfalso | reflexivity ].
        apply merge_inv in E as [E | E].
        * rewrite (wf_gstack_frames _ _ (wf_gctx_stack _ _ HΞ) _ _ Hin) in E; discriminate.
        * rewrite file_lookup in E; destruct (path_beq (p_unit mq) fp) eqn:Hb.
          -- apply path_beq_true in Hb; rewrite Hb in Hch; contradiction.
          -- rewrite (proj2 (proj2 run_chain_fresh) _ _ _ _ Hu _ (or_intror Hch)) in E; discriminate.
      + split; [ apply canon_merge; assumption | apply merge_left, Hag ].
    - intros; split; [| split ]; auto using gds_sub_refl.
    - intros; split; [| split ]; auto using gds_sub_refl.
    - intros; split; [| split ]; auto using gds_sub_refl.
    - intros * Hr1 IH1 Hr2 IH2 HΞ Hc Hst.
      destruct (IH1 HΞ Hc Hst) as (H1 & Hc1 & Hs1).
      pose proof (stack_in_shape _ _ _ (proj1 run_params _ _ _ _ _ _ Hr1) Hst) as Hst1.
      destruct (IH2 H1 Hc1 Hst1) as (H2 & Hc2 & Hs2).
      split; [| split ]; eauto using gds_sub_trans.
    - (* a unit: its imports from nothing, its parameters, then its body in
         the frame named by its path, which nothing it imported filed *)
      intros fp ch imps P cs Θ1 Θ2 mp U Hi IHi HP Hb IHb.
      destruct (IHi ltac:(constructor; constructor; constructor) canon_nil ltac:(intros ? ? [])) as (H1 & Hc1 & _).
      assert (Hn1 : gds_lookup Θ1 fp = None)
        by exact (proj1 (proj2 run_chain_fresh) _ _ _ _ _ _ Hi fp (or_introl eq_refl) eq_refl).
      assert (Hpush : ⊢g Θ1 ⍮ gs_push (p_abs fp nil) P nil).
      { constructor; constructor; [ apply wf_gctx_stack, H1 | constructor; constructor | ].
        - cbn; rewrite app_nil_r; exact HP.
        - cbn; apply gds_fresh_iff; exact Hn1. }
      destruct (IHb Hpush Hc1 ltac:(intros ? ? [[= <- <-] | []]; left; reflexivity)) as (H2 & Hc2 & _).
      pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ Hb) as Hp; cbn in Hp; injection Hp as -> _.
      pose proof (wf_gctx_stack _ _ H2) as Hs; inversion Hs; subst.
      split; [ eapply wf_gctx_deps; eassumption | split; [ assumption | cbn; assumption ] ].
  Qed.

  Corollary import_coherent : forall ch Θ Ξ fp ip Θ',
      ⊢g Θ ⍮ Ξ -> canon Θ -> stack_in ch Ξ ->
      run_cmd ch Θ Ξ (cc_import fp ip) Θ' Ξ ->
      wf_gdeps Θ' /\ gds_lookup Θ' fp <> None.
  Proof.
    intros * HΞ Hc Hst Hr; destruct (proj1 run_wf _ _ _ _ _ _ Hr HΞ Hc Hst) as (H' & _ & _).
    split; [ eapply wf_gctx_deps; eassumption |].
    inversion Hr; subst; [ congruence |].
    (* [fp] was loaded: it is on the top level of what it filed *)
    match goal with Hu : run_unit (?f :: _) _ ?ΘU ?U |- _ =>
      destruct (proj2 (proj2 run_wf) _ _ _ _ Hu) as (HΘU & HcU & _);
      pose proof (proj2 (proj2 run_chain_fresh) _ _ _ _ Hu f ltac:(left; reflexivity)) as HfU;
      assert (Hag : gds_agree Θ (file f U ΘU)) by (apply canon_agree; [| eapply canon_file ]; eassumption);
      rewrite (merge_right _ _ Hag f U); [ discriminate | rewrite file_lookup, path_beq_refl; reflexivity ]
    end.
  Qed.

  Corollary prog_sem_wf : forall prg Θ U,
      prog_sem load_path read to_core prg Θ U ->
      wf_gdeps Θ /\ Θ ⍮ nil ⍮ p_abs (prog_path prg) nil ⊢u U.
  Proof.
    intros * (u & _ & Hu); destruct (proj2 (proj2 run_wf) _ _ _ _ Hu) as (? & _ & ?); split; assumption.
  Qed.
End WellFormed.


(** ** Restricting to What a Unit Imported

    The executable ([Extraction.Command]) keeps one set of filed units for the
    whole program, so no unit is run twice; but a unit runs from nothing, and
    may mention only what it imported.  So it is checked against the
    restriction of that set to the paths it imported, which has the lookups and
    levels of the judgment's state ([equiv_restrict]).  Checking against the
    whole set would accept a unit mentioning a unit it never imported, filed by
    someone else. *)

Definition gd_restrict (S : list fpath) (d : gdep) : gdep :=
  filter (fun e => existsb (path_beq (fst e)) S) d.

(** Drop the empty levels on top, so a unit filed above a restriction lands at
    its canonical level. *)
Fixpoint trim_top (Θ : gdeps) : gdeps :=
  match Θ with
  | nil :: Θ' => trim_top Θ'
  | _ => Θ
  end.

Definition gds_restrict (S : list fpath) (Θ : gdeps) : gdeps := trim_top (map (gd_restrict S) Θ).

Definition gds_dom (Θ : gdeps) : list fpath := map fst (List.concat Θ).

Definition gds_equiv (Θ Θ' : gdeps) : Prop :=
  Θ ⊑ Θ' /\ Θ' ⊑ Θ /\ forall fp, gds_level Θ fp = gds_level Θ' fp.

(** What makes the length of a well-formed [gdeps] a function of its levels
    ([equiv_length]). *)
Definition top_ne (Θ : gdeps) : Prop :=
  match Θ with
  | nil => True
  | d :: _ => d <> nil
  end.

Lemma existsb_path_beq : forall fp S, existsb (path_beq fp) S = true <-> In fp S.
Proof.
  intros; rewrite existsb_exists; split.
  - intros (fq & Hin & Hb); apply path_beq_true in Hb as ->; exact Hin.
  - intros Hin; exists fp; split; [ exact Hin | apply path_beq_refl ].
Qed.

Lemma existsb_path_beq_false : forall fp S, existsb (path_beq fp) S = false <-> ~ In fp S.
Proof.
  intros; rewrite <- existsb_path_beq; destruct (existsb _ _); split; congruence.
Qed.

Lemma gd_lookup_restrict : forall S d fp,
    gd_lookup (gd_restrict S d) fp = if existsb (path_beq fp) S then gd_lookup d fp else None.
Proof.
  unfold gd_restrict; induction d as [| [fq V] d IH]; intros; cbn [filter fst].
  - destruct (existsb _ _); reflexivity.
  - destruct (path_beq fp fq) eqn:Hb.
    + apply path_beq_true in Hb as <-.
      destruct (existsb (path_beq fp) S) eqn:E; rewrite ?gd_lookup_cons, ?path_beq_refl, ?IH, ?E; reflexivity.
    + destruct (existsb (path_beq fq) S); rewrite ?gd_lookup_cons, ?Hb; apply IH.
Qed.

Lemma gd_mem_restrict : forall S d fp,
    gd_mem fp (gd_restrict S d) = existsb (path_beq fp) S && gd_mem fp d.
Proof. intros; rewrite !gd_mem_lookup, gd_lookup_restrict; destruct (existsb _ _); reflexivity. Qed.

Lemma gds_lookup_restrict_map : forall S Θ fp,
    gds_lookup (map (gd_restrict S) Θ) fp = if existsb (path_beq fp) S then gds_lookup Θ fp else None.
Proof.
  induction Θ as [| d Θ IH]; intros; cbn [map].
  - destruct (existsb _ _); reflexivity.
  - rewrite !gds_lookup_cons, gd_lookup_restrict, IH; destruct (existsb _ _); reflexivity.
Qed.

Lemma gds_level_restrict_map : forall S Θ fp,
    gds_level (map (gd_restrict S) Θ) fp = if existsb (path_beq fp) S then gds_level Θ fp else None.
Proof.
  induction Θ as [| d Θ IH]; intros; cbn [map].
  - destruct (existsb _ _); reflexivity.
  - rewrite !gds_level_cons, IH, gd_mem_restrict, length_map; destruct (existsb _ _); reflexivity.
Qed.

Lemma gds_lookup_trim : forall Θ fp, gds_lookup (trim_top Θ) fp = gds_lookup Θ fp.
Proof.
  induction Θ as [| [| e d] Θ IH]; intros; cbn [trim_top]; [ reflexivity | | reflexivity ].
  rewrite IH, gds_lookup_cons; reflexivity.
Qed.

Lemma gds_level_trim : forall Θ fp, gds_level (trim_top Θ) fp = gds_level Θ fp.
Proof.
  induction Θ as [| [| e d] Θ IH]; intros; cbn [trim_top]; [ reflexivity | | reflexivity ].
  rewrite IH, gds_level_cons; destruct (gds_level Θ fp); reflexivity.
Qed.

Lemma wf_trim : forall Θ, wf_gdeps Θ -> wf_gdeps (trim_top Θ).
Proof.
  induction Θ as [| [| e d] Θ IH]; intros H; cbn [trim_top]; [ exact H | | exact H ].
  inversion H; auto.
Qed.

Lemma top_ne_trim : forall Θ, top_ne (trim_top Θ).
Proof. induction Θ as [| [| e d] Θ IH]; cbn; [ exact I | exact IH | discriminate ]. Qed.

Lemma gds_lookup_restrict : forall S Θ fp,
    gds_lookup (gds_restrict S Θ) fp = if existsb (path_beq fp) S then gds_lookup Θ fp else None.
Proof. intros; unfold gds_restrict; rewrite gds_lookup_trim; apply gds_lookup_restrict_map. Qed.

Lemma gds_level_restrict : forall S Θ fp,
    gds_level (gds_restrict S Θ) fp = if existsb (path_beq fp) S then gds_level Θ fp else None.
Proof. intros; unfold gds_restrict; rewrite gds_level_trim; apply gds_level_restrict_map. Qed.

Corollary restrict_lookup_in : forall S Θ fp, In fp S -> gds_lookup (gds_restrict S Θ) fp = gds_lookup Θ fp.
Proof. intros * H; apply existsb_path_beq in H; rewrite gds_lookup_restrict, H; reflexivity. Qed.

Corollary restrict_lookup_out : forall S Θ fp, ~ In fp S -> gds_lookup (gds_restrict S Θ) fp = None.
Proof. intros * H; apply existsb_path_beq_false in H; rewrite gds_lookup_restrict, H; reflexivity. Qed.

Corollary restrict_level_in : forall S Θ fp, In fp S -> gds_level (gds_restrict S Θ) fp = gds_level Θ fp.
Proof. intros * H; apply existsb_path_beq in H; rewrite gds_level_restrict, H; reflexivity. Qed.

Corollary restrict_sub : forall S Θ, gds_restrict S Θ ⊑ Θ.
Proof. intros * fp U; rewrite gds_lookup_restrict; destruct (existsb _ _); [ auto | discriminate ]. Qed.

Lemma gd_keys_lookup : forall d fp, In fp (map fst d) <-> gd_lookup d fp <> None.
Proof.
  induction d as [| [fq V] d IH]; intros; cbn [map In fst]; rewrite ?gd_lookup_cons.
  - split; [ contradiction | intros H; apply H; reflexivity ].
  - destruct (path_beq fp fq) eqn:Hb.
    + apply path_beq_true in Hb as ->; split; [ discriminate | auto ].
    + rewrite <- IH; split; [| auto ].
      intros [-> | H]; [ rewrite path_beq_refl in Hb; discriminate | exact H ].
Qed.

Lemma gds_dom_lookup : forall Θ fp, In fp (gds_dom Θ) <-> gds_lookup Θ fp <> None.
Proof. intros; apply gd_keys_lookup. Qed.

Lemma gds_dom_none : forall Θ fp, ~ In fp (gds_dom Θ) <-> gds_lookup Θ fp = None.
Proof.
  intros; rewrite gds_dom_lookup; destruct (gds_lookup Θ fp); split; intros H;
    [ exfalso; apply H; discriminate | discriminate | reflexivity | intros H'; apply H'; reflexivity ].
Qed.

Lemma merge_none : forall Θ Θ' fp,
    gds_lookup (gds_merge Θ Θ') fp = None <-> gds_lookup Θ fp = None /\ gds_lookup Θ' fp = None.
Proof.
  intros; rewrite <- !gds_level_none, gds_level_merge.
  destruct (gds_level Θ fp), (gds_level Θ' fp); cbn; intuition discriminate.
Qed.

Lemma gds_merge_nil_l : forall Θ, gds_merge nil Θ = Θ.
Proof. intros; unfold gds_merge; cbn; apply rev_involutive. Qed.

Lemma gds_merge_nil_r : forall Θ, gds_merge Θ nil = Θ.
Proof. intros; unfold gds_merge; replace (merge_up (rev Θ) (rev nil)) with (rev Θ) by (destruct (rev Θ); reflexivity); apply rev_involutive. Qed.

Lemma top_ne_merge : forall Θ Θ', top_ne Θ -> top_ne Θ' -> top_ne (gds_merge Θ Θ').
Proof.
  intros [| d Θ] [| d' Θ'] H H'; rewrite ?gds_merge_nil_l, ?gds_merge_nil_r; try assumption.
  destruct (Nat.lt_trichotomy (List.length Θ) (List.length Θ')) as [Hlt | [Heq | Hgt]].
  - rewrite gds_merge_r by (cbn; lia); exact H'.
  - rewrite gds_merge_both by exact Heq; cbn in *; unfold gd_union.
    destruct d; [ contradiction | discriminate ].
  - rewrite gds_merge_l by (cbn; lia); exact H.
Qed.

(** Two well-formed [gdeps] with a unit on top and the same levels have the same
    height: the height is one above the top unit's level. *)
Lemma equiv_length : forall Θ Θ',
    wf_gdeps Θ -> wf_gdeps Θ' -> top_ne Θ -> top_ne Θ' ->
    (forall fp, gds_level Θ fp = gds_level Θ' fp) ->
    List.length Θ = List.length Θ'.
Proof.
  assert (H : forall Θ Θ', wf_gdeps Θ -> top_ne Θ -> (forall fp, gds_level Θ fp = gds_level Θ' fp) ->
                     List.length Θ <= List.length Θ').
  { intros [| [| [fp U] d] Θ] Θ' Hwf Hne Hl; cbn [List.length top_ne] in *; [ lia | contradiction |].
    destruct (wf_top _ _ _ _ Hwf (or_introl eq_refl)) as (_ & Hlv & _).
    rewrite Hl in Hlv; apply gds_level_lt in Hlv; lia. }
  intros * Hwf Hwf' Hne Hne' Hl; apply Nat.le_antisymm; apply H; auto.
Qed.

Lemma gds_equiv_refl : forall Θ, gds_equiv Θ Θ.
Proof. intros; split; [| split ]; auto using gds_sub_refl. Qed.

Lemma gds_equiv_sym : forall Θ Θ', gds_equiv Θ Θ' -> gds_equiv Θ' Θ.
Proof. intros * (H1 & H2 & H3); split; [| split ]; auto. Qed.

Lemma gds_equiv_trans : forall Θ1 Θ2 Θ3, gds_equiv Θ1 Θ2 -> gds_equiv Θ2 Θ3 -> gds_equiv Θ1 Θ3.
Proof.
  intros * (H1 & H2 & H3) (H4 & H5 & H6); split; [| split ]; eauto using gds_sub_trans.
  intros; rewrite H3; auto.
Qed.

(** Term judgments and [⊢g] only read lookups, so they cross [gds_equiv] both
    ways by weakening alone. *)
Lemma equiv_gctx : forall Θ Θ' Ξ, gds_equiv Θ Θ' -> wf_gdeps Θ' -> ⊢g Θ ⍮ Ξ -> ⊢g Θ' ⍮ Ξ.
Proof.
  intros * (H & H' & _) HΘ' HΞ; apply (gstack_levels_grow _ _ H _ HΞ HΘ').
  intros mp U Hin; pose proof (wf_gstack_frames _ _ (wf_gctx_stack _ _ HΞ) _ _ Hin) as Hn.
  destruct (gds_lookup Θ' (p_unit mp)) eqn:E; [ rewrite (H' _ _ E) in Hn; discriminate | reflexivity ].
Qed.

Lemma equiv_exp : forall Θ Θ' Ξ Γ M A,
    gds_equiv Θ Θ' -> ⊢g Θ' ⍮ Ξ -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ' ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * (H & _ & _) HΞ HM; apply (levels_grow _ _ _ H); [ constructor; exact HΞ | exact HM ].
Qed.

Lemma equiv_ctx : forall Θ Θ' Ξ Γ,
    gds_equiv Θ Θ' -> ⊢g Θ' ⍮ Ξ -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ' ⍮ Ξ ⍮ Γ.
Proof.
  intros * (H & _ & _) HΞ HΓ; apply (levels_grow _ _ _ H); [ constructor; exact HΞ | exact HΓ ].
Qed.

(** ** The Restriction is Well Formed

    Without strengthening: a unit of the restriction was checked against its
    own closure, which the levels of the restriction below it extend, as the
    closure is imported too and sits below the unit ([unit_levels_grow]). *)

(** Everything a unit of [S] was checked against is in [S], filed as it is in
    [Θ], at its level in [Θ]. *)
Definition closure_ok (S : list fpath) (Θ : gdeps) : Prop :=
  forall fp U, In fp S -> gds_lookup Θ fp = Some U ->
    exists ΘU, ΘU ⍮ nil ⍮ p_abs fp nil ⊢u U /\ gds_level Θ fp = Some (List.length ΘU) /\
      forall x V, gds_lookup ΘU x = Some V ->
        In x S /\ gds_lookup Θ x = Some V /\ gds_level Θ x = gds_level ΘU x.

Lemma below_top : forall d Θ x V k,
    wf_gdeps (d :: Θ) -> gds_lookup (d :: Θ) x = Some V -> gds_level (d :: Θ) x = Some k ->
    k < List.length Θ -> gds_lookup Θ x = Some V /\ gds_level Θ x = Some k.
Proof.
  intros * Hwf HV Hk Hlt.
  assert (HΘ : gds_level Θ x = Some k).
  { rewrite gds_level_cons in Hk; destruct (gds_level Θ x); [ exact Hk |].
    destruct (gd_mem x d); [ injection Hk as <-; lia | discriminate ]. }
  destruct (gds_level_some _ _ _ HΘ) as [V' HV'].
  destruct (wf_below _ _ _ _ Hwf HV') as [HV'' _]; rewrite HV in HV''; injection HV'' as ->.
  split; assumption.
Qed.

Lemma closure_ok_pop : forall S d Θ, wf_gdeps (d :: Θ) -> closure_ok S (d :: Θ) -> closure_ok S Θ.
Proof.
  intros * Hwf Hc fp U Hin HU.
  destruct (wf_below _ _ _ _ Hwf HU) as [HU' Hlv].
  destruct (Hc _ _ Hin HU') as (ΘU & HwU & Hl & Hx).
  rewrite Hlv in Hl; pose proof (gds_level_lt _ _ _ Hl) as Hlt.
  exists ΘU; split; [ exact HwU | split; [ exact Hl |] ].
  intros x V HV; destruct (Hx _ _ HV) as (HxS & HxV & HxL).
  destruct (gds_level_lookup _ _ _ HV) as [k Hk]; pose proof (gds_level_lt _ _ _ Hk).
  rewrite Hk in HxL; destruct (below_top _ _ _ _ _ Hwf HxV HxL ltac:(lia)) as [HV' HΘx].
  split; [ exact HxS | split; [ exact HV' | rewrite HΘx, Hk; reflexivity ] ].
Qed.

Lemma nodup_keys_filter : forall (p : fpath * gunit -> bool) d,
    NoDup (map fst d) -> NoDup (map fst (filter p d)).
Proof.
  induction d as [| e d IH]; intros H; cbn [filter]; [ constructor |].
  inversion H as [| ? ? Hn Hd]; subst; destruct (p e); cbn [map]; [| auto ].
  constructor; [| auto ].
  intros Hin; apply Hn; apply in_map_iff in Hin as (e' & <- & Hin); apply filter_In in Hin as [Hin _].
  apply in_map; exact Hin.
Qed.

Lemma restrict_map_wf : forall S Θ, wf_gdeps Θ -> closure_ok S Θ -> wf_gdeps (map (gd_restrict S) Θ).
Proof.
  intros S; induction Θ as [| d Θ IH]; intros Hwf Hc; [ constructor |].
  pose proof Hwf as Hwf0; inversion Hwf0 as [| ? ? HΘ Hd]; subst.
  assert (HM : wf_gdeps (map (gd_restrict S) Θ)) by (apply IH; [ exact HΘ | eapply closure_ok_pop; eassumption ]).
  cbn [map]; constructor; [ exact HM |].
  apply wf_gdep_iff in Hd as (_ & Hnd & Hu); apply wf_gdep_iff; split; [ exact HM | split ].
  - apply nodup_keys_filter, Hnd.
  - intros fp U Hin; apply filter_In in Hin as [Hin Hb]; cbn [fst] in Hb; apply existsb_path_beq in Hb.
    destruct (wf_top _ _ _ _ Hwf Hin) as (HU & Hlv & Hn).
    destruct (Hc _ _ Hb HU) as (ΘU & HwU & Hl & Hx).
    rewrite Hlv in Hl; injection Hl as Hlen.
    assert (Hn' : gds_lookup (map (gd_restrict S) Θ) fp = None)
      by (rewrite gds_lookup_restrict_map; destruct (existsb _ _); [ exact Hn | reflexivity ]).
    split.
    + eapply unit_levels_grow; [| exact HM | exact Hn' | exact HwU ].
      intros x V HV; destruct (Hx _ _ HV) as (HxS & HxV & HxL).
      destruct (gds_level_lookup _ _ _ HV) as [k Hk]; pose proof (gds_level_lt _ _ _ Hk).
      rewrite Hk in HxL; destruct (below_top _ _ _ _ _ Hwf HxV HxL ltac:(lia)) as [HV' _].
      rewrite gds_lookup_restrict_map; apply existsb_path_beq in HxS; rewrite HxS; exact HV'.
    + apply gds_fresh_iff; exact Hn'.
Qed.

Theorem restrict_wf : forall S Θ, wf_gdeps Θ -> closure_ok S Θ -> wf_gdeps (gds_restrict S Θ).
Proof. intros; apply wf_trim, restrict_map_wf; assumption. Qed.

(** ** Chains, Stacks and Heights of Runs *)

Section Runs.
  Variables (load_path : fpath -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  #[local] Notation run_cmd := (run_cmd load_path read to_core).
  #[local] Notation run_cmds := (run_cmds load_path read to_core).
  #[local] Notation run_unit := (run_unit load_path read to_core).
  #[local] Notation canon := (canon load_path read to_core).

  Lemma run_dom_mono :
    (forall ch Θ Ξ c Θ' Ξ', run_cmd ch Θ Ξ c Θ' Ξ' ->
       forall x, gds_lookup Θ x <> None -> gds_lookup Θ' x <> None) /\
    (forall ch Θ Ξ cs Θ' Ξ', run_cmds ch Θ Ξ cs Θ' Ξ' ->
       forall x, gds_lookup Θ x <> None -> gds_lookup Θ' x <> None) /\
    (forall ch u Θ U, run_unit ch u Θ U -> True).
  Proof.
    apply run_mut_ind; intros; auto.
    intros E; apply merge_none in E as [E _]; contradiction.
  Qed.

  (** The chain only decides whether a load is a cycle, so a run stands under
      any chain avoiding every unit it filed: what justifies sharing a unit
      loaded under one chain with an import under another. *)
  Lemma run_chain_irrel :
    (forall ch Θ Ξ c Θ' Ξ', run_cmd ch Θ Ξ c Θ' Ξ' ->
       forall ch', (forall x, In x ch' -> gds_lookup Θ' x = None) -> run_cmd ch' Θ Ξ c Θ' Ξ') /\
    (forall ch Θ Ξ cs Θ' Ξ', run_cmds ch Θ Ξ cs Θ' Ξ' ->
       forall ch', (forall x, In x ch' -> gds_lookup Θ' x = None) -> run_cmds ch' Θ Ξ cs Θ' Ξ') /\
    (forall ch u Θ U, run_unit ch u Θ U ->
       forall ch', (forall x, In x (hd nil ch :: ch') -> gds_lookup Θ x = None) -> run_unit (hd nil ch :: ch') u Θ U).
  Proof.
    (* what a run filed before its last step it still has after it *)
    assert (Hpre : forall ch Θ Ξ cs Θ1 Ξ1 ch', run_cmds ch Θ Ξ cs Θ1 Ξ1 ->
              (forall x, In x ch' -> gds_lookup Θ1 x = None) ->
              forall x, In x ch' -> gds_lookup Θ x = None).
    { intros * Hr Hch x Hx; destruct (gds_lookup Θ x) eqn:E; [ exfalso | reflexivity ].
      eapply (proj1 (proj2 run_dom_mono)); [ exact Hr | rewrite E; discriminate | apply Hch, Hx ]. }
    apply run_mut_dind; intros.
    - constructor; assumption.
    - econstructor; eauto.
    - eapply rc_import_filed; eassumption.
    - rename r into Hu, H into IH, H0 into Hch.
      eapply rc_import_load; try eassumption.
      + intros Hin; specialize (Hch _ Hin); apply merge_none in Hch as [_ Hf].
        rewrite file_lookup, path_beq_refl in Hf; discriminate.
      + apply IH; intros x [<- | Hin].
        * exact (proj2 (proj2 (run_chain_fresh load_path read to_core)) _ _ _ _ Hu _ (or_introl eq_refl)).
        * specialize (Hch _ Hin); apply merge_none in Hch as [_ Hf].
          rewrite file_lookup in Hf; destruct (path_beq x fp); [ discriminate | exact Hf ].
    - apply rc_eval_check; assumption.
    - eapply rc_eval_infer; eassumption.
    - constructor.
    - econstructor; [ apply H; eapply Hpre; eassumption | auto ].
    - cbn [hd] in *; econstructor; [ apply H; eapply Hpre; eassumption | assumption | auto ].
  Qed.

  Lemma run_tl :
    (forall ch Θ Ξ c Θ' Ξ', run_cmd ch Θ Ξ c Θ' Ξ' -> tl Ξ' = tl Ξ /\ List.length Ξ' = List.length Ξ) /\
    (forall ch Θ Ξ cs Θ' Ξ', run_cmds ch Θ Ξ cs Θ' Ξ' -> tl Ξ' = tl Ξ /\ List.length Ξ' = List.length Ξ) /\
    (forall ch u Θ U, run_unit ch u Θ U -> True).
  Proof.
    assert (Hadd : forall x E Ξ, tl (gs_add x E Ξ) = tl Ξ /\ List.length (gs_add x E Ξ) = List.length Ξ)
      by (intros ? ? [| [? ?] ?]; split; reflexivity).
    apply run_mut_ind; intros; auto; intuition congruence.
  Qed.

  (** Commands keep the stack below the frame they run in, and an empty stack
      empty. *)
  Corollary run_cmds_tail : forall ch Θ F Ξ cs Θ' Ξ',
      run_cmds ch Θ (F :: Ξ) cs Θ' Ξ' -> exists F', Ξ' = F' :: Ξ.
  Proof.
    intros * H; destruct (proj1 (proj2 run_tl) _ _ _ _ _ _ H) as [Ht Hl].
    destruct Ξ' as [| F' Ξ']; cbn in *; [ discriminate | subst; eauto ].
  Qed.

  Corollary run_cmds_empty : forall ch Θ cs Θ' Ξ', run_cmds ch Θ nil cs Θ' Ξ' -> Ξ' = nil.
  Proof.
    intros * H; destruct (proj1 (proj2 run_tl) _ _ _ _ _ _ H) as [_ Hl].
    destruct Ξ'; [ reflexivity | discriminate ].
  Qed.

  Lemma run_top_ne :
    (forall ch Θ Ξ c Θ' Ξ', run_cmd ch Θ Ξ c Θ' Ξ' -> top_ne Θ -> top_ne Θ') /\
    (forall ch Θ Ξ cs Θ' Ξ', run_cmds ch Θ Ξ cs Θ' Ξ' -> top_ne Θ -> top_ne Θ') /\
    (forall ch u Θ U, run_unit ch u Θ U -> top_ne Θ).
  Proof.
    apply run_mut_ind; intros; auto.
    - apply top_ne_merge; [ assumption | discriminate ].
    - match goal with IH : top_ne nil -> _ |- _ => specialize (IH I) end; auto.
  Qed.

  (** A judgment state below a canonical [Θ], with domain [S], is equivalent
      to the restriction of [Θ] to [S]: the two directions of [⊑] are the
      domain, the levels canonicity. *)
  Lemma equiv_restrict : forall ΘA Θ S,
      canon ΘA -> canon Θ -> ΘA ⊑ Θ -> (forall x, In x S <-> In x (gds_dom ΘA)) ->
      gds_equiv ΘA (gds_restrict S Θ).
  Proof.
    intros * HcA Hc Hsub Hdom; pose proof (canon_agree _ _ _ _ _ HcA Hc) as Hag; split; [| split ].
    - intros x V HV; rewrite restrict_lookup_in; [ auto |].
      apply Hdom, gds_dom_lookup; rewrite HV; discriminate.
    - intros x V HV; rewrite gds_lookup_restrict in HV.
      destruct (existsb (path_beq x) S) eqn:Hb; [| discriminate ]; apply existsb_path_beq, Hdom, gds_dom_lookup in Hb.
      destruct (gds_lookup ΘA x) as [V' |] eqn:E; [| contradiction ].
      rewrite (Hsub _ _ E) in HV; injection HV as ->; reflexivity.
    - intros x; rewrite gds_level_restrict; destruct (existsb (path_beq x) S) eqn:Hb.
      + apply existsb_path_beq, Hdom, gds_dom_lookup in Hb.
        destruct (gds_lookup ΘA x) as [V' |] eqn:E; [| contradiction ].
        exact (proj2 (Hag _ _ _ E (Hsub _ _ E))).
      + apply existsb_path_beq_false in Hb; rewrite Hdom, gds_dom_none, <- gds_level_none in Hb; exact Hb.
  Qed.

  (** [restrict_wf] for a canonical [Θ] and an [S] closed under the canonical
      closures, each filed in [Θ]. *)
  Corollary restrict_wf_canon : forall S Θ,
      wf_gdeps Θ -> canon Θ ->
      (forall fp U, In fp S -> gds_lookup Θ fp = Some U ->
         forall src prg u ch ΘU, load_path fp = Some src -> read src = Some prg -> to_core prg = Some u ->
           run_unit (fp :: ch) u ΘU U -> ΘU ⊑ Θ /\ forall x, In x (gds_dom ΘU) -> In x S) ->
      wf_gdeps (gds_restrict S Θ).
  Proof.
    intros * Hwf Hc Hcl; apply restrict_wf; [ exact Hwf |]; intros fp U Hin HU.
    destruct (Hc _ _ HU) as (src & prg & u & ch & ΘU & Hl & Hr & Ht & Hu & Hlv).
    destruct (Hcl _ _ Hin HU _ _ _ _ _ Hl Hr Ht Hu) as [Hsub Hdom].
    destruct (proj2 (proj2 (run_wf load_path read to_core)) _ _ _ _ Hu) as (_ & HcU & HwU).
    pose proof (canon_agree _ _ _ _ _ HcU Hc) as Hag.
    exists ΘU; split; [ exact HwU | split; [ exact Hlv |] ].
    intros x V HV; split; [ apply Hdom, gds_dom_lookup; rewrite HV; discriminate |].
    split; [ apply Hsub, HV | symmetry; exact (proj2 (Hag _ _ _ HV (Hsub _ _ HV))) ].
  Qed.
End Runs.
