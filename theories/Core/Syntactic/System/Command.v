(** * The Static Semantics of Commands

    A command moves the global state: the filed units [Θ] and the stack [Ξ] of
    open frames.  [cc_load] loads the unit it names, if it is not filed yet,
    by running that unit's own commands from nothing, and merges the units
    that run filed into [Θ]; the chain of units whose loading is in progress
    is what rules a cycle out.  [cc_open] declares the names its items
    generate ([Imports]) as definitions and aliases of the frame.  Every
    command is expanded before it runs, which turns the local opens of the
    bodies it contains into entries.

    Resolution is lexical — a unit is named by its full path, and an import
    lists the names it binds — so elaborating a unit needs none of the units
    it imports, which are only loaded while it runs. *)

From Stdlib Require Import List String PeanoNat Bool.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Command Imports.
From Mctt.Core.Syntactic.System Require Import Definitions Lemmas Structural GlobalPresup.
From Mctt.Core.Syntactic.System Require Export Privacy.
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

Definition gs_path (Ξ : gstack) : qname :=
  match Ξ with
  | (mp, _) :: _ => mp
  | nil => q_abs nil nil
  end.

Definition gs_push (mp : qname) (Δ : ctx) (Ξ : gstack) : gstack := (mp, gu_body Δ ⋄) :: Ξ.

Definition gs_add (x : string) (E : gentry) (Ξ : gstack) : gstack :=
  match Ξ with
  | (mp, U) :: Ξ' => (mp, gu_body (gu_params U) (gu_mod U ⊳ x ↦ E)) :: Ξ'
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

(** ** Imports

    The definitions and aliases an import generates ([Imports]), declared in
    the frame in order, with the premises of [rc_def] and [rc_alias]: what
    the import references is checked once, as written ([rcs_cons]), and a
    generated type is not written, so nothing here checks privacy. *)

Inductive gens_run (Θ : gdeps) : gstack -> list igen -> gstack -> Prop :=
| gr_nil : forall Ξ, gens_run Θ Ξ nil Ξ
| gr_def : forall Ξ d pv A M gs Ξ',
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A -> gs_fresh d Ξ ->
    gens_run Θ (gs_add d (gs_def true pv Ξ A M) Ξ) gs Ξ' ->
    gens_run Θ Ξ (ig_def d pv A M :: gs) Ξ'
| gr_alias : forall Ξ d pv E gs Ξ',
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E -> gs_fresh d Ξ ->
    gens_run Θ (gs_add d (ge_mod pv (gu_mk (gs_tele Ξ) (md_alias E))) Ξ) gs Ξ' ->
    gens_run Θ Ξ (ig_alias d pv E :: gs) Ξ'.

(** ** Merging Filed Units

    A loaded unit runs from nothing, so what its run filed is merged into the
    importer's units: the ones not filed yet are added on top, in their order.
    A path filed on both sides was loaded by two runs of the same file, so it
    is the same unit ([canon_agree]). *)

Definition gds_mem (fp : path) (Θ : gdeps) : bool :=
  match gds_lookup Θ fp with Some _ => true | None => false end.

Definition gds_merge (Θ Θ' : gdeps) : gdeps :=
  filter (fun e => negb (gds_mem (fst e) Θ)) Θ' ++ Θ.

Definition gds_agree (Θ Θ' : gdeps) : Prop :=
  forall fp U U', gds_lookup Θ fp = Some U -> gds_lookup Θ' fp = Some U' -> U = U'.

(** ** Privacy

    Every command checks the terms it introduces for access to private
    members ([acc_ok], in [Privacy]); typing does not. *)

Section Semantics.
  (** File IO: the contents of the unit at a path, if there is one. *)
  Variable load_path : path -> option string.
  (** Lexing and parsing.  The lexer is OCaml, so this is a parameter too. *)
  Variable read : string -> option Cst.prog.
  (** Elaboration into core commands, which needs no filed unit. *)
  Variable to_core : Cst.prog -> option cunit.

  (** ** Running

      [Θ ⍮ Ξ ⊢[ch] c ⇝ Θ' ⍮ Ξ']: [ch] is the chain of units being loaded, the
      one running [c] first.  Only [rc_load] changes [Θ]; the premises
      of [rc_def], [rc_mod] and [rc_alias] are those of [wf_gmod_ext],
      [wf_gmod_nil] and [wf_gentry_alias].  Privacy is checked by
      [rcs_cons], on the command as written. *)

  Inductive run_cmd : list path -> gdeps -> gstack -> ccmd -> gdeps -> gstack -> Prop :=
  | rc_def : forall ch Θ Ξ x b pv A M,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
      gs_fresh x Ξ ->
      Θ ⍮ Ξ ⊢[ch] cc_def x b pv A M ⇝ Θ ⍮ gs_add x (gs_def b pv Ξ A M) Ξ
  (** The body ends on the frame it opened, the stack below as it was; that
      frame becomes the member [x] of the one below, as it is. *)
  | rc_mod : forall ch Θ Ξ x pv Δ cs Θ' mp U,
      tele_ass Δ ->
      ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
      gs_fresh x Ξ ->
      Θ ⍮ gs_push (qname_in (gs_path Ξ) x) Δ Ξ ⊢[ch] cs ⇝* Θ' ⍮ (mp, U) :: Ξ ->
      Θ ⍮ Ξ ⊢[ch] cc_mod x pv Δ cs ⇝ Θ' ⍮ gs_add x (ge_body pv Δ (gu_mod U)) Ξ
  (** An alias is filed with the frames' parameters it is declared under. *)
  | rc_alias : forall ch Θ Ξ x pv Δ E,
      tele_ass Δ ->
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ ->
      Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
      gs_fresh x Ξ ->
      Θ ⍮ Ξ ⊢[ch] cc_alias x pv Δ E ⇝ Θ ⍮ gs_add x (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))) Ξ
  (** A unit filed already, by an earlier load in any unit: shared, not
      reloaded. *)
  | rc_load_filed : forall ch Θ Ξ fp U,
      gds_lookup Θ fp = Some U ->
      Θ ⍮ Ξ ⊢[ch] cc_load fp ⇝ Θ ⍮ Ξ
  (** Not filed: load it, run it from nothing with itself added to the chain,
      file it on top of what it filed, and merge that in.  A unit already in the
      chain is still being loaded, so loading it is a cycle, and no rule
      applies. *)
  | rc_load : forall ch Θ Ξ fp src prg u ΘU U,
      gds_lookup Θ fp = None ->
      ~ In fp ch ->
      load_path fp = Some src ->
      read src = Some prg ->
      prog_path prg = fp ->
      to_core prg = Some u ->
      run_unit (fp :: ch) u ΘU U ->
      Θ ⍮ Ξ ⊢[ch] cc_load fp ⇝ gds_merge Θ ((fp, U) :: ΘU) ⍮ Ξ
  (** An open checks that its target is a module, and declares the
      definitions and aliases its items generate in this frame. *)
  | rc_open : forall ch Θ Ξ E its gs Ξ',
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
      import_gen_ok Θ Ξ (gs_tele Ξ) E its gs ->
      gens_run Θ Ξ gs Ξ' ->
      Θ ⍮ Ξ ⊢[ch] cc_open E its ⇝ Θ ⍮ Ξ'
  (** An [eval] changes nothing, but must type-check where it stands. *)
  | rc_eval_check : forall ch Θ Ξ M A,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
      Θ ⍮ Ξ ⊢[ch] cc_eval M (Some A) ⇝ Θ ⍮ Ξ
  | rc_eval_infer : forall ch Θ Ξ M A,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
      Θ ⍮ Ξ ⊢[ch] cc_eval M None ⇝ Θ ⍮ Ξ
  where "Θ ⍮ Ξ ⊢[ ch ] c ⇝ Θ' ⍮ Ξ'" := (run_cmd ch Θ Ξ c Θ' Ξ')

  with run_cmds : list path -> gdeps -> gstack -> list ccmd -> gdeps -> gstack -> Prop :=
  | rcs_nil : forall ch Θ Ξ, Θ ⍮ Ξ ⊢[ch] nil ⇝* Θ ⍮ Ξ
  (** Each command is checked for privacy as written, then expanded
      ([Imports]) before it runs. *)
  | rcs_cons : forall ch Θ Ξ c c' cs Θ1 Ξ1 Θ2 Ξ2,
      acc_ok Θ Ξ (cmd_refs c) ->
      cmd_xp_ok Θ Ξ c c' ->
      Θ ⍮ Ξ ⊢[ch] c' ⇝ Θ1 ⍮ Ξ1 ->
      Θ1 ⍮ Ξ1 ⊢[ch] cs ⇝* Θ2 ⍮ Ξ2 ->
      Θ ⍮ Ξ ⊢[ch] c :: cs ⇝* Θ2 ⍮ Ξ2
  where "Θ ⍮ Ξ ⊢[ ch ] cs ⇝* Θ' ⍮ Ξ'" := (run_cmds ch Θ Ξ cs Θ' Ξ')

  (** [run_unit (fp :: ch) u Θ U]: the unit [fp], at the head of the chain,
      runs from nothing filed.  Its leading loads run on the empty stack,
      then its parameters are expanded and checked against what they filed,
      then its body runs in its own frame, named [fp]; [Θ] is what it filed,
      [U] the unit. *)
  with run_unit : list path -> cunit -> gdeps -> gunit -> Prop :=
  | ru_intro : forall fp ch imps P P' cs Θ1 Θ2 mp U,
      nil ⍮ nil ⊢[fp :: ch] imps ⇝* Θ1 ⍮ nil ->
      tele_xp_ok Θ1 nil nil P P' ->
      tele_ass P' ->
      ⊢ Θ1 ⍮ nil ⍮ P' ->
      acc_ok Θ1 nil (tele_refs nil P) ->
      Θ1 ⍮ gs_push (q_abs fp nil) P' nil ⊢[fp :: ch] cs ⇝* Θ2 ⍮ (mp, U) :: nil ->
      run_unit (fp :: ch) (imps, P, cs) Θ2 U.

  (** The unit given on the command line: run like an imported one, with
      itself as the whole chain. *)
  Definition prog_sem (prg : Cst.prog) (Θ : gdeps) (U : gunit) : Prop :=
    exists u, to_core prg = Some u /\ run_unit (prog_path prg :: nil) u Θ U.
End Semantics.


(** ** A Cycle Has No Meaning *)

Lemma load_acyclic : forall load_path read to_core ch Θ Ξ fp Θ' Ξ',
    In fp ch ->
    gds_lookup Θ fp = None ->
    ~ run_cmd load_path read to_core ch Θ Ξ (cc_load fp) Θ' Ξ'.
Proof.
  intros * Hin Hnone Hr; inversion Hr; subst; [ congruence | contradiction ].
Qed.

(** ** Running is Deterministic

    Every rule is a check, never a choice, and [load_path], [read] and [to_core]
    are functions; the chain only decides whether a run succeeds.  This is what
    makes a path filed by two runs the same unit, so the merge loses
    nothing. *)

Lemma gens_run_functional : forall Θ Ξ gs Ξ1, gens_run Θ Ξ gs Ξ1 -> forall Ξ2, gens_run Θ Ξ gs Ξ2 -> Ξ1 = Ξ2.
Proof. induction 1; intros * H2; inversion H2; subst; auto. Qed.

Scheme run_cmd_mind := Minimality for run_cmd Sort Prop
with run_cmds_mind := Minimality for run_cmds Sort Prop
with run_unit_mind := Minimality for run_unit Sort Prop.
Combined Scheme run_mut_ind from run_cmd_mind, run_cmds_mind, run_unit_mind.

Section Determinism.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  #[local] Abbreviation run_cmd := (run_cmd load_path read to_core).
  #[local] Abbreviation run_cmds := (run_cmds load_path read to_core).
  #[local] Abbreviation run_unit := (run_unit load_path read to_core).

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
    (* the second derivation is the last hypothesis; expansions and
       generations are unique *)
    apply run_mut_ind; intros; lazymatch goal with H2 : _ |- _ => inversion H2; subst end;
      try congruence; try (split; reflexivity).
    all: repeat match goal with
      | H1 : cmd_xp_ok ?a ?b ?c ?c1, H2 : cmd_xp_ok ?a ?b ?c ?c2 |- _ =>
          assert_fails constr_eq c1 c2; pose proof (cmd_xp_ok_functional _ _ _ _ _ H1 H2); subst c2
      | H1 : tele_xp_ok ?a ?b ?S ?c ?c1, H2 : tele_xp_ok ?a ?b ?S ?c ?c2 |- _ =>
          assert_fails constr_eq c1 c2; pose proof (tele_xp_ok_functional _ _ _ _ _ _ H1 H2); subst c2
      | H1 : import_gen_ok ?a ?b ?G ?E ?is ?g1, H2 : import_gen_ok ?a ?b ?G ?E ?is ?g2 |- _ =>
          assert_fails constr_eq g1 g2; pose proof (import_gen_ok_functional _ _ _ _ _ _ _ H1 H2); subst g2
      end.
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
    - (* an import: its generated commands *)
      match goal with
      | H1 : gens_run _ _ ?gs _, H2 : gens_run _ _ ?gs _ |- _ =>
          rewrite (gens_run_functional _ _ _ _ H1 _ H2)
      end; split; reflexivity.
    - (* a sequence: its head, then its tail from the same state *)
      match goal with
      | IH1 : forall _ _ _, run_cmd _ _ _ ?c _ _ -> _, H1 : run_cmd _ _ _ ?c _ _ |- _ =>
          destruct (IH1 _ _ _ H1); subst
      end; eauto.
    - (* a unit: its loads, then its body from what they filed *)
      cbn [hd] in *; subst.
      match goal with
      | IH1 : forall _ _ _, run_cmds _ nil nil ?is _ _ -> _, H1 : run_cmds _ nil nil ?is _ _ |- _ =>
          destruct (IH1 _ _ _ H1); subst
      end.
      repeat match goal with
      | H1 : tele_xp_ok ?a ?b ?S ?c ?c1, H2 : tele_xp_ok ?a ?b ?S ?c ?c2 |- _ =>
          assert_fails constr_eq c1 c2; pose proof (tele_xp_ok_functional _ _ _ _ _ _ H1 H2); subst c2
      end.
      match goal with
      | IH2 : forall _ _ _, run_cmds _ ?T (gs_push ?mp ?P nil) ?cs _ _ -> _,
        H2 : run_cmds _ ?T (gs_push ?mp ?P nil) ?cs _ _ |- _ =>
          destruct (IH2 _ _ _ H2) as [? Heq]; injection Heq; intros; subst
      end; split; reflexivity.
  Qed.
End Determinism.

(** ** Merging Keeps Both Sides *)

Lemma gds_lookup_merge : forall Θ Θ' fp,
    gds_lookup (gds_merge Θ Θ') fp = match gds_lookup Θ fp with Some U => Some U | None => gds_lookup Θ' fp end.
Proof.
  intros Θ Θ' fp; unfold gds_merge; induction Θ' as [| [fq V] Θ' IH]; cbn [filter List.app].
  - destruct (gds_lookup Θ fp); reflexivity.
  - unfold gds_mem at 1; cbn [fst]; destruct (gds_lookup Θ fq) eqn:Hq; cbn [negb]; rewrite ?IH.
    + cbn [gds_lookup]; destruct (gds_lookup Θ fp) eqn:Hp; [ reflexivity |].
      destruct (path_beq fp fq) eqn:Hb; [ apply path_beq_true in Hb; congruence | reflexivity ].
    + cbn [gds_lookup List.app]; rewrite IH.
      destruct (path_beq fp fq) eqn:Hb; [| reflexivity ].
      apply path_beq_true in Hb; subst; rewrite Hq; reflexivity.
Qed.

Lemma merge_cons : forall Θ fp U Θ',
    gds_merge Θ ((fp, U) :: Θ') = if gds_mem fp Θ then gds_merge Θ Θ' else (fp, U) :: gds_merge Θ Θ'.
Proof. intros; unfold gds_merge; cbn; destruct (gds_mem fp Θ); reflexivity. Qed.

Lemma merge_inv : forall Θ Θ' fp U,
    gds_lookup (gds_merge Θ Θ') fp = Some U ->
    gds_lookup Θ fp = Some U \/ gds_lookup Θ' fp = Some U.
Proof. intros * H; rewrite gds_lookup_merge in H; destruct (gds_lookup Θ fp); auto. Qed.

Lemma merge_none : forall Θ Θ' fp,
    gds_lookup (gds_merge Θ Θ') fp = None <-> gds_lookup Θ fp = None /\ gds_lookup Θ' fp = None.
Proof. intros; rewrite gds_lookup_merge; destruct (gds_lookup Θ fp); intuition discriminate. Qed.

Lemma merge_left : forall Θ Θ', Θ ⊑ gds_merge Θ Θ'.
Proof. intros * fp U HU; rewrite gds_lookup_merge, HU; reflexivity. Qed.

Lemma merge_right : forall Θ Θ', gds_agree Θ Θ' -> Θ' ⊑ gds_merge Θ Θ'.
Proof.
  intros * Hag fp U HU; rewrite gds_lookup_merge.
  destruct (gds_lookup Θ fp) eqn:E; [ f_equal; eapply Hag; eassumption | exact HU ].
Qed.

(** ** Filing More Units Keeps an Open Stack Well Formed

    Each entry of each frame was checked against the units filed when the frame
    was open; resolution only grows along [Θ ⊑ Θ'] ([gc_sub_deps]), so its
    typing moves along an embedding.  A frame names its own unit, which must
    stay unfiled: that is the only thing [Θ'] has to grant. *)

Lemma deps_grow : forall Θ Θ' Ξ,
    Θ ⊑ Θ' -> ⊢ Θ' ⍮ Ξ ⍮ ⋅ ->
    (forall Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ' ⍮ Ξ ⍮ Γ) /\
    (forall Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ' ⍮ Ξ ⍮ Γ ⊢ M : A) /\
    (forall Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Θ' ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A) /\
    (forall Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ' ⍮ Ξ ⍮ Γ ⊢ A ⊆ A') /\
    (forall Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ' ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ') /\
    (forall Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ' ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U') /\
    (forall Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ' ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H').
Proof.
  intros * Hs Hb; apply emb_preserves_wf; constructor;
    [ eapply ctx_wf_gctx; exact Hb | apply gc_sub_deps; exact Hs ].
Qed.

Lemma frame_fresh_grow : forall Θ Θ' Ξ mp,
    frame_fresh Θ Ξ mp -> gds_lookup Θ' (q_unit mp) = None -> frame_fresh Θ' Ξ mp.
Proof. intros * H Hn; destruct Ξ as [| [mq V] Ξ]; cbn in *; [ split; [ exact Hn | exact (proj2 H) ] | exact H ]. Qed.

Section GrowDeps.
  Variables (Θ Θ' : gdeps).
  Hypothesis Hsub : Θ ⊑ Θ'.

  Lemma global_deps_grow :
    (forall Θ0 Ξ mp E, Θ0 ⍮ Ξ ⍮ mp ⊢e E -> Θ0 = Θ -> ⊢g Θ' ⍮ Ξ ->
       gds_lookup Θ' (q_unit mp) = None -> Θ' ⍮ Ξ ⍮ mp ⊢e E) /\
    (forall Θ0 Ξ mp Δ Φ, Θ0 ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ -> Θ0 = Θ -> ⊢g Θ' ⍮ Ξ ->
       gds_lookup Θ' (q_unit mp) = None -> Θ' ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ).
  Proof.
    apply global_wf_mut_ind; intros; subst.
    all: try assert (Hb : ⊢ Θ' ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    all: try pose proof (deps_grow _ _ _ Hsub Hb) as (Hc & He & _ & _ & Hx & _ & Hm).
    - econstructor; apply He; eassumption.
    - econstructor; apply He; eassumption.
    - econstructor; auto.
    - econstructor; [ assumption | apply Hx; assumption | apply Hm; assumption ].
    - econstructor; [ assumption | apply Hc; assumption ].
    - match goal with HE : Θ ⍮ _ ⍮ qname_in _ _ ⊢e _ |- _ => pose proof (wf_gentry_gctx _ _ _ _ HE) as Hg0 end.
      destruct (wf_gstack_cons_inv _ _ _ _ Hg0) as (_ & _ & Hff).
      assert (HΦ : Θ' ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ) by auto.
      econstructor; [ exact HΦ | | assumption ].
      match goal with IH : _ = _ -> ⊢g _ ⍮ (mp, gu_body Δ Φ) :: Ξ -> _ |- _ => apply IH end;
        [ reflexivity | | assumption ].
      apply wf_gstack_cons; [ assumption | exact HΦ | eapply frame_fresh_grow; eassumption ].
  Qed.

  Lemma gstack_deps_grow : forall Ξ, ⊢g Θ ⍮ Ξ -> ⊢g Θ' ⍮ nil ->
      (forall mp U, In (mp, U) Ξ -> gds_lookup Θ' (q_unit mp) = None) -> ⊢g Θ' ⍮ Ξ.
  Proof.
    induction Ξ as [| [mp U] Ξ IH]; intros HΞ HΘ' Hfr; [ exact HΘ' |].
    destruct (wf_gstack_cons_inv _ _ _ _ HΞ) as (HΞ0 & HU & Hff).
    assert (HΞ' : ⊢g Θ' ⍮ Ξ) by (apply IH; [ assumption | assumption | intros; eapply Hfr; right; eassumption ]).
    pose proof (Hfr mp U (or_introl eq_refl)) as Hn.
    destruct HU as (Δ & Φ & -> & HΦ).
    apply wf_gstack_cons; [ exact HΞ' | | eapply frame_fresh_grow; eassumption ].
    eapply (proj2 global_deps_grow); eauto.
  Qed.

  (** A filed unit, which sees no frame but its own, named by its path: that
      path must stay unfiled. *)
  Lemma unit_deps_grow : forall fp U,
      ⊢g Θ' ⍮ nil -> gds_lookup Θ' fp = None ->
      Θ ⍮ nil ⍮ q_abs fp nil ⊢u U -> Θ' ⍮ nil ⍮ q_abs fp nil ⊢u U.
  Proof.
    intros * HΘ' Hn (Δ & Φ & -> & HΦ); apply wf_gunit_intro.
    eapply (proj2 global_deps_grow); [ eassumption | reflexivity | exact HΘ' | exact Hn ].
  Qed.
End GrowDeps.

(** ** Merging Keeps Well-formedness

    A unit of the right side was checked against the units below it there,
    which the merge extends; the sides agree, so the merge has them as they
    are. *)

Theorem merge_wf : forall Θ Θ',
    ⊢g Θ ⍮ nil -> ⊢g Θ' ⍮ nil -> gds_agree Θ Θ' -> ⊢g gds_merge Θ Θ' ⍮ nil.
Proof.
  intros Θ Θ' HΘ; induction Θ' as [| [fp U] Θ' IH]; intros HΘ' Hag; [ exact HΘ |].
  destruct (wf_gstack_file_inv _ _ _ HΘ') as (HΘ0 & HU & Hn).
  assert (Hag0 : gds_agree Θ Θ').
  { intros fq V V' H1 H2; apply (Hag fq V V' H1); cbn.
    destruct (path_beq fq fp) eqn:Hb; [ apply path_beq_true in Hb; subst; congruence | exact H2 ]. }
  assert (HM : ⊢g gds_merge Θ Θ' ⍮ nil) by auto.
  rewrite merge_cons; unfold gds_mem; destruct (gds_lookup Θ fp) eqn:Hf; [ exact HM |].
  assert (HnM : gds_lookup (gds_merge Θ Θ') fp = None) by (apply merge_none; split; assumption).
  apply wf_gstack_file'; [ exact HM | | exact HnM ].
  eapply unit_deps_grow; [ apply merge_right, Hag0 | exact HM | exact HnM | exact HU ].
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
Definition gs_shape (Ξ : gstack) : list (qname * ctx) := map (fun f => (fst f, gu_params (snd f))) Ξ.

Lemma gs_add_params : forall x E Ξ, gs_shape (gs_add x E Ξ) = gs_shape Ξ.
Proof. intros ? ? [| [? ?] ?]; reflexivity. Qed.

(** The frames of a stack belong to units on the chain: the ones being
    loaded, so none a load files. *)
Definition stack_in (ch : list path) (Ξ : gstack) : Prop :=
  forall mp U, In (mp, U) Ξ -> In (q_unit mp) ch.

Lemma stack_in_add : forall ch x E Ξ, stack_in ch Ξ -> stack_in ch (gs_add x E Ξ).
Proof.
  intros * H mp U Hin; destruct Ξ as [| [mq V] Ξ]; [ contradiction |].
  destruct Hin as [[= <- <-] | Hin]; [ eapply H; left; reflexivity | eapply H; right; exact Hin ].
Qed.

Lemma stack_in_push : forall ch x Δ Ξ,
    stack_in ch Ξ -> gs_fresh x Ξ -> stack_in ch (gs_push (qname_in (gs_path Ξ) x) Δ Ξ).
Proof.
  intros * H Hfr mp U [[= <- <-] | Hin]; [| eapply H; exact Hin ].
  destruct Ξ as [| [mq V] Ξ]; [ contradiction |]; cbn; eapply H; left; reflexivity.
Qed.

(** A definition or an alias, checked against the frame so far, keeps the
    stack well formed. *)
Lemma add_def_wf : forall Θ Ξ x b pv A M,
    ⊢g Θ ⍮ Ξ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A -> gs_fresh x Ξ -> ⊢g Θ ⍮ gs_add x (gs_def b pv Ξ A M) Ξ.
Proof.
  intros * HΞ HM Hfr.
  destruct Ξ as [| [mp [P Φ]] Ξ]; [ contradiction |]; cbn in Hfr |- *.
  inversion HΞ as [| | ? ? ? ? ? Hs0 HΦ Hff]; subst.
  apply wf_gstack_cons; [ exact Hs0 | | exact Hff ].
  cbn; econstructor; [ eassumption | unfold gs_def; constructor; exact HM | exact Hfr ].
Qed.

Lemma add_alias_wf : forall Θ Ξ x pv Δ E,
    ⊢g Θ ⍮ Ξ -> tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    gs_fresh x Ξ -> ⊢g Θ ⍮ gs_add x (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))) Ξ.
Proof.
  intros * HΞ Htel HΔ HE Hfr.
  destruct Ξ as [| [mp [P Φ]] Ξ]; [ contradiction |]; cbn in Hfr |- *.
  inversion HΞ as [| | ? ? ? ? ? Hs0 HΦ Hff]; subst.
  apply wf_gstack_cons; [ exact Hs0 | | exact Hff ].
  cbn; econstructor; [ eassumption | constructor; assumption | exact Hfr ].
Qed.

Lemma gens_run_wf : forall Θ Ξ gs Ξ', gens_run Θ Ξ gs Ξ' -> ⊢g Θ ⍮ Ξ -> ⊢g Θ ⍮ Ξ'.
Proof.
  induction 1; intros HΞ; [ exact HΞ | apply IHgens_run; apply add_def_wf; assumption |].
  apply IHgens_run; apply (add_alias_wf _ _ _ _ nil); try assumption; [ constructor |].
  constructor; exact (presup_modexp_eq_ctx H).
Qed.

Lemma gens_run_shape : forall Θ Ξ gs Ξ', gens_run Θ Ξ gs Ξ' -> gs_shape Ξ' = gs_shape Ξ.
Proof. induction 1; rewrite ?IHgens_run, ?gs_add_params; reflexivity. Qed.

Lemma gens_run_tl : forall Θ Ξ gs Ξ', gens_run Θ Ξ gs Ξ' -> tl Ξ' = tl Ξ /\ List.length Ξ' = List.length Ξ.
Proof.
  assert (Hadd : forall x E Ξ, tl (gs_add x E Ξ) = tl Ξ /\ List.length (gs_add x E Ξ) = List.length Ξ)
    by (intros ? ? [| [? ?] ?]; split; reflexivity).
  induction 1; [ auto | |]; destruct IHgens_run; rewrite H2, H3; apply Hadd.
Qed.

Section WellFormed.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  #[local] Abbreviation run_cmd := (run_cmd load_path read to_core).
  #[local] Abbreviation run_cmds := (run_cmds load_path read to_core).
  #[local] Abbreviation run_unit := (run_unit load_path read to_core).

  Lemma run_chain_fresh :
    (forall ch Θ Ξ c Θ' Ξ', run_cmd ch Θ Ξ c Θ' Ξ' ->
       forall fq, In fq ch -> gds_lookup Θ fq = None -> gds_lookup Θ' fq = None) /\
    (forall ch Θ Ξ cs Θ' Ξ', run_cmds ch Θ Ξ cs Θ' Ξ' ->
       forall fq, In fq ch -> gds_lookup Θ fq = None -> gds_lookup Θ' fq = None) /\
    (forall ch u Θ U, run_unit ch u Θ U -> forall fq, In fq ch -> gds_lookup Θ fq = None).
  Proof.
    apply run_mut_ind; intros; eauto.
    - (* a load files what its unit filed, and the unit, which is not on the chain *)
      destruct (gds_lookup (gds_merge _ _) fq) eqn:Ef; [ exfalso | reflexivity ].
      apply merge_inv in Ef as [Ef | Ef]; [ congruence |].
      cbn in Ef; destruct (path_beq fq fp) eqn:Hb.
      + apply path_beq_true in Hb; subst; contradiction.
      + match goal with IH : forall _, In _ (fp :: ch) -> _ |- _ => rewrite (IH fq ltac:(right; assumption)) in Ef end.
        discriminate.
  Qed.

  (** A run keeps the parameters of every frame. *)
  Lemma run_params :
    (forall ch Θ Ξ c Θ' Ξ', run_cmd ch Θ Ξ c Θ' Ξ' -> gs_shape Ξ' = gs_shape Ξ) /\
    (forall ch Θ Ξ cs Θ' Ξ', run_cmds ch Θ Ξ cs Θ' Ξ' -> gs_shape Ξ' = gs_shape Ξ) /\
    (forall ch u Θ U, run_unit ch u Θ U -> True).
  Proof.
    apply run_mut_ind; intros; rewrite ?gs_add_params;
      solve [ congruence | exact I | eapply gens_run_shape; eassumption ].
  Qed.

  (** A filed unit is what loading its file yields. *)
  Definition canon (Θ : gdeps) : Prop :=
    forall fp U, gds_lookup Θ fp = Some U ->
      exists src prg u ch ΘU, load_path fp = Some src /\ read src = Some prg /\ to_core prg = Some u /\
        run_unit (fp :: ch) u ΘU U.

  Lemma canon_agree : forall Θ1 Θ2, canon Θ1 -> canon Θ2 -> gds_agree Θ1 Θ2.
  Proof.
    intros * H1 H2 fp U1 U2 E1 E2.
    destruct (H1 _ _ E1) as (src & prg & u & ch & ΘU & Hl & Hr & Ht & Hu).
    destruct (H2 _ _ E2) as (src' & prg' & u' & ch' & ΘU' & Hl' & Hr' & Ht' & Hu').
    rewrite Hl in Hl'; injection Hl' as <-; rewrite Hr in Hr'; injection Hr' as <-;
      rewrite Ht in Ht'; injection Ht' as <-.
    exact (proj2 (proj2 (proj2 (run_functional load_path read to_core)) _ _ _ _ Hu (fp :: ch') _ _ eq_refl Hu')).
  Qed.

  Lemma canon_nil : canon nil.
  Proof. intros ? ? H; discriminate H. Qed.

  Lemma canon_file : forall ch fp src prg u ΘU U,
      load_path fp = Some src -> read src = Some prg -> to_core prg = Some u ->
      run_unit (fp :: ch) u ΘU U -> canon ΘU -> canon ((fp, U) :: ΘU).
  Proof.
    intros * Hl Hr Ht Hu Hc fq V HV; cbn in HV.
    destruct (path_beq fq fp) eqn:Hb; [| exact (Hc _ _ HV) ].
    apply path_beq_true in Hb as ->; injection HV as <-.
    exists src, prg, u, ch, ΘU; repeat split; assumption.
  Qed.

  Lemma canon_merge : forall Θ1 Θ2, canon Θ1 -> canon Θ2 -> canon (gds_merge Θ1 Θ2).
  Proof. intros * H1 H2 fp U HU; apply merge_inv in HU as [HU | HU]; auto. Qed.

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
       ⊢g Θ ⍮ nil /\ canon Θ /\ Θ ⍮ nil ⍮ q_abs (hd nil ch) nil ⊢u U).
  Proof.
    apply run_mut_dind.
    - (* a definition: the new member is checked against the frame so far *)
      intros ch Θ Ξ x b pv A M HM Hfr HΞ Hc Hst.
      split; [ apply add_def_wf; assumption | split; [ exact Hc | apply gds_sub_refl ] ].
    - (* a module: its body ends on a frame with the path and parameters it opened with *)
      intros ch Θ Ξ x pv Δ cs Θ' mp' U Htel HΔ Hfr Hr IH HΞ Hc Hst.
      destruct Ξ as [| [mp [P Φ]] Ξ0]; [ contradiction |]; cbn [gs_fresh gs_path] in Hfr, Hr, IH |- *.
      assert (Hpush : ⊢g Θ ⍮ gs_push (qname_in mp x) Δ ((mp, gu_mk P Φ) :: Ξ0)).
      { apply wf_gstack_cons; [ exact HΞ | constructor; [ exact Htel | exact HΔ ] |].
        cbn; exists x; split; [ reflexivity | exact Hfr ]. }
      destruct (IH Hpush Hc (stack_in_push _ x Δ _ Hst Hfr)) as (HΞ' & Hc' & Hsub).
      pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ Hr) as Hp; cbn in Hp; injection Hp as -> HP.
      split; [| split; assumption ].
      inversion HΞ' as [| | ? ? ? ? ? Hs1 HU Hff1]; subst.
      inversion Hs1 as [| | ? ? ? ? ? Hs0 HV Hff0]; subst.
      apply wf_gstack_cons; [ exact Hs0 | | exact Hff0 ].
      cbn; econstructor; [ eassumption | constructor; eassumption | exact Hfr ].
    - (* an alias: checked against the frame so far, as a definition is *)
      intros ch Θ Ξ x pv Δ E Htel HΔ HE Hfr HΞ Hc Hst.
      split; [ apply add_alias_wf; assumption | split; [ exact Hc | apply gds_sub_refl ] ].
    - intros; split; [| split ]; auto using gds_sub_refl.
    - (* a load: the unit is filed on its own, then merged in; the frames are
         of units on the chain, so it files none of them *)
      intros ch Θ Ξ fp src prg u ΘU U Hn Hnin Hl Hr Hp Ht Hu IH HΞ Hc Hst.
      destruct IH as (HΘU & HcU & HU); cbn [hd] in HU.
      pose proof (proj2 (proj2 run_chain_fresh) _ _ _ _ Hu fp ltac:(left; reflexivity)) as HfU.
      assert (Hcf : canon ((fp, U) :: ΘU)) by (eapply canon_file; eassumption).
      assert (Hag : gds_agree Θ ((fp, U) :: ΘU)) by (apply canon_agree; assumption).
      assert (Hwf : ⊢g gds_merge Θ ((fp, U) :: ΘU) ⍮ nil)
        by (apply merge_wf; [ eapply wf_gstack_deps; eassumption | apply wf_gstack_file'; assumption | exact Hag ]).
      split; [ eapply gstack_deps_grow; [ apply merge_left | exact HΞ | exact Hwf |] |].
      + intros mq V Hin; pose proof (Hst _ _ Hin) as Hch.
        destruct (gds_lookup (gds_merge _ _) (q_unit mq)) eqn:E; [ exfalso | reflexivity ].
        apply merge_inv in E as [E | E].
        * rewrite (wf_gstack_frames _ _ HΞ _ _ Hin) in E; discriminate.
        * cbn in E; destruct (path_beq (q_unit mq) fp) eqn:Hb.
          -- apply path_beq_true in Hb; rewrite Hb in Hch; contradiction.
          -- rewrite (proj2 (proj2 run_chain_fresh) _ _ _ _ Hu _ (or_intror Hch)) in E; discriminate.
      + split; [ apply canon_merge; assumption | apply merge_left ].
    - (* an import: what its generated commands make *)
      intros * _ _ Hg HΞ Hc Hst; split; [ exact (gens_run_wf _ _ _ _ Hg HΞ) | split; [ exact Hc | apply gds_sub_refl ] ].
    - intros; split; [| split ]; auto using gds_sub_refl.
    - intros; split; [| split ]; auto using gds_sub_refl.
    - intros; split; [| split ]; auto using gds_sub_refl.
    - intros * _ _ Hr1 IH1 Hr2 IH2 HΞ Hc Hst.
      destruct (IH1 HΞ Hc Hst) as (H1 & Hc1 & Hs1).
      pose proof (stack_in_shape _ _ _ (proj1 run_params _ _ _ _ _ _ Hr1) Hst) as Hst1.
      destruct (IH2 H1 Hc1 Hst1) as (H2 & Hc2 & Hs2).
      split; [| split ]; eauto using gds_sub_trans.
    - (* a unit: its imports from nothing, its parameters, then its body in
         the frame named by its path, which nothing it imported filed *)
      intros fp ch imps P0 P cs Θ1 Θ2 mp U Hi IHi _ Htel HP _ Hb IHb.
      destruct (IHi ltac:(constructor; constructor) canon_nil ltac:(intros ? ? [])) as (H1 & Hc1 & _).
      assert (Hn1 : gds_lookup Θ1 fp = None)
        by exact (proj1 (proj2 run_chain_fresh) _ _ _ _ _ _ Hi fp (or_introl eq_refl) eq_refl).
      assert (Hpush : ⊢g Θ1 ⍮ gs_push (q_abs fp nil) P nil).
      { apply wf_gstack_cons; [ exact H1 | constructor | ].
        - exact Htel.
        - cbn; rewrite app_nil_r; exact HP.
        - cbn; split; [ exact Hn1 | reflexivity ]. }
      destruct (IHb Hpush Hc1 ltac:(intros ? ? [[= <- <-] | []]; left; reflexivity)) as (H2 & Hc2 & _).
      pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ Hb) as Hp; cbn in Hp; injection Hp as -> _.
      inversion H2; subst.
      split; [ eapply wf_gstack_deps; eassumption | split; [ assumption | cbn; apply wf_gunit_intro; assumption ] ].
  Qed.

  (** What a load files is well formed, whatever the import checks. *)
  Lemma load_wf : forall ch Θ Ξ fp src prg u ΘU U,
      ⊢g Θ ⍮ Ξ -> canon Θ -> stack_in ch Ξ -> gds_lookup Θ fp = None -> ~ In fp ch ->
      load_path fp = Some src -> read src = Some prg -> to_core prg = Some u ->
      run_unit (fp :: ch) u ΘU U ->
      ⊢g gds_merge Θ ((fp, U) :: ΘU) ⍮ Ξ /\ canon (gds_merge Θ ((fp, U) :: ΘU)) /\ Θ ⊑ gds_merge Θ ((fp, U) :: ΘU).
  Proof.
    intros * HΞ Hc Hst Hn Hnin Hl Hr Ht Hu.
    destruct (proj2 (proj2 run_wf) _ _ _ _ Hu) as (HΘU & HcU & HU); cbn [hd] in HU.
    pose proof (proj2 (proj2 run_chain_fresh) _ _ _ _ Hu fp ltac:(left; reflexivity)) as HfU.
    assert (Hcf : canon ((fp, U) :: ΘU)) by (eapply canon_file; eassumption).
    assert (Hag : gds_agree Θ ((fp, U) :: ΘU)) by (apply canon_agree; assumption).
    assert (Hwf : ⊢g gds_merge Θ ((fp, U) :: ΘU) ⍮ nil)
      by (apply merge_wf; [ eapply wf_gstack_deps; eassumption | apply wf_gstack_file'; assumption | exact Hag ]).
    split; [ eapply gstack_deps_grow; [ apply merge_left | exact HΞ | exact Hwf |] |].
    + intros mq V Hin; pose proof (Hst _ _ Hin) as Hch.
      destruct (gds_lookup (gds_merge _ _) (q_unit mq)) eqn:E; [ exfalso | reflexivity ].
      apply merge_inv in E as [E | E].
      * rewrite (wf_gstack_frames _ _ HΞ _ _ Hin) in E; discriminate.
      * cbn in E; destruct (path_beq (q_unit mq) fp) eqn:Hb.
        -- apply path_beq_true in Hb; rewrite Hb in Hch; contradiction.
        -- rewrite (proj2 (proj2 run_chain_fresh) _ _ _ _ Hu _ (or_intror Hch)) in E; discriminate.
    + split; [ apply canon_merge; assumption | apply merge_left ].
  Qed.

  Corollary load_coherent : forall ch Θ Ξ fp Θ',
      ⊢g Θ ⍮ Ξ -> canon Θ -> stack_in ch Ξ ->
      run_cmd ch Θ Ξ (cc_load fp) Θ' Ξ ->
      ⊢g Θ' ⍮ nil /\ gds_lookup Θ' fp <> None.
  Proof.
    intros * HΞ Hc Hst Hr; destruct (proj1 run_wf _ _ _ _ _ _ Hr HΞ Hc Hst) as (H' & _ & _).
    split; [ eapply wf_gstack_deps; eassumption |].
    inversion Hr; subst; [ congruence |].
    (* [fp] was loaded: it is filed on top of what its run filed *)
    rewrite merge_none; cbn; rewrite path_beq_refl; intros [_ ?]; discriminate.
  Qed.

  Corollary prog_sem_wf : forall prg Θ U,
      prog_sem load_path read to_core prg Θ U ->
      ⊢g Θ ⍮ nil /\ Θ ⍮ nil ⍮ q_abs (prog_path prg) nil ⊢u U.
  Proof.
    intros * (u & _ & Hu); destruct (proj2 (proj2 run_wf) _ _ _ _ Hu) as (? & _ & ?); split; assumption.
  Qed.
End WellFormed.


(** ** Restricting to What a Unit Imported

    The executable ([Extraction.Command]) keeps one set of filed units for the
    whole program, so no unit is run twice; but a unit runs from nothing, and
    may mention only what it imported.  So it is checked against the
    restriction of that set to the paths it imported, which has the lookups of
    the judgment's state ([equiv_restrict]).  Checking against the whole set
    would accept a unit mentioning a unit it never imported, filed by someone
    else. *)

Definition gds_restrict (S : list path) (Θ : gdeps) : gdeps :=
  filter (fun e => existsb (path_beq (fst e)) S) Θ.

Definition gds_dom (Θ : gdeps) : list path := map fst Θ.

Definition gds_equiv (Θ Θ' : gdeps) : Prop := Θ ⊑ Θ' /\ Θ' ⊑ Θ.

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

Lemma gds_lookup_restrict : forall S Θ fp,
    gds_lookup (gds_restrict S Θ) fp = if existsb (path_beq fp) S then gds_lookup Θ fp else None.
Proof.
  unfold gds_restrict; induction Θ as [| [fq V] Θ IH]; intros; cbn [filter fst].
  - destruct (existsb _ _); reflexivity.
  - destruct (path_beq fp fq) eqn:Hb.
    + apply path_beq_true in Hb as <-.
      destruct (existsb (path_beq fp) S) eqn:E; cbn [gds_lookup]; rewrite ?path_beq_refl, ?IH, ?E; reflexivity.
    + destruct (existsb (path_beq fq) S); cbn [gds_lookup]; rewrite ?Hb; apply IH.
Qed.

Corollary restrict_sub : forall S Θ, gds_restrict S Θ ⊑ Θ.
Proof. intros * fp U; rewrite gds_lookup_restrict; destruct (existsb _ _); [ auto | discriminate ]. Qed.

Lemma gds_dom_lookup : forall Θ fp, In fp (gds_dom Θ) <-> gds_lookup Θ fp <> None.
Proof.
  induction Θ as [| [fq V] Θ IH]; intros; cbn [gds_dom map In fst gds_lookup].
  - split; [ contradiction | intros H; apply H; reflexivity ].
  - destruct (path_beq fp fq) eqn:Hb.
    + apply path_beq_true in Hb as ->; split; [ discriminate | auto ].
    + rewrite <- IH; split; [| auto ].
      intros [-> | H]; [ rewrite path_beq_refl in Hb; discriminate | exact H ].
Qed.

Lemma gds_dom_none : forall Θ fp, ~ In fp (gds_dom Θ) <-> gds_lookup Θ fp = None.
Proof.
  intros; rewrite gds_dom_lookup; destruct (gds_lookup Θ fp); split; intros H;
    [ exfalso; apply H; discriminate | discriminate | reflexivity | intros H'; apply H'; reflexivity ].
Qed.

Lemma gds_equiv_refl : forall Θ, gds_equiv Θ Θ.
Proof. intros; split; apply gds_sub_refl. Qed.

Lemma gds_equiv_sym : forall Θ Θ', gds_equiv Θ Θ' -> gds_equiv Θ' Θ.
Proof. intros * [H1 H2]; split; assumption. Qed.

Lemma gds_equiv_trans : forall Θ1 Θ2 Θ3, gds_equiv Θ1 Θ2 -> gds_equiv Θ2 Θ3 -> gds_equiv Θ1 Θ3.
Proof. intros * [H1 H2] [H3 H4]; split; eauto using gds_sub_trans. Qed.

(** A judgment state below [Θ], with domain [S], is equivalent to the
    restriction of [Θ] to [S]. *)
Lemma equiv_restrict : forall ΘA Θ S,
    ΘA ⊑ Θ -> (forall x, In x S <-> In x (gds_dom ΘA)) ->
    gds_equiv ΘA (gds_restrict S Θ).
Proof.
  intros * Hsub Hdom; split.
  - intros x V HV; rewrite gds_lookup_restrict.
    assert (Hx : In x S) by (apply Hdom, gds_dom_lookup; rewrite HV; discriminate).
    apply existsb_path_beq in Hx; rewrite Hx; auto.
  - intros x V HV; rewrite gds_lookup_restrict in HV.
    destruct (existsb (path_beq x) S) eqn:Hb; [| discriminate ]; apply existsb_path_beq, Hdom, gds_dom_lookup in Hb.
    destruct (gds_lookup ΘA x) as [V' |] eqn:E; [| contradiction ].
    rewrite (Hsub _ _ E) in HV; injection HV as ->; reflexivity.
Qed.

(** Term judgments and [⊢g] only read lookups, so they cross [gds_equiv] both
    ways by weakening alone. *)
Lemma equiv_gctx : forall Θ Θ' Ξ, gds_equiv Θ Θ' -> ⊢g Θ' ⍮ nil -> ⊢g Θ ⍮ Ξ -> ⊢g Θ' ⍮ Ξ.
Proof.
  intros * [H H'] HΘ' HΞ; apply (gstack_deps_grow _ _ H _ HΞ HΘ').
  intros mp U Hin; pose proof (wf_gstack_frames _ _ HΞ _ _ Hin) as Hn.
  destruct (gds_lookup Θ' (q_unit mp)) eqn:E; [ rewrite (H' _ _ E) in Hn; discriminate | reflexivity ].
Qed.

Lemma equiv_exp : forall Θ Θ' Ξ Γ M A,
    gds_equiv Θ Θ' -> ⊢g Θ' ⍮ Ξ -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ' ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * [H _] HΞ HM; apply (deps_grow _ _ _ H); [ constructor; exact HΞ | exact HM ].
Qed.

Lemma equiv_ctx : forall Θ Θ' Ξ Γ,
    gds_equiv Θ Θ' -> ⊢g Θ' ⍮ Ξ -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ' ⍮ Ξ ⍮ Γ.
Proof.
  intros * [H _] HΞ HΓ; apply (deps_grow _ _ _ H); [ constructor; exact HΞ | exact HΓ ].
Qed.

Lemma equiv_ext : forall Θ Θ' Ξ Γ Ψ,
    gds_equiv Θ Θ' -> ⊢g Θ' ⍮ Ξ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ -> Θ' ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ.
Proof.
  intros * [H _] HΞ HΨ; apply (deps_grow _ _ _ H); [ constructor; exact HΞ | exact HΨ ].
Qed.

Lemma equiv_modexp : forall Θ Θ' Ξ Γ E,
    gds_equiv Θ Θ' -> ⊢g Θ' ⍮ Ξ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E -> Θ' ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E.
Proof.
  intros * [H _] HΞ HE; apply (deps_grow _ _ _ H); [ constructor; exact HΞ | exact HE ].
Qed.

Lemma equiv_acc : forall Θ Θ' Ξ l, gds_equiv Θ Θ' -> acc_ok Θ Ξ l -> acc_ok Θ' Ξ l.
Proof. intros * Heq Hl; eapply acc_ok_dsub; [ exact (proj2 Heq) | exact Hl ]. Qed.

(** ** The Restriction is Well Formed

    Without strengthening: a unit of the restriction was checked against
    units below it, all imported, which the restriction below it extends. *)

(** Every filed unit of [S] was checked against units of [S] filed, as they
    are, below it. *)
Fixpoint closure_ok (S : list path) (Θ : gdeps) : Prop :=
  match Θ with
  | nil => True
  | (fp, U) :: Θ' =>
      (In fp S -> exists ΘU, ΘU ⍮ nil ⍮ q_abs fp nil ⊢u U /\ ΘU ⊑ Θ' /\ forall x, In x (gds_dom ΘU) -> In x S) /\
      closure_ok S Θ'
  end.

Theorem restrict_wf : forall S Θ, ⊢g Θ ⍮ nil -> closure_ok S Θ -> ⊢g gds_restrict S Θ ⍮ nil.
Proof.
  intros S; induction Θ as [| [fp U] Θ IH]; intros Hwf Hc; [ exact Hwf |].
  destruct Hc as [Hc Hcl]; destruct (wf_gstack_file_inv _ _ _ Hwf) as (HΘ & _ & Hn).
  assert (HR : ⊢g gds_restrict S Θ ⍮ nil) by auto.
  unfold gds_restrict; cbn [filter fst]; fold (gds_restrict S Θ).
  destruct (existsb (path_beq fp) S) eqn:Hb; [| exact HR ].
  apply existsb_path_beq in Hb; destruct (Hc Hb) as (ΘU & HU & Hsub & Hdom).
  assert (HnR : gds_lookup (gds_restrict S Θ) fp = None)
    by (rewrite gds_lookup_restrict; destruct (existsb _ _); [ exact Hn | reflexivity ]).
  apply wf_gstack_file'; [ exact HR | | exact HnR ].
  eapply unit_deps_grow; [| exact HR | exact HnR | exact HU ].
  intros x V HV; rewrite gds_lookup_restrict.
  assert (Hx : In x S) by (apply Hdom, gds_dom_lookup; rewrite HV; discriminate).
  apply existsb_path_beq in Hx; rewrite Hx; exact (Hsub _ _ HV).
Qed.

(** ** Chains and Stacks of Runs *)

Section Runs.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  #[local] Abbreviation run_cmd := (run_cmd load_path read to_core).
  #[local] Abbreviation run_cmds := (run_cmds load_path read to_core).
  #[local] Abbreviation run_unit := (run_unit load_path read to_core).

  Lemma run_dom_mono :
    (forall ch Θ Ξ c Θ' Ξ', run_cmd ch Θ Ξ c Θ' Ξ' ->
       forall x, gds_lookup Θ x <> None -> gds_lookup Θ' x <> None) /\
    (forall ch Θ Ξ cs Θ' Ξ', run_cmds ch Θ Ξ cs Θ' Ξ' ->
       forall x, gds_lookup Θ x <> None -> gds_lookup Θ' x <> None) /\
    (forall ch u Θ U, run_unit ch u Θ U -> True).
  Proof.
    apply run_mut_ind; intros; auto.
    intros Ef; apply merge_none in Ef as [Ef _]; contradiction.
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
    { intros * Hr Hch x Hx; destruct (gds_lookup Θ x) eqn:Ef; [ exfalso | reflexivity ].
      eapply (proj1 (proj2 run_dom_mono)); [ exact Hr | rewrite Ef; discriminate | apply Hch, Hx ]. }
    apply run_mut_dind; intros.
    - constructor; assumption.
    - econstructor; eauto.
    - eapply rc_alias; eassumption.
    - eapply rc_load_filed; eassumption.
    - rename r into Hu, H into IH, H0 into Hch.
      eapply rc_load; try eassumption.
      + intros Hin; specialize (Hch _ Hin); apply merge_none in Hch as [_ Hf].
        cbn in Hf; rewrite path_beq_refl in Hf; discriminate.
      + apply IH; intros x [<- | Hin].
        * exact (proj2 (proj2 (run_chain_fresh load_path read to_core)) _ _ _ _ Hu _ (or_introl eq_refl)).
        * specialize (Hch _ Hin); apply merge_none in Hch as [_ Hf].
          cbn in Hf; destruct (path_beq x fp); [ discriminate | exact Hf ].
    - econstructor; eauto.
    - apply rc_eval_check; assumption.
    - eapply rc_eval_infer; eassumption.
    - constructor.
    - econstructor; [ eassumption | eassumption | apply H; eapply Hpre; eassumption | auto ].
    - cbn [hd] in *; econstructor; [ apply H; eapply Hpre; eassumption | eassumption | assumption | assumption | assumption | auto ].
  Qed.

  Lemma run_tl :
    (forall ch Θ Ξ c Θ' Ξ', run_cmd ch Θ Ξ c Θ' Ξ' -> tl Ξ' = tl Ξ /\ List.length Ξ' = List.length Ξ) /\
    (forall ch Θ Ξ cs Θ' Ξ', run_cmds ch Θ Ξ cs Θ' Ξ' -> tl Ξ' = tl Ξ /\ List.length Ξ' = List.length Ξ) /\
    (forall ch u Θ U, run_unit ch u Θ U -> True).
  Proof.
    assert (Hadd : forall x E Ξ, tl (gs_add x E Ξ) = tl Ξ /\ List.length (gs_add x E Ξ) = List.length Ξ)
      by (intros ? ? [| [? ?] ?]; split; reflexivity).
    apply run_mut_ind; intros; auto; try (eapply gens_run_tl; eassumption); intuition congruence.
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

End Runs.
