(** * The Static Semantics of Commands

    A command moves the global state: the filed units [Θ] and the stack [Ξ] of
    open frames.  [cc_load] loads the unit it names, if it is not filed yet,
    by running that unit's own commands from nothing, and merges the units
    that run filed into [Θ]; the chain of units whose loading is in progress
    is what rules a cycle out.  [cc_open] declares the names its items
    generate ([items_gen], the relation the local opens of bodies share) as
    definitions, aliases and inductive aliases of the frame.  A command runs
    as written, but for its literals ([Builtin]): no expansion comes first.

    Resolution is lexical — a unit is named by its full path, and an import
    lists the names it binds — so elaborating a unit needs none of the units
    it imports, which are only loaded while it runs. *)

From Stdlib Require Import List String PeanoNat Bool.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Command Members Builtin.
From Mctt.Core.Syntactic.System Require Import Definitions Lemmas Structural.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Inductives Require Export Classify.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf Modules.
From Mctt.Core.Syntactic.System Require Export Privacy.
From Mctt.Core.Semantic Require Import NbE.
Import Syntax_Notations GlobalCtx_Notations.

Reserved Notation "Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ ch ] c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'"
  (at level 70, Ξ at level 69, B at level 69, Rb at level 69, ch at level 69, c at level 69, Θ' at level 69, Ξ' at level 69, B' at level 69, Rb' at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ ch ] cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'"
  (at level 70, Ξ at level 69, B at level 69, Rb at level 69, ch at level 69, cs at level 69, Θ' at level 69, Ξ' at level 69, B' at level 69, Rb' at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ ch ]⟨ lp ⍮ rd ⍮ tc ⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'"
  (at level 70, Ξ at level 69, B at level 69, Rb at level 69, ch at level 69, lp at level 69, rd at level 69, tc at level 69, c at level 69, Θ' at level 69, Ξ' at level 69, B' at level 69, Rb' at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ ch ]⟨ lp ⍮ rd ⍮ tc ⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'"
  (at level 70, Ξ at level 69, B at level 69, Rb at level 69, ch at level 69, lp at level 69, rd at level 69, tc at level 69, cs at level 69, Θ' at level 69, Ξ' at level 69, B' at level 69, Rb' at level 69).

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

(** A definition and an axiom as they are filed: closed over the frames'
    parameters. *)
Definition gs_def (b pv : bool) (Ξ : gstack) (A M : exp) : gentry :=
  ge_def b pv (ctx_pi (gs_tele Ξ) A) (Some (ctx_fn (gs_tele Ξ) M)).

Definition gs_axiom (b pv : bool) (Ξ : gstack) (A : exp) : gentry :=
  ge_def b pv (ctx_pi (gs_tele Ξ) A) None.

(** ** Opens

    The definitions and aliases an open generates ([items_gen]), declared in
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
    gens_run Θ Ξ (ig_alias d pv E :: gs) Ξ'
| gr_ind_alias : forall Ξ d pv Δ p Ns gs Ξ',
    Θ ⍮ Ξ ⍮ qname_in (gs_path Ξ) d ⊢ᵉ ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns -> gs_fresh d Ξ ->
    gens_run Θ (gs_add d (ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns) Ξ) gs Ξ' ->
    gens_run Θ Ξ (ig_ind_alias d pv Δ p Ns :: gs) Ξ'.

(** ** Inductive Declarations

    A declaration [x] is filed as the entry [x] of the frame
    ([ge_ind]): the declaration, with the parameters of the frames as its
    outermost uniform parameters ([gs_ind]), and the body of its module,
    whose members are generated ([gen_body]): the constructors, each the
    constructor applied to the uniform parameters, and the recursor, all
    closed over the uniform parameters, which are the module's.  The entry
    is checked member by member ([wf_gentry_ind_ext]).  As a term, the
    path of the entry is the type former ([wf_mem_glob_ind]). *)

Definition gs_ind (Ξ : gstack) (D : ind_decl) : ind_decl :=
  mk_ind (ind_nu D + List.length (gs_tele Ξ)) (ind_params D ++ gs_tele Ξ) (ind_sort D) (ind_cons D).

(** The path of the inductive type [x] a declaration makes. *)
Definition ind_qname (Ξ : gstack) (x : string) : qname := qname_in (gs_path Ξ) x.

(** The recursor of the filed declaration [D], over the module's
    parameters [Γ0] (the uniform ones): at a finite level [u], a motive
    [P : Π Δn. Π (z : X us ns). Type⟨u⟩], one branch per constructor, of
    the type the eliminator gives a branch at the motive [P], then
    [Π Δn. Π (z : X us ns). P ns z].  It is the eliminator, at that motive,
    of branches that are the branch arguments applied to what they bind.
    Below [k] binders past [P], the motive is [P] under [Δn] and [z], and
    the uniform parameters are the module's. *)
Definition rec_motive (D : ind_decl) (k : nat) : exp :=
  apps (a_var (S (ind_nn D) + k)) (vars_from 0 (S (ind_nn D))).

Definition rec_uvars (D : ind_decl) (k : nat) : list exp := vars_from (2 + k) (ind_nu D).

(** The branch types, outermost first, the [k]-th under [k] before it. *)
Fixpoint rec_btys (p : qname) (D : ind_decl) (k : nat) (cs : list (string * list carg)) : list centry :=
  match cs with
  | nil => nil
  | (c, gs) :: cs' =>
      ce_ass (ctx_pi (elim_bctx p D gs (rec_motive D k) (rec_uvars D k))
                (elim_bty p D c gs (rec_motive D k) (rec_uvars D k)))
      :: rec_btys p D (S k) cs'
  end.

(** The level, the motive and the branches, innermost first. *)
Definition rec_tele (p : qname) (D : ind_decl) : ctx :=
  List.rev (rec_btys p D 0 (ind_cons D)) ++
  ce_ass (ctx_pi (elim_mctx p D (vars_from 1 (ind_nu D))) (a_univ (a_var (S (ind_nn D))))) ::
  ce_ass (a_level 0) :: nil.

Definition rec_ty (p : qname) (D : ind_decl) : typ :=
  let K := List.length (ind_cons D) in
  ctx_pi (rec_tele p D) (ctx_pi (elim_mctx p D (rec_uvars D K)) (rec_motive D K)).

(** The branches of the eliminator, each the [j]-th branch argument applied
    to the variables the branch binds. *)
Fixpoint rec_brs (D : ind_decl) (K j : nat) (cs : list (string * list carg)) : list (string * nat * exp) :=
  match cs with
  | nil => nil
  | (c, gs) :: cs' =>
      let n := (ind_nn D + List.length gs + cargs_nrec gs)%nat in
      (c, n, apps (a_var (n + S (ind_nn D) + (K - 1 - j))) (vars_from 0 n)) :: rec_brs D K (S j) cs'
  end.

Definition rec_fn (p : qname) (D : ind_decl) : exp :=
  let K := List.length (ind_cons D) in
  ctx_fn (rec_tele p D)
    (ctx_fn (elim_mctx p D (rec_uvars D K))
       (a_elim (S (ind_nn D)) (rec_motive D (K + S (ind_nn D))) (rec_brs D K 0 (ind_cons D)) (a_var 0))).

(** The constructors of the filed declaration [D], over the module's
    parameters: [D]'s uniform ones, then its recursor.  They are public
    members of the module, as the declaration is: the module's own privacy
    is the declaration's. *)
Definition ind_gens (p : qname) (D : ind_decl) : list igen :=
  List.map (fun cg =>
              ig_def (fst cg) false
                (ctx_pi (ind_nparams D)
                   (ctx_pi (cargs_ctx p D (snd cg)) (apps (a_ind p) (ind_pvars D (List.length (snd cg))))))
                (apps (a_con p (fst cg)) (vars_from 0 (ind_nu D))))
    (ind_cons D)
  ++ ig_def "rec" false (rec_ty p D) (rec_fn p D) :: nil.

(** The body the generated definitions make after [Φ], each closed over the
    telescope [T]; an alias generates nothing here. *)
Fixpoint gens_body (Φ : gmod) (T : ctx) (gs : list igen) : gmod :=
  match gs with
  | nil => Φ
  | ig_def d pv A M :: gs' => gens_body (Φ ⊳ d ↦ ge_def true pv (ctx_pi T A) (Some (ctx_fn T M))) T gs'
  | ig_alias _ _ _ :: gs' | ig_ind_alias _ _ _ _ _ :: gs' => gens_body Φ T gs'
  end.

(** The body of the module of the inductive type [D] at [p]: its
    constructors and its recursor, over the uniform parameters. *)
Definition gen_body (p : qname) (D : ind_decl) : gmod := gens_body ⋄ (ind_uparams D) (ind_gens p D).

(** ** Classifying the Arguments on Normal Forms

    An argument the syntactic classification ([cls_arg]) does not accept is
    read as its normal form: it is a type in the context it is written in
    ([rarg_ctx]: the arguments before it, the declaration's own parameters,
    [Self], the frames' parameters), and its normal form is classified.  So
    [Arr Ord], with [Arr X := ℕ → X], is classified as [ℕ → Ord] is, and
    [(λ X. ℕ) (Ord → ℕ)] as [ℕ].  The syntactic path comes first, so the
    classification is a function of the argument. *)

(** The type of [Self]: the declared type's, over the declaration's own
    parameters. *)
Definition rd_self_ty (R : raw_decl) : typ :=
  ctx_pi (rd_params R) (rd_sort R)[wk_shiftn (List.length (rd_params R) - rd_nu R)]ʷ.

(** The parameters' types are written over the frames' parameters, so
    under [Self] they are weakened past it. *)
Definition rarg_ctx (Ξ : gstack) (R : raw_decl) (args1 : list (string * exp)) : ctx :=
  rtele args1 ++ tele_wk (rd_params R) wk_shift ++ ce_ass (rd_self_ty R) :: gs_tele Ξ.

Inductive cls_arg_in (Θ : gdeps) (Ξ : gstack) (R : raw_decl) (args1 : list (string * exp)) (gs1 : list carg)
    (T : exp) : carg -> Prop :=
(** As written. *)
| cls_in_syn : forall g,
    cls_arg (rd_nu R) (List.length (rd_params R)) gs1 T g -> cls_arg_in Θ Ξ R args1 gs1 T g
(** As its normal form, when not as written. *)
| cls_in_nf : forall i W g,
    (forall g', ~ cls_arg (rd_nu R) (List.length (rd_params R)) gs1 T g') ->
    Θ ⍮ Ξ ⍮ rarg_ctx Ξ R args1 ⊢ T : Typeω@i ->
    nbe_ty Θ Ξ (rarg_ctx Ξ R args1) T W ->
    cls_arg (rd_nu R) (List.length (rd_params R)) gs1 (nf_to_exp W) g ->
    cls_arg_in Θ Ξ R args1 gs1 T g.

Inductive cls_args_in (Θ : gdeps) (Ξ : gstack) (R : raw_decl) :
    list (string * exp) -> list carg -> list (string * exp) -> list carg -> Prop :=
| cls_args_in_nil : forall args1 gs1, cls_args_in Θ Ξ R args1 gs1 nil nil
| cls_args_in_cons : forall args1 gs1 y T args g gs,
    cls_arg_in Θ Ξ R args1 gs1 T g ->
    cls_args_in Θ Ξ R (args1 ++ (y, T) :: nil) (gs1 ++ g :: nil) args gs ->
    cls_args_in Θ Ξ R args1 gs1 ((y, T) :: args) (g :: gs).

Definition cls_cons_in (Θ : gdeps) (Ξ : gstack) (R : raw_decl) (cs : list (string * list carg)) : Prop :=
  Forall2 (fun rc c => fst rc = fst c /\ cls_args_in Θ Ξ R nil nil (snd rc) (snd c)) (rd_cons R) cs.

Lemma cls_arg_in_functional : forall Θ Ξ R args1 gs1 T g g',
    cls_arg_in Θ Ξ R args1 gs1 T g -> cls_arg_in Θ Ξ R args1 gs1 T g' -> g = g'.
Proof.
  intros * H H'; destruct H as [g Hg | i W g Hn _ HW Hg]; inversion H' as [g'' Hg' | i' W' g'' Hn' _ HW' Hg']; subst.
  - eapply cls_arg_functional; eassumption.
  - exfalso; exact (Hn' _ Hg).
  - exfalso; exact (Hn _ Hg').
  - pose proof (functional_nbe_ty _ _ _ _ HW HW') as <-; eapply cls_arg_functional; eassumption.
Qed.

Lemma cls_args_in_functional : forall Θ Ξ R args1 gs1 args gs gs',
    cls_args_in Θ Ξ R args1 gs1 args gs -> cls_args_in Θ Ξ R args1 gs1 args gs' -> gs = gs'.
Proof.
  intros * H; revert gs'; induction H as [| args1 gs1 y T args g gs Hg Hgs IH]; intros gs' H'; inversion H'; subst;
    [ reflexivity |].
  match goal with Hg' : cls_arg_in _ _ _ _ _ _ ?g' |- _ => pose proof (cls_arg_in_functional _ _ _ _ _ _ _ _ Hg Hg') as <- end.
  f_equal; apply IH; assumption.
Qed.

Lemma cls_cons_in_functional : forall Θ Ξ R cs cs', cls_cons_in Θ Ξ R cs -> cls_cons_in Θ Ξ R cs' -> cs = cs'.
Proof.
  unfold cls_cons_in; intros Θ Ξ R; generalize (rd_cons R); intros rcs.
  induction rcs as [| rc rcs IH]; intros * H H'; inversion H; inversion H'; subst; [ reflexivity |].
  destruct y as [c gs], y0 as [c' gs']; cbn in *; destruct_conjs; subst.
  f_equal; [ f_equal; eapply cls_args_in_functional; eassumption | apply IH; assumption ].
Qed.

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

(** ** The Records of Filed Units

    The record of builtin bindings each filed unit ended with, apart from
    the units themselves: merged as they are ([bm_merge]). *)

Definition bmap : Set := list (path * builtins).

Fixpoint bm_lookup (Rb : bmap) (fp : path) : option builtins :=
  match Rb with
  | nil => None
  | (fq, B) :: Rb' => if path_beq fp fq then Some B else bm_lookup Rb' fp
  end.

Definition bm_mem (fp : path) (Rb : bmap) : bool :=
  match bm_lookup Rb fp with Some _ => true | None => false end.

Definition bm_merge (Rb Rb' : bmap) : bmap :=
  filter (fun e => negb (bm_mem (fst e) Rb)) Rb' ++ Rb.

Lemma bm_lookup_merge : forall Rb Rb' fp,
    bm_lookup (bm_merge Rb Rb') fp = match bm_lookup Rb fp with Some B => Some B | None => bm_lookup Rb' fp end.
Proof.
  intros Rb Rb' fp; unfold bm_merge; induction Rb' as [| [fq V] Rb' IH]; cbn [filter List.app].
  - destruct (bm_lookup Rb fp); reflexivity.
  - unfold bm_mem at 1; cbn [fst]; destruct (bm_lookup Rb fq) eqn:Hq; cbn [negb]; rewrite ?IH.
    + cbn [bm_lookup]; destruct (bm_lookup Rb fp) eqn:Hp; [ reflexivity |].
      destruct (path_beq fp fq) eqn:Hb; [ apply path_beq_true in Hb; congruence | reflexivity ].
    + cbn [bm_lookup List.app]; rewrite IH.
      destruct (path_beq fp fq) eqn:Hb; [| reflexivity ].
      apply path_beq_true in Hb; subst; rewrite Hq; reflexivity.
Qed.

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
      of [rc_def], [rc_axiom], [rc_mod] and [rc_alias] are those of
      [wf_gentry_def], [wf_gentry_axiom], [wf_gmod_nil] and
      [wf_gentry_alias], with the freshness of [wf_gmod_ext].  Privacy is checked by
      [rcs_cons], on the command as written.

      [B] is the record of builtin bindings of the unit being run, and [Rb]
      the records the filed units ended with, one per unit of [Θ]: a unit
      sees the bindings it makes and those of the units it imports, never
      those of the unit importing it. *)

  Inductive run_cmd : list path -> builtins -> bmap -> gdeps -> gstack -> ccmd -> builtins -> bmap -> gdeps -> gstack -> Prop :=
  | rc_def : forall ch B Rb Θ Ξ x b pv A M,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
      gs_fresh x Ξ ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_def x b pv A (Some M) ⇝ Θ ⍮ gs_add x (gs_def b pv Ξ A M) Ξ ⍮ B ⍮ Rb
  (** An axiom: only its type is checked. *)
  | rc_axiom : forall ch B Rb Θ Ξ x b pv A i,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i ->
      gs_fresh x Ξ ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_def x b pv A None ⇝ Θ ⍮ gs_add x (gs_axiom b pv Ξ A) Ξ ⍮ B ⍮ Rb
  (** The body ends on the frame it opened, the stack below as it was; that
      frame becomes the member [x] of the one below, as it is. *)
  | rc_mod : forall ch B Rb B' Rb' Θ Ξ x pv Δ cs Θ' mp U,
      tele_ass Δ ->
      ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
      gs_fresh x Ξ ->
      Θ ⍮ gs_push (qname_in (gs_path Ξ) x) Δ Ξ ⍮ B ⍮ Rb ⊢[ch] cs ⇝* Θ' ⍮ (mp, U) :: Ξ ⍮ B' ⍮ Rb' ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_mod x pv Δ cs ⇝ Θ' ⍮ gs_add x (ge_body pv Δ (gu_mod U)) Ξ ⍮ B' ⍮ Rb'
  (** An alias is filed with the frames' parameters it is declared under. *)
  | rc_alias : forall ch B Rb Θ Ξ x pv Δ E,
      tele_ass Δ ->
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ ->
      Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
      gs_fresh x Ξ ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_alias x pv Δ E ⇝ Θ ⍮ gs_add x (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))) Ξ ⍮ B ⍮ Rb
  (** A unit filed already, by an earlier load: shared, not reloaded; the
      record it ended with is merged in. *)
  | rc_load_filed : forall ch B Rb B' Θ Ξ fp U BU,
      gds_lookup Θ fp = Some U ->
      bm_lookup Rb fp = Some BU ->
      bt_merge B BU = Some B' ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_load fp ⇝ Θ ⍮ Ξ ⍮ B' ⍮ Rb
  (** Not filed: load it, run it from nothing with itself added to the chain,
      file it on top of what it filed, and merge that in.  A unit already in the
      chain is still being loaded, so loading it is a cycle, and no rule
      applies.  The unit runs from no binding; the record it ends with is
      merged in, and filed with it. *)
  | rc_load : forall ch B Rb B' Θ Ξ fp src prg u BU RbU ΘU U,
      gds_lookup Θ fp = None ->
      ~ In fp ch ->
      load_path fp = Some src ->
      read src = Some prg ->
      prog_path prg = fp ->
      to_core prg = Some u ->
      run_unit (fp :: ch) u BU RbU ΘU U ->
      bt_merge B BU = Some B' ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_load fp ⇝ gds_merge Θ ((fp, U) :: ΘU) ⍮ Ξ ⍮ B' ⍮ bm_merge Rb ((fp, BU) :: RbU)
  (** An open checks that its target is a module, and declares the
      definitions and aliases its items generate in this frame. *)
  | rc_open : forall ch B Rb Θ Ξ E its gs Ξ',
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
      open_gens Θ Ξ true (gs_tele Ξ) E its gs ->
      gens_run Θ Ξ gs Ξ' ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_open E its ⇝ Θ ⍮ Ξ' ⍮ B ⍮ Rb
  (** A declaration as written: its arguments classified ([cls_cons_in]);
      the entry it is filed as, the declaration with its module's generated
      body, checked where it is declared. *)
  | rc_ind : forall ch B Rb Θ Ξ x pv R cs,
      cls_cons_in Θ Ξ R cs ->
      gs_fresh x Ξ ->
      Θ ⍮ Ξ ⍮ ind_qname Ξ x
        ⊢ᵉ ge_ind pv (ind_qname Ξ x) (gs_ind Ξ (rd_filed R cs)) (gen_body (ind_qname Ξ x) (gs_ind Ξ (rd_filed R cs))) ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_ind x pv R ⇝
        Θ ⍮ gs_add x (ge_ind pv (ind_qname Ξ x) (gs_ind Ξ (rd_filed R cs)) (gen_body (ind_qname Ξ x) (gs_ind Ξ (rd_filed R cs)))) Ξ ⍮ B ⍮ Rb
  (** [builtin natural := X]: [X], a module expression, denotes an inductive type at no argument
      and over no parameter, with the shape of the natural numbers, in
      [Type@0]; its binding is merged in ([bt_bind_nat]), so it is bound
      unless another type is. *)
  | rc_builtin : forall ch B Rb B' Θ Ξ H p D z s,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ H ≈ H ->
      mdenote Θ Ξ (gs_tele Ξ) H (ds_ind nil p nil) ->
      ind_lookup Θ Ξ p = Some D ->
      nat_shape D = Some (z, s) ->
      ind_sort D = nat_sort ->
      bt_bind_nat B p = Some B' ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_builtin nat_kind H ⇝ Θ ⍮ Ξ ⍮ B' ⍮ Rb
  (** [inductive x Δ := E]: [E], a module expression, denotes an inductive
      type at arguments [Ns], over the parameters [Θ'] it is still
      abstracted over; the alias stores the canonical path and the
      arguments, over [Θ'] and [Δ], checked as its entry. *)
  | rc_ind_alias : forall ch B Rb Θ Ξ x pv Δ H Θ' p Ns,
      Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ H ≈ H ->
      mdenote Θ Ξ (Δ ++ gs_tele Ξ) H (ds_ind Θ' p Ns) ->
      Θ ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind_alias pv (Θ' ++ Δ ++ gs_tele Ξ) p Ns ->
      gs_fresh x Ξ ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_ind_alias x pv Δ H ⇝
        Θ ⍮ gs_add x (ge_ind_alias pv (Θ' ++ Δ ++ gs_tele Ξ) p Ns) Ξ ⍮ B ⍮ Rb
  (** An [eval] changes nothing, but must type-check where it stands. *)
  | rc_eval_check : forall ch B Rb Θ Ξ M A,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_eval M (Some A) ⇝ Θ ⍮ Ξ ⍮ B ⍮ Rb
  | rc_eval_infer : forall ch B Rb Θ Ξ M A,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_eval M None ⇝ Θ ⍮ Ξ ⍮ B ⍮ Rb
  where "Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ ch ] c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'" := (run_cmd ch B Rb Θ Ξ c B' Rb' Θ' Ξ')

  with run_cmds : list path -> builtins -> bmap -> gdeps -> gstack -> list ccmd -> builtins -> bmap -> gdeps -> gstack -> Prop :=
  | rcs_nil : forall ch B Rb Θ Ξ, Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] nil ⇝* Θ ⍮ Ξ ⍮ B ⍮ Rb
  (** Each command is checked for privacy as written, and its literals are
      generated from the builtin bindings ([Builtin]) before it runs. *)
  | rcs_cons : forall ch B Rb Θ Ξ c c1 cs B1 Rb1 Θ1 Ξ1 B2 Rb2 Θ2 Ξ2,
      acc_ok Θ Ξ (cmd_refs c) ->
      cmd_lits_ok Θ Ξ B c c1 ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] c1 ⇝ Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ->
      Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ⊢[ch] cs ⇝* Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2 ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] c :: cs ⇝* Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2
  where "Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ ch ] cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'" := (run_cmds ch B Rb Θ Ξ cs B' Rb' Θ' Ξ')

  (** [run_unit (fp :: ch) u B Rb Θ U]: the unit [fp], at the head of the
      chain, runs from nothing filed and no binding.  Its leading loads run
      on the empty stack, then its parameters get their literals and are
      checked against what they filed, then its body runs in
      its own frame, named [fp]; [Θ] is what it filed, [Rb] their records,
      [U] the unit, [B] its own record. *)
  with run_unit : list path -> cunit -> builtins -> bmap -> gdeps -> gunit -> Prop :=
  | ru_intro : forall fp ch B1 Rb1 B2 Rb2 imps P P1 cs Θ1 Θ2 mp U,
      nil ⍮ nil ⍮ bt_empty ⍮ nil ⊢[fp :: ch] imps ⇝* Θ1 ⍮ nil ⍮ B1 ⍮ Rb1 ->
      tele_lits_ok Θ1 nil B1 P P1 ->
      tele_ass P1 ->
      ⊢ Θ1 ⍮ nil ⍮ P1 ->
      acc_ok Θ1 nil (tele_refs nil P) ->
      Θ1 ⍮ gs_push (q_abs fp nil) P1 nil ⍮ B1 ⍮ Rb1 ⊢[fp :: ch] cs ⇝* Θ2 ⍮ (mp, U) :: nil ⍮ B2 ⍮ Rb2 ->
      run_unit (fp :: ch) (imps, P, cs) B2 Rb2 Θ2 U.

  (** The unit given on the command line: run like an imported one, with
      itself as the whole chain; [B] is the record it ends with. *)
  #[warnings="-cannot-define-projection"]
  Record prog_sem (prg : Cst.prog) (B : builtins) (Θ : gdeps) (U : gunit) : Prop := mk_prog_sem
    { ps_unit : cunit
    ; ps_record : bmap
    ; ps_core : to_core prg = Some ps_unit
    ; ps_run : run_unit (prog_path prg :: nil) ps_unit B ps_record Θ U }.
End Semantics.

(** Outside the section, the judgments also name the file IO [lp], the
    lexer and parser [rd] and the elaborator [tc] they run with. *)
Notation "Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ ch ]⟨ lp ⍮ rd ⍮ tc ⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'" :=
  (run_cmd lp rd tc ch B Rb Θ Ξ c B' Rb' Θ' Ξ').
Notation "Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ ch ]⟨ lp ⍮ rd ⍮ tc ⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'" :=
  (run_cmds lp rd tc ch B Rb Θ Ξ cs B' Rb' Θ' Ξ').


(** ** A Cycle Has No Meaning *)

Lemma load_acyclic : forall load_path read to_core ch B Rb Θ Ξ fp B' Rb' Θ' Ξ',
    In fp ch ->
    gds_lookup Θ fp = None ->
    ~ Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_load fp ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'.
Proof.
  intros * Hin Hnone Hr; inversion Hr; subst; [ congruence | contradiction ].
Qed.

(** ** Running is Deterministic

    Every rule is a check, never a choice, and [load_path], [read] and [to_core]
    are functions; the chain only decides whether a run succeeds.  This is what
    makes a path filed by two runs the same unit, so the merge loses
    nothing. *)

Lemma open_gens_functional : forall Θ Ξ io Γ H its gs1 gs2, ⊢ᵍ Θ ⍮ Ξ ->
    open_gens Θ Ξ io Γ H its gs1 -> open_gens Θ Ξ io Γ H its gs2 -> gs1 = gs2.
Proof.
  intros * Hg [_ _ _ _ H1 _] [_ _ _ _ H2 _].
  destruct (mdenote_functional_all _ _ Hg) as (_ & _ & _ & _ & Hf); exact (Hf _ _ _ _ _ H1 _ H2).
Qed.

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

  (** A unit runs in a frame named by the head of its chain, from no
      binding, so two runs of it agree when their chains have the same
      head. *)
  Theorem run_functional :
    (forall ch B Rb Θ Ξ c B1 Rb1 Θ1 Ξ1, Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ->
       forall ch' B2 Rb2 Θ2 Ξ2, Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch']⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2 ->
         Θ1 = Θ2 /\ Ξ1 = Ξ2 /\ B1 = B2 /\ Rb1 = Rb2) /\
    (forall ch B Rb Θ Ξ cs B1 Rb1 Θ1 Ξ1, Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ->
       forall ch' B2 Rb2 Θ2 Ξ2, Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch']⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2 ->
         Θ1 = Θ2 /\ Ξ1 = Ξ2 /\ B1 = B2 /\ Rb1 = Rb2) /\
    (forall ch u B1 Rb1 Θ1 U1, run_unit ch u B1 Rb1 Θ1 U1 ->
       forall ch' B2 Rb2 Θ2 U2, hd nil ch = hd nil ch' -> run_unit ch' u B2 Rb2 Θ2 U2 ->
         Θ1 = Θ2 /\ U1 = U2 /\ B1 = B2 /\ Rb1 = Rb2).
  Proof.
    (* the second derivation is the last hypothesis; literals, expansions
       and generations are unique *)
    apply run_mut_ind; intros; lazymatch goal with H2 : _ |- _ => inversion H2; subst end;
      try congruence; try solve [ repeat split; congruence ].
    all: repeat match goal with
      | H1 : cmd_lits_ok ?a ?b ?B ?c ?c1, H2 : cmd_lits_ok ?a ?b ?B ?c ?c2 |- _ =>
          assert_fails constr_eq c1 c2; assert (c1 = c2) by (unfold cmd_lits_ok in *; congruence); subst c2
      | H1 : tele_lits_ok ?a ?b ?B ?c ?c1, H2 : tele_lits_ok ?a ?b ?B ?c ?c2 |- _ =>
          assert_fails constr_eq c1 c2; assert (c1 = c2) by (unfold tele_lits_ok in *; congruence); subst c2
      | H1 : open_gens ?a ?b ?o ?G ?E ?is ?g1, H2 : open_gens ?a ?b ?o ?G ?E ?is ?g2,
        HE : _ ⍮ _ ⍮ _ ⊢ᵐ _ ≈ _ |- _ =>
          assert_fails constr_eq g1 g2;
          pose proof (open_gens_functional _ _ _ _ _ _ _ _ (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HE)) H1 H2); subst g2
      end.
    (* an inductive alias: the inductive type its target denotes is one *)
    all: try solve [
      match goal with
      | He : _ ⍮ _ ⍮ _ ⊢ᵉ _, H1 : mdenote _ _ ?G ?H ?R1, H2 : mdenote _ _ ?G ?H ?R2 |- _ =>
          assert_fails constr_eq R1 R2;
          pose proof (proj1 (mdenote_functional_all _ _ (wf_gentry_gctx _ _ _ _ He)) _ _ _ H1 _ H2) as E;
          injection E as <- <- <-; repeat split; auto
      end ].
    (* a builtin binding: the type its target denotes is one, and so is the binding it makes *)
    all: try solve [
      match goal with
      | HE : _ ⍮ _ ⍮ _ ⊢ᵐ ?H ≈ _, H1 : mdenote _ _ ?G ?H ?R1, H2 : mdenote _ _ ?G ?H ?R2 |- _ =>
          assert_fails constr_eq R1 R2;
          pose proof (proj1 (mdenote_functional_all _ _ (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HE))) _ _ _ H1 _ H2) as E;
          injection E as <-; repeat split; congruence
      end ].
    - (* a module: its body *)
      match goal with
      | IH : forall _ _ _ _ _, run_cmds _ _ _ _ _ _ _ _ _ _ -> _, H : run_cmds _ _ _ _ _ _ _ _ _ _ |- _ =>
          destruct (IH _ _ _ _ _ H) as (-> & [= -> ->] & -> & ->)
      end; repeat split; auto.
    - (* a load: the same file, hence the same unit *)
      repeat match goal with
        | H1 : ?f ?x = Some ?a, H2 : ?f ?x = Some ?b |- _ =>
            rewrite H1 in H2; injection H2 as <-
        end.
      match goal with
      | IH : forall _ _ _ _ _, _ -> run_unit _ _ _ _ _ _ -> _, H : run_unit ?c _ _ _ _ _ |- _ =>
          destruct (IH c _ _ _ _ eq_refl H) as (-> & -> & -> & ->)
      end; repeat split; congruence.
    - (* an import: its generated commands *)
      match goal with
      | H1 : gens_run _ _ ?gs _, H2 : gens_run _ _ ?gs _ |- _ =>
          rewrite (gens_run_functional _ _ _ _ H1 _ H2)
      end; repeat split; auto.
    - (* a declaration: its classification *)
      match goal with
      | H1 : cls_cons_in ?a ?b ?r ?c1, H2 : cls_cons_in ?a ?b ?r ?c2 |- _ =>
          assert_fails constr_eq c1 c2; pose proof (cls_cons_in_functional _ _ _ _ _ H1 H2); subst c2
      end; repeat split; auto.
    - (* a sequence: its head, then its tail from the same state *)
      match goal with
      | IH1 : forall _ _ _ _ _, run_cmd _ _ _ _ _ ?c _ _ _ _ -> _, H1 : run_cmd _ _ _ _ _ ?c _ _ _ _ |- _ =>
          destruct (IH1 _ _ _ _ _ H1) as (? & ? & ? & ?); subst
      end.
      match goal with
      | IH2 : forall _ _ _ _ _, run_cmds _ _ _ _ _ ?cs _ _ _ _ -> _, H2 : run_cmds _ _ _ _ _ ?cs _ _ _ _ |- _ =>
          destruct (IH2 _ _ _ _ _ H2) as (? & ? & ? & ?); subst
      end.
      repeat split; auto.
    - (* a unit: its loads, then its body from what they filed *)
      cbn [hd] in *; subst.
      match goal with
      | IH1 : forall _ _ _ _ _, run_cmds _ _ _ nil nil ?is _ _ _ _ -> _, H1 : run_cmds _ _ _ nil nil ?is _ _ _ _ |- _ =>
          destruct (IH1 _ _ _ _ _ H1) as (? & ? & ? & ?); subst
      end.
      repeat match goal with
      | H1 : tele_lits_ok ?a ?b ?B ?c ?c1, H2 : tele_lits_ok ?a ?b ?B ?c ?c2 |- _ =>
          assert_fails constr_eq c1 c2; assert (c1 = c2) by (unfold tele_lits_ok in *; congruence); subst c2
      end.
      match goal with
      | IH2 : forall _ _ _ _ _, run_cmds _ _ _ ?T (gs_push ?mp ?P nil) ?cs _ _ _ _ -> _,
        H2 : run_cmds _ _ _ ?T (gs_push ?mp ?P nil) ?cs _ _ _ _ |- _ =>
          destruct (IH2 _ _ _ _ _ H2) as (? & Heq & ? & ?); injection Heq; intros; subst
      end; repeat split; auto.
  Qed.

  Corollary run_cmd_functional : forall ch ch' B Rb Θ Ξ c B1 Rb1 Θ1 Ξ1 B2 Rb2 Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch']⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2 -> Θ1 = Θ2 /\ Ξ1 = Ξ2 /\ B1 = B2 /\ Rb1 = Rb2.
  Proof. intros * H1 H2; exact (proj1 run_functional _ _ _ _ _ _ _ _ _ _ H1 _ _ _ _ _ H2). Qed.

  Corollary run_cmds_functional : forall ch ch' B Rb Θ Ξ cs B1 Rb1 Θ1 Ξ1 B2 Rb2 Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch']⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2 -> Θ1 = Θ2 /\ Ξ1 = Ξ2 /\ B1 = B2 /\ Rb1 = Rb2.
  Proof. intros * H1 H2; exact (proj1 (proj2 run_functional) _ _ _ _ _ _ _ _ _ _ H1 _ _ _ _ _ H2). Qed.

  Corollary run_unit_functional : forall ch ch' u B1 Rb1 Θ1 U1 B2 Rb2 Θ2 U2,
      hd nil ch = hd nil ch' -> run_unit ch u B1 Rb1 Θ1 U1 -> run_unit ch' u B2 Rb2 Θ2 U2 ->
      Θ1 = Θ2 /\ U1 = U2 /\ B1 = B2 /\ Rb1 = Rb2.
  Proof. intros * Hh H1 H2; exact (proj2 (proj2 run_functional) _ _ _ _ _ _ H1 _ _ _ _ _ Hh H2). Qed.
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

(** An entry checked at its path in the innermost frame keeps the stack
    well formed. *)
Lemma add_entry_wf : forall Θ Ξ x E,
    ⊢ᵍ Θ ⍮ Ξ -> Θ ⍮ Ξ ⍮ qname_in (gs_path Ξ) x ⊢ᵉ E -> gs_fresh x Ξ ->
    ⊢ᵍ Θ ⍮ gs_add x E Ξ.
Proof.
  intros * HΞ HE Hfr.
  destruct Ξ as [| [mp [P Φ1]] Ξ]; [ contradiction |]; cbn in Hfr, HE |- *.
  inversion HΞ as [| | ? ? ? ? ? Hs0 HΦ Hff]; subst.
  apply wf_gstack_cons; [ exact Hs0 | | exact Hff ].
  cbn; econstructor; [ eassumption | exact HE | exact Hfr ].
Qed.

Lemma add_ind_wf : forall Θ Ξ x pv D Φ,
    ⊢ᵍ Θ ⍮ Ξ -> Θ ⍮ Ξ ⍮ qname_in (gs_path Ξ) x ⊢ᵉ ge_ind pv (qname_in (gs_path Ξ) x) D Φ -> gs_fresh x Ξ ->
    ⊢ᵍ Θ ⍮ gs_add x (ge_ind pv (qname_in (gs_path Ξ) x) D Φ) Ξ.
Proof. intros; apply add_entry_wf; assumption. Qed.

(** The name of an entry of a frame is fresh in the body before it. *)
Lemma wf_gstack_ext_fresh : forall Θ mq Δ Φ0 y E Ξ0,
    ⊢ᵍ Θ ⍮ (mq, gu_body Δ (Φ0 ⊳ y ↦ E)) :: Ξ0 -> gm_fresh y Φ0.
Proof.
  intros * Hg; destruct (wf_gstack_cons_inv _ _ _ _ Hg) as (_ & HU & _).
  pose proof (wf_gunit_mod _ _ _ _ HU) as HΦ; cbn in HΦ; inversion HΦ; subst; assumption.
Qed.

Section GrowDeps.
  Variables (Θ Θ' : gdeps).
  Hypothesis Hsub : Θ ⊑ Θ'.

  Lemma global_deps_grow :
    (forall Θ0 Ξ mp E, Θ0 ⍮ Ξ ⍮ mp ⊢ᵉ E -> Θ0 = Θ -> ⊢ᵍ Θ' ⍮ Ξ ->
       gds_lookup Θ' (q_unit mp) = None -> Θ' ⍮ Ξ ⍮ mp ⊢ᵉ E) /\
    (forall Θ0 Ξ mp Δ Φ, Θ0 ⍮ Ξ ⍮ mp ⍮ Δ ⊢ᵍᵐ Φ -> Θ0 = Θ -> ⊢ᵍ Θ' ⍮ Ξ ->
       gds_lookup Θ' (q_unit mp) = None -> Θ' ⍮ Ξ ⍮ mp ⍮ Δ ⊢ᵍᵐ Φ).
  Proof.
    apply global_wf_mut_ind; intros; subst.
    all: try assert (Hb : ⊢ Θ' ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    all: try pose proof (deps_grow _ _ _ Hsub Hb) as (Hc & He & _ & _ & Hx & _ & Hm).
    - econstructor; [ apply He; eassumption | intros; apply He; eauto ].
    - econstructor; auto.
    - econstructor; [ assumption | apply Hx; assumption | apply Hm; assumption ].
    - (* an inductive type, before its members *)
      econstructor; try eassumption; intros; first [ apply Hc | apply He ]; eauto.
    - (* one more member, checked with the entry so far declared *)
      rename H0 into IH, H1 into HM.
      pose proof (IH eq_refl ltac:(assumption) ltac:(assumption)) as HE'.
      pose proof (ctx_wf_gctx _ _ _ (presup_exp_ctx HM)) as Hg0.
      assert (Hg' : ⊢ᵍ Θ' ⍮ (mq, gu_body Δ (Φ0 ⊳ y ↦ ge_ind pv (qname_in mq y) D Φ)) :: Ξ).
      { refine (add_ind_wf _ ((mq, gu_body Δ Φ0) :: Ξ) y pv D Φ _ HE' _); [ assumption |].
        cbn; exact (wf_gstack_ext_fresh _ _ _ _ _ _ _ Hg0). }
      pose proof (deps_grow _ _ _ Hsub (wf_ctx_empty _ _ Hg')) as (_ & He' & _).
      econstructor; [ exact HE' | apply He'; exact HM | assumption ].
    - (* an inductive alias *)
      econstructor; [ assumption | apply Hx; assumption
                    | eapply ind_lookup_gc_sub; [ apply gc_sub_deps; exact Hsub | eassumption ]
                    | assumption | apply He; assumption | apply Hm; assumption ].
    - econstructor; [ assumption | apply Hc; assumption ].
    - match goal with HE : Θ ⍮ _ ⍮ qname_in _ _ ⊢ᵉ _ |- _ => pose proof (wf_gentry_gctx _ _ _ _ HE) as Hg0 end.
      destruct (wf_gstack_cons_inv _ _ _ _ Hg0) as (_ & _ & Hff).
      assert (HΦ : Θ' ⍮ Ξ ⍮ mp ⍮ Δ ⊢ᵍᵐ Φ) by auto.
      econstructor; [ exact HΦ | | assumption ].
      match goal with IH : _ = _ -> ⊢ᵍ _ ⍮ (mp, gu_body Δ Φ) :: Ξ -> _ |- _ => apply IH end;
        [ reflexivity | | assumption ].
      apply wf_gstack_cons; [ assumption | exact HΦ | eapply frame_fresh_grow; eassumption ].
  Qed.

  Lemma gstack_deps_grow : forall Ξ, ⊢ᵍ Θ ⍮ Ξ -> ⊢ᵍ Θ' ⍮ nil ->
      (forall mp U, In (mp, U) Ξ -> gds_lookup Θ' (q_unit mp) = None) -> ⊢ᵍ Θ' ⍮ Ξ.
  Proof.
    induction Ξ as [| [mp U] Ξ IH]; intros HΞ HΘ' Hfr; [ exact HΘ' |].
    destruct (wf_gstack_cons_inv _ _ _ _ HΞ) as (HΞ0 & HU & Hff).
    assert (HΞ' : ⊢ᵍ Θ' ⍮ Ξ) by (apply IH; [ assumption | assumption | intros; eapply Hfr; right; eassumption ]).
    pose proof (Hfr mp U (or_introl eq_refl)) as Hn.
    destruct HU as [Δ Φ -> HΦ].
    apply wf_gstack_cons; [ exact HΞ' | | eapply frame_fresh_grow; eassumption ].
    eapply (proj2 global_deps_grow); eauto.
  Qed.

  (** A filed unit, which sees no frame but its own, named by its path: that
      path must stay unfiled. *)
  Lemma unit_deps_grow : forall fp U,
      ⊢ᵍ Θ' ⍮ nil -> gds_lookup Θ' fp = None ->
      Θ ⍮ nil ⍮ q_abs fp nil ⊢ᵍᵘ U -> Θ' ⍮ nil ⍮ q_abs fp nil ⊢ᵍᵘ U.
  Proof.
    intros * HΘ' Hn [Δ Φ -> HΦ]; apply wf_gunit_intro.
    eapply (proj2 global_deps_grow); [ eassumption | reflexivity | exact HΘ' | exact Hn ].
  Qed.
End GrowDeps.

(** ** Merging Keeps Well-formedness

    A unit of the right side was checked against the units below it there,
    which the merge extends; the sides agree, so the merge has them as they
    are. *)

Theorem merge_wf : forall Θ Θ',
    ⊢ᵍ Θ ⍮ nil -> ⊢ᵍ Θ' ⍮ nil -> gds_agree Θ Θ' -> ⊢ᵍ gds_merge Θ Θ' ⍮ nil.
Proof.
  intros Θ Θ' HΘ; induction Θ' as [| [fp U] Θ' IH]; intros HΘ' Hag; [ exact HΘ |].
  destruct (wf_gstack_file_inv _ _ _ HΘ') as (HΘ0 & HU & Hn).
  assert (Hag0 : gds_agree Θ Θ').
  { intros fq V V' H1 H2; apply (Hag fq V V' H1); cbn.
    destruct (path_beq fq fp) eqn:Hb; [ apply path_beq_true in Hb; subst; congruence | exact H2 ]. }
  assert (HM : ⊢ᵍ gds_merge Θ Θ' ⍮ nil) by auto.
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
    ⊢ᵍ Θ ⍮ Ξ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A -> gs_fresh x Ξ -> ⊢ᵍ Θ ⍮ gs_add x (gs_def b pv Ξ A M) Ξ.
Proof.
  intros * HΞ HM Hfr.
  destruct Ξ as [| [mp [P Φ]] Ξ]; [ contradiction |]; cbn in Hfr |- *.
  inversion HΞ as [| | ? ? ? ? ? Hs0 HΦ Hff]; subst.
  apply wf_gstack_cons; [ exact Hs0 | | exact Hff ].
  destruct (presup_exp_typ HM) as [i HA].
  cbn; econstructor; [ eassumption | unfold gs_def; eapply wf_gentry_def_body; [ exact HA | exact HM ] | exact Hfr ].
Qed.

Lemma add_axiom_wf : forall Θ Ξ x b pv A i,
    ⊢ᵍ Θ ⍮ Ξ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i -> gs_fresh x Ξ -> ⊢ᵍ Θ ⍮ gs_add x (gs_axiom b pv Ξ A) Ξ.
Proof.
  intros * HΞ HA Hfr.
  destruct Ξ as [| [mp [P Φ]] Ξ]; [ contradiction |]; cbn in Hfr |- *.
  inversion HΞ as [| | ? ? ? ? ? Hs0 HΦ Hff]; subst.
  apply wf_gstack_cons; [ exact Hs0 | | exact Hff ].
  cbn; econstructor; [ eassumption | unfold gs_axiom; eapply wf_gentry_def_axiom; exact HA | exact Hfr ].
Qed.

Lemma add_alias_wf : forall Θ Ξ x pv Δ E,
    ⊢ᵍ Θ ⍮ Ξ -> tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    gs_fresh x Ξ -> ⊢ᵍ Θ ⍮ gs_add x (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))) Ξ.
Proof.
  intros * HΞ Htel HΔ HE Hfr.
  destruct Ξ as [| [mp [P Φ]] Ξ]; [ contradiction |]; cbn in Hfr |- *.
  inversion HΞ as [| | ? ? ? ? ? Hs0 HΦ Hff]; subst.
  apply wf_gstack_cons; [ exact Hs0 | | exact Hff ].
  cbn; econstructor; [ eassumption | constructor; assumption | exact Hfr ].
Qed.



Lemma gens_run_wf : forall Θ Ξ gs Ξ', gens_run Θ Ξ gs Ξ' -> ⊢ᵍ Θ ⍮ Ξ -> ⊢ᵍ Θ ⍮ Ξ'.
Proof.
  induction 1; intros HΞ; [ exact HΞ | apply IHgens_run; apply add_def_wf; assumption | |].
  - apply IHgens_run; apply (add_alias_wf _ _ _ _ nil); try assumption; [ constructor |].
    constructor; exact (presup_modexp_eq_ctx H).
  - apply IHgens_run; apply add_entry_wf; assumption.
Qed.

Lemma gens_run_shape : forall Θ Ξ gs Ξ', gens_run Θ Ξ gs Ξ' -> gs_shape Ξ' = gs_shape Ξ.
Proof. induction 1; rewrite ?IHgens_run, ?gs_add_params; reflexivity. Qed.

Lemma gens_run_tl : forall Θ Ξ gs Ξ', gens_run Θ Ξ gs Ξ' -> tl Ξ' = tl Ξ /\ List.length Ξ' = List.length Ξ.
Proof.
  assert (Hadd : forall x E Ξ, tl (gs_add x E Ξ) = tl Ξ /\ List.length (gs_add x E Ξ) = List.length Ξ)
    by (intros ? ? [| [? ?] ?]; split; reflexivity).
  induction 1; [ auto | .. ]; destruct IHgens_run as [Ht Hl]; rewrite Ht, Hl; apply Hadd.
Qed.

(** ** Inductive Types Stay Where They Are Declared

    An entry added to the innermost frame, and a closed module frame filed
    as a member of the frame below it, keep every inductive type that could
    be read before. *)

Lemma ind_lookup_add : forall Θ Ξ x E p D,
    ⊢ᵍ Θ ⍮ Ξ -> gs_fresh x Ξ -> ind_lookup Θ Ξ p = Some D -> ind_lookup Θ (gs_add x E Ξ) p = Some D.
Proof.
  intros * HΞ Hfr Hl.
  destruct Ξ as [| [mq U] Ξ0]; [ contradiction |].
  destruct (wf_gstack_cons_inv _ _ _ _ HΞ) as (_ & [P Ψ -> _] & _).
  cbn in Hfr |- *.
  eapply ind_lookup_gc_sub; [ apply gc_sub_grow; exact Hfr | exact Hl ].
Qed.

Lemma gens_run_ind_lookup : forall Θ Ξ gs Ξ', gens_run Θ Ξ gs Ξ' -> ⊢ᵍ Θ ⍮ Ξ ->
    forall p D, ind_lookup Θ Ξ p = Some D -> ind_lookup Θ Ξ' p = Some D.
Proof.
  induction 1; intros HΞ p0 D0 Hl; [ exact Hl | .. ]; apply IHgens_run; try (apply ind_lookup_add; assumption).
  - apply add_def_wf; assumption.
  - apply (add_alias_wf _ _ _ _ nil); try assumption; [ constructor |].
    constructor; exact (presup_modexp_eq_ctx H).
  - apply add_entry_wf; assumption.
Qed.

(** A module frame, closed: what was read in it is read in the member it
    becomes. *)
Lemma ind_lookup_close : forall Θ Ξ x pv Δ Φ p D,
    ⊢ᵍ Θ ⍮ Ξ -> gs_fresh x Ξ ->
    ind_lookup Θ ((qname_in (gs_path Ξ) x, gu_body Δ Φ) :: Ξ) p = Some D ->
    ind_lookup Θ (gs_add x (ge_body pv Δ Φ) Ξ) p = Some D.
Proof.
  intros * HΞ Hfr Hl.
  destruct (ind_lookup_module _ _ _ _ Hl) as [T Hm].
  apply gc_module_frame in Hm as [(y & ip & -> & Hm) | Hm].
  - destruct Ξ as [| [mq U] Ξ0]; [ contradiction |].
    destruct (wf_gstack_cons_inv _ _ _ _ HΞ) as (_ & [P Ψ -> _] & _).
    cbn [gs_path gs_add gu_params gu_mod gs_tele] in Hm |- *.
    assert (Hp : qname_app (qname_in mq x) (y :: ip) = qname_app mq (x :: y :: ip))
      by (unfold qname_app, qname_in; cbn; rewrite <- List.app_assoc; reflexivity).
    rewrite Hp; rewrite ind_lookup_unfold, gc_module_frame_here; cbn [gu_params gu_mod].
    assert (Hm' : ge_submodule (P ++ gs_tele Ξ0) (ge_body pv Δ Φ) y ip = Some (mr_body T (Some D))) by (cbn; exact Hm).
    rewrite (gm_submodule_ext_here _ Ψ x _ _ _ _ Hm'); reflexivity.
  - apply ind_lookup_add; [ exact HΞ | exact Hfr | exact (ind_lookup_body _ _ _ _ _ Hm) ].
Qed.

(** Read under frames of units not filed: as filed. *)
Lemma ind_lookup_below : forall Θ Ξ p D,
    (forall mp U, In (mp, U) Ξ -> gds_lookup Θ (q_unit mp) = None) ->
    ind_lookup Θ nil p = Some D -> ind_lookup Θ Ξ p = Some D.
Proof.
  intros * Hfr Hl.
  unfold ind_lookup, ind_lookup_u, gc_module, gc_module_u in *; cbn [gs_find_tele] in Hl.
  destruct (gs_find_tele Ξ p) as [[[U ip] T] |] eqn:Hf; [| exact Hl ].
  exfalso.
  assert (Hg : gs_find Ξ p = Some (U, ip)) by (rewrite gs_find_tele_find, Hf; reflexivity).
  destruct (gs_find_unit _ _ _ _ Hg) as (mp & Hin & Hu).
  rewrite <- Hu, (Hfr _ _ Hin) in Hl; discriminate.
Qed.

(** A binding well formed at one state is at another that reads every
    inductive type the first does. *)
Lemma builtins_wf_mono : forall Θ Ξ Θ' Ξ' B,
    (forall p D, ind_lookup Θ Ξ p = Some D -> ind_lookup Θ' Ξ' p = Some D) ->
    builtins_wf Θ Ξ B -> builtins_wf Θ' Ξ' B.
Proof. intros * Hm Hb p Hp; destruct (Hb p Hp) as [D z s Hl Hs Ho]; exact (mk_nat_binding_ok _ _ _ D z s (Hm _ _ Hl) Hs Ho). Qed.

(** A record read under no frame is read under frames of units not filed. *)
Lemma builtins_wf_below : forall Θ Ξ B,
    (forall mp U, In (mp, U) Ξ -> gds_lookup Θ (q_unit mp) = None) ->
    builtins_wf Θ nil B -> builtins_wf Θ Ξ B.
Proof. intros * Hfr; apply builtins_wf_mono; intros; apply ind_lookup_below; assumption. Qed.

(** The records of filed units, each read where the units are filed. *)
Definition bm_wf (Θ : gdeps) (Rb : bmap) : Prop :=
  forall fp BU, bm_lookup Rb fp = Some BU -> builtins_wf Θ nil BU.

Lemma bm_wf_sub : forall Θ Θ' Rb, Θ ⊑ Θ' -> bm_wf Θ Rb -> bm_wf Θ' Rb.
Proof.
  intros * Hs HR fp BU HB; eapply builtins_wf_mono; [| exact (HR _ _ HB) ].
  intros; eapply ind_lookup_gc_sub; [ apply gc_sub_deps; exact Hs | eassumption ].
Qed.

Section WellFormed.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  #[local] Abbreviation run_cmd := (run_cmd load_path read to_core).
  #[local] Abbreviation run_cmds := (run_cmds load_path read to_core).
  #[local] Abbreviation run_unit := (run_unit load_path read to_core).

  Lemma run_chain_fresh :
    (forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       forall fq, In fq ch -> gds_lookup Θ fq = None -> gds_lookup Θ' fq = None) /\
    (forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       forall fq, In fq ch -> gds_lookup Θ fq = None -> gds_lookup Θ' fq = None) /\
    (forall ch u B Rb Θ U, run_unit ch u B Rb Θ U -> forall fq, In fq ch -> gds_lookup Θ fq = None).
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
    (forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> gs_shape Ξ' = gs_shape Ξ) /\
    (forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> gs_shape Ξ' = gs_shape Ξ) /\
    (forall ch u B Rb Θ U, run_unit ch u B Rb Θ U -> True).
  Proof.
    apply run_mut_ind; intros; rewrite ?gs_add_params;
      solve [ congruence | exact I | eapply gens_run_shape; eassumption
            | erewrite gens_run_shape by eassumption; apply gs_add_params ].
  Qed.

  (** A filed unit is what loading its file yields, and its record in [Rb]
      the record that run ends with; [Rb] records only filed units. *)
  #[warnings="-cannot-define-projection"]
  Record canon_entry (Rb : bmap) (fp : path) (U : gunit) : Prop := mk_canon_entry
    { cn_record : builtins
    ; cn_src : string
    ; cn_prog : Cst.prog
    ; cn_unit : cunit
    ; cn_chain : list path
    ; cn_rb : bmap
    ; cn_deps : gdeps
    ; cn_lookup : bm_lookup Rb fp = Some cn_record
    ; cn_load : load_path fp = Some cn_src
    ; cn_read : read cn_src = Some cn_prog
    ; cn_core : to_core cn_prog = Some cn_unit
    ; cn_run : run_unit (fp :: cn_chain) cn_unit cn_record cn_rb cn_deps U }.

  Definition canon (Rb : bmap) (Θ : gdeps) : Prop :=
    (forall fp U, gds_lookup Θ fp = Some U -> canon_entry Rb fp U) /\
    (forall fp BU, bm_lookup Rb fp = Some BU -> gds_lookup Θ fp <> None).

  Definition bm_agree (Rb Rb' : bmap) : Prop :=
    forall fp B B', bm_lookup Rb fp = Some B -> bm_lookup Rb' fp = Some B' -> B = B'.

  (** Two runs of the same file give the same unit and the same record. *)
  Lemma canon_agree : forall Rb1 Θ1 Rb2 Θ2, canon Rb1 Θ1 -> canon Rb2 Θ2 -> gds_agree Θ1 Θ2 /\ bm_agree Rb1 Rb2.
  Proof.
    intros * [H1 H1'] [H2 H2'].
    assert (Hrun : forall fp U1 U2, gds_lookup Θ1 fp = Some U1 -> gds_lookup Θ2 fp = Some U2 ->
                     U1 = U2 /\ bm_lookup Rb1 fp = bm_lookup Rb2 fp).
    { intros fp U1 U2 E1 E2.
      destruct (H1 _ _ E1) as [B1 src prg u ch R1 T1 EB1 Hl Hr Ht Hu].
      destruct (H2 _ _ E2) as [B2 src' prg' u' ch' R2 T2 EB2 Hl' Hr' Ht' Hu'].
      rewrite Hl in Hl'; injection Hl' as <-; rewrite Hr in Hr'; injection Hr' as <-;
        rewrite Ht in Ht'; injection Ht' as <-.
      destruct (run_unit_functional load_path read to_core (fp :: ch) (fp :: ch') _ _ _ _ _ _ _ _ _ eq_refl Hu Hu') as (_ & -> & -> & _).
      split; congruence. }
    split.
    - intros fp U1 U2 E1 E2; exact (proj1 (Hrun _ _ _ E1 E2)).
    - intros fp B1 B2 E1 E2.
      destruct (gds_lookup Θ1 fp) as [U1 |] eqn:F1; [| exfalso; exact (H1' _ _ E1 F1) ].
      destruct (gds_lookup Θ2 fp) as [U2 |] eqn:F2; [| exfalso; exact (H2' _ _ E2 F2) ].
      pose proof (proj2 (Hrun _ _ _ F1 F2)) as E; congruence.
  Qed.

  Lemma canon_nil : canon nil nil.
  Proof. split; intros * H; discriminate H. Qed.

  Lemma canon_file : forall ch fp src prg u BU RbU ΘU U,
      load_path fp = Some src -> read src = Some prg -> to_core prg = Some u ->
      run_unit (fp :: ch) u BU RbU ΘU U -> canon RbU ΘU -> canon ((fp, BU) :: RbU) ((fp, U) :: ΘU).
  Proof.
    intros * Hl Hr Ht Hu [Hc Hc']; split.
    - intros fq V HV; cbn in HV; destruct (path_beq fq fp) eqn:Hb.
      + apply path_beq_true in Hb as ->; injection HV as <-.
        apply (mk_canon_entry _ _ _ BU src prg u ch RbU ΘU); [ cbn; rewrite path_beq_refl; reflexivity | assumption .. ].
      + destruct (Hc _ _ HV) as [B0 src0 prg0 u0 ch0 R0 T0 E0 Hl0 Hr0 Ht0 Hu0].
        apply (mk_canon_entry _ _ _ B0 src0 prg0 u0 ch0 R0 T0); [ cbn; rewrite Hb; exact E0 | assumption .. ].
    - intros fq B0 HB; cbn in HB |- *; destruct (path_beq fq fp); [ discriminate | exact (Hc' _ _ HB) ].
  Qed.

  Lemma canon_merge : forall Rb1 Θ1 Rb2 Θ2, canon Rb1 Θ1 -> canon Rb2 Θ2 -> canon (bm_merge Rb1 Rb2) (gds_merge Θ1 Θ2).
  Proof.
    intros * [H1 H1'] [H2 H2']; split.
    - intros fp U HU; rewrite gds_lookup_merge in HU.
      destruct (gds_lookup Θ1 fp) as [U1 |] eqn:E1.
      + injection HU as <-; destruct (H1 _ _ E1) as [B0 src prg u ch R0 T0 EB Hl Hr Ht Hu].
        apply (mk_canon_entry _ _ _ B0 src prg u ch R0 T0); [ rewrite bm_lookup_merge, EB; reflexivity | assumption .. ].
      + destruct (H2 _ _ HU) as [B0 src prg u ch R0 T0 EB Hl Hr Ht Hu].
        apply (mk_canon_entry _ _ _ B0 src prg u ch R0 T0); [| assumption .. ].
        rewrite bm_lookup_merge; destruct (bm_lookup Rb1 fp) eqn:F; [ exfalso; exact (H1' _ _ F E1) | exact EB ].
    - intros fp B0 HB; rewrite bm_lookup_merge in HB; rewrite gds_lookup_merge.
      destruct (bm_lookup Rb1 fp) eqn:F.
      + destruct (gds_lookup Θ1 fp) eqn:E; [ discriminate | exfalso; exact (H1' _ _ F E) ].
      + destruct (gds_lookup Θ1 fp); [ discriminate | exact (H2' _ _ HB) ].
  Qed.

  Lemma stack_in_shape : forall ch Ξ Ξ', gs_shape Ξ' = gs_shape Ξ -> stack_in ch Ξ -> stack_in ch Ξ'.
  Proof.
    intros * Hs H mp U Hin.
    assert (Hin' : In (mp, gu_params U) (gs_shape Ξ')) by (apply (in_map (fun f => (fst f, gu_params (snd f))) _ _ Hin)).
    rewrite Hs in Hin'; apply in_map_iff in Hin' as ([mq V] & [= -> _] & HV); eapply H; exact HV.
  Qed.

  Theorem run_wf :
    (forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       ⊢ᵍ Θ ⍮ Ξ -> canon Rb Θ -> stack_in ch Ξ -> ⊢ᵍ Θ' ⍮ Ξ' /\ canon Rb' Θ' /\ Θ ⊑ Θ' /\ bt_le B B') /\
    (forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       ⊢ᵍ Θ ⍮ Ξ -> canon Rb Θ -> stack_in ch Ξ -> ⊢ᵍ Θ' ⍮ Ξ' /\ canon Rb' Θ' /\ Θ ⊑ Θ' /\ bt_le B B') /\
    (forall ch u B Rb Θ U, run_unit ch u B Rb Θ U ->
       ⊢ᵍ Θ ⍮ nil /\ canon Rb Θ /\ Θ ⍮ nil ⍮ q_abs (hd nil ch) nil ⊢ᵍᵘ U).
  Proof.
    apply run_mut_dind.
    - (* a definition: the new member is checked against the frame so far *)
      intros ch B Rb Θ Ξ x b pv A M HM Hfr HΞ Hc Hst.
      repeat split; [ apply add_def_wf; assumption | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - (* an axiom: its type is checked against the frame so far *)
      intros ch B Rb Θ Ξ x b pv A i HA Hfr HΞ Hc Hst.
      repeat split; [ eapply add_axiom_wf; eassumption | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - (* a module: its body ends on a frame with the path and parameters it opened with *)
      intros ch B Rb B' Rb' Θ Ξ x pv Δ cs Θ' mp' U Htel HΔ Hfr Hr IH HΞ Hc Hst.
      destruct Ξ as [| [mp [P Φ]] Ξ0]; [ contradiction |]; cbn [gs_fresh gs_path] in Hfr, Hr, IH |- *.
      assert (Hpush : ⊢ᵍ Θ ⍮ gs_push (qname_in mp x) Δ ((mp, gu_mk P Φ) :: Ξ0)).
      { apply wf_gstack_cons; [ exact HΞ | constructor; [ exact Htel | exact HΔ ] |].
        cbn; exists x; split; [ reflexivity | exact Hfr ]. }
      destruct (IH Hpush Hc (stack_in_push _ x Δ _ Hst Hfr)) as (HΞ' & Hc' & Hsub & Hle).
      pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hr) as Hp; cbn in Hp; injection Hp as -> HP.
      split; [| split; [| split ]]; try assumption.
      inversion HΞ' as [| | ? ? ? ? ? Hs1 HU Hff1]; subst.
      inversion Hs1 as [| | ? ? ? ? ? Hs0 HV Hff0]; subst.
      apply wf_gstack_cons; [ exact Hs0 | | exact Hff0 ].
      cbn; econstructor; [ eassumption | constructor; eassumption | exact Hfr ].
    - (* an alias: checked against the frame so far, as a definition is *)
      intros ch B Rb Θ Ξ x pv Δ E Htel HΔ HE Hfr HΞ Hc Hst.
      repeat split; [ apply add_alias_wf; assumption | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - (* a shared unit: its record merged in *)
      intros * _ _ Hm HΞ Hc Hst.
      repeat split; [ exact HΞ | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | exact (proj1 (bt_merge_le _ _ _ Hm)) ].
    - (* a load: the unit is filed on its own, then merged in; the frames are
         of units on the chain, so it files none of them.  What was filed
         before was loaded from the same files, so it agrees with what the
         unit filed. *)
      intros ch B Rb B' Θ Ξ fp src prg u BU RbU ΘU U Hn Hnin Hl Hr Hp Ht Hu IH Hm HΞ Hc Hst.
      destruct IH as (HΘU & HcU & HU); cbn [hd] in HU.
      pose proof (proj2 (proj2 run_chain_fresh) _ _ _ _ _ _ Hu fp ltac:(left; reflexivity)) as HfU.
      assert (Hcf : canon ((fp, BU) :: RbU) ((fp, U) :: ΘU)) by (eapply canon_file; eassumption).
      assert (Hag : gds_agree Θ ((fp, U) :: ΘU)) by exact (proj1 (canon_agree _ _ _ _ Hc Hcf)).
      assert (Hwf : ⊢ᵍ gds_merge Θ ((fp, U) :: ΘU) ⍮ nil)
        by (apply merge_wf; [ eapply wf_gstack_deps; eassumption | apply wf_gstack_file'; assumption | exact Hag ]).
      split; [ eapply gstack_deps_grow; [ apply merge_left | exact HΞ | exact Hwf |] |].
      + intros mq V Hin; pose proof (Hst _ _ Hin) as Hch.
        destruct (gds_lookup (gds_merge _ _) (q_unit mq)) eqn:E; [ exfalso | reflexivity ].
        apply merge_inv in E as [E | E].
        * rewrite (wf_gstack_frames _ _ HΞ _ _ Hin) in E; discriminate.
        * cbn in E; destruct (path_beq (q_unit mq) fp) eqn:Hb.
          -- apply path_beq_true in Hb; rewrite Hb in Hch; contradiction.
          -- rewrite (proj2 (proj2 run_chain_fresh) _ _ _ _ _ _ Hu _ (or_intror Hch)) in E; discriminate.
      + pose proof (canon_merge _ _ _ _ Hc Hcf) as Hcm.
        repeat split; [ exact (proj1 Hcm) | exact (proj2 Hcm) | apply merge_left | exact (proj1 (bt_merge_le _ _ _ Hm)) ].
    - (* an import: what its generated commands make *)
      intros * _ _ Hg HΞ Hc Hst.
      repeat split; [ exact (gens_run_wf _ _ _ _ Hg HΞ) | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - (* a declaration: its entry, checked where it is declared *)
      intros ch B Rb Θ Ξ x pv R cs _ Hfr HE HΞ Hc Hst.
      repeat split; [ apply add_ind_wf; assumption | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - (* a builtin binding: nothing filed, and its binding merged in *)
      intros * _ _ _ _ _ Hb HΞ Hc Hst.
      repeat split; [ exact HΞ | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | exact (bt_bind_nat_le _ _ _ Hb) ].
    - (* an inductive alias: its entry, checked where it is declared *)
      intros * _ _ HE Hfr HΞ Hc Hst.
      repeat split; [ apply add_entry_wf; assumption | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - intros * _ HΞ Hc _; repeat split; [ exact HΞ | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - intros * _ HΞ Hc _; repeat split; [ exact HΞ | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - intros * HΞ Hc _; repeat split; [ exact HΞ | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - intros * _ _ Hr1 IH1 Hr2 IH2 HΞ Hc Hst.
      destruct (IH1 HΞ Hc Hst) as (H1 & Hc1 & Hs1 & Hl1).
      pose proof (stack_in_shape _ _ _ (proj1 run_params _ _ _ _ _ _ _ _ _ _ Hr1) Hst) as Hst1.
      destruct (IH2 H1 Hc1 Hst1) as (H2 & Hc2 & Hs2 & Hl2).
      split; [ exact H2 | split; [ exact Hc2 | split; eauto using gds_sub_trans, bt_le_trans ] ].
    - (* a unit: its imports from nothing, its parameters, then its body in
         the frame named by its path, which nothing it imported filed *)
      intros fp ch B1 Rb1 B2 Rb2 imps P0 P cs Θ1 Θ2 mp U Hi IHi _ Htel HP _ Hb IHb.
      destruct (IHi ltac:(constructor; constructor) canon_nil ltac:(intros ? ? [])) as (H1 & Hc1 & _ & _).
      assert (Hn1 : gds_lookup Θ1 fp = None)
        by exact (proj1 (proj2 run_chain_fresh) _ _ _ _ _ _ _ _ _ _ Hi fp (or_introl eq_refl) eq_refl).
      assert (Hpush : ⊢ᵍ Θ1 ⍮ gs_push (q_abs fp nil) P nil).
      { apply wf_gstack_cons; [ exact H1 | constructor | ].
        - exact Htel.
        - cbn; rewrite app_nil_r; exact HP.
        - cbn; split; [ exact Hn1 | reflexivity ]. }
      destruct (IHb Hpush Hc1 ltac:(intros ? ? [[= <- <-] | []]; left; reflexivity)) as (H2 & Hc2 & _ & _).
      pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hb) as Hp; cbn in Hp; injection Hp as -> _.
      inversion H2; subst.
      split; [ eapply wf_gstack_deps; eassumption | split; [ exact Hc2 | cbn; apply wf_gunit_intro; assumption ] ].
  Qed.

  (** What a load files is well formed, whatever the import checks. *)
  Lemma load_wf : forall ch Rb Θ Ξ fp src prg u BU RbU ΘU U,
      ⊢ᵍ Θ ⍮ Ξ -> canon Rb Θ -> stack_in ch Ξ -> gds_lookup Θ fp = None -> ~ In fp ch ->
      load_path fp = Some src -> read src = Some prg -> to_core prg = Some u ->
      run_unit (fp :: ch) u BU RbU ΘU U ->
      ⊢ᵍ gds_merge Θ ((fp, U) :: ΘU) ⍮ Ξ /\ canon (bm_merge Rb ((fp, BU) :: RbU)) (gds_merge Θ ((fp, U) :: ΘU)) /\
        Θ ⊑ gds_merge Θ ((fp, U) :: ΘU).
  Proof.
    intros * HΞ Hc Hst Hn Hnin Hl Hr Ht Hu.
    destruct (proj2 (proj2 run_wf) _ _ _ _ _ _ Hu) as (HΘU & HcU & HU); cbn [hd] in HU.
    pose proof (proj2 (proj2 run_chain_fresh) _ _ _ _ _ _ Hu fp ltac:(left; reflexivity)) as HfU.
    assert (Hcf : canon ((fp, BU) :: RbU) ((fp, U) :: ΘU)) by (eapply canon_file; eassumption).
    assert (Hag : gds_agree Θ ((fp, U) :: ΘU)) by exact (proj1 (canon_agree _ _ _ _ Hc Hcf)).
    assert (Hwf : ⊢ᵍ gds_merge Θ ((fp, U) :: ΘU) ⍮ nil)
      by (apply merge_wf; [ eapply wf_gstack_deps; eassumption | apply wf_gstack_file'; assumption | exact Hag ]).
    split; [ eapply gstack_deps_grow; [ apply merge_left | exact HΞ | exact Hwf |] |].
    + intros mq V Hin; pose proof (Hst _ _ Hin) as Hch.
      destruct (gds_lookup (gds_merge _ _) (q_unit mq)) eqn:E; [ exfalso | reflexivity ].
      apply merge_inv in E as [E | E].
      * rewrite (wf_gstack_frames _ _ HΞ _ _ Hin) in E; discriminate.
      * cbn in E; destruct (path_beq (q_unit mq) fp) eqn:Hb.
        -- apply path_beq_true in Hb; rewrite Hb in Hch; contradiction.
        -- rewrite (proj2 (proj2 run_chain_fresh) _ _ _ _ _ _ Hu _ (or_intror Hch)) in E; discriminate.
    + split; [ apply canon_merge; assumption | apply merge_left ].
  Qed.

  Corollary load_coherent : forall ch B Rb B' Rb' Θ Ξ fp Θ',
      ⊢ᵍ Θ ⍮ Ξ -> canon Rb Θ -> stack_in ch Ξ ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_load fp ⇝ Θ' ⍮ Ξ ⍮ B' ⍮ Rb' ->
      ⊢ᵍ Θ' ⍮ nil /\ gds_lookup Θ' fp <> None.
  Proof.
    intros * HΞ Hc Hst Hr; destruct (proj1 run_wf _ _ _ _ _ _ _ _ _ _ Hr HΞ Hc Hst) as (H' & _ & _).
    split; [ eapply wf_gstack_deps; eassumption |].
    inversion Hr; subst; [ congruence |].
    (* [fp] was loaded: it is filed on top of what its run filed *)
    rewrite merge_none; cbn; rewrite path_beq_refl; intros [_ ?]; discriminate.
  Qed.

  Corollary prog_sem_wf : forall prg B Θ U,
      prog_sem load_path read to_core prg B Θ U ->
      ⊢ᵍ Θ ⍮ nil /\ Θ ⍮ nil ⍮ q_abs (prog_path prg) nil ⊢ᵍᵘ U.
  Proof.
    intros * [u Rb _ Hu]; destruct (proj2 (proj2 run_wf) _ _ _ _ _ _ Hu) as (? & _ & ?); split; assumption.
  Qed.

  (** ** Builtin Bindings Stay Well Formed

      A binding is made of an inductive type of the right shape where it is
      read ([rc_builtin]), and a run keeps reading it: entries are added,
      module frames are closed into members, units are filed and merged,
      and records are merged ([bt_merge_wf]).  The record of a unit, and
      those of the units it filed, are read where it is filed. *)
  Theorem run_builtins_wf :
    (forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       ⊢ᵍ Θ ⍮ Ξ -> canon Rb Θ -> stack_in ch Ξ -> builtins_wf Θ Ξ B -> bm_wf Θ Rb ->
       builtins_wf Θ' Ξ' B' /\ bm_wf Θ' Rb') /\
    (forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       ⊢ᵍ Θ ⍮ Ξ -> canon Rb Θ -> stack_in ch Ξ -> builtins_wf Θ Ξ B -> bm_wf Θ Rb ->
       builtins_wf Θ' Ξ' B' /\ bm_wf Θ' Rb') /\
    (forall ch u B Rb Θ U, run_unit ch u B Rb Θ U ->
       builtins_wf ((hd nil ch, U) :: Θ) nil B /\ bm_wf ((hd nil ch, U) :: Θ) Rb).
  Proof.
    assert (Hadd : forall Θ Ξ x E B, ⊢ᵍ Θ ⍮ Ξ -> gs_fresh x Ξ -> builtins_wf Θ Ξ B -> builtins_wf Θ (gs_add x E Ξ) B)
      by (intros * HΞ Hfr; apply builtins_wf_mono; intros; apply ind_lookup_add; assumption).
    apply run_mut_ind.
    - intros * _ Hfr HΞ _ _ Hb HR; split; [ apply Hadd; assumption | exact HR ].
    - intros * _ Hfr HΞ _ _ Hb HR; split; [ apply Hadd; assumption | exact HR ].
    - (* a module: read in its frame, then in the member it becomes *)
      intros ch B Rb B' Rb' Θ Ξ x pv Δ cs Θ' mp' U Htel HΔ Hfr Hr IH HΞ Hc Hst Hb HR.
      destruct Ξ as [| [mp [P Φ]] Ξ0]; [ contradiction |]; cbn [gs_fresh gs_path] in Hfr, Hr, IH |- *.
      assert (Hff : frame_fresh Θ ((mp, gu_mk P Φ) :: Ξ0) (qname_in mp x))
        by (cbn; exists x; split; [ reflexivity | exact Hfr ]).
      assert (Hpush : ⊢ᵍ Θ ⍮ gs_push (qname_in mp x) Δ ((mp, gu_mk P Φ) :: Ξ0))
        by (apply wf_gstack_cons; [ exact HΞ | constructor; [ exact Htel | exact HΔ ] | exact Hff ]).
      pose proof (stack_in_push _ x Δ _ Hst Hfr) as Hst'.
      assert (Hb0 : builtins_wf Θ (gs_push (qname_in mp x) Δ ((mp, gu_mk P Φ) :: Ξ0)) B)
        by (eapply builtins_wf_mono; [ intros; eapply ind_lookup_gc_sub; [ apply gc_sub_push; exact Hff | eassumption ] | exact Hb ]).
      destruct (proj1 (proj2 run_wf) _ _ _ _ _ _ _ _ _ _ Hr Hpush Hc Hst') as (HΞ' & _).
      destruct (IH Hpush Hc Hst' Hb0 HR) as [Hb' HR'].
      pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hr) as Hp; cbn in Hp; injection Hp as -> HP.
      destruct (wf_gstack_cons_inv _ _ _ _ HΞ') as (HΞ0 & [Δ' Φ' -> _] & _).
      cbn in HP; subst Δ'; cbn [gu_mod].
      split; [| exact HR' ].
      eapply builtins_wf_mono; [| exact Hb' ].
      intros p0 D0 Hl; apply (ind_lookup_close _ ((mp, gu_mk P Φ) :: Ξ0)); [ exact HΞ0 | exact Hfr | exact Hl ].
    - intros * _ _ _ Hfr HΞ _ _ Hb HR; split; [ apply Hadd; assumption | exact HR ].
    - (* a shared unit: its record, read where it is filed, merged in *)
      intros ch B Rb B' Θ Ξ fp U BU _ HBU Hm HΞ _ _ Hb HR; split; [| exact HR ].
      eapply bt_merge_wf; [ exact Hb | | exact Hm ].
      apply builtins_wf_below; [ exact (wf_gstack_frames _ _ HΞ) | exact (HR _ _ HBU) ].
    - (* a load: the unit's record is read where it is filed, and so is what
         was read before *)
      intros ch B Rb B' Θ Ξ fp src prg u BU RbU ΘU U Hn Hnin Hl Hrd Hpp Ht Hu IH Hm HΞ Hc Hst Hb HR.
      cbn [hd] in IH; destruct IH as [HbU HRU].
      assert (Hrun : Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_load fp ⇝ gds_merge Θ ((fp, U) :: ΘU) ⍮ Ξ ⍮ B' ⍮ bm_merge Rb ((fp, BU) :: RbU))
        by (eapply rc_load; eassumption).
      destruct (proj1 run_wf _ _ _ _ _ _ _ _ _ _ Hrun HΞ Hc Hst) as (HΞ' & _ & Hsub & _).
      pose proof (proj2 (proj2 run_chain_fresh) _ _ _ _ _ _ Hu fp ltac:(left; reflexivity)) as HfU.
      destruct (proj2 (proj2 run_wf) _ _ _ _ _ _ Hu) as (_ & HcU & _).
      assert (Hcf : canon ((fp, BU) :: RbU) ((fp, U) :: ΘU)) by (eapply canon_file; eassumption).
      assert (Hsub' : (fp, U) :: ΘU ⊑ gds_merge Θ ((fp, U) :: ΘU))
        by (apply merge_right; exact (proj1 (canon_agree _ _ _ _ Hc Hcf))).
      assert (HRm : bm_wf (gds_merge Θ ((fp, U) :: ΘU)) (bm_merge Rb ((fp, BU) :: RbU))).
      { intros fq Bq Hq; rewrite bm_lookup_merge in Hq.
        destruct (bm_lookup Rb fq) as [Bq' |] eqn:E.
        - injection Hq as <-; exact (bm_wf_sub _ _ _ Hsub HR _ _ E).
        - assert (HRU' : bm_wf ((fp, U) :: ΘU) ((fp, BU) :: RbU))
            by (intros fr Br Hr0; cbn in Hr0; destruct (path_beq fr fp); [ injection Hr0 as <-; exact HbU | exact (HRU _ _ Hr0) ]).
          exact (bm_wf_sub _ _ _ Hsub' HRU' _ _ Hq). }
      split; [| exact HRm ].
      eapply bt_merge_wf; [| | exact Hm ].
      + eapply builtins_wf_mono; [ intros; eapply ind_lookup_gc_sub; [ apply gc_sub_deps; exact Hsub | eassumption ] | exact Hb ].
      + apply builtins_wf_below; [ exact (wf_gstack_frames _ _ HΞ') |].
        eapply builtins_wf_mono; [ intros; eapply ind_lookup_gc_sub; [ apply gc_sub_deps; exact Hsub' | eassumption ] | exact HbU ].
    - intros * _ _ Hg HΞ _ _ Hb HR; split; [| exact HR ].
      revert Hb; apply builtins_wf_mono; intros; eapply gens_run_ind_lookup; eassumption.
    - intros * _ Hfr _ HΞ _ _ Hb HR; split; [ apply Hadd; assumption | exact HR ].
    - (* a binding: of a type read here *)
      intros ch B Rb B' Θ Ξ H p D z0 s0 _ Hl Hs Ho Hso Hbd _ _ _ Hb HR; split; [| exact HR ].
      eapply bt_merge_wf; [ exact Hb | | exact Hbd ].
      intros p1 Hq; cbn in Hq; injection Hq as <-; exact (mk_nat_binding_ok _ _ _ D z0 s0 Hs Ho Hso).
    - intros * _ _ _ Hfr HΞ _ _ Hb HR; split; [ apply Hadd; assumption | exact HR ].
    - intros; split; assumption.
    - intros; split; assumption.
    - intros; split; assumption.
    - intros * _ _ Hr1 IH1 _ IH2 HΞ Hc Hst Hb HR.
      destruct (proj1 run_wf _ _ _ _ _ _ _ _ _ _ Hr1 HΞ Hc Hst) as (H1 & Hc1 & _).
      pose proof (stack_in_shape _ _ _ (proj1 run_params _ _ _ _ _ _ _ _ _ _ Hr1) Hst) as Hst1.
      destruct (IH1 HΞ Hc Hst Hb HR) as [Hb1 HR1].
      exact (IH2 H1 Hc1 Hst1 Hb1 HR1).
    - (* a unit: its imports, its frame pushed, then filed *)
      intros fp ch B1 Rb1 B2 Rb2 imps P0 P cs Θ1 Θ2 mp U Hi IHi _ Htel HP _ Hbd IHb.
      assert (Hnil : ⊢ᵍ nil ⍮ nil) by (constructor; constructor).
      destruct (proj1 (proj2 run_wf) _ _ _ _ _ _ _ _ _ _ Hi Hnil canon_nil ltac:(intros ? ? [])) as (H1 & Hc1 & _).
      assert (Hn1 : gds_lookup Θ1 fp = None)
        by exact (proj1 (proj2 run_chain_fresh) _ _ _ _ _ _ _ _ _ _ Hi fp (or_introl eq_refl) eq_refl).
      assert (Hff : frame_fresh Θ1 nil (q_abs fp nil)) by (cbn; split; [ exact Hn1 | reflexivity ]).
      assert (Hpush : ⊢ᵍ Θ1 ⍮ gs_push (q_abs fp nil) P nil).
      { apply wf_gstack_cons; [ exact H1 | constructor | exact Hff ].
        - exact Htel.
        - cbn; rewrite app_nil_r; exact HP. }
      destruct (IHi Hnil canon_nil ltac:(intros ? ? []) ltac:(intros p Hp; discriminate) ltac:(intros ? ? Hq; discriminate))
        as [Hb1 HR1].
      assert (Hb1' : builtins_wf Θ1 (gs_push (q_abs fp nil) P nil) B1)
        by (eapply builtins_wf_mono; [ intros; eapply ind_lookup_gc_sub; [ apply gc_sub_push; exact Hff | eassumption ] | exact Hb1 ]).
      destruct (IHb Hpush Hc1 ltac:(intros ? ? [[= <- <-] | []]; left; reflexivity) Hb1' HR1) as [Hb2 HR2].
      pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hbd) as Hp; cbn in Hp; injection Hp as -> _.
      assert (Hn2 : gds_lookup Θ2 fp = None)
        by exact (proj1 (proj2 run_chain_fresh) _ _ _ _ _ _ _ _ _ _ Hbd fp (or_introl eq_refl) Hn1).
      cbn [hd]; split.
      + eapply builtins_wf_mono; [| exact Hb2 ].
        intros p0 D0 Hl0; rewrite ind_lookup_file; exact Hl0.
      + exact (bm_wf_sub _ _ _ (gds_sub_cons _ _ _ Hn2) HR2).
  Qed.

  (** At the end of a program, its record is of a type it reads. *)
  Corollary prog_sem_builtins_wf : forall prg B Θ U,
      prog_sem load_path read to_core prg B Θ U -> builtins_wf ((prog_path prg, U) :: Θ) nil B.
  Proof. intros * [u Rb _ Hu]; exact (proj1 (proj2 (proj2 run_builtins_wf) _ _ _ _ _ _ Hu)). Qed.
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

(** Term judgments and [⊢ᵍ] only read lookups, so they cross [gds_equiv] both
    ways by weakening alone. *)
Lemma equiv_gctx : forall Θ Θ' Ξ, gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ nil -> ⊢ᵍ Θ ⍮ Ξ -> ⊢ᵍ Θ' ⍮ Ξ.
Proof.
  intros * [H H'] HΘ' HΞ; apply (gstack_deps_grow _ _ H _ HΞ HΘ').
  intros mp U Hin; pose proof (wf_gstack_frames _ _ HΞ _ _ Hin) as Hn.
  destruct (gds_lookup Θ' (q_unit mp)) eqn:E; [ rewrite (H' _ _ E) in Hn; discriminate | reflexivity ].
Qed.

Lemma equiv_exp : forall Θ Θ' Ξ Γ M A,
    gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ' ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * [H _] HΞ HM; apply (deps_grow _ _ _ H); [ constructor; exact HΞ | exact HM ].
Qed.

Lemma equiv_ctx : forall Θ Θ' Ξ Γ,
    gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ' ⍮ Ξ ⍮ Γ.
Proof.
  intros * [H _] HΞ HΓ; apply (deps_grow _ _ _ H); [ constructor; exact HΞ | exact HΓ ].
Qed.

Lemma equiv_ext : forall Θ Θ' Ξ Γ Ψ,
    gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ -> Θ' ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ.
Proof.
  intros * [H _] HΞ HΨ; apply (deps_grow _ _ _ H); [ constructor; exact HΞ | exact HΨ ].
Qed.

Lemma equiv_modexp : forall Θ Θ' Ξ Γ E,
    gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E -> Θ' ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E.
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
      (In fp S -> exists ΘU, ΘU ⍮ nil ⍮ q_abs fp nil ⊢ᵍᵘ U /\ ΘU ⊑ Θ' /\ forall x, In x (gds_dom ΘU) -> In x S) /\
      closure_ok S Θ'
  end.

Theorem restrict_wf : forall S Θ, ⊢ᵍ Θ ⍮ nil -> closure_ok S Θ -> ⊢ᵍ gds_restrict S Θ ⍮ nil.
Proof.
  intros S; induction Θ as [| [fp U] Θ IH]; intros Hwf Hc; [ exact Hwf |].
  destruct Hc as [Hc Hcl]; destruct (wf_gstack_file_inv _ _ _ Hwf) as (HΘ & _ & Hn).
  assert (HR : ⊢ᵍ gds_restrict S Θ ⍮ nil) by auto.
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
    (forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       forall x, gds_lookup Θ x <> None -> gds_lookup Θ' x <> None) /\
    (forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       forall x, gds_lookup Θ x <> None -> gds_lookup Θ' x <> None) /\
    (forall ch u B Rb Θ U, run_unit ch u B Rb Θ U -> True).
  Proof.
    apply run_mut_ind; intros; auto.
    intros Ef; apply merge_none in Ef as [Ef _]; contradiction.
  Qed.

  (** The chain only decides whether a load is a cycle, so a run stands under
      any chain avoiding every unit it filed: what justifies sharing a unit
      loaded under one chain with an import under another. *)
  Lemma run_chain_irrel :
    (forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       forall ch', (forall x, In x ch' -> gds_lookup Θ' x = None) -> Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch']⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb') /\
    (forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       forall ch', (forall x, In x ch' -> gds_lookup Θ' x = None) -> Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch']⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb') /\
    (forall ch u B Rb Θ U, run_unit ch u B Rb Θ U ->
       forall ch', (forall x, In x (hd nil ch :: ch') -> gds_lookup Θ x = None) -> run_unit (hd nil ch :: ch') u B Rb Θ U).
  Proof.
    (* what a run filed before its last step it still has after it *)
    assert (Hpre : forall ch B Rb Θ Ξ cs B1 Rb1 Θ1 Ξ1 ch', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ->
              (forall x, In x ch' -> gds_lookup Θ1 x = None) ->
              forall x, In x ch' -> gds_lookup Θ x = None).
    { intros * Hr Hch x Hx; destruct (gds_lookup Θ x) eqn:Ef; [ exfalso | reflexivity ].
      eapply (proj1 (proj2 run_dom_mono)); [ exact Hr | rewrite Ef; discriminate | apply Hch, Hx ]. }
    apply run_mut_ind.
    - intros; constructor; assumption.
    - intros; eapply rc_axiom; eassumption.
    - intros; econstructor; eauto.
    - intros; eapply rc_alias; eassumption.
    - intros; eapply rc_load_filed; eassumption.
    - intros ch B Rb B' Θ Ξ fp src prg u BU RbU ΘU U Hn Hnin Hl Hr Hp Ht Hu IH Hm ch' Hch.
      eapply rc_load; try eassumption.
      + intros Hin; specialize (Hch _ Hin); apply merge_none in Hch as [_ Hf].
        cbn in Hf; rewrite path_beq_refl in Hf; discriminate.
      + apply IH; intros x [<- | Hin].
        * exact (proj2 (proj2 (run_chain_fresh load_path read to_core)) _ _ _ _ _ _ Hu _ (or_introl eq_refl)).
        * specialize (Hch _ Hin); apply merge_none in Hch as [_ Hf].
          cbn in Hf; destruct (path_beq x fp); [ discriminate | exact Hf ].
    - intros; econstructor; eauto.
    - intros; eapply rc_ind; eassumption.
    - intros; eapply rc_builtin; eassumption.
    - intros; eapply rc_ind_alias; eassumption.
    - intros; apply rc_eval_check; assumption.
    - intros; eapply rc_eval_infer; eassumption.
    - intros; constructor.
    - intros * Ha Hl Hr1 IH1 Hr2 IH2 ch' Hch.
      econstructor; [ exact Ha | exact Hl | apply IH1; eapply Hpre; eassumption | auto ].
    - intros fp ch B1 Rb1 B2 Rb2 imps P P1 cs Θ1 Θ2 mp U Hi IHi Hl Htel HP Ha Hb IHb ch' Hch.
      cbn [hd] in *; econstructor; [ apply IHi; eapply Hpre; eassumption | eassumption | assumption | assumption | assumption | auto ].
  Qed.

  Lemma run_tl :
    (forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> tl Ξ' = tl Ξ /\ List.length Ξ' = List.length Ξ) /\
    (forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> tl Ξ' = tl Ξ /\ List.length Ξ' = List.length Ξ) /\
    (forall ch u B Rb Θ U, run_unit ch u B Rb Θ U -> True).
  Proof.
    assert (Hadd : forall x E Ξ, tl (gs_add x E Ξ) = tl Ξ /\ List.length (gs_add x E Ξ) = List.length Ξ)
      by (intros ? ? [| [? ?] ?]; split; reflexivity).
    apply run_mut_ind; intros; auto;
      try (match goal with Hg : gens_run _ (gs_add _ _ _) _ _ |- _ =>
             destruct (gens_run_tl _ _ _ _ Hg) as [-> ->]; apply Hadd end);
      try (eapply gens_run_tl; eassumption); intuition congruence.
  Qed.

  (** Commands keep the stack below the frame they run in, and an empty stack
      empty. *)
  Corollary run_cmds_tail : forall ch B Rb Θ F Ξ cs B' Rb' Θ' Ξ',
      Θ ⍮ F :: Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> exists F', Ξ' = F' :: Ξ.
  Proof.
    intros * H; destruct (proj1 (proj2 run_tl) _ _ _ _ _ _ _ _ _ _ H) as [Ht Hl].
    destruct Ξ' as [| F' Ξ']; cbn in *; [ discriminate | subst; eauto ].
  Qed.

  Corollary run_cmds_empty : forall ch B Rb Θ cs B' Rb' Θ' Ξ', Θ ⍮ nil ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> Ξ' = nil.
  Proof.
    intros * H; destruct (proj1 (proj2 run_tl) _ _ _ _ _ _ _ _ _ _ H) as [_ Hl].
    destruct Ξ'; [ reflexivity | discriminate ].
  Qed.

End Runs.

(** ** Lookups of a Run of a Declaration

    What [IndCommand.rc_ind_con_types] reads off a run: the filed
    declaration and its constructors. *)

Lemma ind_lookup_added : forall Θ Ξ x pv D Φ,
    Ξ <> nil -> ind_lookup Θ (gs_add x (ge_ind pv (qname_in (gs_path Ξ) x) D Φ) Ξ) (qname_in (gs_path Ξ) x) = Some D.
Proof.
  intros * Hn; destruct Ξ as [| [mp U] Ξ0]; [ contradiction |].
  rewrite ind_lookup_unfold; cbn [gs_add gs_path].
  change (qname_in mp x) with (qname_app mp (x :: nil)).
  rewrite gc_module_frame_here; cbn; rewrite String.eqb_refl; reflexivity.
Qed.

Lemma Forall2_in_left : forall {X Y} (Rl : X -> Y -> Prop) l1 l2 a,
    Forall2 Rl l1 l2 -> In a l1 -> exists b, In b l2 /\ Rl a b.
Proof.
  intros * H; induction H as [| a1 b1 l1 l2 Hab H IH]; intros Hin; [ destruct Hin |].
  destruct Hin as [<- | Hin]; [ exists b1; split; [ left; reflexivity | exact Hab ] |].
  destruct (IH Hin) as (b & Hb & Hr); exists b; split; [ right; exact Hb | exact Hr ].
Qed.

Lemma cons_lookup_nodup : forall cs c gs, NoDup (map fst cs) -> In (c, gs) cs -> cons_lookup cs c = Some gs.
Proof.
  induction cs as [| [c' gs'] cs IH]; intros * Hnd Hin; [ destruct Hin |]; destruct Hin as [[= <- <-] | Hin]; cbn.
  - rewrite String.eqb_refl; reflexivity.
  - inversion Hnd as [| ? ? Hn Hnd']; subst.
    destruct (String.eqb_spec c c') as [<- |]; [| apply IH; assumption ].
    exfalso; apply Hn, (in_map fst _ (c, gs)), Hin.
Qed.
