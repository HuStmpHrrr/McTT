(** * The Static Semantics of Commands

    A command moves the global state: the global context [Θ] and the frames
    [F] of the modules open around it ([frame]).  A command is checked in the
    context [fctx Γimp F]: the frames' self slots and parameters over the
    unit's leading opens [Γimp].

    - A definition adds an entry to the innermost frame.  An [abstract]
      one also files a constant: its type and body generalized over the
      whole context, sealed; the entry is that constant applied to the
      context's assumptions.
    - A module opens a frame for its body, which becomes a submodule entry
      when the body ends.
    - [cc_load] loads the unit it names, if it is not filed yet, by running
      that unit's own commands from nothing, and merges what that filed
      ([gc_merge]); the chain of units whose loading is in progress is what
      rules a cycle out.
    - [cc_open] declares the names its items generate ([Imports]) as entries
      of the frame.

    Every command is checked for privacy as written, then expanded, which
    turns the local opens of the bodies it contains into entries.  A unit's
    leading loads and opens run before its parameters, the opens declaring
    the context [Γimp] the parameters are read in; [Γimp] is substituted away
    when the unit is filed ([imp_sub]).  A leading open exports nothing: its
    items are all private. *)

From Stdlib Require Import List String PeanoNat Bool Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Command Imports.
From Mctt.Core.Syntactic.System Require Import Definitions Lemmas Structural GlobalPresup MemberWf.
From Mctt.Core.Syntactic.System Require Export Privacy.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.

(** ** Frames *)

Definition fr_add (x : string) (E : gentry) (f : frame) : frame :=
  fr_mk (fr_chain f) (fr_params f) (fr_body f ⊳ x ↦ E).

Definition fr_set (Φ : gmod) (f : frame) : frame := fr_mk (fr_chain f) (fr_params f) Φ.

(** The assumptions of a context, as variables of it, outermost first: what a
    constant generalized over the context is applied to. *)
Fixpoint ctx_args (Γ : ctx) : list exp :=
  match Γ with
  | nil => nil
  | ce_ass _ :: Γ' => map (fun N => N[↑]ʷ) (ctx_args Γ') ++ a_var 0 :: nil
  | _ :: Γ' => map (fun N => N[↑]ʷ) (ctx_args Γ')
  end.

(** The constant an [abstract] definition [x] of the frame at chain [ch] of
    the unit [fp] is filed as. *)
Definition abs_name (fp : path) (ch : list string) (x : string) : qname := q_abs fp (ch ++ x :: nil).

(** ** Generated Items in a Frame

    The definitions and aliases an open generates, declared in the frame in
    order, with the premises of [rc_def] and [rc_alias]: what the open
    references is checked once, as written ([rcs_cons]), and a generated type
    is not written, so nothing here checks privacy. *)

Inductive gens_run (Θ : gctx) (Γimp : ctx) : list frame -> list igen -> list frame -> Prop :=
| gr_nil : forall F, gens_run Θ Γimp F nil F
| gr_def : forall f F d pv A M gs F',
    Θ ⍮ fctx Γimp (f :: F) ⊢ M : A -> gm_fresh d (fr_body f) ->
    gens_run Θ Γimp (fr_add d (ge_def pv A (Some M)) f :: F) gs F' ->
    gens_run Θ Γimp (f :: F) (ig_def d pv A M :: gs) F'
| gr_alias : forall f F d pv E gs F',
    Θ ⍮ fctx Γimp (f :: F) ⊢ᵐ E ≈ E -> gm_fresh d (fr_body f) ->
    gens_run Θ Γimp (fr_add d (ge_mod pv (gu_mk nil (md_alias E))) f :: F) gs F' ->
    gens_run Θ Γimp (f :: F) (ig_alias d pv E :: gs) F'.

(** The alias an open declares first, if any. *)
Definition alias_gens (E : modexp) (oz : option string) : list igen :=
  match oz with
  | Some z => ig_alias z true E :: nil
  | None => nil
  end.

(** ** Leading Opens

    A leading open declares one entry of [Γimp]: a module slot holding an
    alias of its target, from which the names it declares are read, like
    members of a body from its self slot.  Its items are checked as any
    open's are ([open_gen_ok]), reading from the slot, and are private: it
    exports nothing. *)

Definition lead_slot (E : modexp) : centry := ce_mod (gu_mk nil (md_alias E)).

Definition lead_items_ok (its : list iitem) : Prop := List.Forall (fun it => snd it = true) its.

(** No assumption: what [Γimp] holds is substituted away when the unit is
    filed. *)
Definition imp_ok (Γ : ctx) : Prop := List.Forall (fun e => forall A, e <> ce_ass A) Γ.

Fixpoint imp_sub (Γ : ctx) : sub :=
  match Γ with
  | nil => sb_id
  | e :: Γ' =>
      (* Computed once for both uses. *)
      let σ := imp_sub Γ' in
      match e with
      | ce_def _ M => sb_extend σ (se_exp M[σ])
      | ce_mod U => sb_extend σ (se_mod (me_lit U[σ]ᵘ))
      | ce_ass _ => sb_extend σ (se_exp exp_junk)
      end
  end.

(** ** Merging the Global Context of a Loaded Unit

    A unit is run from nothing, so it sees only what its own loads file.
    What it filed is merged into the importer's global context: each of its
    declarations the importer does not have yet is put on top, in order. *)

Definition gd_has (Θ : gctx) (d : gdecl) : bool :=
  match d with
  | gd_unit fp _ => match gc_unit Θ fp with Some _ => true | None => false end
  | gd_const c _ _ _ => match gc_const Θ c with Some _ => true | None => false end
  end.

Definition gc_merge (Θ ΘL : gctx) : gctx := filter (fun d => negb (gd_has Θ d)) ΘL ++ Θ.

(** Shared declarations agree. *)
Definition gc_agree (Θ ΘL : gctx) : Prop :=
  (forall fp U U', gc_unit Θ fp = Some U -> gc_unit ΘL fp = Some U' -> U = U') /\
  (forall qn r r', gc_const Θ qn = Some r -> gc_const ΘL qn = Some r' -> r = r').

Lemma gc_unit_app : forall Θ1 Θ2 fp,
    gc_unit (Θ1 ++ Θ2) fp = match gc_unit Θ1 fp with Some U => Some U | None => gc_unit Θ2 fp end.
Proof.
  induction Θ1 as [| [fq U | c A M b] Θ1 IH]; intros; cbn; [ reflexivity | | apply IH ].
  destruct (path_beq fp fq); [ reflexivity | apply IH ].
Qed.

Lemma gc_const_app : forall Θ1 Θ2 qn,
    gc_const (Θ1 ++ Θ2) qn = match gc_const Θ1 qn with Some r => Some r | None => gc_const Θ2 qn end.
Proof.
  induction Θ1 as [| [fq U | c A M b] Θ1 IH]; intros; cbn; [ reflexivity | apply IH |].
  destruct (qname_beq qn c); [ reflexivity | apply IH ].
Qed.

Lemma gc_unit_filter : forall Θ ΘL fp,
    gc_unit (filter (fun d => negb (gd_has Θ d)) ΘL) fp =
    match gc_unit Θ fp with Some _ => None | None => gc_unit ΘL fp end.
Proof.
  intros Θ; induction ΘL as [| [fq U | c A M b] ΘL IH]; intros; cbn.
  - destruct (gc_unit Θ fp); reflexivity.
  - destruct (path_beq fp fq) eqn:E.
    + apply path_beq_true in E; subst fq.
      destruct (gc_unit Θ fp) eqn:Ef; cbn; [ rewrite (IH fp), Ef; reflexivity | rewrite path_beq_refl; reflexivity ].
    + destruct (gc_unit Θ fq); cbn; [ exact (IH fp) |]; rewrite E; exact (IH fp).
  - destruct (gc_const Θ c); cbn; exact (IH fp).
Qed.

Lemma gc_const_filter : forall Θ ΘL qn,
    gc_const (filter (fun d => negb (gd_has Θ d)) ΘL) qn =
    match gc_const Θ qn with Some _ => None | None => gc_const ΘL qn end.
Proof.
  intros Θ; induction ΘL as [| [fq U | c A M b] ΘL IH]; intros; cbn.
  - destruct (gc_const Θ qn); reflexivity.
  - destruct (gc_unit Θ fq); cbn; exact (IH qn).
  - destruct (qname_beq qn c) eqn:E.
    + apply qname_beq_true in E; subst c.
      destruct (gc_const Θ qn) eqn:Ef; cbn; [ rewrite (IH qn), Ef; reflexivity | rewrite qname_beq_refl; reflexivity ].
    + destruct (gc_const Θ c); cbn; [ exact (IH qn) |]; rewrite E; exact (IH qn).
Qed.

Lemma gc_unit_merge : forall Θ ΘL fp,
    gc_unit (gc_merge Θ ΘL) fp = match gc_unit Θ fp with Some U => Some U | None => gc_unit ΘL fp end.
Proof.
  intros; unfold gc_merge; rewrite gc_unit_app, gc_unit_filter.
  destruct (gc_unit Θ fp); [ reflexivity | destruct (gc_unit ΘL fp); reflexivity ].
Qed.

Lemma gc_const_merge : forall Θ ΘL qn,
    gc_const (gc_merge Θ ΘL) qn = match gc_const Θ qn with Some r => Some r | None => gc_const ΘL qn end.
Proof.
  intros; unfold gc_merge; rewrite gc_const_app, gc_const_filter.
  destruct (gc_const Θ qn); [ reflexivity | destruct (gc_const ΘL qn); reflexivity ].
Qed.

Lemma gc_merge_sub_left : forall Θ ΘL, Θ ⊑ gc_merge Θ ΘL.
Proof.
  intros; split; intros * H; [ rewrite gc_unit_merge, H | rewrite gc_const_merge, H ]; reflexivity.
Qed.

Lemma gc_merge_sub_right : forall Θ ΘL, gc_agree Θ ΘL -> ΘL ⊑ gc_merge Θ ΘL.
Proof.
  intros * [HU HC]; split; intros * H.
  - rewrite gc_unit_merge; destruct (gc_unit Θ fp) eqn:E; [ f_equal; eapply HU; eassumption | exact H ].
  - rewrite gc_const_merge; destruct (gc_const Θ qn) eqn:E; [ f_equal; eapply HC; eassumption | exact H ].
Qed.

Lemma gc_merge_cons : forall Θ d ΘL,
    gc_merge Θ (d :: ΘL) = if gd_has Θ d then gc_merge Θ ΘL else d :: gc_merge Θ ΘL.
Proof. intros; unfold gc_merge; cbn; destruct (gd_has Θ d); reflexivity. Qed.

Lemma gc_agree_tail : forall Θ d ΘL, ⊢g d :: ΘL -> gc_agree Θ (d :: ΘL) -> gc_agree Θ ΘL.
Proof.
  intros * Hg [HU HC]; destruct (wf_gctx_cons_inv _ _ Hg) as [_ Hd].
  split; intros * H1 H2.
  - eapply HU; [ exact H1 |]; destruct d as [fq V | c A M b]; cbn; [| exact H2 ].
    destruct (path_beq fp fq) eqn:E; [| exact H2 ].
    apply path_beq_true in E; subst; destruct Hd as [_ Hn]; congruence.
  - eapply HC; [ exact H1 |]; destruct d as [fq V | c A M b]; cbn; [ exact H2 |].
    destruct (qname_beq qn c) eqn:E; [| exact H2 ].
    apply qname_beq_true in E; subst; destruct Hd as [_ Hn]; congruence.
Qed.

Theorem gc_merge_wf : forall Θ ΘL, ⊢g Θ -> ⊢g ΘL -> gc_agree Θ ΘL -> ⊢g gc_merge Θ ΘL.
Proof.
  intros Θ ΘL HΘ; induction ΘL as [| d ΘL IH]; intros Hg Ha; [ exact HΘ |].
  pose proof (gc_agree_tail _ _ _ Hg Ha) as Ha'.
  destruct (wf_gctx_cons_inv _ _ Hg) as [Hg' Hd].
  specialize (IH Hg' Ha').
  assert (He : Emb ΘL (gc_merge Θ ΘL)) by (constructor; [ exact IH | apply gc_merge_sub_right, Ha' ]).
  rewrite gc_merge_cons; destruct (gd_has Θ d) eqn:Eh; [ exact IH |].
  destruct d as [fp U | c A M b]; cbn in Eh; destruct Hd as [Hd Hn].
  - constructor; [ exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (emb_preserves_wf _ _ He)))))) _ _ _ Hd) |].
    rewrite gc_unit_merge; destruct (gc_unit Θ fp); [ discriminate | exact Hn ].
  - assert (Hn' : gc_const (gc_merge Θ ΘL) c = None)
      by (rewrite gc_const_merge; destruct (gc_const Θ c); [ discriminate | exact Hn ]).
    destruct M as [M |]; cbn in Hd.
    + constructor; [ exact (proj1 (proj2 (emb_preserves_wf _ _ He)) _ _ _ Hd) | exact Hn' ].
    + destruct Hd as [i Hd].
      econstructor; [ exact (proj1 (proj2 (emb_preserves_wf _ _ He)) _ _ _ Hd) | exact Hn' ].
Qed.

Section Semantics.
  (** File IO: the contents of the unit at a path, if there is one. *)
  Variable load_path : path -> option string.
  (** Lexing and parsing.  The lexer is OCaml, so this is a parameter too. *)
  Variable read : string -> option Cst.prog.
  (** Elaboration into core commands, which needs no filed unit. *)
  Variable to_core : Cst.prog -> option cunit.

  (** ** Running

      [run_cmd ch fp Γimp Θ F c Θ' F']: [ch] is the chain of units being
      loaded, [fp] the unit running [c], first in it. *)

  Inductive run_cmd : list path -> path -> ctx -> gctx -> list frame -> ccmd -> gctx -> list frame -> Prop :=
  | rc_def : forall ch fp Γimp Θ f F x pv A M,
      Θ ⍮ fctx Γimp (f :: F) ⊢ M : A ->
      gm_fresh x (fr_body f) ->
      run_cmd ch fp Γimp Θ (f :: F) (cc_def x true pv A (Some M)) Θ (fr_add x (ge_def pv A (Some M)) f :: F)
  (** An [abstract] definition: the constant, then the member defined as it. *)
  | rc_abs : forall ch fp Γimp Θ f F x pv A M,
      Θ ⍮ fctx Γimp (f :: F) ⊢ M : A ->
      gm_fresh x (fr_body f) ->
      gc_const Θ (abs_name fp (fr_chain f) x) = None ->
      run_cmd ch fp Γimp Θ (f :: F) (cc_def x false pv A (Some M))
        (gd_const (abs_name fp (fr_chain f) x) (ctx_pi (fctx Γimp (f :: F)) A) (Some (ctx_fn (fctx Γimp (f :: F)) M)) false :: Θ)
        (fr_add x (ge_def pv A (Some (apps (a_const (abs_name fp (fr_chain f) x)) (ctx_args (fctx Γimp (f :: F)))))) f :: F)
  (** An axiom: a constant without a body, then the member defined as it. *)
  | rc_ax : forall ch fp Γimp Θ f F x b pv A i,
      Θ ⍮ fctx Γimp (f :: F) ⊢ A : Type@i ->
      gm_fresh x (fr_body f) ->
      gc_const Θ (abs_name fp (fr_chain f) x) = None ->
      run_cmd ch fp Γimp Θ (f :: F) (cc_def x b pv A None)
        (gd_const (abs_name fp (fr_chain f) x) (ctx_pi (fctx Γimp (f :: F)) A) None false :: Θ)
        (fr_add x (ge_def pv A (Some (apps (a_const (abs_name fp (fr_chain f) x)) (ctx_args (fctx Γimp (f :: F)))))) f :: F)
  (** The body runs in a frame of its own, the frames outside it as they
      were; it then becomes the member [x]. *)
  | rc_mod : forall ch fp Γimp Θ f F x pv Δ cs Θ' g,
      tele_ass Δ ->
      ⊢ Θ ⍮ Δ ++ fctx Γimp (f :: F) ->
      gm_fresh x (fr_body f) ->
      run_cmds ch fp Γimp Θ (fr_mk (fr_chain f ++ x :: nil) Δ ⋄ :: f :: F) cs Θ' (g :: f :: F) ->
      run_cmd ch fp Γimp Θ (f :: F) (cc_mod x pv Δ cs) Θ' (fr_add x (ge_mod pv (gu_body Δ (fr_body g))) f :: F)
  | rc_alias : forall ch fp Γimp Θ f F x pv Δ E,
      tele_ass Δ ->
      Θ ⍮ fctx Γimp (f :: F) ⊢ˣ Δ ≈ Δ ->
      Θ ⍮ Δ ++ fctx Γimp (f :: F) ⊢ᵐ E ≈ E ->
      gm_fresh x (fr_body f) ->
      run_cmd ch fp Γimp Θ (f :: F) (cc_alias x pv Δ E) Θ (fr_add x (ge_mod pv (gu_mk Δ (md_alias E))) f :: F)
  | rc_load : forall ch fp Γimp Θ F fq Θ',
      run_load ch Θ fq Θ' ->
      run_cmd ch fp Γimp Θ F (cc_load fq) Θ' F
  (** An open checks its target, and declares its alias and the items it
      generates in this frame. *)
  | rc_open : forall ch fp Γimp Θ f F E oz its gs F',
      Θ ⍮ fctx Γimp (f :: F) ⊢ᵐ E ≈ E ->
      open_gen_ok Θ (fctx Γimp (f :: F)) E oz
        (fctx Γimp (fr_set (open_alias (fr_body f) E oz) f :: F)) (open_src E oz) its gs ->
      gens_run Θ Γimp (f :: F) (alias_gens E oz ++ gs) F' ->
      run_cmd ch fp Γimp Θ (f :: F) (cc_open E oz its) Θ F'
  (** An [eval] changes nothing, but must type-check where it stands. *)
  | rc_eval_check : forall ch fp Γimp Θ F M A,
      Θ ⍮ fctx Γimp F ⊢ M : A ->
      run_cmd ch fp Γimp Θ F (cc_eval M (Some A)) Θ F
  | rc_eval_infer : forall ch fp Γimp Θ F M A,
      Θ ⍮ fctx Γimp F ⊢ M : A ->
      run_cmd ch fp Γimp Θ F (cc_eval M None) Θ F

  with run_cmds : list path -> path -> ctx -> gctx -> list frame -> list ccmd -> gctx -> list frame -> Prop :=
  | rcs_nil : forall ch fp Γimp Θ F, run_cmds ch fp Γimp Θ F nil Θ F
  (** Each command is checked for privacy as written, then expanded
      ([Imports]) before it runs. *)
  | rcs_cons : forall ch fp Γimp Θ F c c' cs Θ1 F1 Θ2 F2,
      acc_ok Θ (cmd_refs (fctx_tabs fp Γimp F) c) ->
      cmd_xp_ok Θ (fctx Γimp F) c c' ->
      run_cmd ch fp Γimp Θ F c' Θ1 F1 ->
      run_cmds ch fp Γimp Θ1 F1 cs Θ2 F2 ->
      run_cmds ch fp Γimp Θ F (c :: cs) Θ2 F2

  (** [run_load ch Θ fq Θ']: loading the unit [fq].  A unit filed already is
      shared, not reloaded.  Otherwise its file is run, with itself added to
      the chain, from nothing, so that it sees only what it loads itself; it
      is filed on top of what it filed, and that is merged into [Θ].  A unit
      already in the chain is still being loaded, so loading it is a cycle,
      and no rule applies. *)
  with run_load : list path -> gctx -> path -> gctx -> Prop :=
  | rl_filed : forall ch Θ fq U,
      gc_unit Θ fq = Some U ->
      run_load ch Θ fq Θ
  | rl_run : forall ch Θ fq src prg u ΘU U,
      gc_unit Θ fq = None ->
      ~ In fq ch ->
      load_path fq = Some src ->
      read src = Some prg ->
      prog_path prg = fq ->
      to_core prg = Some u ->
      run_unit (fq :: ch) nil u ΘU U ->
      gc_unit ΘU fq = None ->
      run_load ch Θ fq (gc_merge Θ (gd_unit fq U :: ΘU))

  (** [run_lead ch Θ Γimp c Θ' Γimp']: a leading load or open. *)
  with run_lead : list path -> gctx -> ctx -> ccmd -> gctx -> ctx -> Prop :=
  | rd_load : forall ch Θ Γimp fq Θ',
      run_load ch Θ fq Θ' ->
      run_lead ch Θ Γimp (cc_load fq) Θ' Γimp
  | rd_open : forall ch Θ Γimp E oz its gs,
      lead_items_ok its ->
      Θ ⍮ Γimp ⊢ᵐ E ≈ E ->
      open_gen_ok Θ Γimp E oz (lead_slot E :: Γimp) (me_var 0) its gs ->
      run_lead ch Θ Γimp (cc_open E oz its) Θ (lead_slot E :: Γimp)

  with run_leads : list path -> gctx -> ctx -> list ccmd -> gctx -> ctx -> Prop :=
  | rds_nil : forall ch Θ Γimp, run_leads ch Θ Γimp nil Θ Γimp
  | rds_cons : forall ch Θ Γimp c c' cs Θ1 Γ1 Θ2 Γ2,
      acc_ok Θ (cmd_refs (ctx_tabs Γimp) c) ->
      cmd_xp_ok Θ Γimp c c' ->
      run_lead ch Θ Γimp c' Θ1 Γ1 ->
      run_leads ch Θ1 Γ1 cs Θ2 Γ2 ->
      run_leads ch Θ Γimp (c :: cs) Θ2 Γ2

  (** [run_unit (fp :: ch) Θ0 u Θ U]: the unit [fp], at the head of the
      chain, runs from [Θ0].  Its leading loads and opens run first, then its
      parameters are expanded and checked in what they declared, then its
      body runs in its own frame.  [Θ] is what it filed, [U] the unit, its
      leading opens substituted away. *)
  with run_unit : list path -> gctx -> cunit -> gctx -> gunit -> Prop :=
  | ru_intro : forall fp ch Θ0 leads P P' cs Θ1 Γimp Θ2 f,
      run_leads (fp :: ch) Θ0 nil leads Θ1 Γimp ->
      tele_xp_ok Θ1 (ctx_skel Γimp) P P' ->
      tele_ass P' ->
      acc_ok Θ1 (tele_refs (ctx_tabs Γimp) P) ->
      ⊢ Θ1 ⍮ fctx Γimp (fr_mk nil P' gm_nil :: nil) ->
      run_cmds (fp :: ch) fp Γimp Θ1 (fr_mk nil P' gm_nil :: nil) cs Θ2 (f :: nil) ->
      run_unit (fp :: ch) Θ0 (leads, P, cs) Θ2 (gu_body P' (fr_body f))[imp_sub Γimp]ᵘ.

  (** The unit given on the command line: run like an imported one, from
      nothing, with itself as the whole chain. *)
  Definition prog_sem (prg : Cst.prog) (Θ : gctx) (U : gunit) : Prop :=
    exists u, to_core prg = Some u /\ run_unit (prog_path prg :: nil) nil u Θ U.
End Semantics.

Scheme run_cmd_mind := Minimality for run_cmd Sort Prop
with run_cmds_mind := Minimality for run_cmds Sort Prop
with run_load_mind := Minimality for run_load Sort Prop
with run_lead_mind := Minimality for run_lead Sort Prop
with run_leads_mind := Minimality for run_leads Sort Prop
with run_unit_mind := Minimality for run_unit Sort Prop.
Combined Scheme run_mut_ind from run_cmd_mind, run_cmds_mind, run_load_mind, run_lead_mind,
  run_leads_mind, run_unit_mind.

(** ** A Cycle Has No Meaning *)

Lemma load_acyclic : forall load_path read to_core ch Θ fq Θ',
    In fq ch ->
    gc_unit Θ fq = None ->
    ~ run_load load_path read to_core ch Θ fq Θ'.
Proof.
  intros * Hin Hnone Hr; inversion Hr; subst; [ congruence | contradiction ].
Qed.

(** ** A Constant Applied to its Context

    A closed term of the type generalized over a context, applied to the
    context's assumptions, has the type in the context: the definitions and
    module slots the generalization [let]-bound are equal to the context's
    own, by [δ]. *)

Lemma apps_map_wk : forall args f φ, exp_scoped 0 f -> apps f (map (fun N => N[φ]ʷ) args) = (apps f args)[φ]ʷ.
Proof. intros * Hf; rewrite apps_wk, exp_closed_wk by assumption; reflexivity. Qed.

Lemma wf_apps_ctx_args : forall Θ Γ A f i,
    ⊢ Θ ⍮ Γ -> Θ ⍮ Γ ⊢ A : Type@i -> Θ ⍮ ⋅ ⊢ f : ctx_pi Γ A -> exp_scoped 0 f ->
    Θ ⍮ Γ ⊢ apps f (ctx_args Γ) : A.
Proof.
  intros Θ Γ; induction Γ as [| [B | B N | U] Γ IH]; intros * HΓ HA Hf Hs; cbn [ctx_pi ctx_args] in *; [ exact Hf | | |].
  - (* an assumption: the argument is the variable *)
    assert (HΓ' : ⊢ Θ ⍮ Γ) by mauto 2.
    destruct (ctx_decomp_right HΓ) as [j HB].
    assert (HP : Θ ⍮ Γ ⊢ Π B A : Type@(max j i)) by (eapply wf_pi_max; eassumption).
    specialize (IH _ _ _ HΓ' HP Hf Hs).
    rewrite apps_snoc, apps_map_wk by assumption.
    assert (Hw : Θ ⍮ Γ ▹ B ⊢w ↑ : Γ) by mauto 2.
    assert (H1 : Θ ⍮ Γ ▹ B ⊢ (apps f (ctx_args Γ))[↑]ʷ : Π B[↑]ʷ A[wk_q ↑]ʷ) by exact (wk_preserves_exp _ _ _ _ _ _ IH Hw).
    assert (HB' : Θ ⍮ Γ ▹ B ⊢ B[↑]ʷ : Type@j) by (eapply wk_preserves_typ; eassumption).
    assert (HA' : Θ ⍮ Γ ▹ B ▹ B[↑]ʷ ⊢ A[wk_q ↑]ʷ : Type@i) by (eapply wk_preserves_typ; [ eassumption | eapply wf_wk_q'; eassumption ]).
    assert (H2 : Θ ⍮ Γ ▹ B ⊢ (apps f (ctx_args Γ))[↑]ʷ $ #0 : A[wk_q ↑]ʷ[Id,,#0])
      by (eapply wf_app; [ eapply lift_exp_max_left; exact HB' | eapply lift_exp_max_right; exact HA' | exact H1 | mauto 3 ]).
    assert (Θ ⍮ Γ ▹ B ⊢ A[wk_q ↑]ʷ[Id,,#0] ≈ A : Type@i).
    { rewrite <- (exp_wk_q_shift_single A) at 2.
      eapply (sub_eq_preserves_typ _ _ _ _ _ _ i); [ eassumption | eapply wf_sub_eq_var_zero; eassumption ]. }
    eapply wf_conv; eassumption.
  - (* a definition: the [let] the type was generalized by is [δ] *)
    assert (HΓ' : ⊢ Θ ⍮ Γ) by mauto 2.
    destruct (ctx_decomp_def_typ HΓ) as [j HB].
    pose proof (ctx_decomp_def_body HΓ) as HN.
    assert (HL : Θ ⍮ Γ ⊢ ℓ B ≔ N in A : Type@i) by (eapply wf_let_typ with (oA := Some B); [ exact HB | exact HN | exact HA | solve_let_ann ]).
    specialize (IH _ _ _ HΓ' HL Hf Hs).
    rewrite apps_map_wk by assumption.
    assert (Hw : Θ ⍮ Γ ▸ B ≔ N ⊢w ↑ : Γ) by mauto 2.
    assert (H1 : Θ ⍮ Γ ▸ B ≔ N ⊢ (apps f (ctx_args Γ))[↑]ʷ : ℓ B[↑]ʷ ≔ N[↑]ʷ in A[wk_q ↑]ʷ) by exact (wk_preserves_exp _ _ _ _ _ _ IH Hw).
    assert (HB' : Θ ⍮ Γ ▸ B ≔ N ⊢ B[↑]ʷ : Type@j) by (eapply wk_preserves_typ; eassumption).
    assert (HN' : Θ ⍮ Γ ▸ B ≔ N ⊢ N[↑]ʷ : B[↑]ʷ) by (eapply wk_preserves_exp; eassumption).
    assert (Hw2 : Θ ⍮ Γ ▸ B ≔ N ▸ B[↑]ʷ ≔ N[↑]ʷ ⊢w wk_q ↑ : Γ ▸ B ≔ N) by (eapply wf_wk_q_def; eassumption).
    assert (HA' : Θ ⍮ Γ ▸ B ≔ N ▸ B[↑]ʷ ≔ N[↑]ʷ ⊢ A[wk_q ↑]ʷ : Type@i) by (eapply wk_preserves_typ; eassumption).
    assert (Hz : Θ ⍮ Γ ▸ B ≔ N ⊢ ℓ B[↑]ʷ ≔ N[↑]ʷ in A[wk_q ↑]ʷ ≈ A[wk_q ↑]ʷ[Id,,N[↑]ʷ] : Type@i)
      by (eapply wf_exp_eq_let_zeta_typ with (oA := Some B[↑]ʷ); [ exact HB' | exact HN' | exact HA' | solve_let_ann ]).
    assert (Hσ : Θ ⍮ Γ ▸ B ≔ N ⊢s Id,,N[↑]ʷ ≈ sb_extend Id (se_var 0) : Γ ▸ B ≔ N ▸ B[↑]ʷ ≔ N[↑]ʷ).
    { assert (Hv : Θ ⍮ Γ ▸ B ≔ N ⊢ #0 ≈ N[↑]ʷ : B[↑]ʷ) by mauto 3.
      econstructor.
      - eapply wf_sub_extend_def; [ mauto 3 | eassumption | eassumption | rewrite exp_sub_id; eassumption | rewrite !exp_sub_id; mauto 3 ].
      - apply wf_sub_extend_gen; [ mauto 3 | mauto 3 | | |]; intros * Hlk; inversion Hlk; subst; cbn.
        + rewrite exp_sub_shift_extend, exp_sub_id. mauto 3.
        + rewrite !exp_sub_shift_extend, !exp_sub_id; exact Hv.
      - intros [| x] C Hlk; inversion Hlk; subst; cbn.
        + rewrite exp_sub_shift_extend, exp_sub_id; mauto 3.
        + rewrite exp_sub_shift_extend, exp_sub_id; mauto 3. }
    assert (Θ ⍮ Γ ▸ B ≔ N ⊢ A[wk_q ↑]ʷ[Id,,N[↑]ʷ] ≈ A : Type@i).
    { rewrite <- (exp_wk_q_shift_single A) at 2.
      eapply (sub_eq_preserves_typ _ _ _ _ _ _ i); eassumption. }
    eapply wf_conv; [ exact H1 | exact HA | etransitivity; eassumption ].
  - (* a module slot: the local module the type was generalized by is [ζ] *)
    assert (HΓ' : ⊢ Θ ⍮ Γ) by mauto 2.
    pose proof (ctx_decomp_mod_unit HΓ) as HU.
    assert (HL : Θ ⍮ Γ ⊢ ℓₘ U in A : Type@i) by (eapply wf_let_mod_typ; eassumption).
    specialize (IH _ _ _ HΓ' HL Hf Hs).
    rewrite apps_map_wk by assumption.
    assert (Hw : Θ ⍮ Γ ▹ₘ U ⊢w ↑ : Γ) by mauto 2.
    assert (H1 : Θ ⍮ Γ ▹ₘ U ⊢ (apps f (ctx_args Γ))[↑]ʷ : ℓₘ (gunit_wk U ↑) in A[wk_q ↑]ʷ) by exact (wk_preserves_exp _ _ _ _ _ _ IH Hw).
    assert (HU' : Θ ⍮ Γ ▹ₘ U ⊢ᵘ gunit_wk U ↑ ≈ gunit_wk U ↑) by (eapply wk_preserves_unit; eassumption).
    assert (Hw2 : Θ ⍮ Γ ▹ₘ U ▹ₘ gunit_wk U ↑ ⊢w wk_q ↑ : Γ ▹ₘ U) by (eapply wf_wk_q_mod; eassumption).
    assert (HA' : Θ ⍮ Γ ▹ₘ U ▹ₘ gunit_wk U ↑ ⊢ A[wk_q ↑]ʷ : Type@i) by (eapply wk_preserves_typ; eassumption).
    assert (Hz : Θ ⍮ Γ ▹ₘ U ⊢ ℓₘ (gunit_wk U ↑) in A[wk_q ↑]ʷ ≈ A[wk_q ↑]ʷ[Id ,,ₘ me_lit (gunit_wk U ↑)] : Type@i)
      by (eapply wf_exp_eq_let_mod_zeta_typ; eassumption).
    assert (Hσ : Θ ⍮ Γ ▹ₘ U ⊢s Id ,,ₘ me_lit (gunit_wk U ↑) ≈ sb_extend Id (se_var 0) : Γ ▹ₘ U ▹ₘ gunit_wk U ↑).
    { econstructor.
      - pose proof (wf_sub_extend_mod Θ (Γ ▹ₘ U) (Γ ▹ₘ U) Id (gunit_wk U ↑) ltac:(mauto 3) HU' ltac:(rewrite gunit_sub_id; exact HU')) as Hx.
        rewrite gunit_sub_id in Hx; exact Hx.
      - apply wf_sub_extend_gen; [ mauto 3 | mauto 3 | | |]; intros * Hlk; inversion Hlk; subst; cbn.
        right; exists 0; split; [ reflexivity |]; rewrite gunit_sub_shift_extend, gunit_sub_id; constructor.
      - intros [| x] C Hlk; inversion Hlk; subst; cbn.
        rewrite exp_sub_shift_extend, exp_sub_id; mauto 3. }
    assert (Θ ⍮ Γ ▹ₘ U ⊢ A[wk_q ↑]ʷ[Id ,,ₘ me_lit (gunit_wk U ↑)] ≈ A : Type@i).
    { rewrite <- (exp_wk_q_shift_single A) at 2.
      eapply (sub_eq_preserves_typ _ _ _ _ _ _ i); eassumption. }
    eapply wf_conv; [ exact H1 | exact HA | etransitivity; eassumption ].
Qed.

(** ** Frames Stay Well Formed *)

Lemma fctx_cons : forall Γimp f F, fctx Γimp (f :: F) = self_ent (fr_body f) :: fr_params f ++ fctx Γimp F.
Proof. reflexivity. Qed.

Lemma fctx_body_ok : forall Θ Γimp f F,
    ⊢ Θ ⍮ fctx Γimp (f :: F) -> body_ok Θ (fr_params f ++ fctx Γimp F) (fr_body f).
Proof.
  intros * H; rewrite fctx_cons in H; apply ctx_decomp_mod_unit, unit_parts_of_wf in H.
  cbn in H; destruct_all; assumption.
Qed.

(** An entry checked in the frame context extends the innermost frame. *)
Lemma fctx_add_wf : forall Θ Γimp f F x E,
    ⊢ Θ ⍮ fctx Γimp (f :: F) -> gm_fresh x (fr_body f) -> entry_ok Θ (fctx Γimp (f :: F)) E ->
    ⊢ Θ ⍮ fctx Γimp (fr_add x E f :: F).
Proof.
  intros * H Hx HE; pose proof (fctx_body_ok _ _ _ _ H) as Hb.
  rewrite fctx_cons in H; pose proof (ctx_decomp_mod_left H) as H0.
  cbn [fctx fr_add fr_body fr_params]; apply self_ctx_wf; [ exact H0 |].
  cbn; repeat split; assumption.
Qed.

(** The body of the innermost frame, closed into a submodule. *)
Lemma fctx_close_ok : forall Θ Γimp g F pv,
    ⊢ Θ ⍮ fctx Γimp (g :: F) -> tele_ass (fr_params g) ->
    entry_ok Θ (fctx Γimp F) (ge_mod pv (gu_body (fr_params g) (fr_body g))).
Proof.
  intros * H Ht; pose proof (fctx_body_ok _ _ _ _ H) as Hb.
  rewrite fctx_cons in H; pose proof (ctx_decomp_mod_left H) as H0.
  cbn; apply unit_of_body_ok; [ apply ext_of_ctx; exact H0 | exact Ht | exact Hb ].
Qed.

Lemma entry_ok_def : forall Θ Γ pv A M, Θ ⍮ Γ ⊢ M : A -> entry_ok Θ Γ (ge_def pv A (Some M)).
Proof. intros; cbn; split; [ eapply presup_exp_typ; eassumption | assumption ]. Qed.

Lemma entry_ok_alias : forall Θ Γ pv Δ E,
    tele_ass Δ -> Θ ⍮ Γ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Δ ++ Γ ⊢ᵐ E ≈ E -> entry_ok Θ Γ (ge_mod pv (gu_mk Δ (md_alias E))).
Proof. intros; cbn; eapply wf_unit_eq_alias; eassumption. Qed.

Lemma entry_ok_alias0 : forall Θ Γ pv E,
    Θ ⍮ Γ ⊢ᵐ E ≈ E -> entry_ok Θ Γ (ge_mod pv (gu_mk nil (md_alias E))).
Proof.
  intros; apply entry_ok_alias; [ constructor | constructor; eapply presup_modexp_eq_ctx; eassumption | assumption ].
Qed.

Lemma fctx_tail_wf : forall Θ Γimp f F, ⊢ Θ ⍮ fctx Γimp (f :: F) -> ⊢ Θ ⍮ fctx Γimp F.
Proof. intros * H; rewrite fctx_cons in H; eapply (ctx_app_wf_tail _ (_ :: fr_params f)); exact H. Qed.

Lemma fctx_imp_wf : forall Θ Γimp F, ⊢ Θ ⍮ fctx Γimp F -> ⊢ Θ ⍮ Γimp.
Proof. induction F; intros * H; [ exact H | eauto using fctx_tail_wf ]. Qed.

(** The chains and parameters of the frames. *)
Definition fr_shape (F : list frame) : list (list string * ctx) := map (fun f => (fr_chain f, fr_params f)) F.

Lemma gens_run_wf : forall Θ Γimp F gs F', gens_run Θ Γimp F gs F' ->
    (⊢ Θ ⍮ fctx Γimp F -> ⊢ Θ ⍮ fctx Γimp F') /\ fr_shape F' = fr_shape F.
Proof.
  induction 1; [ auto | |]; destruct IHgens_run as [IH1 IH2]; split; try (rewrite IH2; reflexivity);
    intros HF; apply IH1, fctx_add_wf; eauto using entry_ok_def, entry_ok_alias0.
Qed.

Lemma fctx_emb : forall Θ Θ' Γ, Emb Θ Θ' -> ⊢ Θ ⍮ Γ -> ⊢ Θ' ⍮ Γ.
Proof. intros * He H; exact (proj1 (emb_preserves_wf _ _ He) _ H). Qed.

Lemma lead_slot_wf : forall Θ Γ E, Θ ⍮ Γ ⊢ᵐ E ≈ E -> ⊢ Θ ⍮ lead_slot E :: Γ.
Proof.
  intros * HE; apply wf_ctx_extend_mod; exact (entry_ok_alias0 _ _ true _ HE).
Qed.

(** What the leading opens declare is substituted away. *)
Lemma wf_imp_sub : forall Θ Γ, ⊢ Θ ⍮ Γ -> imp_ok Γ -> Θ ⍮ ⋅ ⊢s imp_sub Γ : Γ.
Proof.
  induction Γ as [| [A | A M | U] Γ IH]; intros HΓ Hi; inversion Hi as [| ? ? He Hi']; subst; cbn [imp_sub].
  - apply wf_sub_id; mauto 2 using ctx_wf_gctx.
  - exfalso; eapply He; reflexivity.
  - destruct (ctx_decomp_def_typ HΓ) as [i HA]; pose proof (ctx_decomp_def_body HΓ) as HM.
    assert (Hσ : Θ ⍮ ⋅ ⊢s imp_sub Γ : Γ) by (apply IH; [ mauto 2 | exact Hi' ]).
    eapply wf_sub_extend_def; [ exact Hσ | exact HA | exact HM | eapply sub_preserves_exp; eassumption | ].
    apply wf_exp_eq_refl; eapply sub_preserves_exp; eassumption.
  - pose proof (ctx_decomp_mod_unit HΓ) as HU.
    assert (Hσ : Θ ⍮ ⋅ ⊢s imp_sub Γ : Γ) by (apply IH; [ eapply ctx_decomp_mod_left; exact HΓ | exact Hi' ]).
    apply wf_sub_extend_mod; [ exact Hσ | exact HU | eapply sub_preserves_unit; eassumption ].
Qed.

Section WellFormed.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  #[local] Abbreviation run_cmd := (run_cmd load_path read to_core).
  #[local] Abbreviation run_cmds := (run_cmds load_path read to_core).
  #[local] Abbreviation run_load := (run_load load_path read to_core).
  #[local] Abbreviation run_lead := (run_lead load_path read to_core).
  #[local] Abbreviation run_leads := (run_leads load_path read to_core).
  #[local] Abbreviation run_unit := (run_unit load_path read to_core).

  (** A run keeps the chains and parameters of every frame. *)
  Lemma run_shape :
    (forall ch fp Γimp Θ F c Θ' F', run_cmd ch fp Γimp Θ F c Θ' F' -> fr_shape F' = fr_shape F) /\
    (forall ch fp Γimp Θ F cs Θ' F', run_cmds ch fp Γimp Θ F cs Θ' F' -> fr_shape F' = fr_shape F) /\
    (forall ch Θ fq Θ', run_load ch Θ fq Θ' -> True) /\
    (forall ch Θ Γ c Θ' Γ', run_lead ch Θ Γ c Θ' Γ' -> True) /\
    (forall ch Θ Γ cs Θ' Γ', run_leads ch Θ Γ cs Θ' Γ' -> True) /\
    (forall ch Θ0 u Θ U, run_unit ch Θ0 u Θ U -> True).
  Proof.
    apply run_mut_ind; intros; auto; try congruence.
    match goal with H : gens_run _ _ _ _ _ |- _ => exact (proj2 (gens_run_wf _ _ _ _ _ H)) end.
  Qed.

  (** ** Determinism

      A run's result does not depend on the chain it runs in: the chain only
      rules runs out.  So running the same unit twice from the same global
      context gives the same result. *)

  Lemma gens_run_functional : forall Θ Γimp F gs F1, gens_run Θ Γimp F gs F1 ->
      forall F2, gens_run Θ Γimp F gs F2 -> F1 = F2.
  Proof.
    induction 1; intros F2 H2; inversion H2; subst; [ reflexivity | auto | auto ].
  Qed.

  Theorem run_functional :
    (forall ch fp Γimp Θ F c Θ1 F1, run_cmd ch fp Γimp Θ F c Θ1 F1 ->
       forall ch' Θ2 F2, run_cmd ch' fp Γimp Θ F c Θ2 F2 -> Θ1 = Θ2 /\ F1 = F2) /\
    (forall ch fp Γimp Θ F cs Θ1 F1, run_cmds ch fp Γimp Θ F cs Θ1 F1 ->
       forall ch' Θ2 F2, run_cmds ch' fp Γimp Θ F cs Θ2 F2 -> Θ1 = Θ2 /\ F1 = F2) /\
    (forall ch Θ fq Θ1, run_load ch Θ fq Θ1 -> forall ch' Θ2, run_load ch' Θ fq Θ2 -> Θ1 = Θ2) /\
    (forall ch Θ Γ c Θ1 Γ1, run_lead ch Θ Γ c Θ1 Γ1 ->
       forall ch' Θ2 Γ2, run_lead ch' Θ Γ c Θ2 Γ2 -> Θ1 = Θ2 /\ Γ1 = Γ2) /\
    (forall ch Θ Γ cs Θ1 Γ1, run_leads ch Θ Γ cs Θ1 Γ1 ->
       forall ch' Θ2 Γ2, run_leads ch' Θ Γ cs Θ2 Γ2 -> Θ1 = Θ2 /\ Γ1 = Γ2) /\
    (forall ch Θ0 u Θ1 U1, run_unit ch Θ0 u Θ1 U1 ->
       forall ch' Θ2 U2, run_unit ch' Θ0 u Θ2 U2 -> hd_error ch' = hd_error ch -> Θ1 = Θ2 /\ U1 = U2).
  Proof.
    apply run_mut_ind; intros;
      match goal with
      | H : hd_error _ = hd_error _ |- _ =>
          match goal with H2 : run_unit _ _ _ _ _ |- _ => inversion H2; subst; cbn in H; injection H as -> end
      | H2 : _ |- _ => inversion H2; subst
      end;
      try congruence; auto.
    - (* a module *)
      match goal with IH : forall _ _ _, run_cmds _ _ _ _ _ ?cs _ _ -> _, H : run_cmds _ _ _ _ _ ?cs _ _ |- _ =>
        destruct (IH _ _ _ H) as [-> E] end.
      injection E as ->; auto.
    - (* a load *)
      match goal with IH : forall _ _, run_load _ _ _ _ -> _, Hl : run_load _ _ _ _ |- _ => rewrite (IH _ _ Hl) end; auto.
    - (* an open *)
      match goal with H1 : open_gen_ok _ _ _ _ _ _ _ ?g1, H : open_gen_ok _ _ _ _ _ _ _ ?g2 |- _ =>
        pose proof (open_gen_ok_functional _ _ _ _ _ _ _ _ _ H1 H); subst g2 end.
      match goal with H1 : gens_run _ _ _ ?gs ?F1, H : gens_run _ _ _ ?gs ?F2 |- _ =>
        assert (F1 = F2) by exact (gens_run_functional _ _ _ _ _ H1 _ H); subst end; auto.
    - (* a command, then the rest *)
      match goal with H1 : cmd_xp_ok _ _ ?c ?c1, H : cmd_xp_ok _ _ ?c ?c2 |- _ =>
        pose proof (cmd_xp_ok_functional _ _ _ _ _ H1 H); subst c2 end.
      match goal with IH : forall _ _ _, run_cmd _ _ _ _ _ ?c _ _ -> _, H : run_cmd _ _ _ _ _ ?c _ _ |- _ =>
        destruct (IH _ _ _ H) as [<- <-] end.
      match goal with IH : forall _ _ _, run_cmds _ _ _ _ _ ?cs _ _ -> _, H : run_cmds _ _ _ _ _ ?cs _ _ |- _ =>
        exact (IH _ _ _ H) end.
    - (* a unit loaded *)
      repeat match goal with H : ?f ?a = Some ?x, H' : ?f ?a = Some ?y |- _ =>
        rewrite H in H'; injection H' as <- end.
      match goal with IH : forall _ _ _, run_unit _ nil ?u _ _ -> _, H : run_unit _ nil ?u _ _ |- _ =>
        destruct (IH _ _ _ H eq_refl) as [<- <-] end; reflexivity.
    - (* a leading load *)
      match goal with IH : forall _ _, run_load _ _ _ _ -> _, Hl : run_load _ _ _ _ |- _ => rewrite (IH _ _ Hl) end; auto.
    - (* a leading command, then the rest *)
      match goal with H1 : cmd_xp_ok _ _ ?c ?c1, H : cmd_xp_ok _ _ ?c ?c2 |- _ =>
        pose proof (cmd_xp_ok_functional _ _ _ _ _ H1 H); subst c2 end.
      match goal with IH : forall _ _ _, run_lead _ _ _ ?c _ _ -> _, H : run_lead _ _ _ ?c _ _ |- _ =>
        destruct (IH _ _ _ H) as [<- <-] end.
      match goal with IH : forall _ _ _, run_leads _ _ _ ?cs _ _ -> _, H : run_leads _ _ _ ?cs _ _ |- _ =>
        exact (IH _ _ _ H) end.
    - (* a unit *)
      match goal with IH : forall _ _ _, run_leads _ _ nil ?l _ _ -> _, H : run_leads _ _ nil ?l _ _ |- _ =>
        destruct (IH _ _ _ H) as [<- <-] end.
      match goal with H1 : tele_xp_ok _ _ ?P ?P1, H : tele_xp_ok _ _ ?P ?P2 |- _ =>
        pose proof (tele_xp_ok_functional _ _ _ _ _ H1 H); subst P2 end.
      match goal with IH : forall _ _ _, run_cmds _ _ _ _ _ ?cs _ _ -> _, H : run_cmds _ _ _ _ _ ?cs _ _ |- _ =>
        destruct (IH _ _ _ H) as [<- E] end.
      injection E as ->; auto.
  Qed.

  (** ** Coherence of Merged Global Contexts

      [loaded fp ΘL]: running the unit [fp] from nothing files [ΘL].  It is
      functional.  A global context is coherent when everything it files
      comes from such a run, unchanged, except the constants of the unit
      running ([own]).  Two coherent global contexts agree on what they
      share, so merging them is well formed. *)

  Definition loaded (fp : path) (ΘL : gctx) : Prop :=
    exists ch src prg u ΘU U, load_path fp = Some src /\ read src = Some prg /\ prog_path prg = fp /\
      to_core prg = Some u /\ run_unit (fp :: ch) nil u ΘU U /\ ΘL = gd_unit fp U :: ΘU.

  Lemma loaded_functional : forall fp Θ1 Θ2, loaded fp Θ1 -> loaded fp Θ2 -> Θ1 = Θ2.
  Proof.
    intros * (ch1 & s1 & p1 & u1 & Θ1' & U1 & Hs1 & Hr1 & _ & Hc1 & Hu1 & ->)
      (ch2 & s2 & p2 & u2 & Θ2' & U2 & Hs2 & Hr2 & _ & Hc2 & Hu2 & ->).
    rewrite Hs1 in Hs2; injection Hs2 as <-; rewrite Hr1 in Hr2; injection Hr2 as <-.
    rewrite Hc1 in Hc2; injection Hc2 as <-.
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 run_functional)))) _ _ _ _ _ Hu1 _ _ _ Hu2 eq_refl) as [-> ->].
    reflexivity.
  Qed.

  Lemma loaded_unit : forall fp ΘL, loaded fp ΘL -> gc_unit ΘL fp <> None.
  Proof. intros * (? & ? & ? & ? & ? & ? & _ & _ & _ & _ & _ & ->); cbn; rewrite path_beq_refl; discriminate. Qed.

  Definition coh (own : path -> Prop) (Θ : gctx) : Prop :=
    (forall fp U, gc_unit Θ fp = Some U -> exists ΘL, loaded fp ΘL /\ ΘL ⊑ Θ) /\
    (forall c r, gc_const Θ c = Some r ->
       own (q_unit c) \/ exists ΘL, loaded (q_unit c) ΘL /\ gc_const ΘL c = Some r /\ ΘL ⊑ Θ).

  (** The units a run files, beyond those it starts from, are not in its
      chain. *)
  Definition fresh (ch : list path) (Θ Θ' : gctx) : Prop :=
    forall R, gc_unit Θ' R <> None -> gc_unit Θ R <> None \/ ~ In R ch.

  Lemma coh_nil : forall own, coh own nil.
  Proof. split; intros; discriminate. Qed.

  Lemma fresh_refl : forall ch Θ, fresh ch Θ Θ.
  Proof. intros ch Θ R H; left; exact H. Qed.

  Lemma fresh_trans : forall ch Θ1 Θ2 Θ3, Θ1 ⊑ Θ2 -> fresh ch Θ1 Θ2 -> fresh ch Θ2 Θ3 -> fresh ch Θ1 Θ3.
  Proof.
    intros * Hs H12 H23 R H; destruct (H23 _ H) as [H2 | H2]; [ exact (H12 _ H2) | right; exact H2 ].
  Qed.

  Lemma coh_const : forall Θ P c A M b, coh (eq P) Θ -> gc_const Θ c = None -> q_unit c = P ->
      coh (eq P) (gd_const c A M b :: Θ).
  Proof.
    intros * [HU HC] Hn Hq.
    pose proof (gc_sub_cons_const _ c A M b Hn) as Hs.
    split; cbn.
    - intros * H; destruct (HU _ _ H) as (ΘL & HL & HS); exists ΘL; split; [ exact HL | eapply gc_sub_trans; eassumption ].
    - intros c' r H; destruct (qname_beq c' c) eqn:E.
      + apply qname_beq_true in E; subst; left; reflexivity.
      + destruct (HC _ _ H) as [Ho | (ΘL & HL & Hc & HS)]; [ left; exact Ho |].
        right; exists ΘL; split; [ exact HL | split; [ exact Hc | eapply gc_sub_trans; eassumption ] ].
  Qed.

  (** What a completed run of [fq] files is coherent with nothing running. *)
  Lemma coh_loaded : forall fq U ΘU, coh (eq fq) ΘU -> gc_unit ΘU fq = None ->
      loaded fq (gd_unit fq U :: ΘU) -> coh (fun _ => False) (gd_unit fq U :: ΘU).
  Proof.
    intros * [HU HC] Hn HL.
    pose proof (gc_sub_cons_unit _ fq U Hn) as Hs.
    split; cbn.
    - intros fp V H; destruct (path_beq fp fq) eqn:E.
      + apply path_beq_true in E; subst; exists (gd_unit fq U :: ΘU); split; [ exact HL | apply gc_sub_refl ].
      + destruct (HU _ _ H) as (ΘL & HL' & HS); exists ΘL; split; [ exact HL' | eapply gc_sub_trans; eassumption ].
    - intros c r H; right; destruct (HC _ _ H) as [<- | (ΘL & HL' & Hc & HS)].
      + exists (gd_unit fq U :: ΘU); split; [ exact HL |]; split; [ exact H | apply gc_sub_refl ].
      + exists ΘL; split; [ exact HL' | split; [ exact Hc | eapply gc_sub_trans; eassumption ] ].
  Qed.

  Lemma coh_agree : forall P ch Θ ΘL, coh (eq P) Θ -> In P ch -> coh (fun _ => False) ΘL ->
      (forall R, gc_unit ΘL R <> None -> ~ In R ch) -> gc_agree Θ ΘL.
  Proof.
    intros * [HU1 HC1] Hin [HU2 HC2] Hfr; split.
    - intros fp U U' H1 H2.
      destruct (HU1 _ _ H1) as (W1 & HW1 & HS1); destruct (HU2 _ _ H2) as (W2 & HW2 & HS2).
      pose proof (loaded_functional _ _ _ HW1 HW2) as <-.
      destruct (gc_unit W1 fp) as [V |] eqn:EV; [| exfalso; exact (loaded_unit _ _ HW1 EV) ].
      pose proof (gc_sub_unit _ _ _ _ HS1 EV); pose proof (gc_sub_unit _ _ _ _ HS2 EV); congruence.
    - intros c r r' H1 H2.
      destruct (HC2 _ _ H2) as [[] | (W2 & HW2 & Hc2 & HS2)].
      destruct (HC1 _ _ H1) as [Ho | (W1 & HW1 & Hc1 & HS1)].
      + exfalso; subst P; apply (Hfr (q_unit c)); [| exact Hin ].
        destruct (gc_unit W2 (q_unit c)) as [V |] eqn:EV; [| exfalso; exact (loaded_unit _ _ HW2 EV) ].
        rewrite (gc_sub_unit _ _ _ _ HS2 EV); discriminate.
      + pose proof (loaded_functional _ _ _ HW1 HW2) as <-; congruence.
  Qed.

  Lemma coh_merge : forall own Θ ΘL, coh own Θ -> coh (fun _ => False) ΘL -> gc_agree Θ ΘL ->
      coh own (gc_merge Θ ΘL).
  Proof.
    intros * [HU1 HC1] [HU2 HC2] Ha.
    pose proof (gc_merge_sub_left Θ ΘL) as S1; pose proof (gc_merge_sub_right _ _ Ha) as S2.
    split.
    - intros fp U H; rewrite gc_unit_merge in H; destruct (gc_unit Θ fp) eqn:E.
      + destruct (HU1 _ _ E) as (W & HW & HS); exists W; split; [ exact HW | eapply gc_sub_trans; eassumption ].
      + destruct (HU2 _ _ H) as (W & HW & HS); exists W; split; [ exact HW | eapply gc_sub_trans; eassumption ].
    - intros c r H; rewrite gc_const_merge in H; destruct (gc_const Θ c) eqn:E.
      + injection H as ->; destruct (HC1 _ _ E) as [Ho | (W & HW & Hc & HS)]; [ left; exact Ho |].
        right; exists W; split; [ exact HW | split; [ exact Hc | eapply gc_sub_trans; eassumption ] ].
      + destruct (HC2 _ _ H) as [[] | (W & HW & Hc & HS)].
        right; exists W; split; [ exact HW | split; [ exact Hc | eapply gc_sub_trans; eassumption ] ].
  Qed.

  Lemma fresh_merge : forall ch Θ ΘL, (forall R, gc_unit ΘL R <> None -> ~ In R ch) -> fresh ch Θ (gc_merge Θ ΘL).
  Proof.
    intros * Hf R H; rewrite gc_unit_merge in H; destruct (gc_unit Θ R) eqn:E; [ left; discriminate | right; exact (Hf _ H) ].
  Qed.

  Lemma gc_unit_const_cons : forall c A M b Θ fp, gc_unit (gd_const c A M b :: Θ) fp = gc_unit Θ fp.
  Proof. reflexivity. Qed.

  Theorem run_wf :
    (forall ch fp Γimp Θ F c Θ' F', run_cmd ch fp Γimp Θ F c Θ' F' ->
       ⊢ Θ ⍮ fctx Γimp F -> coh (eq fp) Θ -> In fp ch ->
       ⊢ Θ' ⍮ fctx Γimp F' /\ Θ ⊑ Θ' /\ coh (eq fp) Θ' /\ fresh ch Θ Θ') /\
    (forall ch fp Γimp Θ F cs Θ' F', run_cmds ch fp Γimp Θ F cs Θ' F' ->
       ⊢ Θ ⍮ fctx Γimp F -> coh (eq fp) Θ -> In fp ch ->
       ⊢ Θ' ⍮ fctx Γimp F' /\ Θ ⊑ Θ' /\ coh (eq fp) Θ' /\ fresh ch Θ Θ') /\
    (forall ch Θ fq Θ', run_load ch Θ fq Θ' ->
       ⊢g Θ -> forall P, coh (eq P) Θ -> In P ch ->
       ⊢g Θ' /\ Θ ⊑ Θ' /\ gc_unit Θ' fq <> None /\ coh (eq P) Θ' /\ fresh ch Θ Θ') /\
    (forall ch Θ Γ c Θ' Γ', run_lead ch Θ Γ c Θ' Γ' ->
       ⊢ Θ ⍮ Γ -> imp_ok Γ -> forall P, coh (eq P) Θ -> In P ch ->
       ⊢ Θ' ⍮ Γ' /\ imp_ok Γ' /\ Θ ⊑ Θ' /\ coh (eq P) Θ' /\ fresh ch Θ Θ') /\
    (forall ch Θ Γ cs Θ' Γ', run_leads ch Θ Γ cs Θ' Γ' ->
       ⊢ Θ ⍮ Γ -> imp_ok Γ -> forall P, coh (eq P) Θ -> In P ch ->
       ⊢ Θ' ⍮ Γ' /\ imp_ok Γ' /\ Θ ⊑ Θ' /\ coh (eq P) Θ' /\ fresh ch Θ Θ') /\
    (forall ch Θ0 u Θ U, run_unit ch Θ0 u Θ U ->
       ⊢g Θ0 -> forall P, hd_error ch = Some P -> coh (eq P) Θ0 ->
       ⊢g Θ /\ Θ0 ⊑ Θ /\ Θ ⍮ ⋅ ⊢ᵘ U ≈ U /\ coh (eq P) Θ /\ fresh ch Θ0 Θ).
  Proof.
    apply run_mut_ind.
    - (* a definition *)
      intros ch fp Γimp Θ f F x pv A M HM Hx HF Hc Hin.
      refine (conj _ (conj (gc_sub_refl _) (conj Hc (fresh_refl _ _)))).
      apply fctx_add_wf; [ assumption | assumption | apply entry_ok_def; assumption ].
    - (* an abstract definition: the constant, then the member *)
      intros ch fp Γimp Θ f F x pv A M HM Hx Hn HF Hc Hin.
      set (Γ := fctx Γimp (f :: F)) in *.
      set (c := abs_name fp (fr_chain f) x) in *.
      destruct (presup_exp_typ HM) as [i HA].
      assert (Hg : ⊢g gd_const c (ctx_pi Γ A) (Some (ctx_fn Γ M)) false :: Θ)
        by (constructor; [ eapply ctx_fn_wf0; eassumption | exact Hn ]).
      assert (He : Emb Θ (gd_const c (ctx_pi Γ A) (Some (ctx_fn Γ M)) false :: Θ))
        by (constructor; [ exact Hg | apply gc_sub_cons_const, Hn ]).
      destruct (emb_preserves_wf _ _ He) as (Hc' & Ht & _).
      refine (conj _ (conj (em_res _ _ He) (conj (coh_const _ _ _ _ _ _ Hc Hn eq_refl) _))).
      + apply fctx_add_wf; [ apply Hc', HF | assumption |].
        apply entry_ok_def, wf_apps_ctx_args with (i := i); [ apply Hc', HF | apply Ht, HA | | exact I ].
        eapply wf_const; [ constructor; exact Hg | cbn; rewrite qname_beq_refl; reflexivity ].
      + intros R HR; left; exact HR.
    - (* an axiom: the constant, without a body, then the member *)
      intros ch fp Γimp Θ f F x b pv A i HA Hx Hn HF Hc Hin.
      set (Γ := fctx Γimp (f :: F)) in *.
      set (c := abs_name fp (fr_chain f) x) in *.
      destruct (ctx_pi_wf0 _ _ _ _ HA) as [j Hj].
      assert (Hg : ⊢g gd_const c (ctx_pi Γ A) None false :: Θ) by (econstructor; [ exact Hj | exact Hn ]).
      assert (He : Emb Θ (gd_const c (ctx_pi Γ A) None false :: Θ))
        by (constructor; [ exact Hg | apply gc_sub_cons_const, Hn ]).
      destruct (emb_preserves_wf _ _ He) as (Hc' & Ht & _).
      refine (conj _ (conj (em_res _ _ He) (conj (coh_const _ _ _ _ _ _ Hc Hn eq_refl) _))).
      + apply fctx_add_wf; [ apply Hc', HF | assumption |].
        apply entry_ok_def, wf_apps_ctx_args with (i := i); [ apply Hc', HF | apply Ht, HA | | exact I ].
        eapply wf_const; [ constructor; exact Hg | cbn; rewrite qname_beq_refl; reflexivity ].
      + intros R HR; left; exact HR.
    - (* a module: its body in a frame of its own *)
      intros ch fp Γimp Θ f F x pv Δ cs Θ' g Ht HΔ Hx Hr IH HF Hc Hin.
      pose proof (proj1 (proj2 run_shape) _ _ _ _ _ _ _ _ Hr) as Hs; cbn in Hs; injection Hs as _ HP.
      destruct IH as (Hg & Hsub & Hc' & Hf).
      { rewrite fctx_cons; cbn [fr_body fr_params]; apply self_ctx_wf; [ exact HΔ | exact I ]. }
      { exact Hc. }
      { exact Hin. }
      refine (conj _ (conj Hsub (conj Hc' Hf))).
      apply fctx_add_wf; [ exact (fctx_tail_wf _ _ _ _ Hg) | assumption |].
      rewrite <- HP; apply fctx_close_ok; [ exact Hg | rewrite HP; exact Ht ].
    - (* an alias *)
      intros ch fp Γimp Θ f F x pv Δ E Ht HΔ HE Hx HF Hc Hin.
      refine (conj _ (conj (gc_sub_refl _) (conj Hc (fresh_refl _ _)))).
      apply fctx_add_wf; [ assumption | assumption | apply entry_ok_alias; assumption ].
    - (* a load: what it files embeds the frames *)
      intros ch fp Γimp Θ F fq Θ' Hl IH HF Hc Hin.
      destruct (IH (ctx_wf_gctx _ _ HF) _ Hc Hin) as (Hg & Hs & _ & Hc' & Hf).
      refine (conj _ (conj Hs (conj Hc' Hf))).
      eapply fctx_emb; [ constructor; eassumption | exact HF ].
    - (* an open: its alias, then its items *)
      intros ch fp Γimp Θ f F E oz its gs F' HE Hgen Hgs HF Hc Hin.
      refine (conj _ (conj (gc_sub_refl _) (conj Hc (fresh_refl _ _)))).
      exact (proj1 (gens_run_wf _ _ _ _ _ Hgs) HF).
    - intros; refine (conj _ (conj (gc_sub_refl _) (conj _ (fresh_refl _ _)))); assumption.
    - intros; refine (conj _ (conj (gc_sub_refl _) (conj _ (fresh_refl _ _)))); assumption.
    - intros; refine (conj _ (conj (gc_sub_refl _) (conj _ (fresh_refl _ _)))); assumption.
    - intros ch fp Γimp Θ F c c' cs Θ1 F1 Θ2 F2 _ _ Hr1 IH1 Hr2 IH2 HF Hc Hin.
      destruct (IH1 HF Hc Hin) as (H1 & Hs1 & Hc1 & Hf1); destruct (IH2 H1 Hc1 Hin) as (H2 & Hs2 & Hc2 & Hf2).
      refine (conj H2 (conj (gc_sub_trans _ _ _ Hs1 Hs2) (conj Hc2 (fresh_trans _ _ _ _ Hs1 Hf1 Hf2)))).
    - (* a unit filed already *)
      intros ch Θ fq U HU Hg P Hc Hin.
      refine (conj Hg (conj (gc_sub_refl _) (conj _ (conj Hc (fresh_refl _ _))))); congruence.
    - (* a unit loaded: run from nothing, filed on top of what it filed, merged *)
      intros ch Θ fq src prg u ΘU U Hn Hni Hs Hr Hp Hcu Hu IH Hn' Hg P Hc Hin.
      destruct (IH ltac:(constructor) fq eq_refl (coh_nil _)) as (HgU & _ & HU & HcU & HfU).
      set (ΘL := gd_unit fq U :: ΘU).
      assert (HgL : ⊢g ΘL) by (constructor; assumption).
      assert (HL : loaded fq ΘL) by (exists ch, src, prg, u, ΘU, U; auto 7).
      pose proof (coh_loaded _ _ _ HcU Hn' HL) as HcL.
      assert (HfL : forall R, gc_unit ΘL R <> None -> ~ In R ch).
      { intros R HR; cbn in HR; destruct (path_beq R fq) eqn:E.
        - apply path_beq_true in E; subst; exact Hni.
        - destruct (HfU _ HR) as [[] | Hc0]; [ reflexivity |]; intros Hc1; apply Hc0; right; exact Hc1. }
      pose proof (coh_agree _ _ _ _ Hc Hin HcL HfL) as Ha.
      refine (conj (gc_merge_wf _ _ Hg HgL Ha) (conj (gc_merge_sub_left _ _) (conj _ (conj (coh_merge _ _ _ Hc HcL Ha) (fresh_merge _ _ _ HfL))))).
      rewrite gc_unit_merge, Hn; cbn; rewrite path_beq_refl; discriminate.
    - (* a leading load *)
      intros ch Θ Γ fq Θ' Hl IH HΓ Hi P Hc Hin.
      destruct (IH (ctx_wf_gctx _ _ HΓ) _ Hc Hin) as (Hg & Hs & _ & Hc' & Hf).
      refine (conj _ (conj Hi (conj Hs (conj Hc' Hf)))).
      eapply fctx_emb with (Θ := Θ); [ constructor; eassumption | exact HΓ ].
    - (* a leading open: the slot of its target *)
      intros ch Θ Γimp E oz its gs _ HE Hgen HΓ Hi P Hc Hin.
      refine (conj (lead_slot_wf _ _ _ HE) (conj _ (conj (gc_sub_refl _) (conj Hc (fresh_refl _ _))))).
      constructor; [ intros A; discriminate | exact Hi ].
    - intros; refine (conj _ (conj _ (conj (gc_sub_refl _) (conj _ (fresh_refl _ _))))); assumption.
    - intros ch Θ Γimp c c' cs Θ1 Γ1 Θ2 Γ2 _ _ Hr1 IH1 Hr2 IH2 HΓ Hi P Hc Hin.
      destruct (IH1 HΓ Hi _ Hc Hin) as (H1 & Hi1 & Hs1 & Hc1 & Hf1).
      destruct (IH2 H1 Hi1 _ Hc1 Hin) as (H2 & Hi2 & Hs2 & Hc2 & Hf2).
      exact (conj H2 (conj Hi2 (conj (gc_sub_trans _ _ _ Hs1 Hs2) (conj Hc2 (fresh_trans _ _ _ _ Hs1 Hf1 Hf2))))).
    - (* a unit: its leading commands, its parameters, its body *)
      intros fp ch Θ0 leads P P' cs Θ1 Γimp Θ2 f Hl IHl _ Ht _ HF0 Hr IHr Hg0 Q HQ Hc0.
      cbn in HQ; injection HQ as <-.
      destruct (IHl ltac:(constructor; exact Hg0) ltac:(constructor) _ Hc0 (or_introl eq_refl))
        as (H1 & Hi1 & Hs1 & Hc1 & Hf1).
      destruct (IHr HF0 Hc1 (or_introl eq_refl)) as (H2 & Hs2 & Hc2 & Hf2).
      pose proof (proj1 (proj2 run_shape) _ _ _ _ _ _ _ _ Hr) as Hs; cbn in Hs; injection Hs as _ HP.
      pose proof (fctx_close_ok _ _ _ _ false H2) as HU; rewrite HP in HU; specialize (HU Ht); cbn in HU.
      refine (conj (ctx_wf_gctx _ _ H2) (conj (gc_sub_trans _ _ _ Hs1 Hs2) (conj _ (conj Hc2 (fresh_trans _ _ _ _ Hs1 Hf1 Hf2))))).
      eapply sub_preserves_unit; [ exact HU |].
      apply wf_imp_sub; [ exact (fctx_imp_wf _ _ _ H2) |].
      (* the leading commands left no assumption *)
      exact Hi1.
  Qed.

  Corollary prog_sem_wf : forall prg Θ U,
      prog_sem load_path read to_core prg Θ U ->
      ⊢g Θ /\ Θ ⍮ ⋅ ⊢ᵘ U ≈ U.
  Proof.
    intros * (u & _ & Hu).
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 run_wf)))) _ _ _ _ _ Hu ltac:(constructor) _ eq_refl (coh_nil _))
      as (? & _ & ? & _); split; assumption.
  Qed.
End WellFormed.


(** ** Programs Without Axioms

    A command files an axiom only from a definition without a body, so a run
    of commands none of which is one, in units none of which has one, from a
    global context without axioms, reaches only global contexts without
    axioms: the consistency and canonicity theorems at [gc_no_axioms] hold of
    such a program. *)

Fixpoint ccmd_no_axioms (c : ccmd) : Prop :=
  match c with
  | cc_def _ _ _ _ oM => oM <> None
  | cc_mod _ _ _ cs =>
      (fix go (cs : list ccmd) : Prop :=
         match cs with
         | nil => True
         | c :: cs' => ccmd_no_axioms c /\ go cs'
         end) cs
  | _ => True
  end.

Fixpoint cmds_no_axioms (cs : list ccmd) : Prop :=
  match cs with
  | nil => True
  | c :: cs' => ccmd_no_axioms c /\ cmds_no_axioms cs'
  end.

Lemma ccmd_no_axioms_mod : forall x pv Δ cs, ccmd_no_axioms (cc_mod x pv Δ cs) <-> cmds_no_axioms cs.
Proof. intros; cbn; induction cs; cbn; tauto. Qed.

Definition unit_no_axioms (u : cunit) : Prop :=
  let '(leads, _, cs) := u in cmds_no_axioms leads /\ cmds_no_axioms cs.

Lemma cmd_xp_ok_no_axioms : forall Θ Γ c c', cmd_xp_ok Θ Γ c c' -> ccmd_no_axioms c -> ccmd_no_axioms c'.
Proof.
  intros * (mt & _ & Ex) Hc.
  destruct c as [x b pv A oM | x pv Δ cs | x pv Δ E | fp | E oz its | M oA].
  - destruct (cmd_xp_def_inv _ _ _ _ _ _ _ _ Ex) as (A' & oM' & -> & Hn); cbn in *; intros Ho; apply Hc, Hn, Ho.
  - destruct (cmd_xp_mod_inv _ _ _ _ _ _ _ Ex) as (Δ' & _ & ->); exact Hc.
  - pose proof (cmd_xp_head _ _ _ _ Ex) as Hh; destruct c'; cbn in Hh; try discriminate; exact I.
  - pose proof (cmd_xp_head _ _ _ _ Ex) as Hh; destruct c'; cbn in Hh; try discriminate; exact I.
  - pose proof (cmd_xp_head _ _ _ _ Ex) as Hh; destruct c'; cbn in Hh; try discriminate; exact I.
  - pose proof (cmd_xp_head _ _ _ _ Ex) as Hh; destruct c'; cbn in Hh; try discriminate; exact I.
Qed.

Lemma gc_no_axioms_nil : gc_no_axioms nil.
Proof. intros ? ? ? ? H; discriminate. Qed.

Lemma gc_no_axioms_cons_const : forall c A M b Θ, gc_no_axioms Θ -> gc_no_axioms (gd_const c A (Some M) b :: Θ).
Proof.
  intros * H qn A' oM b' Hl; cbn in Hl; destruct (qname_beq qn c); [ injection Hl as _ <- _; discriminate | eauto ].
Qed.

Lemma gc_no_axioms_cons_unit : forall fp U Θ, gc_no_axioms Θ -> gc_no_axioms (gd_unit fp U :: Θ).
Proof. intros * H qn A' oM b' Hl; cbn in Hl; eauto. Qed.

Lemma gc_no_axioms_merge : forall Θ ΘL, gc_no_axioms Θ -> gc_no_axioms ΘL -> gc_no_axioms (gc_merge Θ ΘL).
Proof.
  intros * H HL qn A oM b Hl; rewrite gc_const_merge in Hl; destruct (gc_const Θ qn) eqn:E; [ injection Hl as ->; eauto | eauto ].
Qed.

Section NoAxioms.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).

  (** Every unit the files hold is without axioms. *)
  Hypothesis Hall : forall fq src prg u,
      load_path fq = Some src -> read src = Some prg -> to_core prg = Some u -> unit_no_axioms u.

  Theorem run_no_axioms :
    (forall ch fp Γimp Θ F c Θ' F', run_cmd load_path read to_core ch fp Γimp Θ F c Θ' F' ->
       ccmd_no_axioms c -> gc_no_axioms Θ -> gc_no_axioms Θ') /\
    (forall ch fp Γimp Θ F cs Θ' F', run_cmds load_path read to_core ch fp Γimp Θ F cs Θ' F' ->
       cmds_no_axioms cs -> gc_no_axioms Θ -> gc_no_axioms Θ') /\
    (forall ch Θ fq Θ', run_load load_path read to_core ch Θ fq Θ' -> gc_no_axioms Θ -> gc_no_axioms Θ') /\
    (forall ch Θ Γ c Θ' Γ', run_lead load_path read to_core ch Θ Γ c Θ' Γ' ->
       ccmd_no_axioms c -> gc_no_axioms Θ -> gc_no_axioms Θ') /\
    (forall ch Θ Γ cs Θ' Γ', run_leads load_path read to_core ch Θ Γ cs Θ' Γ' ->
       cmds_no_axioms cs -> gc_no_axioms Θ -> gc_no_axioms Θ') /\
    (forall ch Θ0 u Θ U, run_unit load_path read to_core ch Θ0 u Θ U ->
       unit_no_axioms u -> gc_no_axioms Θ0 -> gc_no_axioms Θ).
  Proof.
    apply run_mut_ind; intros; cbn [ccmd_no_axioms cmds_no_axioms unit_no_axioms] in *; destruct_all;
      eauto using gc_no_axioms_cons_const.
    - (* an axiom *) contradiction.
    - (* a command, expanded, then the rest *)
      match goal with IH1 : ccmd_no_axioms ?c' -> _ -> _, Hx : cmd_xp_ok _ _ _ ?c' |- _ =>
        pose proof (cmd_xp_ok_no_axioms _ _ _ _ Hx ltac:(assumption)) end; eauto.
    - (* a unit loaded: run from nothing *)
      apply gc_no_axioms_merge; [ assumption |].
      apply gc_no_axioms_cons_unit; match goal with IH : unit_no_axioms _ -> _ -> gc_no_axioms _ |- _ =>
        apply IH; [ eapply Hall; eassumption | exact gc_no_axioms_nil ] end.
    - match goal with IH1 : ccmd_no_axioms ?c' -> _ -> _, Hx : cmd_xp_ok _ _ _ ?c' |- _ =>
        pose proof (cmd_xp_ok_no_axioms _ _ _ _ Hx ltac:(assumption)) end; eauto.
  Qed.

  (** Every state a unit's commands run through, from a global context
      without axioms, has none. *)
  Corollary run_cmds_no_axioms : forall ch fp Γimp Θ F cs Θ' F',
      run_cmds load_path read to_core ch fp Γimp Θ F cs Θ' F' ->
      cmds_no_axioms cs -> gc_no_axioms Θ -> gc_no_axioms Θ'.
  Proof. exact (proj1 (proj2 run_no_axioms)). Qed.

  (** What a program without axioms files, filed with it. *)
  Corollary prog_sem_no_axioms : forall prg Θ U,
      (forall u, to_core prg = Some u -> unit_no_axioms u) ->
      prog_sem load_path read to_core prg Θ U -> gc_no_axioms (gd_unit (prog_path prg) U :: Θ).
  Proof.
    intros * Hp (u & Hu & Hr).
    apply gc_no_axioms_cons_unit.
    exact (proj2 (proj2 (proj2 (proj2 (proj2 run_no_axioms)))) _ _ _ _ _ Hr (Hp _ Hu) gc_no_axioms_nil).
  Qed.
End NoAxioms.
