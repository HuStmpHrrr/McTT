(** * Running Commands

    The executable for the run of [Core.Syntactic.System.Command]: sound
    by construction, since every result carries its [post_*], and complete
    by [run_impl_complete].

    A run maintains:

    - one [Θ] for the whole program, in which every loaded unit is filed once;
    - a table [K] giving the closure of each filed unit, that is, the paths
      of the state its own run ended in;
    - for the unit being run, the closure [D] of what it has imported so far.

    A unit is checked against [gds_restrict D Θ], which [equiv_restrict]
    relates to the judgment's state by weakening in both directions.  Loading
    recurses on the accessibility of the import chain ([load_step]).

    A run is a list of items ([cmd_item]).  A command as written is checked
    for privacy and filled ([Extraction.TypedElab]) to the items it runs as,
    which run before the rest; a core command runs one rule.  A module and
    a record open their frame, the commands of their bodies run in it as
    the items after, and a close files it.  The items' weight ([items_weight])
    decreases with every step: the run ([items_impl]) is well founded on it.

    A run also logs each [eval] it checked, with its normal form
    ([eval_entry], certified by [eval_ok]), and fails with a [run_error]
    carrying the terms involved ([Extraction.Command]). *)

From Stdlib Require Import List String Wellfounded Wf_nat Lia.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base Soundness Completeness.
From Mctt.Core.Consequences Require Import Consistency.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import Structural Command.
From Mctt.Core Require Import TypedElab.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf Paths LookupSound.
From Mctt.Core.Syntactic.System.Inductives Require Import IndRuns Runs.
From Mctt.Core.Syntactic.System.Records Require Import RecordRuns.
From Mctt.Extraction Require Import Lookup NbE TypeCheck GlobalCheck IndDecl RecordDecl MemberType Opens Privacy.
From Mctt.Extraction Require Import MdefGroup TypedElab FastDesc LookupTwins FastState Command.
Import Syntax_Notations GlobalCtx_Notations.

Local Open Scope string_scope.

Section Impl.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option surface_compilation_unit).
  (** The decision of [levels_abstractable] the checker is given *)
  Variable lvd : levels_abstractable_decider.
  (** How the views of a group are found: [ViewsFound.views_search], which
      [Entrypoint] supplies (it is defined over [views_found]). *)
  Variable views_search : forall (F : FCtx) (HΞ : ⊢ᵍ fc_deps F ⍮ fc_stack F) R csD, run_result (views_found (fc_deps F) (fc_stack F) R csD).
  (** The search finds the views whenever there are some. *)
  Hypothesis views_search_complete : forall F HΞ R csD Vs Ss csV Nvs,
      views_ok (fc_deps F) (fc_stack F) R csD Vs Ss csV Nvs -> exists v, views_search F HΞ R csD = run_success v.
  #[local] Abbreviation run_cmd := (run_cmd load_path read to_core).
  #[local] Abbreviation run_cmds := (run_cmds load_path read to_core).
  #[local] Abbreviation run_unit := (run_unit load_path read to_core).
  #[local] Abbreviation canon := (canon load_path read to_core).
  #[local] Abbreviation run_wf := (run_wf load_path read to_core).

  (** ** The Invariants *)

  Definition set_eq (A B : list path) : Prop := forall x, In x A <-> In x B.

  (** A set of paths closed under the closures [K] records. *)
  Definition closed_under_unit_closures (K : unit_closure_map) (D : list path) : Prop :=
    forall x Dx, In x D -> unit_closure_find K x = Some Dx -> incl Dx D.

  (** The records of a map are those [K] keeps. *)
  Definition builtin_records_in (K : unit_closure_map) (Rb : builtins_map) : Prop :=
    forall fp BU, builtins_map_lookup Rb fp = Some BU -> unit_closure_builtins K fp = Some BU.

  (** The records of the judgment's state [ΘR]: canonical, and those [K]
      keeps. *)
  Definition builtin_records_ok (K : unit_closure_map) (ΘR : gdeps) (Rb : builtins_map) : Prop := canon Rb ΘR /\ builtin_records_in K Rb.

  (** A filed unit is what loading its file yields, under a chain starting
      with it, and [K] keeps the record that run ends with.  The state that
      run ended in is filed as well, below the unit in [Θ], and [K] records
      its domain, closed, and the records of what it filed. *)
  #[warnings="-cannot-define-projection"]
  Record entry_ok (Θ : gdeps) (K : unit_closure_map) (fp : path) (U : gunit) : Prop := mk_entry_ok
    { (** the paths the unit's run imported *)
      entry_ok_dom : list path
      (** the record of builtin bindings it ended with *)
    ; entry_ok_builtins : builtins
      (** the contents of its file *)
    ; entry_ok_src : string
      (** the file, parsed *)
    ; entry_ok_prog : Cst.prog
      (** the unit as written *)
    ; entry_ok_unit : surface_compilation_unit
      (** the chain it ran under, after itself *)
    ; entry_ok_chain : list path
      (** the records of the units its run filed *)
    ; entry_ok_rb : builtins_map
      (** the units its run filed *)
    ; entry_ok_deps : gdeps
      (** [K] records its closure *)
    ; entry_ok_unit_closure_find : unit_closure_find K fp = Some entry_ok_dom
      (** and its record *)
    ; entry_ok_unit_closure_builtins : unit_closure_builtins K fp = Some entry_ok_builtins
      (** its closure is closed *)
    ; entry_ok_closed : closed_under_unit_closures K entry_ok_dom
      (** its file is found *)
    ; entry_ok_load : load_path fp = Some entry_ok_src
      (** and parsed *)
    ; entry_ok_read : read entry_ok_src = Some entry_ok_prog
      (** it declares the unit *)
    ; entry_ok_path : prog_path entry_ok_prog = fp
      (** and is elaborated *)
    ; entry_ok_core : to_core entry_ok_prog = Some entry_ok_unit
      (** its run ends with the unit *)
    ; entry_ok_run : run_unit (fp :: entry_ok_chain) entry_ok_unit entry_ok_builtins entry_ok_rb entry_ok_deps U
      (** what it filed is filed below *)
    ; entry_ok_sub_field : entry_ok_deps ⊑ Θ
      (** its closure is what it filed *)
    ; entry_ok_set : set_eq entry_ok_dom (gds_dom entry_ok_deps)
      (** the records of what it filed are kept *)
    ; entry_ok_builtin_records_in : builtin_records_in K entry_ok_rb }.

  (** Each filed unit is [entry_ok] for the units below it. *)
  Fixpoint entries_ok (K : unit_closure_map) (Θ : gdeps) : Prop :=
    match Θ with
    | nil => True
    | (fp, U) :: Θ' => entry_ok Θ' K fp U /\ entries_ok K Θ'
    end.

  (** The invariant of the global state for a run under chain [ch]; in
      particular, nothing on the chain is filed yet. *)
  Record global_invariant (ch : list path) (Θ : gdeps) (K : unit_closure_map) : Prop :=
    { (** the filed units are well formed *)
      gi_wf : ⊢ᵍ Θ ⍮ nil
      (** nothing on the chain is filed *)
    ; gi_chain : forall x, In x ch -> gds_lookup Θ x = None
      (** each filed unit is what loading it yields *)
    ; gi_entry : entries_ok K Θ
      (** every closure recorded is of a filed unit *)
    ; gi_closures_filed : forall fp D, unit_closure_find K fp = Some D -> gds_lookup Θ fp <> None }.

  (** The invariant of the unit being run, relative to the judgment's state
      [ΘR]: the units [D] it imported are those of [ΘR], filed identically
      in [Θ].  The judgment's records are [builtin_records_ok], apart. *)
  Record unit_invariant (ch : list path) (Θ : gdeps) (K : unit_closure_map) (D : list path) (ΘR : gdeps) (Ξ : gstack) : Prop :=
    { (** the global state's invariant *)
      ui_global : global_invariant ch Θ K
      (** the judgment's units are filed identically *)
    ; ui_sub : ΘR ⊑ Θ
      (** and are those imported *)
    ; ui_dom : set_eq D (gds_dom ΘR)
      (** which are closed under their closures *)
    ; ui_closed : closed_under_unit_closures K D
      (** the frames are well formed at the judgment's state *)
    ; ui_wf : ⊢ᵍ ΘR ⍮ Ξ
      (** and of units on the chain *)
    ; ui_stack : stack_in ch Ξ }.

  (** The global state grows: units filed stay filed, and so do their
      closures and records. *)
  Record ext (Θ : gdeps) (K : unit_closure_map) (Θ' : gdeps) (K' : unit_closure_map) : Prop := mk_ext
    { (** the units filed *)
      ext_sub : Θ ⊑ Θ'
      (** their closures *)
    ; ext_unit_closure_find : forall x Dx, unit_closure_find K x = Some Dx -> unit_closure_find K' x = Some Dx
      (** their records *)
    ; ext_unit_closure_builtins : forall x Bx, unit_closure_builtins K x = Some Bx -> unit_closure_builtins K' x = Some Bx }.

  (** Whatever a run files, it imports; hence at the top level the result has
      exactly the domain of the judgment's state. *)
  Definition grows (Θ Θ' : gdeps) (D' : list path) : Prop :=
    forall x, In x (gds_dom Θ') -> In x (gds_dom Θ) \/ In x D'.

  (** The state of a run, in Core: what the invariants and the [post_*]
      read.  The executable keeps it fast ([run_state], [run_state_read]). *)
  Record run_state_core : Set := mk_run_state_core
    { (** every unit filed so far *)
      run_state_core_deps : gdeps
      (** the closure and the record of each filed unit *)
    ; run_state_core_closures : unit_closure_map
      (** what the unit being run imported *)
    ; run_state_core_imports : list path
      (** the builtin bindings *)
    ; run_state_core_builtins : builtins
      (** the open frames *)
    ; run_state_core_stack : gstack }.

  (** The result of a unit's run, in Core *)
  Record unit_result_core : Set := mk_unit_result_core
    { (** every unit filed so far *)
      unit_result_core_deps : gdeps
      (** the closure and the record of each filed unit *)
    ; unit_result_core_closures : unit_closure_map
      (** what the unit imported *)
    ; unit_result_core_imports : list path
      (** the builtin bindings it ends with *)
    ; unit_result_core_builtins : builtins
      (** the unit *)
    ; unit_result_core_unit : gunit }.

  (** The state of a run as the executable keeps it: the filed units and
      the frames fast *)
  Record run_state : Type := mk_run_state
    { (** every unit filed so far *)
      run_state_units : funits
      (** the closure and the record of each filed unit *)
    ; run_state_closures : unit_closure_map
      (** what the unit being run imported *)
    ; run_state_imports : list path
      (** the builtin bindings *)
    ; run_state_builtins : builtins
      (** the open frames *)
    ; run_state_frames : fstack }.

  (** Its Core reading, for types only *)
  Definition run_state_read (r : run_state) : run_state_core :=
    mk_run_state_core (decode_units (run_state_units r)) (run_state_closures r) (run_state_imports r) (run_state_builtins r) (decode_stack (run_state_frames r)).

  (** The result of a unit's run as the executable keeps it *)
  Record unit_result : Type := mk_unit_result
    { (** every unit filed so far *)
      unit_result_units : funits
      (** the closure and the record of each filed unit *)
    ; unit_result_closures : unit_closure_map
      (** what the unit imported *)
    ; unit_result_imports : list path
      (** the builtin bindings it ends with *)
    ; unit_result_builtins : builtins
      (** the unit, fast *)
    ; unit_result_unit : funit }.

  (** Its Core reading, for types only *)
  Definition unit_result_read (r : unit_result) : unit_result_core :=
    mk_unit_result_core (decode_units (unit_result_units r)) (unit_result_closures r) (unit_result_imports r) (unit_result_builtins r) (decode_unit (unit_result_unit r)).

  (** What a run from [Θ ⍮ K] to [r] proves: the judgment, from the
      judgment's state and records the run started at, reaches
      [cmd_post_deps] and [cmd_post_builtin_records] ([run]), and the
      invariants hold again. *)
  #[warnings="-cannot-define-projection"]
  Record cmd_post (run : builtins_map -> gdeps -> Prop) ch (Θ : gdeps) (K : unit_closure_map) (r : run_state_core) : Prop := mk_cmd_post
    { (** the judgment's state at the end *)
      cmd_post_deps : gdeps
      (** the judgment's records at the end *)
    ; cmd_post_builtin_records : builtins_map
      (** the judgment *)
    ; cmd_post_run : run cmd_post_builtin_records cmd_post_deps
      (** the invariant at the end *)
    ; cmd_post_unit_invariant : unit_invariant ch (run_state_core_deps r) (run_state_core_closures r) (run_state_core_imports r) cmd_post_deps (run_state_core_stack r)
      (** the records at the end *)
    ; cmd_post_builtin_records_ok : builtin_records_ok (run_state_core_closures r) cmd_post_deps cmd_post_builtin_records
      (** the global state grew *)
    ; cmd_post_ext : ext Θ K (run_state_core_deps r) (run_state_core_closures r)
      (** by imports only *)
    ; cmd_post_grows : grows Θ (run_state_core_deps r) (run_state_core_imports r) }.

  (** One core command run *)
  Definition post_cmd ch Θ K D B Ξ c (r : run_state_core) : Prop :=
    forall ΘR RbR, unit_invariant ch Θ K D ΘR Ξ -> builtin_records_ok K ΘR RbR ->
      cmd_post (fun RbR' ΘR' => ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ ΘR' ⍮ run_state_core_stack r ⍮ run_state_core_builtins r ⍮ RbR') ch Θ K r.

  (** A list of items run *)
  Definition post_cmds ch Θ K D B Ξ (its : list cmd_item) (r : run_state_core) : Prop :=
    forall ΘR RbR, unit_invariant ch Θ K D ΘR Ξ -> builtin_records_ok K ΘR RbR ->
      cmd_post (fun RbR' ΘR' => ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ its ⇝* ΘR' ⍮ run_state_core_stack r ⍮ run_state_core_builtins r ⍮ RbR') ch Θ K r.

  (** A unit runs from no binding and nothing filed. *)
  #[warnings="-cannot-define-projection"]
  Record unit_post ch (Θ : gdeps) (K : unit_closure_map) (u : surface_compilation_unit) (r : unit_result_core) : Prop := mk_unit_post
    { (** the records of the units its run filed *)
      unit_post_rb : builtins_map
      (** the units its run filed *)
    ; unit_post_deps : gdeps
      (** the run *)
    ; unit_post_run : run_unit ch u (unit_result_core_builtins r) unit_post_rb unit_post_deps (unit_result_core_unit r)
      (** the global invariant at the end *)
    ; unit_post_global_invariant : global_invariant ch (unit_result_core_deps r) (unit_result_core_closures r)
      (** what it filed is filed *)
    ; unit_post_sub : unit_post_deps ⊑ unit_result_core_deps r
      (** and is what it imported *)
    ; unit_post_set : set_eq (unit_result_core_imports r) (gds_dom unit_post_deps)
      (** which is closed under closures *)
    ; unit_post_closed : closed_under_unit_closures (unit_result_core_closures r) (unit_result_core_imports r)
      (** whose records are kept *)
    ; unit_post_builtin_records_in : builtin_records_in (unit_result_core_closures r) unit_post_rb
      (** the global state grew *)
    ; unit_post_ext : ext Θ K (unit_result_core_deps r) (unit_result_core_closures r)
      (** by imports only *)
    ; unit_post_grows : grows Θ (unit_result_core_deps r) (unit_result_core_imports r) }.

  Definition post_unit ch Θ K u (r : unit_result_core) : Prop := global_invariant ch Θ K -> unit_post ch Θ K u r.

  (** ** Consequences of the Invariants *)

  Lemma entry_ok_sub : forall Θ1 Θ2 K fp U, Θ1 ⊑ Θ2 -> entry_ok Θ1 K fp U -> entry_ok Θ2 K fp U.
  Proof.
    intros * Hs [D BU src prg u ch RbU ΘU HK HB Hcl Hl Hr Hp Ht Hu Hsub Hdom HR].
    apply (mk_entry_ok _ _ _ _ D BU src prg u ch RbU ΘU); try assumption.
    eapply gds_sub_trans; eassumption.
  Qed.

  Lemma entries_ok_lookup : forall K Θ, ⊢ᵍ Θ ⍮ nil -> entries_ok K Θ ->
      forall fp U, gds_lookup Θ fp = Some U -> entry_ok Θ K fp U.
  Proof.
    intros K; induction Θ as [| [fq V] Θ IH]; intros Hwf HE fp U HU; [ discriminate |]; destruct HE as [HV HΘ].
    destruct (wf_gstack_file_inv _ _ _ Hwf) as (Hwf0 & _ & Hn).
    apply (entry_ok_sub Θ); [ apply gds_sub_cons, Hn |].
    cbn in HU; destruct (path_beq fp fq) eqn:Hb; [| exact (IH Hwf0 HΘ _ _ HU) ].
    apply path_beq_true in Hb as ->; injection HU as <-; exact HV.
  Qed.

  Lemma global_invariant_entry {ch Θ K} : global_invariant ch Θ K -> forall fp U, gds_lookup Θ fp = Some U -> entry_ok Θ K fp U.
  Proof. intros G; exact (entries_ok_lookup _ _ (gi_wf _ _ _ G) (gi_entry _ _ _ G)). Qed.

  Lemma entries_closure : forall K D Θ, closed_under_unit_closures K D -> entries_ok K Θ -> closure_ok D Θ.
  Proof.
    intros K D; induction Θ as [| [fp U] Θ IH]; intros Hcl HΘ; [ exact I |].
    destruct HΘ as [[Dfp BU src prg u ch0 RbU ΘU HK _ _ _ _ _ _ Hu Hsub Hdom _] HΘ].
    split; [| auto ]; intros Hin.
    destruct (proj1 (proj2 (proj2 run_wf)) _ _ _ _ _ _ Hu) as (_ & _ & HwU); cbn [hd] in HwU.
    exists ΘU; split; [ exact HwU | split; [ exact Hsub |] ].
    intros x Hx; apply (Hcl _ _ Hin HK), Hdom, Hx.
  Qed.

  Lemma global_invariant_restrict_wf {ch Θ K D} : global_invariant ch Θ K -> closed_under_unit_closures K D -> ⊢ᵍ gds_restrict D Θ ⍮ nil.
  Proof. intros G Hcl; exact (restrict_wf _ _ (gi_wf _ _ _ G) (entries_closure _ _ _ Hcl (gi_entry _ _ _ G))). Qed.

  (** A unit with its closure, as [K] records it, is a well-formed context:
      the closure of a filed unit is closed ([entry_ok_closed]). *)
  Lemma global_invariant_closure_wf {ch Θ K fp Dx} : global_invariant ch Θ K -> unit_closure_find K fp = Some Dx ->
      ⊢ᵍ gds_restrict (fp :: Dx) Θ ⍮ nil.
  Proof.
    intros G HD; apply (global_invariant_restrict_wf G).
    destruct (gds_lookup Θ fp) as [U |] eqn:EU; [| exfalso; exact (gi_closures_filed _ _ _ G _ _ HD EU) ].
    destruct (global_invariant_entry G _ _ EU) as [Dfp _ _ _ _ _ _ _ HK _ Hcl _ _ _ _ _ _ _ _].
    rewrite HD in HK; injection HK as <-.
    intros x Dy [<- | Hx] Hy z Hz.
    - rewrite HD in Hy; injection Hy as <-; right; exact Hz.
    - right; exact (Hcl _ _ Hx Hy _ Hz).
  Qed.

  Lemma unit_invariant_in {ch Θ K D ΘR Ξ} : unit_invariant ch Θ K D ΘR Ξ -> forall x, In x D -> gds_lookup Θ x <> None.
  Proof.
    intros Hli x Hx; apply (ui_dom _ _ _ _ _ _ Hli), gds_dom_lookup in Hx.
    destruct (gds_lookup ΘR x) eqn:E; [| contradiction ].
    rewrite (ui_sub _ _ _ _ _ _ Hli _ _ E); discriminate.
  Qed.

  Lemma unit_invariant_equiv {ch Θ K D ΘR Ξ} : unit_invariant ch Θ K D ΘR Ξ -> gds_equiv ΘR (gds_restrict D Θ).
  Proof.
    intros Hli; exact (equiv_restrict _ _ _ (ui_sub _ _ _ _ _ _ Hli) (ui_dom _ _ _ _ _ _ Hli)).
  Qed.

  Lemma unit_invariant_restrict_gctx {ch Θ K D ΘR Ξ} : unit_invariant ch Θ K D ΘR Ξ -> ⊢ᵍ gds_restrict D Θ ⍮ Ξ.
  Proof.
    intros Hli; exact (equiv_gctx _ _ _ (unit_invariant_equiv Hli)
                         (global_invariant_restrict_wf (ui_global _ _ _ _ _ _ Hli) (ui_closed _ _ _ _ _ _ Hli))
                         (ui_wf _ _ _ _ _ _ Hli)).
  Qed.

  Lemma pre_gctx {ch Θ K D Ξ} : (exists ΘR, unit_invariant ch Θ K D ΘR Ξ) -> ⊢ᵍ gds_restrict D Θ ⍮ Ξ.
  Proof. intros [ΘR Hli]; exact (unit_invariant_restrict_gctx Hli). Qed.

  Lemma pre_ctx {ch Θ K D Ξ} : (exists ΘR, unit_invariant ch Θ K D ΘR Ξ) -> ⊢ gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ.
  Proof. intros H; exact (wf_gs_tele _ _ (pre_gctx H)). Qed.

  Lemma unit_invariant_stack {ch Θ K D ΘR Ξ Ξ'} :
    unit_invariant ch Θ K D ΘR Ξ -> ⊢ᵍ ΘR ⍮ Ξ' -> stack_in ch Ξ' -> unit_invariant ch Θ K D ΘR Ξ'.
  Proof. intros [] H Hs; constructor; assumption. Qed.

  (** A command run from a state the invariant holds at, as [run_wf] has
      it *)
  Lemma unit_invariant_run_wf {ch Θ K D B RbR ΘR Ξ c B' RbR' ΘR' Ξ'} :
    unit_invariant ch Θ K D ΘR Ξ -> canon RbR ΘR -> ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
    ⊢ᵍ ΘR' ⍮ Ξ' /\ canon RbR' ΘR' /\ ΘR ⊑ ΘR' /\ builtins_le B B' /\ stack_in ch Ξ'.
  Proof.
    intros Hli Hc Hr;
      exact (proj1 run_wf _ _ _ _ _ _ _ _ _ _ Hr (ui_wf _ _ _ _ _ _ Hli) Hc (ui_stack _ _ _ _ _ _ Hli)).
  Qed.

  (** Items run from a state the invariant holds at *)
  Lemma unit_invariant_runs_wf {ch Θ K D B RbR ΘR Ξ cs B' RbR' ΘR' Ξ'} :
    unit_invariant ch Θ K D ΘR Ξ -> canon RbR ΘR -> ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
    ⊢ᵍ ΘR' ⍮ Ξ' /\ canon RbR' ΘR' /\ ΘR ⊑ ΘR' /\ builtins_le B B' /\ stack_in ch Ξ'.
  Proof.
    intros Hli Hc Hr;
      exact (proj1 (proj2 run_wf) _ _ _ _ _ _ _ _ _ _ Hr (ui_wf _ _ _ _ _ _ Hli) Hc (ui_stack _ _ _ _ _ _ Hli)).
  Qed.

  (** A command that files no unit keeps the invariant. *)
  Lemma unit_invariant_run_same {ch Θ K D B RbR ΘR Ξ c B' Ξ'} :
    unit_invariant ch Θ K D ΘR Ξ -> canon RbR ΘR -> ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ ΘR ⍮ Ξ' ⍮ B' ⍮ RbR -> unit_invariant ch Θ K D ΘR Ξ'.
  Proof.
    intros Hli Hc Hr; destruct (unit_invariant_run_wf Hli Hc Hr) as (Hw & _ & _ & _ & Hs).
    exact (unit_invariant_stack Hli Hw Hs).
  Qed.

  (** A module's frame opened keeps the invariant. *)
  Lemma unit_invariant_push {ch Θ K D ΘR Ξ x Δ l} :
    unit_invariant ch Θ K D ΘR Ξ -> all_assumptions Δ -> gs_fresh x Ξ -> ⊢ gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
    params_evaluated (gds_restrict D Θ) Ξ (gs_tele Ξ) Δ l ->
    ⊢ ΘR ⍮ Ξ ⍮ Δ ++ gs_tele Ξ /\ params_evaluated ΘR Ξ (gs_tele Ξ) Δ l /\
      unit_invariant ch Θ K D ΘR (gs_push (qname_in (gs_path Ξ) x) Δ Ξ).
  Proof.
    intros Hli Htel Hfr HΔ HPr.
    assert (HΔ' : ⊢ ΘR ⍮ Ξ ⍮ Δ ++ gs_tele Ξ)
      by exact (equiv_ctx _ _ _ _ (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) (ui_wf _ _ _ _ _ _ Hli) HΔ).
    pose proof (equiv_params_evaluated _ _ _ _ _ _ (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) (ui_wf _ _ _ _ _ _ Hli) HPr) as HPr'.
    split; [ exact HΔ' | split; [ exact HPr' |] ].
    apply (unit_invariant_stack Hli); [| exact (stack_in_push _ _ _ _ (ui_stack _ _ _ _ _ _ Hli) Hfr) ].
    destruct (params_evaluated_sorts _ _ _ _ _ HPr') as (ps & Hps & HT).
    apply wf_gstack_cons; [ apply (ui_wf _ _ _ _ _ _ Hli) | eapply wf_gmod_nil; eassumption |].
    destruct Ξ as [| [[mp Kq] U] Ξ]; [ contradiction |]; cbn; exists x; split; [ reflexivity | exact Hfr ].
  Qed.

  (** A unit's own frame: its path heads the chain, so it is not filed. *)
  Lemma unit_invariant_push_unit {fp ch Θ K D ΘR P l} :
    unit_invariant (fp :: ch) Θ K D ΘR nil -> all_assumptions P -> ⊢ gds_restrict D Θ ⍮ nil ⍮ P ->
    params_evaluated (gds_restrict D Θ) nil nil P l ->
    ⊢ ΘR ⍮ nil ⍮ P /\ params_evaluated ΘR nil nil P l /\ unit_invariant (fp :: ch) Θ K D ΘR (gs_push (q_abs fp nil) P nil).
  Proof.
    intros Hli Htel HP HPr.
    assert (HP' : ⊢ ΘR ⍮ nil ⍮ P)
      by exact (equiv_ctx _ _ _ _ (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) (ui_wf _ _ _ _ _ _ Hli) HP).
    pose proof (equiv_params_evaluated _ _ _ _ _ _ (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) (ui_wf _ _ _ _ _ _ Hli) HPr) as HPr'.
    split; [ exact HP' | split; [ exact HPr' |] ].
    apply (unit_invariant_stack Hli); [| intros ? ? ? [[= <- <- <-] | []]; left; reflexivity ].
    destruct (params_evaluated_sorts _ _ _ _ _ HPr') as (ps & Hps & HT).
    apply wf_gstack_cons;
      [ apply (ui_wf _ _ _ _ _ _ Hli) | eapply wf_gmod_nil; [ exact Htel | cbn; rewrite app_nil_r; exact HP' | eassumption .. ] |].
    cbn; split; [| reflexivity ].
    exact (sub_none _ _ _ (ui_sub _ _ _ _ _ _ Hli) (gi_chain _ _ _ (ui_global _ _ _ _ _ _ Hli) _ (or_introl eq_refl))).
  Qed.

  Lemma ext_refl : forall Θ K, ext Θ K Θ K.
  Proof. constructor; [ apply gds_sub_refl | auto | auto ]. Qed.

  Lemma ext_trans : forall Θ1 K1 Θ2 K2 Θ3 K3, ext Θ1 K1 Θ2 K2 -> ext Θ2 K2 Θ3 K3 -> ext Θ1 K1 Θ3 K3.
  Proof. intros * [H1 H2 H2'] [H3 H4 H4']; constructor; [ eapply gds_sub_trans; eassumption | auto | auto ]. Qed.

  Lemma grows_refl : forall Θ D, grows Θ Θ D.
  Proof. intros ? ? ? ?; left; assumption. Qed.

  (** Growth composes, when the imports of the later step include those
      of the earlier one. *)
  Lemma grows_trans {Θ0 Θ1 Θ2 D1 D2} : grows Θ0 Θ1 D1 -> grows Θ1 Θ2 D2 -> incl D1 D2 -> grows Θ0 Θ2 D2.
  Proof.
    intros H1 H2 Hi x Hx; destruct (H2 _ Hx) as [Hx1 | Hx1]; [| right; exact Hx1 ].
    destruct (H1 _ Hx1) as [Hx0 | Hx0]; [ left; exact Hx0 | right; exact (Hi _ Hx0) ].
  Qed.

  Lemma closed_under_unit_closures_cons : forall K T fp Dfp Bfp,
      closed_under_unit_closures K T -> (forall y, In y T -> y <> fp) -> closed_under_unit_closures ((fp, (Dfp, Bfp)) :: K) T.
  Proof.
    intros * Hcl Hne y Dy Hy HK; simp unit_closure_find in HK; rewrite (path_beq_false _ _ (Hne _ Hy)) in HK; eauto.
  Qed.

  Lemma builtin_records_in_cons : forall K fp Dfp Bfp Rb,
      (forall y By, builtins_map_lookup Rb y = Some By -> y <> fp) -> builtin_records_in K Rb -> builtin_records_in ((fp, (Dfp, Bfp)) :: K) Rb.
  Proof.
    intros * Hne HR y By Hy; simp unit_closure_builtins; rewrite (path_beq_false _ _ (Hne _ _ Hy)); exact (HR _ _ Hy).
  Qed.

  Lemma entries_ok_cons_K : forall K fp Dfp Bfp Θ,
      (forall y Dy, unit_closure_find K y = Some Dy -> y <> fp) -> (forall y By, unit_closure_builtins K y = Some By -> y <> fp) ->
      (forall y, In y (gds_dom Θ) -> y <> fp) ->
      entries_ok K Θ -> entries_ok ((fp, (Dfp, Bfp)) :: K) Θ.
  Proof.
    intros K fp Dfp Bfp; induction Θ as [| [fq V] Θ IH]; intros HK HKb Hd HΘ; [ exact I |].
    destruct HΘ as [[Dy By src prg u ch RbU ΘUy HKy HBy Hcly Hl Hr Hp Ht Hu Hsuby Hdomy HRy] HΘ].
    split; [| apply IH; [ exact HK | exact HKb | intros y Hy; apply Hd; right; exact Hy | exact HΘ ] ].
    apply (mk_entry_ok _ _ _ _ Dy By src prg u ch RbU ΘUy); try assumption.
    - simp unit_closure_find; rewrite path_beq_false by (eapply HK; eassumption); exact HKy.
    - simp unit_closure_builtins; rewrite path_beq_false by (eapply HK; eassumption); exact HBy.
    - apply closed_under_unit_closures_cons; [ exact Hcly | intros z Hz; apply Hd; right; apply (sub_dom _ _ _ Hsuby), Hdomy, Hz ].
    - intros z Bz Hz; simp unit_closure_builtins; rewrite path_beq_false; [ exact (HRy _ _ Hz) | exact (HKb _ _ (HRy _ _ Hz)) ].
  Qed.

  Lemma global_invariant_nil : forall ch, global_invariant ch nil nil.
  Proof. intros; constructor; [ constructor | reflexivity | exact I | discriminate ]. Qed.

  Lemma nil_unit_invariant {ch Θ K} : global_invariant ch Θ K -> unit_invariant ch Θ K nil nil nil.
  Proof.
    intros G; constructor; [ exact G | discriminate | intros ?; cbn; tauto | intros ? ? [] | | intros ? ? ? [] ].
    constructor; constructor; constructor.
  Qed.

  Lemma builtin_records_ok_nil : forall K, builtin_records_ok K nil nil.
  Proof. intros; split; [ apply canon_nil | intros ? ? H; discriminate H ]. Qed.

  (** The records [K] keeps of the units of [ΘR]: the judgment's records
      exist whenever its state does. *)
  Fixpoint builtin_records_of (K : unit_closure_map) (Θ : gdeps) : builtins_map :=
    match Θ with
    | nil => nil
    | (fp, _) :: Θ' => match unit_closure_builtins K fp with Some B => (fp, B) :: builtin_records_of K Θ' | None => builtin_records_of K Θ' end
    end.

  Lemma builtins_map_lookup_builtin_records_of : forall K Θ fp,
      builtins_map_lookup (builtin_records_of K Θ) fp = match gds_lookup Θ fp with Some _ => unit_closure_builtins K fp | None => None end.
  Proof.
    intros K; induction Θ as [| [fq V] Θ IH]; intros fp; [ reflexivity |]; cbn [builtin_records_of gds_lookup].
    destruct (unit_closure_builtins K fq) as [Bq |] eqn:Eq; cbn [builtins_map_lookup]; destruct (path_beq fp fq) eqn:Hb;
      try (apply path_beq_true in Hb as ->); rewrite ?IH; try reflexivity;
      try (symmetry; exact Eq); destruct (gds_lookup Θ fq); congruence.
  Qed.

  Lemma unit_invariant_builtin_records {ch Θ K D ΘR Ξ} : unit_invariant ch Θ K D ΘR Ξ -> exists RbR, builtin_records_ok K ΘR RbR.
  Proof.
    intros Hli; exists (builtin_records_of K ΘR); split; [ split |].
    - intros fp U HU.
      destruct (global_invariant_entry (ui_global _ _ _ _ _ _ Hli) _ _ (ui_sub _ _ _ _ _ _ Hli _ _ HU))
        as [D0 BU src prg u ch0 RbU ΘU _ HB _ Hl Hr _ Ht Hu _ _ _].
      apply (mk_canon_entry _ _ _ _ _ _ BU src prg u ch0 RbU ΘU); [ rewrite builtins_map_lookup_builtin_records_of, HU; exact HB | assumption .. ].
    - intros fp BU HB; rewrite builtins_map_lookup_builtin_records_of in HB; destruct (gds_lookup ΘR fp); [ discriminate | discriminate HB ].
    - intros fp BU HB; rewrite builtins_map_lookup_builtin_records_of in HB; destruct (gds_lookup ΘR fp); [ exact HB | discriminate HB ].
  Qed.

  (** Where a command ends, the invariant holds. *)
  Lemma cmd_post_pre {ch Θ K D B Ξ c r} :
    (exists ΘR, unit_invariant ch Θ K D ΘR Ξ) -> post_cmd ch Θ K D B Ξ c r ->
    exists ΘR, unit_invariant ch (run_state_core_deps r) (run_state_core_closures r) (run_state_core_imports r) ΘR (run_state_core_stack r).
  Proof.
    intros [ΘR Hli] Hp; destruct (unit_invariant_builtin_records Hli) as [RbR Hrb].
    destruct (Hp _ _ Hli Hrb) as [ΘR' RbR' _ Hli' _ _ _]; eauto.
  Qed.

  (** Where items end, the invariant holds. *)
  Lemma cmds_post_pre {ch Θ K D B Ξ cs r} :
    (exists ΘR, unit_invariant ch Θ K D ΘR Ξ) -> post_cmds ch Θ K D B Ξ cs r ->
    exists ΘR, unit_invariant ch (run_state_core_deps r) (run_state_core_closures r) (run_state_core_imports r) ΘR (run_state_core_stack r).
  Proof.
    intros [ΘR Hli] Hp; destruct (unit_invariant_builtin_records Hli) as [RbR Hrb].
    destruct (Hp _ _ Hli Hrb) as [ΘR' RbR' _ Hli' _ _ _]; eauto.
  Qed.

  (** ** One Step per Rule

      Each lemma proves the [post_*] of one branch of the executable from the
      checks that branch makes, at the restriction. *)

  (** A step that files no unit and makes no binding, from the run at the
      judgment's state *)
  Lemma same_post {ch Θ K D B Ξ c Ξ' B'} :
    (forall ΘR RbR, unit_invariant ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ ΘR ⍮ Ξ' ⍮ B' ⍮ RbR) ->
    post_cmd ch Θ K D B Ξ c (mk_run_state_core Θ K D B' Ξ').
  Proof.
    intros Hr ΘR RbR Hli Hrb; cbn [run_state_core_deps run_state_core_closures run_state_core_imports run_state_core_builtins run_state_core_stack].
    pose proof (Hr _ RbR Hli) as Hr'.
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR);
      [ exact Hr' | exact (unit_invariant_run_same Hli (proj1 Hrb) Hr') | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  Lemma def_ok {ch Θ K D B Ξ x b pv κ A M} {i : nat} :
    gs_fresh x Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : abs_kind_sort κ Typeω@i ->
    (κ = ak_level -> level_sorted_parameters (gs_tele Ξ)) -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    post_cmd ch Θ K D B Ξ (core_cmd_def x b pv κ A (Some M)) (mk_run_state_core Θ K D B (gs_add x (gs_def b pv κ Ξ A M) Ξ)).
  Proof.
    intros Hfr HA Hlv HM; apply same_post; intros ΘR RbR Hli.
    pose proof (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) as He.
    eapply run_cmd_def; [ exact (equiv_exp _ _ _ _ _ _ He (ui_wf _ _ _ _ _ _ Hli) HA) | exact Hlv
                        | exact (equiv_exp _ _ _ _ _ _ He (ui_wf _ _ _ _ _ _ Hli) HM) | exact Hfr ].
  Qed.

  Lemma axiom_ok {ch Θ K D B Ξ x b pv κ A} {i : nat} :
    gs_fresh x Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : abs_kind_sort κ Typeω@i -> κ <> ak_level ->
    post_cmd ch Θ K D B Ξ (core_cmd_def x b pv κ A None) (mk_run_state_core Θ K D B (gs_add x (gs_axiom b pv κ Ξ A) Ξ)).
  Proof.
    intros Hfr HA Hk; apply same_post; intros ΘR RbR Hli.
    eapply run_cmd_axiom; [ exact (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) (ui_wf _ _ _ _ _ _ Hli) HA)
                          | exact Hk | exact Hfr ].
  Qed.

  Lemma eval_ok {ch Θ K D B Ξ M A} :
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    post_cmd ch Θ K D B Ξ (core_cmd_eval M A) (mk_run_state_core Θ K D B Ξ).
  Proof.
    intros HM; apply same_post; intros ΘR RbR Hli.
    constructor; exact (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) (ui_wf _ _ _ _ _ _ Hli) HM).
  Qed.

  (** A builtin binding, with the premises of [run_cmd_builtin] at the
      restriction. *)
  Lemma builtin_ok {ch Θ K D B Ξ E M W p Dd z s B'} :
    modexp_as_term E = Some M ->
    @alg_type_infer (gc_mk (gds_restrict D Θ) Ξ) (gs_tele Ξ) W M ->
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : nf_to_exp W ->
    nf_is_universe W ->
    nbe (gds_restrict D Θ) Ξ (gs_tele Ξ) M (nf_to_exp W) (nf_indty p 0 nil) ->
    ind_lookup (gds_restrict D Θ) Ξ p = Some Dd -> nat_shape Dd = Some (z, s) -> ind_sort Dd = nat_sort ->
    builtins_bind_nat B p = Some B' ->
    post_cmd ch Θ K D B Ξ (core_cmd_builtin nat_kind E) (mk_run_state_core Θ K D B' Ξ).
  Proof.
    intros Ht HW HM Hu Hn Hl Hs Hsort Hb; apply same_post; intros ΘR RbR Hli.
    pose proof (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) as He.
    eapply run_cmd_builtin; [ exact Ht | exact (equiv_alg_infer _ _ _ _ _ _ He (ui_wf _ _ _ _ _ _ Hli) HW)
                         | exact (equiv_exp _ _ _ _ _ _ He (ui_wf _ _ _ _ _ _ Hli) HM) | exact Hu
                         | exact (equiv_nbe _ _ _ He _ _ _ _ Hn)
                         | rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); exact Hl
                         | exact Hs | exact Hsort | exact Hb ].
  Qed.

  (** A module's frame opened, with the premises of [run_cmd_mod_open] at
      the restriction. *)
  Lemma mod_open_ok {ch Θ K D B Ξ x pv Δ l} :
    all_assumptions Δ -> gs_fresh x Ξ -> ⊢ gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
    params_evaluated (gds_restrict D Θ) Ξ (gs_tele Ξ) Δ l ->
    post_cmd ch Θ K D B Ξ (core_cmd_mod_open x pv Δ) (mk_run_state_core Θ K D B (gs_push (qname_in (gs_path Ξ) x) Δ Ξ)).
  Proof.
    intros Htel Hfr HΔ HPr ΘR RbR Hli Hrb; cbn [run_state_core_deps run_state_core_closures run_state_core_imports run_state_core_builtins run_state_core_stack].
    destruct (unit_invariant_push Hli Htel Hfr HΔ HPr) as (HΔ' & HPr' & Hli').
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR);
      [ eapply run_cmd_mod_open; eassumption | exact Hli' | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  (** The frame of a module on top closed, as [run_cmd_close_mod] files
      it. *)
  Lemma close_mod_ok {ch Θ K D B Ξ x pv U} :
    gs_fresh x Ξ ->
    post_cmd ch Θ K D B ((qname_in (gs_path Ξ) x, fk_module, U) :: Ξ) (core_cmd_close x pv)
      (mk_run_state_core Θ K D B (gs_add x (ge_body pv (gu_params U) (gu_mod U)) Ξ)).
  Proof.
    intros Hfr; apply same_post; intros ΘR RbR Hli.
    eapply run_cmd_close_mod; [ reflexivity | exact Hfr ].
  Qed.

  (** The frame of a record's module on top closed, as
      [run_cmd_close_record] files it. *)
  Lemma close_record_ok {ch Θ K D B Ξ x pv R U} :
    gs_fresh x Ξ ->
    post_cmd ch Θ K D B ((ind_qname Ξ x, fk_record R, U) :: Ξ) (core_cmd_close x pv)
      (mk_run_state_core Θ K D B (gs_add x (ge_record pv (ind_qname Ξ x) R (gu_mod U)) Ξ)).
  Proof.
    intros Hfr; apply same_post; intros ΘR RbR Hli.
    eapply run_cmd_close_record; [ reflexivity | exact Hfr ].
  Qed.

  Lemma alias_ok {ch Θ K D B Ξ x pv Δ l E} :
    all_assumptions Δ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ ->
    gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E -> params_evaluated (gds_restrict D Θ) Ξ (gs_tele Ξ) Δ l ->
    levels_abstractable (gds_restrict D Θ) Ξ ⋅ (Δ ++ gs_tele Ξ) E -> gs_fresh x Ξ ->
    post_cmd ch Θ K D B Ξ (core_cmd_alias x pv Δ E) (mk_run_state_core Θ K D B (gs_add x (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))) Ξ)).
  Proof.
    intros Htel HΔ HE HPr Hlv Hfr; apply same_post; intros ΘR RbR Hli.
    pose proof (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) as Heq; pose proof (ui_wf _ _ _ _ _ _ Hli) as HΞ.
    eapply run_cmd_alias; [ exact Htel | exact (equiv_ext _ _ _ _ _ Heq HΞ HΔ) | exact (equiv_modexp _ _ _ _ _ Heq HΞ HE)
                          | exact (equiv_params_evaluated _ _ _ _ _ _ Heq HΞ HPr)
                          | exact (equiv_levels_abstractable _ _ _ Heq HΞ _ _ _ Hlv) | exact Hfr ].
  Qed.

  (** An inductive alias, with the premises of [run_cmd_ind_alias] at the
      restriction. *)
  Lemma indalias_ok {ch Θ K D B Ξ x pv Δ l E M W} {i : nat} :
    all_assumptions Δ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ ->
    gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    params_evaluated (gds_restrict D Θ) Ξ (gs_tele Ξ) Δ l ->
    modexp_as_term E = Some M ->
    @alg_type_infer (gc_mk (gds_restrict D Θ) Ξ) (Δ ++ gs_tele Ξ) W M ->
    gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ nf_to_exp W : Typeω@i ->
    gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ M : nf_to_exp W ->
    ind_former (gds_restrict D Θ) Ξ (Δ ++ gs_tele Ξ) M W ->
    levels_abstractable (gds_restrict D Θ) Ξ ⋅ (Δ ++ gs_tele Ξ) E ->
    gs_fresh x Ξ ->
    post_cmd ch Θ K D B Ξ (core_cmd_inductive_alias x pv Δ E) (mk_run_state_core Θ K D B (gs_add x (dm_entry Ξ pv Δ (nf_to_exp W) M E) Ξ)).
  Proof.
    intros Htel HΔ HE HPr Ht HW HWt HM Hf Hlv Hfr; apply same_post; intros ΘR RbR Hli.
    pose proof (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) as Heq; pose proof (ui_wf _ _ _ _ _ _ Hli) as HΞ.
    eapply run_cmd_ind_alias; [ exact Htel | exact (equiv_ext _ _ _ _ _ Heq HΞ HΔ) | exact (equiv_modexp _ _ _ _ _ Heq HΞ HE)
                              | exact (equiv_params_evaluated _ _ _ _ _ _ Heq HΞ HPr) | exact Ht
                              | exact (equiv_alg_infer _ _ _ _ _ _ Heq HΞ HW)
                              | exact (equiv_exp _ _ _ _ _ _ Heq HΞ HWt) | exact (equiv_exp _ _ _ _ _ _ Heq HΞ HM)
                              | exact (equiv_ind_former _ _ _ _ _ _ Heq Hf)
                              | exact (equiv_levels_abstractable _ _ _ Heq HΞ _ _ _ Hlv) | exact Hfr ].
  Qed.

  (** A record alias, with the premises of [run_cmd_record_alias] at the
      restriction. *)
  Lemma recalias_ok {ch Θ K D B Ξ x pv Δ l E M W} {i : nat} :
    all_assumptions Δ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ ->
    gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    params_evaluated (gds_restrict D Θ) Ξ (gs_tele Ξ) Δ l ->
    modexp_as_term E = Some M ->
    @alg_type_infer (gc_mk (gds_restrict D Θ) Ξ) (Δ ++ gs_tele Ξ) W M ->
    gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ nf_to_exp W : Typeω@i ->
    gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ M : nf_to_exp W ->
    record_former (gds_restrict D Θ) Ξ (Δ ++ gs_tele Ξ) M W ->
    levels_abstractable (gds_restrict D Θ) Ξ ⋅ (Δ ++ gs_tele Ξ) E ->
    gs_fresh x Ξ ->
    post_cmd ch Θ K D B Ξ (core_cmd_record_alias x pv Δ E) (mk_run_state_core Θ K D B (gs_add x (dm_entry Ξ pv Δ (nf_to_exp W) M E) Ξ)).
  Proof.
    intros Htel HΔ HE HPr Ht HW HWt HM Hf Hlv Hfr; apply same_post; intros ΘR RbR Hli.
    pose proof (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) as Heq; pose proof (ui_wf _ _ _ _ _ _ Hli) as HΞ.
    eapply run_cmd_record_alias; [ exact Htel | exact (equiv_ext _ _ _ _ _ Heq HΞ HΔ) | exact (equiv_modexp _ _ _ _ _ Heq HΞ HE)
                                 | exact (equiv_params_evaluated _ _ _ _ _ _ Heq HΞ HPr) | exact Ht
                                 | exact (equiv_alg_infer _ _ _ _ _ _ Heq HΞ HW)
                                 | exact (equiv_exp _ _ _ _ _ _ Heq HΞ HWt) | exact (equiv_exp _ _ _ _ _ _ Heq HΞ HM)
                                 | exact (equiv_record_former _ _ _ _ _ _ Heq Hf)
                                 | exact (equiv_levels_abstractable _ _ _ Heq HΞ _ _ _ Hlv) | exact Hfr ].
  Qed.

  (** A mutual definition, with the premises of [run_cmd_mdef] at the
      restriction: its definitions are filed on the stack [Ξ'] their run
      ends at. *)
  Lemma mdef_ok {ch Θ K D B Ξ Ξ' b pv Δ f0 fs pq m0 Ps Dd Us ms} :
    all_assumptions Δ ->
    ⊢ gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
    mdef_group (gds_restrict D Θ) Ξ Δ (raw_fun_head_of f0) (List.map raw_fun_head_of fs) pq m0 Ps Dd Us ms ->
    mdefs_run (gds_restrict D Θ) b pv (mdef_defs pq Dd Us Δ (f0 :: fs) ms) Ξ Ξ' ->
    post_cmd ch Θ K D B Ξ (core_cmd_mdef b pv Δ (f0 :: fs)) (mk_run_state_core Θ K D B Ξ').
  Proof.
    intros Htel HΔ Hgp Hr; apply same_post; intros ΘR RbR Hli.
    pose proof (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) as Heq; pose proof (ui_wf _ _ _ _ _ _ Hli) as HΞ.
    eapply run_cmd_mdef;
      [ exact Htel | exact (equiv_ctx _ _ _ _ Heq HΞ HΔ) | exact (equiv_mdef_group _ _ _ _ _ _ _ _ _ _ _ _ Heq HΞ Hgp)
      | exact (equiv_mdefs_run _ _ _ _ _ _ _ Heq HΞ Hr) ].
  Qed.

  (** *** Loads *)

  (** A unit the unit being run imported already: its record, kept in [K],
      is merged in again. *)
  Lemma load_in_ok {ch Θ K D B Ξ fp U BU B'} :
    In fp D -> gds_lookup Θ fp = Some U -> unit_closure_builtins K fp = Some BU -> builtins_merge B BU = Some B' ->
    post_cmd ch Θ K D B Ξ (core_cmd_load fp) (mk_run_state_core Θ K D B' Ξ).
  Proof.
    intros Hin HU HB Hm ΘR RbR Hli Hrb; cbn [run_state_core_deps run_state_core_closures run_state_core_imports run_state_core_builtins run_state_core_stack].
    apply (ui_dom _ _ _ _ _ _ Hli), gds_dom_lookup in Hin.
    destruct (gds_lookup ΘR fp) as [V |] eqn:E'; [| contradiction ].
    destruct (proj1 (proj1 Hrb) _ _ E') as [BU' src prg u ch0 RbU ΘU EB _ _ _ _].
    pose proof (proj2 Hrb _ _ EB) as HB'; rewrite HB in HB'; injection HB' as <-.
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ core_cmd_load fp ⇝ ΘR ⍮ Ξ ⍮ B' ⍮ RbR) by (eapply run_cmd_load_filed; eassumption).
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR); [ exact Hr | exact Hli | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  (** A record kept in [K] is of a unit [K] has the closure of. *)
  Lemma unit_closure_builtins_unit_closure_find : forall K fp B, unit_closure_builtins K fp = Some B -> exists D, unit_closure_find K fp = Some D.
  Proof.
    induction K as [| [fq [Dq Bq]] K IH]; intros fp B H; simp unit_closure_builtins in H; [ discriminate |].
    simp unit_closure_find; destruct (path_beq fp fq); [ eauto | exact (IH _ _ H) ].
  Qed.

  (** Loading a filed unit that the unit being run has not imported yet:
      the judgment loads it, which the entry of [Θ] justifies once the chain
      is changed; it ends with the record [K] keeps. *)
  Lemma hit_unit_invariant {ch Θ K D Ξ fp U Dfp BU} :
    ~ In fp D -> gds_lookup Θ fp = Some U -> unit_closure_find K fp = Some Dfp -> unit_closure_builtins K fp = Some BU ->
    forall ΘR RbR, unit_invariant ch Θ K D ΘR Ξ -> builtin_records_ok K ΘR RbR ->
    exists src prg u RbU ΘU, gds_lookup ΘR fp = None /\ ~ In fp ch /\ load_path fp = Some src /\
      read src = Some prg /\ prog_path prg = fp /\ to_core prg = Some u /\ run_unit (fp :: ch) u BU RbU ΘU U /\
      unit_invariant ch Θ K (p_union D (fp :: Dfp)) (gds_merge ΘR ((fp, U) :: ΘU)) Ξ /\
      builtin_records_ok K (gds_merge ΘR ((fp, U) :: ΘU)) (builtins_map_merge RbR ((fp, BU) :: RbU)).
  Proof.
    intros Hnin HU HK HB ΘR RbR Hli Hrb.
    pose proof (ui_global _ _ _ _ _ _ Hli) as G.
    destruct (global_invariant_entry G _ _ HU)
      as [Dfp' BU' src prg u ch0 RbU ΘU HK' HB' Hcl Hl Hrd Hp Ht Hu Hsub Hdom HRU].
    rewrite HK in HK'; injection HK' as <-; rewrite HB in HB'; injection HB' as <-.
    assert (Hn : gds_lookup ΘR fp = None)
      by (apply gds_dom_none; intros Hin; apply Hnin, (ui_dom _ _ _ _ _ _ Hli), Hin).
    assert (Hnch : ~ In fp ch) by (intros Hin; rewrite (gi_chain _ _ _ G _ Hin) in HU; discriminate).
    assert (Hu' : run_unit (fp :: ch) u BU RbU ΘU U).
    { apply (proj1 (proj2 (proj2 (run_chain_irrel load_path read to_core))) _ _ _ _ _ _ Hu ch).
      intros x [<- | Hin].
      - exact (proj1 (proj2 (proj2 (run_chain_fresh load_path read to_core))) _ _ _ _ _ _ Hu _ (or_introl eq_refl)).
      - exact (sub_none _ _ _ Hsub (gi_chain _ _ _ G _ Hin)). }
    destruct (load_wf load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ (ui_wf _ _ _ _ _ _ Hli) (proj1 Hrb)
                (ui_stack _ _ _ _ _ _ Hli) Hn Hnch Hl Hrd Ht Hu') as (Hwf' & Hc' & _).
    exists src, prg, u, RbU, ΘU; do 7 (split; [ assumption |]).
    split; [ constructor; [ exact G | | | | exact Hwf' | exact (ui_stack _ _ _ _ _ _ Hli) ] |].
    - intros y V HV; apply merge_inv in HV as [HV | HV]; [ exact (ui_sub _ _ _ _ _ _ Hli _ _ HV) |].
      cbn in HV; destruct (path_beq y fp) eqn:Hb; [| exact (Hsub _ _ HV) ].
      apply path_beq_true in Hb as ->; injection HV as <-; exact HU.
    - intros y; rewrite p_union_iff, dom_merge, dom_cons, <- (ui_dom _ _ _ _ _ _ Hli y), <- (Hdom y); cbn [In].
      intuition congruence.
    - intros y Dy Hy HKy; apply p_union_iff in Hy as [Hy | [<- | Hy]]; intros z Hz; apply p_union_iff.
      + left; exact (ui_closed _ _ _ _ _ _ Hli _ _ Hy HKy _ Hz).
      + rewrite HK in HKy; injection HKy as <-; right; right; exact Hz.
      + right; right; exact (Hcl _ _ Hy HKy _ Hz).
    - split; [ exact Hc' |].
      intros y By Hy; rewrite builtins_map_lookup_merge in Hy; destruct (builtins_map_lookup RbR y) eqn:E.
      + injection Hy as <-; exact (proj2 Hrb _ _ E).
      + cbn in Hy; destruct (path_beq y fp) eqn:Hb; [ apply path_beq_true in Hb as ->; injection Hy as <-; exact HB | exact (HRU _ _ Hy) ].
  Qed.

  Lemma load_hit_ok {ch Θ K D B Ξ fp U Dfp BU B'} :
    ~ In fp D -> gds_lookup Θ fp = Some U -> unit_closure_find K fp = Some Dfp -> unit_closure_builtins K fp = Some BU -> builtins_merge B BU = Some B' ->
    post_cmd ch Θ K D B Ξ (core_cmd_load fp) (mk_run_state_core Θ K (p_union D (fp :: Dfp)) B' Ξ).
  Proof.
    intros Hnin HU HK HB Hm ΘR RbR Hli Hrb; cbn [run_state_core_deps run_state_core_closures run_state_core_imports run_state_core_builtins run_state_core_stack].
    destruct (hit_unit_invariant Hnin HU HK HB _ _ Hli Hrb) as (src & prg & u & RbU & ΘU & Hn & Hnch & Hl & Hrd & Hp & Ht & Hu & Hli' & Hrb').
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ core_cmd_load fp ⇝ gds_merge ΘR ((fp, U) :: ΘU) ⍮ Ξ ⍮ B' ⍮ builtins_map_merge RbR ((fp, BU) :: RbU))
      by (eapply run_cmd_load; eassumption).
    apply (mk_cmd_post _ _ _ _ _ (gds_merge ΘR ((fp, U) :: ΘU)) (builtins_map_merge RbR ((fp, BU) :: RbU)));
      [ exact Hr | exact Hli' | exact Hrb' | apply ext_refl | apply grows_refl ].
  Qed.

  Lemma load_pre {ch Θ K D Ξ fp} :
    (exists ΘR, unit_invariant ch Θ K D ΘR Ξ) -> gds_lookup Θ fp = None -> ~ In fp ch -> global_invariant (fp :: ch) Θ K.
  Proof.
    intros [ΘR Hli] Hn Hnch; pose proof (ui_global _ _ _ _ _ _ Hli) as [].
    constructor; auto; intros x [<- | Hx]; auto.
  Qed.

  (** A loaded unit is filed on top of everything its run filed, which holds
      the state the judgment's run ended in, with the record it ended with;
      the bindings are [B'], that record merged in. *)
  Definition load_state (fp : path) (D : list path) (Ξ : gstack) (B' : builtins) (r : unit_result_core) : run_state_core :=
    mk_run_state_core ((fp, unit_result_core_unit r) :: unit_result_core_deps r) ((fp, (unit_result_core_imports r, unit_result_core_builtins r)) :: unit_result_core_closures r) (p_union D (fp :: unit_result_core_imports r)) B' Ξ.

  Lemma load_unit_invariant {ch Θ K D Ξ fp src prg u r B'} :
    gds_lookup Θ fp = None -> ~ In fp ch ->
    load_path fp = Some src -> read src = Some prg -> prog_path prg = fp -> to_core prg = Some u ->
    post_unit (fp :: ch) Θ K u r -> forall ΘR RbR, unit_invariant ch Θ K D ΘR Ξ -> builtin_records_ok K ΘR RbR ->
    exists RbU ΘU, gds_lookup ΘR fp = None /\ run_unit (fp :: ch) u (unit_result_core_builtins r) RbU ΘU (unit_result_core_unit r) /\
      unit_invariant ch (run_state_core_deps (load_state fp D Ξ B' r)) (run_state_core_closures (load_state fp D Ξ B' r)) (run_state_core_imports (load_state fp D Ξ B' r))
        (gds_merge ΘR ((fp, unit_result_core_unit r) :: ΘU)) Ξ /\
      builtin_records_ok (run_state_core_closures (load_state fp D Ξ B' r)) (gds_merge ΘR ((fp, unit_result_core_unit r) :: ΘU)) (builtins_map_merge RbR ((fp, unit_result_core_builtins r) :: RbU)) /\
      ext Θ K (run_state_core_deps (load_state fp D Ξ B' r)) (run_state_core_closures (load_state fp D Ξ B' r)) /\
      grows Θ (run_state_core_deps (load_state fp D Ξ B' r)) (run_state_core_imports (load_state fp D Ξ B' r)).
  Proof.
    intros Hn Hnch Hl Hrd Hp Ht Hpost ΘR RbR Hli Hrb.
    pose proof (ui_global _ _ _ _ _ _ Hli) as G.
    assert (Gin : global_invariant (fp :: ch) Θ K) by (eapply load_pre; [ exists ΘR; exact Hli | assumption | assumption ]).
    destruct r as [Θ1 K1 Dfp B1 U]; unfold load_state; cbn [unit_result_core_deps unit_result_core_closures unit_result_core_imports unit_result_core_builtins unit_result_core_unit run_state_core_deps run_state_core_closures run_state_core_imports run_state_core_builtins run_state_core_stack] in *.
    destruct (Hpost Gin) as [RbU ΘU Hu G1 Hsub1 Hdom1 Hcl1 HRU [Hext1 HextK HextB] Hgr1].
    cbn [unit_result_core_deps unit_result_core_closures unit_result_core_imports unit_result_core_builtins unit_result_core_unit] in *.
    destruct (proj1 (proj2 (proj2 run_wf)) _ _ _ _ _ _ Hu) as (HwU & HcU & HUu); cbn [hd] in HUu.
    assert (HnR : gds_lookup ΘR fp = None) by exact (sub_none _ _ _ (ui_sub _ _ _ _ _ _ Hli) Hn).
    destruct (load_wf load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ (ui_wf _ _ _ _ _ _ Hli) (proj1 Hrb)
                (ui_stack _ _ _ _ _ _ Hli) HnR Hnch Hl Hrd Ht Hu) as (Hwf' & Hc' & _).
    assert (Hn1 : gds_lookup Θ1 fp = None) by exact (gi_chain _ _ _ G1 _ (or_introl eq_refl)).
    set (ΘN := (fp, U) :: Θ1).
    assert (HwN : ⊢ᵍ ΘN ⍮ nil).
    { apply wf_gstack_file'; [ exact (gi_wf _ _ _ G1) | | exact Hn1 ].
      eapply unit_deps_grow; [ exact Hsub1 | exact (gi_wf _ _ _ G1) | exact Hn1 | exact HUu ]. }
    assert (Hsub1N : Θ1 ⊑ ΘN) by exact (gds_sub_cons _ _ _ Hn1).
    assert (HfpN : gds_lookup ΘN fp = Some U) by (cbn; rewrite path_beq_refl; reflexivity).
    assert (HsubU : ΘU ⊑ ΘN) by exact (gds_sub_trans _ _ _ Hsub1 Hsub1N).
    assert (HK1 : forall y Dy, unit_closure_find K1 y = Some Dy -> y <> fp)
      by (intros y Dy HKy ->; exact (gi_closures_filed _ _ _ G1 _ _ HKy Hn1)).
    assert (HKb1 : forall y By, unit_closure_builtins K1 y = Some By -> y <> fp)
      by (intros y By HKy; destruct (unit_closure_builtins_unit_closure_find _ _ _ HKy) as [Dy HKy']; exact (HK1 _ _ HKy')).
    assert (Hd1 : forall y, In y (gds_dom Θ1) -> y <> fp)
      by (intros y Hy ->; apply gds_dom_lookup in Hy; contradiction).
    assert (Hdfp : forall y, In y Dfp -> y <> fp)
      by (intros y Hy; apply Hd1, (sub_dom _ _ _ Hsub1), Hdom1, Hy).
    assert (HRU' : builtin_records_in ((fp, (Dfp, B1)) :: K1) RbU)
      by (apply builtin_records_in_cons; [ intros y By Hy; exact (HKb1 _ _ (HRU _ _ Hy)) | exact HRU ]).
    assert (GN : global_invariant ch ΘN ((fp, (Dfp, B1)) :: K1)).
    { constructor; [ exact HwN | | | ].
      - intros y Hy; cbn; rewrite path_beq_false by (intros ->; contradiction).
        exact (gi_chain _ _ _ G1 _ (or_intror Hy)).
      - split; [| exact (entries_ok_cons_K _ _ _ _ _ HK1 HKb1 Hd1 (gi_entry _ _ _ G1)) ].
        apply (mk_entry_ok _ _ _ _ Dfp B1 src prg u ch RbU ΘU);
          [ simp unit_closure_find; rewrite path_beq_refl; reflexivity | simp unit_closure_builtins; rewrite path_beq_refl; reflexivity
          | exact (closed_under_unit_closures_cons _ _ _ _ _ Hcl1 Hdfp) | assumption .. ].
      - intros y Dy HKy; simp unit_closure_find in HKy; destruct (path_beq y fp) eqn:Hb.
        + apply path_beq_true in Hb as ->; rewrite HfpN; discriminate.
        + intros E; apply (gi_closures_filed _ _ _ G1 _ _ HKy), (sub_none _ _ _ Hsub1N), E. }
    assert (Hfresh : forall y, gds_lookup Θ y <> None -> y <> fp) by (intros y Hy ->; contradiction).
    exists RbU, ΘU; cbn [run_state_core_deps run_state_core_closures run_state_core_imports run_state_core_builtins run_state_core_stack unit_result_core_deps unit_result_core_closures unit_result_core_imports unit_result_core_builtins unit_result_core_unit].
    split; [ exact HnR | split; [ exact Hu |] ].
    split; [| split; [| split ] ].
    - constructor; [ exact GN | | | | exact Hwf' | exact (ui_stack _ _ _ _ _ _ Hli) ].
      + intros y V HV; apply merge_inv in HV as [HV | HV].
        * exact (Hsub1N _ _ (Hext1 _ _ (ui_sub _ _ _ _ _ _ Hli _ _ HV))).
        * cbn in HV; destruct (path_beq y fp) eqn:Hb; [| exact (HsubU _ _ HV) ].
          apply path_beq_true in Hb as ->; injection HV as <-; exact HfpN.
      + intros y; rewrite p_union_iff, dom_merge, dom_cons, <- (ui_dom _ _ _ _ _ _ Hli y), <- (Hdom1 y); cbn [In].
        intuition congruence.
      + intros y Dy Hy HKy; simp unit_closure_find in HKy; destruct (path_beq y fp) eqn:Hb.
        * apply path_beq_true in Hb as ->; injection HKy as <-; intros z Hz; apply p_union_iff; right; right; exact Hz.
        * intros z Hz; apply p_union_iff; apply p_union_iff in Hy as [Hy | [<- | Hy]].
          -- left; pose proof (unit_invariant_in Hli _ Hy) as Hy'.
             destruct (gds_lookup Θ y) as [Vy |] eqn:Ey; [| contradiction ].
             destruct (global_invariant_entry G _ _ Ey) as [Dy' _ _ _ _ _ _ _ HKy' _ _ _ _ _ _ _ _ _ _].
             rewrite (HextK _ _ HKy') in HKy; injection HKy as <-.
             exact (ui_closed _ _ _ _ _ _ Hli _ _ Hy HKy' _ Hz).
          -- rewrite path_beq_refl in Hb; discriminate.
          -- right; right; exact (Hcl1 _ _ Hy HKy _ Hz).
    - split; [ exact Hc' |].
      intros y By Hy; rewrite builtins_map_lookup_merge in Hy; destruct (builtins_map_lookup RbR y) eqn:E.
      + injection Hy as <-; simp unit_closure_builtins; rewrite path_beq_false; [ exact (HextB _ _ (proj2 Hrb _ _ E)) |].
        apply Hfresh; intros Hny; apply (proj2 (proj1 Hrb) _ _ E).
        destruct (gds_lookup ΘR y) eqn:Ey; [ exfalso; rewrite (ui_sub _ _ _ _ _ _ Hli _ _ Ey) in Hny; discriminate | reflexivity ].
      + cbn in Hy; destruct (path_beq y fp) eqn:Hb.
        * apply path_beq_true in Hb as ->; injection Hy as <-; simp unit_closure_builtins; rewrite path_beq_refl; reflexivity.
        * exact (HRU' _ _ Hy).
    - constructor; [ exact (gds_sub_trans _ _ _ Hext1 Hsub1N) | |].
      + intros y Dy HKy; simp unit_closure_find; rewrite path_beq_false; [ exact (HextK _ _ HKy) |].
        intros ->; exact (gi_closures_filed _ _ _ G _ _ HKy Hn).
      + intros y By HKy; simp unit_closure_builtins; rewrite path_beq_false; [ exact (HextB _ _ HKy) |].
        destruct (unit_closure_builtins_unit_closure_find _ _ _ HKy) as [Dy HKy']; intros ->; exact (gi_closures_filed _ _ _ G _ _ HKy' Hn).
    - intros y Hy; unfold ΘN in Hy; apply dom_cons in Hy as [-> | Hy].
      + right; apply p_union_iff; right; left; reflexivity.
      + destruct (Hgr1 _ Hy) as [H | H]; [ left; exact H | right; apply p_union_iff; right; right; exact H ].
  Qed.

  Lemma load_ok {ch Θ K D B Ξ fp src prg u r B'} :
    gds_lookup Θ fp = None -> ~ In fp ch ->
    load_path fp = Some src -> read src = Some prg -> prog_path prg = fp -> to_core prg = Some u ->
    post_unit (fp :: ch) Θ K u r -> builtins_merge B (unit_result_core_builtins r) = Some B' ->
    post_cmd ch Θ K D B Ξ (core_cmd_load fp) (load_state fp D Ξ B' r).
  Proof.
    intros Hn Hnch Hl Hrd Hp Ht Hpost Hm ΘR RbR Hli Hrb.
    destruct (load_unit_invariant (B' := B') Hn Hnch Hl Hrd Hp Ht Hpost _ _ Hli Hrb) as (RbU & ΘU & HnR & Hu & Hli' & Hrb' & Hext & Hgr).
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ core_cmd_load fp ⇝
                   gds_merge ΘR ((fp, unit_result_core_unit r) :: ΘU) ⍮ Ξ ⍮ B' ⍮ builtins_map_merge RbR ((fp, unit_result_core_builtins r) :: RbU))
      by (eapply run_cmd_load; eassumption).
    apply (mk_cmd_post _ _ _ _ _ (gds_merge ΘR ((fp, unit_result_core_unit r) :: ΘU)) (builtins_map_merge RbR ((fp, unit_result_core_builtins r) :: RbU)));
      [ exact Hr | exact Hli' | exact Hrb' | exact Hext | exact Hgr ].
  Qed.

  (** *** The Generated Entries of an Open *)

  Definition post_gens ch Θ K D Ξ gs Ξ' : Prop :=
    forall ΘR, unit_invariant ch Θ K D ΘR Ξ -> gens_run ΘR Ξ gs Ξ' /\ unit_invariant ch Θ K D ΘR Ξ'.

  Lemma gens_nil_ok {ch Θ K D Ξ} : post_gens ch Θ K D Ξ nil Ξ.
  Proof. intros ΘR Hli; split; [ constructor | exact Hli ]. Qed.

  Lemma gen_def_step {ch Θ K D ΘR Ξ d pv κ A M} {i : nat} :
    unit_invariant ch Θ K D ΘR Ξ -> gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : abs_kind_sort κ Typeω@i ->
    (κ = ak_level -> level_sorted_parameters (gs_tele Ξ)) -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    ΘR ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : abs_kind_sort κ Typeω@i /\ ΘR ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A /\
    unit_invariant ch Θ K D ΘR (gs_add d (gs_def true pv κ Ξ A M) Ξ).
  Proof.
    intros Hli Hfr HA Hlv HM.
    pose proof (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) (ui_wf _ _ _ _ _ _ Hli) HM) as HM'.
    pose proof (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) (ui_wf _ _ _ _ _ _ Hli) HA) as HA'.
    split; [ exact HA' | split; [ exact HM' |] ].
    exact (unit_invariant_stack Hli (add_def_wf _ _ _ _ _ _ _ _ _ (ui_wf _ _ _ _ _ _ Hli) HA' Hlv HM' Hfr)
             (stack_in_add _ _ _ _ (ui_stack _ _ _ _ _ _ Hli))).
  Qed.

  Lemma gen_alias_step {ch Θ K D ΘR Ξ d pv E} :
    unit_invariant ch Θ K D ΘR Ξ -> gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
    levels_abstractable (gds_restrict D Θ) Ξ ⋅ (gs_tele Ξ) E ->
    ΘR ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E /\ levels_abstractable ΘR Ξ ⋅ (gs_tele Ξ) E /\
    unit_invariant ch Θ K D ΘR (gs_add d (ge_mod pv (gu_mk (gs_tele Ξ) (md_alias E))) Ξ).
  Proof.
    intros Hli Hfr HE Hlv.
    pose proof (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) as Heq; pose proof (ui_wf _ _ _ _ _ _ Hli) as HΞ.
    pose proof (equiv_modexp _ _ _ _ _ Heq HΞ HE) as HE'.
    pose proof (equiv_levels_abstractable _ _ _ Heq HΞ _ _ _ Hlv) as Hlv'.
    split; [ exact HE' | split; [ exact Hlv' |] ].
    apply (unit_invariant_stack Hli); [| exact (stack_in_add _ _ _ _ (ui_stack _ _ _ _ _ _ Hli)) ].
    apply (add_alias_wf _ _ _ _ nil _ 0);
      [ exact HΞ | constructor | | exact HE' | apply params_evaluated_nil | exact Hlv' | exact Hfr ].
    constructor; exact (presup_modexp_eq_ctx HE').
  Qed.

  Lemma gen_def_pre {ch Θ K D Ξ d pv κ A M} {i : nat} :
    (exists ΘR, unit_invariant ch Θ K D ΘR Ξ) -> gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : abs_kind_sort κ Typeω@i ->
    (κ = ak_level -> level_sorted_parameters (gs_tele Ξ)) -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    exists ΘR, unit_invariant ch Θ K D ΘR (gs_add d (gs_def true pv κ Ξ A M) Ξ).
  Proof. intros [ΘR Hli] Hfr HA Hlv HM; exists ΘR; exact (proj2 (proj2 (gen_def_step Hli Hfr HA Hlv HM))). Qed.

  Lemma gen_alias_pre {ch Θ K D Ξ d pv E} :
    (exists ΘR, unit_invariant ch Θ K D ΘR Ξ) -> gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
    levels_abstractable (gds_restrict D Θ) Ξ ⋅ (gs_tele Ξ) E ->
    exists ΘR, unit_invariant ch Θ K D ΘR (gs_add d (ge_mod pv (gu_mk (gs_tele Ξ) (md_alias E))) Ξ).
  Proof. intros [ΘR Hli] Hfr HE Hlv; exists ΘR; exact (proj2 (proj2 (gen_alias_step Hli Hfr HE Hlv))). Qed.

  Lemma gen_def_ok {ch Θ K D Ξ d pv κ A M gs Ξ'} {i : nat} :
    gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : abs_kind_sort κ Typeω@i ->
    (κ = ak_level -> level_sorted_parameters (gs_tele Ξ)) -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    post_gens ch Θ K D (gs_add d (gs_def true pv κ Ξ A M) Ξ) gs Ξ' ->
    post_gens ch Θ K D Ξ (generated_item_def d pv κ A M :: gs) Ξ'.
  Proof.
    intros Hfr HA Hlv HM Hp ΘR Hli; destruct (gen_def_step (pv := pv) Hli Hfr HA Hlv HM) as (HA' & HM' & Hli').
    destruct (Hp _ Hli') as [Hg Hli2]; split; [ econstructor; eassumption | exact Hli2 ].
  Qed.

  Lemma gen_alias_ok {ch Θ K D Ξ d pv E gs Ξ'} :
    gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
    levels_abstractable (gds_restrict D Θ) Ξ ⋅ (gs_tele Ξ) E ->
    post_gens ch Θ K D (gs_add d (ge_mod pv (gu_mk (gs_tele Ξ) (md_alias E))) Ξ) gs Ξ' ->
    post_gens ch Θ K D Ξ (generated_item_alias d pv E :: gs) Ξ'.
  Proof.
    intros Hfr HE Hlv Hp ΘR Hli; destruct (gen_alias_step (pv := pv) Hli Hfr HE Hlv) as (HE' & Hlv' & Hli').
    destruct (Hp _ Hli') as [Hg Hli2]; split; [ econstructor; eassumption | exact Hli2 ].
  Qed.

  (** A generated definition with a module part, its term [M] of the type
      [W] inferred for it and its module part the alias of [E]. *)
  Lemma gen_dm_step {ch Θ K D ΘR Ξ d pv M E W} {i : nat} :
    unit_invariant ch Θ K D ΘR Ξ -> gs_fresh d Ξ ->
    @alg_type_infer (gc_mk (gds_restrict D Θ) Ξ) (gs_tele Ξ) W M ->
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ nf_to_exp W : Typeω@i ->
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : nf_to_exp W ->
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
    levels_abstractable (gds_restrict D Θ) Ξ ⋅ (gs_tele Ξ) E ->
    @alg_type_infer (gc_mk ΘR Ξ) (gs_tele Ξ) W M /\ ΘR ⍮ Ξ ⍮ gs_tele Ξ ⊢ nf_to_exp W : Typeω@i /\
    ΘR ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : nf_to_exp W /\ ΘR ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E /\ levels_abstractable ΘR Ξ ⋅ (gs_tele Ξ) E /\
    unit_invariant ch Θ K D ΘR (gs_add d (dm_entry Ξ pv nil (nf_to_exp W) M E) Ξ).
  Proof.
    intros Hli Hfr HW HWt HM HE Hlv.
    pose proof (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) as Heq; pose proof (ui_wf _ _ _ _ _ _ Hli) as HΞ.
    pose proof (equiv_exp _ _ _ _ _ _ Heq HΞ HM) as HM'.
    pose proof (equiv_exp _ _ _ _ _ _ Heq HΞ HWt) as HWt'.
    pose proof (equiv_modexp _ _ _ _ _ Heq HΞ HE) as HE'.
    pose proof (equiv_levels_abstractable _ _ _ Heq HΞ _ _ _ Hlv) as Hlv'.
    split; [ exact (equiv_alg_infer _ _ _ _ _ _ Heq HΞ HW) |].
    do 4 (split; [ assumption |]).
    apply (unit_invariant_stack Hli); [| exact (stack_in_add _ _ _ _ (ui_stack _ _ _ _ _ _ Hli)) ].
    apply (add_dm_wf _ _ _ _ nil _ _ _ i 0);
      [ exact HΞ | constructor | | exact HWt' | exact HM' | exact HE' | apply params_evaluated_nil | exact Hlv' | exact Hfr ].
    constructor; exact (presup_exp_ctx HM').
  Qed.

  (** The invariant after a generated definition with a module part. *)
  Lemma gen_dm_pre {ch Θ K D Ξ d pv M E W} {i : nat} :
    (exists ΘR, unit_invariant ch Θ K D ΘR Ξ) -> gs_fresh d Ξ ->
    @alg_type_infer (gc_mk (gds_restrict D Θ) Ξ) (gs_tele Ξ) W M ->
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ nf_to_exp W : Typeω@i ->
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : nf_to_exp W ->
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
    levels_abstractable (gds_restrict D Θ) Ξ ⋅ (gs_tele Ξ) E ->
    exists ΘR, unit_invariant ch Θ K D ΘR (gs_add d (dm_entry Ξ pv nil (nf_to_exp W) M E) Ξ).
  Proof.
    intros [ΘR Hli] Hfr HW HWt HM HE Hlv; exists ΘR.
    exact (proj2 (proj2 (proj2 (proj2 (proj2 (gen_dm_step Hli Hfr HW HWt HM HE Hlv)))))).
  Qed.

  (** A generated definition with a module part, then the rest, run as
      [gens_run_def_mod] runs them. *)
  Lemma gen_dm_ok {ch Θ K D Ξ d pv A M E W gs Ξ'} {i : nat} :
    gs_fresh d Ξ ->
    @alg_type_infer (gc_mk (gds_restrict D Θ) Ξ) (gs_tele Ξ) W M ->
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ nf_to_exp W : Typeω@i ->
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : nf_to_exp W ->
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
    levels_abstractable (gds_restrict D Θ) Ξ ⋅ (gs_tele Ξ) E ->
    post_gens ch Θ K D (gs_add d (dm_entry Ξ pv nil (nf_to_exp W) M E) Ξ) gs Ξ' ->
    post_gens ch Θ K D Ξ (generated_item_def_mod d pv A M E :: gs) Ξ'.
  Proof.
    intros Hfr HW HWt HM HE Hlv Hp ΘR Hli;
      destruct (gen_dm_step (pv := pv) Hli Hfr HW HWt HM HE Hlv) as (HW' & HWt' & HM' & HE' & Hlv' & Hli').
    destruct (Hp _ Hli') as [Hg Hli2]; split; [ econstructor; eassumption | exact Hli2 ].
  Qed.

  (** What an open generates is read off descriptions, which read the
      dependencies through their lookups alone. *)
  Lemma open_gens_equiv : forall Θ1 Θ2 Ξ Γ H its gs, gds_equiv Θ1 Θ2 ->
      open_gens Θ1 Ξ Γ H its gs -> open_gens Θ2 Ξ Γ H its gs.
  Proof.
    intros * He [R Rm HR HRm Hg Hok].
    pose proof (gds_equiv_mdenote_all _ _ Ξ He) as (H1 & _ & _ & _ & H5).
    apply (mk_open_gens _ _ _ _ _ _ R Rm); [ exact (H1 _ _ _ HR) | | exact (H5 _ _ _ _ Hg) | exact Hok ].
    exact HRm.
  Qed.

  (** An open declares what its items generate, which files nothing. *)
  Lemma open_ok {ch Θ K D B Ξ E its gs Ξ'}
    (HE : gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E) :
    open_gens (gds_restrict D Θ) Ξ (gs_tele Ξ) E its gs ->
    post_gens ch Θ K D Ξ gs Ξ' ->
    post_cmd ch Θ K D B Ξ (core_cmd_open E its) (mk_run_state_core Θ K D B Ξ').
  Proof.
    intros Hgen Hgs ΘR RbR Hli Hrb; cbn [run_state_core_deps run_state_core_closures run_state_core_imports run_state_core_builtins run_state_core_stack].
    destruct (Hgs _ Hli) as [Hr Hli'].
    pose proof (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) as Heq.
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR); [| exact Hli' | exact Hrb | apply ext_refl | apply grows_refl ].
    eapply run_cmd_open; [ exact (equiv_modexp _ _ _ _ _ Heq (ui_wf _ _ _ _ _ _ Hli) HE) | | exact Hr ].
    exact (open_gens_equiv _ _ _ _ _ _ _ Heq Hgen).
  Qed.

  (** *** Items *)

  Lemma nil_ok {ch Θ K D B Ξ} : post_cmds ch Θ K D B Ξ nil (mk_run_state_core Θ K D B Ξ).
  Proof.
    intros ΘR RbR Hli Hrb.
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR); [ constructor | exact Hli | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  (** The imports of a later step include those of an earlier one. *)
  Lemma dom_grows {ch Θ1 K1 D1 B1 RbR1 ΘR1 Ξ1 Θ2 K2 D2 B2 RbR2 ΘR2 Ξ2 cs} :
    unit_invariant ch Θ1 K1 D1 ΘR1 Ξ1 -> canon RbR1 ΘR1 -> ΘR1 ⍮ Ξ1 ⍮ B1 ⍮ RbR1 ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* ΘR2 ⍮ Ξ2 ⍮ B2 ⍮ RbR2 ->
    unit_invariant ch Θ2 K2 D2 ΘR2 Ξ2 -> incl D1 D2.
  Proof.
    intros Hli1 Hc Hr Hli2 x Hx.
    destruct (unit_invariant_runs_wf Hli1 Hc Hr) as (_ & _ & Hs & _).
    apply (ui_dom _ _ _ _ _ _ Hli2), (sub_dom _ _ _ Hs), (ui_dom _ _ _ _ _ _ Hli1), Hx.
  Qed.

  (** The imports of a later command include those of an earlier one. *)
  Lemma dom_grows_cmd {ch Θ1 K1 D1 B1 RbR1 ΘR1 Ξ1 Θ2 K2 D2 B2 RbR2 ΘR2 Ξ2 c} :
    unit_invariant ch Θ1 K1 D1 ΘR1 Ξ1 -> canon RbR1 ΘR1 -> ΘR1 ⍮ Ξ1 ⍮ B1 ⍮ RbR1 ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ ΘR2 ⍮ Ξ2 ⍮ B2 ⍮ RbR2 ->
    unit_invariant ch Θ2 K2 D2 ΘR2 Ξ2 -> incl D1 D2.
  Proof.
    intros Hli1 Hc Hr Hli2 x Hx.
    destruct (unit_invariant_run_wf Hli1 Hc Hr) as (_ & _ & Hs & _).
    apply (ui_dom _ _ _ _ _ _ Hli2), (sub_dom _ _ _ Hs), (ui_dom _ _ _ _ _ _ Hli1), Hx.
  Qed.

  (** A core command, then the rest *)
  Lemma core_cons_ok {ch Θ K D B Ξ c cs r1 r2} :
    post_cmd ch Θ K D B Ξ c r1 ->
    post_cmds ch (run_state_core_deps r1) (run_state_core_closures r1) (run_state_core_imports r1) (run_state_core_builtins r1) (run_state_core_stack r1) cs r2 ->
    post_cmds ch Θ K D B Ξ (ci_core c :: cs) r2.
  Proof.
    intros H1 H2 ΘR RbR Hli Hrb.
    destruct (H1 _ _ Hli Hrb) as [ΘR1 RbR1 Hr1 Hli1 Hrb1 He1 Hg1].
    destruct (H2 _ _ Hli1 Hrb1) as [ΘR2 RbR2 Hr2 Hli2 Hrb2 He2 Hg2]; cbn beta in Hr2.
    apply (mk_cmd_post _ _ _ _ _ ΘR2 RbR2); [ eapply run_cmds_core; eassumption | exact Hli2 | exact Hrb2
                                            | eapply ext_trans; eassumption |].
    exact (grows_trans Hg1 Hg2 (dom_grows Hli1 (proj1 Hrb1) Hr2 Hli2)).
  Qed.

  (** A command as written: checked for privacy, filled, its items run,
      then the rest *)
  Lemma written_cons_ok {ch Θ K D B Ξ c its cs r1 r2} :
    acc_ok (gds_restrict D Θ) Ξ (cmd_refs c) -> fill_cmd (gds_restrict D Θ) Ξ B c its ->
    post_cmds ch Θ K D B Ξ its r1 ->
    post_cmds ch (run_state_core_deps r1) (run_state_core_closures r1) (run_state_core_imports r1) (run_state_core_builtins r1) (run_state_core_stack r1) cs r2 ->
    post_cmds ch Θ K D B Ξ (ci_written c :: cs) r2.
  Proof.
    intros Hac Hfc H1 H2 ΘR RbR Hli Hrb.
    pose proof (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) as Heq.
    pose proof (equiv_acc _ _ _ _ Heq Hac) as Hac'.
    pose proof (equiv_fill_cmd _ _ _ _ _ _ Heq (ui_wf _ _ _ _ _ _ Hli) Hfc) as Hfc'.
    destruct (H1 _ _ Hli Hrb) as [ΘR1 RbR1 Hr1 Hli1 Hrb1 He1 Hg1]; cbn beta in Hr1.
    destruct (H2 _ _ Hli1 Hrb1) as [ΘR2 RbR2 Hr2 Hli2 Hrb2 He2 Hg2]; cbn beta in Hr2.
    apply (mk_cmd_post _ _ _ _ _ ΘR2 RbR2); [ eapply run_cmds_written; eassumption | exact Hli2 | exact Hrb2
                                            | eapply ext_trans; eassumption |].
    exact (grows_trans Hg1 Hg2 (dom_grows Hli1 (proj1 Hrb1) Hr2 Hli2)).
  Qed.

  (** An entry checked at the restriction, at a path in the innermost
      frame, is checked at the judgment's state: its unit is on the chain,
      so not filed ([global_deps_grow]). *)
  Lemma unit_invariant_entry_at {ch Θ K D ΘR Ξ x E} : unit_invariant ch Θ K D ΘR Ξ -> gs_fresh x Ξ ->
      gds_restrict D Θ ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ E -> ΘR ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ E.
  Proof.
    intros Hli Hfr HE.
    apply (proj1 (global_deps_grow _ _ (proj1 (gds_equiv_sym _ _ (unit_invariant_equiv Hli)))) _ _ _ _ HE eq_refl
             (ui_wf _ _ _ _ _ _ Hli)).
    apply (sub_none _ _ _ (ui_sub _ _ _ _ _ _ Hli)), (gi_chain _ _ _ (ui_global _ _ _ _ _ _ Hli)).
    destruct Ξ as [| [[mq Kq] V] Ξ0]; [ contradiction |]; cbn; eapply (ui_stack _ _ _ _ _ _ Hli); left; reflexivity.
  Qed.

  (** *** Groups *)

  (** The recursor module of a group reads the global context only for
      the names of the members its views are of. *)
  Lemma equiv_recursor_mod_cmds : forall Θ1 Θ2 Ξ pq Dd Δu, gds_equiv Θ1 Θ2 ->
      recursor_mod_cmds Θ1 Ξ pq Dd Δu = recursor_mod_cmds Θ2 Ξ pq Dd Δu.
  Proof.
    intros * He; unfold recursor_mod_cmds, recursor_names.
    assert (Hn : forall p j, member_name Θ1 Ξ p j = member_name Θ2 Ξ p j)
      by (intros; unfold member_name; rewrite (gds_equiv_ind_lookup _ _ _ _ He); reflexivity).
    assert (Hm : List.map (recursor_member_name Θ1 Ξ) (ind_block_members Dd) = List.map (recursor_member_name Θ2 Ξ) (ind_block_members Dd)).
    { assert (Hi : forall Is, inst_member_names Θ1 Ξ Is = inst_member_names Θ2 Ξ Is)
        by (intros; unfold inst_member_names; f_equal; apply List.map_ext; intros I;
            destruct (app_head I); try reflexivity; rewrite Hn; reflexivity).
      apply List.map_ext; intros M; unfold recursor_member_name; destruct (im_head M) as [pm | qc k Is vm | qr Is fl];
        [ reflexivity | rewrite Hn, Hi; reflexivity | rewrite Hi; reflexivity ]. }
    rewrite Hm; reflexivity.
  Qed.

  Lemma equiv_rec_cmds : forall Θ1 Θ2 Ξ R pq Dd, gds_equiv Θ1 Θ2 -> rec_cmds Θ1 Ξ R pq Dd = rec_cmds Θ2 Ξ R pq Dd.
  Proof. intros * He; unfold rec_cmds; rewrite (equiv_recursor_mod_cmds _ _ _ _ _ _ He); reflexivity. Qed.

  (** So do the commands of a declared member's module. *)
  Lemma equiv_ind_mod_cmds : forall Θ1 Θ2 Ξ R pq Dd k M, gds_equiv Θ1 Θ2 ->
      ind_mod_cmds Θ1 Ξ R pq Dd k M = ind_mod_cmds Θ2 Ξ R pq Dd k M.
  Proof. intros * He; unfold ind_mod_cmds, ind_recursor_cmds; rewrite (equiv_recursor_mod_cmds _ _ _ _ _ _ He); reflexivity. Qed.

  (** The first of the members [xs] is well formed with an empty module,
      where it is declared. *)
  Definition head_entry ch Θ K D Ξ pv pq Dd k (xs : list string) : Prop :=
    match xs with
    | nil => True
    | x :: _ => forall ΘR, unit_invariant ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv pq k Dd ⋄
    end.

  (** A later member is well formed with an empty module where it is
      declared. *)
  Lemma later_head_entry {ch Θ K D Ξ pv R pq Dd k xs} : mems_pre Ξ R pq Dd (S k) xs ->
      (forall ΘR, unit_invariant ch Θ K D ΘR Ξ -> exists l, params_evaluated ΘR Ξ (gs_tele Ξ) (raw_decl_uparams R) l) ->
      head_entry ch Θ K D Ξ pv pq Dd (S k) xs.
  Proof.
    intros Hp Hrel; destruct xs as [| x xs]; [ exact I |]; intros ΘR Hli.
    destruct (Hrel ΘR Hli) as [lu Hlu].
    destruct (mems_pre_later _ _ _ _ _ _ Hp ltac:(apply PeanoNat.Nat.lt_0_succ)) as [mq Kq Δ Φ Ξ0 y0 pv0 Φm -> He ->].
    destruct (mems_pre_heads _ _ _ _ _ _ Hp 0 x eq_refl) as (M & HM & Hh); rewrite PeanoNat.Nat.add_0_r in HM.
    pose proof (mems_pre_count _ _ _ _ _ _ Hp) as Hc; cbn [List.length] in Hc.
    eapply later_member_entry;
      [ exact (ui_wf _ _ _ _ _ _ Hli) | exact He | exact HM | apply PeanoNat.Nat.lt_0_succ
      | eapply PeanoNat.Nat.lt_le_trans; [| exact Hc ]; rewrite PeanoNat.Nat.add_succ_r; apply PeanoNat.Nat.lt_succ_r, PeanoNat.Nat.le_add_r
      | exact Hh | exact (mems_pre_uparams _ _ _ _ _ _ Hp) | exact Hlu ].
  Qed.

  (** The first member is, by the group checked at its views' instances. *)
  Lemma first_head_entry {ch Θ K D Ξ pv R pq Dd xs IsS} : mems_pre Ξ R pq Dd 0 xs ->
      ind_nil_at (gds_restrict D Θ) Ξ pq Dd IsS -> head_entry ch Θ K D Ξ pv pq Dd 0 xs.
  Proof.
    intros Hp Hnil; destruct xs as [| x xs]; [ exact I |]; intros ΘR Hli.
    rewrite <- (mems_pre_first _ _ _ _ _ _ Hp eq_refl x xs eq_refl).
    exact (ind_nil_at_entry _ _ _ _ _
             (equiv_ind_nil_at _ _ _ (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) (ui_wf _ _ _ _ _ _ Hli) _ _ _ Hnil) pv).
  Qed.

  (** The frame of a declared member's module, opened where the member is
      declared, keeps the invariant. *)
  Lemma unit_invariant_push_ind {ch Θ K D ΘR Ξ x pv R pq Dd k} :
    unit_invariant ch Θ K D ΘR Ξ -> gs_fresh x Ξ -> ind_uparams Dd = (raw_decl_uparams R ++ gs_tele Ξ)%list ->
    ΘR ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv pq k Dd ⋄ ->
    unit_invariant ch Θ K D ΘR (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ).
  Proof.
    intros Hli Hfr Hu HE; destruct (ind_nil_entry_uparams _ _ _ _ _ _ _ _ HE Hu) as [Htel HΔ].
    destruct (ind_empty_entry_params_evaluated _ _ _ _ _ _ _ _ HE Hu) as [l HPr].
    destruct (params_evaluated_sorts _ _ _ _ _ HPr) as (ps & Hps & HT).
    apply (unit_invariant_stack Hli); [| exact (stack_in_push_ind _ _ _ _ _ _ _ (ui_stack _ _ _ _ _ _ Hli) Hfr) ].
    destruct Ξ as [| [[mq Kq] Uq] Ξ0]; [ contradiction |].
    apply wf_gstack_cons; [ exact (ui_wf _ _ _ _ _ _ Hli) | eapply wf_gmod_ind_nil; eassumption |].
    cbn; exists x; split; [ reflexivity | exact Hfr ].
  Qed.

  Lemma push_ind_pre {ch Θ K D Ξ x pv R pq Dd k} :
    (exists ΘR, unit_invariant ch Θ K D ΘR Ξ) -> gs_fresh x Ξ -> ind_uparams Dd = (raw_decl_uparams R ++ gs_tele Ξ)%list ->
    (forall ΘR, unit_invariant ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv pq k Dd ⋄) ->
    exists ΘR, unit_invariant ch Θ K D ΘR (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ).
  Proof. intros [ΘR Hli] Hfr Hu HE; exists ΘR; exact (unit_invariant_push_ind Hli Hfr Hu (HE _ Hli)). Qed.

  (** A declared member's module, its commands run in its frame by [r1]:
      the frame closes into the member's entry, as [run_ind_members_cons]
      files it.  The frames below are those it was opened on. *)
  Lemma member_ok {ch Θ K D B Ξ pv R pq Dd k x M r1 mp Kf U Ξ2} :
    gs_fresh x Ξ -> ind_uparams Dd = (raw_decl_uparams R ++ gs_tele Ξ)%list ->
    (forall ΘR, unit_invariant ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv pq k Dd ⋄) ->
    post_cmds ch Θ K D B (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ)
      (List.map ci_core (ind_mod_cmds (gds_restrict D Θ) (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ) R pq Dd k M)) r1 ->
    run_state_core_stack r1 = (mp, Kf, U) :: Ξ2 ->
    forall ΘR RbR, unit_invariant ch Θ K D ΘR Ξ -> builtin_records_ok K ΘR RbR ->
      (Ξ2 = Ξ /\ mp = ind_qname Ξ x /\ Kf = fk_ind pq k Dd /\ gu_params U = raw_decl_uparams R) /\
      cmd_post (fun RbR' ΘR' => ΘR ⍮ gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ ⍮ B ⍮ RbR
                                  ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩
                                  List.map ci_core (ind_mod_cmds ΘR (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ) R pq Dd k M) ⇝*
                                  ΘR' ⍮ (mp, Kf, U) :: Ξ ⍮ run_state_core_builtins r1 ⍮ RbR') ch Θ K
        (mk_run_state_core (run_state_core_deps r1) (run_state_core_closures r1) (run_state_core_imports r1) (run_state_core_builtins r1) (gs_add x (ge_ind pv pq k Dd (gu_mod U)) Ξ)).
  Proof.
    intros Hfr Hu HE Hpost HΞ ΘR RbR Hli Hrb.
    pose proof (HE _ Hli) as HE0.
    pose proof (unit_invariant_push_ind Hli Hfr Hu HE0) as Hli'.
    destruct (Hpost _ _ Hli' Hrb) as [ΘR1 RbR1 Hrun Hli1 Hrb1 Hext Hgr]; cbn beta in Hrun.
    rewrite HΞ in Hrun, Hli1.
    rewrite <- (equiv_ind_mod_cmds _ _ _ _ _ _ _ _ (unit_invariant_equiv Hli)) in Hrun.
    destruct (ind_mod_cmds_run_gen load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun (ui_wf _ _ _ _ _ _ Hli'))
      as [_ _ _ _ _ Hsh Htl].
    cbn in Htl; subst Ξ2; cbn [gs_shape List.map fst snd gs_push_ind gu_params] in Hsh; injection Hsh as Emp EKf EU.
    split; [ exact (conj eq_refl (conj Emp (conj EKf EU))) |].
    destruct (ind_member_run_gen load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ui_wf _ _ _ _ _ _ Hli) Hu Hfr HE0 Hrun)
      as [HΘ _ _ Hw _ _ _]; subst ΘR1.
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR1 Hrun); cbn [run_state_core_deps run_state_core_closures run_state_core_imports run_state_core_stack];
      [| exact Hrb1 | exact Hext | exact Hgr ].
    apply (unit_invariant_stack Hli1); [ exact Hw | exact (stack_in_add _ _ _ _ (ui_stack _ _ _ _ _ _ Hli)) ].
  Qed.

  (** What a run of the declared members [k], [k + 1], … named [xs] proves. *)
  Definition post_mems ch Θ K D B Ξ pv R pq Dd k xs (r : run_state_core) : Prop :=
    forall ΘR RbR, unit_invariant ch Θ K D ΘR Ξ -> builtin_records_ok K ΘR RbR ->
      cmd_post (fun RbR' ΘR' => run_ind_members load_path read to_core ch B RbR ΘR Ξ pv R pq Dd k xs
                                  (run_state_core_builtins r) RbR' ΘR' (run_state_core_stack r)) ch Θ K r.

  Lemma mems_nil_ok {ch Θ K D B Ξ pv R pq Dd k} : post_mems ch Θ K D B Ξ pv R pq Dd k nil (mk_run_state_core Θ K D B Ξ).
  Proof.
    intros ΘR RbR Hli Hrb.
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR); [ constructor | exact Hli | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  Lemma mems_cons_ok {ch Θ K D B Ξ pv R pq Dd k x xs M r1 mp Kf U Ξ2 r2} :
    ind_member Dd k = Some M -> gs_fresh x Ξ -> ind_uparams Dd = (raw_decl_uparams R ++ gs_tele Ξ)%list ->
    (forall ΘR, unit_invariant ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv pq k Dd ⋄) ->
    post_cmds ch Θ K D B (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ)
      (List.map ci_core (ind_mod_cmds (gds_restrict D Θ) (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ) R pq Dd k M)) r1 ->
    run_state_core_stack r1 = (mp, Kf, U) :: Ξ2 ->
    post_mems ch (run_state_core_deps r1) (run_state_core_closures r1) (run_state_core_imports r1) (run_state_core_builtins r1) (gs_add x (ge_ind pv pq k Dd (gu_mod U)) Ξ) pv R pq Dd (S k) xs r2 ->
    post_mems ch Θ K D B Ξ pv R pq Dd k (x :: xs) r2.
  Proof.
    intros HM Hfr Hu HE Hpost HΞ H2 ΘR RbR Hli Hrb.
    destruct (member_ok Hfr Hu HE Hpost HΞ _ _ Hli Hrb) as [_ [ΘR1 RbR1 Hr1 Hli1 Hrb1 He1 Hg1]];
      cbn [run_state_core_deps run_state_core_closures run_state_core_imports run_state_core_builtins run_state_core_stack] in *.
    destruct (H2 _ _ Hli1 Hrb1) as [ΘR2 RbR2 Hr2 Hli2 Hrb2 He2 Hg2]; cbn beta in Hr2.
    destruct (ind_members_run_gen load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr2 (ui_wf _ _ _ _ _ _ Hli1)
                ltac:(rewrite gs_tele_add; exact Hu)) as [HΘ _ _ _ _ _ _].
    apply (mk_cmd_post _ _ _ _ _ ΘR2 RbR2);
      [ eapply run_ind_members_cons; [ exact HM | exact Hfr | exact (HE _ Hli) | exact Hr1 | exact Hr2 ]
      | exact Hli2 | exact Hrb2 | eapply ext_trans; eassumption |].
    apply (grows_trans Hg1 Hg2); intros y Hy.
    apply (ui_dom _ _ _ _ _ _ Hli2); rewrite HΘ; apply (ui_dom _ _ _ _ _ _ Hli1); exact Hy.
  Qed.

  Lemma mems_post_pre {ch Θ K D B Ξ pv R pq Dd k xs r} :
    (exists ΘR, unit_invariant ch Θ K D ΘR Ξ) -> post_mems ch Θ K D B Ξ pv R pq Dd k xs r ->
    exists ΘR, unit_invariant ch (run_state_core_deps r) (run_state_core_closures r) (run_state_core_imports r) ΘR (run_state_core_stack r).
  Proof.
    intros [ΘR Hli] Hp; destruct (unit_invariant_builtin_records Hli) as [RbR Hrb].
    destruct (Hp _ _ Hli Hrb) as [ΘR' RbR' _ Hli' _ _ _]; eauto.
  Qed.

  (** A group declaration, with the premises of [run_cmd_ind_case] at the
      restriction: its declared members, each with its module, then its
      recursor module, if any, from where they end. *)
  Lemma ind_ok {ch Θ K D B Ξ pv R Mr0 Mrs csD Vs Ss csV Nvs Dd r1 r2} :
    raw_decl_members R = Mr0 :: Mrs ->
    Forall (fun Mr => raw_member_sort Mr = raw_member_sort Mr0) Mrs ->
    Forall2 (raw_member_classify (gds_restrict D Θ) Ξ R) (raw_decl_members R) csD ->
    Forall2 (view_siblings (gds_restrict D Θ) Ξ R) Vs Ss ->
    Forall2 (view_classify (gds_restrict D Θ) Ξ R) Vs csV ->
    Forall2 (view_nparams (gds_restrict D Θ) Ξ R) Vs Nvs ->
    views_dfs (siblings_table Vs Ss) (meets_table Vs csV) nil (List.concat (List.map classified_cons_views csD)) Vs ->
    raw_decl_filed (gds_restrict D Θ) Ξ R Vs Ss csD csV Nvs = Some Dd ->
    ind_nil_at (gds_restrict D Θ) Ξ (ind_qname Ξ (raw_member_name Mr0)) Dd (grp_self_insts (ind_qname Ξ (raw_member_name Mr0)) Dd) ->
    gen_names_free Ξ R Dd ->
    post_mems ch Θ K D B Ξ pv R (ind_qname Ξ (raw_member_name Mr0)) Dd 0 (List.map raw_member_name (raw_decl_members R)) r1 ->
    post_cmds ch (run_state_core_deps r1) (run_state_core_closures r1) (run_state_core_imports r1) (run_state_core_builtins r1) (run_state_core_stack r1)
      (List.map ci_core (rec_cmds (gds_restrict (run_state_core_imports r1) (run_state_core_deps r1)) (run_state_core_stack r1) R (ind_qname Ξ (raw_member_name Mr0)) Dd)) r2 ->
    post_cmd ch Θ K D B Ξ (core_cmd_inductive pv R) r2.
  Proof.
    intros HR Hsort Hcls Hsibs Hvcls Hvnps Hbfs Hfil Hnil Hgn H1 H2 ΘR RbR Hli Hrb.
    pose proof (gds_equiv_sym _ _ (unit_invariant_equiv Hli)) as Heq.
    pose proof (ui_wf _ _ _ _ _ _ Hli) as HΞ.
    pose proof (equiv_raw_member_classify _ _ _ Heq HΞ _ _ _ Hcls) as Hcls'.
    assert (Hsibs' : Forall2 (view_siblings ΘR Ξ R) Vs Ss)
      by (eapply Forall2_impl; [ intros x ss; apply (equiv_view_siblings _ _ _ Heq HΞ) | exact Hsibs ]).
    assert (Hvcls' : Forall2 (view_classify ΘR Ξ R) Vs csV)
      by (eapply Forall2_impl; [ intros x cs; apply (equiv_view_classify _ _ _ Heq HΞ) | exact Hvcls ]).
    assert (Hvnps' : Forall2 (view_nparams ΘR Ξ R) Vs Nvs)
      by (eapply Forall2_impl; [ intros x Nv; apply (equiv_view_nparams _ _ _ Heq HΞ) | exact Hvnps ]).
    assert (Hfil' : raw_decl_filed ΘR Ξ R Vs Ss csD csV Nvs = Some Dd) by (rewrite <- (equiv_raw_decl_filed _ _ _ Heq); exact Hfil).
    pose proof (equiv_ind_nil_at _ _ _ Heq HΞ _ _ _ Hnil) as Hnil'.
    destruct (H1 _ _ Hli Hrb) as [ΘR1 RbR1 Hr1 Hli1 Hrb1 He1 Hg1]; cbn beta in Hr1.
    destruct (H2 _ _ Hli1 Hrb1) as [ΘR2 RbR2 Hr2 Hli2 Hrb2 He2 Hg2]; cbn beta in Hr2.
    rewrite <- (equiv_rec_cmds _ _ _ _ _ _ (unit_invariant_equiv Hli1)) in Hr2.
    apply (mk_cmd_post _ _ _ _ _ ΘR2 RbR2); [ eapply run_cmd_ind_case; eassumption | exact Hli2 | exact Hrb2
                                            | eapply ext_trans; eassumption |].
    exact (grows_trans Hg1 Hg2 (dom_grows Hli1 (proj1 Hrb1) Hr2 Hli2)).
  Qed.

  (** *** Records *)

  (** The frame of a record's module, opened where the record is declared,
      keeps the invariant. *)
  Lemma unit_invariant_push_record {ch Θ K D ΘR Ξ x pv Δ Srt fs} :
    unit_invariant ch Θ K D ΘR Ξ -> gs_fresh x Ξ ->
    ΘR ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_record pv (ind_qname Ξ x) (record_at Ξ Δ Srt fs) ⋄ ->
    unit_invariant ch Θ K D ΘR (gs_push_record (ind_qname Ξ x) (record_at Ξ Δ Srt fs) Δ Ξ).
  Proof.
    intros Hli Hfr HE; destruct (record_nil_entry_params _ _ _ _ _ _ _ _ HE) as [Htel HΔ].
    destruct (record_nil_entry_params_evaluated _ _ _ _ _ _ _ _ HE) as [l HPr].
    destruct (params_evaluated_sorts _ _ _ _ _ HPr) as (ps & Hps & HT).
    apply (unit_invariant_stack Hli); [| exact (stack_in_push_record _ _ _ _ _ (ui_stack _ _ _ _ _ _ Hli) Hfr) ].
    destruct Ξ as [| [[mq Kq] Uq] Ξ0]; [ contradiction |].
    apply wf_gstack_cons; [ exact (ui_wf _ _ _ _ _ _ Hli) | eapply wf_gmod_record_nil; [ exact Htel | exact HΔ | exact Hps | exact HT | exact HE | reflexivity ] |].
    cbn; exists x; split; [ reflexivity | exact Hfr ].
  Qed.

  (** A record's frame opened and its field definitions run in it, as
      [run_cmd_record_open] runs them, its entry checked at the
      restriction. *)
  Lemma record_open_ok {ch Θ K D B Ξ x pv Δ Srt fs r} :
    gs_fresh x Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_record pv (ind_qname Ξ x) (record_at Ξ Δ Srt fs) ⋄ ->
    post_cmds ch Θ K D B (gs_push_record (ind_qname Ξ x) (record_at Ξ Δ Srt fs) Δ Ξ)
      (List.map ci_core (record_field_cmds (record_at Ξ Δ Srt fs))) r ->
    post_cmd ch Θ K D B Ξ (core_cmd_record_open x pv Δ Srt fs) r.
  Proof.
    intros Hfr HE Hp ΘR RbR Hli Hrb.
    pose proof (unit_invariant_entry_at Hli Hfr HE) as HE'.
    destruct (Hp _ _ (unit_invariant_push_record Hli Hfr HE') Hrb) as [ΘR1 RbR1 Hr1 Hli1 Hrb1 He1 Hg1]; cbn beta in Hr1.
    apply (mk_cmd_post _ _ _ _ _ ΘR1 RbR1); [ eapply run_cmd_record_open; eassumption | assumption .. ].
  Qed.

  (** *** Units *)

  Lemma unit_pre {ch Θ K} : global_invariant ch Θ K -> exists ΘR, unit_invariant ch Θ K nil ΘR nil.
  Proof. intros G; exists nil; exact (nil_unit_invariant G). Qed.

  (** The imports run on the empty stack, from no binding, and leave the
      stack empty. *)
  Lemma unit_imports {ch Θ K imps r1} :
    global_invariant ch Θ K -> post_cmds ch Θ K nil builtins_empty nil imps r1 ->
    exists ΘR1 RbR1, nil ⍮ nil ⍮ builtins_empty ⍮ nil ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ imps ⇝* ΘR1 ⍮ nil ⍮ run_state_core_builtins r1 ⍮ RbR1 /\ run_state_core_stack r1 = nil /\
      unit_invariant ch (run_state_core_deps r1) (run_state_core_closures r1) (run_state_core_imports r1) ΘR1 nil /\ builtin_records_ok (run_state_core_closures r1) ΘR1 RbR1 /\
      ext Θ K (run_state_core_deps r1) (run_state_core_closures r1) /\ grows Θ (run_state_core_deps r1) (run_state_core_imports r1).
  Proof.
    intros G Hp; destruct (Hp _ _ (nil_unit_invariant G) (builtin_records_ok_nil K)) as [ΘR1 RbR1 Hr1 Hli1 Hrb1 He1 Hg1]; cbn beta in Hr1.
    pose proof (run_cmds_empty _ _ _ _ _ _ _ _ _ _ _ _ Hr1) as HΞ; rewrite HΞ in Hr1, Hli1.
    exists ΘR1, RbR1; exact (conj Hr1 (conj HΞ (conj Hli1 (conj Hrb1 (conj He1 Hg1))))).
  Qed.

  Lemma unit_gctx {ch Θ K imps r1} :
    global_invariant ch Θ K -> post_cmds ch Θ K nil builtins_empty nil imps r1 -> ⊢ᵍ gds_restrict (run_state_core_imports r1) (run_state_core_deps r1) ⍮ nil.
  Proof. intros G Hp; destruct (unit_imports G Hp) as (ΘR1 & _ & _ & _ & Hli1 & _); exact (unit_invariant_restrict_gctx Hli1). Qed.

  Lemma unit_body_pre {fp ch Θ K imps r1 P l} :
    global_invariant (fp :: ch) Θ K -> post_cmds (fp :: ch) Θ K nil builtins_empty nil imps r1 -> all_assumptions P ->
    ⊢ gds_restrict (run_state_core_imports r1) (run_state_core_deps r1) ⍮ nil ⍮ P ->
    params_evaluated (gds_restrict (run_state_core_imports r1) (run_state_core_deps r1)) nil nil P l ->
    exists ΘR, unit_invariant (fp :: ch) (run_state_core_deps r1) (run_state_core_closures r1) (run_state_core_imports r1) ΘR (gs_push (q_abs fp nil) P nil).
  Proof.
    intros G Hp Htel HP HPr; destruct (unit_imports G Hp) as (ΘR1 & _ & _ & _ & Hli1 & _).
    exists ΘR1; exact (proj2 (proj2 (unit_invariant_push_unit Hli1 Htel HP HPr))).
  Qed.

  (** A unit: its imports, its parameters filled and checked, then its
      body in its own frame, which is the only one left. *)
  Lemma unit_ok {fp ch Θ K imps P0 P l cs r1 r2 mp Kf U} :
    post_cmds (fp :: ch) Θ K nil builtins_empty nil (List.map ci_written imps) r1 ->
    fill_params (gds_restrict (run_state_core_imports r1) (run_state_core_deps r1)) nil (run_state_core_builtins r1) P0 P ->
    all_assumptions P ->
    ⊢ gds_restrict (run_state_core_imports r1) (run_state_core_deps r1) ⍮ nil ⍮ P ->
    params_evaluated (gds_restrict (run_state_core_imports r1) (run_state_core_deps r1)) nil nil P l ->
    acc_ok (gds_restrict (run_state_core_imports r1) (run_state_core_deps r1)) nil (tele_refs nil P0) ->
    post_cmds (fp :: ch) (run_state_core_deps r1) (run_state_core_closures r1) (run_state_core_imports r1) (run_state_core_builtins r1)
      (gs_push (q_abs fp nil) P nil) (List.map ci_written cs) r2 ->
    run_state_core_stack r2 = (mp, Kf, U) :: nil ->
    post_unit (fp :: ch) Θ K (imps, P0, cs) (mk_unit_result_core (run_state_core_deps r2) (run_state_core_closures r2) (run_state_core_imports r2) (run_state_core_builtins r2) U).
  Proof.
    intros Hp1 Hfa Htel HP HPr Hac Hp2 HΞ G; cbn [unit_result_core_deps unit_result_core_closures unit_result_core_imports unit_result_core_builtins unit_result_core_unit].
    destruct (unit_imports G Hp1) as (ΘR1 & RbR1 & Hr1 & _ & Hli1 & Hrb1 & He1 & Hg1).
    pose proof (gds_equiv_sym _ _ (unit_invariant_equiv Hli1)) as Heq.
    pose proof (equiv_acc _ _ _ _ Heq Hac) as Hac'.
    pose proof (equiv_fill_params _ _ _ _ _ _ Heq (ui_wf _ _ _ _ _ _ Hli1) Hfa) as Hfa'.
    destruct (unit_invariant_push_unit Hli1 Htel HP HPr) as (HP' & HPr' & Hli1').
    destruct (Hp2 _ _ Hli1' Hrb1) as [ΘR2 RbR2 Hr2 Hli2 Hrb2 He2 Hg2]; cbn beta in Hr2.
    rewrite HΞ in Hr2, Hli2.
    destruct (unit_invariant_runs_wf Hli1' (proj1 Hrb1) Hr2) as (_ & _ & Hs12 & _).
    destruct Hli2 as [G2 Hs2 Hd2 Hc2 _ _].
    apply (mk_unit_post _ _ _ _ _ RbR2 ΘR2);
      [ eapply run_unit_intro; [ exact Hr1 | exact Hfa' | exact Htel | exact HP' | exact HPr' | exact Hac' | exact Hr2 ]
      | exact G2 | exact Hs2 | exact Hd2 | exact Hc2 | exact (proj2 Hrb2) | eapply ext_trans; eassumption |].
    intros x Hx; destruct (Hg2 _ Hx) as [Hx1 | Hx1]; [| right; exact Hx1 ].
    destruct (Hg1 _ Hx1) as [Hx0 | Hx0]; [ left; exact Hx0 | right ].
    apply Hd2, (sub_dom _ _ _ Hs12), (ui_dom _ _ _ _ _ _ Hli1), Hx0.
  Qed.

  (** ** The Executable

      A list of items runs by [items_impl], well founded on the items'
      weight ([items_weight]): a command as written weighs more than the
      items it is filled to, a core command one.  The commands a
      declaration generates run by [gen_items_impl], structural on the
      list.  Only a load recurses on something else: the chain grows by an
      unfiled path that [load_path] knows ([load_step]), and
      [run_unit_impl] is structural on the accessibility proof.  The
      executable takes that proof, never the list of files. *)

  #[warnings="-cannot-define-projection"]
  Record load_step (ch' ch : list path) : Prop := mk_load_step
    { (** the path loaded *)
      load_step_path : path
      (** its contents *)
    ; load_step_src : string
      (** the chain grows by it *)
    ; load_step_chain : ch' = load_step_path :: ch
      (** which it was not on *)
    ; load_step_fresh : ~ In load_step_path ch
      (** and whose file is found *)
    ; load_step_load : load_path load_step_path = Some load_step_src }.

  Definition load_step_intro {ch fp src} (Hn : ~ In fp ch) (Hs : load_path fp = Some src) :
    load_step (fp :: ch) ch :=
    mk_load_step _ _ fp src eq_refl Hn Hs.

  (** *** The Fast State

      The executable keeps the state fast ([run_state], [unit_result]); the
      invariants and the [post_*] are about its Core reading ([run_state_read],
      [unit_result_read]).  A fast state refines its reading: its filed units are
      the translations of theirs ([units_rep]) and its frames those of its
      stack ([fs_of]).  With the well-formedness the invariant has, which
      makes the reading canonical, this is what makes the fast context of
      a command a translation ([pre_fctx_ok]).

      A unit filed or seen stores values right in its home: the units its
      run imported ([unit_closure_find]) and the unit itself, with no frame
      open.  The open frames store values right in the context of each
      frame and the frames below it ([frames_values_ok]). *)

  (** A unit's values, right in its home *)
  #[warnings="-cannot-define-projection"]
  Record unit_values_home (K : unit_closure_map) (Θ : gdeps) (fp : path) (u : funit) : Prop := mk_unit_values_home
    { (** the units the unit's run imported *)
      uvh_closure : list path
      (** as [K] records them *)
    ; uvh_find : unit_closure_find K fp = Some uvh_closure
      (** the values are right where the unit and its closure are filed,
          with no frame open *)
    ; uvh_values : funit_values_ok (gds_restrict (fp :: uvh_closure) Θ) nil u }.

  (** The values of the units filed and of the units seen, right in their
      homes *)
  Record units_values_ok (K : unit_closure_map) (s : funits) : Prop := mk_units_values_ok
    { (** of every unit filed *)
      uvo_filed : forall fp u, fus_find s fp = Some u -> unit_values_home K (decode_units s) fp u
      (** of every unit seen *)
    ; uvo_seen : forall fp u, path_key_find fp (fus_visible s) = Some u -> unit_values_home K (decode_units s) fp u }.

  (** Fast frames that refine their reading *)
  Record frames_rep (Θ : gdeps) (fs : fstack) : Prop := mk_frames_rep
    { (** the frames, their values dropped, are the translation of their
          reading *)
      frep_drop : fstack_drop fs = fs_of (decode_stack fs)
      (** their values are right, in [Θ] *)
    ; frep_values : frames_values_ok Θ fs }.

  (** A restriction grows with its paths and its units. *)
  Lemma restrict_mono : forall S S' Θ Θ', incl S S' -> Θ ⊑ Θ' -> gds_restrict S Θ ⊑ gds_restrict S' Θ'.
  Proof.
    intros * HS HΘ fp U; rewrite !gds_lookup_restrict.
    destruct (existsb (path_beq fp) S) eqn:E; [| discriminate ].
    apply existsb_path_beq, HS, existsb_path_beq in E; rewrite E; apply HΘ.
  Qed.

  (** A unit's values stay right in its home as more units are filed. *)
  Lemma unit_values_home_grow : forall ch ch' K K' Θ Θ' fp u,
      global_invariant ch Θ K -> global_invariant ch' Θ' K' ->
      (forall Dx, unit_closure_find K fp = Some Dx -> unit_closure_find K' fp = Some Dx) -> Θ ⊑ Θ' ->
      unit_values_home K Θ fp u -> unit_values_home K' Θ' fp u.
  Proof.
    intros * G G' HK HΘ [Dx HD Hv]; apply (mk_unit_values_home _ _ _ _ Dx (HK _ HD)).
    refine (funit_values_grow _ _ _ _ (gc_sub_deps _ _ _ _) (global_invariant_closure_wf G HD)
              (global_invariant_closure_wf G' (HK _ HD)) _ Hv).
    apply restrict_mono; [ apply incl_refl | exact HΘ ].
  Qed.

  (** The units seen store values right in what a command sees. *)
  Lemma units_values_view : forall ch K s D Ξ, global_invariant ch (decode_units s) K ->
      units_values_ok K s -> visible_rep s D -> closed_under_unit_closures K D ->
      ⊢ᵍ gds_restrict D (decode_units s) ⍮ Ξ ->
      forall fp u, path_key_find fp (fus_visible s) = Some u -> funit_values_ok (gds_restrict D (decode_units s)) Ξ u.
  Proof.
    intros * G Hs Hv Hc HΞ fp u Hu.
    destruct (uvo_seen _ _ Hs _ _ Hu) as [Dx HD Hx].
    assert (Hin : In fp D).
    { pose proof (Hv fp) as E; rewrite Hu in E; cbn [option_map] in E.
      destruct (existsb (path_beq fp) D) eqn:Eb; [ apply existsb_path_beq, Eb | discriminate ]. }
    assert (Hsub : gds_restrict (fp :: Dx) (decode_units s) ⊑ gds_restrict D (decode_units s)).
    { apply restrict_mono; [| apply gds_sub_refl ]; intros y [<- | Hy]; [ exact Hin | exact (Hc _ _ Hin HD _ Hy) ]. }
    rewrite <- (app_nil_r Ξ) in HΞ |- *.
    destruct (wf_gstack_app_inv _ _ _ HΞ) as [HD0 HsΞ].
    pose proof (funit_values_grow _ _ _ _ (gc_sub_deps _ _ nil Hsub) (global_invariant_closure_wf G HD) HD0 _ Hx) as Hx'.
    exact (funit_values_grow _ _ _ _ HsΞ HD0 HΞ _ Hx').
  Qed.

  (** What a step needs of the state it runs at, fast: the invariant of its
      reading, and that it refines it *)
  Record pre (ch : list path) (s : funits) (K : unit_closure_map) (D : list path) (fs : fstack) : Prop := mk_pre
    { (** the invariant of the reading *)
      pre_unit_invariant : exists ΘR, unit_invariant ch (decode_units s) K D ΘR (decode_stack fs)
      (** the filed units refine their reading *)
    ; pre_units : units_rep (funits_drop s) (decode_units s)
      (** the units seen are those filed at the imported paths *)
    ; pre_visible : visible_rep s D
      (** the frames are those of their reading *)
    ; pre_frames : fstack_drop fs = fs_of (decode_stack fs)
      (** the units filed and seen store values right in their homes *)
    ; pre_unit_values : units_values_ok K s
      (** the frames store values right where they are open *)
    ; pre_frame_values : frames_values_ok (gds_restrict D (decode_units s)) fs }.

  (** What a step proves of the fast state it ends with: [P] of its
      reading, which it refines *)
  Record fast_res (P : run_state_core -> Prop) (r : run_state) : Prop := mk_fast_res
    { (** what the step proves of the reading *)
      fres_post : P (run_state_read r)
      (** the filed units refine their reading *)
    ; fres_units : units_rep (funits_drop (run_state_units r)) (decode_units (run_state_units r))
      (** the units seen are those filed at the imported paths *)
    ; fres_visible : visible_rep (run_state_units r) (run_state_imports r)
      (** the frames are those of their reading *)
    ; fres_frames : fstack_drop (run_state_frames r) = fs_of (decode_stack (run_state_frames r))
      (** the units filed and seen store values right in their homes *)
    ; fres_unit_values : units_values_ok (run_state_closures r) (run_state_units r)
      (** the frames store values right where they are open *)
    ; fres_frame_values : frames_values_ok (gds_restrict (run_state_imports r) (decode_units (run_state_units r))) (run_state_frames r) }.

  (** The reading of a state the invariant holds at is canonical. *)
  Lemma unit_invariant_canon {ch Θ K D ΘR Ξ} : unit_invariant ch Θ K D ΘR Ξ -> canon_deps Θ /\ canon_stack Ξ.
  Proof.
    intros Hli; split;
      [ exact (proj1 (canon_of_wf _ _ (gi_wf _ _ _ (ui_global _ _ _ _ _ _ Hli)))) | exact (proj2 (canon_of_wf _ _ (ui_wf _ _ _ _ _ _ Hli))) ].
  Qed.

  Lemma pre_canon {ch s K D fs} : pre ch s K D fs -> canon_stack (decode_stack fs).
  Proof. intros [[ΘR Hli] _ _ _]; exact (proj2 (unit_invariant_canon Hli)). Qed.

  (** The fast context of a command is a translation. *)
  Lemma pre_fctx_ok {ch s K D fs} : pre ch s K D fs -> fctx_ok (cmd_view s D) fs.
  Proof.
    intros [[ΘR Hli] Hu Hv Hf Huv Hfv]; destruct (unit_invariant_canon Hli) as [HcΘ HcΞ].
    pose proof (unit_invariant_restrict_gctx Hli) as HΞ.
    exact (mk_fctx_ok (cmd_view s D) fs (decode_units s) (decode_stack fs) HcΘ HcΞ Hu Hv Hf
             (units_values_view _ K s D _ (ui_global _ _ _ _ _ _ Hli) Huv Hv (ui_closed _ _ _ _ _ _ Hli) HΞ) (frames_values_current _ _ HΞ Hfv)).
  Qed.

  (** The fast context a step's checks look names up in *)
  #[local] Abbreviation cmd_F B H := (fctx_cmd B _ _ _ (pre_fctx_ok H)).

  (** What is found at a step's fast context, read at its restriction and
      its stack *)
  Lemma cmd_read {ch s K D fs} B (H : pre ch s K D fs) (P : GCtx -> ctx -> Prop) :
      P (fc_gctx (cmd_F B H)) (fc_tele (cmd_F B H)) -> P (gc_mk (gds_restrict D (decode_units s)) (decode_stack fs)) (gs_tele (decode_stack fs)).
  Proof. rewrite fc_gctx_cmd, fc_tele_cmd; exact (fun h => h). Qed.

  (** The other way round *)
  Lemma cmd_unread {ch s K D fs} B (H : pre ch s K D fs) (P : GCtx -> ctx -> Prop) :
      P (gc_mk (gds_restrict D (decode_units s)) (decode_stack fs)) (gs_tele (decode_stack fs)) -> P (fc_gctx (cmd_F B H)) (fc_tele (cmd_F B H)).
  Proof. rewrite fc_gctx_cmd, fc_tele_cmd; exact (fun h => h). Qed.

  Lemma pre_gctx_f {ch s K D fs} B (H : pre ch s K D fs) : ⊢ᵍ fc_deps (cmd_F B H) ⍮ fc_stack (cmd_F B H).
  Proof. exact (cmd_unread B H (fun G _ => ⊢ᵍ @gc_deps G ⍮ @gc_stack G) (pre_gctx (pre_unit_invariant _ _ _ _ _ H))). Qed.

  Lemma pre_ctx_f {ch s K D fs} B (H : pre ch s K D fs) : ⊢ fc_deps (cmd_F B H) ⍮ fc_stack (cmd_F B H) ⍮ fc_tele (cmd_F B H).
  Proof. exact (cmd_unread B H (fun G Γ => ⊢ @gc_deps G ⍮ @gc_stack G ⍮ Γ) (pre_ctx (pre_unit_invariant _ _ _ _ _ H))). Qed.

  (** A term typed at a step's fast context, read in Core *)
  Lemma cmd_exp {ch s K D fs} B (H : pre ch s K D fs) Δ M A :
      fc_deps (cmd_F B H) ⍮ fc_stack (cmd_F B H) ⍮ Δ ++ fc_tele (cmd_F B H) ⊢ M : A ->
      gds_restrict D (decode_units s) ⍮ decode_stack fs ⍮ Δ ++ gs_tele (decode_stack fs) ⊢ M : A.
  Proof. exact (cmd_read B H (fun G Γ => @gc_deps G ⍮ @gc_stack G ⍮ Δ ++ Γ ⊢ M : A)). Qed.

  (** A telescope's extension *)
  Lemma cmd_ext {ch s K D fs} B (H : pre ch s K D fs) Δ :
      fc_deps (cmd_F B H) ⍮ fc_stack (cmd_F B H) ⍮ fc_tele (cmd_F B H) ⊢ˣ Δ ≈ Δ ->
      gds_restrict D (decode_units s) ⍮ decode_stack fs ⍮ gs_tele (decode_stack fs) ⊢ˣ Δ ≈ Δ.
  Proof. exact (cmd_read B H (fun G Γ => @gc_deps G ⍮ @gc_stack G ⍮ Γ ⊢ˣ Δ ≈ Δ)). Qed.

  (** A module expression *)
  Lemma cmd_modexp {ch s K D fs} B (H : pre ch s K D fs) Δ E :
      fc_deps (cmd_F B H) ⍮ fc_stack (cmd_F B H) ⍮ Δ ++ fc_tele (cmd_F B H) ⊢ᵐ E ≈ E ->
      gds_restrict D (decode_units s) ⍮ decode_stack fs ⍮ Δ ++ gs_tele (decode_stack fs) ⊢ᵐ E ≈ E.
  Proof. exact (cmd_read B H (fun G Γ => @gc_deps G ⍮ @gc_stack G ⍮ Δ ++ Γ ⊢ᵐ E ≈ E)). Qed.

  (** A context *)
  Lemma cmd_ctx {ch s K D fs} B (H : pre ch s K D fs) Δ :
      ⊢ fc_deps (cmd_F B H) ⍮ fc_stack (cmd_F B H) ⍮ Δ ++ fc_tele (cmd_F B H) ->
      ⊢ gds_restrict D (decode_units s) ⍮ decode_stack fs ⍮ Δ ++ gs_tele (decode_stack fs).
  Proof. exact (cmd_read B H (fun G Γ => ⊢ @gc_deps G ⍮ @gc_stack G ⍮ Δ ++ Γ)). Qed.

  (** A context given whole *)
  Lemma cmd_ctx_at {ch s K D fs} B (H : pre ch s K D fs) Γ :
      ⊢ fc_deps (cmd_F B H) ⍮ fc_stack (cmd_F B H) ⍮ Γ -> ⊢ gds_restrict D (decode_units s) ⍮ decode_stack fs ⍮ Γ.
  Proof. exact (cmd_read B H (fun G _ => ⊢ @gc_deps G ⍮ @gc_stack G ⍮ Γ)). Qed.

  (** An inference *)
  Lemma cmd_infer {ch s K D fs} B (H : pre ch s K D fs) Δ W M :
      @alg_type_infer (fc_gctx (cmd_F B H)) (Δ ++ fc_tele (cmd_F B H)) W M ->
      @alg_type_infer (gc_mk (gds_restrict D (decode_units s)) (decode_stack fs)) (Δ ++ gs_tele (decode_stack fs)) W M.
  Proof. exact (cmd_read B H (fun G Γ => @alg_type_infer G (Δ ++ Γ) W M)). Qed.

  (** Parameters of evaluated kinds, over the frames' telescope *)
  Lemma cmd_params_evaluated {ch s K D fs} B (H : pre ch s K D fs) Δ l :
      params_evaluated (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) (fc_tele (cmd_F B H)) Δ l ->
      params_evaluated (gds_restrict D (decode_units s)) (decode_stack fs) (gs_tele (decode_stack fs)) Δ l.
  Proof. exact (cmd_read B H (fun G Γ => params_evaluated (@gc_deps G) (@gc_stack G) Γ Δ l)). Qed.

  (** Parameters of evaluated kinds, over a context given whole *)
  Lemma cmd_params_evaluated_at {ch s K D fs} B (H : pre ch s K D fs) Γ Δ l :
      params_evaluated (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) Γ Δ l ->
      params_evaluated (gds_restrict D (decode_units s)) (decode_stack fs) Γ Δ l.
  Proof. exact (cmd_read B H (fun G _ => params_evaluated (@gc_deps G) (@gc_stack G) Γ Δ l)). Qed.

  (** A module read with no member of a type of levels over a parameter
      of a universe *)
  Lemma cmd_levels_abstractable {ch s K D fs} B (H : pre ch s K D fs) Δ E :
      levels_abstractable (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) ⋅ (Δ ++ fc_tele (cmd_F B H)) E ->
      levels_abstractable (gds_restrict D (decode_units s)) (decode_stack fs) ⋅ (Δ ++ gs_tele (decode_stack fs)) E.
  Proof. exact (cmd_read B H (fun G Γ => levels_abstractable (@gc_deps G) (@gc_stack G) ⋅ (Δ ++ Γ) E)). Qed.

  (** The privacy of a command's references *)
  Lemma cmd_acc {ch s K D fs} B (H : pre ch s K D fs) l :
      acc_ok (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) l -> acc_ok (gds_restrict D (decode_units s)) (decode_stack fs) l.
  Proof. exact (cmd_read B H (fun G _ => acc_ok (@gc_deps G) (@gc_stack G) l)). Qed.

  (** A normal form *)
  Lemma cmd_nbe {ch s K D fs} B (H : pre ch s K D fs) Δ M A W :
      nbe (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) (Δ ++ fc_tele (cmd_F B H)) M A W ->
      nbe (gds_restrict D (decode_units s)) (decode_stack fs) (Δ ++ gs_tele (decode_stack fs)) M A W.
  Proof. exact (cmd_read B H (fun G Γ => nbe (@gc_deps G) (@gc_stack G) (Δ ++ Γ) M A W)). Qed.

  (** A group found *)
  Lemma cmd_ind_lookup {ch s K D fs} B (H : pre ch s K D fs) p o :
      ind_lookup (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) p = o -> ind_lookup (gds_restrict D (decode_units s)) (decode_stack fs) p = o.
  Proof. exact (cmd_read B H (fun G _ => ind_lookup (@gc_deps G) (@gc_stack G) p = o)). Qed.

  (** A type former of an inductive type *)
  Lemma cmd_ind_former {ch s K D fs} B (H : pre ch s K D fs) Δ M W :
      ind_former (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) (Δ ++ fc_tele (cmd_F B H)) M W ->
      ind_former (gds_restrict D (decode_units s)) (decode_stack fs) (Δ ++ gs_tele (decode_stack fs)) M W.
  Proof. exact (cmd_read B H (fun G Γ => ind_former (@gc_deps G) (@gc_stack G) (Δ ++ Γ) M W)). Qed.

  (** A type former of a record type *)
  Lemma cmd_record_former {ch s K D fs} B (H : pre ch s K D fs) Δ M W :
      record_former (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) (Δ ++ fc_tele (cmd_F B H)) M W ->
      record_former (gds_restrict D (decode_units s)) (decode_stack fs) (Δ ++ gs_tele (decode_stack fs)) M W.
  Proof. exact (cmd_read B H (fun G Γ => record_former (@gc_deps G) (@gc_stack G) (Δ ++ Γ) M W)). Qed.

  (** A mutual definition's group *)
  Lemma cmd_mdef_group {ch s K D fs} B (H : pre ch s K D fs) Δ f0 fs0 pq m0 Ps Dd Us ms :
      mdef_group (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) Δ f0 fs0 pq m0 Ps Dd Us ms ->
      mdef_group (gds_restrict D (decode_units s)) (decode_stack fs) Δ f0 fs0 pq m0 Ps Dd Us ms.
  Proof. exact (cmd_read B H (fun G _ => mdef_group (@gc_deps G) (@gc_stack G) Δ f0 fs0 pq m0 Ps Dd Us ms)). Qed.

  (** A record checked with an empty module *)
  Lemma cmd_record_entry {ch s K D fs} B (H : pre ch s K D fs) mp pv Δ Srt fds :
      fc_deps (cmd_F B H) ⍮ fc_stack (cmd_F B H) ⍮ mp ⊢ᵉ ge_record pv mp (record_at (fc_stack (cmd_F B H)) Δ Srt fds) ⋄ ->
      gds_restrict D (decode_units s) ⍮ decode_stack fs ⍮ mp ⊢ᵉ ge_record pv mp (record_at (decode_stack fs) Δ Srt fds) ⋄.
  Proof. exact (cmd_read B H (fun G _ => @gc_deps G ⍮ @gc_stack G ⍮ mp ⊢ᵉ ge_record pv mp (record_at (@gc_stack G) Δ Srt fds) ⋄)). Qed.

  (** A fill found at a step's fast context, read in Core *)
  Lemma cmd_fill {ch s K D fs} B (H : pre ch s K D fs) c its :
      fill_cmd (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) B c its -> fill_cmd (gds_restrict D (decode_units s)) (decode_stack fs) B c its.
  Proof. exact (cmd_read B H (fun G _ => fill_cmd (@gc_deps G) (@gc_stack G) B c its)). Qed.

  (** A telescope's fill *)
  Lemma cmd_fill_params {ch s K D fs} B (H : pre ch s K D fs) Δ Δ' :
      fill_params (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) B Δ Δ' -> fill_params (gds_restrict D (decode_units s)) (decode_stack fs) B Δ Δ'.
  Proof. exact (cmd_read B H (fun G _ => fill_params (@gc_deps G) (@gc_stack G) B Δ Δ')). Qed.

  (** What an open generates *)
  Lemma cmd_open_gens {ch s K D fs} B (H : pre ch s K D fs) E its gs HE :
      import_gen (cmd_F B H) (pre_gctx_f B H) (fc_tele (cmd_F B H)) E E HE its = open_success gs ->
      open_gens (gds_restrict D (decode_units s)) (decode_stack fs) (gs_tele (decode_stack fs)) E its gs.
  Proof.
    intros Eg; apply import_gen_spec in Eg.
    exact (cmd_read B H (fun G Γ => open_gens (@gc_deps G) (@gc_stack G) Γ E its gs) Eg).
  Qed.

  (** An entry's values right at a command's fast context, read in Core *)
  Lemma cmd_entry_values {ch s K D fs} B (H : pre ch s K D fs) e :
      fentry_values_ok (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) e -> fentry_values_ok (gds_restrict D (decode_units s)) (decode_stack fs) e.
  Proof. exact (cmd_read B H (fun G _ => fentry_values_ok (@gc_deps G) (@gc_stack G) e)). Qed.

  (** The commands of a member's module, read in Core *)
  Lemma ind_mod_cmds_cmd {ch s K D fs} B (H : pre ch s K D fs) R pq Dd k M :
      ind_mod_cmds_f (cmd_F B H) R pq Dd k M = ind_mod_cmds (gds_restrict D (decode_units s)) (decode_stack fs) R pq Dd k M.
  Proof.
    rewrite ind_mod_cmds_f_ok.
    exact (cmd_unread B H (fun G _ => ind_mod_cmds (@gc_deps G) (@gc_stack G) R pq Dd k M
                                        = ind_mod_cmds (gds_restrict D (decode_units s)) (decode_stack fs) R pq Dd k M) eq_refl).
  Qed.

  (** The commands of a group's recursor module, read in Core *)
  Lemma rec_cmds_cmd {ch s K D fs} B (H : pre ch s K D fs) R pq Dd :
      rec_cmds_f (cmd_F B H) R pq Dd = rec_cmds (gds_restrict D (decode_units s)) (decode_stack fs) R pq Dd.
  Proof.
    rewrite rec_cmds_f_ok.
    exact (cmd_unread B H (fun G _ => rec_cmds (@gc_deps G) (@gc_stack G) R pq Dd = rec_cmds (gds_restrict D (decode_units s)) (decode_stack fs) R pq Dd)
             eq_refl).
  Qed.

  (** An entry added, fast: a step that ends with [x ↦ E] added to the
      innermost frame ends with the fast entry added that translates it. *)
  Lemma add_res {ch s K D fs x E} {e : fentry} {P : gstack -> Prop} :
      pre ch s K D fs -> fentry_drop e = translate_entry E -> canon_stack (gs_add x E (decode_stack fs)) -> P (gs_add x E (decode_stack fs)) ->
      P (decode_stack (fs_add x e fs)) /\ fstack_drop (fs_add x e fs) = fs_of (decode_stack (fs_add x e fs)).
  Proof.
    intros H Hd Hc Hp.
    rewrite (decode_stack_add _ _ _ _ (pre_frames _ _ _ _ _ H) Hd Hc); split; [ exact Hp |].
    exact (fs_add_drop_of _ _ _ _ (pre_frames _ _ _ _ _ H) Hd).
  Qed.

  (** A translated entry stores no value. *)
  Lemma translate_entry_drop_of : forall e E, e = translate_entry E -> fentry_drop e = translate_entry E.
  Proof. intros * ->; apply translate_entry_drop. Qed.

  (** A step ending with an entry added to the innermost frame, the units
      and the rest unchanged *)
  Lemma add_post {ch s K D B fs c x E} {e : fentry} : pre ch s K D fs -> fentry_drop e = translate_entry E ->
      fentry_values_ok (gds_restrict D (decode_units s)) (decode_stack fs) e ->
      post_cmd ch (decode_units s) K D B (decode_stack fs) c (mk_run_state_core (decode_units s) K D B (gs_add x E (decode_stack fs))) ->
      post_cmd ch (decode_units s) K D B (decode_stack fs) c (mk_run_state_core (decode_units s) K D B (decode_stack (fs_add x e fs))) /\
      frames_rep (gds_restrict D (decode_units s)) (fs_add x e fs).
  Proof.
    intros H Hd He Hp.
    destruct (pre_unit_invariant _ _ _ _ _ H) as [ΘR Hli]; destruct (unit_invariant_builtin_records Hli) as [RbR Hrb].
    destruct (Hp _ _ Hli Hrb) as [ΘR' RbR' _ Hli' _ _ _].
    destruct (add_res (P := fun Ξ => post_cmd ch (decode_units s) K D B (decode_stack fs) c (mk_run_state_core (decode_units s) K D B Ξ)) H
                Hd (proj2 (unit_invariant_canon Hli')) Hp) as [Hp' Hf].
    split; [ exact Hp' | constructor; [ exact Hf |] ].
    apply (frames_values_add_before _ _ _ _ E (unit_invariant_restrict_gctx Hli) (unit_invariant_restrict_gctx Hli') (pre_frame_values _ _ _ _ _ H)); [| exact He ].
    exact (decode_stack_add _ _ _ _ (pre_frames _ _ _ _ _ H) Hd (proj2 (unit_invariant_canon Hli'))).
  Qed.

  (** A translated entry, added as a step's result: it stores no value. *)
  Lemma add_post_translate {ch s K D B fs c x E} {e : fentry} : pre ch s K D fs -> e = translate_entry E ->
      post_cmd ch (decode_units s) K D B (decode_stack fs) c (mk_run_state_core (decode_units s) K D B (gs_add x E (decode_stack fs))) ->
      post_cmd ch (decode_units s) K D B (decode_stack fs) c (mk_run_state_core (decode_units s) K D B (decode_stack (fs_add x e fs))) /\
      frames_rep (gds_restrict D (decode_units s)) (fs_add x e fs).
  Proof. intros H He; apply (add_post H (translate_entry_drop_of _ _ He)); subst e; apply translate_entry_values. Qed.

  (** A fast entry standing for [E] where it is added to the frames [Ξ] at
      [Θ]: [E]'s translation, its values dropped, and its values right *)
  Record entry_rep (Θ : gdeps) (Ξ : gstack) (E : gentry) (e : fentry) : Prop := mk_entry_rep
    { (** it is [E]'s translation, its values dropped *)
      erep_drop : fentry_drop e = translate_entry E
      (** its values are right *)
    ; erep_values : fentry_values_ok Θ Ξ e }.

  (** A translated entry stands for what it translates. *)
  Lemma translate_entry_rep : forall Θ Ξ E, entry_rep Θ Ξ E (translate_entry E).
  Proof. intros; constructor; [ apply translate_entry_drop | apply translate_entry_values ]. Qed.

  (** An entry equal to a translation stands for what it translates. *)
  Lemma entry_rep_of_eq : forall Θ Ξ E e, e = translate_entry E -> entry_rep Θ Ξ E e.
  Proof. intros * ->; apply translate_entry_rep. Qed.

  (** The fast entry of a definition, at a step *)
  Definition def_entry_rep {ch s K D fs} B (H : pre ch s K D fs) (b pv : bool) (κ : abs_kind) (i : nat) (A M : exp)
      (HA : fc_deps (cmd_F B H) ⍮ fc_stack (cmd_F B H) ⍮ fc_tele (cmd_F B H) ⊢ A : abs_kind_sort κ Typeω@i)
      (HM : fc_deps (cmd_F B H) ⍮ fc_stack (cmd_F B H) ⍮ fc_tele (cmd_F B H) ⊢ M : A) :
      {e : fentry | entry_rep (gds_restrict D (decode_units s)) (decode_stack fs) (gs_def b pv κ (decode_stack fs) A M) e} :=
    let (e, He) := def_fentry (cmd_F B H) b pv κ i A M HA HM in
    exist _ e (mk_entry_rep _ _ _ _ (eq_trans (proj1 He) (f_equal translate_entry (fs_def_dec b pv κ fs A M))) (cmd_entry_values B H e (proj2 He))).

  (** The fast entry of a definition with a module part, at a step *)
  Definition dm_entry_rep {ch s K D fs} B (H : pre ch s K D fs) (pv : bool) (Δ : ctx) (i : nat) (A M : exp) (E : modexp)
      (HA : fc_deps (cmd_F B H) ⍮ fc_stack (cmd_F B H) ⍮ Δ ++ fc_tele (cmd_F B H) ⊢ A : Typeω@i)
      (HM : fc_deps (cmd_F B H) ⍮ fc_stack (cmd_F B H) ⍮ Δ ++ fc_tele (cmd_F B H) ⊢ M : A) :
      {e : fentry | entry_rep (gds_restrict D (decode_units s)) (decode_stack fs) (dm_entry (decode_stack fs) pv Δ A M E) e} :=
    let (e, He) := dm_fentry (cmd_F B H) pv Δ i A M E HA HM in
    exist _ e (mk_entry_rep _ _ _ _ (eq_trans (proj1 He) (f_equal translate_entry (fs_dm_entry_dec fs pv Δ A M E)))
                 (cmd_entry_values B H e (proj2 He))).

  (** The state a step runs at, as a result, when its post holds there *)
  Lemma same_res {ch s K D B fs} {P : run_state_core -> Prop} : pre ch s K D fs ->
      P (mk_run_state_core (decode_units s) K D B (decode_stack fs)) -> fast_res P (mk_run_state s K D B fs).
  Proof.
    intros H Hp; constructor; [ exact Hp | exact (pre_units _ _ _ _ _ H) | exact (pre_visible _ _ _ _ _ H) | exact (pre_frames _ _ _ _ _ H)
                              | exact (pre_unit_values _ _ _ _ _ H) | exact (pre_frame_values _ _ _ _ _ H) ].
  Qed.

  (** A step that changed neither the units nor the frames, as a result *)
  Lemma state_res {ch s K D fs} {P : run_state_core -> Prop} {B'} : pre ch s K D fs ->
      P (mk_run_state_core (decode_units s) K D B' (decode_stack fs)) -> fast_res P (mk_run_state s K D B' fs).
  Proof.
    intros H Hp; constructor; [ exact Hp | exact (pre_units _ _ _ _ _ H) | exact (pre_visible _ _ _ _ _ H) | exact (pre_frames _ _ _ _ _ H)
                              | exact (pre_unit_values _ _ _ _ _ H) | exact (pre_frame_values _ _ _ _ _ H) ].
  Qed.

  (** The result of a step that changed the frames only *)
  Lemma frames_res {ch s K D B fs fs'} {P : run_state_core -> Prop} : pre ch s K D fs ->
      P (mk_run_state_core (decode_units s) K D B (decode_stack fs')) /\ frames_rep (gds_restrict D (decode_units s)) fs' -> fast_res P (mk_run_state s K D B fs').
  Proof.
    intros H [Hp [Hf Hfv]]; constructor;
      [ exact Hp | exact (pre_units _ _ _ _ _ H) | exact (pre_visible _ _ _ _ _ H) | exact Hf | exact (pre_unit_values _ _ _ _ _ H) | exact Hfv ].
  Qed.

  (** How a unit loaded under chain [ch] is run.  Its log holds the evals of
      the unit itself, not of the units it loads. *)
  Record unit_run_ok (ch : list path) (s : funits) (K : unit_closure_map) (u : surface_compilation_unit) (r : unit_result) : Prop := mk_unit_run_ok
    { (** what the run proves of the reading *)
      unit_run_ok_post : post_unit ch (decode_units s) K u (unit_result_read r)
      (** the filed units refine their reading *)
    ; unit_run_ok_units : units_rep (funits_drop (unit_result_units r)) (decode_units (unit_result_units r))
      (** the unit, its values dropped, is the translation of its reading *)
    ; unit_run_ok_unit : funit_drop (unit_result_unit r) = translate_unit (decode_unit (unit_result_unit r))
      (** the units filed and seen store values right in their homes *)
    ; unit_run_ok_unit_values : units_values_ok (unit_result_closures r) (unit_result_units r)
      (** the unit stores values right where it is filed, on top of what
          it imported *)
    ; unit_run_ok_own_values : forall fp, hd_error ch = Some fp ->
        funit_values_ok ((fp, decode_unit (unit_result_unit r)) :: gds_restrict (unit_result_imports r) (decode_units (unit_result_units r))) nil (unit_result_unit r) }.

  (** How a unit is loaded under the chain [ch] *)
  Definition loader (ch : list path) : Type :=
    forall fp src, ~ In fp ch -> load_path fp = Some src ->
      forall s K u, global_invariant (fp :: ch) (decode_units s) K -> units_rep (funits_drop s) (decode_units s) -> units_values_ok K s ->
        run_result ({r | unit_run_ok (fp :: ch) s K u r} * certified_log)%type.

  (** The result of a step on one core command *)
  Definition step_result ch s K D B fs c : Type :=
    run_result ({r | fast_res (post_cmd ch (decode_units s) K D B (decode_stack fs) c) r} * certified_log)%type.

  (** The result of a step that changes the frames only *)
  Definition frames_result ch s K D B fs c : Type :=
    run_result {fs' | post_cmd ch (decode_units s) K D B (decode_stack fs) c (mk_run_state_core (decode_units s) K D B (decode_stack fs')) /\
                      frames_rep (gds_restrict D (decode_units s)) fs'}.

  (** A step that changes the frames only, as a step on a command *)
  Definition frames_step {ch s K D B fs c} (H : pre ch s K D fs) (x : frames_result ch s K D B fs c) : step_result ch s K D B fs c :=
    match x with
    | run_success (exist _ fs' Hp) => run_success (exist _ (mk_run_state s K D B fs') (frames_res H Hp), log_nil)
    | run_failure e => run_failure e
    end.

  (** The invariant where a command ends *)
  Lemma cmd_pre_f {ch s K D B fs c r} : pre ch s K D fs -> fast_res (post_cmd ch (decode_units s) K D B (decode_stack fs) c) r ->
      pre ch (run_state_units r) (run_state_closures r) (run_state_imports r) (run_state_frames r).
  Proof.
    intros H [Hp Hu Hv Hf Huv Hfv]; constructor;
      [ exact (cmd_post_pre (pre_unit_invariant _ _ _ _ _ H) Hp) | exact Hu | exact Hv | exact Hf | exact Huv | exact Hfv ].
  Qed.

  (** The invariant where items end *)
  Lemma cmds_pre_f {ch s K D B fs cs r} : pre ch s K D fs -> fast_res (post_cmds ch (decode_units s) K D B (decode_stack fs) cs) r ->
      pre ch (run_state_units r) (run_state_closures r) (run_state_imports r) (run_state_frames r).
  Proof.
    intros H [Hp Hu Hv Hf Huv Hfv]; constructor;
      [ exact (cmds_post_pre (pre_unit_invariant _ _ _ _ _ H) Hp) | exact Hu | exact Hv | exact Hf | exact Huv | exact Hfv ].
  Qed.

  (** A core command, then the rest, fast *)
  Lemma core_cons_res {ch s K D B fs c cs r1 r2} :
      fast_res (post_cmd ch (decode_units s) K D B (decode_stack fs) c) r1 ->
      fast_res (post_cmds ch (decode_units (run_state_units r1)) (run_state_closures r1) (run_state_imports r1) (run_state_builtins r1) (decode_stack (run_state_frames r1)) cs) r2 ->
      fast_res (post_cmds ch (decode_units s) K D B (decode_stack fs) (ci_core c :: cs)) r2.
  Proof.
    intros [H1 _ _ _] [H2 Hu Hv Hf Huv Hfv]; constructor; [ exact (core_cons_ok H1 H2) | exact Hu | exact Hv | exact Hf | exact Huv | exact Hfv ].
  Qed.

  (** A command as written, then the rest, fast *)
  Lemma written_cons_res {ch s K D B fs c its cs r1 r2} :
      acc_ok (gds_restrict D (decode_units s)) (decode_stack fs) (cmd_refs c) ->
      fill_cmd (gds_restrict D (decode_units s)) (decode_stack fs) B c its ->
      fast_res (post_cmds ch (decode_units s) K D B (decode_stack fs) its) r1 ->
      fast_res (post_cmds ch (decode_units (run_state_units r1)) (run_state_closures r1) (run_state_imports r1) (run_state_builtins r1) (decode_stack (run_state_frames r1)) cs) r2 ->
      fast_res (post_cmds ch (decode_units s) K D B (decode_stack fs) (ci_written c :: cs)) r2.
  Proof.
    intros Hac Hfc [H1 _ _ _] [H2 Hu Hv Hf Huv Hfv]; constructor;
      [ exact (written_cons_ok Hac Hfc H1 H2) | exact Hu | exact Hv | exact Hf | exact Huv | exact Hfv ].
  Qed.

  (** *** Deciders *)

  (** "Are the parameters [Δ] over [Γ] of evaluated kinds, at a level?" *)
  Definition params_evaluated_dec (F : FCtx) (HΞ : ⊢ᵍ fc_deps F ⍮ fc_stack F) (Γ Δ : ctx) :
      {l | params_evaluated (fc_deps F) (fc_stack F) Γ Δ l} + {forall l, ~ params_evaluated (fc_deps F) (fc_stack F) Γ Δ l} :=
    match params_sorts_dec F (lvd _ _) HΞ Γ Δ with
    | inleft (exist _ (lP, bs) (conj _ HPs)) =>
        inleft (exist _ lP (params_evaluated_of_sorts _ _ _ _ _ (fun k => param_bool_sort lP (List.nth k (List.rev bs) false))
                              (fun k => param_bool_sort_ok _ _) HPs))
    | inright Hn => inright Hn
    end.

  (** Whether every assumption of a telescope is a type of levels, as a
      boolean *)
  Fixpoint level_sorted_parameters_b (Δ : ctx) : bool :=
    match Δ with
    | nil => true
    | ce_ass κ _ :: Δ' => (if abs_kind_eq_dec κ ak_level then true else false) && level_sorted_parameters_b Δ'
    | _ :: Δ' => level_sorted_parameters_b Δ'
    end.

  Lemma level_sorted_parameters_b_spec : forall Δ, level_sorted_parameters_b Δ = true <-> level_sorted_parameters Δ.
  Proof.
    induction Δ as [| e Δ IH].
    - split; [ intros _ Δ1 κ T Δ2 E; destruct Δ1; discriminate | reflexivity ].
    - assert (Htl : level_sorted_parameters (e :: Δ) -> level_sorted_parameters Δ)
        by (intros H Δ1 κ T Δ2 E; apply (H (e :: Δ1) κ T Δ2); rewrite E; reflexivity).
      destruct e as [κ0 T0 | T0 M0 | U0 | T0 M0 U0]; cbn [level_sorted_parameters_b].
      + split.
        * intros Hb Δ1 κ T Δ2 E; apply andb_prop in Hb as [Hk Hb].
          destruct Δ1 as [| e1 Δ1]; cbn in E; injection E as E1 E2.
          -- subst; destruct (abs_kind_eq_dec κ ak_level); [ assumption | discriminate ].
          -- subst; exact (proj1 IH Hb _ _ _ _ eq_refl).
        * intros H; apply andb_true_intro; split; [| apply IH, Htl, H ].
          destruct (abs_kind_eq_dec κ0 ak_level) as [| Hn]; [ reflexivity | exfalso; apply Hn, (H nil κ0 T0 Δ); reflexivity ].
      + split; [ intros Hb Δ1 κ T Δ2 E; destruct Δ1 as [| e1 Δ1]; cbn in E; injection E as E1 E2; [ discriminate | subst; exact (proj1 IH Hb _ _ _ _ eq_refl) ]
               | intros H; apply IH, Htl, H ].
      + split; [ intros Hb Δ1 κ T Δ2 E; destruct Δ1 as [| e1 Δ1]; cbn in E; injection E as E1 E2; [ discriminate | subst; exact (proj1 IH Hb _ _ _ _ eq_refl) ]
               | intros H; apply IH, Htl, H ].
      + split; [ intros Hb Δ1 κ T Δ2 E; destruct Δ1 as [| e1 Δ1]; cbn in E; injection E as E1 E2; [ discriminate | subst; exact (proj1 IH Hb _ _ _ _ eq_refl) ]
               | intros H; apply IH, Htl, H ].
  Qed.

  (** What [run_cmd_def] asks of a definition's kind and the frames'
      parameters, decided *)
  Definition level_premise_dec (κ : abs_kind) (Δ : ctx) : {κ = ak_level -> level_sorted_parameters Δ} + {~ (κ = ak_level -> level_sorted_parameters Δ)}.
  Proof.
    destruct (abs_kind_eq_dec κ ak_level) as [-> | Hn]; [| left; intros E; contradiction ].
    destruct (level_sorted_parameters_b Δ) eqn:E;
      [ left; intros _; apply level_sorted_parameters_b_spec, E
      | right; intros H; apply level_sorted_parameters_b_spec in H; [ congruence | reflexivity ] ].
  Defined.

  (** The level premise, at the fast telescope, read at the Core one *)
  Lemma level_premise_at {fs κ} : (κ = ak_level -> level_sorted_parameters (fs_tele fs)) ->
      κ = ak_level -> level_sorted_parameters (gs_tele (decode_stack fs)).
  Proof. rewrite fs_tele_dec; exact (fun h => h). Qed.

  (** A type of the sort of one kind, at another equal to it *)
  Definition kind_cast {Θ Ξ Γ A κ' κ} {i : nat} (E : κ' = κ) (HA : Θ ⍮ Ξ ⍮ Γ ⊢ A : abs_kind_sort κ' Typeω@i) :
      Θ ⍮ Ξ ⍮ Γ ⊢ A : abs_kind_sort κ Typeω@i :=
    eq_rect κ' (fun k => Θ ⍮ Ξ ⍮ Γ ⊢ A : abs_kind_sort k Typeω@i) HA κ E.

  (** A context, extended by nothing *)
  Lemma ctx_app_nil {Θ Ξ Γ} : ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ ⍮ Ξ ⍮ Γ ++ ⋅.
  Proof. rewrite app_nil_r; exact (fun h => h). Qed.

  (** The name a command as written declares, if any *)
  Definition surface_cmd_name (c : surface_cmd) : option string :=
    match c with
    | surface_cmd_def x _ _ _ _ | surface_cmd_mod x _ _ _ | surface_cmd_alias x _ _ _
    | surface_cmd_inductive_alias x _ _ _ | surface_cmd_record_alias x _ _ _ | surface_cmd_record x _ _ _ _ _ => Some x
    | _ => None
    end.

  (** *** Messages *)

  (** Parameters of [x], well formed, one of which is of no evaluated
      kind: a proposition, say [h : n = 0] in [module M (n : ℕ) (h : n = 0)
      ≔ …], which a module may not take. *)
  Definition run_error_param_prop (x : string) : run_error :=
    run_error_msg ("a parameter of " ++ x ++ " is a proposition: the parameters of a module must be types of a universe or of levels").

  (** A module read with a member of a type of levels over a parameter of
      a universe ([levels_abstractable]) *)
  Definition run_error_levels (x : string) : run_error :=
    run_error_msg (x ++ " reads a level computed from a parameter that is not a level").

  (** The last name of the path of an inductive type. *)
  Definition ind_short (p : qname) : string := List.last (q_chain p) EmptyString.

  (** A binding that another one meets. *)
  Definition bound_msg (B : builtins) : string :=
    match builtins_nat B with
    | Some p0 => "the natural numbers are bound already, to " ++ ind_short p0
    | None => "the natural numbers are bound already"
    end.

  Definition nat_shape_msg (p : qname) : string :=
    ind_short p ++ " is not shaped as the natural numbers: it must have no parameter, " ++
    "one constructor without arguments and one with a single recursive argument".

  (** The path a command names a module by, as written, if it is one. *)
  Definition written_name (E : modexp) (p : qname) : qname :=
    match mod_qname E with Some pq => pq | None => p end.

  (** A builtin bound to something that is no inductive type. *)
  Definition builtin_target_error (E : modexp) : run_error :=
    match mod_qname E with
    | Some pq => run_error_not_ind pq
    | None => run_error_msg "the natural numbers must be bound to an inductive type, named by its path"
    end.

  (** An inductive alias whose module expression names no inductive type. *)
  Definition alias_target_error (x : string) (E : modexp) : run_error :=
    match mod_qname (fst (me_unapps E)) with
    | Some pq => run_error_not_ind pq
    | None => run_error_msg ("inductive alias " ++ x ++ " must name an inductive type by its path")
    end.

  (** An inductive alias whose module expression is ill-formed although the
      module it applies is not: an inductive type applied past its uniform
      parameters is named as such. *)
  Definition alias_wf_error (x : string) (F : FCtx) (Hg : ⊢ᵍ fc_deps F ⍮ fc_stack F) (Γ : ctx) (E : modexp)
      (Hh : fc_deps F ⍮ fc_stack F ⍮ Γ ⊢ᵐ fst (me_unapps E) ≈ fst (me_unapps E)) : run_error :=
    match mdenote_impl F Hg Γ (fst (me_unapps E)) (mdenote_order_of_wf _ _ Hg _ _ _ Hh) with
    | inleft (exist _ (fmdesc_dm Θ0 _ M _) _) =>
        (* a type former: its term part is the group's constant applied to
           the arguments given so far *)
        match app_head M with
        | a_ind p _ =>
            match fc_ind F p with
            | Some Dp =>
                if Nat.ltb (ind_nu Dp) (List.length (app_args M) + (List.length (snd (me_unapps E)) - List.length Θ0))
                then run_error_msg ("inductive alias " ++ x ++ ": more arguments than uniform parameters of " ++ ind_short p)
                else run_error_msg ("ill-formed inductive alias " ++ x)
            | None => run_error_msg ("ill-formed inductive alias " ++ x)
            end
        | _ => run_error_msg ("ill-formed inductive alias " ++ x)
        end
    | _ => run_error_msg ("ill-formed inductive alias " ++ x)
    end.

  (** A record alias whose module expression names no record type. *)
  Definition recalias_target_error (x : string) : run_error :=
    run_error_msg ("record alias " ++ x ++ " must name a record type").

  (** The message of a function with no member. *)
  Definition mdef_why_error (f : string) (e : mdef_why) : run_error :=
    match e with
    | mdef_why_scrut_untyped => run_error_msg ("the scrutinee's type of " ++ f ++ " is not a type")
    | mdef_why_member_untyped _ => run_error_msg ("a member of the group is not a type at the uniform parameters of " ++ f)
    | mdef_why_no_member _ => run_error_msg ("the scrutinee's type of " ++ f ++ " is that of no member of the group")
    | mdef_why_nparams n m => run_error_mdef_nparams f m n
    end.

  (** The message of a definition not filed. *)
  Definition mdefs_why_error (e : mdefs_why) : run_error :=
    match e with
    | mdefs_why_dup x => run_error_msg (x ++ " is already declared")
    | mdefs_why_untyped_type x Ξ A => run_error_def_typ x Ξ A
    | mdefs_why_untyped x Ξ A M => run_error_def x Ξ A M
    end.

  (** The message of functions with no group. *)
  Definition mdef_group_why_error (e : mdef_group_why) : run_error :=
    match e with
    | mdef_group_why_function f w => mdef_why_error f w
    | mdef_group_why_not_inductive f => run_error_msg ("the scrutinee's type of " ++ f ++ " is not an inductive type")
    | mdef_group_why_no_group pq => run_error_not_ind pq
    | mdef_group_why_view f => run_error_msg ("the scrutinee's type of " ++ f ++ " is a view, not a declared type")
    | mdef_group_why_uparams f =>
        run_error_msg ("the uniform parameters of the scrutinee's type of " ++ f ++ " depend on its non-uniform parameters")
    | mdef_group_why_count n m => run_error_mdef_count n m
    | mdef_group_why_shared => run_error_msg "two functions of a mutual definition are for the same member"
    end.

  (** The rejection of an argument the classification does not accept. *)
  Definition classify_msg (x c y : string) (r : nat) : string :=
    match r with
    | 0 => "the argument " ++ y ++ " of " ++ c ++ " depends on a recursive argument"
    | 2 => x ++ " occurs in the domain of a function in the argument " ++ y ++ " of " ++ c ++
             ", which is not strictly positive"
    | 3 => x ++ " is not applied to its uniform parameters as declared in the argument " ++ y ++ " of " ++ c
    | 4 => x ++ " occurs in the argument " ++ y ++ " of " ++ c ++
             " under a head that does not compute (an opaque definition, an axiom or a parameter)"
    | _ => x ++ " occurs in a non-positive position in the argument " ++ y ++ " of " ++ c
    end.

  (** The first name of [xs] that occurs again after it. *)
  Fixpoint first_dup (xs : list string) : option string :=
    match xs with
    | nil => None
    | y :: xs' => if List.existsb (String.eqb y) xs' then Some y else first_dup xs'
    end.

  (** Why a record declaration is rejected. *)
  Definition record_why_error (x : string) (fs : list (string * abs_kind * typ)) (e : record_why) : run_error :=
    match e with
    | rw_params => run_error_msg ("parameters of record " ++ x ++ " that are not assumptions")
    | rw_mvc => run_error_msg ("a type of record " ++ x ++ " mentions a module variable")
    | rw_sort => run_error_msg ("the sort of record " ++ x ++ " is not a universe")
    | rw_dup =>
        run_error_msg ("duplicate field name " ++ match first_dup (List.map (fun f => fst (fst f)) fs) with Some f => f | None => "" end
                ++ " in record " ++ x)
    | rw_field_kind => run_error_msg ("a field of record " ++ x ++ " is a level: a field is never a level")
    | rw_field f => run_error_msg ("the type of field " ++ f ++ " of record " ++ x ++ " is not a type of its sort")
    | rw_param_level => run_error_param_prop ("record " ++ x)
    end.

  (** An open's target, checked in the context the error reader builds. *)
  Definition mod_check (F : FCtx) (Hg : ⊢ᵍ fc_deps F ⍮ fc_stack F) (Γ : ctx) (E : modexp)
      : option (fc_deps F ⍮ fc_stack F ⍮ Γ ⊢ᵐ E ≈ E) :=
    match check_ctx F (lvd _ _) Hg Γ with
    | left HΓ =>
        match check_modexp F (lvd _ _) Γ HΓ E with
        | left HE => Some HE
        | right _ => None
        end
    | right _ => None
    end.

  (** The skeleton of the frames of a fast context: [frame_skeleton] *)
  Definition fc_skeleton (F : FCtx) : skeleton := map (fun _ => None) (fc_tele F).

  (** The error of a rejected core command: the first open of it that
      generates nothing, if any, otherwise the error found. *)
  Definition open_error (F : FCtx) (Hg : ⊢ᵍ fc_deps F ⍮ fc_stack F) (c : core_cmd) (e : run_error) : run_error :=
    match cmd_open_error F Hg (mod_check F Hg) (fc_skeleton F) c with
    | Some e' => run_error_import e'
    | None => e
    end.

  (** The first mismatch of a block's branches, named [cs], against the
      constructors of the member [Mk]: a name of no constructor, then a
      constructor without a branch or with two, then the order of the
      branches ([branch_check], the binders not read). *)
  Definition branch_names_check (Mk : imember) (cs : list string) : option run_error :=
    first_some (first_some
      (List.fold_right (fun c r => match ind_con Mk c with Some _ => r | None => Some (run_error_branch_unknown c) end) None cs)
      (fun _ => List.fold_right (fun cg r =>
                  match List.length (List.filter (String.eqb (fst cg)) cs) with
                  | 0 => Some (run_error_branch_missing (fst cg))
                  | 1 => r
                  | _ => Some (run_error_branch_dup (fst cg))
                  end) None (im_cons Mk)))
      (fun _ => if strings_eqb cs (List.map fst (im_cons Mk)) then None
                else Some (run_error_branch_order (List.map fst (im_cons Mk)))).

  (** The first block of an eliminator of the group [D], its branches named
      [css], whose branches do not match its member's constructors, the
      blocks taken in member order. *)
  Definition blocks_branch_blame (D : ind_decl) (css : list (list string)) : option run_error :=
    List.fold_right (fun mcs r => first_some (branch_names_check (fst mcs) (snd mcs)) (fun _ => r)) None
      (List.combine (ind_block_members D) css).

  (** Blocks whose branches are named [css], for a message: what the
      printer reads of them is the names. *)
  Definition named_blocks (css : list (list string)) : list eblock :=
    List.map (fun cs => eb_mk 0 a_prop a_prop (List.map (fun c => (c, 0, a_prop)) cs)) css.

  (** Why a command declaring [ox] has no fill, as a run error: a term's
      context is given past the stack's telescope.  An eliminator no
      reading of which fits its blocks is blamed on its scrutinee's own
      group [pc]: on its blocks, too few, too many or out of member order
      ([elim_blocks_check]), else on a block's branches
      ([blocks_branch_blame]), else as fitting no group. *)
  Definition fill_run_error (F : FCtx) (Hg : ⊢ᵍ fc_deps F ⍮ fc_stack F) (ox : option string) (e : fill_failure) : run_error :=
    let fs := fc_frames F in
    let past (Γ : ctx) := List.firstn (List.length Γ - List.length (fc_tele F)) Γ in
    match e with
    | fill_failure_no_type y Γ M => run_error_access_no_type fs ox (past Γ) M y
    | fill_failure_not_record y Γ M W => run_error_access_not_record fs ox (past Γ) M (nf_to_exp W) y
    | fill_failure_private qd x => run_error_private qd x
    | fill_failure_mdef_group e' => mdef_group_why_error e'
    | fill_failure_literal e' => run_error_lit e'
    | fill_failure_elim_scrutinee Γ M oW => run_error_elim_scrutinee fs ox (past Γ) M (option_map nf_to_exp oW)
    | fill_failure_elim_none Γ pc k Rs m css M =>
        match fc_ind F pc with
        | Some D =>
            match elim_blocks_check F (past Γ) (a_elim ak_relevant pc (List.firstn (ind_nu D) (List.map nf_to_exp Rs)) m (named_blocks css) M) with
            | Some e' => e'
            | None =>
                match blocks_branch_blame D css with
                | Some e' => e'
                | None => run_error_elim_no_group fs (past Γ) (a_elim ak_relevant pc nil m (named_blocks css) M)
                end
            end
        | None => run_error_elim_no_group fs (past Γ) (a_elim ak_relevant pc nil m (named_blocks css) M)
        end
    | fill_failure_elim_ambiguous Γ E rs => run_error_elim_ambiguous fs (past Γ) E rs
    | fill_failure_body Γ Φ =>
        match open_expand_body F Hg (mod_check F Hg) (List.map centry_skeleton Γ) Φ with
        | open_failure e' => run_error_import e'
        | open_success _ => run_error_msg "a local open of a body opens no module"
        end
    | fill_failure_message s => run_error_msg s
    end.

  (** Whether a fill failure is final: a member selected through a term
      that infers no type, or no record type, or is private; a mutual
      definition's functions with no group; a literal with no binding; an
      eliminator whose scrutinee's type is no inductive type, or with no
      reading or several.  Any other failure is of a definition's type or
      an [eval]'s term, which [fill_blame] blames as the check of the
      filled part does, or of a command that does not run anyway. *)
  Definition fill_failure_final (e : fill_failure) : bool :=
    match e with
    | fill_failure_no_type y _ _ | fill_failure_not_record y _ _ _ => negb (String.eqb y "")
    | fill_failure_private _ _ | fill_failure_mdef_group _ | fill_failure_literal _ => true
    | fill_failure_elim_scrutinee _ _ (Some _) | fill_failure_elim_none _ _ _ _ _ _ _
    | fill_failure_elim_ambiguous _ _ _ | fill_failure_body _ _ => true
    | fill_failure_elim_scrutinee _ _ None | fill_failure_message _ => false
    end.

  (** Why a command as written has no fill: a final failure as it is; the
      type of a definition, or the term of an [eval], that has no sort or
      no type, blamed as its check blames it. *)
  Definition fill_blame (F : FCtx) (B : builtins) (Hg : ⊢ᵍ fc_deps F ⍮ fc_stack F) (HΓ : ⊢ fc_deps F ⍮ fc_stack F ⍮ fc_tele F)
      (c : surface_cmd) (e : fill_failure) : run_error :=
    let fs := fc_frames F in
    let other := fill_run_error F Hg (surface_cmd_name c) e in
    if fill_failure_final e then other else
    match c with
    | surface_cmd_def x _ _ A _ =>
        match fill_exp_fn F B (lvd _ _) Hg (fc_tele F) A with
        | fill_ok A' =>
            match check_type F (lvd _ _) (fc_tele F) HΓ A' with
            | inright _ => blame_error fs (find_level_blame F (lvd _ _) (fc_tele F) HΓ A')
                             (mod_error F (Some x) (A' :: nil) (run_error_def_typ x fs A'))
            | inleft _ => other
            end
        | fill_error _ => other
        end
    | surface_cmd_eval M A =>
        match fill_exp_fn F B (lvd _ _) Hg (fc_tele F) M with
        | fill_ok M' =>
            if is_surface_hole A then
              mod_error F None (M' :: nil) (field_error F None (lvd _ _) HΓ M' (run_error_eval_infer fs M'))
            else
              match fill_exp_fn F B (lvd _ _) Hg (fc_tele F) A with
              | fill_ok A' =>
                  match check_type F (lvd _ _) (fc_tele F) HΓ A' with
                  | inright _ => blame_error fs (find_level_blame F (lvd _ _) (fc_tele F) HΓ A')
                                   (mod_error F None (A' :: nil) (run_error_eval_typ fs M' A'))
                  | inleft _ => other
                  end
              | fill_error _ => other
              end
        | fill_error _ => other
        end
    | _ => other
    end.

  (** *** Definitions, Modules and Aliases *)

  (** A definition or an axiom, at the kind its command carries: the type
      of the sort of the kind, the frames' parameters types of levels when
      it is a level, the body at the type. *)
  Equations def_step (ch : list path) (s : funits) (K : unit_closure_map) (D : list path) (B : builtins) (fs : fstack)
    (x : string) (b pv : bool) (κ : abs_kind) (A : typ) (oM : option exp) (H : pre ch s K D fs) :
    frames_result ch s K D B fs (core_cmd_def x b pv κ A oM) :=
  | ch, s, K, D, B, fs, x, b, pv, κ, A, oM, H with fs_fresh_sum x fs (pre_frames _ _ _ _ _ H) (pre_canon H) => {
    | right _ => run_failure (run_error_msg (x ++ " is already declared"))
    | left Hfr with check_type (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) A => {
      | inright _ => run_failure (blame_error fs (find_level_blame (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) A)
                            (mod_error (cmd_F B H) (Some x) (A :: nil) (run_error_def_typ x fs A)))
      | inleft (existT _ κ' (exist _ i HA')) with abs_kind_eq_dec κ' κ => {
        | right _ => run_failure (run_error_msg ("the type of " ++ x ++ " is not of the sort its kind says"))
        | left Eκ with oM => {
          | None with abs_kind_eq_dec κ ak_level => {
            | left _ => run_failure (run_error_msg ("the axiom " ++ x ++ " is a level: a level is never assumed"))
            | right Hk =>
                run_success (exist _ _ (add_post_translate H (f_equal translate_entry (fs_axiom_dec b pv κ fs A))
                                          (axiom_ok Hfr (cmd_exp B H nil A _ (kind_cast Eκ HA')) Hk))) }
          | Some M with level_premise_dec κ (fs_tele fs) => {
            | right _ => run_failure (run_error_levels x)
            | left Hlv
                with check_exp_typed (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) A
                       (type_of_check_type (cmd_F B H) _ _ _ _ (kind_cast Eκ HA')) M => {
              | left HM =>
                  let (e, He) := def_entry_rep B H b pv κ i A M (kind_cast Eκ HA') HM in
                  run_success (exist _ (fs_add x e fs)
                                 (add_post H (erep_drop _ _ _ _ He) (erep_values _ _ _ _ He)
                                    (def_ok Hfr (cmd_exp B H nil A _ (kind_cast Eκ HA')) (level_premise_at Hlv) (cmd_exp B H nil M A HM))))
              | right _ =>
                  run_failure (mod_error (cmd_F B H) (Some x) (M :: nil)
                                 (field_error (cmd_F B H) (Some x) (lvd _ _) (pre_ctx_f B H) M (run_error_def x fs A M))) } } } } } }.

  (** A frame opened, empty: the frames are still those of their
      reading. *)
  Lemma push_frames : forall fs f, fstack_drop fs = fs_of (decode_stack fs) -> ff_body f = ft_empty ->
      fstack_drop (f :: fs) = fs_of (decode_stack (f :: fs)).
  Proof.
    intros fs [mp Kf Δ t] Hf Ht; cbn [ff_body] in Ht; subst t.
    change (decode_stack (mk_fframe mp Kf Δ ft_empty :: fs)) with (decode_frame (mk_fframe mp Kf Δ ft_empty) :: decode_stack fs).
    change (fs_of (decode_frame (mk_fframe mp Kf Δ ft_empty) :: decode_stack fs))
      with (translate_frame (decode_frame (mk_fframe mp Kf Δ ft_empty)) :: fs_of (decode_stack fs)).
    change (fstack_drop (mk_fframe mp Kf Δ ft_empty :: fs)) with (fframe_drop (mk_fframe mp Kf Δ ft_empty) :: fstack_drop fs).
    rewrite <- Hf; reflexivity.
  Qed.

  (** An empty frame opened, where the invariant holds *)
  Lemma pre_cons {ch s K D fs f} : pre ch s K D fs -> ff_body f = ft_empty ->
      (exists ΘR, unit_invariant ch (decode_units s) K D ΘR (decode_stack (f :: fs))) -> pre ch s K D (f :: fs).
  Proof.
    intros H Ht Hl; constructor;
      [ exact Hl | exact (pre_units _ _ _ _ _ H) | exact (pre_visible _ _ _ _ _ H) | exact (push_frames _ _ (pre_frames _ _ _ _ _ H) Ht)
      | exact (pre_unit_values _ _ _ _ _ H) | exact (frames_values_push _ _ _ (pre_frame_values _ _ _ _ _ H) Ht) ].
  Qed.

  (** A module's frame opened, at the path [x] in the innermost frame *)
  Lemma push_mod_post {ch s K D B fs x pv Δ l} (H : pre ch s K D fs) : all_assumptions Δ -> gs_fresh x (decode_stack fs) ->
      ⊢ gds_restrict D (decode_units s) ⍮ decode_stack fs ⍮ Δ ++ gs_tele (decode_stack fs) ->
      params_evaluated (gds_restrict D (decode_units s)) (decode_stack fs) (gs_tele (decode_stack fs)) Δ l ->
      post_cmd ch (decode_units s) K D B (decode_stack fs) (core_cmd_mod_open x pv Δ)
        (mk_run_state_core (decode_units s) K D B (decode_stack (fs_push (qname_in (fs_path fs) x) Δ fs))) /\
      frames_rep (gds_restrict D (decode_units s)) (fs_push (qname_in (fs_path fs) x) Δ fs).
  Proof.
    intros Htel Hfr HΔ HPr; rewrite <- fs_path_dec; split; [ exact (mod_open_ok Htel Hfr HΔ HPr) |].
    unfold fs_push; constructor;
      [ apply push_frames; [ exact (pre_frames _ _ _ _ _ H) | reflexivity ]
      | apply frames_values_push; [ exact (pre_frame_values _ _ _ _ _ H) | reflexivity ] ].
  Qed.

  (** A module's frame opened, its parameters checked as
      [run_cmd_mod_open] checks them *)
  Equations mod_open_step (ch : list path) (s : funits) (K : unit_closure_map) (D : list path) (B : builtins) (fs : fstack)
    (x : string) (pv : bool) (Δ : ctx) (H : pre ch s K D fs) : frames_result ch s K D B fs (core_cmd_mod_open x pv Δ) :=
  | ch, s, K, D, B, fs, x, pv, Δ, H with all_assumptions_dec Δ => {
    | right _ => run_failure (run_error_msg ("parameters of module " ++ x ++ " that are not assumptions"))
    | left Htel with check_ctx (cmd_F B H) (lvd _ _) (pre_gctx_f B H) (Δ ++ fc_tele (cmd_F B H)) => {
      | right _ =>
          run_failure (tele_blame_error fs (find_tele_blame (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) Δ)
                         (run_error_msg ("ill-formed parameters of module " ++ x)))
      | left HΔ with params_evaluated_dec (cmd_F B H) (pre_gctx_f B H) (fc_tele (cmd_F B H)) Δ => {
        | inright _ => run_failure (run_error_param_prop x)
        | inleft (exist _ l HPr) with fs_fresh_sum x fs (pre_frames _ _ _ _ _ H) (pre_canon H) => {
          | right _ => run_failure (run_error_msg (x ++ " is already declared"))
          | left Hfr =>
              run_success (exist _ _ (push_mod_post H Htel Hfr (cmd_ctx B H Δ HΔ) (cmd_params_evaluated B H Δ l HPr))) } } } }.

  (** *** Frames Closed *)

  (** The innermost frame's body is the translation of its reading. *)
  Lemma frame_body_translate : forall f fs2, fstack_drop (f :: fs2) = fs_of (decode_stack (f :: fs2)) ->
      ftrie_drop (ff_body f) = translate_mod (decode_mod (ff_body f)).
  Proof.
    intros [mp Kf Δ t] fs2 Hf; change (fframe_drop (mk_fframe mp Kf Δ t) :: fstack_drop fs2 = fs_of (decode_stack (mk_fframe mp Kf Δ t :: fs2))) in Hf.
    injection Hf as Ht _; exact Ht.
  Qed.

  (** And the frames below it are those of their reading. *)
  Lemma frames_tail_translate : forall f fs2, fstack_drop (f :: fs2) = fs_of (decode_stack (f :: fs2)) ->
      fstack_drop fs2 = fs_of (decode_stack fs2).
  Proof.
    intros [mp Kf Δ t] fs2 Hf; change (fframe_drop (mk_fframe mp Kf Δ t) :: fstack_drop fs2 = fs_of (decode_stack (mk_fframe mp Kf Δ t :: fs2))) in Hf.
    injection Hf as _ Ht; exact Ht.
  Qed.

  (** The frames below the innermost one, of a state the invariant holds
      at, are well formed and canonical. *)
  Lemma pre_tail_wf {ch s K D f fs2} : pre ch s K D (f :: fs2) -> ⊢ᵍ gds_restrict D (decode_units s) ⍮ decode_stack fs2.
  Proof.
    intros H; pose proof (pre_gctx (pre_unit_invariant _ _ _ _ _ H)) as Hw.
    change (decode_stack (f :: fs2)) with (decode_frame f :: decode_stack fs2) in Hw.
    destruct f as [mp Kf Δ t]; exact (proj1 (wf_gstack_cons_inv _ _ _ _ _ Hw)).
  Qed.

  Lemma pre_tail_canon {ch s K D f fs2} : pre ch s K D (f :: fs2) -> canon_stack (decode_stack fs2).
  Proof. intros H; exact (proj2 (canon_of_wf _ _ (pre_tail_wf H))). Qed.

  (** The fast entry a frame closed is filed as, in the frame below *)
  Definition close_fentry (pv : bool) (f : fframe) : fentry :=
    match ff_kind f with
    | fk_module => fe_mod pv (fu_mk (ff_params f) (fmd_body (ff_body f)))
    | fk_ind pq k Dd => fe_ind pv pq k Dd (ff_body f)
    | fk_record R => fe_record pv (ff_path f) R (ff_body f)
    end.

  (** It translates the entry [frame_entry] files. *)
  Lemma close_fentry_drop : forall pv f, ftrie_drop (ff_body f) = translate_mod (decode_mod (ff_body f)) ->
      fentry_drop (close_fentry pv f) = translate_entry (frame_entry pv (ff_path f) (ff_kind f) (ff_params f) (decode_mod (ff_body f))).
  Proof.
    intros pv [mp Kf Δ t] Ht; cbn [ff_path ff_kind ff_params ff_body] in *; unfold close_fentry; cbn [ff_path ff_kind ff_params ff_body].
    destruct Kf; cbn [frame_entry translate_entry translate_unit fentry_drop funit_drop fmoddef_drop]; rewrite Ht; reflexivity.
  Qed.

  (** Its values are those of the frame's body. *)
  Lemma close_fentry_values : forall pv f Θ Ξ, ftrie_values_ok Θ Ξ (ff_body f) -> fentry_values_ok Θ Ξ (close_fentry pv f).
  Proof. intros pv [mp Kf Δ t] Θ Ξ Ht; unfold close_fentry; destruct Kf; exact Ht. Qed.

  (** The innermost frame [f] closed into the entry [x] of the frame
      below, fast: the frames are those of their reading, with right
      values, once the Core stack with the entry is well formed. *)
  Lemma close_frames {ch s K D f fs2 x pv} : pre ch s K D (f :: fs2) ->
      gs_fresh x (decode_stack fs2) -> ff_path f = qname_in (gs_path (decode_stack fs2)) x ->
      kind_tele (ff_path f) (ff_kind f) (ff_params f) (gs_tele (decode_stack fs2)) ->
      ⊢ᵍ gds_restrict D (decode_units s) ⍮ gs_add x (frame_entry pv (ff_path f) (ff_kind f) (ff_params f) (decode_mod (ff_body f))) (decode_stack fs2) ->
      decode_stack (fs_add x (close_fentry pv f) fs2) = gs_add x (frame_entry pv (ff_path f) (ff_kind f) (ff_params f) (decode_mod (ff_body f))) (decode_stack fs2) /\
      frames_rep (gds_restrict D (decode_units s)) (fs_add x (close_fentry pv f) fs2).
  Proof.
    intros H Hfr Hp HK Hw.
    pose proof (pre_frames _ _ _ _ _ H) as Hf.
    pose proof (frames_tail_translate _ _ Hf) as Hf2.
    pose proof (close_fentry_drop pv f (frame_body_translate _ _ Hf)) as Hd.
    pose proof (decode_stack_add _ _ _ _ Hf2 Hd (proj2 (canon_of_wf _ _ Hw))) as Ed.
    split; [ exact Ed |]; constructor; [ rewrite Ed; exact (fs_add_drop_of _ _ _ _ Hf2 Hd) |].
    pose proof (pre_gctx (pre_unit_invariant _ _ _ _ _ H)) as HΞf.
    pose proof (pre_tail_wf H) as HΞ0.
    destruct (pre_frame_values _ _ _ _ _ H) as [Hft Hfs].
    exact (frames_values_close _ _ _ f x pv _ (gds_sub_refl _) HΞ0 HΞf Hfs Hft HΞ0 Hfr Hw Hp HK
             (fun Θ0 Ξ0 => close_fentry_values pv f Θ0 Ξ0) Ed).
  Qed.

  (** A record frame's own parameters are those of its record after a
      value of it, as [kind_tele] has them. *)
  Lemma record_frame_kind_tele {Θ Ξ mp R Δ Φ} : ⊢ᵍ Θ ⍮ (mp, fk_record R, gu_body Δ Φ) :: Ξ -> kind_tele mp (fk_record R) Δ (gs_tele Ξ).
  Proof.
    intros Hw; destruct (wf_gstack_cons_inv _ _ _ _ _ Hw) as (_ & HU & _).
    pose proof (wf_gunit_mod _ _ _ _ _ HU) as HΦ; cbn [gu_params gu_mod] in HΦ.
    destruct (wf_gmod_record_params _ _ _ _ _ _ HΦ R eq_refl) as (Δr & -> & HP & _).
    exists Δr; split; [ reflexivity | exact HP ].
  Qed.

  (** A module's frame on top closed, fast *)
  Lemma close_mod_res {ch s K D B f fs2 x pv} (H : pre ch s K D (f :: fs2)) (Hfr : gs_fresh x (decode_stack fs2))
      (Hp : ff_path f = qname_in (fs_path fs2) x) (Ek : ff_kind f = fk_module) :
      post_cmd ch (decode_units s) K D B (decode_stack (f :: fs2)) (core_cmd_close x pv)
        (mk_run_state_core (decode_units s) K D B (decode_stack (fs_add x (close_fentry pv f) fs2))) /\
      frames_rep (gds_restrict D (decode_units s)) (fs_add x (close_fentry pv f) fs2).
  Proof.
    rewrite <- fs_path_dec in Hp.
    assert (Hpost : post_cmd ch (decode_units s) K D B (decode_stack (f :: fs2)) (core_cmd_close x pv)
                      (mk_run_state_core (decode_units s) K D B
                         (gs_add x (frame_entry pv (ff_path f) (ff_kind f) (ff_params f) (decode_mod (ff_body f))) (decode_stack fs2)))).
    { change (decode_stack (f :: fs2)) with (decode_frame f :: decode_stack fs2).
      destruct f as [mp Kf Δ t]; cbn [ff_path ff_kind ff_params ff_body decode_frame] in *; subst mp Kf.
      exact (close_mod_ok Hfr). }
    destruct (cmd_post_pre (pre_unit_invariant _ _ _ _ _ H) Hpost) as [ΘR Hli].
    destruct (close_frames (pv := pv) H Hfr Hp ltac:(rewrite Ek; exact I) (unit_invariant_restrict_gctx Hli)) as [Ed Hrep].
    rewrite Ed; split; [ exact Hpost | exact Hrep ].
  Qed.

  (** A record's frame on top closed, fast *)
  Lemma close_record_res {ch s K D B f fs2 x pv R} (H : pre ch s K D (f :: fs2)) (Hfr : gs_fresh x (decode_stack fs2))
      (Hp : ff_path f = qname_in (fs_path fs2) x) (Ek : ff_kind f = fk_record R) :
      post_cmd ch (decode_units s) K D B (decode_stack (f :: fs2)) (core_cmd_close x pv)
        (mk_run_state_core (decode_units s) K D B (decode_stack (fs_add x (close_fentry pv f) fs2))) /\
      frames_rep (gds_restrict D (decode_units s)) (fs_add x (close_fentry pv f) fs2).
  Proof.
    rewrite <- fs_path_dec in Hp.
    assert (Hpost : post_cmd ch (decode_units s) K D B (decode_stack (f :: fs2)) (core_cmd_close x pv)
                      (mk_run_state_core (decode_units s) K D B
                         (gs_add x (frame_entry pv (ff_path f) (ff_kind f) (ff_params f) (decode_mod (ff_body f))) (decode_stack fs2)))).
    { change (decode_stack (f :: fs2)) with (decode_frame f :: decode_stack fs2).
      destruct f as [mp Kf Δ t]; cbn [ff_path ff_kind ff_params ff_body decode_frame] in *; subst mp Kf.
      exact (close_record_ok Hfr). }
    destruct (cmd_post_pre (pre_unit_invariant _ _ _ _ _ H) Hpost) as [ΘR Hli].
    assert (HK : kind_tele (ff_path f) (ff_kind f) (ff_params f) (gs_tele (decode_stack fs2))).
    { pose proof (pre_gctx (pre_unit_invariant _ _ _ _ _ H)) as Hw.
      change (decode_stack (f :: fs2)) with (decode_frame f :: decode_stack fs2) in Hw.
      destruct f as [mp Kf Δ t]; cbn [ff_path ff_kind ff_params ff_body decode_frame] in *; subst Kf.
      exact (record_frame_kind_tele Hw). }
    destruct (close_frames (pv := pv) H Hfr Hp HK (unit_invariant_restrict_gctx Hli)) as [Ed Hrep].
    rewrite Ed; split; [ exact Hpost | exact Hrep ].
  Qed.

  (** The frame on top closed, as [run_cmd_close_mod] or
      [run_cmd_close_record] files it; a member's frame is closed by its
      group's run only. *)
  Equations close_step (ch : list path) (s : funits) (K : unit_closure_map) (D : list path) (B : builtins) (fs : fstack)
    (x : string) (pv : bool) (H : pre ch s K D fs) : frames_result ch s K D B fs (core_cmd_close x pv) :=
  | ch, s, K, D, B, nil, x, pv, H => run_failure (run_error_msg ("internal error: " ++ x ++ " is closed with no frame open"))
  | ch, s, K, D, B, f :: fs2, x, pv, H
      with fs_fresh_sum x fs2 (frames_tail_translate _ _ (pre_frames _ _ _ _ _ H)) (pre_tail_canon H) => {
    | right _ => run_failure (run_error_msg (x ++ " is already declared"))
    | left Hfr with qname_eq_dec (ff_path f) (qname_in (fs_path fs2) x) => {
      | right _ => run_failure (run_error_msg ("internal error: " ++ x ++ " closes the frame of another module"))
      | left Hp with inspect (ff_kind f) => {
        | exist _ (fk_ind _ _ _) _ => run_failure (run_error_msg ("internal error: " ++ x ++ " closes the frame of a member"))
        | exist _ fk_module Ek => run_success (exist _ _ (close_mod_res H Hfr Hp Ek))
        | exist _ (fk_record R) Ek => run_success (exist _ _ (close_record_res H Hfr Hp Ek)) } } }.

  (** A module alias, checked premise by premise as [run_cmd_alias] has
      them. *)
  Equations alias_step (ch : list path) (s : funits) (K : unit_closure_map) (D : list path) (B : builtins) (fs : fstack)
    (x : string) (pv : bool) (Δ : ctx) (E : modexp) (H : pre ch s K D fs) : frames_result ch s K D B fs (core_cmd_alias x pv Δ E) :=
  | ch, s, K, D, B, fs, x, pv, Δ, E, H with all_assumptions_dec Δ => {
    | right _ => run_failure (run_error_msg ("parameters of module " ++ x ++ " that are not assumptions"))
    | left Htel with check_ext (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) Δ => {
      | right _ =>
          run_failure (tele_blame_error fs (find_tele_blame (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) Δ)
                         (run_error_msg ("ill-formed parameters of module " ++ x)))
      | left HΔ with params_evaluated_dec (cmd_F B H) (pre_gctx_f B H) (fc_tele (cmd_F B H)) Δ => {
        | inright _ => run_failure (run_error_param_prop x)
        | inleft (exist _ l HPr) with check_modexp (cmd_F B H) (lvd _ _) (Δ ++ fc_tele (cmd_F B H)) (ext_eq_ctx_left _ _ _ _ _ HΔ) E => {
          | right _ => run_failure (run_error_msg ("ill-formed module expression for module " ++ x))
          | left HE with lvd _ _ nil (Δ ++ fc_tele (cmd_F B H))%list E (ctx_app_nil (ext_eq_ctx_left _ _ _ _ _ HΔ)) => {
            | right _ => run_failure (run_error_levels ("module " ++ x))
            | left Hlv with fs_fresh_sum x fs (pre_frames _ _ _ _ _ H) (pre_canon H) => {
              | right _ => run_failure (run_error_msg (x ++ " is already declared"))
              | left Hfr =>
                  run_success (exist _ _ (add_post_translate H (e := translate_entry (ge_mod pv (gu_mk (Δ ++ fs_tele fs) (md_alias E))))
                                (eq_sym (f_equal (fun T => translate_entry (ge_mod pv (gu_mk (Δ ++ T) (md_alias E)))) (fs_tele_dec fs)))
                                (alias_ok Htel (cmd_ext B H Δ HΔ) (cmd_modexp B H Δ E HE) (cmd_params_evaluated B H Δ l HPr)
                                   (cmd_levels_abstractable B H Δ E Hlv) Hfr))) } } } } } }.

  (** *** The Generated Entries of an Open *)

  (** An entry added on the way of an open's generated entries, fast:
      the invariant of the frames it ends with *)
  Lemma add_dec {ch s K D fs x E} {e : fentry} : pre ch s K D fs -> entry_rep (gds_restrict D (decode_units s)) (decode_stack fs) E e ->
      (exists ΘR, unit_invariant ch (decode_units s) K D ΘR (gs_add x E (decode_stack fs))) ->
      decode_stack (fs_add x e fs) = gs_add x E (decode_stack fs) /\ fstack_drop (fs_add x e fs) = fs_of (decode_stack (fs_add x e fs)).
  Proof.
    intros H He [ΘR Hli].
    apply (add_res (P := fun Ξ => Ξ = gs_add x E (decode_stack fs)) H (erep_drop _ _ _ _ He)); [ exact (proj2 (unit_invariant_canon Hli)) | reflexivity ].
  Qed.

  Lemma pre_add {ch s K D fs x E} {e : fentry} : pre ch s K D fs -> entry_rep (gds_restrict D (decode_units s)) (decode_stack fs) E e ->
      (exists ΘR, unit_invariant ch (decode_units s) K D ΘR (gs_add x E (decode_stack fs))) -> pre ch s K D (fs_add x e fs).
  Proof.
    intros H He Hl; destruct (add_dec H He Hl) as [Ed Ef].
    constructor; [ rewrite Ed; exact Hl | exact (pre_units _ _ _ _ _ H) | exact (pre_visible _ _ _ _ _ H) | exact Ef
                 | exact (pre_unit_values _ _ _ _ _ H) |].
    exact (frames_values_add_before _ _ _ _ E (pre_gctx (pre_unit_invariant _ _ _ _ _ H)) (pre_gctx Hl) (pre_frame_values _ _ _ _ _ H) Ed
             (erep_values _ _ _ _ He)).
  Qed.

  (** The entries an open generates, in order, as [gens_run] declares
      them: written by no one, so with no privacy check. *)
  Fixpoint gens_impl (ch : list path) (s : funits) (K : unit_closure_map) (D : list path) (B : builtins) (fs : fstack)
    (gs : list generated_item) (H : pre ch s K D fs) {struct gs} :
    run_result {fs' | post_gens ch (decode_units s) K D (decode_stack fs) gs (decode_stack fs') /\ frames_rep (gds_restrict D (decode_units s)) fs'} :=
    match gs as gs0 return run_result {fs' | post_gens ch (decode_units s) K D (decode_stack fs) gs0 (decode_stack fs') /\ frames_rep (gds_restrict D (decode_units s)) fs'} with
    | nil => run_success (exist _ fs (conj gens_nil_ok (mk_frames_rep _ _ (pre_frames _ _ _ _ _ H) (pre_frame_values _ _ _ _ _ H))))
    | generated_item_def d pv κ A M :: gs' =>
        match fs_fresh_sum d fs (pre_frames _ _ _ _ _ H) (pre_canon H) with
        | right _ => run_failure (run_error_msg (d ++ " is already declared"))
        | left Hfr =>
            (** the type, of the sort of the kind the item is tagged with *)
            match check_type (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) A with
            | inright _ => run_failure (run_error_def d fs A M)
            | inleft (existT _ κ' (exist _ i HA')) =>
                match abs_kind_eq_dec κ' κ with
                | right _ => run_failure (run_error_def d fs A M)
                | left Eκ =>
                    match level_premise_dec κ (fs_tele fs) with
                    | right _ => run_failure (run_error_levels d)
                    | left Hlv =>
                        match check_exp_typed (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) A
                                (type_of_check_type (cmd_F B H) _ _ _ _ (kind_cast Eκ HA')) M with
                        | right _ => run_failure (run_error_def d fs A M)
                        | left HM =>
                            let HA0 := cmd_exp B H nil A _ (kind_cast Eκ HA') in
                            let HM' := cmd_exp B H nil M A HM in
                            let Hl := gen_def_pre (pv := pv) (pre_unit_invariant _ _ _ _ _ H) Hfr HA0 (level_premise_at Hlv) HM' in
                            let (e0, He) := def_entry_rep B H true pv κ i A M (kind_cast Eκ HA') HM in
                            match gens_impl ch s K D B (fs_add d e0 fs) gs' (pre_add H He Hl) with
                            | run_failure e => run_failure e
                            | run_success (exist _ fs' (conj Hp Hf)) =>
                                run_success (exist _ fs' (conj (gen_def_ok Hfr HA0 (level_premise_at Hlv) HM'
                                                          (eq_ind _ (fun Ξ1 => post_gens ch (decode_units s) K D Ξ1 gs' (decode_stack fs')) Hp _
                                                             (proj1 (add_dec H He Hl)))) Hf))
                            end
                        end
                    end
                end
            end
        end
    | generated_item_alias d pv E :: gs' =>
        match fs_fresh_sum d fs (pre_frames _ _ _ _ _ H) (pre_canon H) with
        | right _ => run_failure (run_error_msg (d ++ " is already declared"))
        | left Hfr =>
            match check_modexp (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) E with
            | right _ => run_failure (run_error_msg ("ill-formed module expression for module " ++ d))
            | left HE =>
                match lvd _ _ nil (fc_tele (cmd_F B H)) E (ctx_app_nil (pre_ctx_f B H)) with
                | right _ => run_failure (run_error_levels ("module " ++ d))
                | left Hlv =>
                    let HE' := cmd_modexp B H nil E HE in
                    let Hlv' := cmd_levels_abstractable B H nil E Hlv in
                    let Hl := gen_alias_pre (pv := pv) (pre_unit_invariant _ _ _ _ _ H) Hfr HE' Hlv' in
                    let He := entry_rep_of_eq _ _ _ _ (eq_sym (f_equal (fun T => translate_entry (ge_mod pv (gu_mk T (md_alias E)))) (fs_tele_dec fs))) in
                    match gens_impl ch s K D B (fs_add d (translate_entry (ge_mod pv (gu_mk (fs_tele fs) (md_alias E)))) fs) gs' (pre_add H He Hl) with
                    | run_failure e => run_failure e
                    | run_success (exist _ fs' (conj Hp Hf)) =>
                        run_success (exist _ fs' (conj (gen_alias_ok Hfr HE' Hlv'
                                                  (eq_ind _ (fun Ξ1 => post_gens ch (decode_units s) K D Ξ1 gs' (decode_stack fs')) Hp _
                                                     (proj1 (add_dec H He Hl)))) Hf))
                    end
                end
            end
        end
    | generated_item_def_mod d pv A M E :: gs' =>
        match fs_fresh_sum d fs (pre_frames _ _ _ _ _ H) (pre_canon H) with
        | right _ => run_failure (run_error_msg (d ++ " is already declared"))
        | left Hfr =>
            match type_infer (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) M (type_infer_order_all M) with
            | inright _ => run_failure (run_error_msg ("ill-formed definition " ++ d))
            | inleft (exist _ W HW) =>
                match check_modexp (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) E with
                | right _ => run_failure (run_error_msg ("ill-formed module expression for module " ++ d))
                | left HE =>
                    match lvd _ _ nil (fc_tele (cmd_F B H)) E (ctx_app_nil (pre_ctx_f B H)) with
                    | right _ => run_failure (run_error_levels ("module " ++ d))
                    | left Hlv =>
                        match large_type_dec (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) (nf_to_exp W) with
                        | inright _ => run_failure (run_error_msg ("ill-formed definition " ++ d))
                        | inleft (exist _ i HWt) =>
                            let HW' := cmd_infer B H nil W M HW in
                            let HWt' := cmd_exp B H nil (nf_to_exp W) Typeω@i HWt in
                            let HM' := cmd_exp B H nil M (nf_to_exp W) (alg_type_infer_sound HW (pre_ctx_f B H)) in
                            let HE' := cmd_modexp B H nil E HE in
                            let Hlv' := cmd_levels_abstractable B H nil E Hlv in
                            let Hl := gen_dm_pre (pv := pv) (pre_unit_invariant _ _ _ _ _ H) Hfr HW' HWt' HM' HE' Hlv' in
                            let (e0, He) := dm_entry_rep B H pv nil i (nf_to_exp W) M E HWt (alg_type_infer_sound HW (pre_ctx_f B H)) in
                            match gens_impl ch s K D B (fs_add d e0 fs) gs' (pre_add H He Hl) with
                            | run_failure e => run_failure e
                            | run_success (exist _ fs' (conj Hp Hf)) =>
                                run_success (exist _ fs' (conj (gen_dm_ok (A := A) Hfr HW' HWt' HM' HE' Hlv'
                                                          (eq_ind _ (fun Ξ1 => post_gens ch (decode_units s) K D Ξ1 gs' (decode_stack fs')) Hp _
                                                             (proj1 (add_dec H He Hl)))) Hf))
                            end
                        end
                    end
                end
            end
        end
    end.

  (** *** Builtins, Aliases of Types, Mutual Definitions *)

  (** A builtin binding's post, as its result, at the fast state [s], [fs] *)
  Definition builtins_cmd_ok {ch s K D B fs c B'}
      (Hp : post_cmd ch (decode_units s) K D B (decode_stack fs) c (mk_run_state_core (decode_units s) K D B' (decode_stack fs))) :
      {B0 | post_cmd ch (decode_units s) K D B (decode_stack fs) c (mk_run_state_core (decode_units s) K D B0 (decode_stack fs))} := exist _ B' Hp.

  (** A builtin binding, checked premise by premise: the module expression
      read as a term, its inferred type, then its normal form. *)
  Equations builtin_step (ch : list path) (s : funits) (K : unit_closure_map) (D : list path) (B : builtins) (fs : fstack)
    (k : string) (E : modexp) (H : pre ch s K D fs) :
    run_result {B' | post_cmd ch (decode_units s) K D B (decode_stack fs) (core_cmd_builtin k E) (mk_run_state_core (decode_units s) K D B' (decode_stack fs))} :=
  | ch, s, K, D, B, fs, k, E, H with string_dec k nat_kind => {
    | right _ => run_failure (run_error_msg ("there is no builtin " ++ k))
    | left Hk with opt_case (modexp_as_term E) => {
      | inright _ => run_failure (builtin_target_error E)
      | inleft (exist _ M Ht)
          with type_infer (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) M (type_infer_order_all M) => {
        | inright _ => run_failure (builtin_target_error E)
        | inleft (exist _ W HW) with nf_is_universe_dec W => {
          | right _ => run_failure (builtin_target_error E)
          | left Hu
              with nbe_impl (cmd_F B H) (fc_tele (cmd_F B H)) M (nf_to_exp W)
                     (typed_nbe_order (alg_type_infer_sound HW (pre_ctx_f B H))) => {
            | exist _ (nf_indty p 0 nil) Hn with ind_lookup_f (cmd_F B H) p => {
              | exist _ None _ => run_failure (run_error_not_ind p)
              | exist _ (Some Dd) Hl with inspect (nat_shape Dd) => {
                | exist _ None _ => run_failure (run_error_msg (nat_shape_msg p))
                | exist _ (Some (z, sc)) Hs with inspect (is_nat_sort (ind_sort Dd)) => {
                  | exist _ false _ => run_failure (run_error_msg ("the natural numbers must be declared in Type@0, not " ++ ind_short p))
                  | exist _ true Ek with inspect (builtins_bind_nat B p) => {
                    | exist _ None _ => run_failure (run_error_msg (bound_msg B))
                    | exist _ (Some B') Hb =>
                        run_success (builtins_cmd_ok (eq_rect _ (fun k0 => post_cmd ch (decode_units s) K D B (decode_stack fs) (core_cmd_builtin k0 E)
                                                               (mk_run_state_core (decode_units s) K D B' (decode_stack fs)))
                                         (builtin_ok Ht (cmd_infer B H nil W M HW)
                                            (cmd_exp B H nil M (nf_to_exp W) (alg_type_infer_sound HW (pre_ctx_f B H))) Hu
                                            (cmd_nbe B H nil M (nf_to_exp W) _ Hn)
                                            (cmd_ind_lookup B H p _ Hl) Hs (proj1 (is_nat_sort_spec _) Ek) Hb) _ (eq_sym Hk))) } } } }
            | exist _ (nf_indty p _ _) _ => run_failure (run_error_msg (nat_shape_msg (written_name E p)))
            | exist _ _ _ => run_failure (builtin_target_error E) } } } } }.

  (** The module a well-formed module expression applies is well formed
      ([modexp_gen]). *)
  Lemma me_apps_head_wf : forall Θ0 Ξ0 Γ H0 L,
      Θ0 ⍮ Ξ0 ⍮ Γ ⊢ᵐ me_apps H0 L ≈ me_apps H0 L -> Θ0 ⍮ Ξ0 ⍮ Γ ⊢ᵐ H0 ≈ H0.
  Proof.
    intros *; induction L as [| N L IH] using List.rev_ind; intros HH; [ exact HH |].
    rewrite me_apps_snoc in HH; apply IH.
    exact (proj1 (proj1 (modexp_gen _ _ _ _ _ HH))).
  Qed.

  Lemma me_unapps_head_wf : forall Θ0 Ξ0 Γ E,
      Θ0 ⍮ Ξ0 ⍮ Γ ⊢ᵐ E ≈ E -> Θ0 ⍮ Ξ0 ⍮ Γ ⊢ᵐ fst (me_unapps E) ≈ fst (me_unapps E).
  Proof.
    intros * HE; rewrite (proj1 (me_unapps_spec E)) in HE; exact (me_apps_head_wf _ _ _ _ _ HE).
  Qed.

  (** An inductive alias, checked premise by premise: its parameters, the
      module it applies, the module expression, read as a term, its type
      inferred, and whether it is a type former of an inductive type. *)
  Equations indalias_step (ch : list path) (s : funits) (K : unit_closure_map) (D : list path) (B : builtins) (fs : fstack)
    (x : string) (pv : bool) (Δ : ctx) (E : modexp) (H : pre ch s K D fs) : frames_result ch s K D B fs (core_cmd_inductive_alias x pv Δ E) :=
  | ch, s, K, D, B, fs, x, pv, Δ, E, H with all_assumptions_dec Δ => {
    | right _ => run_failure (run_error_msg ("parameters of inductive alias " ++ x ++ " that are not assumptions"))
    | left Htel with check_ext (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) Δ => {
      | right _ => run_failure (run_error_msg ("ill-formed inductive alias " ++ x))
      | left HΔ with check_modexp (cmd_F B H) (lvd _ _) (Δ ++ fc_tele (cmd_F B H)) (ext_eq_ctx_left _ _ _ _ _ HΔ) (fst (me_unapps E)) => {
        | right _ => run_failure (alias_target_error x E)
        | left Hh with check_modexp (cmd_F B H) (lvd _ _) (Δ ++ fc_tele (cmd_F B H)) (ext_eq_ctx_left _ _ _ _ _ HΔ) E => {
          | right _ => run_failure (alias_wf_error x (cmd_F B H) (pre_gctx_f B H) _ E Hh)
          | left HE with opt_case (modexp_as_term E) => {
            | inright _ => run_failure (alias_target_error x E)
            | inleft (exist _ M Ht)
                with type_infer (cmd_F B H) (lvd _ _) (Δ ++ fc_tele (cmd_F B H)) (ext_eq_ctx_left _ _ _ _ _ HΔ) M (type_infer_order_all M) => {
              | inright _ => run_failure (alias_target_error x E)
              | inleft (exist _ W HW)
                  with ind_former_dec (cmd_F B H) (Δ ++ fc_tele (cmd_F B H)) M W
                         (alg_type_infer_sound HW (ext_eq_ctx_left _ _ _ _ _ HΔ)) => {
                | right _
                    with record_former_dec (cmd_F B H) (Δ ++ fc_tele (cmd_F B H)) M W
                           (alg_type_infer_sound HW (ext_eq_ctx_left _ _ _ _ _ HΔ)) => {
                  | left _ => run_failure (run_error_msg ("inductive alias " ++ x ++ " names a record type: use record"))
                  | right _ => run_failure (alias_target_error x E) }
                | left Hf with lvd _ _ nil (Δ ++ fc_tele (cmd_F B H))%list E (ctx_app_nil (ext_eq_ctx_left _ _ _ _ _ HΔ)) => {
                  | right _ => run_failure (run_error_levels ("inductive alias " ++ x))
                  | left Hlv with fs_fresh_sum x fs (pre_frames _ _ _ _ _ H) (pre_canon H) => {
                    | right _ => run_failure (run_error_msg (x ++ " is already declared"))
                    | left Hfr with params_evaluated_dec (cmd_F B H) (pre_gctx_f B H) (fc_tele (cmd_F B H)) Δ => {
                      | inright _ => run_failure (run_error_param_prop x)
                      | inleft (exist _ l HPr)
                          with large_type_dec (cmd_F B H) (lvd _ _) (Δ ++ fc_tele (cmd_F B H)) (ext_eq_ctx_left _ _ _ _ _ HΔ) (nf_to_exp W) => {
                        | inright _ => run_failure (alias_target_error x E)
                        | inleft (exist _ i HWt) =>
                            let (e, He) := dm_entry_rep B H pv Δ i (nf_to_exp W) M E HWt
                                             (alg_type_infer_sound HW (ext_eq_ctx_left _ _ _ _ _ HΔ)) in
                            run_success (exist _ (fs_add x e fs) (add_post H (erep_drop _ _ _ _ He) (erep_values _ _ _ _ He)
                                          (indalias_ok Htel (cmd_ext B H Δ HΔ) (cmd_modexp B H Δ E HE) (cmd_params_evaluated B H Δ l HPr)
                                             Ht (cmd_infer B H Δ W M HW) (cmd_exp B H Δ (nf_to_exp W) Typeω@i HWt)
                                             (cmd_exp B H Δ M (nf_to_exp W) (alg_type_infer_sound HW (ext_eq_ctx_left _ _ _ _ _ HΔ)))
                                             (cmd_ind_former B H Δ M W Hf) (cmd_levels_abstractable B H Δ E Hlv) Hfr))) } } } } } } } } } } }.

  (** A record alias, checked as an inductive alias is, for a type former
      of a record type. *)
  Equations recalias_step (ch : list path) (s : funits) (K : unit_closure_map) (D : list path) (B : builtins) (fs : fstack)
    (x : string) (pv : bool) (Δ : ctx) (E : modexp) (H : pre ch s K D fs) : frames_result ch s K D B fs (core_cmd_record_alias x pv Δ E) :=
  | ch, s, K, D, B, fs, x, pv, Δ, E, H with all_assumptions_dec Δ => {
    | right _ => run_failure (run_error_msg ("parameters of record alias " ++ x ++ " that are not assumptions"))
    | left Htel with check_ext (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) Δ => {
      | right _ => run_failure (run_error_msg ("ill-formed record alias " ++ x))
      | left HΔ with check_modexp (cmd_F B H) (lvd _ _) (Δ ++ fc_tele (cmd_F B H)) (ext_eq_ctx_left _ _ _ _ _ HΔ) E => {
        | right _ => run_failure (run_error_msg ("ill-formed record alias " ++ x))
        | left HE with opt_case (modexp_as_term E) => {
          | inright _ => run_failure (recalias_target_error x)
          | inleft (exist _ M Ht)
              with type_infer (cmd_F B H) (lvd _ _) (Δ ++ fc_tele (cmd_F B H)) (ext_eq_ctx_left _ _ _ _ _ HΔ) M (type_infer_order_all M) => {
            | inright _ => run_failure (recalias_target_error x)
            | inleft (exist _ W HW)
                with record_former_dec (cmd_F B H) (Δ ++ fc_tele (cmd_F B H)) M W
                       (alg_type_infer_sound HW (ext_eq_ctx_left _ _ _ _ _ HΔ)) => {
              | right _
                  with ind_former_dec (cmd_F B H) (Δ ++ fc_tele (cmd_F B H)) M W
                         (alg_type_infer_sound HW (ext_eq_ctx_left _ _ _ _ _ HΔ)) => {
                | left _ => run_failure (run_error_msg ("record alias " ++ x ++ " names an inductive type: use inductive"))
                | right _ => run_failure (recalias_target_error x) }
              | left Hf with lvd _ _ nil (Δ ++ fc_tele (cmd_F B H))%list E (ctx_app_nil (ext_eq_ctx_left _ _ _ _ _ HΔ)) => {
                | right _ => run_failure (run_error_levels ("record alias " ++ x))
                | left Hlv with fs_fresh_sum x fs (pre_frames _ _ _ _ _ H) (pre_canon H) => {
                  | right _ => run_failure (run_error_msg (x ++ " is already declared"))
                  | left Hfr with params_evaluated_dec (cmd_F B H) (pre_gctx_f B H) (fc_tele (cmd_F B H)) Δ => {
                    | inright _ => run_failure (run_error_param_prop x)
                    | inleft (exist _ l HPr)
                        with large_type_dec (cmd_F B H) (lvd _ _) (Δ ++ fc_tele (cmd_F B H)) (ext_eq_ctx_left _ _ _ _ _ HΔ) (nf_to_exp W) => {
                      | inright _ => run_failure (recalias_target_error x)
                      | inleft (exist _ i HWt) =>
                          let (e, He) := dm_entry_rep B H pv Δ i (nf_to_exp W) M E HWt
                                           (alg_type_infer_sound HW (ext_eq_ctx_left _ _ _ _ _ HΔ)) in
                          run_success (exist _ (fs_add x e fs) (add_post H (erep_drop _ _ _ _ He) (erep_values _ _ _ _ He)
                                        (recalias_ok Htel (cmd_ext B H Δ HΔ) (cmd_modexp B H Δ E HE) (cmd_params_evaluated B H Δ l HPr)
                                           Ht (cmd_infer B H Δ W M HW) (cmd_exp B H Δ (nf_to_exp W) Typeω@i HWt)
                                           (cmd_exp B H Δ M (nf_to_exp W) (alg_type_infer_sound HW (ext_eq_ctx_left _ _ _ _ _ HΔ)))
                                           (cmd_record_former B H Δ M W Hf) (cmd_levels_abstractable B H Δ E Hlv) Hfr))) } } } } } } } } } }.

  (** The wf of the frames, read at the units a command sees *)
  Lemma pre_gctx_view {ch s K D fs} (H : pre ch s K D fs) : ⊢ᵍ view_deps (cmd_view s D) ⍮ decode_stack fs.
  Proof. rewrite cmd_view_deps; exact (pre_gctx (pre_unit_invariant _ _ _ _ _ H)). Qed.

  (** A mutual definition's definitions filed, fast *)
  Lemma mdef_res {ch s K D B fs b pv Δ f0 fs0 pq m0 Ps Dd Us ms fs'} : all_assumptions Δ ->
      ⊢ gds_restrict D (decode_units s) ⍮ decode_stack fs ⍮ Δ ++ gs_tele (decode_stack fs) ->
      mdef_group (gds_restrict D (decode_units s)) (decode_stack fs) Δ (raw_fun_head_of f0) (List.map raw_fun_head_of fs0) pq m0 Ps Dd Us ms ->
      mdefs_filed (cmd_view s D) b pv (mdef_defs pq Dd Us Δ (f0 :: fs0) ms) fs fs' ->
      post_cmd ch (decode_units s) K D B (decode_stack fs) (core_cmd_mdef b pv Δ (f0 :: fs0)) (mk_run_state_core (decode_units s) K D B (decode_stack fs')) /\
      frames_rep (gds_restrict D (decode_units s)) fs'.
  Proof.
    intros Htel HΔ Hgp [Hok Hv Hr]; rewrite cmd_view_deps in Hr, Hv; split; [| exact (mk_frames_rep _ _ (proj1 (fctx_ok_frames _ _ Hok)) Hv) ].
    exact (mdef_ok Htel HΔ Hgp Hr).
  Qed.

  (** A mutual definition, checked premise by premise: its parameters, its
      functions' group ([mdef_group_dec]), then the definitions filed. *)
  Equations mdef_step (ch : list path) (s : funits) (K : unit_closure_map) (D : list path) (B : builtins) (fs : fstack)
    (b pv : bool) (Δ : ctx) (fns : list raw_fun) (H : pre ch s K D fs) : frames_result ch s K D B fs (core_cmd_mdef b pv Δ fns) :=
  | ch, s, K, D, B, fs, b, pv, Δ, nil, H => run_failure (run_error_msg "a mutual definition with no function")
  | ch, s, K, D, B, fs, b, pv, Δ, f0 :: fns, H with all_assumptions_dec Δ => {
    | right _ => run_failure (run_error_msg "parameters of a mutual definition that are not assumptions")
    | left Htel with check_ctx (cmd_F B H) (lvd _ _) (pre_gctx_f B H) (Δ ++ fc_tele (cmd_F B H)) => {
      | right _ => run_failure (tele_blame_error fs (find_tele_blame (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) Δ)
                           (run_error_msg "ill-formed parameters of a mutual definition"))
      | left HΔ with mdef_group_dec (cmd_F B H) (lvd _ _) (pre_gctx_f B H) Δ (raw_fun_head_of f0) (List.map raw_fun_head_of fns) => {
        | inr e => run_failure (mdef_group_why_error e)
        | inl (exist _ (pq, m0, Ps, Dd, Us, ms) Hgp)
            with mdefs_dec lvd (cmd_view s D) b pv (mdef_defs pq Dd Us Δ (f0 :: fns) ms) fs (pre_fctx_ok H) (pre_gctx_view H)
                   (pre_frame_values _ _ _ _ _ H) => {
          | inr (exist _ e _) => run_failure (mdefs_why_error e)
          | inl (exist _ fs' Hm) =>
              run_success (exist _ fs' (mdef_res Htel (cmd_ctx B H Δ HΔ) (cmd_mdef_group B H _ _ _ _ _ _ _ _ _ Hgp) Hm)) } } } }.

  (** *** Generated Commands

      What a declaration generates are definitions, and frames of modules
      opened and closed ([recursor_mod_cmds]); they are run as they are, by
      the steps of written ones. *)

  Definition gen_step (ch : list path) (s : funits) (K : unit_closure_map) (D : list path) (B : builtins) (fs : fstack)
    (c : core_cmd) (H : pre ch s K D fs) : step_result ch s K D B fs c :=
    match c as c0 return step_result ch s K D B fs c0 with
    | core_cmd_def x b pv κ A oM => frames_step H (def_step ch s K D B fs x b pv κ A oM H)
    | core_cmd_mod_open x pv Δ => frames_step H (mod_open_step ch s K D B fs x pv Δ H)
    | core_cmd_close x pv => frames_step H (close_step ch s K D B fs x pv H)
    | _ => run_failure (run_error_msg "internal error: a generated command is a definition, or opens or closes a frame")
    end.

  (** Generated commands, in order *)
  Fixpoint gen_items_impl (ch : list path) (s : funits) (K : unit_closure_map) (D : list path) (B : builtins) (fs : fstack)
    (cs : list core_cmd) (H : pre ch s K D fs) {struct cs} :
    run_result ({r | fast_res (post_cmds ch (decode_units s) K D B (decode_stack fs) (List.map ci_core cs)) r} * certified_log)%type :=
    match cs as cs0 return run_result ({r | fast_res (post_cmds ch (decode_units s) K D B (decode_stack fs) (List.map ci_core cs0)) r} * certified_log)%type with
    | nil => run_success (exist _ _ (same_res H nil_ok), log_nil)
    | c :: cs' =>
        match gen_step ch s K D B fs c H with
        | run_failure e => run_failure e
        | run_success (exist _ r1 Hr1, l1) =>
            match gen_items_impl ch (run_state_units r1) (run_state_closures r1) (run_state_imports r1) (run_state_builtins r1)
                    (run_state_frames r1) cs' (cmd_pre_f H Hr1) with
            | run_failure e => run_failure e
            | run_success (exist _ r2 Hr2, l2) => run_success (exist _ r2 (core_cons_res Hr1 Hr2), log_app l1 l2)
            end
        end
    end.

  (** *** Groups *)

  (** A member's frame, at the path of its member *)
  Lemma pre_push_ind {ch s K D fs x pq k Dd Δ} : pre ch s K D fs ->
      (exists ΘR, unit_invariant ch (decode_units s) K D ΘR (gs_push_ind (ind_qname (decode_stack fs) x) pq k Dd Δ (decode_stack fs))) ->
      pre ch s K D (fs_push_ind (fs_ind_qname fs x) pq k Dd Δ fs).
  Proof. intros H Hl; rewrite <- fs_ind_qname_dec in Hl; apply (pre_cons H); [ reflexivity | exact Hl ]. Qed.

  (** The frame of the member [k] of a group, opened *)
  Lemma member_push_pre {ch s K D fs pv R pq Dd k x xs} : pre ch s K D fs -> mems_pre (decode_stack fs) R pq Dd k (x :: xs) ->
      head_entry ch (decode_units s) K D (decode_stack fs) pv pq Dd k (x :: xs) ->
      pre ch s K D (fs_push_ind (fs_ind_qname fs x) pq k Dd (raw_decl_uparams R) fs).
  Proof. intros H Hp HE; exact (pre_push_ind H (push_ind_pre (pre_unit_invariant _ _ _ _ _ H) (mems_fresh_head Hp) (mems_pre_uparams _ _ _ _ _ _ Hp) HE)). Qed.

  (** A member's module, its commands run in its frame by [r1], read in
      Core: the frame it ends with is the member's, on the frames below,
      and closes into the member's entry. *)
  Lemma member_close {ch s K D B fs pv R pq Dd k x xs M} (H : pre ch s K D fs) (Hp : mems_pre (decode_stack fs) R pq Dd k (x :: xs))
      (HE : head_entry ch (decode_units s) K D (decode_stack fs) pv pq Dd k (x :: xs)) {r1 : run_state} {f fs2}
      (Hr1 : fast_res (post_cmds ch (decode_units s) K D B (decode_stack (fs_push_ind (fs_ind_qname fs x) pq k Dd (raw_decl_uparams R) fs))
                         (List.map ci_core (ind_mod_cmds_f (cmd_F B (member_push_pre H Hp HE)) R pq Dd k M))) r1)
      (HΞ : run_state_frames r1 = f :: fs2) :
      post_cmds ch (decode_units s) K D B (gs_push_ind (ind_qname (decode_stack fs) x) pq k Dd (raw_decl_uparams R) (decode_stack fs))
        (List.map ci_core (ind_mod_cmds (gds_restrict D (decode_units s)) (gs_push_ind (ind_qname (decode_stack fs) x) pq k Dd (raw_decl_uparams R) (decode_stack fs)) R pq Dd k M))
        (run_state_read r1) /\
      run_state_core_stack (run_state_read r1) = (ind_qname (decode_stack fs) x, fk_ind pq k Dd, gu_body (raw_decl_uparams R) (decode_mod (ff_body f))) :: decode_stack fs /\
      decode_stack (fs_add x (close_fentry pv f) fs2) = gs_add x (ge_ind pv pq k Dd (decode_mod (ff_body f))) (decode_stack fs) /\
      pre ch (run_state_units r1) (run_state_closures r1) (run_state_imports r1) (fs_add x (close_fentry pv f) fs2).
  Proof.
    pose proof (cmds_pre_f (member_push_pre H Hp HE) Hr1) as H1; rewrite HΞ in H1.
    destruct Hr1 as [Hr Hu Hv Hf Huv Hfv]; rewrite ind_mod_cmds_cmd in Hr.
    change (decode_stack (fs_push_ind (fs_ind_qname fs x) pq k Dd (raw_decl_uparams R) fs))
      with (gs_push_ind (fs_ind_qname fs x) pq k Dd (raw_decl_uparams R) (decode_stack fs)) in Hr.
    rewrite fs_ind_qname_dec in Hr.
    assert (Est : run_state_core_stack (run_state_read r1) = decode_frame f :: decode_stack fs2)
      by (cbn [run_state_read run_state_core_stack]; rewrite HΞ; reflexivity).
    destruct (pre_unit_invariant _ _ _ _ _ H) as [ΘR Hli]; destruct (unit_invariant_builtin_records Hli) as [RbR Hrb].
    destruct (member_ok (mems_fresh_head Hp) (mems_pre_uparams _ _ _ _ _ _ Hp) HE Hr Est _ _ Hli Hrb)
      as [(E2 & Emp & EKf & EU) [ΘR1 RbR1 _ Hli1 _ _ _]].
    destruct f as [mp Kf Δ t]; cbn [decode_frame ff_path ff_kind ff_params ff_body gu_params] in *; subst mp Kf Δ.
    split; [ exact Hr | split; [ rewrite Est, E2; reflexivity |] ].
    cbn [run_state_core_deps run_state_core_closures run_state_core_imports run_state_core_stack gu_mod] in Hli1.
    rewrite <- E2 in Hli1.
    destruct (close_frames (pv := pv) H1 ltac:(rewrite E2; exact (mems_fresh_head Hp)) ltac:(cbn [ff_path]; rewrite E2; reflexivity)
                ltac:(cbn [ff_path ff_kind ff_params kind_tele]; rewrite E2; exact (mems_pre_uparams _ _ _ _ _ _ Hp))
                (unit_invariant_restrict_gctx Hli1)) as [Ed Hrep].
    cbn [ff_path ff_kind ff_params ff_body frame_entry] in Ed; rewrite E2 in Ed.
    split; [ exact Ed |].
    constructor; [ rewrite Ed, <- E2; exists ΘR1; exact Hli1 | exact Hu | exact Hv | exact (frep_drop _ _ Hrep) | exact Huv | exact (frep_values _ _ Hrep) ].
  Qed.

  (** The members [k], [k + 1], …, filed *)
  Lemma mems_cons_res {ch s K D B fs pv R pq Dd k x xs M} (H : pre ch s K D fs) (Hp : mems_pre (decode_stack fs) R pq Dd k (x :: xs))
      (HE : head_entry ch (decode_units s) K D (decode_stack fs) pv pq Dd k (x :: xs)) {r1 : run_state} {f fs2}
      (HM : ind_member Dd k = Some M)
      (Hr1 : fast_res (post_cmds ch (decode_units s) K D B (decode_stack (fs_push_ind (fs_ind_qname fs x) pq k Dd (raw_decl_uparams R) fs))
                         (List.map ci_core (ind_mod_cmds_f (cmd_F B (member_push_pre H Hp HE)) R pq Dd k M))) r1)
      (HΞ : run_state_frames r1 = f :: fs2) {r2 : run_state} :
      fast_res (post_mems ch (decode_units (run_state_units r1)) (run_state_closures r1) (run_state_imports r1) (run_state_builtins r1)
                  (decode_stack (fs_add x (close_fentry pv f) fs2)) pv R pq Dd (S k) xs) r2 ->
      fast_res (post_mems ch (decode_units s) K D B (decode_stack fs) pv R pq Dd k (x :: xs)) r2.
  Proof.
    intros [Hr2 Hu Hv Hf Huv Hfv]; constructor; [| exact Hu | exact Hv | exact Hf | exact Huv | exact Hfv ].
    destruct (member_close (pv := pv) H Hp HE Hr1 HΞ) as (Hr & Est & Ed & _).
    rewrite Ed in Hr2.
    exact (mems_cons_ok HM (mems_fresh_head Hp) (mems_pre_uparams _ _ _ _ _ _ Hp) HE Hr Est Hr2).
  Qed.

  (** What the later members meet, where the member [k] is filed *)
  Lemma member_next_mems {ch s K D B fs pv R pq Dd k x xs M} (H : pre ch s K D fs) (Hp : mems_pre (decode_stack fs) R pq Dd k (x :: xs))
      (HE : head_entry ch (decode_units s) K D (decode_stack fs) pv pq Dd k (x :: xs)) {r1 : run_state} {f fs2}
      (Hr1 : fast_res (post_cmds ch (decode_units s) K D B (decode_stack (fs_push_ind (fs_ind_qname fs x) pq k Dd (raw_decl_uparams R) fs))
                         (List.map ci_core (ind_mod_cmds_f (cmd_F B (member_push_pre H Hp HE)) R pq Dd k M))) r1)
      (HΞ : run_state_frames r1 = f :: fs2) :
      mems_pre (decode_stack (fs_add x (close_fentry pv f) fs2)) R pq Dd (S k) xs.
  Proof. rewrite (proj1 (proj2 (proj2 (member_close (pv := pv) H Hp HE Hr1 HΞ)))); exact (mems_pre_tail Hp pv _). Qed.

  Lemma member_next_head {ch s K D B fs pv R pq Dd k x xs M} (H : pre ch s K D fs) (Hp : mems_pre (decode_stack fs) R pq Dd k (x :: xs))
      (HE : head_entry ch (decode_units s) K D (decode_stack fs) pv pq Dd k (x :: xs)) {r1 : run_state} {f fs2}
      (Hr1 : fast_res (post_cmds ch (decode_units s) K D B (decode_stack (fs_push_ind (fs_ind_qname fs x) pq k Dd (raw_decl_uparams R) fs))
                         (List.map ci_core (ind_mod_cmds_f (cmd_F B (member_push_pre H Hp HE)) R pq Dd k M))) r1)
      (HΞ : run_state_frames r1 = f :: fs2) :
      head_entry ch (decode_units (run_state_units r1)) (run_state_closures r1) (run_state_imports r1) (decode_stack (fs_add x (close_fentry pv f) fs2)) pv pq Dd (S k) xs.
  Proof.
    rewrite (proj1 (proj2 (proj2 (member_close (pv := pv) H Hp HE Hr1 HΞ)))); apply (later_head_entry (mems_pre_tail Hp pv _)).
    (** the uniform parameters are of evaluated kinds where the member is filed *)
    intros ΘR Hli.
    exact (added_ind_params_evaluated _ _ _ _ _ _ _ _ _ (mems_fresh_head Hp) (ui_wf _ _ _ _ _ _ Hli) (mems_pre_uparams _ _ _ _ _ _ Hp)).
  Qed.

  (** The declared members [k], [k + 1], … of a group, named [xs]: each
      member's module's commands run in its frame, as [run_ind_members_cons]
      runs them, and the member filed with the body they end with. *)
  Equations members_step (ch : list path) (s : funits) (K : unit_closure_map) (D : list path) (B : builtins) (fs : fstack)
    (pv : bool) (R : raw_decl) (pq : qname) (Dd : ind_decl) (k : nat) (xs : list string)
    (H : pre ch s K D fs) (Hp : mems_pre (decode_stack fs) R pq Dd k xs) (HE : head_entry ch (decode_units s) K D (decode_stack fs) pv pq Dd k xs) :
    run_result ({r | fast_res (post_mems ch (decode_units s) K D B (decode_stack fs) pv R pq Dd k xs) r} * certified_log)%type by struct xs :=
  | ch, s, K, D, B, fs, pv, R, pq, Dd, k, nil, H, Hp, HE => run_success (exist _ _ (same_res H mems_nil_ok), log_nil)
  | ch, s, K, D, B, fs, pv, R, pq, Dd, k, x :: xs', H, Hp, HE with member_case Dd k => {
    | inright _ => run_failure (run_error_msg "internal error: a declared member is missing")
    | inleft (exist _ M HM)
        with gen_items_impl ch s K D B (fs_push_ind (fs_ind_qname fs x) pq k Dd (raw_decl_uparams R) fs)
               (ind_mod_cmds_f (cmd_F B (member_push_pre H Hp HE)) R pq Dd k M) (member_push_pre H Hp HE) => {
      | run_failure e => run_failure e
      | run_success (exist _ r1 Hr1, l1) with list_case (run_state_frames r1) => {
        | inright _ => run_failure (run_error_msg "internal error: a member's module lost its frame")
        | inleft (existT _ f (exist _ fs2 HΞ))
            with members_step ch (run_state_units r1) (run_state_closures r1) (run_state_imports r1) (run_state_builtins r1)
                   (fs_add x (close_fentry pv f) fs2) pv R pq Dd (S k) xs'
                   (proj2 (proj2 (proj2 (member_close (pv := pv) H Hp HE Hr1 HΞ)))) (member_next_mems H Hp HE Hr1 HΞ)
                   (member_next_head H Hp HE Hr1 HΞ) => {
          | run_failure e => run_failure e
          | run_success (exist _ r2 Hr2, l2) => run_success (exist _ r2 (mems_cons_res H Hp HE HM Hr1 HΞ Hr2), log_app l1 l2) } } } }.

  (** ** Why a Group Is Ill Formed

      Read only for the checker's message, once [ind_nil_at_dec] has
      rejected the group. *)

  (** Which non-uniform parameter, if any, of the telescope [l] (innermost
      first, over [U]) has a type not in the sort [S]: its position,
      outermost [0], the context its type is in, its type and the sort
      there. *)
  Fixpoint nparams_blame (F : FCtx) (HΞ : ⊢ᵍ fc_deps F ⍮ fc_stack F) (U : ctx) (S : typ) (l : ctx)
    : option (nat * ctx * typ * typ) :=
    match l with
    | nil => None
    | ce_ass _ T :: Δ2 =>
        match nparams_blame F HΞ U S Δ2 with
        | Some r => Some r
        | None =>
            if check_exp_at F (lvd _ _) HΞ (Δ2 ++ U)%list S[wk_shiftn (List.length Δ2)]ʷ T then None
            else Some (List.length Δ2, (Δ2 ++ U)%list, T, S[wk_shiftn (List.length Δ2)]ʷ)
        end
    | _ :: Δ2 => nparams_blame F HΞ U S Δ2
    end.

  (** The first declared member, with its name, whose non-uniform
      parameters [nparams_blame] blames. *)
  Fixpoint members_nparams_blame (F : FCtx) (HΞ : ⊢ᵍ fc_deps F ⍮ fc_stack F) (Dd : ind_decl)
    (Mrs : list raw_member) (Ms : list imember) : option (string * (nat * ctx * typ * typ)) :=
    match Mrs, Ms with
    | Mr :: Mrs', Mk :: Ms' =>
        match nparams_blame F HΞ (ind_uparams Dd) (ind_sort Dd) (im_nparams Mk) with
        | Some r => Some (raw_member_name Mr, r)
        | None => members_nparams_blame F HΞ Dd Mrs' Ms'
        end
    | _, _ => None
    end.

  (** Whether a recursive argument of some member is its member at a
      number of non-uniform arguments other than that member's: the
      member's position, if so. *)
  Definition rec_arity_blame (Dd : ind_decl) : option nat :=
    List.find (fun j => negb (forallb (fun Mi =>
                 forallb (fun cg => forallb (fun g => match g with
                                                      | ca_rec t =>
                                                          if Nat.eqb (ptyp_mem t) j then
                                                            Nat.eqb (List.length (ptyp_ps t))
                                                              (match ind_member Dd j with Some Mj => im_nn Mj | None => 0 end)
                                                          else true
                                                      | ca_arg _ _ => true
                                                      end) (snd cg)) (im_cons Mi)) (ind_members Dd)))
      (List.seq 0 (List.length (ind_members Dd))).

  (** The message of an ill-formed group: a non-uniform parameter not in
      the sort, a recursive argument at the wrong number of arguments, or
      the group itself. *)
  Definition ind_wf_error (F : FCtx) (HΞ : ⊢ᵍ fc_deps F ⍮ fc_stack F) (R : raw_decl) (Mr0 : raw_member) (Dd : ind_decl)
    : run_error :=
    match members_nparams_blame F HΞ Dd (raw_decl_members R) (ind_members Dd) with
    | Some (x, (k, Δ, T, St)) => run_error_ind_nparams x k Δ T St
    | None =>
        match rec_arity_blame Dd with
        | Some j =>
            run_error_msg ("a recursive argument is "
                    ++ match List.nth_error (raw_decl_members R) j with Some Mr => raw_member_name Mr | None => raw_member_name Mr0 end
                    ++ " applied to all its parameters")
        | None => run_error_msg ("ill-formed inductive declaration " ++ raw_member_name Mr0)
        end
    end.

  (** The first member of [ms] whose name is not fresh in the innermost
      frame [fs], fast. *)
  Fixpoint first_taken (fs : fstack) (ms : list raw_member) : option string :=
    match ms with
    | nil => None
    | Mr :: ms' => if fs_fresh_dec (raw_member_name Mr) fs then first_taken fs ms' else Some (raw_member_name Mr)
    end.

  (** Whether the first declared member of [D] has a constructor [c]. *)
  Definition first_has_con (D : ind_decl) (c : string) : bool :=
    match ind_member D 0 with
    | Some M => List.existsb (String.eqb c) (List.map fst (im_cons M))
    | None => false
    end.

  Lemma first_has_con_false : forall D c, first_has_con D c = false ->
      forall M, ind_member D 0 = Some M -> ~ In c (List.map fst (im_cons M)).
  Proof.
    intros * H M HM Hin; unfold first_has_con in H; rewrite HM in H.
    rewrite <- Bool.not_true_iff_false, List.existsb_exists in H; apply H; exists c; split; [ exact Hin | apply String.eqb_refl ].
  Qed.

  (** Which name a group declared as [R] at [Ξ], filed as [D], with first
      member [x0], generates where one of its own names is: [rec] or
      [Rec] at a constructor of the first member, [Rec] at a member of a
      [mutual T] group or already in [T]'s frame ([gen_names_free]). *)
  Definition gen_names_blame (Ξ : gstack) (R : raw_decl) (D : ind_decl) (x0 : string) : option run_error :=
    if (ind_has_rec D && first_has_con D "rec")%bool then
      Some (run_error_msg ("rec is the recursor of " ++ x0 ++ ", not a constructor"))
    else if (negb (raw_decl_rec_field R) && first_has_con D "Rec")%bool then
      Some (run_error_msg ("Rec is the recursor module of " ++ x0 ++ ", not a constructor"))
    else if (raw_decl_rec_field R && List.existsb (String.eqb "Rec") (List.map raw_member_name (raw_decl_members R)))%bool then
      Some (run_error_msg ("Rec is the recursor module of " ++ qname_last (gs_path Ξ) ++ ", not a member"))
    else if (raw_decl_rec_field R && negb (if gs_fresh_dec "Rec" Ξ then true else false))%bool then
      Some (run_error_msg "Rec is already declared")
    else None.

  Lemma gen_names_blame_none {Ξ R D x0} : gen_names_blame Ξ R D x0 = None -> gen_names_free Ξ R D.
  Proof.
    unfold gen_names_blame; intros H.
    destruct (ind_has_rec D && first_has_con D "rec")%bool eqn:E1; [ discriminate |].
    destruct (negb (raw_decl_rec_field R) && first_has_con D "Rec")%bool eqn:E2; [ discriminate |].
    destruct (raw_decl_rec_field R && List.existsb (String.eqb "Rec") (List.map raw_member_name (raw_decl_members R)))%bool eqn:E3; [ discriminate |].
    destruct (raw_decl_rec_field R && negb (if gs_fresh_dec "Rec" Ξ then true else false))%bool eqn:E4; [ discriminate |].
    constructor.
    - intros Hr; rewrite Hr in E1; exact (first_has_con_false _ _ E1).
    - intros Hr; rewrite Hr in E2; exact (first_has_con_false _ _ E2).
    - intros Hr Hin; rewrite Hr in E3; cbn [andb] in E3.
      rewrite <- Bool.not_true_iff_false, List.existsb_exists in E3; apply E3.
      exists "Rec"%string; split; [ exact Hin | apply String.eqb_refl ].
    - intros Hr; rewrite Hr in E4; cbn [andb] in E4.
      destruct (gs_fresh_dec "Rec" Ξ) as [Hf | Hf]; [ exact Hf | discriminate ].
  Qed.

  Lemma gen_names_blame_free {Ξ R D x0} : gen_names_free Ξ R D -> gen_names_blame Ξ R D x0 = None.
  Proof.
    intros [H1 H2 H3 H4]; unfold gen_names_blame.
    assert (Hfc : forall c, (forall M, ind_member D 0 = Some M -> ~ In c (List.map fst (im_cons M))) ->
                    first_has_con D c = false).
    { intros c Hc; unfold first_has_con; destruct (ind_member D 0) as [M |] eqn:HM; [| reflexivity ].
      apply Bool.not_true_iff_false; intros E; apply List.existsb_exists in E as (c' & Hc' & Hq).
      apply String.eqb_eq in Hq; subst c'; exact (Hc M eq_refl Hc'). }
    assert (E1 : (ind_has_rec D && first_has_con D "rec")%bool = false).
    { destruct (ind_has_rec D) eqn:Er; [ exact (Hfc _ (H1 eq_refl)) | reflexivity ]. }
    assert (E2 : (negb (raw_decl_rec_field R) && first_has_con D "Rec")%bool = false).
    { destruct (raw_decl_rec_field R) eqn:Ed; [ reflexivity | exact (Hfc _ (H2 eq_refl)) ]. }
    assert (E3 : (raw_decl_rec_field R && List.existsb (String.eqb "Rec") (List.map raw_member_name (raw_decl_members R)))%bool = false).
    { destruct (raw_decl_rec_field R) eqn:Ed; [| reflexivity ]; cbn [andb negb].
      apply Bool.not_true_iff_false; intros E; apply List.existsb_exists in E as (c & Hc & Hq).
      apply String.eqb_eq in Hq; subst c; exact (H3 eq_refl Hc). }
    assert (E4 : (raw_decl_rec_field R && negb (if gs_fresh_dec "Rec" Ξ then true else false))%bool = false).
    { destruct (raw_decl_rec_field R) eqn:Ed; [| reflexivity ]; cbn [andb negb].
      destruct (gs_fresh_dec "Rec" Ξ) as [Hf | Hf]; [ reflexivity | exfalso; exact (Hf (H4 eq_refl)) ]. }
    rewrite E1, E2, E3, E4; reflexivity.
  Qed.

  (** [gen_names_blame], on the fast frames *)
  Definition gen_names_blame_f (fs : fstack) (R : raw_decl) (D : ind_decl) (x0 : string) : option run_error :=
    if (ind_has_rec D && first_has_con D "rec")%bool then
      Some (run_error_msg ("rec is the recursor of " ++ x0 ++ ", not a constructor"))
    else if (negb (raw_decl_rec_field R) && first_has_con D "Rec")%bool then
      Some (run_error_msg ("Rec is the recursor module of " ++ x0 ++ ", not a constructor"))
    else if (raw_decl_rec_field R && List.existsb (String.eqb "Rec") (List.map raw_member_name (raw_decl_members R)))%bool then
      Some (run_error_msg ("Rec is the recursor module of " ++ qname_last (fs_path fs) ++ ", not a member"))
    else if (raw_decl_rec_field R && negb (fs_fresh_dec "Rec" fs))%bool then
      Some (run_error_msg "Rec is already declared")
    else None.

  Lemma gen_names_blame_f_eq : forall fs R D x0, fstack_drop fs = fs_of (decode_stack fs) -> canon_stack (decode_stack fs) ->
      gen_names_blame_f fs R D x0 = gen_names_blame (decode_stack fs) R D x0.
  Proof.
    intros * Hr Hc; unfold gen_names_blame_f, gen_names_blame; rewrite fs_path_dec.
    assert (E : fs_fresh_dec "Rec" fs = if gs_fresh_dec "Rec" (decode_stack fs) then true else false).
    { rewrite <- fs_fresh_dec_drop, Hr; destruct (gs_fresh_dec "Rec" (decode_stack fs)) as [Hf | Hf].
      - apply (fs_fresh_dec_of _ _ Hc), Hf.
      - apply Bool.not_true_iff_false; intros E; apply Hf; exact (proj1 (fs_fresh_dec_of _ _ Hc) E). }
    rewrite E; reflexivity.
  Qed.

  (** What a group declaration checked at its command's fast context
      proves, read in Core, and its members' and recursor module's runs:
      [run_cmd_ind_case]. *)
  Lemma ind_res {ch s K D B fs pv R Mr0 Mrs csD Vs Ss csV Nvs Dd} (H : pre ch s K D fs) {r1 r2 : run_state} :
      raw_decl_members R = Mr0 :: Mrs ->
      Forall (fun Mr => raw_member_sort Mr = raw_member_sort Mr0) Mrs ->
      Forall2 (raw_member_classify (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) R) (raw_decl_members R) csD ->
      views_ok (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) R csD Vs Ss csV Nvs ->
      raw_decl_filed (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) R Vs Ss csD csV Nvs = Some Dd ->
      ind_nil_at (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) (fs_ind_qname fs (raw_member_name Mr0)) Dd
        (grp_self_insts (fs_ind_qname fs (raw_member_name Mr0)) Dd) ->
      gen_names_free (decode_stack fs) R Dd ->
      fast_res (post_mems ch (decode_units s) K D B (decode_stack fs) pv R (fs_ind_qname fs (raw_member_name Mr0)) Dd 0
                  (List.map raw_member_name (raw_decl_members R))) r1 ->
      fast_res (post_cmds ch (decode_units (run_state_units r1)) (run_state_closures r1) (run_state_imports r1) (run_state_builtins r1) (decode_stack (run_state_frames r1))
                  (List.map ci_core (rec_cmds (gds_restrict (run_state_imports r1) (decode_units (run_state_units r1))) (decode_stack (run_state_frames r1)) R
                     (fs_ind_qname fs (raw_member_name Mr0)) Dd))) r2 ->
      fast_res (post_cmd ch (decode_units s) K D B (decode_stack fs) (core_cmd_inductive pv R)) r2.
  Proof.
    intros HR Hsort Hcls Hv Hfil Hnil Hgn [Hr1 _ _ _] [Hr2 Hu Hvis Hf Huv Hfv]; constructor;
      [| exact Hu | exact Hvis | exact Hf | exact Huv | exact Hfv ].
    pose proof (cmd_read B H (fun G _ => Forall2 (raw_member_classify (@gc_deps G) (@gc_stack G) R) (raw_decl_members R) csD) Hcls) as Hcls'.
    pose proof (cmd_read B H (fun G _ => views_ok (@gc_deps G) (@gc_stack G) R csD Vs Ss csV Nvs) Hv) as Hv'.
    pose proof (cmd_read B H (fun G _ => raw_decl_filed (@gc_deps G) (@gc_stack G) R Vs Ss csD csV Nvs = Some Dd) Hfil) as Hfil'.
    pose proof (cmd_read B H (fun G _ => ind_nil_at (@gc_deps G) (@gc_stack G) (fs_ind_qname fs (raw_member_name Mr0)) Dd
                                          (grp_self_insts (fs_ind_qname fs (raw_member_name Mr0)) Dd)) Hnil) as Hnil'.
    cbn beta in Hcls', Hv', Hfil', Hnil'.
    rewrite fs_ind_qname_dec in Hnil', Hr1, Hr2.
    exact (ind_ok HR Hsort Hcls' (views_siblings _ _ _ _ _ _ _ _ Hv') (views_classified _ _ _ _ _ _ _ _ Hv')
             (views_nparams _ _ _ _ _ _ _ _ Hv') (views_search_run _ _ _ _ _ _ _ _ Hv') Hfil' Hnil' Hgn Hr1 Hr2).
  Qed.

  (** The members' run's invariant, at the fast state it ends with *)
  Lemma mems_res_pre {ch s K D B fs pv R pq Dd k xs} {r : run_state} : pre ch s K D fs ->
      fast_res (post_mems ch (decode_units s) K D B (decode_stack fs) pv R pq Dd k xs) r ->
      pre ch (run_state_units r) (run_state_closures r) (run_state_imports r) (run_state_frames r).
  Proof.
    intros H [Hp Hu Hv Hf Huv Hfv]; constructor;
      [ exact (mems_post_pre (pre_unit_invariant _ _ _ _ _ H) Hp) | exact Hu | exact Hv | exact Hf | exact Huv | exact Hfv ].
  Qed.

  (** The first member's module, read at the declaration's facts *)
  Lemma ind_mems_pre_f {ch s K D fs R Mr0 Mrs Vs Ss csD csV Nvs Dd} B (H : pre ch s K D fs) :
      raw_decl_members R = Mr0 :: Mrs ->
      raw_decl_filed (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) R Vs Ss csD csV Nvs = Some Dd ->
      List.NoDup (List.map raw_member_name (raw_decl_members R)) ->
      Forall (fun Mr => gs_fresh (raw_member_name Mr) (decode_stack fs)) (raw_decl_members R) ->
      mems_pre (decode_stack fs) R (fs_ind_qname fs (raw_member_name Mr0)) Dd 0 (List.map raw_member_name (raw_decl_members R)).
  Proof.
    intros HR Hfil Hnd Hfr.
    pose proof (cmd_read B H (fun G _ => raw_decl_filed (@gc_deps G) (@gc_stack G) R Vs Ss csD csV Nvs = Some Dd) Hfil) as Hfil'.
    rewrite fs_ind_qname_dec; exact (ind_mems_pre HR Hfil' Hnd Hfr).
  Qed.

  Lemma first_head_entry_f {ch s K D fs pv R Dd xs} B (H : pre ch s K D fs) {x0} :
      mems_pre (decode_stack fs) R (fs_ind_qname fs x0) Dd 0 xs ->
      ind_nil_at (fc_deps (cmd_F B H)) (fc_stack (cmd_F B H)) (fs_ind_qname fs x0) Dd (grp_self_insts (fs_ind_qname fs x0) Dd) ->
      head_entry ch (decode_units s) K D (decode_stack fs) pv (fs_ind_qname fs x0) Dd 0 xs.
  Proof.
    intros Hp Hnil.
    pose proof (cmd_read B H (fun G _ => ind_nil_at (@gc_deps G) (@gc_stack G) (fs_ind_qname fs x0) Dd
                                          (grp_self_insts (fs_ind_qname fs x0) Dd)) Hnil) as Hnil'.
    exact (first_head_entry Hp Hnil').
  Qed.

  (** A group declaration, checked premise by premise: one sort, the
      declared members' constructors classified, the views found, the
      group filed, its names, the group well formed at its views'
      instances read back, and the names it generates free; then its
      members, each with its module, by [members_step], and its recursor
      module, if any, by [gen_items_impl]. *)
  Equations ind_step (ch : list path) (s : funits) (K : unit_closure_map) (D : list path) (B : builtins) (fs : fstack)
    (pv : bool) (R : raw_decl) (H : pre ch s K D fs) : step_result ch s K D B fs (core_cmd_inductive pv R) :=
  | ch, s, K, D, B, fs, pv, R, H with list_case (raw_decl_members R) => {
    | inright _ => run_failure (run_error_msg "a declaration of no inductive type")
    | inleft (existT _ Mr0 (exist _ Mrs HR))
        with Forall_dec (fun Mr => raw_member_sort Mr = raw_member_sort Mr0) (fun Mr => exp_eq_dec (raw_member_sort Mr) (raw_member_sort Mr0)) Mrs => {
      | right _ => run_failure (run_error_msg ("the types declared with " ++ raw_member_name Mr0 ++ " are not all of its sort"))
      | left Hsort with raw_members_classify_dec (cmd_F B H) (lvd _ _) (pre_gctx_f B H) R (raw_decl_members R) => {
        | inr (exist _ (x, c, y, classify_why_code sf) _) => run_failure (run_error_msg (classify_msg x c y sf))
        | inr (exist _ (x, c, y, classify_why_unapplied k) _) =>
            run_failure (run_error_msg (classify_msg (List.nth k (List.map raw_member_name (raw_decl_members R)) x) c y 3))
        | inr (exist _ (x, c, y, classify_why_nested h) _) => run_failure (run_error_nested x c y h)
        | inr (exist _ (x, c, y, classify_why_self_arg j k Δ h) _) =>
            run_failure (run_error_self_arg (List.nth j (List.map raw_member_name (raw_decl_members R)) x) x c y k Δ h)
        | inr (exist _ (x, c, y, classify_why_proof) _) =>
            run_failure (run_error_msg ("the argument " ++ y ++ " of " ++ c ++ " nests " ++ x
                                          ++ " at an instance that holds a proof, which is not supported"))
        | inr (exist _ (x, c, y, classify_why_rec_kind) _) =>
            run_failure (run_error_msg ("the recursive argument " ++ y ++ " of " ++ c ++ " is written of another kind than a type of "
                                          ++ x ++ ", which is in a universe"))
        | inl (exist _ csD Hcls) with views_search (cmd_F B H) (pre_gctx_f B H) R csD => {
          | run_failure e => run_failure e
          | run_success (existT _ Vs (existT _ Ss (existT _ csV (exist _ Nvs Hv))))
              with raw_decl_filed_case (cmd_F B H) R Vs Ss csD csV Nvs => {
            | inright _ => run_failure (run_error_msg ("internal error: the group of " ++ raw_member_name Mr0 ++ " cannot be filed"))
            | inleft (exist _ Dd Hfil) with nodup_dec (List.map raw_member_name (raw_decl_members R)) => {
              | right _ => run_failure (run_error_msg ("two types declared with " ++ raw_member_name Mr0 ++ " have one name"))
              | left Hnd with Forall_dec (fun Mr => gs_fresh (raw_member_name Mr) (decode_stack fs))
                                (fun Mr => fs_fresh_sum (raw_member_name Mr) fs (pre_frames _ _ _ _ _ H) (pre_canon H)) (raw_decl_members R) => {
                | right _ =>
                    run_failure (run_error_msg (match first_taken fs (raw_decl_members R) with Some x => x | None => raw_member_name Mr0 end
                                         ++ " is already declared"))
                | left Hfr
                    with ind_nil_at_dec (cmd_F B H) (lvd _ _) (pre_gctx_f B H) (fs_ind_qname fs (raw_member_name Mr0)) Dd
                           (grp_self_insts (fs_ind_qname fs (raw_member_name Mr0)) Dd) => {
                  | right _ => run_failure (ind_wf_error (cmd_F B H) (pre_gctx_f B H) R Mr0 Dd)
                  | left Hnil with inspect (gen_names_blame_f fs R Dd (raw_member_name Mr0)) => {
                  | exist _ (Some e) _ => run_failure e
                  | exist _ None Egn
                      with members_step ch s K D B fs pv R (fs_ind_qname fs (raw_member_name Mr0)) Dd 0
                             (List.map raw_member_name (raw_decl_members R)) H
                             (ind_mems_pre_f B H HR Hfil Hnd Hfr) (first_head_entry_f B H (ind_mems_pre_f B H HR Hfil Hnd Hfr) Hnil) => {
                    | run_failure e => run_failure e
                    | run_success (exist _ r1 Hr1, l1)
                        with gen_items_impl ch (run_state_units r1) (run_state_closures r1) (run_state_imports r1) (run_state_builtins r1) (run_state_frames r1)
                               (rec_cmds_f (cmd_F (run_state_builtins r1) (mems_res_pre H Hr1)) R (fs_ind_qname fs (raw_member_name Mr0)) Dd)
                               (mems_res_pre H Hr1) => {
                      | run_failure e => run_failure e
                      | run_success (exist _ r2 Hr2, l2) =>
                          run_success (exist _ r2 (ind_res H HR Hsort Hcls Hv Hfil Hnil
                                             (gen_names_blame_none
                                                (eq_trans (eq_sym (gen_names_blame_f_eq _ _ _ _ (pre_frames _ _ _ _ _ H) (pre_canon H))) Egn))
                                             Hr1 (eq_ind _ (fun cs => fast_res (post_cmds ch _ _ _ _ _ (List.map ci_core cs)) r2) Hr2 _
                                                    (rec_cmds_cmd (run_state_builtins r1) (mems_res_pre H Hr1) _ _ _))),
                               log_app l1 l2) } } } } } } } } } } }.

  (** *** Records *)

  (** A record's frame, at the path of the innermost frame *)
  Lemma pre_push_record {ch s K D fs x Δ Srt fds} : pre ch s K D fs ->
      (exists ΘR, unit_invariant ch (decode_units s) K D ΘR
                    (gs_push_record (ind_qname (decode_stack fs) x) (record_at (decode_stack fs) Δ Srt fds) Δ (decode_stack fs))) ->
      pre ch s K D (fs_push_record (fs_ind_qname fs x) (fs_record_at fs Δ Srt fds) Δ fs).
  Proof. intros H Hl; rewrite <- fs_ind_qname_dec, <- fs_record_at_dec in Hl; apply (pre_cons H); [ reflexivity | exact Hl ]. Qed.

  (** The record's frame opened, its entry checked at the restriction *)
  Lemma record_push_pre {ch s K D fs x pv Δ Srt fds} (H : pre ch s K D fs) :
      gs_fresh x (decode_stack fs) ->
      gds_restrict D (decode_units s) ⍮ decode_stack fs ⍮ ind_qname (decode_stack fs) x
        ⊢ᵉ ge_record pv (ind_qname (decode_stack fs) x) (record_at (decode_stack fs) Δ Srt fds) ⋄ ->
      pre ch s K D (fs_push_record (fs_ind_qname fs x) (fs_record_at fs Δ Srt fds) Δ fs).
  Proof.
    intros Hfr HE; destruct (pre_unit_invariant _ _ _ _ _ H) as [ΘR Hli].
    exact (pre_push_record H (ex_intro _ ΘR (unit_invariant_push_record Hli Hfr (unit_invariant_entry_at Hli Hfr HE)))).
  Qed.

  (** A record's frame opened and its field definitions run, fast *)
  Lemma record_open_res {ch s K D B fs x pv Δ Srt fds} {r : run_state} (H : pre ch s K D fs) :
      gs_fresh x (decode_stack fs) ->
      gds_restrict D (decode_units s) ⍮ decode_stack fs ⍮ ind_qname (decode_stack fs) x
        ⊢ᵉ ge_record pv (ind_qname (decode_stack fs) x) (record_at (decode_stack fs) Δ Srt fds) ⋄ ->
      fast_res (post_cmds ch (decode_units s) K D B (decode_stack (fs_push_record (fs_ind_qname fs x) (fs_record_at fs Δ Srt fds) Δ fs))
                  (List.map ci_core (record_field_cmds (fs_record_at fs Δ Srt fds)))) r ->
      fast_res (post_cmd ch (decode_units s) K D B (decode_stack fs) (core_cmd_record_open x pv Δ Srt fds)) r.
  Proof.
    intros Hfr HE [Hp Hu Hv Hf Huv Hfv]; constructor; [| exact Hu | exact Hv | exact Hf | exact Huv | exact Hfv ].
    change (decode_stack (fs_push_record (fs_ind_qname fs x) (fs_record_at fs Δ Srt fds) Δ fs))
      with (gs_push_record (fs_ind_qname fs x) (fs_record_at fs Δ Srt fds) Δ (decode_stack fs)) in Hp.
    rewrite fs_ind_qname_dec, fs_record_at_dec in Hp.
    exact (record_open_ok Hfr HE Hp).
  Qed.

  (** A record: its entry checked with an empty module
      ([record_entry_dec]), its frame opened, its field definitions run in
      it. *)
  Equations record_open_step (ch : list path) (s : funits) (K : unit_closure_map) (D : list path) (B : builtins) (fs : fstack)
    (x : string) (pv : bool) (Δ : ctx) (Srt : typ) (fds : list (string * abs_kind * typ)) (H : pre ch s K D fs) :
    step_result ch s K D B fs (core_cmd_record_open x pv Δ Srt fds) :=
  | ch, s, K, D, B, fs, x, pv, Δ, Srt, fds, H with fs_fresh_sum x fs (pre_frames _ _ _ _ _ H) (pre_canon H) => {
    | right _ => run_failure (run_error_msg (x ++ " is already declared"))
    | left Hfr with record_entry_dec (cmd_F B H) (lvd _ _) (pre_gctx_f B H) (fs_ind_qname fs x) pv Δ Srt fds => {
      | inr (exist _ e _) => run_failure (record_why_error x fds e)
      | inl HE
          with gen_items_impl ch s K D B (fs_push_record (fs_ind_qname fs x) (fs_record_at fs Δ Srt fds) Δ fs)
                 (record_field_cmds (fs_record_at fs Δ Srt fds))
                 (record_push_pre H Hfr (eq_ind _ (fun mp => _ ⍮ _ ⍮ mp ⊢ᵉ ge_record pv mp _ ⋄) (cmd_record_entry B H _ pv Δ Srt fds HE) _ (fs_ind_qname_dec fs x))) => {
        | run_failure e => run_failure e
        | run_success (exist _ r Hr, l) =>
            run_success (exist _ r (record_open_res H Hfr
                                      (eq_ind _ (fun mp => _ ⍮ _ ⍮ mp ⊢ᵉ ge_record pv mp _ ⋄) (cmd_record_entry B H _ pv Δ Srt fds HE) _ (fs_ind_qname_dec fs x))
                                      Hr), l) } } }.

  (** *** Loads *)

  (** Seeing more filed units keeps their values right. *)
  Lemma units_values_see : forall K s L, units_values_ok K s -> units_values_ok K (fus_see L s).
  Proof.
    intros K s L [Hf Hs]; constructor; [ exact Hf |].
    intros fp u Hu; destruct (fus_see_visible _ _ _ _ Hu) as [E | E]; [ exact (Hf _ _ E) | exact (Hs _ _ E) ].
  Qed.

  (** The global context a command's result sees is well formed. *)
  Lemma post_cmd_gctx {ch s K D B fs c r} : pre ch s K D fs ->
      post_cmd ch (decode_units s) K D B (decode_stack fs) c r ->
      ⊢ᵍ gds_restrict (run_state_core_imports r) (run_state_core_deps r) ⍮ run_state_core_stack r.
  Proof.
    intros H Hp; destruct (pre_unit_invariant _ _ _ _ _ H) as [ΘR Hli].
    destruct (unit_invariant_builtin_records Hli) as [RbR Hrb].
    destruct (Hp _ _ Hli Hrb) as [ΘR' RbR' _ Hli' _ _ _]; exact (pre_gctx (ex_intro _ _ Hli')).
  Qed.

  (** A step that imported the filed units at [L] and changed neither the
      units filed nor the frames, as a result: [L] seen as well *)
  Lemma see_res {ch s K D B fs c B'} L : pre ch s K D fs ->
      post_cmd ch (decode_units s) K D B (decode_stack fs) c (mk_run_state_core (decode_units s) K (p_union D L) B' (decode_stack fs)) ->
      fast_res (post_cmd ch (decode_units s) K D B (decode_stack fs) c) (mk_run_state (fus_see L s) K (p_union D L) B' fs).
  Proof.
    intros H Hp; pose proof (post_cmd_gctx H Hp) as Hg; cbn [run_state_core_imports run_state_core_deps run_state_core_stack] in Hg.
    constructor; [ exact Hp | exact (units_rep_drop_see _ _ _ (pre_units _ _ _ _ _ H)) | | exact (pre_frames _ _ _ _ _ H)
                              | exact (units_values_see _ _ _ (pre_unit_values _ _ _ _ _ H)) |].
    - cbn [run_state_units run_state_imports]; apply (visible_rep_ext _ (D ++ L)); [ intros x; rewrite in_app_iff, p_union_iff; reflexivity |].
      exact (visible_rep_see _ _ _ (pre_visible _ _ _ _ _ H)).
    - cbn [run_state_units run_state_imports run_state_frames].
      refine (frames_values_deps _ _ _ _ (pre_gctx (pre_unit_invariant _ _ _ _ _ H)) Hg (pre_frame_values _ _ _ _ _ H)).
      apply restrict_mono; [ intros y Hy; apply p_union_iff; left; exact Hy | intros fq U HU; exact HU ].
  Qed.

  (** A builtin binding's result *)
  Definition builtins_ok {ch s K D B fs c} (H : pre ch s K D fs)
      (x : {B' | post_cmd ch (decode_units s) K D B (decode_stack fs) c (mk_run_state_core (decode_units s) K D B' (decode_stack fs))}) :
      {r | fast_res (post_cmd ch (decode_units s) K D B (decode_stack fs) c) r} :=
    let (B', Hp) := x in exist _ (mk_run_state s K D B' fs) (state_res H Hp).

  (** A unit found filed, read in Core *)
  Lemma units_found {ch s K D fs fp u} : pre ch s K D fs -> fus_find s fp = Some u ->
      gds_lookup (decode_units s) fp = Some (decode_unit u).
  Proof.
    intros H Hu; rewrite <- decode_units_drop, (decode_units_lookup _ _ (pre_units _ _ _ _ _ H)), fus_find_drop, Hu.
    cbn [option_map]; rewrite decode_unit_drop; reflexivity.
  Qed.

  (** A unit not filed, read in Core *)
  Lemma units_none {ch s K D fs fp} : pre ch s K D fs -> fus_find s fp = None -> gds_lookup (decode_units s) fp = None.
  Proof. intros H Hn; rewrite <- decode_units_drop, (decode_units_lookup _ _ (pre_units _ _ _ _ _ H)), fus_find_drop, Hn; reflexivity. Qed.

  (** The units after a load: the unit filed on top of everything its run
      filed, and seen, with its closure, next to the units seen before the
      load, which its run set aside *)
  Definition load_units (s : funits) (fp : path) (r : unit_result) : funits :=
    fus_see (fp :: unit_result_imports r) (fus_with_visible (fus_file fp (unit_result_unit r) (unit_result_units r)) (fus_visible s)).

  (** They are the units filed at the paths imported after the load. *)
  Lemma load_visible {ch s K D fs fp u0} {r : unit_result} : pre ch s K D fs -> fus_find s fp = None -> ~ In fp ch ->
      unit_run_ok (fp :: ch) s K u0 r -> visible_rep (load_units s fp r) (p_union D (fp :: unit_result_imports r)).
  Proof.
    intros H Hn Hnch [Hpost Hu _].
    pose proof (load_pre (pre_unit_invariant _ _ _ _ _ H) (units_none H Hn) Hnch) as G.
    destruct (pre_unit_invariant _ _ _ _ _ H) as [ΘR Hli].
    assert (Hq : forall fq, In fq D ->
               option_map funit_drop (fus_find (fus_file fp (unit_result_unit r) (unit_result_units r)) fq) = option_map funit_drop (fus_find s fq)).
    { intros fq Hq.
      apply (ui_dom _ _ _ _ _ _ Hli), gds_dom_lookup in Hq.
      destruct (gds_lookup ΘR fq) as [U |] eqn:EU; [| contradiction ].
      apply (ui_sub _ _ _ _ _ _ Hli) in EU.
      pose proof (ur_find _ _ (pre_units _ _ _ _ _ H) fq) as Es; rewrite EU, fus_find_drop in Es.
      destruct (Hpost G) as [_ _ _ _ _ _ _ _ [Hsub _ _] _].
      apply Hsub in EU; unfold unit_result_read in EU; cbn [unit_result_core_deps] in EU.
      unfold fus_find at 1, fus_file; cbn [fus_map]; rewrite path_key_find_add.
      destruct (path_beq fq fp) eqn:Eb.
      - apply path_beq_true in Eb as ->; rewrite Hn in Es; discriminate.
      - change (option_map funit_drop (fus_find (unit_result_units r) fq) = option_map funit_drop (fus_find s fq)).
        rewrite Es, <- fus_find_drop, (ur_find _ _ Hu fq), EU; reflexivity. }
    apply (visible_rep_ext _ (D ++ fp :: unit_result_imports r)); [ intros x; rewrite in_app_iff, p_union_iff; reflexivity |].
    unfold load_units; apply visible_rep_see, (visible_rep_grow s); [ exact (pre_visible _ _ _ _ _ H) | exact Hq ].
  Qed.

  (** A restriction to a path first and others, of units the path is
      not among, is the restriction to the others. *)
  Lemma gds_restrict_cons_absent : forall fp I Θ, gds_lookup Θ fp = None -> gds_restrict (fp :: I) Θ = gds_restrict I Θ.
  Proof.
    intros fp I Θ; induction Θ as [| [fq V] Θ IH]; intros Hn; [ reflexivity |].
    cbn [gds_lookup] in Hn; destruct (path_beq fp fq) eqn:E; [ discriminate |].
    unfold gds_restrict in *; cbn [filter]; rewrite (IH Hn); cbn [fst existsb].
    rewrite (path_beq_false fq fp ltac:(intros ->; rewrite path_beq_refl in E; discriminate)); reflexivity.
  Qed.

  (** So a unit filed at [fp], restricted to [fp] and others, is the unit
      on the restriction to the others. *)
  Lemma gds_restrict_cons_head : forall fp U I Θ, gds_lookup Θ fp = None ->
      gds_restrict (fp :: I) ((fp, U) :: Θ) = (fp, U) :: gds_restrict I Θ.
  Proof.
    intros * Hn; rewrite <- (gds_restrict_cons_absent fp I Θ Hn); unfold gds_restrict at 1; cbn [filter].
    replace (existsb (path_beq (fst (fp, U))) (fp :: I)) with true by (cbn [fst existsb]; rewrite path_beq_refl; reflexivity); reflexivity.
  Qed.

  (** After a load, the values of the units filed and seen are right in
      their homes, the loaded unit's at its closure, and those of the
      frames where they are open. *)
  Lemma load_values {ch s K D fs fp u0} {r : unit_result} : pre ch s K D fs -> fus_find s fp = None -> ~ In fp ch ->
      unit_run_ok (fp :: ch) s K u0 r -> canon_deps ((fp, decode_unit (unit_result_unit r)) :: decode_units (unit_result_units r)) ->
      decode_units (fus_file fp (unit_result_unit r) (unit_result_units r)) = (fp, decode_unit (unit_result_unit r)) :: decode_units (unit_result_units r) ->
      ⊢ᵍ gds_restrict (p_union D (fp :: unit_result_imports r)) (decode_units (load_units s fp r)) ⍮ decode_stack fs ->
      global_invariant ch ((fp, decode_unit (unit_result_unit r)) :: decode_units (unit_result_units r))
        ((fp, (unit_result_imports r, unit_result_builtins r)) :: unit_result_closures r) ->
      units_values_ok ((fp, (unit_result_imports r, unit_result_builtins r)) :: unit_result_closures r) (load_units s fp r) /\
      frames_values_ok (gds_restrict (p_union D (fp :: unit_result_imports r)) (decode_units (load_units s fp r))) fs.
  Proof.
    intros H Hn Hnch [Hpost _ _ Huv Hown] Hc Ed Hg G'.
    pose proof (load_pre (pre_unit_invariant _ _ _ _ _ H) (units_none H Hn) Hnch) as G.
    destruct (Hpost G) as [_ _ _ Gr _ _ _ _ [Hsub HKf _] _]; cbn [unit_result_read unit_result_core_deps unit_result_core_closures] in Gr; cbn [unit_result_read unit_result_core_deps unit_result_core_closures] in Hsub, HKf.
    assert (Hsub' : decode_units (unit_result_units r) ⊑ (fp, decode_unit (unit_result_unit r)) :: decode_units (unit_result_units r)).
    { intros fq V HV; cbn [gds_lookup]; destruct (path_beq fq fp) eqn:E; [| exact HV ].
      apply path_beq_true in E; subst fq; rewrite (proj1 Hc) in HV; discriminate. }
    assert (HKr : forall fq Dx, path_beq fq fp = false -> unit_closure_find (unit_result_closures r) fq = Some Dx ->
                    unit_closure_find ((fp, (unit_result_imports r, unit_result_builtins r)) :: unit_result_closures r) fq = Some Dx)
      by (intros fq Dx E HD; simp unit_closure_find; rewrite E; exact HD).
    change (decode_units (load_units s fp r)) with (decode_units (fus_file fp (unit_result_unit r) (unit_result_units r))) in Hg |- *;
      rewrite Ed in Hg |- *.
    split.
    - apply units_values_see; constructor.
      + change (decode_units (fus_with_visible (fus_file fp (unit_result_unit r) (unit_result_units r)) (fus_visible s))) with
          (decode_units (fus_file fp (unit_result_unit r) (unit_result_units r))); rewrite Ed.
        intros fq w Hw; unfold fus_find, fus_file in Hw; cbn [fus_map fus_with_visible] in Hw; rewrite path_key_find_add in Hw.
        destruct (path_beq fq fp) eqn:E.
        * apply path_beq_true in E; subst fq; injection Hw as <-.
          apply (mk_unit_values_home _ _ _ _ (unit_result_imports r)); [ simp unit_closure_find; rewrite path_beq_refl; reflexivity |].
          rewrite (gds_restrict_cons_head _ _ _ _ (proj1 Hc)); exact (Hown fp eq_refl).
        * exact (unit_values_home_grow _ _ _ _ _ _ _ _ Gr G' (fun Dx => HKr fq Dx E) Hsub' (uvo_filed _ _ Huv _ _ Hw)).
      + change (decode_units (fus_with_visible (fus_file fp (unit_result_unit r) (unit_result_units r)) (fus_visible s))) with
          (decode_units (fus_file fp (unit_result_unit r) (unit_result_units r))); rewrite Ed.
        intros fq w Hw; cbn [fus_visible fus_with_visible] in Hw.
        destruct (path_beq fq fp) eqn:E.
        * exfalso; apply path_beq_true in E; subst fq.
          pose proof (pre_visible _ _ _ _ _ H fp) as Hv; rewrite Hw, Hn in Hv; destruct (existsb _ _); discriminate.
        * refine (unit_values_home_grow _ _ _ _ _ _ _ _ G G' _ (gds_sub_trans _ _ _ Hsub Hsub') (uvo_seen _ _ (pre_unit_values _ _ _ _ _ H) _ _ Hw)).
          intros Dx HD; exact (HKr _ _ E (HKf _ _ HD)).
    - refine (frames_values_deps _ _ _ _ (pre_gctx (pre_unit_invariant _ _ _ _ _ H)) Hg (pre_frame_values _ _ _ _ _ H)).
      apply restrict_mono; [ intros y Hy; apply p_union_iff; left; exact Hy | exact (gds_sub_trans _ _ _ Hsub Hsub') ].
  Qed.

  (** The global invariant a command's result keeps. *)
  Lemma post_cmd_global {ch s K D B fs c r} : pre ch s K D fs ->
      post_cmd ch (decode_units s) K D B (decode_stack fs) c r ->
      global_invariant ch (run_state_core_deps r) (run_state_core_closures r).
  Proof.
    intros H Hp; destruct (pre_unit_invariant _ _ _ _ _ H) as [ΘR Hli].
    destruct (unit_invariant_builtin_records Hli) as [RbR Hrb].
    destruct (Hp _ _ Hli Hrb) as [ΘR' RbR' _ Hli' _ _ _]; exact (ui_global _ _ _ _ _ _ Hli').
  Qed.

  (** A unit loaded, filed fast: on top of everything its run filed, with
      the closure and the record it ends with ([load_state]) *)
  Lemma load_res {ch s K D B fs fp src prg u} {r : unit_result} {B'} (H : pre ch s K D fs) :
      fus_find s fp = None -> ~ In fp ch ->
      load_path fp = Some src -> read src = Some prg -> prog_path prg = fp -> to_core prg = Some u ->
      unit_run_ok (fp :: ch) s K u r -> builtins_merge B (unit_result_builtins r) = Some B' ->
      fast_res (post_cmd ch (decode_units s) K D B (decode_stack fs) (core_cmd_load fp))
        (mk_run_state (load_units s fp r) ((fp, (unit_result_imports r, unit_result_builtins r)) :: unit_result_closures r) (p_union D (fp :: unit_result_imports r)) B' fs).
  Proof.
    intros Hn Hnch Hl Hrd Hp Ht Hr Hm; pose proof (load_visible H Hn Hnch Hr) as Hv; pose proof Hr as Hr0; destruct Hr as [Hpost Hu Hut].
    pose proof (load_ok (D := D) (Ξ := decode_stack fs) (B := B) (units_none H Hn) Hnch Hl Hrd Hp Ht Hpost Hm) as Hok.
    assert (Hc : canon_deps ((fp, decode_unit (unit_result_unit r)) :: decode_units (unit_result_units r))).
    { destruct (pre_unit_invariant _ _ _ _ _ H) as [ΘR Hli]; destruct (unit_invariant_builtin_records Hli) as [RbR Hrb].
      destruct (Hok _ _ Hli Hrb) as [ΘR' RbR' _ Hli' _ _ _]; exact (proj1 (unit_invariant_canon Hli')). }
    assert (Ed : decode_units (fus_file fp (unit_result_unit r) (unit_result_units r)) = (fp, decode_unit (unit_result_unit r)) :: decode_units (unit_result_units r))
      by exact (decode_units_file _ _ _ _ Hu Hut Hc).
    assert (Hg : ⊢ᵍ gds_restrict (p_union D (fp :: unit_result_imports r)) (decode_units (load_units s fp r)) ⍮ decode_stack fs).
    { pose proof (post_cmd_gctx H Hok) as Hg; unfold load_state in Hg; cbn [run_state_core_imports run_state_core_deps run_state_core_stack] in Hg.
      change (decode_units (load_units s fp r)) with (decode_units (fus_file fp (unit_result_unit r) (unit_result_units r))); rewrite Ed; exact Hg. }
    pose proof (post_cmd_global H Hok) as G'; unfold load_state in G'; cbn [run_state_core_deps run_state_core_closures] in G'.
    destruct (load_values H Hn Hnch Hr0 Hc Ed Hg G') as [Huv Hfv].
    constructor; [| | | | exact Huv | exact Hfv ]; unfold run_state_read, load_units; cbn [run_state_units run_state_closures run_state_imports run_state_builtins run_state_frames].
    - change (decode_units (fus_see _ _)) with (decode_units (fus_file fp (unit_result_unit r) (unit_result_units r))); rewrite Ed; exact Hok.
    - apply units_rep_drop_see, units_rep_drop_with_visible.
      change (decode_units (fus_see _ _)) with (decode_units (fus_file fp (unit_result_unit r) (unit_result_units r))).
      rewrite Ed; exact (units_rep_drop_file _ _ _ _ _ Hu Hut).
    - exact Hv.
    - exact (pre_frames _ _ _ _ _ H).
  Qed.

  (** An [eval] rejected: its type no type, or its term not of it *)
  Definition eval_error (F : FCtx) (HΓ : ⊢ fc_deps F ⍮ fc_stack F ⍮ fc_tele F) (M A : exp) : run_error :=
    match check_type F (lvd _ _) (fc_tele F) HΓ A with
    | inright _ => blame_error (fc_frames F) (find_level_blame F (lvd _ _) (fc_tele F) HΓ A)
                     (mod_error F None (A :: nil) (run_error_eval_typ (fc_frames F) M A))
    | inleft _ => mod_error F None (M :: nil) (field_error F None (lvd _ _) HΓ M (run_error_eval_check (fc_frames F) M A))
    end.

  (** *** One Core Command *)

  Equations core_step (ch : list path) (L : loader ch) (s : funits) (K : unit_closure_map) (D : list path) (B : builtins) (fs : fstack)
    (c : core_cmd) (H : pre ch s K D fs) : step_result ch s K D B fs c :=
  | ch, L, s, K, D, B, fs, core_cmd_def x b pv κ A oM, H => frames_step H (def_step ch s K D B fs x b pv κ A oM H)
  | ch, L, s, K, D, B, fs, core_cmd_mod_open x pv Δ, H => frames_step H (mod_open_step ch s K D B fs x pv Δ H)
  | ch, L, s, K, D, B, fs, core_cmd_close x pv, H => frames_step H (close_step ch s K D B fs x pv H)
  | ch, L, s, K, D, B, fs, core_cmd_alias x pv Δ E, H => frames_step H (alias_step ch s K D B fs x pv Δ E H)
  | ch, L, s, K, D, B, fs, core_cmd_load fp, H with opt_case (fus_find s fp) => {
    | inleft (exist _ u HU) with opt_case (unit_closure_builtins K fp) => {
      | inright _ => run_failure (run_error_msg "internal error: a filed unit has no record")
      | inleft (exist _ BU HB) with inspect (builtins_merge B BU) => {
        | exist _ None _ => run_failure (run_error_msg (bound_msg B))
        | exist _ (Some B') Hm with in_dec path_eq_dec fp D => {
          | left Hin => run_success (exist _ _ (state_res H (load_in_ok Hin (units_found H HU) HB Hm)), log_nil)
          | right Hnin with opt_case (unit_closure_find K fp) => {
            | inleft (exist _ Dfp HK) => run_success (exist _ _ (see_res (fp :: Dfp) H (load_hit_ok Hnin (units_found H HU) HK HB Hm)), log_nil)
            | inright _ => run_failure (run_error_msg "internal error: a filed unit has no closure") } } } }
    | inright Hn with in_dec path_eq_dec fp ch => {
      | left _ => run_failure (run_error_cycle (cycle_chain fp ch))
      | right Hnch with opt_case (load_path fp) => {
        | inright _ => run_failure (run_error_unit fp "cannot find unit")
        | inleft (exist _ src Hsrc) with opt_case (read src) => {
          | inright _ => run_failure (run_error_unit fp "cannot parse unit")
          | inleft (exist _ prg Hprg) with path_eq_dec (prog_path prg) fp => {
            | right _ => run_failure (run_error_unit fp "the file of the unit declares another unit")
            | left Hp with opt_case (to_core prg) => {
              | inright _ => run_failure (run_error_unit fp "cannot elaborate unit")
              | inleft (exist _ u Hu)
                  with L fp src Hnch Hsrc s K u (load_pre (pre_unit_invariant _ _ _ _ _ H) (units_none H Hn) Hnch) (pre_units _ _ _ _ _ H)
                         (pre_unit_values _ _ _ _ _ H) => {
                | run_failure e => run_failure e
                | run_success (exist _ r Hr, _) with inspect (builtins_merge B (unit_result_builtins r)) => {
                  | exist _ None _ => run_failure (run_error_msg (bound_msg B))
                  | exist _ (Some B') Hm => run_success (exist _ _ (load_res H Hn Hnch Hsrc Hprg Hp Hu Hr Hm), log_nil) } } } } } } } }
  | ch, L, s, K, D, B, fs, core_cmd_open E its, H with check_modexp (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) E => {
    | right _ => run_failure (run_error_import (open_failure_reason_target E))
    | left HE with inspect (import_gen (cmd_F B H) (pre_gctx_f B H) (fc_tele (cmd_F B H)) E E HE its) => {
      | exist _ (open_failure e) _ => run_failure (run_error_import e)
      | exist _ (open_success gs) Eg with gens_impl ch s K D B fs gs H => {
        | run_failure e => run_failure e
        | run_success (exist _ fs' (conj Hgs Hf)) =>
            run_success (exist _ (mk_run_state s K D B fs')
                           (frames_res H (conj (open_ok (cmd_modexp B H nil E HE) (cmd_open_gens B H E its gs HE Eg) Hgs) Hf)), log_nil) } } }
  | ch, L, s, K, D, B, fs, core_cmd_eval M A, H with check_exp (cmd_F B H) (lvd _ _) (fc_tele (cmd_F B H)) (pre_ctx_f B H) A M => {
    | left HM => run_success (exist _ _ (state_res H (eval_ok (cmd_exp B H nil M A HM))), eval_log (cmd_F B H) (pre_gctx_f B H) M A HM)
    | right _ => run_failure (eval_error (cmd_F B H) (pre_ctx_f B H) M A) }
  | ch, L, s, K, D, B, fs, core_cmd_inductive pv R, H => ind_step ch s K D B fs pv R H
  | ch, L, s, K, D, B, fs, core_cmd_mdef b pv Δ fns, H => frames_step H (mdef_step ch s K D B fs b pv Δ fns H)
  | ch, L, s, K, D, B, fs, core_cmd_builtin k E, H with builtin_step ch s K D B fs k E H => {
    | run_failure e => run_failure e
    | run_success Hp => run_success (builtins_ok H Hp, log_nil) }
  | ch, L, s, K, D, B, fs, core_cmd_inductive_alias x pv Δ E, H => frames_step H (indalias_step ch s K D B fs x pv Δ E H)
  | ch, L, s, K, D, B, fs, core_cmd_record_alias x pv Δ E, H => frames_step H (recalias_step ch s K D B fs x pv Δ E H)
  | ch, L, s, K, D, B, fs, core_cmd_record_open x pv Δ Srt fds, H => record_open_step ch s K D B fs x pv Δ Srt fds H.

  (** *** Items

      The weight of an item: a core command one; a command as written two,
      a module or a record three and its body's, which is more than the
      items it is filled to weigh ([fill_cmd_weight]). *)

  Fixpoint surface_cmd_weight (c : surface_cmd) : nat :=
    match c with
    | surface_cmd_mod _ _ _ cs => 3 + list_sum (List.map surface_cmd_weight cs)
    | surface_cmd_record _ _ _ _ _ cs => 3 + list_sum (List.map surface_cmd_weight cs)
    | _ => 2
    end.

  Lemma surface_cmd_weight_pos : forall c, 1 <= surface_cmd_weight c.
  Proof. intros []; cbn [surface_cmd_weight]; lia. Qed.

  Definition item_weight (it : cmd_item) : nat :=
    match it with
    | ci_written c => surface_cmd_weight c
    | ci_core _ => 1
    end.

  Definition items_weight (its : list cmd_item) : nat := list_sum (List.map item_weight its).

  Lemma items_weight_cons : forall it its, items_weight (it :: its) = item_weight it + items_weight its.
  Proof. reflexivity. Qed.

  Lemma items_weight_app : forall l1 l2, items_weight (l1 ++ l2) = items_weight l1 + items_weight l2.
  Proof. intros; unfold items_weight; rewrite List.map_app, list_sum_app; reflexivity. Qed.

  Lemma items_weight_written : forall cs, items_weight (List.map ci_written cs) = list_sum (List.map surface_cmd_weight cs).
  Proof. intros; unfold items_weight; rewrite List.map_map; reflexivity. Qed.

  (** A command as written weighs more than the items it is filled to. *)
  Lemma fill_cmd_weight : forall Θ Ξ B c its, fill_cmd Θ Ξ B c its -> items_weight its < surface_cmd_weight c.
  Proof.
    intros * Hf; inversion Hf; subst; cbn [surface_cmd_weight]; rewrite ?items_weight_cons, ?items_weight_app, ?items_weight_cons, ?items_weight_written;
      cbn [item_weight]; unfold items_weight; cbn; lia.
  Qed.

  (** The items of a run, one after the other: a command as written checked
      for privacy, filled ([fill_cmd_fn]), its items run, then the rest; a
      core command run by [core_step], then the rest. *)
  Equations items_impl (ch : list path) (L : loader ch) (its : list cmd_item) (s : funits) (K : unit_closure_map) (D : list path) (B : builtins)
    (fs : fstack) (H : pre ch s K D fs) :
    run_result ({r | fast_res (post_cmds ch (decode_units s) K D B (decode_stack fs) its) r} * certified_log)%type
    by wf (items_weight its) lt :=
  | ch, L, nil, s, K, D, B, fs, H => run_success (exist _ _ (same_res H nil_ok), log_nil)
  | ch, L, ci_core c :: its', s, K, D, B, fs, H with core_step ch L s K D B fs c H => {
    | run_failure e => run_failure (run_error_nat (cmd_view s D) fs (nat_view_f (cmd_F B H) B) (open_error (cmd_F B H) (pre_gctx_f B H) c e))
    | run_success (exist _ r1 Hr1, l1)
        with items_impl ch L its' (run_state_units r1) (run_state_closures r1) (run_state_imports r1) (run_state_builtins r1)
               (run_state_frames r1) (cmd_pre_f H Hr1) => {
      | run_failure e => run_failure e
      | run_success (exist _ r2 Hr2, l2) => run_success (exist _ r2 (core_cons_res Hr1 Hr2), log_app l1 l2) } }
  | ch, L, ci_written c :: its', s, K, D, B, fs, H with refs_check (cmd_F B H) (pre_gctx_f B H) (cmd_refs c) => {
    | inleft (exist _ e _) => run_failure (run_error_nat (cmd_view s D) fs (nat_view_f (cmd_F B H) B) (privacy_run_error e))
    | inright Hac with inspect (fill_cmd_fn (cmd_F B H) B (lvd _ _) (pre_gctx_f B H) c) => {
      | exist _ (fill_error e) _ =>
          run_failure (run_error_nat (cmd_view s D) fs (nat_view_f (cmd_F B H) B) (fill_blame (cmd_F B H) B (pre_gctx_f B H) (pre_ctx_f B H) c e))
      | exist _ (fill_ok its1) Ea with items_impl ch L its1 s K D B fs H => {
        | run_failure e => run_failure e
        | run_success (exist _ r1 Hr1, l1)
            with items_impl ch L its' (run_state_units r1) (run_state_closures r1) (run_state_imports r1) (run_state_builtins r1)
                   (run_state_frames r1) (cmds_pre_f H Hr1) => {
          | run_failure e => run_failure e
          | run_success (exist _ r2 Hr2, l2) =>
              run_success (exist _ r2 (written_cons_res (cmd_acc B H _ Hac) (cmd_fill B H _ _ (fill_cmd_fn_sound _ _ _ _ _ _ Ea)) Hr1 Hr2),
                           log_app l1 l2) } } } }.
  Solve All Obligations with
    intros; rewrite ?items_weight_cons; cbn [item_weight] in *;
    repeat match goal with
      | Ea : fill_cmd_fn _ _ _ _ _ = fill_ok _ |- _ =>
          pose proof (fill_cmd_weight _ _ _ _ _ (fill_cmd_fn_sound _ _ _ _ _ _ Ea)); clear Ea
      | c : surface_cmd |- _ => pose proof (surface_cmd_weight_pos c); clear c
      end; lia.

  (** *** Units *)

  (** Seeing no unit keeps the values of the units filed right. *)
  Lemma units_values_unseen : forall K s, units_values_ok K s -> units_values_ok K (fus_with_visible s (PM.empty _)).
  Proof. intros K s [Hf _]; constructor; [ exact Hf | intros fp u Hu; unfold path_key_find in Hu; cbn in Hu; discriminate ]. Qed.

  (** Nothing filed, nothing seen *)
  Lemma units_values_empty : units_values_ok nil funits_empty.
  Proof. constructor; intros fp u Hu; unfold fus_find, path_key_find in Hu; cbn in Hu; discriminate. Qed.

  (** A unit's run starts with nothing open. *)
  Lemma unit_pre_f {ch s K} : global_invariant ch (decode_units s) K -> units_rep (funits_drop s) (decode_units s) -> units_values_ok K s ->
      pre ch (fus_with_visible s (PM.empty _)) K nil nil.
  Proof.
    intros G Hs Hsv; constructor;
      [ exact (unit_pre G) | exact (units_rep_drop_with_visible _ _ _ Hs) | apply visible_rep_nil | reflexivity | exact (units_values_unseen _ _ Hsv) | exact I ].
  Qed.

  (** Where a unit's imports end, nothing is open. *)
  Lemma unit_mid_pre {ch s K imps} {r1 : run_state} : global_invariant ch (decode_units s) K ->
      fast_res (post_cmds ch (decode_units s) K nil builtins_empty nil imps) r1 -> pre ch (run_state_units r1) (run_state_closures r1) (run_state_imports r1) nil.
  Proof.
    intros G [Hp Hu Hv _ Huv _]; destruct (unit_imports G Hp) as (ΘR1 & _ & _ & _ & Hli1 & _).
    constructor; [ exists ΘR1; exact Hli1 | exact Hu | exact Hv | reflexivity | exact Huv | exact I ].
  Qed.

  (** The unit's own frame, opened *)
  Lemma pre_push_unit {ch s K D fp P} : pre ch s K D nil ->
      (exists ΘR, unit_invariant ch (decode_units s) K D ΘR (gs_push (q_abs fp nil) P nil)) -> pre ch s K D (fs_push (q_abs fp nil) P nil).
  Proof. intros H Hl; apply (pre_cons H); [ reflexivity | exact Hl ]. Qed.

  (** A unit run: its own frame, the only one left, filed as the unit,
      fast *)
  Lemma unit_res {fp ch s K imps P0 P l cs} (r1 r2 : run_state) {f} : global_invariant (fp :: ch) (decode_units s) K ->
      fast_res (post_cmds (fp :: ch) (decode_units s) K nil builtins_empty nil (List.map ci_written imps)) r1 ->
      fill_params (gds_restrict (run_state_imports r1) (decode_units (run_state_units r1))) nil (run_state_builtins r1) P0 P ->
      all_assumptions P ->
      ⊢ gds_restrict (run_state_imports r1) (decode_units (run_state_units r1)) ⍮ nil ⍮ P ->
      params_evaluated (gds_restrict (run_state_imports r1) (decode_units (run_state_units r1))) nil nil P l ->
      acc_ok (gds_restrict (run_state_imports r1) (decode_units (run_state_units r1))) nil (tele_refs nil P0) ->
      fast_res (post_cmds (fp :: ch) (decode_units (run_state_units r1)) (run_state_closures r1) (run_state_imports r1) (run_state_builtins r1)
                  (decode_stack (fs_push (q_abs fp nil) P nil)) (List.map ci_written cs)) r2 ->
      run_state_frames r2 = f :: nil ->
      unit_run_ok (fp :: ch) s K (imps, P0, cs) (mk_unit_result (run_state_units r2) (run_state_closures r2) (run_state_imports r2) (run_state_builtins r2) (fu_mk (ff_params f) (fmd_body (ff_body f)))).
  Proof.
    intros G Hr1 Hfa Htel HP HPr Hac Hr2 HΞ.
    destruct (unit_body_pre G (fres_post _ _ Hr1) Htel HP HPr) as [ΘR1 Hli1].
    destruct (unit_invariant_builtin_records Hli1) as [RbR1 Hrb1].
    destruct Hr1 as [Hp1 _ _ _]; destruct Hr2 as [Hp2 Hu _ Hf Huv Hfv].
    destruct (Hp2 _ _ Hli1 Hrb1) as [ΘR2 RbR2 Hrun Hli2 _ _ _];
      cbn [run_state_read run_state_core_stack run_state_core_deps run_state_core_imports run_state_core_closures] in Hrun, Hli2.
    rewrite HΞ in Hrun, Hli2, Hf, Hfv.
    pose proof (proj1 (proj2 (run_bottom load_path read to_core)) _ _ _ _ _ _ _ _ _ _ Hrun) as Hb.
    destruct f as [mp Kf Δ t]; cbn in Hb; injection Hb as -> -> ->.
    assert (Est : run_state_core_stack (run_state_read r2) = decode_frame (mk_fframe (q_abs fp nil) fk_module P t) :: nil)
      by (cbn [run_state_read run_state_core_stack]; rewrite HΞ; reflexivity).
    pose proof (unit_ok Hp1 Hfa Htel HP HPr Hac Hp2 Est) as Hpost.
    constructor.
    - exact Hpost.
    - exact Hu.
    - pose proof (frame_body_translate _ _ Hf) as Ht; cbn [ff_body] in Ht.
      cbn [unit_result_unit decode_unit translate_unit funit_drop fmoddef_drop ff_params ff_body]; rewrite Ht; reflexivity.
    - exact Huv.
    - intros fq Efq; injection Efq as <-; cbn [unit_result_unit unit_result_imports unit_result_units ff_params ff_body].
      pose proof (ui_global _ _ _ _ _ _ Hli2) as G2.
      assert (Hn : gds_lookup (gds_restrict (run_state_imports r2) (decode_units (run_state_units r2))) fp = None)
        by (rewrite gds_lookup_restrict, (gi_chain _ _ _ G2 fp (or_introl eq_refl)); destruct (existsb _ _); reflexivity).
      pose proof (unit_invariant_restrict_gctx Hli2) as Hfwf.
      exact (ftrie_values_grow _ _ _ _ (gc_sub_file _ fp _ Hn) Hfwf (wf_gstack_file _ _ _ Hfwf) _ (proj1 Hfv)).
  Qed.

  (** The error of a rejected telescope: the first open in it that
      generates nothing, if any, otherwise the error found. *)
  Definition tele_error (F : FCtx) (Hg : ⊢ᵍ fc_deps F ⍮ fc_stack F) (S : skeleton) (Δ : ctx) (e : run_error) : run_error :=
    match tele_open_error F Hg (mod_check F Hg) S Δ with
    | Some e' => run_error_import e'
    | None => e
    end.

  (** A unit: its imports, its parameters filled and checked, then its
      body in its own frame, which must be the only one left. *)
  Definition run_unit_step (ch : list path) (L : loader ch) (s : funits) (K : unit_closure_map) (u : surface_compilation_unit)
    (G : global_invariant ch (decode_units s) K) (Hs : units_rep (funits_drop s) (decode_units s)) (Hsv : units_values_ok K s) :
    run_result ({r | unit_run_ok ch s K u r} * certified_log)%type :=
    match ch as ch0 return loader ch0 -> global_invariant ch0 (decode_units s) K -> run_result ({r | unit_run_ok ch0 s K u r} * certified_log)%type with
    | nil => fun _ _ => run_failure (run_error_msg "internal error: no unit to run")
    | fp :: ch0 => fun L G =>
    match u as u0 return run_result ({r | unit_run_ok (fp :: ch0) s K u0 r} * certified_log)%type with
    | (imps, P0, cs) =>
        match items_impl (fp :: ch0) L (List.map ci_written imps) (fus_with_visible s (PM.empty _)) K nil builtins_empty nil (unit_pre_f G Hs Hsv) with
        | run_failure e => run_failure e
        | run_success (exist _ r1 Hr1, l1) =>
            let H1 := unit_mid_pre G Hr1 in
            let F1 := cmd_F (run_state_builtins r1) H1 in
            let Hg1 := pre_gctx_f (run_state_builtins r1) H1 in
            let nat_err := run_error_nat (cmd_view (run_state_units r1) (run_state_imports r1)) nil (nat_view_f F1 (run_state_builtins r1)) in
            match inspect (fill_params_fn F1 (run_state_builtins r1) (lvd _ _) Hg1 P0) with
            | exist _ (fill_error e) _ => run_failure (nat_err (fill_run_error F1 Hg1 None e))
            | exist _ (fill_ok P) Ea =>
            match all_assumptions_dec P with
            | right _ => run_failure (nat_err (tele_error F1 Hg1 nil P (run_error_msg "unit parameters that are not assumptions")))
            | left Htel =>
            match check_ctx F1 (lvd _ _) Hg1 P with
            | right _ =>
                run_failure (nat_err (tele_error F1 Hg1 nil P (tele_blame_error nil (find_tele_blame F1 (lvd _ _) nil (wf_ctx_empty _ _ Hg1) P)
                        (run_error_msg "ill-formed unit parameters"))))
            | left HP =>
            match params_evaluated_dec F1 Hg1 nil P with
            | inright _ => run_failure (nat_err (run_error_param_prop "the unit"))
            | inleft (exist _ l HPr) =>
            match refs_check F1 Hg1 (tele_refs nil P0) with
            | inleft (exist _ e _) => run_failure (nat_err (privacy_run_error e))
            | inright Hac =>
                let HP' := cmd_ctx_at (run_state_builtins r1) H1 P HP in
                let HPr' := cmd_params_evaluated_at (run_state_builtins r1) H1 nil P l HPr in
                match items_impl (fp :: ch0) L (List.map ci_written cs) (run_state_units r1) (run_state_closures r1) (run_state_imports r1)
                        (run_state_builtins r1) (fs_push (q_abs fp nil) P nil)
                        (pre_push_unit H1 (unit_body_pre G (fres_post _ _ Hr1) Htel HP' HPr')) with
                | run_failure e => run_failure e
                | run_success (exist _ r2 Hr2, l2) =>
                    match run_state_frames r2 as fr return run_state_frames r2 = fr -> run_result ({r | unit_run_ok (fp :: ch0) s K (imps, P0, cs) r} * certified_log)%type with
                    | f :: nil => fun HΞ =>
                        run_success (exist _ _ (unit_res (s := s) r1 r2 G Hr1
                                                  (cmd_fill_params (run_state_builtins r1) H1 _ _ (fill_params_fn_sound F1 (run_state_builtins r1) (lvd _ _) Hg1 _ _ Ea))
                                                  Htel HP' HPr' (cmd_acc (run_state_builtins r1) H1 _ Hac) Hr2 HΞ),
                                     log_app l1 l2)
                    | _ => fun _ => run_failure (run_error_msg "the body of a unit does not end in its own frame")
                    end eq_refl
                end
            end
            end
            end
            end
            end
        end
    end
    end L G.

  #[derive(eliminator=no)]
  Equations run_unit_impl (ch : list path) (Hacc : Acc load_step ch) :
    forall s K u, global_invariant ch (decode_units s) K -> units_rep (funits_drop s) (decode_units s) -> units_values_ok K s ->
      run_result ({r | unit_run_ok ch s K u r} * certified_log)%type by struct Hacc :=
  run_unit_impl ch Hacc :=
    run_unit_step ch (fun fp src Hn Hs => run_unit_impl (fp :: ch) (Acc_inv Hacc (load_step_intro Hn Hs))).

  Definition loader_of (ch : list path) (Hacc : Acc load_step ch) : loader ch :=
    fun fp src Hn Hs => run_unit_impl (fp :: ch) (Acc_inv Hacc (load_step_intro Hn Hs)).

  Lemma run_unit_impl_unfold : forall ch Hacc, run_unit_impl ch Hacc = run_unit_step ch (loader_of ch Hacc).
  Proof. intros; exact (run_unit_impl_equation_1 ch Hacc). Qed.

  (** The unit [u] of the program [prg] run like an imported unit, with
      [prg]'s path as the whole chain, nothing filed and no builtin
      binding.  The driver, which has elaborated the program already to
      report an elaboration error, runs its unit by this, so that the
      program is elaborated once ([prog_impl_unit_run]).  The result has
      the bindings the run ends with, which the printer reads.  The log
      holds its own evals; those of the units it loads are checked but
      not returned. *)
  Definition unit_run (prg : Cst.prog) (u : surface_compilation_unit) (Hacc : Acc load_step (prog_path prg :: nil)) :
    run_result (builtins * funits * funit * list eval_entry)%type :=
    match run_unit_impl (prog_path prg :: nil) Hacc funits_empty nil u (global_invariant_nil _) (units_rep_drop_of_rep _ _ units_rep_empty)
            units_values_empty with
    | run_success (exist _ r _, l) => run_success (unit_result_builtins r, funits_drop (unit_result_units r), funit_drop (unit_result_unit r), proj1_sig l)
    | run_failure e => run_failure e
    end.

  Definition prog_impl (prg : Cst.prog) (Hacc : Acc load_step (prog_path prg :: nil)) :
    run_result (builtins * funits * funit * list eval_entry)%type :=
    match to_core prg with
    | None => run_failure (run_error_msg "cannot elaborate the program")
    | Some u => unit_run prg u Hacc
    end.

  (** Run on the unit it elaborates to, the program runs as that unit. *)
  Lemma prog_impl_unit_run : forall prg u Hacc, to_core prg = Some u -> prog_impl prg Hacc = unit_run prg u Hacc.
  Proof. intros * Ht; unfold prog_impl; rewrite Ht; reflexivity. Qed.

  (** ** Soundness

      By construction: a result carries its [post_*], whatever the loader and
      the accessibility proof. *)

  Lemma unit_equiv {ch Θ K u r} :
    global_invariant ch Θ K -> post_unit ch Θ K u r ->
    exists RbU ΘU, run_unit ch u (unit_result_core_builtins r) RbU ΘU (unit_result_core_unit r) /\ global_invariant ch (unit_result_core_deps r) (unit_result_core_closures r) /\
      gds_equiv ΘU (gds_restrict (unit_result_core_imports r) (unit_result_core_deps r)) /\ grows Θ (unit_result_core_deps r) (unit_result_core_imports r) /\
      ΘU ⊑ unit_result_core_deps r /\ set_eq (unit_result_core_imports r) (gds_dom ΘU).
  Proof.
    intros G Hp; destruct (Hp G) as [RbU ΘU Hu G' Hsub Hdom _ _ _ Hgr].
    exists RbU, ΘU; split; [ exact Hu | split; [ exact G' |] ].
    split; [ exact (equiv_restrict _ _ _ Hsub Hdom) |].
    split; [ exact Hgr | split; assumption ].
  Qed.

  (** The run of items reaches the reading of the fast state it ends with;
      the frames it starts at are read the same way. *)
  Theorem items_impl_sound : forall ch L its s K D B fs H r ΘR RbR,
      unit_invariant ch (decode_units s) K D ΘR (decode_stack fs) -> builtin_records_ok K ΘR RbR -> items_impl ch L its s K D B fs H = run_success r ->
      exists ΘR' RbR', ΘR ⍮ decode_stack fs ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ its ⇝*
          ΘR' ⍮ run_state_core_stack (run_state_read (proj1_sig (fst r))) ⍮ run_state_core_builtins (run_state_read (proj1_sig (fst r))) ⍮ RbR' /\
        unit_invariant ch (run_state_core_deps (run_state_read (proj1_sig (fst r)))) (run_state_core_closures (run_state_read (proj1_sig (fst r))))
          (run_state_core_imports (run_state_read (proj1_sig (fst r)))) ΘR' (run_state_core_stack (run_state_read (proj1_sig (fst r)))) /\ logs_ok (proj1_sig (snd r)).
  Proof.
    intros * Hli Hrb _; destruct r as [[r Hr] [l Hl]]; cbn [proj1_sig fst snd]; destruct Hr as [Hr _ _ _]; destruct (Hr _ _ Hli Hrb) as [ΘR' RbR' ? ? _ _ _]; cbn; eauto.
  Qed.

  (** A unit run from the filed units [s], read in Core *)
  Theorem run_unit_impl_sound : forall ch Hacc s K u G Hs Hsv r,
      run_unit_impl ch Hacc s K u G Hs Hsv = run_success r ->
      exists RbU ΘU, run_unit ch u (unit_result_core_builtins (unit_result_read (proj1_sig (fst r)))) RbU ΘU (unit_result_core_unit (unit_result_read (proj1_sig (fst r)))) /\
        global_invariant ch (unit_result_core_deps (unit_result_read (proj1_sig (fst r)))) (unit_result_core_closures (unit_result_read (proj1_sig (fst r)))) /\
        gds_equiv ΘU (gds_restrict (unit_result_core_imports (unit_result_read (proj1_sig (fst r)))) (unit_result_core_deps (unit_result_read (proj1_sig (fst r))))) /\
        logs_ok (proj1_sig (snd r)).
  Proof.
    intros * _; destruct r as [[r Hr] [l Hl]]; cbn [proj1_sig fst snd]; destruct Hr as [Hr _ _]; destruct (unit_equiv G Hr) as (RbU & ΘU & ? & ? & ? & _); cbn; eauto 7.
  Qed.

  (** ** The Program

      Only what the program imports is filed, so the whole accumulated [Θ] is
      equivalent to the judgment's.  Each log entry is an eval of the program,
      typed and normalized in the restriction it was checked in.  The
      program's filed units and its unit are returned fast; the statements
      read them in Core. *)

  Theorem prog_impl_sound : forall prg Hacc B s u log,
      prog_impl prg Hacc = run_success (B, s, u, log) ->
      (exists ΘR, prog_sem load_path read to_core prg B ΘR (decode_unit u) /\ gds_equiv ΘR (decode_units s)) /\
      (forall e, In e log ->
         ⊢ᵍ eval_entry_deps e ⍮ eval_entry_stack e /\ eval_entry_deps e ⍮ eval_entry_stack e ⍮ gs_tele (eval_entry_stack e) ⊢ eval_entry_exp e : eval_entry_typ e /\
         nbe (eval_entry_deps e) (eval_entry_stack e) (gs_tele (eval_entry_stack e)) (eval_entry_exp e) (eval_entry_typ e) (eval_entry_nf e)).
  Proof.
    unfold prog_impl, unit_run; intros * E.
    destruct (to_core prg) as [u0 |] eqn:Ht; [| discriminate ].
    revert E; match goal with |- context [run_unit_impl ?a ?b ?c ?d ?e ?f ?g ?h] =>
      destruct (run_unit_impl a b c d e f g h) as [[[r [Hp _ _]] [l Hl]] | e'] end; intros E; [| discriminate ].
    injection E as <- <- <- <-; rewrite decode_unit_drop, decode_units_drop; split; [| intros e He; destruct (Hl e He) as [Hw Ht' Hn]; auto ].
    destruct (unit_equiv (global_invariant_nil _) Hp) as (RbU & ΘU & Hu & G & _ & Hgr & Hsub & Hdom).
    cbn [unit_result_read unit_result_core_deps unit_result_core_imports unit_result_core_unit unit_result_core_builtins unit_result_core_closures] in *.
    exists ΘU; split; [ exists u0 RbU; assumption |].
    split; [ exact Hsub |].
    intros y V HV.
    destruct (Hgr y ltac:(apply gds_dom_lookup; rewrite HV; discriminate)) as [[] | Hy].
    apply Hdom, gds_dom_lookup in Hy; destruct (gds_lookup ΘU y) as [V' |] eqn:E; [| contradiction ].
    rewrite (Hsub _ _ E) in HV; injection HV as ->; reflexivity.
  Qed.

  (** The program's fast results refine their reading. *)
  Theorem prog_impl_rep : forall prg Hacc B s u log,
      prog_impl prg Hacc = run_success (B, s, u, log) -> units_rep s (decode_units s) /\ u = translate_unit (decode_unit u).
  Proof.
    unfold prog_impl, unit_run; intros * E.
    destruct (to_core prg) as [u0 |]; [| discriminate ].
    revert E; match goal with |- context [run_unit_impl ?a ?b ?c ?d ?e ?f ?g ?h] =>
      destruct (run_unit_impl a b c d e f g h) as [[[r [_ Hs Hu]] l] | e'] end; intros E; [| discriminate ].
    injection E as <- <- <- <-; rewrite decode_units_drop, decode_unit_drop; split; assumption.
  Qed.
End Impl.
