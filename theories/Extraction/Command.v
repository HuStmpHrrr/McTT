(** * Running Commands

    The executable for [Core.Syntactic.System.Command].  It is sound by
    construction, since every result carries its [post_*], and complete by
    [run_impl_complete].

    A run maintains:

    - one [Θ] for the whole program, in which every loaded unit is filed once;
    - a table [K] giving the closure of each filed unit, that is, the paths
      of the state its own run ended in;
    - for the unit being run, the closure [D] of what it has imported so far.

    A unit is checked against [gds_restrict D Θ], which [equiv_restrict]
    relates to the judgment's state by weakening in both directions.  Loading
    recurses on the accessibility of the import chain ([load_step]).

    Each command is expanded ([Imports]) with the member-type oracle of the
    restriction ([mt_of]), which meets the specification of the judgment's
    state too ([linv_mt_spec]), so the expansion is the judgment's.

    A run also logs each [eval] it checked, with its normal form
    ([eval_entry], certified by [eval_ok]), and fails with a [run_error]
    carrying the terms involved. *)

From Stdlib Require Import List String Wellfounded Wf_nat.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base Soundness.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import Structural Command.
From Mctt.Extraction Require Import NbE TypeCheck GlobalCheck MemberType Privacy.
Import Syntax_Notations GlobalCtx_Notations.

Local Open Scope string_scope.

(** ** Deciders *)

Definition opt_case {A} (o : option A) : {a | o = Some a} + {o = None} :=
  match o as o0 return {a | o0 = Some a} + {o0 = None} with
  | Some a => inleft (exist _ a eq_refl)
  | None => inright eq_refl
  end.

Definition list_case {A} (l : list A) : {x : A & {l' | l = x :: l'}} + {l = nil} :=
  match l as l0 return {x : A & {l' | l0 = x :: l'}} + {l0 = nil} with
  | x :: l' => inleft (existT _ x (exist _ l' eq_refl))
  | nil => inright eq_refl
  end.

Definition gs_fresh_dec (x : string) (Ξ : gstack) : {gs_fresh x Ξ} + {~ gs_fresh x Ξ} :=
  match Ξ as Ξ0 return {gs_fresh x Ξ0} + {~ gs_fresh x Ξ0} with
  | (_, U) :: _ => check_gm_fresh x (gu_mod U)
  | nil => right (fun H => H)
  end.

(** ** Closures and Paths *)

Definition kmap : Set := list (path * list path).

Equations kfind (K : kmap) (fp : path) : option (list path) by struct K :=
| nil, _ => None
| (fq, D) :: K', fp => if path_beq fp fq then Some D else kfind K' fp.

Definition p_union (A B : list path) : list path :=
  fold_right (fun x acc => if in_dec path_eq_dec x acc then acc else x :: acc) A B.

Lemma p_union_iff : forall A B x, In x (p_union A B) <-> In x A \/ In x B.
Proof.
  intros A B; unfold p_union; induction B as [| y B IH]; intros x; cbn [fold_right In]; [ tauto |].
  destruct (in_dec path_eq_dec y _) as [Hy | Hy]; rewrite IH in *; cbn [In]; rewrite ?IH.
  - split; [ tauto | intros [H | [<- | H]]; tauto ].
  - tauto.
Qed.

Definition path_str (fp : path) : string := String.concat "::" fp.

(** The chain up to the unit imported again, where the cycle starts. *)
Equations chain_to (fp : path) (ch : list path) : list path by struct ch :=
| _, nil => nil
| fp, fq :: ch' => if path_beq fp fq then fq :: nil else fq :: chain_to fp ch'.

(** The cycle, from the unit imported again back to itself. *)
Definition cycle_chain (fp : path) (ch : list path) : list path :=
  List.app (rev (chain_to fp ch)) (fp :: nil).

Definition cycle_msg (cyc : list path) : string :=
  "cyclic import: " ++ String.concat " -> " (map path_str cyc).

(** ** Results

    The errors a run can fail with, carrying the terms involved, if any, for
    the driver to print.  The message of [re_unit] concerns the unit at the
    path it carries and does not repeat that path. *)

Inductive run_error : Set :=
| re_msg : string -> run_error
(** The body of a definition is not of its declared type, which is a type. *)
| re_def : string -> gstack -> typ -> exp -> run_error
(** The declared type of a definition with a body is not a type. *)
| re_def_typ : string -> gstack -> typ -> run_error
(** An ascribed eval: the term is not of its ascription, which is a type. *)
| re_eval_check : gstack -> exp -> typ -> run_error
(** An ascribed eval: the ascription of the term is not a type. *)
| re_eval_typ : gstack -> exp -> typ -> run_error
| re_eval_infer : gstack -> exp -> run_error
(** A small universe [Type@{t}] whose level [t] is of no type of levels,
    found by [find_level_blame] where a type or a telescope is rejected:
    [t] lives in the context the stack's telescope is extended by, innermost
    entry first. *)
| re_level : gstack -> ctx -> exp -> run_error
| re_cycle : list path -> run_error
| re_unit : path -> string -> run_error
(** A private member, named by its module, reached from outside it. *)
| re_private : qname -> string -> run_error
(** A private entry of a local body, by the chain of submodules from the
    local module, reached from outside it. *)
| re_private_local : list string -> string -> run_error
(** An import that generates nothing ([Imports]). *)
| re_import : xerr -> run_error.

Definition priv_error (e : priv_err) : run_error :=
  match e with
  | pe_global qd x => re_private qd x
  | pe_local ch x => re_private_local ch x
  end.

(** The error for a rejected type or telescope: the blamed level if
    [find_level_blame] found one, otherwise the given error. *)
Definition blame_error {Θ Ξ Γ} (b : option (level_blame Θ Ξ Γ)) (e : run_error) : run_error :=
  match b with
  | Some (exist _ (Δ, t) _) => re_level Ξ Δ t
  | None => e
  end.

Definition tele_blame_error {Θ Ξ Γ Δ} (b : option (level_blame Θ Ξ Γ) + { ⊢ Θ ⍮ Ξ ⍮ (Δ ++ Γ) })
    (e : run_error) : run_error :=
  match b with
  | inleft ob => blame_error ob e
  | inright _ => e
  end.

Inductive rres (A : Type) : Type :=
| rok : A -> rres A
| rerr : run_error -> rres A.

Arguments rok {A}.
Arguments rerr {A}.

(** A checked and normalized [eval]: in the restriction [ev_deps] of the
    state to the imports so far, on the stack [ev_stack], and in the context
    of the frames' parameters, the expression [ev_exp] has type [ev_typ]
    (ascribed or inferred) and normalizes to [ev_nf]. *)
Record eval_entry : Set :=
  { ev_deps : gdeps; ev_stack : gstack; ev_exp : exp; ev_typ : typ; ev_nf : nf }.

Definition eval_ok (e : eval_entry) : Prop :=
  ⊢g ev_deps e ⍮ ev_stack e /\ ev_deps e ⍮ ev_stack e ⍮ gs_tele (ev_stack e) ⊢ ev_exp e : ev_typ e /\
    nbe (ev_deps e) (ev_stack e) (gs_tele (ev_stack e)) (ev_exp e) (ev_typ e) (ev_nf e).

Definition logs_ok (l : list eval_entry) : Prop := forall e, In e l -> eval_ok e.

(** The log of a run, in program order, with every entry certified. *)
Definition elog : Set := {l | logs_ok l}.

Definition log_nil : elog := exist logs_ok nil (fun e (H : In e nil) => False_ind _ H).

Definition log_app (l1 l2 : elog) : elog.
Proof.
  refine (exist _ (List.app (proj1_sig l1) (proj1_sig l2)) _).
  abstract (intros e He; apply in_app_or in He as [He | He]; [ exact (proj2_sig l1 _ He) | exact (proj2_sig l2 _ He) ]).
Defined.

Lemma typed_nbe_order {Θ Ξ Γ M A} : Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> nbe_order Θ Ξ Γ M A.
Proof. intros H; destruct (soundness_gctx _ _ _ _ _ H) as (W & HW & _); exact (nbe_order_sound _ _ _ _ _ _ HW). Qed.

(** Normalize a checked [eval] into its entry. *)
Lemma eval_log_ok {Θ Ξ M A W} : ⊢g Θ ⍮ Ξ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A -> nbe Θ Ξ (gs_tele Ξ) M A W ->
  logs_ok ({| ev_deps := Θ; ev_stack := Ξ; ev_exp := M; ev_typ := A; ev_nf := W |} :: nil).
Proof. intros HΞ HM HW e [<- | []]; unfold eval_ok; cbn; auto. Qed.

Definition eval_log (Θ : gdeps) (Ξ : gstack) (HΞ : ⊢g Θ ⍮ Ξ) (M : exp) (A : typ)
  (HM : Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A) : elog :=
  match nbe_impl Θ Ξ (gs_tele Ξ) M A (typed_nbe_order HM) with
  | exist _ W HW => exist _ _ (eval_log_ok HΞ HM HW)
  end.

Lemma sub_none : forall Θ Θ' fp, Θ ⊑ Θ' -> gds_lookup Θ' fp = None -> gds_lookup Θ fp = None.
Proof. intros * Hs Hn; destruct (gds_lookup Θ fp) eqn:E; [ rewrite (Hs _ _ E) in Hn; discriminate | reflexivity ]. Qed.

Lemma sub_dom : forall Θ Θ' fp, Θ ⊑ Θ' -> In fp (gds_dom Θ) -> In fp (gds_dom Θ').
Proof.
  intros * Hs H; rewrite gds_dom_lookup in *; destruct (gds_lookup Θ fp) eqn:E; [| contradiction ].
  rewrite (Hs _ _ E); discriminate.
Qed.

Lemma dom_merge : forall Θ Θ' fp,
    In fp (gds_dom (gds_merge Θ Θ')) <-> In fp (gds_dom Θ) \/ In fp (gds_dom Θ').
Proof.
  intros; rewrite !gds_dom_lookup; split.
  - intros H; destruct (gds_lookup Θ fp) eqn:E1; [ left; discriminate |].
    right; intros E2; apply H, merge_none; auto.
  - intros [H | H] E; apply merge_none in E as [E1 E2]; contradiction.
Qed.

Lemma dom_cons : forall fp U Θ fq, In fq (gds_dom ((fp, U) :: Θ)) <-> fq = fp \/ In fq (gds_dom Θ).
Proof. intros; cbn; split; intros [H | H]; auto. Qed.

Section Impl.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  #[local] Abbreviation run_cmd := (run_cmd load_path read to_core).
  #[local] Abbreviation run_cmds := (run_cmds load_path read to_core).
  #[local] Abbreviation run_unit := (run_unit load_path read to_core).
  #[local] Abbreviation canon := (canon load_path read to_core).
  #[local] Abbreviation run_wf := (run_wf load_path read to_core).
  #[local] Abbreviation run_functional := (run_functional load_path read to_core).

  (** ** The Invariants *)

  Definition set_eq (A B : list path) : Prop := forall x, In x A <-> In x B.

  (** A set of paths closed under the closures [K] records. *)
  Definition closedK (K : kmap) (D : list path) : Prop :=
    forall x Dx, In x D -> kfind K x = Some Dx -> incl Dx D.

  (** A filed unit is what loading its file yields, under a chain starting
      with it.  The state that run ended in is filed as well, below the unit
      in [Θ], and [K] records its domain, closed. *)
  Definition entry_ok (Θ : gdeps) (K : kmap) (fp : path) (U : gunit) : Prop :=
    exists D, kfind K fp = Some D /\ closedK K D /\
      exists src prg u ch ΘU, load_path fp = Some src /\ read src = Some prg /\ prog_path prg = fp /\
        to_core prg = Some u /\ run_unit (fp :: ch) u ΘU U /\ ΘU ⊑ Θ /\ set_eq D (gds_dom ΘU).

  (** Each filed unit is [entry_ok] for the units below it. *)
  Fixpoint entries_ok (K : kmap) (Θ : gdeps) : Prop :=
    match Θ with
    | nil => True
    | (fp, U) :: Θ' => entry_ok Θ' K fp U /\ entries_ok K Θ'
    end.

  (** The invariant of the global state for a run under chain [ch]; in
      particular, nothing on the chain is filed yet. *)
  Record ginv (ch : list path) (Θ : gdeps) (K : kmap) : Prop :=
    { gi_wf : ⊢g Θ ⍮ nil
    ; gi_chain : forall x, In x ch -> gds_lookup Θ x = None
    ; gi_entry : entries_ok K Θ
    ; gi_kdom : forall fp D, kfind K fp = Some D -> gds_lookup Θ fp <> None }.

  (** The invariant of the unit being run, relative to the judgment's state
      [ΘR]: the units [D] it imported are those of [ΘR], filed identically in
      [Θ]. *)
  Record linv (ch : list path) (Θ : gdeps) (K : kmap) (D : list path) (ΘR : gdeps) (Ξ : gstack) : Prop :=
    { li_g : ginv ch Θ K
    ; li_sub : ΘR ⊑ Θ
    ; li_dom : set_eq D (gds_dom ΘR)
    ; li_closed : closedK K D
    ; li_wf : ⊢g ΘR ⍮ Ξ
    ; li_canon : canon ΘR
    ; li_stack : stack_in ch Ξ }.

  Definition ext (Θ : gdeps) (K : kmap) (Θ' : gdeps) (K' : kmap) : Prop :=
    Θ ⊑ Θ' /\ forall x Dx, kfind K x = Some Dx -> kfind K' x = Some Dx.

  (** Whatever a run files, it imports; hence at the top level the result has
      exactly the domain of the judgment's state. *)
  Definition grows (Θ Θ' : gdeps) (D' : list path) : Prop :=
    forall x, In x (gds_dom Θ') -> In x (gds_dom Θ) \/ In x D'.

  Record cstate : Set := cst { cs_deps : gdeps; cs_k : kmap; cs_dom : list path; cs_stack : gstack }.
  Record ustate : Set := ust { us_deps : gdeps; us_k : kmap; us_dom : list path; us_unit : gunit }.

  Definition post_cmd ch Θ K D Ξ c (r : cstate) : Prop :=
    forall ΘR, linv ch Θ K D ΘR Ξ ->
      exists ΘR', run_cmd ch ΘR Ξ c ΘR' (cs_stack r) /\
        linv ch (cs_deps r) (cs_k r) (cs_dom r) ΘR' (cs_stack r) /\
        ext Θ K (cs_deps r) (cs_k r) /\ grows Θ (cs_deps r) (cs_dom r).

  Definition post_cmds ch Θ K D Ξ cs (r : cstate) : Prop :=
    forall ΘR, linv ch Θ K D ΘR Ξ ->
      exists ΘR', run_cmds ch ΘR Ξ cs ΘR' (cs_stack r) /\
        linv ch (cs_deps r) (cs_k r) (cs_dom r) ΘR' (cs_stack r) /\
        ext Θ K (cs_deps r) (cs_k r) /\ grows Θ (cs_deps r) (cs_dom r).

  (** A command expanded ([Imports]) and run, as [rcs_cons] does. *)
  Definition post_xcmd ch Θ K D Ξ c (r : cstate) : Prop :=
    forall ΘR, linv ch Θ K D ΘR Ξ ->
      exists c' ΘR', cmd_xp_ok ΘR Ξ c c' /\ run_cmd ch ΘR Ξ c' ΘR' (cs_stack r) /\
        linv ch (cs_deps r) (cs_k r) (cs_dom r) ΘR' (cs_stack r) /\
        ext Θ K (cs_deps r) (cs_k r) /\ grows Θ (cs_deps r) (cs_dom r).

  Definition post_unit ch Θ K u (r : ustate) : Prop :=
    ginv ch Θ K ->
      exists ΘU, run_unit ch u ΘU (us_unit r) /\ ginv ch (us_deps r) (us_k r) /\
        ΘU ⊑ us_deps r /\ set_eq (us_dom r) (gds_dom ΘU) /\ closedK (us_k r) (us_dom r) /\
        ext Θ K (us_deps r) (us_k r) /\ grows Θ (us_deps r) (us_dom r).

  (** ** Consequences of the Invariants *)

  Lemma entry_ok_sub : forall Θ1 Θ2 K fp U, Θ1 ⊑ Θ2 -> entry_ok Θ1 K fp U -> entry_ok Θ2 K fp U.
  Proof.
    intros * Hs (D & HK & Hcl & src & prg & u & ch & ΘU & Hl & Hr & Hp & Ht & Hu & Hsub & Hdom).
    exists D; split; [ exact HK | split; [ exact Hcl |] ].
    exists src, prg, u, ch, ΘU; do 5 (split; [ assumption |]); split; [ eapply gds_sub_trans; eassumption | exact Hdom ].
  Qed.

  Lemma entries_ok_lookup : forall K Θ, ⊢g Θ ⍮ nil -> entries_ok K Θ ->
      forall fp U, gds_lookup Θ fp = Some U -> entry_ok Θ K fp U.
  Proof.
    intros K; induction Θ as [| [fq V] Θ IH]; intros Hwf HE fp U HU; [ discriminate |]; destruct HE as [HV HΘ].
    destruct (wf_gstack_file_inv _ _ _ Hwf) as (Hwf0 & _ & Hn).
    apply (entry_ok_sub Θ); [ apply gds_sub_cons, Hn |].
    cbn in HU; destruct (path_beq fp fq) eqn:Hb; [| exact (IH Hwf0 HΘ _ _ HU) ].
    apply path_beq_true in Hb as ->; injection HU as <-; exact HV.
  Qed.

  Lemma ginv_entry {ch Θ K} : ginv ch Θ K -> forall fp U, gds_lookup Θ fp = Some U -> entry_ok Θ K fp U.
  Proof. intros G; exact (entries_ok_lookup _ _ (gi_wf _ _ _ G) (gi_entry _ _ _ G)). Qed.

  Lemma ginv_canon {ch Θ K} : ginv ch Θ K -> canon Θ.
  Proof.
    intros G fp U HU.
    destruct (ginv_entry G _ _ HU) as (D & _ & _ & src & prg & u & ch0 & ΘU & Hl & Hr & _ & Ht & Hu & _).
    exists src, prg, u, ch0, ΘU; repeat split; assumption.
  Qed.

  Lemma entries_closure : forall K D Θ, closedK K D -> entries_ok K Θ -> closure_ok D Θ.
  Proof.
    intros K D; induction Θ as [| [fp U] Θ IH]; intros Hcl HΘ; [ exact I |].
    destruct HΘ as [(Dfp & HK & _ & src & prg & u & ch0 & ΘU & _ & _ & _ & _ & Hu & Hsub & Hdom) HΘ].
    split; [| auto ]; intros Hin.
    destruct (proj2 (proj2 run_wf) _ _ _ _ Hu) as (_ & _ & HwU); cbn [hd] in HwU.
    exists ΘU; split; [ exact HwU | split; [ exact Hsub |] ].
    intros x Hx; apply (Hcl _ _ Hin HK), Hdom, Hx.
  Qed.

  Lemma ginv_restrict_wf {ch Θ K D} : ginv ch Θ K -> closedK K D -> ⊢g gds_restrict D Θ ⍮ nil.
  Proof. intros G Hcl; exact (restrict_wf _ _ (gi_wf _ _ _ G) (entries_closure _ _ _ Hcl (gi_entry _ _ _ G))). Qed.

  Lemma linv_in {ch Θ K D ΘR Ξ} : linv ch Θ K D ΘR Ξ -> forall x, In x D -> gds_lookup Θ x <> None.
  Proof.
    intros Hli x Hx; apply (li_dom _ _ _ _ _ _ Hli), gds_dom_lookup in Hx.
    destruct (gds_lookup ΘR x) eqn:E; [| contradiction ].
    rewrite (li_sub _ _ _ _ _ _ Hli _ _ E); discriminate.
  Qed.

  Lemma linv_equiv {ch Θ K D ΘR Ξ} : linv ch Θ K D ΘR Ξ -> gds_equiv ΘR (gds_restrict D Θ).
  Proof.
    intros Hli; exact (equiv_restrict _ _ _ (li_sub _ _ _ _ _ _ Hli) (li_dom _ _ _ _ _ _ Hli)).
  Qed.

  Lemma linv_restrict_gctx {ch Θ K D ΘR Ξ} : linv ch Θ K D ΘR Ξ -> ⊢g gds_restrict D Θ ⍮ Ξ.
  Proof.
    intros Hli; exact (equiv_gctx _ _ _ (linv_equiv Hli)
                         (ginv_restrict_wf (li_g _ _ _ _ _ _ Hli) (li_closed _ _ _ _ _ _ Hli))
                         (li_wf _ _ _ _ _ _ Hli)).
  Qed.

  Lemma pre_gctx {ch Θ K D Ξ} : (exists ΘR, linv ch Θ K D ΘR Ξ) -> ⊢g gds_restrict D Θ ⍮ Ξ.
  Proof. intros [ΘR Hli]; exact (linv_restrict_gctx Hli). Qed.

  Lemma pre_ctx {ch Θ K D Ξ} : (exists ΘR, linv ch Θ K D ΘR Ξ) -> ⊢ gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ.
  Proof. intros H; exact (wf_gs_tele _ _ (pre_gctx H)). Qed.

  Lemma linv_stack {ch Θ K D ΘR Ξ Ξ'} :
    linv ch Θ K D ΘR Ξ -> ⊢g ΘR ⍮ Ξ' -> stack_in ch Ξ' -> linv ch Θ K D ΘR Ξ'.
  Proof. intros [] H Hs; constructor; assumption. Qed.

  Lemma linv_run_wf {ch Θ K D ΘR Ξ c ΘR' Ξ'} :
    linv ch Θ K D ΘR Ξ -> run_cmd ch ΘR Ξ c ΘR' Ξ' -> ⊢g ΘR' ⍮ Ξ' /\ canon ΘR' /\ ΘR ⊑ ΘR'.
  Proof.
    intros Hli Hr;
      exact (proj1 run_wf _ _ _ _ _ _ Hr (li_wf _ _ _ _ _ _ Hli) (li_canon _ _ _ _ _ _ Hli) (li_stack _ _ _ _ _ _ Hli)).
  Qed.

  Lemma linv_run_stack {ch Θ K D ΘR Ξ c ΘR' Ξ'} :
    linv ch Θ K D ΘR Ξ -> run_cmd ch ΘR Ξ c ΘR' Ξ' -> stack_in ch Ξ'.
  Proof.
    intros Hli Hr; exact (stack_in_shape _ _ _ (proj1 (run_params load_path read to_core) _ _ _ _ _ _ Hr)
                            (li_stack _ _ _ _ _ _ Hli)).
  Qed.

  Lemma linv_run_same {ch Θ K D ΘR Ξ c Ξ'} :
    linv ch Θ K D ΘR Ξ -> run_cmd ch ΘR Ξ c ΘR Ξ' -> linv ch Θ K D ΘR Ξ'.
  Proof.
    intros Hli Hr; apply (linv_stack Hli); [ exact (proj1 (linv_run_wf Hli Hr)) | exact (linv_run_stack Hli Hr) ].
  Qed.

  Lemma linv_push {ch Θ K D ΘR Ξ x Δ} :
    linv ch Θ K D ΘR Ξ -> tele_ass Δ -> gs_fresh x Ξ -> ⊢ gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
    ⊢ ΘR ⍮ Ξ ⍮ Δ ++ gs_tele Ξ /\ linv ch Θ K D ΘR (gs_push (qname_in (gs_path Ξ) x) Δ Ξ).
  Proof.
    intros Hli Htel Hfr HΔ.
    assert (HΔ' : ⊢ ΘR ⍮ Ξ ⍮ Δ ++ gs_tele Ξ)
      by exact (equiv_ctx _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HΔ).
    split; [ exact HΔ' |]; apply (linv_stack Hli); [| exact (stack_in_push _ _ _ _ (li_stack _ _ _ _ _ _ Hli) Hfr) ].
    apply wf_gstack_cons; [ apply (li_wf _ _ _ _ _ _ Hli) | constructor; [ exact Htel | exact HΔ' ] |].
    destruct Ξ as [| [mp U] Ξ]; [ contradiction |]; cbn; exists x; split; [ reflexivity | exact Hfr ].
  Qed.

  (** A unit's own frame: its path heads the chain, so it is not filed. *)
  Lemma linv_push_unit {fp ch Θ K D ΘR P} :
    linv (fp :: ch) Θ K D ΘR nil -> tele_ass P -> ⊢ gds_restrict D Θ ⍮ nil ⍮ P ->
    ⊢ ΘR ⍮ nil ⍮ P /\ linv (fp :: ch) Θ K D ΘR (gs_push (q_abs fp nil) P nil).
  Proof.
    intros Hli Htel HP.
    assert (HP' : ⊢ ΘR ⍮ nil ⍮ P)
      by exact (equiv_ctx _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HP).
    split; [ exact HP' |]; apply (linv_stack Hli); [| intros ? ? [[= <- <-] | []]; left; reflexivity ].
    apply wf_gstack_cons;
      [ apply (li_wf _ _ _ _ _ _ Hli) | constructor; [ exact Htel | cbn; rewrite app_nil_r; exact HP' ] |].
    cbn; split; [| reflexivity ].
    exact (sub_none _ _ _ (li_sub _ _ _ _ _ _ Hli) (gi_chain _ _ _ (li_g _ _ _ _ _ _ Hli) _ (or_introl eq_refl))).
  Qed.

  Lemma ext_refl : forall Θ K, ext Θ K Θ K.
  Proof. split; [ apply gds_sub_refl | auto ]. Qed.

  Lemma ext_trans : forall Θ1 K1 Θ2 K2 Θ3 K3, ext Θ1 K1 Θ2 K2 -> ext Θ2 K2 Θ3 K3 -> ext Θ1 K1 Θ3 K3.
  Proof. intros * [H1 H2] [H3 H4]; split; [ eapply gds_sub_trans; eassumption | auto ]. Qed.

  Lemma grows_refl : forall Θ D, grows Θ Θ D.
  Proof. intros ? ? ? ?; left; assumption. Qed.

  Lemma closedK_cons : forall K T fp Dfp,
      closedK K T -> (forall y, In y T -> y <> fp) -> closedK ((fp, Dfp) :: K) T.
  Proof.
    intros * Hcl Hne y Dy Hy HK; simp kfind in HK; rewrite (path_beq_false _ _ (Hne _ Hy)) in HK; eauto.
  Qed.

  Lemma entries_ok_cons_K : forall K fp Dfp Θ,
      (forall y Dy, kfind K y = Some Dy -> y <> fp) -> (forall y, In y (gds_dom Θ) -> y <> fp) ->
      entries_ok K Θ -> entries_ok ((fp, Dfp) :: K) Θ.
  Proof.
    intros K fp Dfp; induction Θ as [| [fq V] Θ IH]; intros HK Hd HΘ; [ exact I |].
    destruct HΘ as [(Dy & HKy & Hcly & src & prg & u & ch & ΘUy & Hl & Hr & Hp & Ht & Hu & Hsuby & Hdomy) HΘ].
    split; [| apply IH; [ exact HK | intros y Hy; apply Hd; right; exact Hy | exact HΘ ] ].
    exists Dy; simp kfind; rewrite path_beq_false by (eapply HK; eassumption); split; [ exact HKy |].
    split; [ apply closedK_cons; [ exact Hcly | intros z Hz; apply Hd; right; apply (sub_dom _ _ _ Hsuby), Hdomy, Hz ] |].
    exists src, prg, u, ch, ΘUy; do 6 (split; [ assumption |]); exact Hdomy.
  Qed.

  Lemma ginv_nil : forall ch, ginv ch nil nil.
  Proof. intros; constructor; [ constructor | reflexivity | exact I | discriminate ]. Qed.

  Lemma nil_linv {ch Θ K} : ginv ch Θ K -> linv ch Θ K nil nil nil.
  Proof.
    intros G; constructor; [ exact G | discriminate | intros ?; cbn; tauto | intros ? ? [] | | apply canon_nil | intros ? ? [] ].
    constructor; constructor; constructor.
  Qed.

  (** ** Expansion at the Executable's State

      The executable expands with the oracle of the restriction it checks
      against; it meets the specification of the judgment's state too, which
      has the same member types ([linv_equiv]). *)

  Lemma equiv_mt_spec : forall Θ Θ' Ξ mt, gds_equiv Θ Θ' -> mt_spec Θ' Ξ mt -> mt_spec Θ Ξ mt.
  Proof.
    intros * (H1 & H2) Hs; apply (mt_spec_transfer Θ' Ξ); [| exact Hs ].
    intros; split; intros HR.
    - exact (proj1 (member_type_gc_sub _ _ _ _ (gc_sub_deps _ _ _ H2)) _ _ _ _ HR).
    - exact (proj1 (member_type_gc_sub _ _ _ _ (gc_sub_deps _ _ _ H1)) _ _ _ _ HR).
  Qed.

  Lemma linv_mt_spec {ch Θ K D ΘR Ξ} (Hli : linv ch Θ K D ΘR Ξ) (Hg : ⊢g gds_restrict D Θ ⍮ Ξ) :
    mt_spec ΘR Ξ (mt_of _ _ Hg).
  Proof. exact (equiv_mt_spec _ _ _ _ (linv_equiv Hli) (mt_of_spec _ _ Hg)). Qed.

  Lemma xp_lift {ch Θ K D Ξ c c' r} (Hg : ⊢g gds_restrict D Θ ⍮ Ξ) :
    cmd_xp (mt_of _ _ Hg) (frame_skel Ξ) c = xok c' ->
    post_cmd ch Θ K D Ξ c' r -> post_xcmd ch Θ K D Ξ c r.
  Proof.
    intros E Hp ΘR Hli; destruct (Hp _ Hli) as (ΘR' & Hr & Hrest).
    exists c', ΘR'; split; [ exists (mt_of _ _ Hg); split; [ exact (linv_mt_spec Hli Hg) | exact E ] | exact (conj Hr Hrest) ].
  Qed.

  Lemma xp_eq {ch Θ K D ΘR Ξ c c'} (Hg : ⊢g gds_restrict D Θ ⍮ Ξ) :
    linv ch Θ K D ΘR Ξ -> cmd_xp_ok ΘR Ξ c c' -> cmd_xp (mt_of _ _ Hg) (frame_skel Ξ) c = xok c'.
  Proof. intros Hli Hx; exact (cmd_xp_ok_spec _ _ _ _ _ (linv_mt_spec Hli Hg) Hx). Qed.

  (** ** One Step per Rule

      Each lemma proves the [post_*] of one branch of the executable from the
      checks that branch makes. *)

  Lemma def_ok {ch Θ K D Ξ x b pv A M} :
    gs_fresh x Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    post_cmd ch Θ K D Ξ (cc_def x b pv A (Some M)) (cst Θ K D (gs_add x (gs_def b pv Ξ A M) Ξ)).
  Proof.
    intros Hfr HM ΘR Hli; cbn [cs_deps cs_k cs_dom cs_stack].
    assert (Hr : run_cmd ch ΘR Ξ (cc_def x b pv A (Some M)) ΘR (gs_add x (gs_def b pv Ξ A M) Ξ)).
    { constructor; [| exact Hfr ].
      exact (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HM). }
    exists ΘR; split; [ exact Hr | split; [ exact (linv_run_same Hli Hr) | split; [ apply ext_refl | apply grows_refl ] ] ].
  Qed.

  Lemma axiom_ok {ch Θ K D Ξ x b pv A i} :
    gs_fresh x Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i ->
    post_cmd ch Θ K D Ξ (cc_def x b pv A None) (cst Θ K D (gs_add x (gs_axiom b pv Ξ A) Ξ)).
  Proof.
    intros Hfr HA ΘR Hli; cbn [cs_deps cs_k cs_dom cs_stack].
    assert (Hr : run_cmd ch ΘR Ξ (cc_def x b pv A None) ΘR (gs_add x (gs_axiom b pv Ξ A) Ξ)).
    { econstructor; [| exact Hfr ].
      exact (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HA). }
    exists ΘR; split; [ exact Hr | split; [ exact (linv_run_same Hli Hr) | split; [ apply ext_refl | apply grows_refl ] ] ].
  Qed.

  Lemma eval_check_ok {ch Θ K D Ξ M A} :
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    post_cmd ch Θ K D Ξ (cc_eval M (Some A)) (cst Θ K D Ξ).
  Proof.
    intros HM ΘR Hli; cbn [cs_deps cs_k cs_dom cs_stack].
    assert (Hr : run_cmd ch ΘR Ξ (cc_eval M (Some A)) ΘR Ξ)
      by (constructor; exact (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HM)).
    exists ΘR; split; [ exact Hr | split; [ exact Hli | split; [ apply ext_refl | apply grows_refl ] ] ].
  Qed.

  Lemma eval_infer_ok {ch Θ K D Ξ M} (A : typ) :
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    post_cmd ch Θ K D Ξ (cc_eval M None) (cst Θ K D Ξ).
  Proof.
    intros HM ΘR Hli; cbn [cs_deps cs_k cs_dom cs_stack].
    assert (Hr : run_cmd ch ΘR Ξ (cc_eval M None) ΘR Ξ)
      by (econstructor; exact (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HM)).
    exists ΘR; split; [ exact Hr | split; [ exact Hli | split; [ apply ext_refl | apply grows_refl ] ] ].
  Qed.

  Lemma mod_pre {ch Θ K D Ξ x Δ} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> tele_ass Δ -> gs_fresh x Ξ -> ⊢ gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
    exists ΘR, linv ch Θ K D ΘR (gs_push (qname_in (gs_path Ξ) x) Δ Ξ).
  Proof. intros [ΘR Hli] Htel Hfr HΔ; exists ΘR; exact (proj2 (linv_push Hli Htel Hfr HΔ)). Qed.

  Lemma mod_ok {ch Θ K D Ξ x pv Δ cs r mp U Ξ2} :
    tele_ass Δ -> gs_fresh x Ξ -> ⊢ gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
    post_cmds ch Θ K D (gs_push (qname_in (gs_path Ξ) x) Δ Ξ) cs r -> cs_stack r = (mp, U) :: Ξ2 ->
    post_cmd ch Θ K D Ξ (cc_mod x pv Δ cs) (cst (cs_deps r) (cs_k r) (cs_dom r) (gs_add x (ge_body pv Δ (gu_mod U)) Ξ)).
  Proof.
    intros Htel Hfr HΔ Hpost HΞ ΘR Hli; cbn [cs_deps cs_k cs_dom cs_stack].
    destruct (linv_push Hli Htel Hfr HΔ) as [HΔ' Hli'].
    destruct (Hpost _ Hli') as (ΘR' & Hrun & Hli2 & Hext & Hgr).
    rewrite HΞ in Hrun, Hli2.
    destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ Hrun) as [F HF]; injection HF as <- ->.
    assert (Hr : run_cmd ch ΘR Ξ (cc_mod x pv Δ cs) ΘR' (gs_add x (ge_body pv Δ (gu_mod U)) Ξ))
      by (econstructor; eassumption).
    exists ΘR'; split; [ exact Hr | split; [| split; assumption ] ].
    apply (linv_stack Hli2); [ exact (proj1 (linv_run_wf Hli Hr)) | exact (linv_run_stack Hli Hr) ].
  Qed.

  Lemma alias_ok {ch Θ K D Ξ x pv Δ E} :
    tele_ass Δ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ ->
    gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E -> gs_fresh x Ξ ->
    post_cmd ch Θ K D Ξ (cc_alias x pv Δ E) (cst Θ K D (gs_add x (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))) Ξ)).
  Proof.
    intros Htel HΔ HE Hfr ΘR Hli; cbn [cs_deps cs_k cs_dom cs_stack].
    pose proof (gds_equiv_sym _ _ (linv_equiv Hli)) as Heq.
    assert (Hr : run_cmd ch ΘR Ξ (cc_alias x pv Δ E) ΘR (gs_add x (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))) Ξ))
      by (constructor; [ exact Htel | exact (equiv_ext _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HΔ)
                       | exact (equiv_modexp _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HE) | exact Hfr ]).
    exists ΘR; split; [ exact Hr | split; [ exact (linv_run_same Hli Hr) | split; [ apply ext_refl | apply grows_refl ] ] ].
  Qed.

  Lemma load_in_ok {ch Θ K D Ξ fp U} :
    In fp D -> gds_lookup Θ fp = Some U -> post_cmd ch Θ K D Ξ (cc_load fp) (cst Θ K D Ξ).
  Proof.
    intros Hin HU ΘR Hli; cbn [cs_deps cs_k cs_dom cs_stack].
    apply (li_dom _ _ _ _ _ _ Hli), gds_dom_lookup in Hin.
    destruct (gds_lookup ΘR fp) as [V |] eqn:E'; [| contradiction ].
    assert (Hr : run_cmd ch ΘR Ξ (cc_load fp) ΘR Ξ) by (eapply rc_load_filed; eassumption).
    exists ΘR; split; [ exact Hr | split; [ exact Hli | split; [ apply ext_refl | apply grows_refl ] ] ].
  Qed.

  (** Loading a filed unit that the unit being run has not imported yet:
      the judgment loads it, which the entry of [Θ] justifies once the chain
      is changed. *)
  Lemma hit_linv {ch Θ K D Ξ fp U Dfp} :
    ~ In fp D -> gds_lookup Θ fp = Some U -> kfind K fp = Some Dfp -> forall ΘR, linv ch Θ K D ΘR Ξ ->
    exists src prg u ΘU, gds_lookup ΘR fp = None /\ ~ In fp ch /\ load_path fp = Some src /\
      read src = Some prg /\ prog_path prg = fp /\ to_core prg = Some u /\ run_unit (fp :: ch) u ΘU U /\
      linv ch Θ K (p_union D (fp :: Dfp)) (gds_merge ΘR ((fp, U) :: ΘU)) Ξ.
  Proof.
    intros Hnin HU HK ΘR Hli.
    pose proof (li_g _ _ _ _ _ _ Hli) as G.
    destruct (ginv_entry G _ _ HU)
      as (Dfp' & HK' & Hcl & src & prg & u & ch0 & ΘU & Hl & Hrd & Hp & Ht & Hu & Hsub & Hdom).
    rewrite HK in HK'; injection HK' as <-.
    assert (Hn : gds_lookup ΘR fp = None)
      by (apply gds_dom_none; intros Hin; apply Hnin, (li_dom _ _ _ _ _ _ Hli), Hin).
    assert (Hnch : ~ In fp ch) by (intros Hin; rewrite (gi_chain _ _ _ G _ Hin) in HU; discriminate).
    assert (Hu' : run_unit (fp :: ch) u ΘU U).
    { apply (proj2 (proj2 (run_chain_irrel load_path read to_core)) _ _ _ _ Hu ch).
      intros x [<- | Hin].
      - exact (proj2 (proj2 (run_chain_fresh load_path read to_core)) _ _ _ _ Hu _ (or_introl eq_refl)).
      - exact (sub_none _ _ _ Hsub (gi_chain _ _ _ G _ Hin)). }
    destruct (load_wf load_path read to_core _ _ _ _ _ _ _ _ _ (li_wf _ _ _ _ _ _ Hli) (li_canon _ _ _ _ _ _ Hli)
                (li_stack _ _ _ _ _ _ Hli) Hn Hnch Hl Hrd Ht Hu') as (Hwf' & Hc' & _).
    exists src, prg, u, ΘU; do 7 (split; [ assumption |]).
    constructor; [ exact G | | | | exact Hwf' | exact Hc' | exact (li_stack _ _ _ _ _ _ Hli) ].
    - intros y V HV; apply merge_inv in HV as [HV | HV]; [ exact (li_sub _ _ _ _ _ _ Hli _ _ HV) |].
      cbn in HV; destruct (path_beq y fp) eqn:Hb; [| exact (Hsub _ _ HV) ].
      apply path_beq_true in Hb as ->; injection HV as <-; exact HU.
    - intros y; rewrite p_union_iff, dom_merge, dom_cons, <- (li_dom _ _ _ _ _ _ Hli y), <- (Hdom y); cbn [In].
      intuition congruence.
    - intros y Dy Hy HKy; apply p_union_iff in Hy as [Hy | [<- | Hy]]; intros z Hz; apply p_union_iff.
      + left; exact (li_closed _ _ _ _ _ _ Hli _ _ Hy HKy _ Hz).
      + rewrite HK in HKy; injection HKy as <-; right; right; exact Hz.
      + right; right; exact (Hcl _ _ Hy HKy _ Hz).
  Qed.

  Lemma load_hit_ok {ch Θ K D Ξ fp U Dfp} :
    ~ In fp D -> gds_lookup Θ fp = Some U -> kfind K fp = Some Dfp ->
    post_cmd ch Θ K D Ξ (cc_load fp) (cst Θ K (p_union D (fp :: Dfp)) Ξ).
  Proof.
    intros Hnin HU HK ΘR Hli; cbn [cs_deps cs_k cs_dom cs_stack].
    destruct (hit_linv Hnin HU HK _ Hli) as (src & prg & u & ΘU & Hn & Hnch & Hl & Hrd & Hp & Ht & Hu & Hli').
    assert (Hr : run_cmd ch ΘR Ξ (cc_load fp) (gds_merge ΘR ((fp, U) :: ΘU)) Ξ) by (eapply rc_load; eassumption).
    exists (gds_merge ΘR ((fp, U) :: ΘU)); split; [ exact Hr | split; [ exact Hli' | split; [ apply ext_refl | apply grows_refl ] ] ].
  Qed.

  Lemma load_pre {ch Θ K D Ξ fp} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> gds_lookup Θ fp = None -> ~ In fp ch -> ginv (fp :: ch) Θ K.
  Proof.
    intros [ΘR Hli] Hn Hnch; pose proof (li_g _ _ _ _ _ _ Hli) as [].
    constructor; auto; intros x [<- | Hx]; auto.
  Qed.

  (** A loaded unit is filed on top of everything its run filed, which holds
      the state the judgment's run ended in. *)
  Definition load_state (fp : path) (D : list path) (Ξ : gstack) (r : ustate) : cstate :=
    cst ((fp, us_unit r) :: us_deps r) ((fp, us_dom r) :: us_k r) (p_union D (fp :: us_dom r)) Ξ.

  Lemma load_linv {ch Θ K D Ξ fp src prg u r} :
    gds_lookup Θ fp = None -> ~ In fp ch ->
    load_path fp = Some src -> read src = Some prg -> prog_path prg = fp -> to_core prg = Some u ->
    post_unit (fp :: ch) Θ K u r -> forall ΘR, linv ch Θ K D ΘR Ξ ->
    exists ΘU, gds_lookup ΘR fp = None /\ run_unit (fp :: ch) u ΘU (us_unit r) /\
      linv ch (cs_deps (load_state fp D Ξ r)) (cs_k (load_state fp D Ξ r)) (cs_dom (load_state fp D Ξ r))
        (gds_merge ΘR ((fp, us_unit r) :: ΘU)) Ξ /\
      ext Θ K (cs_deps (load_state fp D Ξ r)) (cs_k (load_state fp D Ξ r)) /\
      grows Θ (cs_deps (load_state fp D Ξ r)) (cs_dom (load_state fp D Ξ r)).
  Proof.
    intros Hn Hnch Hl Hrd Hp Ht Hpost ΘR Hli.
    pose proof (li_g _ _ _ _ _ _ Hli) as G.
    assert (Gin : ginv (fp :: ch) Θ K) by (eapply load_pre; [ exists ΘR; exact Hli | assumption | assumption ]).
    destruct r as [Θ1 K1 Dfp U]; unfold load_state; cbn [us_deps us_k us_dom us_unit cs_deps cs_k cs_dom cs_stack] in *.
    destruct (Hpost Gin) as (ΘU & Hu & G1 & Hsub1 & Hdom1 & Hcl1 & [Hext1 HextK] & Hgr1).
    cbn [us_deps us_k us_dom us_unit] in *.
    destruct (proj2 (proj2 run_wf) _ _ _ _ Hu) as (HwU & HcU & HUu); cbn [hd] in HUu.
    assert (HnR : gds_lookup ΘR fp = None) by exact (sub_none _ _ _ (li_sub _ _ _ _ _ _ Hli) Hn).
    destruct (load_wf load_path read to_core _ _ _ _ _ _ _ _ _ (li_wf _ _ _ _ _ _ Hli) (li_canon _ _ _ _ _ _ Hli)
                (li_stack _ _ _ _ _ _ Hli) HnR Hnch Hl Hrd Ht Hu) as (Hwf' & Hc' & _).
    assert (Hn1 : gds_lookup Θ1 fp = None) by exact (gi_chain _ _ _ G1 _ (or_introl eq_refl)).
    set (ΘN := (fp, U) :: Θ1).
    assert (HwN : ⊢g ΘN ⍮ nil).
    { apply wf_gstack_file'; [ exact (gi_wf _ _ _ G1) | | exact Hn1 ].
      eapply unit_deps_grow; [ exact Hsub1 | exact (gi_wf _ _ _ G1) | exact Hn1 | exact HUu ]. }
    assert (Hsub1N : Θ1 ⊑ ΘN) by exact (gds_sub_cons _ _ _ Hn1).
    assert (HfpN : gds_lookup ΘN fp = Some U) by (cbn; rewrite path_beq_refl; reflexivity).
    assert (HsubU : ΘU ⊑ ΘN) by exact (gds_sub_trans _ _ _ Hsub1 Hsub1N).
    assert (HK1 : forall y Dy, kfind K1 y = Some Dy -> y <> fp)
      by (intros y Dy HKy ->; exact (gi_kdom _ _ _ G1 _ _ HKy Hn1)).
    assert (Hd1 : forall y, In y (gds_dom Θ1) -> y <> fp)
      by (intros y Hy ->; apply gds_dom_lookup in Hy; contradiction).
    assert (Hdfp : forall y, In y Dfp -> y <> fp)
      by (intros y Hy; apply Hd1, (sub_dom _ _ _ Hsub1), Hdom1, Hy).
    assert (GN : ginv ch ΘN ((fp, Dfp) :: K1)).
    { constructor; [ exact HwN | | | ].
      - intros y Hy; cbn; rewrite path_beq_false by (intros ->; contradiction).
        exact (gi_chain _ _ _ G1 _ (or_intror Hy)).
      - split; [| exact (entries_ok_cons_K _ _ _ _ HK1 Hd1 (gi_entry _ _ _ G1)) ].
        exists Dfp; simp kfind; rewrite path_beq_refl; split; [ reflexivity |].
        split; [ exact (closedK_cons _ _ _ _ Hcl1 Hdfp) |].
        exists src, prg, u, ch, ΘU; do 6 (split; [ assumption |]); exact Hdom1.
      - intros y Dy HKy; simp kfind in HKy; destruct (path_beq y fp) eqn:Hb.
        + apply path_beq_true in Hb as ->; rewrite HfpN; discriminate.
        + intros E; apply (gi_kdom _ _ _ G1 _ _ HKy), (sub_none _ _ _ Hsub1N), E. }
    exists ΘU; cbn [cs_deps cs_k cs_dom cs_stack us_deps us_k us_dom us_unit]; split; [ exact HnR | split; [ exact Hu |] ].
    split; [| split ].
    - constructor; [ exact GN | | | | exact Hwf' | exact Hc' | exact (li_stack _ _ _ _ _ _ Hli) ].
      + intros y V HV; apply merge_inv in HV as [HV | HV].
        * exact (Hsub1N _ _ (Hext1 _ _ (li_sub _ _ _ _ _ _ Hli _ _ HV))).
        * cbn in HV; destruct (path_beq y fp) eqn:Hb; [| exact (HsubU _ _ HV) ].
          apply path_beq_true in Hb as ->; injection HV as <-; exact HfpN.
      + intros y; rewrite p_union_iff, dom_merge, dom_cons, <- (li_dom _ _ _ _ _ _ Hli y), <- (Hdom1 y); cbn [In].
        intuition congruence.
      + intros y Dy Hy HKy; simp kfind in HKy; destruct (path_beq y fp) eqn:Hb.
        * apply path_beq_true in Hb as ->; injection HKy as <-; intros z Hz; apply p_union_iff; right; right; exact Hz.
        * intros z Hz; apply p_union_iff; apply p_union_iff in Hy as [Hy | [<- | Hy]].
          -- left; pose proof (linv_in Hli _ Hy) as Hy'.
             destruct (gds_lookup Θ y) as [Vy |] eqn:Ey; [| contradiction ].
             destruct (ginv_entry G _ _ Ey) as (Dy' & HKy' & _).
             rewrite (HextK _ _ HKy') in HKy; injection HKy as <-.
             exact (li_closed _ _ _ _ _ _ Hli _ _ Hy HKy' _ Hz).
          -- rewrite path_beq_refl in Hb; discriminate.
          -- right; right; exact (Hcl1 _ _ Hy HKy _ Hz).
    - split; [ exact (gds_sub_trans _ _ _ Hext1 Hsub1N) |].
      intros y Dy HKy; simp kfind; rewrite path_beq_false; [ exact (HextK _ _ HKy) |].
      intros ->; exact (gi_kdom _ _ _ G _ _ HKy Hn).
    - intros y Hy; unfold ΘN in Hy; apply dom_cons in Hy as [-> | Hy].
      + right; apply p_union_iff; right; left; reflexivity.
      + destruct (Hgr1 _ Hy) as [H | H]; [ left; exact H | right; apply p_union_iff; right; right; exact H ].
  Qed.

  Lemma load_ok {ch Θ K D Ξ fp src prg u r} :
    gds_lookup Θ fp = None -> ~ In fp ch ->
    load_path fp = Some src -> read src = Some prg -> prog_path prg = fp -> to_core prg = Some u ->
    post_unit (fp :: ch) Θ K u r ->
    post_cmd ch Θ K D Ξ (cc_load fp) (load_state fp D Ξ r).
  Proof.
    intros Hn Hnch Hl Hrd Hp Ht Hpost ΘR Hli.
    destruct (load_linv Hn Hnch Hl Hrd Hp Ht Hpost _ Hli) as (ΘU & HnR & Hu & Hli' & Hext & Hgr).
    assert (Hr : run_cmd ch ΘR Ξ (cc_load fp) (gds_merge ΘR ((fp, us_unit r) :: ΘU)) Ξ) by (eapply rc_load; eassumption).
    exists (gds_merge ΘR ((fp, us_unit r) :: ΘU)); split; [ exact Hr | split; [ exact Hli' | split; assumption ] ].
  Qed.

  (** ** The Generated Entries of an Import *)

  Definition post_gens ch Θ K D Ξ gs Ξ' : Prop :=
    forall ΘR, linv ch Θ K D ΘR Ξ -> gens_run ΘR Ξ gs Ξ' /\ linv ch Θ K D ΘR Ξ'.

  Lemma gens_nil_ok {ch Θ K D Ξ} : post_gens ch Θ K D Ξ nil Ξ.
  Proof. intros ΘR Hli; split; [ constructor | exact Hli ]. Qed.

  Lemma gdef_step {ch Θ K D ΘR Ξ d pv A M} :
    linv ch Θ K D ΘR Ξ -> gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    ΘR ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A /\ linv ch Θ K D ΘR (gs_add d (gs_def true pv Ξ A M) Ξ).
  Proof.
    intros Hli Hfr HM.
    pose proof (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HM) as HM'.
    split; [ exact HM' |].
    assert (Hr : run_cmd ch ΘR Ξ (cc_def d true pv A (Some M)) ΘR (gs_add d (gs_def true pv Ξ A M) Ξ))
      by (constructor; assumption).
    exact (linv_run_same Hli Hr).
  Qed.

  Lemma galias_step {ch Θ K D ΘR Ξ d pv E} :
    linv ch Θ K D ΘR Ξ -> gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
    ΘR ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E /\ linv ch Θ K D ΘR (gs_add d (ge_mod pv (gu_mk (gs_tele Ξ) (md_alias E))) Ξ).
  Proof.
    intros Hli Hfr HE.
    pose proof (equiv_modexp _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HE) as HE'.
    split; [ exact HE' |].
    assert (Hr : run_cmd ch ΘR Ξ (cc_alias d pv nil E) ΘR (gs_add d (ge_mod pv (gu_mk (nil ++ gs_tele Ξ) (md_alias E))) Ξ))
      by (constructor; [ constructor | constructor; exact (presup_modexp_eq_ctx HE') | exact HE' | exact Hfr ]).
    exact (linv_run_same Hli Hr).
  Qed.

  Lemma gdef_pre {ch Θ K D Ξ d pv A M} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    exists ΘR, linv ch Θ K D ΘR (gs_add d (gs_def true pv Ξ A M) Ξ).
  Proof. intros [ΘR Hli] Hfr HM; exists ΘR; exact (proj2 (gdef_step Hli Hfr HM)). Qed.

  Lemma galias_pre {ch Θ K D Ξ d pv E} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
    exists ΘR, linv ch Θ K D ΘR (gs_add d (ge_mod pv (gu_mk (gs_tele Ξ) (md_alias E))) Ξ).
  Proof. intros [ΘR Hli] Hfr HE; exists ΘR; exact (proj2 (galias_step Hli Hfr HE)). Qed.

  Lemma gdef_ok {ch Θ K D Ξ d pv A M gs Ξ'} :
    gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    post_gens ch Θ K D (gs_add d (gs_def true pv Ξ A M) Ξ) gs Ξ' ->
    post_gens ch Θ K D Ξ (ig_def d pv A M :: gs) Ξ'.
  Proof.
    intros Hfr HM Hp ΘR Hli; destruct (gdef_step (pv := pv) Hli Hfr HM) as [HM' Hli'].
    destruct (Hp _ Hli') as [Hg Hli2]; split; [ constructor; assumption | exact Hli2 ].
  Qed.

  Lemma galias_ok {ch Θ K D Ξ d pv E gs Ξ'} :
    gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
    post_gens ch Θ K D (gs_add d (ge_mod pv (gu_mk (gs_tele Ξ) (md_alias E))) Ξ) gs Ξ' ->
    post_gens ch Θ K D Ξ (ig_alias d pv E :: gs) Ξ'.
  Proof.
    intros Hfr HE Hp ΘR Hli; destruct (galias_step (pv := pv) Hli Hfr HE) as [HE' Hli'].
    destruct (Hp _ Hli') as [Hg Hli2]; split; [ constructor; assumption | exact Hli2 ].
  Qed.

  (** An import declares what its items generate, which files nothing. *)
  Lemma import_ok {ch Θ K D Ξ E its gs Ξ'} (Hg : ⊢g gds_restrict D Θ ⍮ Ξ) :
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
    import_gen (mt_of _ _ Hg) (gs_tele Ξ) E its = xok gs ->
    post_gens ch Θ K D Ξ gs Ξ' ->
    post_cmd ch Θ K D Ξ (cc_open E its) (cst Θ K D Ξ').
  Proof.
    intros HE Hgen Hgs ΘR Hli; cbn [cs_deps cs_k cs_dom cs_stack].
    destruct (Hgs _ Hli) as [Hr Hli'].
    pose proof (gds_equiv_sym _ _ (linv_equiv Hli)) as Heq.
    exists ΘR; split; [| split; [ exact Hli' | split; [ apply ext_refl | apply grows_refl ] ] ].
    eapply rc_open; [ exact (equiv_modexp _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HE) | | exact Hr ].
    exists (mt_of _ _ Hg); split; [ exact (linv_mt_spec Hli Hg) | exact Hgen ].
  Qed.

  Lemma nil_ok {ch Θ K D Ξ} : post_cmds ch Θ K D Ξ nil (cst Θ K D Ξ).
  Proof.
    intros ΘR Hli; exists ΘR; split; [ constructor | split; [ exact Hli | split; [ apply ext_refl | apply grows_refl ] ] ].
  Qed.

  Lemma cons_pre {ch Θ K D Ξ c r} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> post_xcmd ch Θ K D Ξ c r ->
    exists ΘR, linv ch (cs_deps r) (cs_k r) (cs_dom r) ΘR (cs_stack r).
  Proof. intros [ΘR Hli] Hp; destruct (Hp _ Hli) as (c' & ΘR' & _ & _ & Hli' & _); eauto. Qed.

  (** The imports of a later step include those of an earlier one. *)
  Lemma dom_grows {ch Θ1 K1 D1 ΘR1 Ξ1 Θ2 K2 D2 ΘR2 Ξ2 cs} :
    linv ch Θ1 K1 D1 ΘR1 Ξ1 -> run_cmds ch ΘR1 Ξ1 cs ΘR2 Ξ2 -> linv ch Θ2 K2 D2 ΘR2 Ξ2 -> incl D1 D2.
  Proof.
    intros Hli1 Hr Hli2 x Hx.
    destruct (proj1 (proj2 run_wf) _ _ _ _ _ _ Hr (li_wf _ _ _ _ _ _ Hli1) (li_canon _ _ _ _ _ _ Hli1) (li_stack _ _ _ _ _ _ Hli1)) as (_ & _ & Hs).
    apply (li_dom _ _ _ _ _ _ Hli2), (sub_dom _ _ _ Hs), (li_dom _ _ _ _ _ _ Hli1), Hx.
  Qed.

  Lemma cons_ok {ch Θ K D Ξ c cs r1 r2} :
    acc_ok (gds_restrict D Θ) Ξ (cmd_refs c) ->
    post_xcmd ch Θ K D Ξ c r1 -> post_cmds ch (cs_deps r1) (cs_k r1) (cs_dom r1) (cs_stack r1) cs r2 ->
    post_cmds ch Θ K D Ξ (c :: cs) r2.
  Proof.
    intros Hac H1 H2 ΘR Hli.
    pose proof (equiv_acc _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) Hac) as Hac'.
    destruct (H1 _ Hli) as (c' & ΘR1 & Hxp & Hr1 & Hli1 & He1 & Hg1).
    destruct (H2 _ Hli1) as (ΘR2 & Hr2 & Hli2 & He2 & Hg2).
    exists ΘR2; split; [ econstructor; eassumption |].
    split; [ exact Hli2 | split; [ eapply ext_trans; eassumption |] ].
    intros x Hx; destruct (Hg2 _ Hx) as [Hx1 | Hx1]; [| right; exact Hx1 ].
    destruct (Hg1 _ Hx1) as [Hx0 | Hx0]; [ left; exact Hx0 | right; exact (dom_grows Hli1 Hr2 Hli2 _ Hx0) ].
  Qed.

  Lemma unit_pre {ch Θ K} : ginv ch Θ K -> exists ΘR, linv ch Θ K nil ΘR nil.
  Proof. intros G; exists nil; exact (nil_linv G). Qed.

  (** The imports run on the empty stack and leave it empty. *)
  Lemma unit_imports {ch Θ K imps r1} :
    ginv ch Θ K -> post_cmds ch Θ K nil nil imps r1 ->
    exists ΘR1, run_cmds ch nil nil imps ΘR1 nil /\ cs_stack r1 = nil /\
      linv ch (cs_deps r1) (cs_k r1) (cs_dom r1) ΘR1 nil /\
      ext Θ K (cs_deps r1) (cs_k r1) /\ grows Θ (cs_deps r1) (cs_dom r1).
  Proof.
    intros G Hp; destruct (Hp _ (nil_linv G)) as (ΘR1 & Hr1 & Hli1 & He1 & Hg1).
    pose proof (run_cmds_empty _ _ _ _ _ _ _ _ Hr1) as HΞ; rewrite HΞ in Hr1, Hli1.
    exists ΘR1; exact (conj Hr1 (conj HΞ (conj Hli1 (conj He1 Hg1)))).
  Qed.

  Lemma unit_gctx {ch Θ K imps r1} :
    ginv ch Θ K -> post_cmds ch Θ K nil nil imps r1 -> ⊢g gds_restrict (cs_dom r1) (cs_deps r1) ⍮ nil.
  Proof. intros G Hp; destruct (unit_imports G Hp) as (ΘR1 & _ & _ & Hli1 & _); exact (linv_restrict_gctx Hli1). Qed.

  Lemma unit_body_pre {fp ch Θ K imps r1 P} :
    ginv (fp :: ch) Θ K -> post_cmds (fp :: ch) Θ K nil nil imps r1 -> tele_ass P ->
    ⊢ gds_restrict (cs_dom r1) (cs_deps r1) ⍮ nil ⍮ P ->
    exists ΘR, linv (fp :: ch) (cs_deps r1) (cs_k r1) (cs_dom r1) ΘR (gs_push (q_abs fp nil) P nil).
  Proof.
    intros G Hp Htel HP; destruct (unit_imports G Hp) as (ΘR1 & _ & _ & Hli1 & _).
    exists ΘR1; exact (proj2 (linv_push_unit Hli1 Htel HP)).
  Qed.

  Lemma unit_ok {fp ch Θ K imps P0 P cs r1 r2 mp U Ξ2} (Hg : ⊢g gds_restrict (cs_dom r1) (cs_deps r1) ⍮ nil) :
    post_cmds (fp :: ch) Θ K nil nil imps r1 ->
    tele_xp (mt_of _ _ Hg) nil P0 = xok P ->
    tele_ass P ->
    ⊢ gds_restrict (cs_dom r1) (cs_deps r1) ⍮ nil ⍮ P ->
    acc_ok (gds_restrict (cs_dom r1) (cs_deps r1)) nil (tele_refs nil P0) ->
    post_cmds (fp :: ch) (cs_deps r1) (cs_k r1) (cs_dom r1) (gs_push (q_abs fp nil) P nil) cs r2 ->
    cs_stack r2 = (mp, U) :: Ξ2 ->
    post_unit (fp :: ch) Θ K (imps, P0, cs) (ust (cs_deps r2) (cs_k r2) (cs_dom r2) U).
  Proof.
    intros Hp1 EP Htel HP Hac Hp2 HΞ G; cbn [us_deps us_k us_dom us_unit].
    destruct (unit_imports G Hp1) as (ΘR1 & Hr1 & _ & Hli1 & He1 & Hg1).
    pose proof (equiv_acc _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli1)) Hac) as Hac'.
    destruct (linv_push_unit Hli1 Htel HP) as [HP' Hli1'].
    destruct (Hp2 _ Hli1') as (ΘR2 & Hr2 & Hli2 & He2 & Hg2).
    rewrite HΞ in Hr2, Hli2.
    destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ Hr2) as [F HF]; injection HF as <- ->.
    exists ΘR2; split.
    { eapply ru_intro; [ exact Hr1 | | exact Htel | exact HP' | exact Hac' | exact Hr2 ].
      exists (mt_of _ _ Hg); split; [ exact (linv_mt_spec Hli1 Hg) | exact EP ]. }
    destruct Hli2 as [G2 Hs2 Hd2 Hc2 _ _ _].
    split; [ exact G2 | split; [ exact Hs2 | split; [ exact Hd2 | split; [ exact Hc2 | split; [ eapply ext_trans; eassumption |] ] ] ] ].
    intros x Hx; destruct (Hg2 _ Hx) as [Hx1 | Hx1]; [| right; exact Hx1 ].
    destruct (Hg1 _ Hx1) as [Hx0 | Hx0]; [ left; exact Hx0 | right ].
    apply Hd2, (sub_dom _ _ _ (proj2 (proj2 (proj1 (proj2 run_wf) _ _ _ _ _ _ Hr2
                                                 (li_wf _ _ _ _ _ _ Hli1') (li_canon _ _ _ _ _ _ Hli1')
                                                 (li_stack _ _ _ _ _ _ Hli1'))))).
    apply (li_dom _ _ _ _ _ _ Hli1), Hx0.
  Qed.

  (** ** The Executable

      Recursion on commands is structural, including on the command lists
      nested in modules: the local helper [go] of [cmds_step] takes the
      function for one command as a uniform parameter, so the guard checker
      sees through it.  Only a load recurses on something else: the chain
      grows by an unfiled path that [load_path] knows ([load_step]), and
      [run_unit_impl] is structural on the accessibility proof.  The
      executable takes that proof, never the list of files. *)

  Definition load_step (ch' ch : list path) : Prop :=
    exists fp s, ch' = fp :: ch /\ ~ In fp ch /\ load_path fp = Some s.

  Definition load_step_intro {ch fp src} (Hn : ~ In fp ch) (Hs : load_path fp = Some src) :
    load_step (fp :: ch) ch :=
    ex_intro _ fp (ex_intro _ src (conj eq_refl (conj Hn Hs))).

  (** How a unit loaded under chain [ch] is run.  Its log holds the evals of
      the unit itself, not of the units it loads. *)
  Definition loader (ch : list path) : Type :=
    forall fp src, ~ In fp ch -> load_path fp = Some src ->
      forall Θ K u, ginv (fp :: ch) Θ K -> rres ({r | post_unit (fp :: ch) Θ K u r} * elog)%type.

  Definition cmd_fun (ch : list path) : Type :=
    forall Θ K D Ξ c (H : exists ΘR, linv ch Θ K D ΘR Ξ), rres ({r | post_xcmd ch Θ K D Ξ c r} * elog)%type.

  Equations cmds_step (ch : list path) (rc : cmd_fun ch) :
    forall Θ K D Ξ cs (H : exists ΘR, linv ch Θ K D ΘR Ξ), rres ({r | post_cmds ch Θ K D Ξ cs r} * elog)%type :=
  cmds_step ch rc := go
  where go Θ0 K0 D0 Ξ0 (cs : list ccmd) (H0 : exists ΘR, linv ch Θ0 K0 D0 ΘR Ξ0) :
    rres ({r | post_cmds ch Θ0 K0 D0 Ξ0 cs r} * elog)%type by struct cs :=
  | Θ0, K0, D0, Ξ0, nil, H0 => rok (exist _ _ nil_ok, log_nil)
  | Θ0, K0, D0, Ξ0, c :: cs', H0 with refs_check (gds_restrict D0 Θ0) Ξ0 (pre_gctx H0) (cmd_refs c) => {
    | inleft (exist _ e _) => rerr (priv_error e)
    | inright Hac with rc Θ0 K0 D0 Ξ0 c H0 => {
      | rerr e => rerr e
      | rok (exist _ r1 Hr1, l1) with go (cs_deps r1) (cs_k r1) (cs_dom r1) (cs_stack r1) cs' (cons_pre H0 Hr1) => {
        | rerr e => rerr e
        | rok (exist _ r2 Hr2, l2) => rok (exist _ _ (cons_ok Hac Hr1 Hr2), log_app l1 l2) } } }.

  Definition da_ok {ch Θ K D Ξ c Ξ'} (Hp : post_cmd ch Θ K D Ξ c (cst Θ K D Ξ')) :
      {Ξ0 | post_cmd ch Θ K D Ξ c (cst Θ K D Ξ0)} := exist _ Ξ' Hp.

  (** A definition or an alias, checked as written: the non-recursive step
      of [cc_def] and [cc_alias], which also runs the commands an import
      generates. *)
  Equations defalias_step (ch : list path) (Θ : gdeps) (K : kmap) (D : list path) (Ξ : gstack)
    (c : ccmd) (H : exists ΘR, linv ch Θ K D ΘR Ξ) : rres {Ξ' | post_cmd ch Θ K D Ξ c (cst Θ K D Ξ')} :=
  | ch, Θ, K, D, Ξ, cc_def x b pv A (Some M), H with gs_fresh_dec x Ξ => {
    | right _ => rerr (re_msg ("duplicate name " ++ x))
    | left Hfr with check_typ (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A => {
      | inright _ => rerr (blame_error (find_level_blame _ _ _ (pre_ctx H) A) (re_def_typ x Ξ A))
      | inleft (exist _ i HA) with check_exp_typed (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A (ex_intro _ i HA) M => {
        | left HM => rok (da_ok (def_ok Hfr HM))
        | right _ => rerr (re_def x Ξ A M) } } }
  | ch, Θ, K, D, Ξ, cc_def x b pv A None, H with gs_fresh_dec x Ξ => {
    | right _ => rerr (re_msg ("duplicate name " ++ x))
    | left Hfr with check_typ (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A => {
      | inleft (exist _ i HA) => rok (da_ok (axiom_ok Hfr HA))
      | inright _ =>
          rerr (blame_error (find_level_blame _ _ _ (pre_ctx H) A)
                  (re_msg ("the type of axiom " ++ x ++ " is not a type"))) } }
  | ch, Θ, K, D, Ξ, cc_alias x pv Δ E, H with tele_ass_dec Δ => {
    | right _ => rerr (re_msg ("parameters of module " ++ x ++ " that are not assumptions"))
    | left Htel with check_ext (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) Δ => {
      | right _ =>
          rerr (tele_blame_error (find_tele_blame _ _ _ (pre_ctx H) Δ)
                  (re_msg ("ill-formed parameters of module " ++ x)))
      | left HΔ with check_modexp (gds_restrict D Θ) Ξ (Δ ++ gs_tele Ξ) (ext_eq_ctx_left _ _ _ _ _ HΔ) E => {
        | right _ => rerr (re_msg ("ill-formed module expression for module " ++ x))
        | left HE with gs_fresh_dec x Ξ => {
          | right _ => rerr (re_msg ("duplicate name " ++ x))
          | left Hfr => rok (da_ok (alias_ok Htel HΔ HE Hfr)) } } } }
  | _, _, _, _, _, _, _ => rerr (re_msg "internal error: not a definition or an alias").

  (** The entries an import generates, in order, as [gens_run] declares
      them: written by no one, so with no privacy check. *)
  Fixpoint gens_impl (ch : list path) (Θ : gdeps) (K : kmap) (D : list path) (Ξ : gstack)
    (gs : list igen) (H : exists ΘR, linv ch Θ K D ΘR Ξ) {struct gs} : rres {Ξ' | post_gens ch Θ K D Ξ gs Ξ'} :=
    match gs as gs0 return rres {Ξ' | post_gens ch Θ K D Ξ gs0 Ξ'} with
    | nil => rok (exist _ Ξ gens_nil_ok)
    | ig_def d pv A M :: gs' =>
        match gs_fresh_dec d Ξ with
        | right _ => rerr (re_msg ("duplicate name " ++ d))
        | left Hfr =>
            match check_exp (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A M with
            | right _ => rerr (re_def d Ξ A M)
            | left HM =>
                match gens_impl ch Θ K D (gs_add d (gs_def true pv Ξ A M) Ξ) gs' (gdef_pre H Hfr HM) with
                | rerr e => rerr e
                | rok (exist _ Ξ' Hp) => rok (exist _ Ξ' (gdef_ok Hfr HM Hp))
                end
            end
        end
    | ig_alias d pv E :: gs' =>
        match gs_fresh_dec d Ξ with
        | right _ => rerr (re_msg ("duplicate name " ++ d))
        | left Hfr =>
            match check_modexp (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) E with
            | right _ => rerr (re_msg ("ill-formed module expression for module " ++ d))
            | left HE =>
                match gens_impl ch Θ K D (gs_add d (ge_mod pv (gu_mk (gs_tele Ξ) (md_alias E))) Ξ) gs'
                        (galias_pre H Hfr HE) with
                | rerr e => rerr e
                | rok (exist _ Ξ' Hp) => rok (exist _ Ξ' (galias_ok Hfr HE Hp))
                end
            end
        end
    end.

  Definition cmd_ok {ch Θ K D Ξ c r} (Hp : post_cmd ch Θ K D Ξ c r) : {r0 | post_cmd ch Θ K D Ξ c r0} :=
    exist _ r Hp.

  (** Every expanded command but a module, which recurses on its body. *)
  Equations simple_step (ch : list path) (L : loader ch) (Θ : gdeps) (K : kmap) (D : list path) (Ξ : gstack)
    (c : ccmd) (H : exists ΘR, linv ch Θ K D ΘR Ξ) : rres ({r | post_cmd ch Θ K D Ξ c r} * elog)%type :=
  | ch, L, Θ, K, D, Ξ, cc_def x b pv A M, H with defalias_step ch Θ K D Ξ (cc_def x b pv A M) H => {
    | rerr e => rerr e
    | rok (exist _ Ξ' Hp) => rok (cmd_ok Hp, log_nil) }
  | ch, L, Θ, K, D, Ξ, cc_alias x pv Δ E, H with defalias_step ch Θ K D Ξ (cc_alias x pv Δ E) H => {
    | rerr e => rerr e
    | rok (exist _ Ξ' Hp) => rok (cmd_ok Hp, log_nil) }
  | ch, L, Θ, K, D, Ξ, cc_mod _ _ _ _, H => rerr (re_msg "internal error: a module is run by its own step")
  | ch, L, Θ, K, D, Ξ, cc_load fp, H with opt_case (gds_lookup Θ fp) => {
    | inleft (exist _ U HU) with in_dec path_eq_dec fp D => {
      | left Hin => rok (exist _ _ (load_in_ok Hin HU), log_nil)
      | right Hnin with opt_case (kfind K fp) => {
        | inleft (exist _ Dfp HK) => rok (exist _ _ (load_hit_ok Hnin HU HK), log_nil)
        | inright _ => rerr (re_msg "internal error: a filed unit has no closure") } }
    | inright Hn with in_dec path_eq_dec fp ch => {
      | left _ => rerr (re_cycle (cycle_chain fp ch))
      | right Hnch with opt_case (load_path fp) => {
        | inright _ => rerr (re_unit fp "cannot find unit")
        | inleft (exist _ src Hsrc) with opt_case (read src) => {
          | inright _ => rerr (re_unit fp "cannot parse unit")
          | inleft (exist _ prg Hprg) with path_eq_dec (prog_path prg) fp => {
            | right _ => rerr (re_unit fp "the file of the unit declares another unit")
            | left Hp with opt_case (to_core prg) => {
              | inright _ => rerr (re_unit fp "cannot elaborate unit")
              | inleft (exist _ u Hu) with L fp src Hnch Hsrc Θ K u (load_pre H Hn Hnch) => {
                | rerr e => rerr e
                | rok (exist _ r Hr, _) => rok (exist _ _ (load_ok Hn Hnch Hsrc Hprg Hp Hu Hr), log_nil) } } } } } } }
  | ch, L, Θ, K, D, Ξ, cc_open E its, H with check_modexp (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) E => {
    | right _ => rerr (re_import (xe_target E))
    | left HE with inspect (import_gen (mt_of _ _ (pre_gctx H)) (gs_tele Ξ) E its) => {
      | exist _ (xfail e) _ => rerr (re_import e)
      | exist _ (xok gs) Eg with gens_impl ch Θ K D Ξ gs H => {
        | rerr e => rerr e
        | rok (exist _ Ξ' Hgs) => rok (exist _ _ (import_ok (pre_gctx H) HE Eg Hgs), log_nil) } } }
  | ch, L, Θ, K, D, Ξ, cc_eval M (Some A), H
      with check_typ (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A => {
    | inright _ => rerr (blame_error (find_level_blame _ _ _ (pre_ctx H) A) (re_eval_typ Ξ M A))
    | inleft (exist _ i HA)
        with check_exp_typed (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A (ex_intro _ i HA) M => {
      | left HM => rok (exist _ _ (eval_check_ok HM), eval_log _ _ (pre_gctx H) M A HM)
      | right _ => rerr (re_eval_check Ξ M A) } }
  | ch, L, Θ, K, D, Ξ, cc_eval M None, H
      with @type_infer_at (gc_mk (gds_restrict D Θ) Ξ) (gs_tele Ξ) (pre_ctx H) M (user_exp_all M) => {
    | inleft (exist _ A HA) => rok (exist _ _ (eval_infer_ok A HA), eval_log _ _ (pre_gctx H) M A HA)
    | inright _ => rerr (re_eval_infer Ξ M) }.

  (** A command expanded, then run by [simple_step]. *)
  Definition xp_simple (ch : list path) (L : loader ch) (Θ : gdeps) (K : kmap) (D : list path) (Ξ : gstack)
    (c : ccmd) (H : exists ΘR, linv ch Θ K D ΘR Ξ) : rres ({r | post_xcmd ch Θ K D Ξ c r} * elog)%type :=
    match inspect (cmd_xp (mt_of _ _ (pre_gctx H)) (frame_skel Ξ) c) with
    | exist _ (xfail e) _ => rerr (re_import e)
    | exist _ (xok c') E =>
        match simple_step ch L Θ K D Ξ c' H with
        | rok (exist _ r Hp, l) => rok (exist _ r (xp_lift _ E Hp), l)
        | rerr e => rerr e
        end
    end.

  #[derive(eliminator=no)]
  Equations run_cmd_impl (ch : list path) (L : loader ch) (Θ : gdeps) (K : kmap) (D : list path) (Ξ : gstack)
    (c : ccmd) (H : exists ΘR, linv ch Θ K D ΘR Ξ) : rres ({r | post_xcmd ch Θ K D Ξ c r} * elog)%type by struct c :=
  | ch, L, Θ, K, D, Ξ, cc_mod x pv Δ0 cs, H with inspect (tele_xp (mt_of _ _ (pre_gctx H)) (frame_skel Ξ) Δ0) => {
    | exist _ (xfail e) _ => rerr (re_import e)
    | exist _ (xok Δ) EΔ with tele_ass_dec Δ => {
    | right _ => rerr (re_msg ("parameters of module " ++ x ++ " that are not assumptions"))
    | left Htel with check_ctx (gds_restrict D Θ) Ξ (pre_gctx H) (Δ ++ gs_tele Ξ) => {
      | right _ =>
          rerr (tele_blame_error (find_tele_blame _ _ _ (pre_ctx H) Δ)
                  (re_msg ("ill-formed parameters of module " ++ x)))
      | left HΔ with gs_fresh_dec x Ξ => {
        | right _ => rerr (re_msg ("duplicate name " ++ x))
        | left Hfr with cmds_step ch (run_cmd_impl ch L) Θ K D (gs_push (qname_in (gs_path Ξ) x) Δ Ξ) cs
                          (mod_pre H Htel Hfr HΔ) => {
          | rerr e => rerr e
          | rok (exist _ r Hr, l) with list_case (cs_stack r) => {
            | inleft (existT _ (mp, U) (exist _ _ HΞ)) =>
                rok (exist _ _ (xp_lift _ (cmd_xp_mod _ _ x pv _ _ cs EΔ) (mod_ok Htel Hfr HΔ Hr HΞ)), l)
            | inright _ => rerr (re_msg "internal error: a module body lost its frame") } } } } } }
  | ch, L, Θ, K, D, Ξ, cc_def x b pv A M, H => xp_simple ch L Θ K D Ξ (cc_def x b pv A M) H
  | ch, L, Θ, K, D, Ξ, cc_alias x pv Δ E, H => xp_simple ch L Θ K D Ξ (cc_alias x pv Δ E) H
  | ch, L, Θ, K, D, Ξ, cc_load fp, H => xp_simple ch L Θ K D Ξ (cc_load fp) H
  | ch, L, Θ, K, D, Ξ, cc_open E its, H => xp_simple ch L Θ K D Ξ (cc_open E its) H
  | ch, L, Θ, K, D, Ξ, cc_eval M oA, H => xp_simple ch L Θ K D Ξ (cc_eval M oA) H.

  Definition run_cmds_impl (ch : list path) (L : loader ch) := cmds_step ch (run_cmd_impl ch L).

  Definition run_unit_step (ch : list path) (L : loader ch) (Θ : gdeps) (K : kmap) (u : cunit)
    (H : ginv ch Θ K) : rres ({r | post_unit ch Θ K u r} * elog)%type :=
    match ch as ch0 return loader ch0 -> ginv ch0 Θ K -> rres ({r | post_unit ch0 Θ K u r} * elog)%type with
    | nil => fun _ _ => rerr (re_msg "internal error: no unit to run")
    | fp :: ch0 => fun L H =>
    match u as u0 return rres ({r | post_unit (fp :: ch0) Θ K u0 r} * elog)%type with
    | (imps, P0, cs) =>
        match run_cmds_impl (fp :: ch0) L Θ K nil nil imps (unit_pre H) with
        | rerr e => rerr e
        | rok (exist _ r1 Hr1, l1) =>
            match inspect (tele_xp (mt_of _ _ (unit_gctx H Hr1)) nil P0) with
            | exist _ (xfail e) _ => rerr (re_import e)
            | exist _ (xok P) EP =>
            match tele_ass_dec P with
            | right _ => rerr (re_msg "unit parameters that are not assumptions")
            | left Htel =>
            match check_ctx (gds_restrict (cs_dom r1) (cs_deps r1)) nil (unit_gctx H Hr1) P with
            | right _ =>
                rerr (tele_blame_error (find_tele_blame _ _ _ (wf_ctx_empty _ _ (unit_gctx H Hr1)) P)
                        (re_msg "ill-formed unit parameters"))
            | left HP =>
            match refs_check (gds_restrict (cs_dom r1) (cs_deps r1)) nil (unit_gctx H Hr1) (tele_refs nil P0) with
            | inleft (exist _ e _) => rerr (priv_error e)
            | inright Hac =>
                match run_cmds_impl (fp :: ch0) L (cs_deps r1) (cs_k r1) (cs_dom r1) (gs_push (q_abs fp nil) P nil) cs
                        (unit_body_pre H Hr1 Htel HP) with
                | rerr e => rerr e
                | rok (exist _ r2 Hr2, l2) =>
                    match list_case (cs_stack r2) with
                    | inleft (existT _ (mp, U) (exist _ _ HΞ)) =>
                        rok (exist _ _ (unit_ok (unit_gctx H Hr1) Hr1 EP Htel HP Hac Hr2 HΞ), log_app l1 l2)
                    | inright _ => rerr (re_msg "internal error: a unit body lost its frame")
                    end
                end
            end
            end
            end
            end
        end
    end
    end L H.

  #[derive(eliminator=no)]
  Equations run_unit_impl (ch : list path) (Hacc : Acc load_step ch) :
    forall Θ K u, ginv ch Θ K -> rres ({r | post_unit ch Θ K u r} * elog)%type by struct Hacc :=
  run_unit_impl ch Hacc :=
    run_unit_step ch (fun fp src Hn Hs => run_unit_impl (fp :: ch) (Acc_inv Hacc (load_step_intro Hn Hs))).

  Definition loader_of (ch : list path) (Hacc : Acc load_step ch) : loader ch :=
    fun fp src Hn Hs => run_unit_impl (fp :: ch) (Acc_inv Hacc (load_step_intro Hn Hs)).

  Lemma run_unit_impl_unfold : forall ch Hacc, run_unit_impl ch Hacc = run_unit_step ch (loader_of ch Hacc).
  Proof. intros; exact (run_unit_impl_equation_1 ch Hacc). Qed.

  (** The program given on the command line is run like an imported unit,
      with itself as the whole chain and nothing filed.  The log holds its
      own evals; those of the units it loads are checked but not returned. *)
  Definition prog_impl (prg : Cst.prog) (Hacc : Acc load_step (prog_path prg :: nil)) :
    rres (gdeps * gunit * list eval_entry)%type :=
    match to_core prg with
    | None => rerr (re_msg "cannot elaborate the program")
    | Some u =>
        match run_unit_impl (prog_path prg :: nil) Hacc nil nil u (ginv_nil _) with
        | rok (exist _ r _, l) => rok (us_deps r, us_unit r, proj1_sig l)
        | rerr e => rerr e
        end
    end.

  (** ** Soundness

      By construction: a result carries its [post_*], whatever the loader and
      the accessibility proof. *)

  Lemma unit_equiv {ch Θ K u r} :
    ginv ch Θ K -> post_unit ch Θ K u r ->
    exists ΘU, run_unit ch u ΘU (us_unit r) /\ ginv ch (us_deps r) (us_k r) /\
      gds_equiv ΘU (gds_restrict (us_dom r) (us_deps r)) /\ grows Θ (us_deps r) (us_dom r) /\
      ΘU ⊑ us_deps r /\ set_eq (us_dom r) (gds_dom ΘU).
  Proof.
    intros G Hp; destruct (Hp G) as (ΘU & Hu & G' & Hsub & Hdom & _ & _ & Hgr).
    exists ΘU; split; [ exact Hu | split; [ exact G' |] ].
    split; [ exact (equiv_restrict _ _ _ Hsub Hdom) |].
    split; [ exact Hgr | split; assumption ].
  Qed.

  (** A command runs as expanded. *)
  Theorem run_cmd_impl_sound : forall ch L Θ K D Ξ c H r ΘR,
      linv ch Θ K D ΘR Ξ -> run_cmd_impl ch L Θ K D Ξ c H = rok r ->
      exists c' ΘR', cmd_xp_ok ΘR Ξ c c' /\ run_cmd ch ΘR Ξ c' ΘR' (cs_stack (proj1_sig (fst r))) /\
        linv ch (cs_deps (proj1_sig (fst r))) (cs_k (proj1_sig (fst r))) (cs_dom (proj1_sig (fst r))) ΘR'
          (cs_stack (proj1_sig (fst r))) /\ logs_ok (proj1_sig (snd r)).
  Proof.
    intros * Hli _; destruct r as [[r Hr] [l Hl]]; destruct (Hr _ Hli) as (c' & ΘR' & ? & ? & ? & _); cbn; eauto 7.
  Qed.

  Theorem run_cmds_impl_sound : forall ch L Θ K D Ξ cs H r ΘR,
      linv ch Θ K D ΘR Ξ -> run_cmds_impl ch L Θ K D Ξ cs H = rok r ->
      exists ΘR', run_cmds ch ΘR Ξ cs ΘR' (cs_stack (proj1_sig (fst r))) /\
        linv ch (cs_deps (proj1_sig (fst r))) (cs_k (proj1_sig (fst r))) (cs_dom (proj1_sig (fst r))) ΘR'
          (cs_stack (proj1_sig (fst r))) /\ logs_ok (proj1_sig (snd r)).
  Proof.
    intros * Hli _; destruct r as [[r Hr] [l Hl]]; destruct (Hr _ Hli) as (ΘR' & ? & ? & _); cbn; eauto.
  Qed.

  Theorem run_unit_impl_sound : forall ch Hacc Θ K u H r,
      run_unit_impl ch Hacc Θ K u H = rok r ->
      exists ΘU, run_unit ch u ΘU (us_unit (proj1_sig (fst r))) /\
        ginv ch (us_deps (proj1_sig (fst r))) (us_k (proj1_sig (fst r))) /\
        gds_equiv ΘU (gds_restrict (us_dom (proj1_sig (fst r))) (us_deps (proj1_sig (fst r)))) /\
        logs_ok (proj1_sig (snd r)).
  Proof.
    intros * _; destruct r as [[r Hr] [l Hl]]; destruct (unit_equiv H Hr) as (ΘU & ? & ? & ? & _); cbn; eauto 6.
  Qed.

  (** ** Completeness

      By induction on the derivation, for every accessibility proof.  The
      executable loads only where the derivation does ([rc_load]), and
      under the same chain.  For a unit filed already, the derivation loads
      it, but the executable shares it without recursing.  Both expand a
      command with an oracle meeting the specification, hence identically. *)

  Lemma def_complete : forall ch ΘR Ξ x b pv A oM ΘR' Ξ' Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ),
      linv ch Θ K D ΘR Ξ -> run_cmd ch ΘR Ξ (cc_def x b pv A oM) ΘR' Ξ' ->
      exists r, defalias_step ch Θ K D Ξ (cc_def x b pv A oM) H = rok r.
  Proof.
    intros * Hli Hr; inversion Hr; subst; simp defalias_step;
      (destruct (gs_fresh_dec x Ξ) as [Hfr' | Hfr']; [| contradiction ]; simp defalias_step).
    - match goal with HM : _ ⍮ _ ⍮ _ ⊢ _ : A |- _ =>
          pose proof (equiv_exp _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HM) as HM0 end.
      match goal with |- context [check_typ ?a ?b ?c ?d ?e] => destruct (check_typ a b c d e) as [[j HA'] | HA'] end;
        simp defalias_step; [| exfalso; exact (not_exp_of_not_typ _ _ _ _ _ HA' HM0) ].
      match goal with |- context [check_exp_typed ?a ?b ?c ?d ?e ?f ?g] => destruct (check_exp_typed a b c d e f g) as [HM' | HM'] end;
        simp defalias_step; [ eexists; reflexivity |].
      exfalso; exact (HM' HM0).
    - (* an axiom: its type is a type *)
      match goal with |- context [check_typ ?a ?b ?c ?d ?e] => destruct (check_typ a b c d e) as [[j HA'] | HA'] end;
        simp defalias_step; [ eexists; reflexivity |].
      exfalso; eapply HA'.
      match goal with HA : _ ⍮ _ ⍮ _ ⊢ A : _ |- _ => exact (equiv_exp _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HA) end.
  Qed.

  Lemma alias_complete : forall ch ΘR Ξ x pv Δ E ΘR' Ξ' Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ),
      linv ch Θ K D ΘR Ξ -> run_cmd ch ΘR Ξ (cc_alias x pv Δ E) ΘR' Ξ' ->
      exists r, defalias_step ch Θ K D Ξ (cc_alias x pv Δ E) H = rok r.
  Proof.
    intros * Hli Hr; inversion Hr as [| | | ? ? ? ? ? ? ? Htel HΔ HE Hfr | | | | |]; subst; simp defalias_step.
    destruct (tele_ass_dec Δ) as [Htel' | Htel']; [| contradiction ]; simp defalias_step.
    match goal with |- context [check_ext ?a ?b ?c ?d ?e] => destruct (check_ext a b c d e) as [HΔ' | HΔ'] end;
      [| exfalso; apply HΔ'; exact (equiv_ext _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HΔ) ].
    simp defalias_step.
    match goal with |- context [check_modexp ?a ?b ?c ?d ?e] => destruct (check_modexp a b c d e) as [HE' | HE'] end;
      [| exfalso; apply HE'; exact (equiv_modexp _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HE) ].
    simp defalias_step.
    destruct (gs_fresh_dec x Ξ) as [Hfr' | Hfr']; [| contradiction ]; simp defalias_step.
    eexists; reflexivity.
  Qed.

  Lemma gens_complete : forall ΘR Ξ gs Ξ', gens_run ΘR Ξ gs Ξ' ->
      forall ch Θ K D (Hx : exists ΘR0, linv ch Θ K D ΘR0 Ξ), linv ch Θ K D ΘR Ξ ->
      exists r, gens_impl ch Θ K D Ξ gs Hx = rok r.
  Proof.
    induction 1 as [Ξ | Ξ d pv A M gs Ξ' HM Hfr Hg IH | Ξ d pv E gs Ξ' HE Hfr Hg IH];
      intros ch Θ K D Hx Hli; cbn [gens_impl]; [ eexists; reflexivity | |].
    - destruct (gs_fresh_dec d Ξ) as [Hfr' | Hfr']; [| contradiction ].
      match goal with |- context [check_exp ?a ?b ?c ?d ?e ?f] => destruct (check_exp a b c d e f) as [HM' | HM'] end;
        [| exfalso; apply HM'; exact (equiv_exp _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HM) ].
      destruct (IH ch Θ K D (gdef_pre Hx Hfr' HM') (proj2 (gdef_step (pv := pv) Hli Hfr' HM'))) as [[Ξ1 Hp] E].
      rewrite E; eexists; reflexivity.
    - destruct (gs_fresh_dec d Ξ) as [Hfr' | Hfr']; [| contradiction ].
      match goal with |- context [check_modexp ?a ?b ?c ?d ?e] => destruct (check_modexp a b c d e) as [HE' | HE'] end;
        [| exfalso; apply HE'; exact (equiv_modexp _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HE) ].
      destruct (IH ch Θ K D (galias_pre Hx Hfr' HE') (proj2 (galias_step (pv := pv) Hli Hfr' HE'))) as [[Ξ1 Hp] E1].
      rewrite E1; eexists; reflexivity.
  Qed.

  Lemma xp_simple_complete {ch L Θ K D ΘR Ξ c c'} (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ) :
    linv ch Θ K D ΘR Ξ -> cmd_xp_ok ΘR Ξ c c' -> (exists r, simple_step ch L Θ K D Ξ c' H = rok r) ->
    exists r, xp_simple ch L Θ K D Ξ c H = rok r.
  Proof.
    intros Hli Hx [r Er]; unfold xp_simple.
    pose proof (xp_eq (pre_gctx H) Hli Hx) as E.
    destruct (inspect _) as [[c'' | e] E']; [ assert (c'' = c') as -> by congruence | exfalso; congruence ].
    rewrite Er; destruct r as [[r Hp] l]; eexists; reflexivity.
  Qed.

  (** Every command but a module runs by [simple_step] once expanded. *)
  Lemma nonmod_complete {ch L Θ K D ΘR Ξ c c'} (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ) :
    ccmd_head c' <> 1 -> linv ch Θ K D ΘR Ξ -> cmd_xp_ok ΘR Ξ c c' ->
    (exists r, simple_step ch L Θ K D Ξ c' H = rok r) ->
    exists r, run_cmd_impl ch L Θ K D Ξ c H = rok r.
  Proof.
    intros Hh Hli Hx Hs.
    assert (Hc : ccmd_head c <> 1) by (destruct Hx as (mt & _ & Ex); rewrite <- (cmd_xp_head _ _ _ _ Ex); exact Hh).
    destruct c; try (exfalso; apply Hc; reflexivity); simp run_cmd_impl; eapply xp_simple_complete; eassumption.
  Qed.

  Theorem run_impl_complete :
    (forall ch ΘR Ξ c' ΘR' Ξ', run_cmd ch ΘR Ξ c' ΘR' Ξ' ->
       forall Hacc Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ), linv ch Θ K D ΘR Ξ ->
       forall c, cmd_xp_ok ΘR Ξ c c' ->
         exists r, run_cmd_impl ch (loader_of ch Hacc) Θ K D Ξ c H = rok r) /\
    (forall ch ΘR Ξ cs ΘR' Ξ', run_cmds ch ΘR Ξ cs ΘR' Ξ' ->
       forall Hacc Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ), linv ch Θ K D ΘR Ξ ->
         exists r, run_cmds_impl ch (loader_of ch Hacc) Θ K D Ξ cs H = rok r) /\
    (forall ch u ΘU U, run_unit ch u ΘU U ->
       forall Hacc Θ K (H : ginv ch Θ K), exists r, run_unit_impl ch Hacc Θ K u H = rok r).
  Proof.
    apply run_mut_dind.
    - (* a definition *)
      intros ch ΘR Ξ x b pv A M HM Hfr Hacc Θ K D H Hli c Hx.
      refine (nonmod_complete H _ Hli Hx _); [ cbn; discriminate |]; simp simple_step.
      destruct (def_complete ch ΘR Ξ x b pv A (Some M) _ _ Θ K D H Hli ltac:(constructor; assumption)) as [[Ξ1 Hp] Er].
      rewrite Er; simp simple_step; eexists; reflexivity.
    - (* an axiom *)
      intros ch ΘR Ξ x b pv A i HA Hfr Hacc Θ K D H Hli c Hx.
      refine (nonmod_complete H _ Hli Hx _); [ cbn; discriminate |]; simp simple_step.
      destruct (def_complete ch ΘR Ξ x b pv A None _ _ Θ K D H Hli ltac:(econstructor; eassumption)) as [[Ξ1 Hp] Er].
      rewrite Er; simp simple_step; eexists; reflexivity.
    - (* a module *)
      intros ch ΘR Ξ x pv Δ cs ΘR' mp U Htel HΔ Hfr Hr IH Hacc Θ K D H Hli c Hx.
      pose proof (xp_eq (pre_gctx H) Hli Hx) as Ex.
      assert (Hc : ccmd_head c = 1) by (rewrite <- (cmd_xp_head _ _ _ _ Ex); reflexivity).
      destruct c as [| x0 pv0 Δ0 cs0 | | | |]; try discriminate.
      destruct (cmd_xp_mod_inv _ _ _ _ _ _ _ Ex) as (Δ1 & EΔ & [= <- <- <- <-]).
      simp run_cmd_impl.
      destruct (inspect _) as [[Δ2 | e] EΔ']; [ assert (Δ2 = Δ) as -> by congruence | exfalso; congruence ].
      simp run_cmd_impl.
      destruct (tele_ass_dec Δ) as [Htel' | Htel']; [| contradiction ]; simp run_cmd_impl.
      match goal with |- context [check_ctx ?a ?b ?c ?d] => destruct (check_ctx a b c d) as [HΔ' | HΔ'] end;
        [| exfalso; apply HΔ'; exact (equiv_ctx _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HΔ) ].
      simp run_cmd_impl.
      destruct (gs_fresh_dec x Ξ) as [Hfr' | Hfr']; [| contradiction ]; simp run_cmd_impl.
      destruct (linv_push Hli Htel' Hfr' HΔ') as [_ Hli'].
      destruct (IH Hacc Θ K D (mod_pre H Htel' Hfr' HΔ') Hli') as [[[r Hp] l] E]; unfold run_cmds_impl in E; rewrite E.
      simp run_cmd_impl.
      destruct (Hp _ Hli') as (ΘR2 & Hr2 & _); destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ Hr2) as [F HF].
      destruct (list_case (cs_stack r)) as [[[mp' U'] [Ξ2 HΞ]] | HΞ]; simp run_cmd_impl; [ eexists; reflexivity | congruence ].
    - (* an alias *)
      intros ch ΘR Ξ x pv Δ E Htel HΔ HE Hfr Hacc Θ K D H Hli c Hx.
      refine (nonmod_complete H _ Hli Hx _); [ cbn; discriminate |]; simp simple_step.
      destruct (alias_complete ch ΘR Ξ x pv Δ E _ _ Θ K D H Hli ltac:(constructor; assumption)) as [[Ξ1 Hp] Er].
      rewrite Er; simp simple_step; eexists; reflexivity.
    - (* a load of a unit the judgment has *)
      intros ch ΘR Ξ fp U HU Hacc Θ K D H Hli c Hx.
      refine (nonmod_complete H _ Hli Hx _); [ cbn; discriminate |]; simp simple_step.
      pose proof (li_sub _ _ _ _ _ _ Hli _ _ HU) as HUg.
      assert (Hin : In fp D) by (apply (li_dom _ _ _ _ _ _ Hli), gds_dom_lookup; rewrite HU; discriminate).
      destruct (opt_case (gds_lookup Θ fp)) as [[U' HU'] | HU']; [| congruence ].
      assert (U' = U) as -> by congruence; simp simple_step.
      destruct (in_dec path_eq_dec fp D) as [Hin' | Hin']; [| contradiction ]; simp simple_step.
      eexists; reflexivity.
    - (* a load: shared if some other unit filed it, run otherwise *)
      intros ch ΘR Ξ fp src prg u ΘU U Hn Hnin Hl Hrd Hp Ht Hu IH Hacc Θ K D H Hli c Hx.
      refine (nonmod_complete H _ Hli Hx _); [ cbn; discriminate |]; simp simple_step.
      assert (HnD : ~ In fp D)
        by (intros Hin; apply (li_dom _ _ _ _ _ _ Hli), gds_dom_lookup in Hin; contradiction).
      destruct (opt_case (gds_lookup Θ fp)) as [[U' HU'] | Hng]; simp simple_step.
      + destruct (in_dec path_eq_dec fp D) as [Hin | Hin]; [ contradiction |]; simp simple_step.
        destruct (ginv_entry (li_g _ _ _ _ _ _ Hli) _ _ HU') as (Dfp & HK & _).
        destruct (opt_case (kfind K fp)) as [[Dfp' HK'] | HK']; [| congruence ]; simp simple_step.
        eexists; reflexivity.
      + destruct (in_dec path_eq_dec fp ch) as [Hin | Hin]; [ contradiction |]; simp simple_step.
        destruct (opt_case (load_path fp)) as [[src' Hl'] | Hl']; [| congruence ].
        assert (src' = src) as -> by congruence; simp simple_step.
        destruct (opt_case (read src)) as [[prg' Hr'] | Hr']; [| congruence ].
        assert (prg' = prg) as -> by congruence; simp simple_step.
        destruct (path_eq_dec (prog_path prg) fp) as [Hp' | Hp']; [| contradiction ]; simp simple_step.
        destruct (opt_case (to_core prg)) as [[u' Ht'] | Ht']; [| congruence ].
        assert (u' = u) as -> by congruence; simp simple_step.
        unfold loader_of.
        match goal with |- context [run_unit_impl (fp :: ch) ?a Θ K u ?b] =>
          destruct (IH a Θ K b) as [[[r Hpost] l] E']; rewrite E'; simp simple_step
        end.
        eexists; reflexivity.
    - (* an import: its target, then its generated commands *)
      intros ch ΘR Ξ E its gs Ξ' HE Hgen Hgs Hacc Θ K D H Hli c Hx.
      refine (nonmod_complete H _ Hli Hx _); [ cbn; discriminate |]; simp simple_step.
      match goal with |- context [check_modexp ?a ?b ?c ?d ?e] => destruct (check_modexp a b c d e) as [HE' | HE'] end;
        [| exfalso; apply HE'; exact (equiv_modexp _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HE) ].
      simp simple_step.
      pose proof (import_gen_ok_spec _ _ _ _ _ _ _ (linv_mt_spec Hli (pre_gctx H)) Hgen) as Eg.
      destruct (inspect _) as [[gs1 | e] Eg']; [ assert (gs1 = gs) as -> by congruence | exfalso; congruence ].
      simp simple_step.
      destruct (gens_complete _ _ _ _ Hgs _ _ _ _ H Hli) as [[Ξ1 Hp1] E1]; rewrite E1; simp simple_step.
      eexists; reflexivity.
    - (* an ascribed eval *)
      intros ch ΘR Ξ M A HM Hacc Θ K D H Hli c Hx.
      refine (nonmod_complete H _ Hli Hx _); [ cbn; discriminate |]; simp simple_step.
      pose proof (equiv_exp _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HM) as HM0.
      match goal with |- context [check_typ ?a ?b ?c ?d ?e] => destruct (check_typ a b c d e) as [[j HA'] | HA'] end;
        simp simple_step; [| exfalso; exact (not_exp_of_not_typ _ _ _ _ _ HA' HM0) ].
      match goal with |- context [check_exp_typed ?a ?b ?c ?d ?e ?f ?g] => destruct (check_exp_typed a b c d e f g) as [HM' | HM'] end;
        simp simple_step.
      { eexists; reflexivity. }
      exfalso; exact (HM' HM0).
    - (* an inferred eval: failure of inference contradicts its completeness *)
      intros ch ΘR Ξ M A HM Hacc Θ K D H Hli c Hx.
      refine (nonmod_complete H _ Hli Hx _); [ cbn; discriminate |]; simp simple_step.
      match goal with |- context [@type_infer_at ?g ?G ?a ?b ?c] => destruct (@type_infer_at g G a b c) as [[A' HA'] | Hno] end;
        simp simple_step.
      { eexists; reflexivity. }
      exfalso.
      pose proof (equiv_exp _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HM) as HM'.
      destruct (@alg_type_infer_complete (gc_mk (gds_restrict D Θ) Ξ) (gs_tele Ξ) A M (user_exp_all M) HM') as (B & HB & _).
      exact (Hno B HB).
    - intros ch ΘR Ξ Hacc Θ K D H Hli; unfold run_cmds_impl; simp cmds_step; eexists; reflexivity.
    - (* a sequence: the head's result is the judgment's, by determinism *)
      intros ch ΘR Ξ c c' cs ΘR1 Ξ1 ΘR2 Ξ2 Hac Hx Hc IHc Hcs IHcs Hacc Θ K D H Hli; unfold run_cmds_impl; simp cmds_step.
      match goal with |- context [refs_check ?a ?b ?c ?d] => destruct (refs_check a b c d) as [[e Hq] | Hac'] end;
        simp cmds_step; [ exfalso; apply Hq; exact (equiv_acc _ _ _ _ (linv_equiv Hli) Hac) |].
      destruct (IHc Hacc Θ K D H Hli c Hx) as [[[r1 Hp1] l1] E1]; rewrite E1; simp cmds_step.
      destruct (Hp1 _ Hli) as (c'' & ΘR1' & Hx' & Hr1 & Hli1 & _).
      rewrite (cmd_xp_ok_functional _ _ _ _ _ Hx' Hx) in Hr1.
      destruct (proj1 run_functional _ _ _ _ _ _ Hc _ _ _ Hr1) as [<- HΞ1]; subst Ξ1.
      destruct (IHcs Hacc _ _ _ (cons_pre H Hp1) Hli1) as [[[r2 Hp2] l2] E2]; unfold run_cmds_impl in E2; simp cmds_step in E2; rewrite E2.
      simp cmds_step; eexists; reflexivity.
    - (* a unit *)
      intros fp ch imps P0 P cs ΘR1 ΘR2 mp U Hi IHi HPx Htel HP Hac Hb IHb Hacc Θ K H.
      rewrite run_unit_impl_unfold; cbn [run_unit_step].
      destruct (IHi Hacc Θ K nil (unit_pre H) (nil_linv H)) as [[[r1 Hp1] l1] E1]; rewrite E1; cbv beta iota.
      destruct (Hp1 _ (nil_linv H)) as (ΘR1' & Hr1 & Hli1 & _).
      destruct (proj1 (proj2 run_functional) _ _ _ _ _ _ Hi _ _ _ Hr1) as [<- HΞ]; rewrite <- HΞ in Hli1.
      pose proof (tele_xp_ok_spec _ _ _ _ _ _ (linv_mt_spec Hli1 (unit_gctx H Hp1)) HPx) as EP.
      destruct (inspect _) as [[P1 | e] EP']; [ assert (P1 = P) as -> by congruence | exfalso; congruence ].
      destruct (tele_ass_dec P) as [Htel' | Htel']; [| contradiction ]; cbv beta iota.
      match goal with |- context [check_ctx ?a ?b ?c ?d] => destruct (check_ctx a b c d) as [HP' | HP'] end;
        [| exfalso; apply HP'; exact (equiv_ctx _ _ _ _ (linv_equiv Hli1) (linv_restrict_gctx Hli1) HP) ].
      match goal with |- context [refs_check ?a ?b ?c ?d] => destruct (refs_check a b c d) as [[e Hq] | Hac'] end;
        [ exfalso; apply Hq; exact (equiv_acc _ _ _ _ (linv_equiv Hli1) Hac) | cbv beta iota ].
      destruct (linv_push_unit Hli1 Htel' HP') as [_ Hli1'].
      destruct (IHb Hacc _ _ _ (unit_body_pre H Hp1 Htel' HP') Hli1') as [[[r2 Hp2] l2] E2]; rewrite E2; cbv beta iota.
      destruct (Hp2 _ Hli1') as (ΘR2' & Hr2 & _); destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ Hr2) as [F HF].
      destruct (list_case (cs_stack r2)) as [[[mp' U'] [Ξ2 HΞ2]] | HΞ2]; [ eexists; reflexivity | congruence ].
  Qed.

  (** The result is the judgment's, by determinism. *)
  Corollary run_cmd_impl_complete : forall ch ΘR Ξ c0 c ΘR' Ξ' Hacc Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ),
      linv ch Θ K D ΘR Ξ -> cmd_xp_ok ΘR Ξ c0 c -> run_cmd ch ΘR Ξ c ΘR' Ξ' ->
      exists r, run_cmd_impl ch (loader_of ch Hacc) Θ K D Ξ c0 H = rok r /\ cs_stack (proj1_sig (fst r)) = Ξ' /\
        linv ch (cs_deps (proj1_sig (fst r))) (cs_k (proj1_sig (fst r))) (cs_dom (proj1_sig (fst r))) ΘR' Ξ'.
  Proof.
    intros * Hli Hx Hr; destruct (proj1 run_impl_complete _ _ _ _ _ _ Hr Hacc _ _ _ H Hli _ Hx) as [r E].
    exists r; split; [ exact E |].
    destruct r as [[r Hp] l]; destruct (Hp _ Hli) as (c' & ΘR'' & Hx' & Hr' & Hli' & _); cbn [proj1_sig fst].
    rewrite (cmd_xp_ok_functional _ _ _ _ _ Hx' Hx) in Hr'.
    destruct (proj1 run_functional _ _ _ _ _ _ Hr _ _ _ Hr') as [<- HΞ]; rewrite <- HΞ in Hli'; split; [ symmetry; exact HΞ | exact Hli' ].
  Qed.

  Corollary run_cmds_impl_complete : forall ch ΘR Ξ cs ΘR' Ξ' Hacc Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ),
      linv ch Θ K D ΘR Ξ -> run_cmds ch ΘR Ξ cs ΘR' Ξ' ->
      exists r, run_cmds_impl ch (loader_of ch Hacc) Θ K D Ξ cs H = rok r /\ cs_stack (proj1_sig (fst r)) = Ξ' /\
        linv ch (cs_deps (proj1_sig (fst r))) (cs_k (proj1_sig (fst r))) (cs_dom (proj1_sig (fst r))) ΘR' Ξ'.
  Proof.
    intros * Hli Hr; destruct (proj1 (proj2 run_impl_complete) _ _ _ _ _ _ Hr Hacc _ _ _ H Hli) as [r E].
    exists r; split; [ exact E |].
    destruct r as [[r Hp] l]; destruct (Hp _ Hli) as (ΘR'' & Hr' & Hli' & _); cbn [proj1_sig fst].
    destruct (proj1 (proj2 run_functional) _ _ _ _ _ _ Hr _ _ _ Hr') as [<- HΞ]; rewrite <- HΞ in Hli'; split; [ symmetry; exact HΞ | exact Hli' ].
  Qed.

  Corollary run_unit_impl_complete : forall ch u ΘU U Hacc Θ K (H : ginv ch Θ K),
      run_unit ch u ΘU U ->
      exists r, run_unit_impl ch Hacc Θ K u H = rok r /\ us_unit (proj1_sig (fst r)) = U /\
        ginv ch (us_deps (proj1_sig (fst r))) (us_k (proj1_sig (fst r))) /\
        gds_equiv ΘU (gds_restrict (us_dom (proj1_sig (fst r))) (us_deps (proj1_sig (fst r)))).
  Proof.
    intros * Hu; destruct (proj2 (proj2 run_impl_complete) _ _ _ _ Hu Hacc _ _ H) as [r E].
    exists r; split; [ exact E |].
    destruct r as [[r Hp] l]; destruct (unit_equiv H Hp) as (ΘU' & Hu' & G' & Heq & _); cbn [proj1_sig fst].
    destruct (proj2 (proj2 run_functional) _ _ _ _ Hu _ _ _ eq_refl Hu') as [<- <-]; auto.
  Qed.

  (** ** The Program

      Only what the program imports is filed, so the whole accumulated [Θ] is
      equivalent to the judgment's.  Each log entry is an eval of the program,
      typed and normalized in the restriction it was checked in. *)

  Theorem prog_impl_sound : forall prg Hacc Θ U log,
      prog_impl prg Hacc = rok (Θ, U, log) ->
      (exists ΘR, prog_sem load_path read to_core prg ΘR U /\ gds_equiv ΘR Θ) /\
      (forall e, In e log ->
         ⊢g ev_deps e ⍮ ev_stack e /\ ev_deps e ⍮ ev_stack e ⍮ gs_tele (ev_stack e) ⊢ ev_exp e : ev_typ e /\
         nbe (ev_deps e) (ev_stack e) (gs_tele (ev_stack e)) (ev_exp e) (ev_typ e) (ev_nf e)).
  Proof.
    unfold prog_impl; intros * E.
    destruct (to_core prg) as [u |] eqn:Ht; [| discriminate ].
    revert E; match goal with |- context [run_unit_impl ?a ?b ?c ?d ?e ?f] =>
      destruct (run_unit_impl a b c d e f) as [[[r Hp] [l Hl]] | e'] end; intros E; [| discriminate ].
    injection E as <- <- <-; split; [| exact Hl ].
    destruct (unit_equiv (ginv_nil _) Hp) as (ΘU & Hu & G & _ & Hgr & Hsub & Hdom).
    exists ΘU; split; [ exists u; split; assumption |].
    split; [ exact Hsub |].
    intros y V HV.
    destruct (Hgr y ltac:(apply gds_dom_lookup; rewrite HV; discriminate)) as [[] | Hy].
    apply Hdom, gds_dom_lookup in Hy; destruct (gds_lookup ΘU y) as [V' |] eqn:E; [| contradiction ].
    rewrite (Hsub _ _ E) in HV; injection HV as ->; reflexivity.
  Qed.

  Theorem prog_impl_complete : forall prg ΘR U,
      prog_sem load_path read to_core prg ΘR U ->
      forall Hacc, exists Θ log, prog_impl prg Hacc = rok (Θ, U, log) /\ gds_equiv ΘR Θ.
  Proof.
    intros * (u & Ht & Hu) Hacc.
    destruct (proj2 (proj2 run_impl_complete) _ _ _ _ Hu Hacc nil nil (ginv_nil _)) as [[[r Hp] l] E].
    assert (Hprog : prog_impl prg Hacc = rok (us_deps r, us_unit r, proj1_sig l))
      by (unfold prog_impl; revert E; rewrite Ht; intros E; rewrite E; reflexivity).
    destruct (prog_impl_sound _ _ _ _ _ Hprog) as [(ΘR' & (u' & Ht' & Hu') & Heq) _].
    rewrite Ht in Ht'; injection Ht' as <-.
    destruct (proj2 (proj2 run_functional) _ _ _ _ Hu _ _ _ eq_refl Hu') as [<- ->].
    exists (us_deps r), (proj1_sig l); split; assumption.
  Qed.
End Impl.

(** ** Finitely Many Files

    Only here is [load_path] assumed to know finitely many files.  Each load
    adds one of them to the chain, so loading terminates, in whatever order
    it happens.  The executable never sees the list. *)

Section Files.
  Variable load_path : path -> option string.
  Variable all_files : list path.
  Hypothesis Hfiles : forall fp, (exists s, load_path fp = Some s) <-> In fp all_files.

  Definition unloaded (ch : list path) : nat :=
    List.length (filter (fun fp => if in_dec path_eq_dec fp ch then false else true) all_files).

  Lemma filter_mono : forall (p1 p2 : path -> bool) l, (forall y, p1 y = true -> p2 y = true) ->
      List.length (filter p1 l) <= List.length (filter p2 l).
  Proof.
    intros * Hpq; induction l as [| y l IH]; cbn; [ lia |].
    destruct (p1 y) eqn:Ep; [ rewrite (Hpq _ Ep); cbn; lia | destruct (p2 y); cbn; lia ].
  Qed.

  Lemma filter_strict : forall (p1 p2 : path -> bool) l x, (forall y, p1 y = true -> p2 y = true) ->
      In x l -> p1 x = false -> p2 x = true -> List.length (filter p1 l) < List.length (filter p2 l).
  Proof.
    intros * Hpq; induction l as [| y l IH]; intros Hin Hp Hq; [ contradiction |].
    pose proof (filter_mono p1 p2 l Hpq); destruct Hin as [-> | Hin]; cbn.
    - rewrite Hp, Hq; cbn; lia.
    - specialize (IH Hin Hp Hq).
      destruct (p1 y) eqn:Ep; [ rewrite (Hpq _ Ep); cbn; lia | destruct (p2 y); cbn; lia ].
  Qed.

  Theorem load_step_wf : well_founded (load_step load_path).
  Proof.
    apply (wf_incl _ _ (ltof _ unloaded)); [| apply well_founded_ltof ].
    intros ch' ch (fp & s & -> & Hn & Hs); unfold ltof, unloaded.
    apply (filter_strict _ _ _ fp).
    - intros y; destruct (in_dec path_eq_dec y (fp :: ch)) as [| Hy]; [ discriminate |].
      destruct (in_dec path_eq_dec y ch) as [Hy' |]; [ exfalso; apply Hy; right; exact Hy' | reflexivity ].
    - apply Hfiles; eauto.
    - destruct (in_dec path_eq_dec fp (fp :: ch)) as [| Hc]; [ reflexivity | exfalso; apply Hc; left; reflexivity ].
    - destruct (in_dec path_eq_dec fp ch); [ contradiction | reflexivity ].
  Qed.

  Corollary prog_impl_complete_wf : forall read to_core prg ΘR U,
      prog_sem load_path read to_core prg ΘR U ->
      exists Θ log, prog_impl load_path read to_core prg (load_step_wf _) = rok (Θ, U, log) /\ gds_equiv ΘR Θ.
  Proof. intros * H; exact (prog_impl_complete _ _ _ _ _ _ H _). Qed.
End Files.
