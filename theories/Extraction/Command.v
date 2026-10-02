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
From Mctt.Extraction Require Import NbE TypeCheck GlobalCheck.
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

Equations gm_has_mod_dec (ip : list string) (Φ : gmod) :
  {gm_has_mod Φ ip} + {~ gm_has_mod Φ ip} by struct ip :=
| nil, Φ => left I
| x :: ip', Φ with gm_find_mod Φ x => {
  | Some Φx => gm_has_mod_dec ip' Φx
  | None => right (fun H => H) }.

Definition gs_fresh_dec (x : string) (Ξ : gstack) : {gs_fresh x Ξ} + {~ gs_fresh x Ξ} :=
  match Ξ as Ξ0 return {gs_fresh x Ξ0} + {~ gs_fresh x Ξ0} with
  | (_, U) :: _ => check_gm_fresh x (gu_mod U)
  | nil => right (fun H => H)
  end.

(** ** Closures and Paths *)

Definition kmap : Set := list (fpath * list fpath).

Equations kfind (K : kmap) (fp : fpath) : option (list fpath) by struct K :=
| nil, _ => None
| (fq, D) :: K', fp => if path_beq fp fq then Some D else kfind K' fp.

Definition p_union (A B : list fpath) : list fpath :=
  fold_right (fun x acc => if in_dec path_eq_dec x acc then acc else x :: acc) A B.

Lemma p_union_iff : forall A B x, In x (p_union A B) <-> In x A \/ In x B.
Proof.
  intros A B; unfold p_union; induction B as [| y B IH]; intros x; cbn [fold_right In]; [ tauto |].
  destruct (in_dec path_eq_dec y _) as [Hy | Hy]; rewrite IH in *; cbn [In]; rewrite ?IH.
  - split; [ tauto | intros [H | [<- | H]]; tauto ].
  - tauto.
Qed.

Definition path_str (fp : fpath) : string := String.concat "::" fp.

(** The chain up to the unit imported again, where the cycle starts. *)
Equations chain_to (fp : fpath) (ch : list fpath) : list fpath by struct ch :=
| _, nil => nil
| fp, fq :: ch' => if path_beq fp fq then fq :: nil else fq :: chain_to fp ch'.

(** The cycle, from the unit imported again back to itself. *)
Definition cycle_chain (fp : fpath) (ch : list fpath) : list fpath :=
  List.app (rev (chain_to fp ch)) (fp :: nil).

Definition cycle_msg (cyc : list fpath) : string :=
  "cyclic import: " ++ String.concat " -> " (map path_str cyc).

(** ** Results

    The errors a run can fail with, carrying the terms involved, if any, for
    the driver to print.  The message of [re_unit] concerns the unit at the
    path it carries and does not repeat that path. *)

Inductive run_error : Set :=
| re_msg : string -> run_error
| re_def : string -> gstack -> typ -> exp -> run_error
| re_eval_check : gstack -> exp -> typ -> run_error
| re_eval_infer : gstack -> exp -> run_error
| re_cycle : list fpath -> run_error
| re_unit : fpath -> string -> run_error.

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

Lemma dom_file : forall fp U Θ fq, In fq (gds_dom (file fp U Θ)) <-> fq = fp \/ In fq (gds_dom Θ).
Proof.
  intros; rewrite !gds_dom_lookup, file_lookup; destruct (path_beq fq fp) eqn:Hb.
  - apply path_beq_true in Hb; split; [ auto | discriminate ].
  - split; [ auto | intros [-> | H]; [ rewrite path_beq_refl in Hb; discriminate | exact H ] ].
Qed.

Section Impl.
  Variables (load_path : fpath -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  #[local] Abbreviation run_cmd := (run_cmd load_path read to_core).
  #[local] Abbreviation run_cmds := (run_cmds load_path read to_core).
  #[local] Abbreviation run_unit := (run_unit load_path read to_core).
  #[local] Abbreviation canon := (canon load_path read to_core).
  #[local] Abbreviation run_wf := (run_wf load_path read to_core).
  #[local] Abbreviation run_functional := (run_functional load_path read to_core).

  (** ** The Invariants *)

  Definition set_eq (A B : list fpath) : Prop := forall x, In x A <-> In x B.

  (** A set of paths closed under the closures [K] records. *)
  Definition closedK (K : kmap) (D : list fpath) : Prop :=
    forall x Dx, In x D -> kfind K x = Some Dx -> incl Dx D.

  (** A filed unit is what loading its file yields, under a chain starting
      with it, at the height of the state that run ended in.  That state is
      filed as well, and [K] records its domain, closed. *)
  Definition entry_ok (Θ : gdeps) (K : kmap) (fp : fpath) (U : gunit) : Prop :=
    exists D, kfind K fp = Some D /\ closedK K D /\
      exists src prg u ch ΘU, load_path fp = Some src /\ read src = Some prg /\ prog_path prg = fp /\
        to_core prg = Some u /\ run_unit (fp :: ch) u ΘU U /\
        gds_level Θ fp = Some (List.length ΘU) /\ ΘU ⊑ Θ /\ set_eq D (gds_dom ΘU).

  (** The invariant of the global state for a run under chain [ch]; in
      particular, nothing on the chain is filed yet. *)
  Record ginv (ch : list fpath) (Θ : gdeps) (K : kmap) : Prop :=
    { gi_wf : wf_gdeps Θ
    ; gi_chain : forall x, In x ch -> gds_lookup Θ x = None
    ; gi_entry : forall fp U, gds_lookup Θ fp = Some U -> entry_ok Θ K fp U
    ; gi_kdom : forall fp D, kfind K fp = Some D -> gds_lookup Θ fp <> None }.

  (** The invariant of the unit being run, relative to the judgment's state
      [ΘR]: the units [D] it imported are those of [ΘR], filed identically in
      [Θ]. *)
  Record linv (ch : list fpath) (Θ : gdeps) (K : kmap) (D : list fpath) (ΘR : gdeps) (Ξ : gstack) : Prop :=
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
  Definition grows (Θ Θ' : gdeps) (D' : list fpath) : Prop :=
    forall x, In x (gds_dom Θ') -> In x (gds_dom Θ) \/ In x D'.

  Record cstate : Set := cst { cs_deps : gdeps; cs_k : kmap; cs_dom : list fpath; cs_stack : gstack }.
  Record ustate : Set := ust { us_deps : gdeps; us_k : kmap; us_dom : list fpath; us_unit : gunit }.

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

  Definition post_unit ch Θ K u (r : ustate) : Prop :=
    ginv ch Θ K ->
      exists ΘU, run_unit ch u ΘU (us_unit r) /\ ginv ch (us_deps r) (us_k r) /\
        ΘU ⊑ us_deps r /\ set_eq (us_dom r) (gds_dom ΘU) /\ closedK (us_k r) (us_dom r) /\
        ext Θ K (us_deps r) (us_k r) /\ grows Θ (us_deps r) (us_dom r).

  (** ** Consequences of the Invariants *)

  Lemma ginv_canon {ch Θ K} : ginv ch Θ K -> canon Θ.
  Proof.
    intros G fp U HU.
    destruct (gi_entry _ _ _ G _ _ HU) as (D & _ & _ & src & prg & u & ch0 & ΘU & Hl & Hr & _ & Ht & Hu & Hlv & _).
    exists src, prg, u, ch0, ΘU; repeat split; assumption.
  Qed.

  Lemma ginv_closure {ch Θ K D} : ginv ch Θ K -> closedK K D -> closure_ok D Θ.
  Proof.
    intros G Hcl fp U Hin HU.
    destruct (gi_entry _ _ _ G _ _ HU) as (Dfp & HK & _ & src & prg & u & ch0 & ΘU & _ & _ & _ & _ & Hu & Hlv & Hsub & Hdom).
    destruct (proj2 (proj2 run_wf) _ _ _ _ Hu) as (_ & HcU & HwU); cbn [hd] in HwU.
    pose proof (canon_agree _ _ _ _ _ HcU (ginv_canon G)) as Hag.
    exists ΘU; split; [ exact HwU | split; [ exact Hlv |] ].
    intros x V HV; split; [ apply (Hcl _ _ Hin HK), Hdom, gds_dom_lookup; rewrite HV; discriminate |].
    split; [ apply Hsub, HV | symmetry; exact (proj2 (Hag _ _ _ HV (Hsub _ _ HV))) ].
  Qed.

  Lemma ginv_restrict_wf {ch Θ K D} : ginv ch Θ K -> closedK K D -> wf_gdeps (gds_restrict D Θ).
  Proof. intros G Hcl; exact (restrict_wf _ _ (gi_wf _ _ _ G) (ginv_closure G Hcl)). Qed.

  Lemma linv_in {ch Θ K D ΘR Ξ} : linv ch Θ K D ΘR Ξ -> forall x, In x D -> gds_lookup Θ x <> None.
  Proof.
    intros Hli x Hx; apply (li_dom _ _ _ _ _ _ Hli), gds_dom_lookup in Hx.
    destruct (gds_lookup ΘR x) eqn:E; [| contradiction ].
    rewrite (li_sub _ _ _ _ _ _ Hli _ _ E); discriminate.
  Qed.

  Lemma linv_equiv {ch Θ K D ΘR Ξ} : linv ch Θ K D ΘR Ξ -> gds_equiv ΘR (gds_restrict D Θ).
  Proof.
    intros Hli; exact (equiv_restrict _ _ _ _ _ _ (li_canon _ _ _ _ _ _ Hli) (ginv_canon (li_g _ _ _ _ _ _ Hli))
                         (li_sub _ _ _ _ _ _ Hli) (li_dom _ _ _ _ _ _ Hli)).
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
    linv ch Θ K D ΘR Ξ -> gs_fresh x Ξ -> ⊢ gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
    ⊢ ΘR ⍮ Ξ ⍮ Δ ++ gs_tele Ξ /\ linv ch Θ K D ΘR (gs_push (path_in (gs_path Ξ) x) Δ Ξ).
  Proof.
    intros Hli Hfr HΔ.
    assert (HΔ' : ⊢ ΘR ⍮ Ξ ⍮ Δ ++ gs_tele Ξ)
      by exact (equiv_ctx _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HΔ).
    split; [ exact HΔ' |]; apply (linv_stack Hli); [| exact (stack_in_push _ _ _ _ (li_stack _ _ _ _ _ _ Hli) Hfr) ].
    constructor; constructor; [ apply wf_gctx_stack, (li_wf _ _ _ _ _ _ Hli) | constructor; constructor; exact HΔ' |].
    destruct Ξ as [| [mp U] Ξ]; [ contradiction |]; cbn; exists x; split; [ reflexivity | exact Hfr ].
  Qed.

  (** A unit's own frame: its path heads the chain, so it is not filed. *)
  Lemma linv_push_unit {fp ch Θ K D ΘR P} :
    linv (fp :: ch) Θ K D ΘR nil -> ⊢ gds_restrict D Θ ⍮ nil ⍮ P ->
    ⊢ ΘR ⍮ nil ⍮ P /\ linv (fp :: ch) Θ K D ΘR (gs_push (p_abs fp nil) P nil).
  Proof.
    intros Hli HP.
    assert (HP' : ⊢ ΘR ⍮ nil ⍮ P)
      by exact (equiv_ctx _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HP).
    split; [ exact HP' |]; apply (linv_stack Hli); [| intros ? ? [[= <- <-] | []]; left; reflexivity ].
    constructor; constructor; [ apply wf_gctx_stack, (li_wf _ _ _ _ _ _ Hli) | constructor; constructor; cbn; rewrite app_nil_r; exact HP' |].
    cbn; apply gds_fresh_iff.
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

  Lemma ginv_nil : forall ch, ginv ch nil nil.
  Proof. intros; constructor; [ constructor | reflexivity | discriminate | discriminate ]. Qed.

  Lemma nil_linv {ch Θ K} : ginv ch Θ K -> linv ch Θ K nil nil nil.
  Proof.
    intros G; constructor; [ exact G | discriminate | intros ?; cbn; tauto | intros ? ? [] | | apply canon_nil | intros ? ? [] ].
    constructor; constructor; constructor.
  Qed.

  (** ** One Step per Rule

      Each lemma proves the [post_*] of one branch of the executable from the
      checks that branch makes. *)

  Lemma def_ok {ch Θ K D Ξ x b pv A M} :
    gs_fresh x Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    post_cmd ch Θ K D Ξ (cc_def x b pv A M) (cst Θ K D (gs_add x (gs_def b pv Ξ A M) Ξ)).
  Proof.
    intros Hfr HM ΘR Hli; cbn [cs_deps cs_k cs_dom cs_stack].
    assert (Hr : run_cmd ch ΘR Ξ (cc_def x b pv A M) ΘR (gs_add x (gs_def b pv Ξ A M) Ξ)).
    { constructor; [| exact Hfr ].
      exact (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HM). }
    exists ΘR; split; [ exact Hr | split; [ exact (linv_run_same Hli Hr) | split; [ apply ext_refl | apply grows_refl ] ] ].
  Qed.

  Lemma eval_check_ok {ch Θ K D Ξ M A} :
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A -> post_cmd ch Θ K D Ξ (cc_eval M (Some A)) (cst Θ K D Ξ).
  Proof.
    intros HM ΘR Hli; cbn [cs_deps cs_k cs_dom cs_stack].
    assert (Hr : run_cmd ch ΘR Ξ (cc_eval M (Some A)) ΘR Ξ)
      by (constructor; exact (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HM)).
    exists ΘR; split; [ exact Hr | split; [ exact Hli | split; [ apply ext_refl | apply grows_refl ] ] ].
  Qed.

  Lemma eval_infer_ok {ch Θ K D Ξ M} (A : typ) :
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A -> post_cmd ch Θ K D Ξ (cc_eval M None) (cst Θ K D Ξ).
  Proof.
    intros HM ΘR Hli; cbn [cs_deps cs_k cs_dom cs_stack].
    assert (Hr : run_cmd ch ΘR Ξ (cc_eval M None) ΘR Ξ)
      by (econstructor; exact (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HM)).
    exists ΘR; split; [ exact Hr | split; [ exact Hli | split; [ apply ext_refl | apply grows_refl ] ] ].
  Qed.

  Lemma mod_pre {ch Θ K D Ξ x Δ} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> gs_fresh x Ξ -> ⊢ gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
    exists ΘR, linv ch Θ K D ΘR (gs_push (path_in (gs_path Ξ) x) Δ Ξ).
  Proof. intros [ΘR Hli] Hfr HΔ; exists ΘR; exact (proj2 (linv_push Hli Hfr HΔ)). Qed.

  Lemma mod_ok {ch Θ K D Ξ x Δ cs r mp U Ξ2} :
    gs_fresh x Ξ -> ⊢ gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
    post_cmds ch Θ K D (gs_push (path_in (gs_path Ξ) x) Δ Ξ) cs r -> cs_stack r = (mp, U) :: Ξ2 ->
    post_cmd ch Θ K D Ξ (cc_mod x Δ cs) (cst (cs_deps r) (cs_k r) (cs_dom r) (gs_add x (ge_mod Δ (gu_mod U)) Ξ)).
  Proof.
    intros Hfr HΔ Hpost HΞ ΘR Hli; cbn [cs_deps cs_k cs_dom cs_stack].
    destruct (linv_push Hli Hfr HΔ) as [HΔ' Hli'].
    destruct (Hpost _ Hli') as (ΘR' & Hrun & Hli2 & Hext & Hgr).
    rewrite HΞ in Hrun, Hli2.
    destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ Hrun) as [F HF]; injection HF as <- ->.
    assert (Hr : run_cmd ch ΘR Ξ (cc_mod x Δ cs) ΘR' (gs_add x (ge_mod Δ (gu_mod U)) Ξ))
      by (econstructor; eassumption).
    exists ΘR'; split; [ exact Hr | split; [| split; assumption ] ].
    apply (linv_stack Hli2); [ exact (proj1 (linv_run_wf Hli Hr)) | exact (linv_run_stack Hli Hr) ].
  Qed.

  Lemma import_in_ok {ch Θ K D Ξ fp ip U} :
    In fp D -> gds_lookup Θ fp = Some U -> gm_has_mod (gu_mod U) ip ->
    post_cmd ch Θ K D Ξ (cc_import fp ip) (cst Θ K D Ξ).
  Proof.
    intros Hin HU Hm ΘR Hli; cbn [cs_deps cs_k cs_dom cs_stack].
    apply (li_dom _ _ _ _ _ _ Hli), gds_dom_lookup in Hin.
    destruct (gds_lookup ΘR fp) as [V |] eqn:E; [| contradiction ].
    rewrite (li_sub _ _ _ _ _ _ Hli _ _ E) in HU; injection HU as ->.
    assert (Hr : run_cmd ch ΘR Ξ (cc_import fp ip) ΘR Ξ) by (eapply rc_import_filed; eassumption).
    exists ΘR; split; [ exact Hr | split; [ exact Hli | split; [ apply ext_refl | apply grows_refl ] ] ].
  Qed.

  (** Importing a filed unit that the unit being run has not imported yet:
      the judgment loads it, which the entry of [Θ] justifies once the chain
      is changed. *)
  Lemma import_hit_ok {ch Θ K D Ξ fp ip U Dfp} :
    ~ In fp D -> gds_lookup Θ fp = Some U -> kfind K fp = Some Dfp -> gm_has_mod (gu_mod U) ip ->
    post_cmd ch Θ K D Ξ (cc_import fp ip) (cst Θ K (p_union D (fp :: Dfp)) Ξ).
  Proof.
    intros Hnin HU HK Hm ΘR Hli; cbn [cs_deps cs_k cs_dom cs_stack].
    pose proof (li_g _ _ _ _ _ _ Hli) as G.
    destruct (gi_entry _ _ _ G _ _ HU)
      as (Dfp' & HK' & Hcl & src & prg & u & ch0 & ΘU & Hl & Hrd & Hp & Ht & Hu & _ & Hsub & Hdom).
    rewrite HK in HK'; injection HK' as <-.
    assert (Hn : gds_lookup ΘR fp = None)
      by (apply gds_dom_none; intros Hin; apply Hnin, (li_dom _ _ _ _ _ _ Hli), Hin).
    assert (Hnch : ~ In fp ch) by (intros Hin; rewrite (gi_chain _ _ _ G _ Hin) in HU; discriminate).
    assert (Hu' : run_unit (fp :: ch) u ΘU U).
    { apply (proj2 (proj2 (run_chain_irrel load_path read to_core)) _ _ _ _ Hu ch).
      intros x [<- | Hin].
      - exact (proj2 (proj2 (run_chain_fresh load_path read to_core)) _ _ _ _ Hu _ (or_introl eq_refl)).
      - exact (sub_none _ _ _ Hsub (gi_chain _ _ _ G _ Hin)). }
    assert (Hr : run_cmd ch ΘR Ξ (cc_import fp ip) (gds_merge ΘR (file fp U ΘU)) Ξ)
      by (eapply rc_import_load; eassumption).
    destruct (linv_run_wf Hli Hr) as (Hwf' & Hc' & _).
    exists (gds_merge ΘR (file fp U ΘU)); split; [ exact Hr |].
    split; [| split; [ apply ext_refl | apply grows_refl ] ].
    constructor; [ exact G | | | | exact Hwf' | exact Hc' | exact (li_stack _ _ _ _ _ _ Hli) ].
    - intros y V HV; apply merge_inv in HV as [HV | HV]; [ exact (li_sub _ _ _ _ _ _ Hli _ _ HV) |].
      rewrite file_lookup in HV; destruct (path_beq y fp) eqn:Hb; [| exact (Hsub _ _ HV) ].
      apply path_beq_true in Hb as ->; injection HV as <-; exact HU.
    - intros y; rewrite p_union_iff, dom_merge, dom_file, <- (li_dom _ _ _ _ _ _ Hli y), <- (Hdom y); cbn [In].
      intuition congruence.
    - intros y Dy Hy HKy; apply p_union_iff in Hy as [Hy | [<- | Hy]]; intros z Hz; apply p_union_iff.
      + left; exact (li_closed _ _ _ _ _ _ Hli _ _ Hy HKy _ Hz).
      + rewrite HK in HKy; injection HKy as <-; right; right; exact Hz.
      + right; right; exact (Hcl _ _ Hy HKy _ Hz).
  Qed.

  Lemma load_pre {ch Θ K D Ξ fp} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> gds_lookup Θ fp = None -> ~ In fp ch -> ginv (fp :: ch) Θ K.
  Proof.
    intros [ΘR Hli] Hn Hnch; pose proof (li_g _ _ _ _ _ _ Hli) as [].
    constructor; auto; intros x [<- | Hx]; auto.
  Qed.

  (** A loaded unit is filed above the restriction to its closure, matching
      the judgment, which files it above the state its run ended in. *)
  Definition load_state (fp : fpath) (D : list fpath) (Ξ : gstack) (r : ustate) : cstate :=
    cst (gds_merge (us_deps r) (file fp (us_unit r) (gds_restrict (us_dom r) (us_deps r))))
        ((fp, us_dom r) :: us_k r) (p_union D (fp :: us_dom r)) Ξ.

  Lemma load_ok {ch Θ K D Ξ fp ip src prg u r} :
    gds_lookup Θ fp = None -> ~ In fp ch ->
    load_path fp = Some src -> read src = Some prg -> prog_path prg = fp -> to_core prg = Some u ->
    post_unit (fp :: ch) Θ K u r -> gm_has_mod (gu_mod (us_unit r)) ip ->
    post_cmd ch Θ K D Ξ (cc_import fp ip) (load_state fp D Ξ r).
  Proof.
    intros Hn Hnch Hl Hrd Hp Ht Hpost Hm ΘR Hli.
    pose proof (li_g _ _ _ _ _ _ Hli) as G.
    assert (Gin : ginv (fp :: ch) Θ K) by (eapply load_pre; [ exists ΘR; exact Hli | assumption | assumption ]).
    destruct r as [Θ1 K1 Dfp U]; unfold load_state; cbn [us_deps us_k us_dom us_unit cs_deps cs_k cs_dom cs_stack] in *.
    destruct (Hpost Gin) as (ΘU & Hu & G1 & Hsub1 & Hdom1 & Hcl1 & [Hext1 HextK] & Hgr1).
    cbn [us_deps us_k us_dom us_unit] in *.
    destruct (proj2 (proj2 run_wf) _ _ _ _ Hu) as (HwU & HcU & HUu); cbn [hd] in HUu.
    assert (HnR : gds_lookup ΘR fp = None) by exact (sub_none _ _ _ (li_sub _ _ _ _ _ _ Hli) Hn).
    assert (Hrun : run_cmd ch ΘR Ξ (cc_import fp ip) (gds_merge ΘR (file fp U ΘU)) Ξ)
      by (eapply rc_import_load; eassumption).
    destruct (linv_run_wf Hli Hrun) as (Hwf' & Hc' & _).
    set (R := gds_restrict Dfp Θ1).
    assert (Hn1 : gds_lookup Θ1 fp = None) by exact (gi_chain _ _ _ G1 _ (or_introl eq_refl)).
    assert (HnR1 : gds_lookup R fp = None)
      by (unfold R; rewrite gds_lookup_restrict; destruct (existsb _ _); [ exact Hn1 | reflexivity ]).
    assert (HwR : wf_gdeps R) by exact (ginv_restrict_wf G1 Hcl1).
    assert (HeqU : gds_equiv ΘU R)
      by exact (equiv_restrict _ _ _ _ _ _ HcU (ginv_canon G1) Hsub1 Hdom1).
    assert (HwF : wf_gdeps (file fp U R))
      by (apply wf_file; [ exact HwR | exact HnR1 | exact (unit_levels_grow _ _ _ _ (proj1 HeqU) HwR HnR1 HUu) ]).
    assert (Hag : gds_agree Θ1 (file fp U R)).
    { intros y V V' H1 H2; rewrite file_lookup in H2; destruct (path_beq y fp) eqn:Hb.
      - apply path_beq_true in Hb; subst; congruence.
      - unfold R in H2; rewrite gds_lookup_restrict in H2.
        destruct (existsb (path_beq y) Dfp) eqn:Hy; [| discriminate ].
        rewrite H1 in H2; injection H2 as <-; split; [ reflexivity |].
        unfold file, R; rewrite gds_level_cons, gds_level_restrict, Hy.
        destruct (gds_level_lookup _ _ _ H1) as [k Hk]; rewrite Hk; reflexivity. }
    set (ΘN := gds_merge Θ1 (file fp U R)).
    assert (HwN : wf_gdeps ΘN) by exact (merge_wf _ _ (gi_wf _ _ _ G1) HwF Hag).
    assert (Hsub1N : Θ1 ⊑ ΘN) by exact (merge_left _ _ Hag).
    assert (HfpN : gds_lookup ΘN fp = Some U)
      by (apply (merge_right _ _ Hag); rewrite file_lookup, path_beq_refl; reflexivity).
    assert (HlvN : gds_level ΘN fp = Some (List.length ΘU)).
    { unfold ΘN; rewrite gds_level_merge, (proj2 (gds_level_none _ _) Hn1), file_level by exact HnR1; cbn.
      f_equal; symmetry; apply equiv_length; [ exact HwU | exact HwR | | apply top_ne_trim | apply HeqU ].
      exact (proj2 (proj2 (run_top_ne load_path read to_core)) _ _ _ _ Hu). }
    assert (HsubU : ΘU ⊑ ΘN) by exact (gds_sub_trans _ _ _ Hsub1 Hsub1N).
    assert (HK1 : forall y Dy, kfind K1 y = Some Dy -> y <> fp)
      by (intros y Dy HKy ->; exact (gi_kdom _ _ _ G1 _ _ HKy Hn1)).
    assert (HN1 : forall y V, gds_lookup ΘN y = Some V -> y = fp /\ V = U \/ gds_lookup Θ1 y = Some V).
    { intros y V HV; apply merge_inv in HV as [HV | HV]; [ auto |].
      rewrite file_lookup in HV; destruct (path_beq y fp) eqn:Hb.
      - apply path_beq_true in Hb; injection HV as <-; auto.
      - right; exact (restrict_sub _ _ _ _ HV). }
    assert (Hd1 : forall y, In y (gds_dom Θ1) -> y <> fp)
      by (intros y Hy ->; apply gds_dom_lookup in Hy; contradiction).
    assert (Hdfp : forall y, In y Dfp -> y <> fp)
      by (intros y Hy; apply Hd1, (sub_dom _ _ _ Hsub1), Hdom1, Hy).
    assert (GN : ginv ch ΘN ((fp, Dfp) :: K1)).
    { constructor; [ exact HwN | | | ].
      - intros y Hy; apply merge_none; split; [ exact (gi_chain _ _ _ G1 _ (or_intror Hy)) |].
        rewrite file_lookup, path_beq_false by (intros ->; contradiction).
        exact (sub_none _ _ _ (restrict_sub _ _) (gi_chain _ _ _ G1 _ (or_intror Hy))).
      - intros y V HV; destruct (HN1 _ _ HV) as [[-> ->] | HV1].
        + exists Dfp; simp kfind; rewrite path_beq_refl; split; [ reflexivity |].
          split; [ exact (closedK_cons _ _ _ _ Hcl1 Hdfp) |].
          exists src, prg, u, ch, ΘU; do 7 (split; [ assumption |]); exact Hdom1.
        + destruct (gi_entry _ _ _ G1 _ _ HV1)
            as (Dy & HKy & Hcly & src' & prg' & u' & ch' & ΘUy & ? & ? & ? & ? & ? & Hlvy & Hsuby & Hdomy).
          assert (Hy : y <> fp) by (eapply HK1; eassumption).
          exists Dy; simp kfind; rewrite path_beq_false by exact Hy; split; [ exact HKy |].
          split; [ apply closedK_cons; [ exact Hcly | intros z Hz; apply Hd1, (sub_dom _ _ _ Hsuby), Hdomy, Hz ] |].
          exists src', prg', u', ch', ΘUy; do 5 (split; [ assumption |]).
          split; [ apply merge_level; [ exact Hag | left; exact Hlvy ] |].
          split; [ exact (gds_sub_trans _ _ _ Hsuby Hsub1N) | exact Hdomy ].
      - intros y Dy HKy; simp kfind in HKy; destruct (path_beq y fp) eqn:Hb.
        + apply path_beq_true in Hb as ->; rewrite HfpN; discriminate.
        + intros E; apply (gi_kdom _ _ _ G1 _ _ HKy), (sub_none _ _ _ Hsub1N), E. }
    exists (gds_merge ΘR (file fp U ΘU)); cbn [cs_deps cs_k cs_dom cs_stack us_deps us_k us_dom us_unit]; split; [ exact Hrun |].
    split; [| split ].
    - constructor; [ exact GN | | | | exact Hwf' | exact Hc' | exact (li_stack _ _ _ _ _ _ Hli) ].
      + intros y V HV; apply merge_inv in HV as [HV | HV].
        * exact (Hsub1N _ _ (Hext1 _ _ (li_sub _ _ _ _ _ _ Hli _ _ HV))).
        * rewrite file_lookup in HV; destruct (path_beq y fp) eqn:Hb; [| exact (HsubU _ _ HV) ].
          apply path_beq_true in Hb as ->; injection HV as <-; exact HfpN.
      + intros y; rewrite p_union_iff, dom_merge, dom_file, <- (li_dom _ _ _ _ _ _ Hli y), <- (Hdom1 y); cbn [In].
        intuition congruence.
      + intros y Dy Hy HKy; simp kfind in HKy; destruct (path_beq y fp) eqn:Hb.
        * apply path_beq_true in Hb as ->; injection HKy as <-; intros z Hz; apply p_union_iff; right; right; exact Hz.
        * intros z Hz; apply p_union_iff; apply p_union_iff in Hy as [Hy | [<- | Hy]].
          -- left; pose proof (linv_in Hli _ Hy) as Hy'.
             destruct (gds_lookup Θ y) as [Vy |] eqn:Ey; [| contradiction ].
             destruct (gi_entry _ _ _ G _ _ Ey) as (Dy' & HKy' & _).
             rewrite (HextK _ _ HKy') in HKy; injection HKy as <-.
             exact (li_closed _ _ _ _ _ _ Hli _ _ Hy HKy' _ Hz).
          -- rewrite path_beq_refl in Hb; discriminate.
          -- right; right; exact (Hcl1 _ _ Hy HKy _ Hz).
    - split; [ exact (gds_sub_trans _ _ _ Hext1 Hsub1N) |].
      intros y Dy HKy; simp kfind; rewrite path_beq_false; [ exact (HextK _ _ HKy) |].
      intros ->; exact (gi_kdom _ _ _ G _ _ HKy Hn).
    - intros y Hy; unfold ΘN in Hy; apply dom_merge in Hy as [Hy | Hy].
      + destruct (Hgr1 _ Hy) as [H | H]; [ left; exact H | right; apply p_union_iff; right; right; exact H ].
      + right; apply p_union_iff; right; apply dom_file in Hy as [-> | Hy]; [ left; reflexivity | right ].
        apply gds_dom_lookup in Hy; unfold R in Hy; rewrite gds_lookup_restrict in Hy.
        destruct (existsb (path_beq y) Dfp) eqn:Hb; [ apply existsb_path_beq, Hb | contradiction ].
  Qed.

  Lemma nil_ok {ch Θ K D Ξ} : post_cmds ch Θ K D Ξ nil (cst Θ K D Ξ).
  Proof.
    intros ΘR Hli; exists ΘR; split; [ constructor | split; [ exact Hli | split; [ apply ext_refl | apply grows_refl ] ] ].
  Qed.

  Lemma cons_pre {ch Θ K D Ξ c r} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> post_cmd ch Θ K D Ξ c r ->
    exists ΘR, linv ch (cs_deps r) (cs_k r) (cs_dom r) ΘR (cs_stack r).
  Proof. intros [ΘR Hli] Hp; destruct (Hp _ Hli) as (ΘR' & _ & Hli' & _); eauto. Qed.

  (** The imports of a later step include those of an earlier one. *)
  Lemma dom_grows {ch Θ1 K1 D1 ΘR1 Ξ1 Θ2 K2 D2 ΘR2 Ξ2 cs} :
    linv ch Θ1 K1 D1 ΘR1 Ξ1 -> run_cmds ch ΘR1 Ξ1 cs ΘR2 Ξ2 -> linv ch Θ2 K2 D2 ΘR2 Ξ2 -> incl D1 D2.
  Proof.
    intros Hli1 Hr Hli2 x Hx.
    destruct (proj1 (proj2 run_wf) _ _ _ _ _ _ Hr (li_wf _ _ _ _ _ _ Hli1) (li_canon _ _ _ _ _ _ Hli1) (li_stack _ _ _ _ _ _ Hli1)) as (_ & _ & Hs).
    apply (li_dom _ _ _ _ _ _ Hli2), (sub_dom _ _ _ Hs), (li_dom _ _ _ _ _ _ Hli1), Hx.
  Qed.

  Lemma cons_ok {ch Θ K D Ξ c cs r1 r2} :
    post_cmd ch Θ K D Ξ c r1 -> post_cmds ch (cs_deps r1) (cs_k r1) (cs_dom r1) (cs_stack r1) cs r2 ->
    post_cmds ch Θ K D Ξ (c :: cs) r2.
  Proof.
    intros H1 H2 ΘR Hli.
    destruct (H1 _ Hli) as (ΘR1 & Hr1 & Hli1 & He1 & Hg1).
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
    ginv (fp :: ch) Θ K -> post_cmds (fp :: ch) Θ K nil nil imps r1 ->
    ⊢ gds_restrict (cs_dom r1) (cs_deps r1) ⍮ nil ⍮ P ->
    exists ΘR, linv (fp :: ch) (cs_deps r1) (cs_k r1) (cs_dom r1) ΘR (gs_push (p_abs fp nil) P nil).
  Proof.
    intros G Hp HP; destruct (unit_imports G Hp) as (ΘR1 & _ & _ & Hli1 & _).
    exists ΘR1; exact (proj2 (linv_push_unit Hli1 HP)).
  Qed.

  Lemma unit_ok {fp ch Θ K imps P cs r1 r2 mp U Ξ2} :
    post_cmds (fp :: ch) Θ K nil nil imps r1 ->
    ⊢ gds_restrict (cs_dom r1) (cs_deps r1) ⍮ nil ⍮ P ->
    post_cmds (fp :: ch) (cs_deps r1) (cs_k r1) (cs_dom r1) (gs_push (p_abs fp nil) P nil) cs r2 ->
    cs_stack r2 = (mp, U) :: Ξ2 ->
    post_unit (fp :: ch) Θ K (imps, P, cs) (ust (cs_deps r2) (cs_k r2) (cs_dom r2) U).
  Proof.
    intros Hp1 HP Hp2 HΞ G; cbn [us_deps us_k us_dom us_unit].
    destruct (unit_imports G Hp1) as (ΘR1 & Hr1 & _ & Hli1 & He1 & Hg1).
    destruct (linv_push_unit Hli1 HP) as [HP' Hli1'].
    destruct (Hp2 _ Hli1') as (ΘR2 & Hr2 & Hli2 & He2 & Hg2).
    rewrite HΞ in Hr2, Hli2.
    destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ Hr2) as [F HF]; injection HF as <- ->.
    exists ΘR2; split; [ econstructor; eassumption |].
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

  Definition load_step (ch' ch : list fpath) : Prop :=
    exists fp s, ch' = fp :: ch /\ ~ In fp ch /\ load_path fp = Some s.

  Definition load_step_intro {ch fp src} (Hn : ~ In fp ch) (Hs : load_path fp = Some src) :
    load_step (fp :: ch) ch :=
    ex_intro _ fp (ex_intro _ src (conj eq_refl (conj Hn Hs))).

  (** How a unit loaded under chain [ch] is run.  Its log holds the evals of
      the unit itself, not of the units it loads. *)
  Definition loader (ch : list fpath) : Type :=
    forall fp src, ~ In fp ch -> load_path fp = Some src ->
      forall Θ K u, ginv (fp :: ch) Θ K -> rres ({r | post_unit (fp :: ch) Θ K u r} * elog)%type.

  Definition cmd_fun (ch : list fpath) : Type :=
    forall Θ K D Ξ c (H : exists ΘR, linv ch Θ K D ΘR Ξ), rres ({r | post_cmd ch Θ K D Ξ c r} * elog)%type.

  Equations cmds_step (ch : list fpath) (rc : cmd_fun ch) :
    forall Θ K D Ξ cs (H : exists ΘR, linv ch Θ K D ΘR Ξ), rres ({r | post_cmds ch Θ K D Ξ cs r} * elog)%type :=
  cmds_step ch rc := go
  where go Θ0 K0 D0 Ξ0 (cs : list ccmd) (H0 : exists ΘR, linv ch Θ0 K0 D0 ΘR Ξ0) :
    rres ({r | post_cmds ch Θ0 K0 D0 Ξ0 cs r} * elog)%type by struct cs :=
  | Θ0, K0, D0, Ξ0, nil, H0 => rok (exist _ _ nil_ok, log_nil)
  | Θ0, K0, D0, Ξ0, c :: cs', H0 with rc Θ0 K0 D0 Ξ0 c H0 => {
    | rerr e => rerr e
    | rok (exist _ r1 Hr1, l1) with go (cs_deps r1) (cs_k r1) (cs_dom r1) (cs_stack r1) cs' (cons_pre H0 Hr1) => {
      | rerr e => rerr e
      | rok (exist _ r2 Hr2, l2) => rok (exist _ _ (cons_ok Hr1 Hr2), log_app l1 l2) } }.

  #[derive(eliminator=no)]
  Equations run_cmd_impl (ch : list fpath) (L : loader ch) (Θ : gdeps) (K : kmap) (D : list fpath) (Ξ : gstack)
    (c : ccmd) (H : exists ΘR, linv ch Θ K D ΘR Ξ) : rres ({r | post_cmd ch Θ K D Ξ c r} * elog)%type by struct c :=
  | ch, L, Θ, K, D, Ξ, cc_def x b pv A M, H with gs_fresh_dec x Ξ => {
    | right _ => rerr (re_msg ("duplicate name " ++ x))
    | left Hfr with check_exp (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A M => {
      | left HM => rok (exist _ _ (def_ok Hfr HM), log_nil)
      | right _ => rerr (re_def x Ξ A M) } }
  | ch, L, Θ, K, D, Ξ, cc_mod x Δ cs, H with check_ctx (gds_restrict D Θ) Ξ (pre_gctx H) (Δ ++ gs_tele Ξ) => {
    | right _ => rerr (re_msg ("ill-formed parameters of module " ++ x))
    | left HΔ with gs_fresh_dec x Ξ => {
      | right _ => rerr (re_msg ("duplicate name " ++ x))
      | left Hfr with cmds_step ch (run_cmd_impl ch L) Θ K D (gs_push (path_in (gs_path Ξ) x) Δ Ξ) cs
                        (mod_pre H Hfr HΔ) => {
        | rerr e => rerr e
        | rok (exist _ r Hr, l) with list_case (cs_stack r) => {
          | inleft (existT _ (mp, U) (exist _ _ HΞ)) => rok (exist _ _ (mod_ok Hfr HΔ Hr HΞ), l)
          | inright _ => rerr (re_msg "internal error: a module body lost its frame") } } } }
  | ch, L, Θ, K, D, Ξ, cc_import fp ip, H with opt_case (gds_lookup Θ fp) => {
    | inleft (exist _ U HU) with in_dec path_eq_dec fp D => {
      | left Hin with gm_has_mod_dec ip (gu_mod U) => {
        | left Hm => rok (exist _ _ (import_in_ok Hin HU Hm), log_nil)
        | right _ => rerr (re_msg ("no module to import in " ++ path_str fp)) }
      | right Hnin with opt_case (kfind K fp) => {
        | inleft (exist _ Dfp HK) with gm_has_mod_dec ip (gu_mod U) => {
          | left Hm => rok (exist _ _ (import_hit_ok Hnin HU HK Hm), log_nil)
          | right _ => rerr (re_msg ("no module to import in " ++ path_str fp)) }
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
                | rok (exist _ r Hr, _) with gm_has_mod_dec ip (gu_mod (us_unit r)) => {
                  | left Hm => rok (exist _ _ (load_ok Hn Hnch Hsrc Hprg Hp Hu Hr Hm), log_nil)
                  | right _ => rerr (re_msg ("no module to import in " ++ path_str fp)) } } } } } } } }
  | ch, L, Θ, K, D, Ξ, cc_eval M (Some A), H
      with check_exp (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A M => {
    | left HM => rok (exist _ _ (eval_check_ok HM), eval_log _ _ (pre_gctx H) M A HM)
    | right _ => rerr (re_eval_check Ξ M A) }
  | ch, L, Θ, K, D, Ξ, cc_eval M None, H
      with @type_infer_at (gc_mk (gds_restrict D Θ) Ξ) (gs_tele Ξ) (pre_ctx H) M (user_exp_all M) => {
    | inleft (exist _ A HA) => rok (exist _ _ (eval_infer_ok A HA), eval_log _ _ (pre_gctx H) M A HA)
    | inright _ => rerr (re_eval_infer Ξ M) }.

  Definition run_cmds_impl (ch : list fpath) (L : loader ch) := cmds_step ch (run_cmd_impl ch L).

  Definition run_unit_step (ch : list fpath) (L : loader ch) (Θ : gdeps) (K : kmap) (u : cunit)
    (H : ginv ch Θ K) : rres ({r | post_unit ch Θ K u r} * elog)%type :=
    match ch as ch0 return loader ch0 -> ginv ch0 Θ K -> rres ({r | post_unit ch0 Θ K u r} * elog)%type with
    | nil => fun _ _ => rerr (re_msg "internal error: no unit to run")
    | fp :: ch0 => fun L H =>
    match u as u0 return rres ({r | post_unit (fp :: ch0) Θ K u0 r} * elog)%type with
    | (imps, P, cs) =>
        match run_cmds_impl (fp :: ch0) L Θ K nil nil imps (unit_pre H) with
        | rerr e => rerr e
        | rok (exist _ r1 Hr1, l1) =>
            match check_ctx (gds_restrict (cs_dom r1) (cs_deps r1)) nil (unit_gctx H Hr1) P with
            | right _ => rerr (re_msg "ill-formed unit parameters")
            | left HP =>
                match run_cmds_impl (fp :: ch0) L (cs_deps r1) (cs_k r1) (cs_dom r1) (gs_push (p_abs fp nil) P nil) cs
                        (unit_body_pre H Hr1 HP) with
                | rerr e => rerr e
                | rok (exist _ r2 Hr2, l2) =>
                    match list_case (cs_stack r2) with
                    | inleft (existT _ (mp, U) (exist _ _ HΞ)) => rok (exist _ _ (unit_ok Hr1 HP Hr2 HΞ), log_app l1 l2)
                    | inright _ => rerr (re_msg "internal error: a unit body lost its frame")
                    end
                end
            end
        end
    end
    end L H.

  #[derive(eliminator=no)]
  Equations run_unit_impl (ch : list fpath) (Hacc : Acc load_step ch) :
    forall Θ K u, ginv ch Θ K -> rres ({r | post_unit ch Θ K u r} * elog)%type by struct Hacc :=
  run_unit_impl ch Hacc :=
    run_unit_step ch (fun fp src Hn Hs => run_unit_impl (fp :: ch) (Acc_inv Hacc (load_step_intro Hn Hs))).

  Definition loader_of (ch : list fpath) (Hacc : Acc load_step ch) : loader ch :=
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

  Lemma top_equiv : forall ΘU Θ, canon ΘU -> canon Θ -> ΘU ⊑ Θ -> Θ ⊑ ΘU -> gds_equiv ΘU Θ.
  Proof.
    intros * HcU Hc H1 H2; split; [ exact H1 | split; [ exact H2 |] ]; intros y.
    destruct (gds_lookup ΘU y) as [V |] eqn:E.
    - exact (proj2 (canon_agree _ _ _ _ _ HcU Hc _ _ _ E (H1 _ _ E))).
    - rewrite (proj2 (gds_level_none _ _) E), (proj2 (gds_level_none _ _) (sub_none _ _ _ H2 E)); reflexivity.
  Qed.

  Lemma unit_equiv {ch Θ K u r} :
    ginv ch Θ K -> post_unit ch Θ K u r ->
    exists ΘU, run_unit ch u ΘU (us_unit r) /\ ginv ch (us_deps r) (us_k r) /\
      gds_equiv ΘU (gds_restrict (us_dom r) (us_deps r)) /\ grows Θ (us_deps r) (us_dom r) /\
      ΘU ⊑ us_deps r /\ set_eq (us_dom r) (gds_dom ΘU).
  Proof.
    intros G Hp; destruct (Hp G) as (ΘU & Hu & G' & Hsub & Hdom & _ & _ & Hgr).
    destruct (proj2 (proj2 run_wf) _ _ _ _ Hu) as (_ & HcU & _).
    exists ΘU; split; [ exact Hu | split; [ exact G' |] ].
    split; [ exact (equiv_restrict _ _ _ _ _ _ HcU (ginv_canon G') Hsub Hdom) |].
    split; [ exact Hgr | split; assumption ].
  Qed.

  Theorem run_cmd_impl_sound : forall ch L Θ K D Ξ c H r ΘR,
      linv ch Θ K D ΘR Ξ -> run_cmd_impl ch L Θ K D Ξ c H = rok r ->
      exists ΘR', run_cmd ch ΘR Ξ c ΘR' (cs_stack (proj1_sig (fst r))) /\
        linv ch (cs_deps (proj1_sig (fst r))) (cs_k (proj1_sig (fst r))) (cs_dom (proj1_sig (fst r))) ΘR'
          (cs_stack (proj1_sig (fst r))) /\ logs_ok (proj1_sig (snd r)).
  Proof.
    intros * Hli _; destruct r as [[r Hr] [l Hl]]; destruct (Hr _ Hli) as (ΘR' & ? & ? & _); cbn; eauto.
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
      executable loads only where the derivation does ([rc_import_load]), and
      under the same chain.  For a unit filed already, the derivation loads it,
      but the executable shares it without recursing. *)

  Theorem run_impl_complete :
    (forall ch ΘR Ξ c ΘR' Ξ', run_cmd ch ΘR Ξ c ΘR' Ξ' ->
       forall Hacc Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ), linv ch Θ K D ΘR Ξ ->
         exists r, run_cmd_impl ch (loader_of ch Hacc) Θ K D Ξ c H = rok r) /\
    (forall ch ΘR Ξ cs ΘR' Ξ', run_cmds ch ΘR Ξ cs ΘR' Ξ' ->
       forall Hacc Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ), linv ch Θ K D ΘR Ξ ->
         exists r, run_cmds_impl ch (loader_of ch Hacc) Θ K D Ξ cs H = rok r) /\
    (forall ch u ΘU U, run_unit ch u ΘU U ->
       forall Hacc Θ K (H : ginv ch Θ K), exists r, run_unit_impl ch Hacc Θ K u H = rok r).
  Proof.
    apply run_mut_dind.
    - (* a definition *)
      intros ch ΘR Ξ x b pv A M HM Hfr Hacc Θ K D H Hli; simp run_cmd_impl.
      destruct (gs_fresh_dec x Ξ) as [Hfr' | Hfr']; [| contradiction ]; simp run_cmd_impl.
      match goal with |- context [check_exp ?a ?b ?c ?d ?e ?f] => destruct (check_exp a b c d e f) as [HM' | HM'] end;
        simp run_cmd_impl; [ eexists; reflexivity |].
      exfalso; apply HM'; exact (equiv_exp _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HM).
    - (* a module *)
      intros ch ΘR Ξ x Δ cs ΘR' mp U HΔ Hfr Hr IH Hacc Θ K D H Hli; simp run_cmd_impl.
      match goal with |- context [check_ctx ?a ?b ?c ?d] => destruct (check_ctx a b c d) as [HΔ' | HΔ'] end;
        [| exfalso; apply HΔ'; exact (equiv_ctx _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HΔ) ].
      simp run_cmd_impl.
      destruct (gs_fresh_dec x Ξ) as [Hfr' | Hfr']; [| contradiction ]; simp run_cmd_impl.
      destruct (linv_push Hli Hfr' HΔ') as [_ Hli'].
      destruct (IH Hacc Θ K D (mod_pre H Hfr' HΔ') Hli') as [[[r Hp] l] E]; unfold run_cmds_impl in E; rewrite E.
      simp run_cmd_impl.
      destruct (Hp _ Hli') as (ΘR2 & Hr2 & _); destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ Hr2) as [F HF].
      destruct (list_case (cs_stack r)) as [[[mp' U'] [Ξ2 HΞ]] | HΞ]; simp run_cmd_impl; [ eexists; reflexivity | congruence ].
    - (* an import of a unit the judgment has *)
      intros ch ΘR Ξ fp ip U HU Hm Hacc Θ K D H Hli; simp run_cmd_impl.
      pose proof (li_sub _ _ _ _ _ _ Hli _ _ HU) as HUg.
      assert (Hin : In fp D) by (apply (li_dom _ _ _ _ _ _ Hli), gds_dom_lookup; rewrite HU; discriminate).
      destruct (opt_case (gds_lookup Θ fp)) as [[U' HU'] | HU']; [| congruence ].
      assert (U' = U) as -> by congruence; simp run_cmd_impl.
      destruct (in_dec path_eq_dec fp D) as [Hin' | Hin']; [| contradiction ]; simp run_cmd_impl.
      destruct (gm_has_mod_dec ip (gu_mod U)) as [Hm' | Hm']; simp run_cmd_impl; [ eexists; reflexivity | contradiction ].
    - (* a load: shared if some other unit filed it, run otherwise *)
      intros ch ΘR Ξ fp ip src prg u ΘU U Hn Hnin Hl Hrd Hp Ht Hu IH Hm Hacc Θ K D H Hli; simp run_cmd_impl.
      assert (HnD : ~ In fp D)
        by (intros Hin; apply (li_dom _ _ _ _ _ _ Hli), gds_dom_lookup in Hin; contradiction).
      destruct (opt_case (gds_lookup Θ fp)) as [[U' HU'] | Hng]; simp run_cmd_impl.
      + destruct (in_dec path_eq_dec fp D) as [Hin | Hin]; [ contradiction |]; simp run_cmd_impl.
        destruct (gi_entry _ _ _ (li_g _ _ _ _ _ _ Hli) _ _ HU')
          as (Dfp & HK & _ & src' & prg' & u' & ch0 & ΘU' & Hl' & Hr' & _ & Ht' & Hu' & _).
        rewrite Hl in Hl'; injection Hl' as <-; rewrite Hrd in Hr'; injection Hr' as <-.
        rewrite Ht in Ht'; injection Ht' as <-.
        destruct (proj2 (proj2 run_functional) _ _ _ _ Hu (fp :: ch0) _ _ eq_refl Hu') as [_ <-].
        destruct (opt_case (kfind K fp)) as [[Dfp' HK'] | HK']; [| congruence ]; simp run_cmd_impl.
        destruct (gm_has_mod_dec ip (gu_mod U)) as [Hm' | Hm']; simp run_cmd_impl; [ eexists; reflexivity | contradiction ].
      + destruct (in_dec path_eq_dec fp ch) as [Hin | Hin]; [ contradiction |]; simp run_cmd_impl.
        destruct (opt_case (load_path fp)) as [[src' Hl'] | Hl']; [| congruence ].
        assert (src' = src) as -> by congruence; simp run_cmd_impl.
        destruct (opt_case (read src)) as [[prg' Hr'] | Hr']; [| congruence ].
        assert (prg' = prg) as -> by congruence; simp run_cmd_impl.
        destruct (path_eq_dec (prog_path prg) fp) as [Hp' | Hp']; [| contradiction ]; simp run_cmd_impl.
        destruct (opt_case (to_core prg)) as [[u' Ht'] | Ht']; [| congruence ].
        assert (u' = u) as -> by congruence; simp run_cmd_impl.
        unfold loader_of.
        match goal with |- context [run_unit_impl (fp :: ch) ?a Θ K u ?b] =>
          destruct (IH a Θ K b) as [[[r Hpost] l] E]; rewrite E; simp run_cmd_impl;
          destruct (Hpost b) as (ΘU' & Hu' & _)
        end.
        destruct (proj2 (proj2 run_functional) _ _ _ _ Hu (fp :: ch) _ _ eq_refl Hu') as [_ HU].
        destruct (gm_has_mod_dec ip (gu_mod (us_unit r))) as [Hm' | Hm']; simp run_cmd_impl;
          [ eexists; reflexivity | rewrite <- HU in Hm'; contradiction ].
    - (* an ascribed eval *)
      intros ch ΘR Ξ M A HM Hacc Θ K D H Hli; simp run_cmd_impl.
      match goal with |- context [check_exp ?a ?b ?c ?d ?e ?f] => destruct (check_exp a b c d e f) as [HM' | HM'] end;
        simp run_cmd_impl; [ eexists; reflexivity |].
      exfalso; apply HM'; exact (equiv_exp _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HM).
    - (* an inferred eval: failure of inference contradicts its completeness *)
      intros ch ΘR Ξ M A HM Hacc Θ K D H Hli; simp run_cmd_impl.
      match goal with |- context [@type_infer_at ?g ?G ?a ?b ?c] => destruct (@type_infer_at g G a b c) as [[A' HA'] | Hno] end;
        simp run_cmd_impl; [ eexists; reflexivity | exfalso ].
      pose proof (equiv_exp _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HM) as HM'.
      destruct (@alg_type_infer_complete (gc_mk (gds_restrict D Θ) Ξ) (gs_tele Ξ) A M (user_exp_all M) HM') as (B & HB & _).
      exact (Hno B HB).
    - intros ch ΘR Ξ Hacc Θ K D H Hli; unfold run_cmds_impl; simp cmds_step; eexists; reflexivity.
    - (* a sequence: the head's result is the judgment's, by determinism *)
      intros ch ΘR Ξ c cs ΘR1 Ξ1 ΘR2 Ξ2 Hc IHc Hcs IHcs Hacc Θ K D H Hli; unfold run_cmds_impl; simp cmds_step.
      destruct (IHc Hacc Θ K D H Hli) as [[[r1 Hp1] l1] E1]; rewrite E1; simp cmds_step.
      destruct (Hp1 _ Hli) as (ΘR1' & Hr1 & Hli1 & _).
      destruct (proj1 run_functional _ _ _ _ _ _ Hc _ _ _ Hr1) as [<- HΞ1]; subst Ξ1.
      destruct (IHcs Hacc _ _ _ (cons_pre H Hp1) Hli1) as [[[r2 Hp2] l2] E2]; unfold run_cmds_impl in E2; simp cmds_step in E2; rewrite E2.
      simp cmds_step; eexists; reflexivity.
    - (* a unit *)
      intros fp ch imps P cs ΘR1 ΘR2 mp U Hi IHi HP Hb IHb Hacc Θ K H.
      rewrite run_unit_impl_unfold; cbn [run_unit_step].
      destruct (IHi Hacc Θ K nil (unit_pre H) (nil_linv H)) as [[[r1 Hp1] l1] E1]; rewrite E1; cbv beta iota.
      destruct (Hp1 _ (nil_linv H)) as (ΘR1' & Hr1 & Hli1 & _).
      destruct (proj1 (proj2 run_functional) _ _ _ _ _ _ Hi _ _ _ Hr1) as [<- HΞ]; rewrite <- HΞ in Hli1.
      match goal with |- context [check_ctx ?a ?b ?c ?d] => destruct (check_ctx a b c d) as [HP' | HP'] end;
        [| exfalso; apply HP'; exact (equiv_ctx _ _ _ _ (linv_equiv Hli1) (linv_restrict_gctx Hli1) HP) ].
      destruct (linv_push_unit Hli1 HP') as [_ Hli1'].
      destruct (IHb Hacc _ _ _ (unit_body_pre H Hp1 HP') Hli1') as [[[r2 Hp2] l2] E2]; rewrite E2; cbv beta iota.
      destruct (Hp2 _ Hli1') as (ΘR2' & Hr2 & _); destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ Hr2) as [F HF].
      destruct (list_case (cs_stack r2)) as [[[mp' U'] [Ξ2 HΞ2]] | HΞ2]; [ eexists; reflexivity | congruence ].
  Qed.

  (** The result is the judgment's, by determinism. *)
  Corollary run_cmd_impl_complete : forall ch ΘR Ξ c ΘR' Ξ' Hacc Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ),
      linv ch Θ K D ΘR Ξ -> run_cmd ch ΘR Ξ c ΘR' Ξ' ->
      exists r, run_cmd_impl ch (loader_of ch Hacc) Θ K D Ξ c H = rok r /\ cs_stack (proj1_sig (fst r)) = Ξ' /\
        linv ch (cs_deps (proj1_sig (fst r))) (cs_k (proj1_sig (fst r))) (cs_dom (proj1_sig (fst r))) ΘR' Ξ'.
  Proof.
    intros * Hli Hr; destruct (proj1 run_impl_complete _ _ _ _ _ _ Hr Hacc _ _ _ H Hli) as [r E].
    exists r; split; [ exact E |].
    destruct r as [[r Hp] l]; destruct (Hp _ Hli) as (ΘR'' & Hr' & Hli' & _); cbn [proj1_sig fst].
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
    destruct (proj2 (proj2 run_wf) _ _ _ _ Hu) as (_ & HcU & _).
    exists ΘU; split; [ exists u; split; assumption |].
    apply top_equiv; [ exact HcU | exact (ginv_canon G) | exact Hsub |].
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
  Variable load_path : fpath -> option string.
  Variable all_files : list fpath.
  Hypothesis Hfiles : forall fp, (exists s, load_path fp = Some s) <-> In fp all_files.

  Definition unloaded (ch : list fpath) : nat :=
    List.length (filter (fun fp => if in_dec path_eq_dec fp ch then false else true) all_files).

  Lemma filter_mono : forall (p1 p2 : fpath -> bool) l, (forall y, p1 y = true -> p2 y = true) ->
      List.length (filter p1 l) <= List.length (filter p2 l).
  Proof.
    intros * Hpq; induction l as [| y l IH]; cbn; [ lia |].
    destruct (p1 y) eqn:Ep; [ rewrite (Hpq _ Ep); cbn; lia | destruct (p2 y); cbn; lia ].
  Qed.

  Lemma filter_strict : forall (p1 p2 : fpath -> bool) l x, (forall y, p1 y = true -> p2 y = true) ->
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
