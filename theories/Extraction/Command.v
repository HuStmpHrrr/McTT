(** * Running Commands

    The executable for [Core.Syntactic.System.Command].  It is sound by
    construction, since every result carries the judgment it computed, and
    complete by [run_impl_complete].

    It follows the judgment step by step, with one difference: a unit is
    run once.  What its run filed is kept in a cache, and a later load of it
    from another unit merges the cached result instead of running the unit
    again.  The result of a run does not depend on the chain it ran under
    ([run_chain_irrel]), provided no unit of that chain is among what it
    filed, which the executable checks; the judgment's run under the new
    chain is then the cached one ([run_functional]).

    A run also logs each [eval] it checked, with its normal form
    ([eval_entry], certified by [eval_ok]), and fails with a [run_error]
    carrying the terms involved. *)

From Stdlib Require Import List String Wellfounded Wf_nat.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base Soundness.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import Structural MemberWf Command.
From Mctt.Extraction Require Import NbE TypeCheck GlobalCheck MemberType Privacy.
Import Syntax_Notations GlobalCtx_Notations.

Local Open Scope string_scope.

(** ** Deciders *)

Definition opt_case {A} (o : option A) : {a | o = Some a} + {o = None} :=
  match o as o0 return {a | o0 = Some a} + {o0 = None} with
  | Some a => inleft (exist _ a eq_refl)
  | None => inright eq_refl
  end.

Definition lead_items_dec (its : list iitem) : {lead_items_ok its} + {~ lead_items_ok its}.
Proof.
  unfold lead_items_ok; induction its as [| it its IH]; [ left; constructor |].
  destruct (Bool.bool_dec (snd it) true) as [Ht | Ht].
  - destruct IH as [IH | IH]; [ left; constructor; assumption | right; intros Hf; inversion Hf; contradiction ].
  - right; intros Hf; inversion Hf; contradiction.
Defined.

(** Whether no unit of a chain is filed. *)
Definition chain_free (ch : list path) (Θ : gctx) :
  {x : path | In x ch /\ gc_unit Θ x <> None} + {forall x, In x ch -> gc_unit Θ x = None}.
Proof.
  induction ch as [| y ch IH]; [ right; intros ? [] |].
  destruct (opt_case (gc_unit Θ y)) as [[U HU] | HU].
  - left; exists y; split; [ left; reflexivity | congruence ].
  - destruct IH as [[x [Hx Hn]] | IH]; [ left; exists x; split; [ right; exact Hx | exact Hn ] |].
    right; intros x [<- | Hx]; auto.
Defined.

Definition path_str (fp : path) : string := String.concat "::" fp.

(** The chain up to the unit imported again, where the cycle starts. *)
Equations chain_to (fp : path) (ch : list path) : list path by struct ch :=
| _, nil => nil
| fp, fq :: ch' => if path_beq fp fq then fq :: nil else fq :: chain_to fp ch'.

(** The cycle, from the unit imported again back to itself. *)
Definition cycle_chain (fp : path) (ch : list path) : list path :=
  List.app (rev (chain_to fp ch)) (fp :: nil).

(** ** Results

    The errors a run can fail with, carrying the terms involved, if any, for
    the driver to print, each with the context it was checked in.  The
    message of [re_unit] concerns the unit at the path it carries and does
    not repeat that path. *)

Inductive run_error : Set :=
| re_msg : string -> run_error
| re_def : string -> ctx -> typ -> exp -> run_error
| re_eval_check : ctx -> exp -> typ -> run_error
| re_eval_infer : ctx -> exp -> run_error
| re_cycle : list path -> run_error
| re_unit : path -> string -> run_error
(** A private member, named by its module, reached from outside it. *)
| re_private : qname -> string -> run_error
(** A private entry of a local body, by the chain of submodules from the
    local module, reached from outside it. *)
| re_private_local : list string -> string -> run_error
(** An open that generates nothing ([Imports]), in the context it is
    checked in. *)
| re_import : ctx -> xerr -> run_error.

Definition priv_error (e : priv_err) : run_error :=
  match e with
  | pe_global qd x => re_private qd x
  | pe_local ch x => re_private_local ch x
  end.

Inductive rres (A : Type) : Type :=
| rok : A -> rres A
| rerr : run_error -> rres A.

Arguments rok {A}.
Arguments rerr {A}.

(** A checked and normalized [eval]: in the global context [ev_gctx] and the
    context [ev_ctx] of the enclosing frames, the expression [ev_exp] has
    type [ev_typ] (ascribed or inferred) and normalizes to [ev_nf]. *)
Record eval_entry : Set :=
  { ev_gctx : gctx; ev_ctx : ctx; ev_exp : exp; ev_typ : typ; ev_nf : nf }.

Definition eval_ok (e : eval_entry) : Prop :=
  ⊢ ev_gctx e ⍮ ev_ctx e /\ ev_gctx e ⍮ ev_ctx e ⊢ ev_exp e : ev_typ e /\
    nbe (ev_gctx e) (ev_ctx e) (ev_exp e) (ev_typ e) (ev_nf e).

Definition logs_ok (l : list eval_entry) : Prop := forall e, In e l -> eval_ok e.

(** The log of a run, in program order, with every entry certified. *)
Definition elog : Set := {l | logs_ok l}.

Definition log_nil : elog := exist logs_ok nil (fun e (H : In e nil) => False_ind _ H).

Definition log_app (l1 l2 : elog) : elog.
Proof.
  refine (exist _ (List.app (proj1_sig l1) (proj1_sig l2)) _).
  abstract (intros e He; apply in_app_or in He as [He | He]; [ exact (proj2_sig l1 _ He) | exact (proj2_sig l2 _ He) ]).
Defined.

Lemma typed_nbe_order {Θ Γ M A} : Θ ⍮ Γ ⊢ M : A -> nbe_order Θ Γ M A.
Proof. intros H; destruct (soundness_gctx _ _ _ _ H) as (W & HW & _); exact (nbe_order_sound _ _ _ _ _ HW). Qed.

Lemma eval_log_ok {Θ Γ M A W} : ⊢ Θ ⍮ Γ -> Θ ⍮ Γ ⊢ M : A -> nbe Θ Γ M A W ->
  logs_ok ({| ev_gctx := Θ; ev_ctx := Γ; ev_exp := M; ev_typ := A; ev_nf := W |} :: nil).
Proof. intros HΓ HM HW e [<- | []]; unfold eval_ok; cbn; auto. Qed.

(** Normalize a checked [eval] into its entry. *)
Definition eval_log (Θ : gctx) (Γ : ctx) (HΓ : ⊢ Θ ⍮ Γ) (M : exp) (A : typ) (HM : Θ ⍮ Γ ⊢ M : A) : elog :=
  match nbe_impl Θ Γ M A (typed_nbe_order HM) with
  | exist _ W HW => exist _ _ (eval_log_ok HΓ HM HW)
  end.

(** ** The Chain of a Run

    A run's chain only rules runs out.  A run files no unit of its chain,
    beyond those it starts from, and it runs as well under any chain none
    of whose units it ends up with. *)

Lemma gc_unit_merge_none : forall Θ ΘL x,
    gc_unit (gc_merge Θ ΘL) x = None <-> gc_unit Θ x = None /\ gc_unit ΘL x = None.
Proof. intros; rewrite gc_unit_merge; destruct (gc_unit Θ x); split; intuition congruence. Qed.

Lemma gens_run_tail : forall Θ Γimp F gs F', gens_run Θ Γimp F gs F' ->
    forall f F0, F = f :: F0 -> exists f', F' = f' :: F0.
Proof. induction 1; intros f0 F0 Ef; [ subst; eauto | injection Ef as <- <-; eauto .. ]. Qed.

Lemma gens_run_grows : forall Θ Γimp F gs F', gens_run Θ Γimp F gs F' ->
    forall f F0, F = f :: F0 -> exists f', F' = f' :: F0 /\ fr_grows f f'.
Proof.
  induction 1 as [| f F d pv A M gs F' _ _ _ IH | f F d pv E gs F' _ _ _ IH]; intros f0 F0 Ef.
  - subst; eexists; split; [ reflexivity | apply fr_grows_refl ].
  - injection Ef as <- <-; destruct (IH _ _ eq_refl) as (f' & -> & Hg).
    eexists; split; [ reflexivity | eapply fr_grows_trans; [ apply fr_grows_add | exact Hg ] ].
  - injection Ef as <- <-; destruct (IH _ _ eq_refl) as (f' & -> & Hg).
    eexists; split; [ reflexivity | eapply fr_grows_trans; [ apply fr_grows_add | exact Hg ] ].
Qed.

Section Chains.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  #[local] Abbreviation run_cmd := (run_cmd load_path read to_core).
  #[local] Abbreviation run_cmds := (run_cmds load_path read to_core).
  #[local] Abbreviation run_load := (run_load load_path read to_core).
  #[local] Abbreviation run_lead := (run_lead load_path read to_core).
  #[local] Abbreviation run_leads := (run_leads load_path read to_core).
  #[local] Abbreviation run_unit := (run_unit load_path read to_core).

  (** Commands change the innermost frame only. *)
  Lemma run_tail :
    (forall ch fp Γimp Θ F c Θ' F', run_cmd ch fp Γimp Θ F c Θ' F' ->
       forall f F0, F = f :: F0 -> exists f', F' = f' :: F0) /\
    (forall ch fp Γimp Θ F cs Θ' F', run_cmds ch fp Γimp Θ F cs Θ' F' ->
       forall f F0, F = f :: F0 -> exists f', F' = f' :: F0) /\
    (forall ch Θ fq Θ', run_load ch Θ fq Θ' -> True) /\
    (forall ch Θ Γ c Θ' Γ', run_lead ch Θ Γ c Θ' Γ' -> True) /\
    (forall ch Θ Γ cs Θ' Γ', run_leads ch Θ Γ cs Θ' Γ' -> True) /\
    (forall ch Θ0 u Θ U, run_unit ch Θ0 u Θ U -> True).
  Proof.
    apply run_mut_ind; intros; try exact I;
      try solve [ match goal with E : _ :: _ = _ :: _ |- _ => injection E; intros; subst end; eexists; reflexivity
                | subst; eexists; reflexivity ].
    - match goal with E : _ :: _ = _ :: _ |- _ => injection E; intros; subst end.
      match goal with Hg : gens_run _ _ _ _ _ |- _ => exact (gens_run_tail _ _ _ _ _ Hg _ _ eq_refl) end.
    - match goal with IH1 : forall f F0, ?F = f :: F0 -> exists f', ?F1 = _, E : ?F = _ :: _ |- _ =>
        destruct (IH1 _ _ E) as [f1 E1] end.
      match goal with IH2 : forall f F0, ?F1 = f :: F0 -> _, E1 : ?F1 = _ :: _ |- _ => exact (IH2 _ _ E1) end.
  Qed.

  (** A command adds entries to the innermost frame's body, and changes
      nothing else of the frames. *)
  Lemma run_cmd_grows : forall ch fp Γimp Θ F c Θ' F', run_cmd ch fp Γimp Θ F c Θ' F' ->
      forall f F0, F = f :: F0 -> exists f', F' = f' :: F0 /\ fr_grows f f'.
  Proof.
    intros * Hr; destruct Hr; intros f0 F0 Ef;
      try (injection Ef as <- <-; eexists; split; [ reflexivity | apply fr_grows_add ]);
      try (subst; eexists; split; [ reflexivity | apply fr_grows_refl ]).
    injection Ef as <- <-; eapply gens_run_grows; [ eassumption | reflexivity ].
  Qed.

  Lemma run_unit_mono :
    (forall ch fp Γimp Θ F c Θ' F', run_cmd ch fp Γimp Θ F c Θ' F' ->
       forall x, gc_unit Θ' x = None -> gc_unit Θ x = None) /\
    (forall ch fp Γimp Θ F cs Θ' F', run_cmds ch fp Γimp Θ F cs Θ' F' ->
       forall x, gc_unit Θ' x = None -> gc_unit Θ x = None) /\
    (forall ch Θ fq Θ', run_load ch Θ fq Θ' -> forall x, gc_unit Θ' x = None -> gc_unit Θ x = None) /\
    (forall ch Θ Γ c Θ' Γ', run_lead ch Θ Γ c Θ' Γ' -> forall x, gc_unit Θ' x = None -> gc_unit Θ x = None) /\
    (forall ch Θ Γ cs Θ' Γ', run_leads ch Θ Γ cs Θ' Γ' -> forall x, gc_unit Θ' x = None -> gc_unit Θ x = None) /\
    (forall ch Θ0 u Θ U, run_unit ch Θ0 u Θ U -> forall x, gc_unit Θ x = None -> gc_unit Θ0 x = None).
  Proof.
    apply run_mut_ind; intros; cbn [gc_unit] in *; eauto.
    match goal with H : gc_unit (gc_merge _ _) _ = None |- _ => apply gc_unit_merge_none in H; tauto end.
  Qed.

  Lemma run_chain_fresh :
    (forall ch fp Γimp Θ F c Θ' F', run_cmd ch fp Γimp Θ F c Θ' F' ->
       forall x, In x ch -> gc_unit Θ x = None -> gc_unit Θ' x = None) /\
    (forall ch fp Γimp Θ F cs Θ' F', run_cmds ch fp Γimp Θ F cs Θ' F' ->
       forall x, In x ch -> gc_unit Θ x = None -> gc_unit Θ' x = None) /\
    (forall ch Θ fq Θ', run_load ch Θ fq Θ' -> forall x, In x ch -> gc_unit Θ x = None -> gc_unit Θ' x = None) /\
    (forall ch Θ Γ c Θ' Γ', run_lead ch Θ Γ c Θ' Γ' ->
       forall x, In x ch -> gc_unit Θ x = None -> gc_unit Θ' x = None) /\
    (forall ch Θ Γ cs Θ' Γ', run_leads ch Θ Γ cs Θ' Γ' ->
       forall x, In x ch -> gc_unit Θ x = None -> gc_unit Θ' x = None) /\
    (forall ch Θ0 u Θ U, run_unit ch Θ0 u Θ U -> forall x, In x ch -> gc_unit Θ0 x = None -> gc_unit Θ x = None).
  Proof.
    apply run_mut_ind; intros; cbn [gc_unit] in *; eauto.
    (* a unit loaded *)
    apply gc_unit_merge_none; split; [ assumption |]; cbn.
    destruct (path_beq x fq) eqn:E; [ apply path_beq_true in E; subst; contradiction |].
    match goal with IH : forall x, In x (fq :: ch) -> _ -> _ |- _ => apply IH; [ right; assumption | reflexivity ] end.
  Qed.

  Lemma run_chain_irrel :
    (forall ch fp Γimp Θ F c Θ' F', run_cmd ch fp Γimp Θ F c Θ' F' ->
       forall ch', (forall x, In x ch' -> gc_unit Θ' x = None) -> run_cmd ch' fp Γimp Θ F c Θ' F') /\
    (forall ch fp Γimp Θ F cs Θ' F', run_cmds ch fp Γimp Θ F cs Θ' F' ->
       forall ch', (forall x, In x ch' -> gc_unit Θ' x = None) -> run_cmds ch' fp Γimp Θ F cs Θ' F') /\
    (forall ch Θ fq Θ', run_load ch Θ fq Θ' ->
       forall ch', (forall x, In x ch' -> gc_unit Θ' x = None) -> run_load ch' Θ fq Θ') /\
    (forall ch Θ Γ c Θ' Γ', run_lead ch Θ Γ c Θ' Γ' ->
       forall ch', (forall x, In x ch' -> gc_unit Θ' x = None) -> run_lead ch' Θ Γ c Θ' Γ') /\
    (forall ch Θ Γ cs Θ' Γ', run_leads ch Θ Γ cs Θ' Γ' ->
       forall ch', (forall x, In x ch' -> gc_unit Θ' x = None) -> run_leads ch' Θ Γ cs Θ' Γ') /\
    (forall ch Θ0 u Θ U, run_unit ch Θ0 u Θ U ->
       forall ch', hd_error ch' = hd_error ch -> (forall x, In x ch' -> gc_unit Θ x = None) -> run_unit ch' Θ0 u Θ U).
  Proof.
    apply run_mut_ind; intros; try solve [ econstructor; eassumption ];
      try solve [ econstructor; try eassumption;
                  match goal with IH : forall ch', (forall x, In x ch' -> _) -> _ |- _ => apply IH; assumption end ].
    - (* a sequence *)
      econstructor; try eassumption; [| eauto ].
      match goal with IH : forall ch', _ -> run_cmd ch' _ _ _ _ _ _ _ |- _ => apply IH end.
      intros; eapply (proj1 (proj2 run_unit_mono)); eauto.
    - (* a unit loaded *)
      match goal with H : forall x, In x ch' -> _ |- _ => rename H into Hch end.
      eapply rl_run; try eassumption.
      + intros Hin; specialize (Hch _ Hin); rewrite gc_unit_merge in Hch.
        match goal with Hn : gc_unit Θ fq = None |- _ => rewrite Hn in Hch end; cbn in Hch.
        rewrite path_beq_refl in Hch; discriminate.
      + match goal with IH : forall ch', hd_error ch' = hd_error (fq :: ch) -> _ |- _ => apply IH; [ reflexivity |] end.
        intros x [<- | Hx]; [ assumption |].
        specialize (Hch _ Hx); apply gc_unit_merge_none in Hch as [_ Hch]; cbn in Hch.
        destruct (path_beq x fq); [ discriminate | exact Hch ].
    - (* a sequence of leading commands *)
      econstructor; try eassumption; [| eauto ].
      match goal with IH : forall ch', _ -> run_lead ch' _ _ _ _ _ |- _ => apply IH end.
      intros; eapply (proj1 (proj2 (proj2 (proj2 (proj2 run_unit_mono))))); eauto.
    - (* a unit *)
      match goal with H : hd_error _ = _ |- _ => rename H into Hhd end.
      match goal with H : forall x, In x ch' -> _ |- _ => rename H into Hch end.
      destruct ch' as [| fp' ch0]; cbn in Hhd; [ discriminate |]; injection Hhd as ->.
      econstructor; try eassumption; [| eauto ].
      match goal with IH : forall ch', _ -> run_leads ch' _ _ _ _ _ |- _ => apply IH end.
      intros; eapply (proj1 (proj2 run_unit_mono)); eauto.
  Qed.
End Chains.

(** ** The Cache *)

Definition cache : Set := list (path * (gctx * gunit)).

Fixpoint cfind (C : cache) (fp : path) : option (gctx * gunit) :=
  match C with
  | nil => None
  | (fq, r) :: C' => if path_beq fp fq then Some r else cfind C' fp
  end.

Section Impl.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  #[local] Abbreviation run_cmd := (run_cmd load_path read to_core).
  #[local] Abbreviation run_cmds := (run_cmds load_path read to_core).
  #[local] Abbreviation run_load := (run_load load_path read to_core).
  #[local] Abbreviation run_lead := (run_lead load_path read to_core).
  #[local] Abbreviation run_leads := (run_leads load_path read to_core).
  #[local] Abbreviation run_unit := (run_unit load_path read to_core).
  #[local] Abbreviation run_wf := (run_wf load_path read to_core).
  #[local] Abbreviation run_functional := (run_functional load_path read to_core).
  #[local] Abbreviation coh := (coh load_path read to_core).
  #[local] Abbreviation coh_nil := (coh_nil load_path read to_core).

  (** What the cache holds of a unit: what running its file from nothing
      filed, and the unit. *)
  Definition loaded_res (fq : path) (ΘU : gctx) (U : gunit) : Prop :=
    exists src prg u ch, load_path fq = Some src /\ read src = Some prg /\ prog_path prg = fq /\
      to_core prg = Some u /\ run_unit (fq :: ch) nil u ΘU U /\ gc_unit ΘU fq = None.

  Definition cache_ok (C : cache) : Prop := forall fq ΘU U, cfind C fq = Some (ΘU, U) -> loaded_res fq ΘU U.

  Lemma cache_ok_nil : cache_ok nil.
  Proof. intros ? ? ? H; discriminate. Qed.

  Lemma cache_ok_cons : forall C fq ΘU U, cache_ok C -> loaded_res fq ΘU U -> cache_ok ((fq, (ΘU, U)) :: C).
  Proof.
    intros * HC HL fp V W; cbn; destruct (path_beq fp fq) eqn:E; [| apply HC ].
    apply path_beq_true in E as ->; intros [= <- <-]; exact HL.
  Qed.

  (** ** The Invariants

      What the checks a command makes need: its context is well formed, and
      the global context is coherent, so that what a load merges agrees with
      it ([run_wf]). *)

  Definition cinv (ch : list path) (fp : path) (Γimp : ctx) (Θ : gctx) (F : list frame) : Prop :=
    F <> nil /\ ⊢ Θ ⍮ fctx Γimp F /\ coh (eq fp) Θ /\ In fp ch.

  Definition linv (ch : list path) (fp : path) (Θ : gctx) (Γ : ctx) : Prop :=
    ⊢ Θ ⍮ Γ /\ imp_ok Γ /\ coh (eq fp) Θ /\ In fp ch.

  Lemma cinv_ctx {ch fp Γimp Θ F} : cinv ch fp Γimp Θ F -> ⊢ Θ ⍮ fctx Γimp F.
  Proof. intros H; exact (proj1 (proj2 H)). Qed.

  Lemma cinv_gctx {ch fp Γimp Θ F} : cinv ch fp Γimp Θ F -> ⊢g Θ.
  Proof. intros H; exact (ctx_wf_gctx _ _ (cinv_ctx H)). Qed.

  Lemma linv_ctx {ch fp Θ Γ} : linv ch fp Θ Γ -> ⊢ Θ ⍮ Γ.
  Proof. intros H; exact (proj1 H). Qed.

  Lemma linv_gctx {ch fp Θ Γ} : linv ch fp Θ Γ -> ⊢g Θ.
  Proof. intros H; exact (ctx_wf_gctx _ _ (linv_ctx H)). Qed.

  Lemma cinv_step {ch fp Γimp Θ F c Θ' F'} :
    cinv ch fp Γimp Θ F -> run_cmd ch fp Γimp Θ F c Θ' F' -> cinv ch fp Γimp Θ' F'.
  Proof.
    intros (Hne & HF & Hc & Hin) Hr.
    destruct (proj1 run_wf _ _ _ _ _ _ _ _ Hr HF Hc Hin) as (HF' & _ & Hc' & _).
    refine (conj _ (conj HF' (conj Hc' Hin))).
    destruct F as [| f F0]; [ contradiction |].
    destruct (proj1 (run_tail load_path read to_core) _ _ _ _ _ _ _ _ Hr _ _ eq_refl) as [f' ->]; discriminate.
  Qed.

  Lemma linv_step {ch fp Θ Γ c Θ' Γ'} :
    linv ch fp Θ Γ -> run_lead ch Θ Γ c Θ' Γ' -> linv ch fp Θ' Γ'.
  Proof.
    intros (HΓ & Hi & Hc & Hin) Hr.
    destruct (proj1 (proj2 (proj2 (proj2 run_wf))) _ _ _ _ _ _ Hr HΓ Hi _ Hc Hin) as (HΓ' & Hi' & _ & Hc' & _).
    exact (conj HΓ' (conj Hi' (conj Hc' Hin))).
  Qed.

  Lemma linv_leads {ch fp Θ Γ cs Θ' Γ'} :
    linv ch fp Θ Γ -> run_leads ch Θ Γ cs Θ' Γ' -> linv ch fp Θ' Γ'.
  Proof.
    intros (HΓ & Hi & Hc & Hin) Hr.
    destruct (proj1 (proj2 (proj2 (proj2 (proj2 run_wf)))) _ _ _ _ _ _ Hr HΓ Hi _ Hc Hin) as (HΓ' & Hi' & _ & Hc' & _).
    exact (conj HΓ' (conj Hi' (conj Hc' Hin))).
  Qed.

  Lemma linv_nil : forall fp ch, linv (fp :: ch) fp nil nil.
  Proof.
    intros; refine (conj _ (conj (Forall_nil _) (conj (coh_nil _) (or_introl eq_refl)))).
    constructor; constructor.
  Qed.

  (** ** Results of Each Judgment *)

  Record cres : Set := cr { cr_gctx : gctx; cr_frames : list frame; cr_cache : cache }.

  Definition post_cmd ch fp Γimp Θ F c (r : cres) : Prop :=
    run_cmd ch fp Γimp Θ F c (cr_gctx r) (cr_frames r) /\ cache_ok (cr_cache r).

  (** A command expanded ([Imports]) and run, as [rcs_cons] does. *)
  Definition post_xcmd ch fp Γimp Θ F c (r : cres) : Prop :=
    exists c', cmd_xp_ok Θ (fctx Γimp F) c c' /\ post_cmd ch fp Γimp Θ F c' r.

  Definition post_cmds ch fp Γimp Θ F cs (r : cres) : Prop :=
    run_cmds ch fp Γimp Θ F cs (cr_gctx r) (cr_frames r) /\ cache_ok (cr_cache r).

  Record lres : Set := lr { lr_gctx : gctx; lr_ctx : ctx; lr_cache : cache }.

  Definition post_lead ch Θ Γ c (r : lres) : Prop :=
    run_lead ch Θ Γ c (lr_gctx r) (lr_ctx r) /\ cache_ok (lr_cache r).

  Definition post_leads ch Θ Γ cs (r : lres) : Prop :=
    run_leads ch Θ Γ cs (lr_gctx r) (lr_ctx r) /\ cache_ok (lr_cache r).

  Definition post_load ch Θ fq (r : (gctx * cache)%type) : Prop :=
    run_load ch Θ fq (fst r) /\ cache_ok (snd r).

  Definition post_unit ch u (r : (gctx * gunit * cache)%type) : Prop :=
    run_unit ch nil u (fst (fst r)) (snd (fst r)) /\ cache_ok (snd r).

  Lemma xcache_ok {ch fp Γimp Θ F c r} : post_xcmd ch fp Γimp Θ F c r -> cache_ok (cr_cache r).
  Proof. intros (c' & _ & _ & H); exact H. Qed.

  Lemma cinv_xstep {ch fp Γimp Θ F c r} :
    cinv ch fp Γimp Θ F -> post_xcmd ch fp Γimp Θ F c r -> cinv ch fp Γimp (cr_gctx r) (cr_frames r).
  Proof. intros H (c' & _ & Hr & _); exact (cinv_step H Hr). Qed.

  Lemma cons_ok {ch fp Γimp Θ F S c cs r1 r2} :
    S = fctx_tabs fp Γimp F -> acc_ok Θ (cmd_refs S c) -> post_xcmd ch fp Γimp Θ F c r1 ->
    post_cmds ch fp Γimp (cr_gctx r1) (cr_frames r1) cs r2 -> post_cmds ch fp Γimp Θ F (c :: cs) r2.
  Proof.
    intros -> Hac (c' & Hx & Hr1 & _) [Hr2 HC]; split; [ econstructor; eassumption | exact HC ].
  Qed.

  (** The tables of the frames after a command, from those before it
      ([tabs_next]): the command added entries to the innermost frame. *)
  Definition next_tabs (F F' : list frame) (S : list ptab) : list ptab :=
    match F, F' with
    | f :: _, f' :: _ => tabs_next f f' S
    | _, _ => S
    end.

  Lemma next_tabs_ok {ch fp Γimp Θ F c r S} :
    cinv ch fp Γimp Θ F -> post_xcmd ch fp Γimp Θ F c r -> S = fctx_tabs fp Γimp F ->
    next_tabs F (cr_frames r) S = fctx_tabs fp Γimp (cr_frames r).
  Proof.
    intros H (c' & _ & Hr & _) HS.
    destruct F as [| f F0]; [ exfalso; exact (proj1 H eq_refl) |].
    destruct (run_cmd_grows load_path read to_core _ _ _ _ _ _ _ _ Hr _ _ eq_refl) as (f' & E & Hg).
    rewrite E; exact (tabs_next_ok _ _ _ _ _ _ HS Hg).
  Qed.

  Lemma lcons_ok {ch Θ Γ c c' cs r1 r2} :
    acc_ok Θ (cmd_refs (ctx_tabs Γ) c) -> cmd_xp_ok Θ Γ c c' -> post_lead ch Θ Γ c' r1 ->
    post_leads ch (lr_gctx r1) (lr_ctx r1) cs r2 -> post_leads ch Θ Γ (c :: cs) r2.
  Proof. intros Hac Hx [Hr1 _] [Hr2 HC]; split; [ econstructor; eassumption | exact HC ]. Qed.

  Lemma xp_ok {Θ Γ c c'} (Hg : ⊢g Θ) : cmd_xp (mt_of Θ Hg) (ctx_skel Γ) c = xok c' -> cmd_xp_ok Θ Γ c c'.
  Proof. intros E; exists (mt_of Θ Hg); split; [ apply mt_of_spec | exact E ]. Qed.

  Lemma open_ok {Θ Γ E oz Γs src its gs} (Hg : ⊢g Θ) :
    open_gen (mt_of Θ Hg) Γ E oz Γs src its = xok gs -> open_gen_ok Θ Γ E oz Γs src its gs.
  Proof. intros Eg; exists (mt_of Θ Hg); split; [ apply mt_of_spec | exact Eg ]. Qed.

  (** ** Loading *)

  Definition loader (ch : list path) : Type :=
    forall fq src, ~ In fq ch -> load_path fq = Some src ->
      forall C, cache_ok C -> forall u, rres ({r | post_unit (fq :: ch) u r} * elog)%type.

  Lemma hit_ok {ch Θ C fq src prg u ΘU U} :
    cache_ok C -> gc_unit Θ fq = None -> ~ In fq ch ->
    load_path fq = Some src -> read src = Some prg -> prog_path prg = fq -> to_core prg = Some u ->
    cfind C fq = Some (ΘU, U) -> (forall x, In x ch -> gc_unit ΘU x = None) ->
    post_load ch Θ fq (gc_merge Θ (gd_unit fq U :: ΘU), C).
  Proof.
    intros HC Hn Hnch Hs Hr Hp Ht Hc Hfree.
    destruct (HC _ _ _ Hc) as (src' & prg' & u' & ch0 & Hs' & Hr' & _ & Ht' & Hu & HnU).
    rewrite Hs in Hs'; injection Hs' as <-; rewrite Hr in Hr'; injection Hr' as <-; rewrite Ht in Ht'; injection Ht' as <-.
    split; [| exact HC ]; cbn [fst].
    eapply rl_run; try eassumption.
    apply (proj2 (proj2 (proj2 (proj2 (proj2 (run_chain_irrel load_path read to_core)))))
             _ _ _ _ _ Hu (fq :: ch) eq_refl).
    intros x [<- | Hx]; auto.
  Qed.

  Lemma miss_ok {ch Θ fq src prg u r} :
    gc_unit Θ fq = None -> ~ In fq ch ->
    load_path fq = Some src -> read src = Some prg -> prog_path prg = fq -> to_core prg = Some u ->
    post_unit (fq :: ch) u r -> gc_unit (fst (fst r)) fq = None ->
    post_load ch Θ fq (gc_merge Θ (gd_unit fq (snd (fst r)) :: fst (fst r)), (fq, fst r) :: snd r).
  Proof.
    intros Hn Hnch Hs Hr Hp Ht [Hu HC] HnU; destruct r as [[ΘU U] C']; cbn [fst snd] in *.
    split; [ eapply rl_run; eassumption |].
    apply cache_ok_cons; [ exact HC |]; exists src, prg, u, ch; auto 7.
  Qed.

  Equations load_impl (ch : list path) (L : loader ch) (Θ : gctx) (C : cache) (HC : cache_ok C) (fq : path) :
    rres {r : (gctx * cache)%type | post_load ch Θ fq r} :=
  load_impl ch L Θ C HC fq with opt_case (gc_unit Θ fq) => {
    | inleft (exist _ U HU) => rok (exist _ (Θ, C) (conj (rl_filed _ _ _ _ _ _ _ HU) HC))
    | inright Hn with in_dec path_eq_dec fq ch => {
      | left _ => rerr (re_cycle (cycle_chain fq ch))
      | right Hnch with opt_case (load_path fq) => {
        | inright _ => rerr (re_unit fq "cannot find unit")
        | inleft (exist _ src Hsrc) with opt_case (read src) => {
          | inright _ => rerr (re_unit fq "cannot parse unit")
          | inleft (exist _ prg Hprg) with path_eq_dec (prog_path prg) fq => {
            | right _ => rerr (re_unit fq "the file of the unit declares another unit")
            | left Hp with opt_case (to_core prg) => {
              | inright _ => rerr (re_unit fq "cannot elaborate unit")
              | inleft (exist _ u Hu) with opt_case (cfind C fq) => {
                | inleft (exist _ (ΘU, U) Hc) with chain_free ch ΘU => {
                  | inleft (exist _ x _) => rerr (re_cycle (cycle_chain x ch))
                  | inright Hfree =>
                      rok (exist _ (gc_merge Θ (gd_unit fq U :: ΘU), C)
                             (hit_ok HC Hn Hnch Hsrc Hprg Hp Hu Hc Hfree)) }
                | inright _ with L fq src Hnch Hsrc C HC u => {
                  | rerr e => rerr e
                  | rok (exist _ r Hr, _) with opt_case (gc_unit (fst (fst r)) fq) => {
                    | inleft _ => rerr (re_cycle (fq :: fq :: nil))
                    | inright HnU => rok (exist _ _ (miss_ok Hn Hnch Hsrc Hprg Hp Hu Hr HnU)) } } } } } } } } }.

  (** ** Generated Entries *)

  Lemma gens_def_wf {Θ Γimp f F d pv A M} :
    ⊢ Θ ⍮ fctx Γimp (f :: F) -> gm_fresh d (fr_body f) -> Θ ⍮ fctx Γimp (f :: F) ⊢ M : A ->
    ⊢ Θ ⍮ fctx Γimp (fr_add d (ge_def pv A (Some M)) f :: F).
  Proof. intros; apply fctx_add_wf; [ assumption | assumption | apply entry_ok_def; assumption ]. Qed.

  Lemma gens_alias_wf {Θ Γimp f F d pv E} :
    ⊢ Θ ⍮ fctx Γimp (f :: F) -> gm_fresh d (fr_body f) -> Θ ⍮ fctx Γimp (f :: F) ⊢ᵐ E ≈ E ->
    ⊢ Θ ⍮ fctx Γimp (fr_add d (ge_mod pv (gu_mk nil (md_alias E))) f :: F).
  Proof. intros; apply fctx_add_wf; [ assumption | assumption | apply entry_ok_alias0; assumption ]. Qed.

  (** The entries an open generates, in order, as [gens_run] declares them:
      written by no one, so with no privacy check. *)
  Fixpoint gens_impl (Θ : gctx) (Γimp : ctx) (f : frame) (F : list frame) (HF : ⊢ Θ ⍮ fctx Γimp (f :: F))
    (gs : list igen) {struct gs} : rres {F' | gens_run Θ Γimp (f :: F) gs F'} :=
    match gs as gs0 return rres {F' | gens_run Θ Γimp (f :: F) gs0 F'} with
    | nil => rok (exist _ (f :: F) (gr_nil _ _ _))
    | ig_def d pv A M :: gs' =>
        match check_gm_fresh d (fr_body f) with
        | right _ => rerr (re_msg ("duplicate name " ++ d))
        | left Hfr =>
            match check_exp_fast Θ (fctx Γimp (f :: F)) HF A M with
            | right _ => rerr (re_def d (fctx Γimp (f :: F)) A M)
            | left HM =>
                match gens_impl Θ Γimp (fr_add d (ge_def pv A (Some M)) f) F (gens_def_wf HF Hfr HM) gs' with
                | rerr e => rerr e
                | rok (exist _ F' Hg) => rok (exist _ F' (gr_def _ _ _ _ _ _ _ _ _ _ HM Hfr Hg))
                end
            end
        end
    | ig_alias d pv E :: gs' =>
        match check_gm_fresh d (fr_body f) with
        | right _ => rerr (re_msg ("duplicate name " ++ d))
        | left Hfr =>
            match check_modexp Θ (fctx Γimp (f :: F)) HF E with
            | right _ => rerr (re_msg ("ill-formed module expression for module " ++ d))
            | left HE =>
                match gens_impl Θ Γimp (fr_add d (ge_mod pv (gu_mk nil (md_alias E))) f) F (gens_alias_wf HF Hfr HE) gs' with
                | rerr e => rerr e
                | rok (exist _ F' Hg) => rok (exist _ F' (gr_alias _ _ _ _ _ _ _ _ _ HE Hfr Hg))
                end
            end
        end
    end.

  (** ** Leading Commands *)

  Definition lead_step (ch : list path) (L : loader ch) (fp : path) (Θ : gctx) (Γ : ctx) (C : cache) (HC : cache_ok C)
    (H : linv ch fp Θ Γ) (c : ccmd) : rres {r | post_lead ch Θ Γ c r} :=
    match c as c0 return rres {r | post_lead ch Θ Γ c0 r} with
    | cc_load fq =>
        match load_impl ch L Θ C HC fq with
        | rerr e => rerr e
        | rok (exist _ r Hr) => rok (exist _ (lr (fst r) Γ (snd r)) (conj (rd_load _ _ _ _ _ _ _ _ (proj1 Hr)) (proj2 Hr)))
        end
    | cc_open E oz its =>
        match lead_items_dec its with
        | right _ => rerr (re_msg "export is not allowed before the module header")
        | left Hits =>
            match check_modexp Θ Γ (linv_ctx H) E with
            | right _ => rerr (re_import Γ (xe_target E))
            | left HE =>
                match inspect (open_gen (mt_of Θ (linv_gctx H)) Γ E oz (lead_slot E :: Γ) (me_var 0) its) with
                | exist _ (xfail e) _ => rerr (re_import Γ e)
                | exist _ (xok gs) Eg =>
                    rok (exist _ (lr Θ (lead_slot E :: Γ) C)
                           (conj (rd_open _ _ _ _ _ _ _ _ _ _ Hits HE (open_ok _ Eg)) HC))
                end
            end
        end
    | _ => rerr (re_msg "internal error: a leading command that is neither an import nor an open")
    end.

  Fixpoint leads_impl (ch : list path) (L : loader ch) (fp : path) (Θ : gctx) (Γ : ctx) (C : cache) (HC : cache_ok C)
    (H : linv ch fp Θ Γ) (cs : list ccmd) {struct cs} : rres {r | post_leads ch Θ Γ cs r} :=
    match cs as cs0 return rres {r | post_leads ch Θ Γ cs0 r} with
    | nil => rok (exist _ (lr Θ Γ C) (conj (rds_nil _ _ _ _ _ _) HC))
    | c :: cs' =>
        match refs_check Θ (cmd_refs (ctx_tabs Γ) c) with
        | inleft (exist _ e _) => rerr (priv_error e)
        | inright Hac =>
            match inspect (cmd_xp (mt_of Θ (linv_gctx H)) (ctx_skel Γ) c) with
            | exist _ (xfail e) _ => rerr (re_import Γ e)
            | exist _ (xok c') Ex =>
                match lead_step ch L fp Θ Γ C HC H c' with
                | rerr e => rerr e
                | rok (exist _ r1 Hr1) =>
                    match leads_impl ch L fp (lr_gctx r1) (lr_ctx r1) (lr_cache r1) (proj2 Hr1)
                            (linv_step H (proj1 Hr1)) cs' with
                    | rerr e => rerr e
                    | rok (exist _ r2 Hr2) => rok (exist _ r2 (lcons_ok Hac (xp_ok _ Ex) Hr1 Hr2))
                    end
                end
            end
        end
    end.

  (** ** Commands *)

  Definition cres_ok {ch fp Γimp Θ F c} (Θ' : gctx) (F' : list frame) (C : cache)
    (Hr : run_cmd ch fp Γimp Θ F c Θ' F') (HC : cache_ok C) : {r | post_cmd ch fp Γimp Θ F c r} :=
    exist _ (cr Θ' F' C) (conj Hr HC).

  (** A definition: transparent, [abstract] or an axiom. *)
  Definition def_step (ch : list path) (fp : path) (Γimp : ctx) (Θ : gctx) (f : frame) (F : list frame)
    (C : cache) (HC : cache_ok C) (HF : ⊢ Θ ⍮ fctx Γimp (f :: F)) (x : string) (b pv : bool) (A : typ) (oM : option exp) :
    rres {r | post_cmd ch fp Γimp Θ (f :: F) (cc_def x b pv A oM) r} :=
    match check_gm_fresh x (fr_body f) with
    | right _ => rerr (re_msg ("duplicate name " ++ x))
    | left Hfr =>
        match oM as oM0 return rres {r | post_cmd ch fp Γimp Θ (f :: F) (cc_def x b pv A oM0) r} with
        | Some M =>
            match check_exp Θ (fctx Γimp (f :: F)) HF A M with
            | right _ => rerr (re_def x (fctx Γimp (f :: F)) A M)
            | left HM =>
                match b as b0 return rres {r | post_cmd ch fp Γimp Θ (f :: F) (cc_def x b0 pv A (Some M)) r} with
                | true => rok (cres_ok _ _ C (rc_def _ _ _ ch fp Γimp Θ f F x pv A M HM Hfr) HC)
                | false =>
                    match opt_case (gc_const Θ (abs_name fp (fr_chain f) x)) with
                    | inleft _ => rerr (re_msg ("internal error: the constant of " ++ x ++ " is filed already"))
                    | inright Hn => rok (cres_ok _ _ C (rc_abs _ _ _ ch fp Γimp Θ f F x pv A M HM Hfr Hn) HC)
                    end
                end
            end
        | None =>
            match check_typ Θ (fctx Γimp (f :: F)) HF A with
            | inright _ => rerr (re_msg ("the type of axiom " ++ x ++ " is not a type"))
            | inleft (exist _ i HA) =>
                match opt_case (gc_const Θ (abs_name fp (fr_chain f) x)) with
                | inleft _ => rerr (re_msg ("internal error: the constant of " ++ x ++ " is filed already"))
                | inright Hn => rok (cres_ok _ _ C (rc_ax _ _ _ ch fp Γimp Θ f F x b pv A i HA Hfr Hn) HC)
                end
            end
        end
    end.

  Definition alias_step (ch : list path) (fp : path) (Γimp : ctx) (Θ : gctx) (f : frame) (F : list frame)
    (C : cache) (HC : cache_ok C) (HF : ⊢ Θ ⍮ fctx Γimp (f :: F)) (x : string) (pv : bool) (Δ : ctx) (E : modexp) :
    rres {r | post_cmd ch fp Γimp Θ (f :: F) (cc_alias x pv Δ E) r} :=
    match tele_ass_dec Δ with
    | right _ => rerr (re_msg ("parameters of module " ++ x ++ " that are not assumptions"))
    | left Htel =>
        match check_ext Θ (fctx Γimp (f :: F)) HF Δ with
        | right _ => rerr (re_msg ("ill-formed parameters of module " ++ x))
        | left HΔ =>
            match check_modexp Θ (Δ ++ fctx Γimp (f :: F)) (ext_eq_ctx_left _ _ _ _ HΔ) E with
            | right _ => rerr (re_msg ("ill-formed module expression for module " ++ x))
            | left HE =>
                match check_gm_fresh x (fr_body f) with
                | right _ => rerr (re_msg ("duplicate name " ++ x))
                | left Hfr => rok (cres_ok _ _ C (rc_alias _ _ _ ch fp Γimp Θ f F x pv Δ E Htel HΔ HE Hfr) HC)
                end
            end
        end
    end.

  Definition open_step (ch : list path) (fp : path) (Γimp : ctx) (Θ : gctx) (f : frame) (F : list frame)
    (C : cache) (HC : cache_ok C) (HF : ⊢ Θ ⍮ fctx Γimp (f :: F)) (E : modexp) (oz : option string) (its : list iitem) :
    rres {r | post_cmd ch fp Γimp Θ (f :: F) (cc_open E oz its) r} :=
    match check_modexp Θ (fctx Γimp (f :: F)) HF E with
    | right _ => rerr (re_import (fctx Γimp (f :: F)) (xe_target E))
    | left HE =>
        match inspect (open_gen (mt_of Θ (ctx_wf_gctx _ _ HF)) (fctx Γimp (f :: F)) E oz
                         (fctx Γimp (fr_set (open_alias (fr_body f) E oz) f :: F)) (open_src E oz) its) with
        | exist _ (xfail e) _ => rerr (re_import (fctx Γimp (f :: F)) e)
        | exist _ (xok gs) Eg =>
            match gens_impl Θ Γimp f F HF (alias_gens E oz ++ gs) with
            | rerr e => rerr e
            | rok (exist _ F' Hgs) =>
                rok (cres_ok _ _ C (rc_open _ _ _ ch fp Γimp Θ f F E oz its gs F' HE (open_ok _ Eg) Hgs) HC)
            end
        end
    end.

  (** Every expanded command but a module, which recurses on its body. *)
  Definition frame_step (ch : list path) (L : loader ch) (fp : path) (Γimp : ctx) (Θ : gctx) (f : frame)
    (F : list frame) (C : cache) (HC : cache_ok C) (HF : ⊢ Θ ⍮ fctx Γimp (f :: F)) (c : ccmd) :
    rres ({r | post_cmd ch fp Γimp Θ (f :: F) c r} * elog)%type :=
    match c as c0 return rres ({r | post_cmd ch fp Γimp Θ (f :: F) c0 r} * elog)%type with
    | cc_def x b pv A oM =>
        match def_step ch fp Γimp Θ f F C HC HF x b pv A oM with
        | rerr e => rerr e
        | rok r => rok (r, log_nil)
        end
    | cc_alias x pv Δ E =>
        match alias_step ch fp Γimp Θ f F C HC HF x pv Δ E with
        | rerr e => rerr e
        | rok r => rok (r, log_nil)
        end
    | cc_open E oz its =>
        match open_step ch fp Γimp Θ f F C HC HF E oz its with
        | rerr e => rerr e
        | rok r => rok (r, log_nil)
        end
    | cc_mod _ _ _ _ => rerr (re_msg "internal error: a module is run by its own step")
    | cc_load fq =>
        match load_impl ch L Θ C HC fq with
        | rerr e => rerr e
        | rok (exist _ r Hr) =>
            rok (cres_ok (fst r) (f :: F) (snd r) (rc_load _ _ _ _ _ _ _ _ _ _ (proj1 Hr)) (proj2 Hr), log_nil)
        end
    | cc_eval M (Some A) =>
        match check_exp Θ (fctx Γimp (f :: F)) HF A M with
        | right _ => rerr (re_eval_check (fctx Γimp (f :: F)) M A)
        | left HM =>
            rok (cres_ok Θ (f :: F) C (rc_eval_check _ _ _ _ _ _ _ _ _ _ HM) HC,
                 eval_log Θ (fctx Γimp (f :: F)) HF M A HM)
        end
    | cc_eval M None =>
        match @type_infer_at (gc_mk Θ) (fctx Γimp (f :: F)) HF M (user_exp_all M) with
        | inright _ => rerr (re_eval_infer (fctx Γimp (f :: F)) M)
        | inleft (exist _ A HA) =>
            rok (cres_ok Θ (f :: F) C (rc_eval_infer _ _ _ _ _ _ _ _ _ A HA) HC,
                 eval_log Θ (fctx Γimp (f :: F)) HF M A HA)
        end
    end.

  Definition simple_step (ch : list path) (L : loader ch) (fp : path) (Γimp : ctx) (Θ : gctx) (F : list frame)
    (C : cache) (HC : cache_ok C) (H : cinv ch fp Γimp Θ F) (c : ccmd) :
    rres ({r | post_cmd ch fp Γimp Θ F c r} * elog)%type :=
    match F as F0 return cinv ch fp Γimp Θ F0 -> rres ({r | post_cmd ch fp Γimp Θ F0 c r} * elog)%type with
    | nil => fun H => False_rect _ (proj1 H eq_refl)
    | f :: F0 => fun H => frame_step ch L fp Γimp Θ f F0 C HC (cinv_ctx H) c
    end H.

  (** A command expanded, then run by [simple_step]. *)
  Definition xp_simple (ch : list path) (L : loader ch) (fp : path) (Γimp : ctx) (Θ : gctx) (F : list frame)
    (C : cache) (HC : cache_ok C) (H : cinv ch fp Γimp Θ F) (c : ccmd) :
    rres ({r | post_xcmd ch fp Γimp Θ F c r} * elog)%type :=
    match inspect (cmd_xp (mt_of Θ (cinv_gctx H)) (ctx_skel (fctx Γimp F)) c) with
    | exist _ (xfail e) _ => rerr (re_import (fctx Γimp F) e)
    | exist _ (xok c') E =>
        match simple_step ch L fp Γimp Θ F C HC H c' with
        | rok (exist _ r Hp, l) => rok (exist _ r (ex_intro _ c' (conj (xp_ok _ E) Hp)), l)
        | rerr e => rerr e
        end
    end.

  (** [S] is the scope of the frames, [fctx_tabs], kept by [cmds_step]. *)
  Definition cmd_fun (ch : list path) (fp : path) (Γimp : ctx) : Type :=
    forall Θ F C (HC : cache_ok C) (H : cinv ch fp Γimp Θ F) (S : list ptab) (HS : S = fctx_tabs fp Γimp F)
      (c : ccmd),
      rres ({r | post_xcmd ch fp Γimp Θ F c r} * elog)%type.

  (** Recursion on commands is structural, including on the command lists
      nested in modules: [cmds_step] takes the function for one command as a
      uniform parameter, so the guard checker sees through it.  It keeps
      the scope [S] of the frames from one command to the next
      ([next_tabs]), rather than building it for each command. *)
  Definition cmds_step (ch : list path) (fp : path) (Γimp : ctx) (rc : cmd_fun ch fp Γimp) :=
    fix go (Θ : gctx) (F : list frame) (C : cache) (HC : cache_ok C) (H : cinv ch fp Γimp Θ F)
      (S : list ptab) (HS : S = fctx_tabs fp Γimp F) (cs : list ccmd)
      {struct cs} : rres ({r | post_cmds ch fp Γimp Θ F cs r} * elog)%type :=
      match cs as cs0 return rres ({r | post_cmds ch fp Γimp Θ F cs0 r} * elog)%type with
      | nil => rok (exist _ (cr Θ F C) (conj (rcs_nil _ _ _ _ _ _ _ _) HC), log_nil)
      | c :: cs' =>
          match refs_check Θ (cmd_refs S c) with
          | inleft (exist _ e _) => rerr (priv_error e)
          | inright Hac =>
              match rc Θ F C HC H S HS c with
              | rerr e => rerr e
              | rok (exist _ r1 Hr1, l1) =>
                  match go (cr_gctx r1) (cr_frames r1) (cr_cache r1) (xcache_ok Hr1) (cinv_xstep H Hr1)
                          (next_tabs F (cr_frames r1) S) (next_tabs_ok H Hr1 HS) cs' with
                  | rerr e => rerr e
                  | rok (exist _ r2 Hr2, l2) => rok (exist _ r2 (cons_ok HS Hac Hr1 Hr2), log_app l1 l2)
                  end
              end
          end
      end.

  Lemma cmds_step_cons : forall ch fp Γimp rc Θ F C HC H S HS c cs,
      cmds_step ch fp Γimp rc Θ F C HC H S HS (c :: cs) =
      match refs_check Θ (cmd_refs S c) with
      | inleft (exist _ e _) => rerr (priv_error e)
      | inright Hac =>
          match rc Θ F C HC H S HS c with
          | rerr e => rerr e
          | rok (exist _ r1 Hr1, l1) =>
              match cmds_step ch fp Γimp rc (cr_gctx r1) (cr_frames r1) (cr_cache r1) (xcache_ok Hr1)
                      (cinv_xstep H Hr1) (next_tabs F (cr_frames r1) S) (next_tabs_ok H Hr1 HS) cs with
              | rerr e => rerr e
              | rok (exist _ r2 Hr2, l2) => rok (exist _ r2 (cons_ok HS Hac Hr1 Hr2), log_app l1 l2)
              end
          end
      end.
  Proof. reflexivity. Qed.

  (** A module's body runs in a frame of its own. *)
  Lemma mod_inv {ch fp Γimp Θ f F x Δ} :
    cinv ch fp Γimp Θ (f :: F) -> ⊢ Θ ⍮ Δ ++ fctx Γimp (f :: F) ->
    cinv ch fp Γimp Θ (fr_mk (fr_chain f ++ x :: nil) Δ ⋄ :: f :: F).
  Proof.
    intros (_ & _ & Hc & Hin) HΔ; split; [ discriminate |]; refine (conj _ (conj Hc Hin)).
    rewrite fctx_cons; cbn [fr_body fr_params]; apply self_ctx_wf; [ exact HΔ | exact I ].
  Qed.

  Definition head_frame {ch fp Γimp Θ g0 f F cs r}
    (Hr : run_cmds ch fp Γimp Θ (g0 :: f :: F) cs (cr_gctx r) (cr_frames r)) : {g | cr_frames r = g :: f :: F}.
  Proof.
    destruct (cr_frames r) as [| g F'] eqn:E.
    - exfalso; destruct (proj1 (proj2 (run_tail load_path read to_core)) _ _ _ _ _ _ _ _ Hr _ _ eq_refl) as [g' Hg]; congruence.
    - exists g; destruct (proj1 (proj2 (run_tail load_path read to_core)) _ _ _ _ _ _ _ _ Hr _ _ eq_refl) as [g' Hg]; congruence.
  Defined.

  Lemma mod_ok {ch fp Γimp Θ f F x pv Δ0 Δ cs r g} (Hg : ⊢g Θ) :
    tele_xp (mt_of Θ Hg) (ctx_skel (fctx Γimp (f :: F))) Δ0 = xok Δ ->
    tele_ass Δ -> ⊢ Θ ⍮ Δ ++ fctx Γimp (f :: F) -> gm_fresh x (fr_body f) ->
    post_cmds ch fp Γimp Θ (fr_mk (fr_chain f ++ x :: nil) Δ ⋄ :: f :: F) cs r -> cr_frames r = g :: f :: F ->
    post_xcmd ch fp Γimp Θ (f :: F) (cc_mod x pv Δ0 cs)
      (cr (cr_gctx r) (fr_add x (ge_mod pv (gu_body Δ (fr_body g))) f :: F) (cr_cache r)).
  Proof.
    intros EΔ Htel HΔ Hfr [Hr HC] Eg; exists (cc_mod x pv Δ cs); split; [ apply (xp_ok Hg), cmd_xp_mod, EΔ |].
    split; [ cbn [cr_gctx cr_frames]; rewrite Eg in Hr; econstructor; eassumption | exact HC ].
  Qed.

  Fixpoint run_cmd_impl (ch : list path) (L : loader ch) (fp : path) (Γimp : ctx) (Θ : gctx) (F : list frame)
    (C : cache) (HC : cache_ok C) (H : cinv ch fp Γimp Θ F) (S : list ptab) (HS : S = fctx_tabs fp Γimp F)
    (c : ccmd) {struct c} :
    rres ({r | post_xcmd ch fp Γimp Θ F c r} * elog)%type :=
    match c as c0 return rres ({r | post_xcmd ch fp Γimp Θ F c0 r} * elog)%type with
    | cc_mod x pv Δ0 cs =>
        match F as F0 return cinv ch fp Γimp Θ F0 -> S = fctx_tabs fp Γimp F0 ->
                             rres ({r | post_xcmd ch fp Γimp Θ F0 (cc_mod x pv Δ0 cs) r} * elog)%type with
        | nil => fun H _ => False_rect _ (proj1 H eq_refl)
        | f :: F0 => fun H HS =>
            match inspect (tele_xp (mt_of Θ (cinv_gctx H)) (ctx_skel (fctx Γimp (f :: F0))) Δ0) with
            | exist _ (xfail e) _ => rerr (re_import (fctx Γimp (f :: F0)) e)
            | exist _ (xok Δ) EΔ =>
                match tele_ass_dec Δ with
                | right _ => rerr (re_msg ("parameters of module " ++ x ++ " that are not assumptions"))
                | left Htel =>
                    match check_ext Θ (fctx Γimp (f :: F0)) (cinv_ctx H) Δ with
                    | right _ => rerr (re_msg ("ill-formed parameters of module " ++ x))
                    | left HΔx =>
                        let HΔ := ext_eq_ctx_left _ _ _ _ HΔx in
                        match check_gm_fresh x (fr_body f) with
                        | right _ => rerr (re_msg ("duplicate name " ++ x))
                        | left Hfr =>
                            match cmds_step ch fp Γimp (run_cmd_impl ch L fp Γimp) Θ
                                    (fr_mk (fr_chain f ++ x :: nil) Δ ⋄ :: f :: F0) C HC (mod_inv H HΔ)
                                    (tabs_push fp (fr_mk (fr_chain f ++ x :: nil) Δ ⋄) S) (tabs_push_ok _ _ _ _ _ HS) cs with
                            | rerr e => rerr e
                            | rok (exist _ r Hr, l) =>
                                let (g, Eg) := head_frame (proj1 Hr) in
                                rok (exist _ _ (mod_ok _ EΔ Htel HΔ Hfr Hr Eg), l)
                            end
                        end
                    end
                end
            end
        end H HS
    | c0 => xp_simple ch L fp Γimp Θ F C HC H c0
    end.

  (** ** Units *)

  Lemma unit_cinv {fp ch leads r1 P'} :
    post_leads (fp :: ch) nil nil leads r1 -> ⊢ lr_gctx r1 ⍮ fctx (lr_ctx r1) (fr_mk nil P' gm_nil :: nil) ->
    cinv (fp :: ch) fp (lr_ctx r1) (lr_gctx r1) (fr_mk nil P' gm_nil :: nil).
  Proof.
    intros [Hr _] HF; destruct (linv_leads (linv_nil fp ch) Hr) as (_ & _ & Hc & Hin).
    split; [ discriminate | exact (conj HF (conj Hc Hin)) ].
  Qed.

  Lemma leads_gctx {fp ch leads r1} : post_leads (fp :: ch) nil nil leads r1 -> ⊢g lr_gctx r1.
  Proof. intros [Hr _]; exact (linv_gctx (linv_leads (linv_nil fp ch) Hr)). Qed.

  Lemma leads_ctx {fp ch leads r1} : post_leads (fp :: ch) nil nil leads r1 -> ⊢ lr_gctx r1 ⍮ lr_ctx r1.
  Proof. intros [Hr _]; exact (linv_ctx (linv_leads (linv_nil fp ch) Hr)). Qed.

  (** The unit's own frame: its self slot, empty, over its parameters. *)
  Lemma unit_frame_wf {Θ Γimp P} : ⊢ Θ ⍮ P ++ Γimp -> ⊢ Θ ⍮ fctx Γimp (fr_mk nil P gm_nil :: nil).
  Proof. intros HP; rewrite fctx_cons; cbn [fr_body fr_params fctx]; apply self_ctx_wf; [ exact HP | exact I ]. Qed.

  Definition last_frame {ch fp Γimp Θ g0 cs r}
    (Hr : run_cmds ch fp Γimp Θ (g0 :: nil) cs (cr_gctx r) (cr_frames r)) : {g | cr_frames r = g :: nil}.
  Proof.
    destruct (cr_frames r) as [| g F'] eqn:E.
    - exfalso; destruct (proj1 (proj2 (run_tail load_path read to_core)) _ _ _ _ _ _ _ _ Hr _ _ eq_refl) as [g' Hg]; congruence.
    - exists g; destruct (proj1 (proj2 (run_tail load_path read to_core)) _ _ _ _ _ _ _ _ Hr _ _ eq_refl) as [g' Hg]; congruence.
  Defined.

  Lemma unit_ok {fp ch leads P P' cs r1 r2 f} (Hg : ⊢g lr_gctx r1) :
    post_leads (fp :: ch) nil nil leads r1 ->
    tele_xp (mt_of (lr_gctx r1) Hg) (ctx_skel (lr_ctx r1)) P = xok P' ->
    tele_ass P' ->
    acc_ok (lr_gctx r1) (tele_refs (ctx_tabs (lr_ctx r1)) P) ->
    ⊢ lr_gctx r1 ⍮ fctx (lr_ctx r1) (fr_mk nil P' gm_nil :: nil) ->
    post_cmds (fp :: ch) fp (lr_ctx r1) (lr_gctx r1) (fr_mk nil P' gm_nil :: nil) cs r2 ->
    cr_frames r2 = f :: nil ->
    post_unit (fp :: ch) (leads, P, cs) (cr_gctx r2, (gu_body P' (fr_body f))[imp_sub (lr_ctx r1)]ᵘ, cr_cache r2).
  Proof.
    intros [Hr1 _] EP Htel Hac HF [Hr2 HC] Ef; split; [| exact HC ]; cbn [fst snd].
    rewrite Ef in Hr2; eapply ru_intro; try eassumption.
    exists (mt_of _ Hg); split; [ apply mt_of_spec | exact EP ].
  Qed.

  Definition run_unit_step (ch : list path) (L : loader ch) (C : cache) (HC : cache_ok C) (u : cunit) :
    rres ({r | post_unit ch u r} * elog)%type :=
    match ch as ch0 return loader ch0 -> rres ({r | post_unit ch0 u r} * elog)%type with
    | nil => fun _ => rerr (re_msg "internal error: no unit to run")
    | fp :: ch0 => fun L =>
    match u as u0 return rres ({r | post_unit (fp :: ch0) u0 r} * elog)%type with
    | (leads, P, cs) =>
        match leads_impl (fp :: ch0) L fp nil nil C HC (linv_nil fp ch0) leads with
        | rerr e => rerr e
        | rok (exist _ r1 Hr1) =>
            match inspect (tele_xp (mt_of (lr_gctx r1) (leads_gctx Hr1)) (ctx_skel (lr_ctx r1)) P) with
            | exist _ (xfail e) _ => rerr (re_import (lr_ctx r1) e)
            | exist _ (xok P') EP =>
            match tele_ass_dec P' with
            | right _ => rerr (re_msg "unit parameters that are not assumptions")
            | left Htel =>
            match refs_check (lr_gctx r1) (tele_refs (ctx_tabs (lr_ctx r1)) P) with
            | inleft (exist _ e _) => rerr (priv_error e)
            | inright Hac =>
            match check_ext (lr_gctx r1) (lr_ctx r1) (leads_ctx Hr1) P' with
            | right _ => rerr (re_msg "ill-formed unit parameters")
            | left HPx =>
                let HF := unit_frame_wf (ext_eq_ctx_left _ _ _ _ HPx) in
                match cmds_step (fp :: ch0) fp (lr_ctx r1) (run_cmd_impl (fp :: ch0) L fp (lr_ctx r1)) (lr_gctx r1)
                        (fr_mk nil P' gm_nil :: nil) (lr_cache r1) (proj2 Hr1) (unit_cinv Hr1 HF)
                        (fctx_tabs fp (lr_ctx r1) (fr_mk nil P' gm_nil :: nil)) eq_refl cs with
                | rerr e => rerr e
                | rok (exist _ r2 Hr2, l2) =>
                    let (f, Ef) := last_frame (proj1 Hr2) in
                    rok (exist _ _ (unit_ok _ Hr1 EP Htel Hac HF Hr2 Ef), l2)
                end
            end
            end
            end
            end
        end
    end
    end L.

  (** Only a load recurses on something other than a subterm: the chain
      grows by an unfiled path that [load_path] knows ([load_step]), and
      [run_unit_impl] is structural on the accessibility proof.  The
      executable takes that proof, never the list of files. *)

  Definition load_step (ch' ch : list path) : Prop :=
    exists fp s, ch' = fp :: ch /\ ~ In fp ch /\ load_path fp = Some s.

  Definition load_step_intro {ch fp src} (Hn : ~ In fp ch) (Hs : load_path fp = Some src) :
    load_step (fp :: ch) ch :=
    ex_intro _ fp (ex_intro _ src (conj eq_refl (conj Hn Hs))).

  #[derive(eliminator=no)]
  Equations run_unit_impl (ch : list path) (Hacc : Acc load_step ch) :
    forall C, cache_ok C -> forall u, rres ({r | post_unit ch u r} * elog)%type by struct Hacc :=
  run_unit_impl ch Hacc :=
    run_unit_step ch (fun fq src Hn Hs => run_unit_impl (fq :: ch) (Acc_inv Hacc (load_step_intro Hn Hs))).

  Definition loader_of (ch : list path) (Hacc : Acc load_step ch) : loader ch :=
    fun fq src Hn Hs => run_unit_impl (fq :: ch) (Acc_inv Hacc (load_step_intro Hn Hs)).

  Lemma run_unit_impl_unfold : forall ch Hacc, run_unit_impl ch Hacc = run_unit_step ch (loader_of ch Hacc).
  Proof. intros; exact (run_unit_impl_equation_1 ch Hacc). Qed.

  (** The program given on the command line is run like an imported unit,
      with itself as the whole chain and nothing filed.  The log holds its
      own evals; those of the units it loads are checked but not returned. *)
  Definition prog_impl (prg : Cst.prog) (Hacc : Acc load_step (prog_path prg :: nil)) :
    rres (gctx * gunit * list eval_entry)%type :=
    match to_core prg with
    | None => rerr (re_msg "cannot elaborate the program")
    | Some u =>
        match run_unit_impl (prog_path prg :: nil) Hacc nil cache_ok_nil u with
        | rok (exist _ r _, l) => rok (fst (fst r), snd (fst r), proj1_sig l)
        | rerr e => rerr e
        end
    end.

  (** ** Soundness

      By construction: a result carries its judgment. *)

  Theorem prog_impl_sound : forall prg Hacc Θ U log,
      prog_impl prg Hacc = rok (Θ, U, log) ->
      prog_sem load_path read to_core prg Θ U /\ logs_ok log.
  Proof.
    unfold prog_impl; intros * E.
    destruct (to_core prg) as [u |] eqn:Ht; [| discriminate ].
    revert E; match goal with |- context [run_unit_impl ?a ?b ?c ?d ?e] =>
      destruct (run_unit_impl a b c d e) as [[[r [Hp _]] [l Hl]] | e'] end; intros E; [| discriminate ].
    injection E as <- <- <-; split; [ exists u; split; assumption | exact Hl ].
  Qed.

  (** ** Completeness

      By induction on the derivation, for every accessibility proof, cache
      and invariant.  The executable loads only where the derivation does,
      and under the same chain; a unit it has run already it takes from the
      cache, whose result is the derivation's ([run_functional]), so that
      the check of the chain succeeds ([run_chain_fresh]).  Both expand a
      command with an oracle meeting the specification, hence identically. *)

  Ltac dec_ok H :=
    let Hn := fresh "Hn" in
    match goal with
    | |- context [check_gm_fresh ?x ?Φ] => destruct (check_gm_fresh x Φ) as [? | Hn]; [| exfalso; exact (Hn H) ]
    | |- context [tele_ass_dec ?Δ] => destruct (tele_ass_dec Δ) as [? | Hn]; [| exfalso; exact (Hn H) ]
    | |- context [lead_items_dec ?its] => destruct (lead_items_dec its) as [? | Hn]; [| exfalso; exact (Hn H) ]
    | |- context [check_exp ?a ?b ?c ?d ?e] => destruct (check_exp a b c d e) as [? | Hn]; [| exfalso; exact (Hn H) ]
    | |- context [check_exp_fast ?a ?b ?c ?d ?e] => destruct (check_exp_fast a b c d e) as [? | Hn]; [| exfalso; exact (Hn H) ]
    | |- context [check_modexp ?a ?b ?c ?d] => destruct (check_modexp a b c d) as [? | Hn]; [| exfalso; exact (Hn H) ]
    | |- context [check_ext ?a ?b ?c ?d] => destruct (check_ext a b c d) as [? | Hn]; [| exfalso; exact (Hn H) ]
    | |- context [check_ctx ?a ?b ?c] => destruct (check_ctx a b c) as [? | Hn]; [| exfalso; exact (Hn H) ]
    | |- context [check_centry ?a ?b ?c ?d] => destruct (check_centry a b c d) as [? | Hn]; [| exfalso; exact (Hn H) ]
    | |- context [check_typ ?a ?b ?c ?d] => destruct (check_typ a b c d) as [[? ?] | Hn]; [| exfalso; exact (Hn _ H) ]
    | |- context [refs_check ?a ?b] => destruct (refs_check a b) as [[? Hn] | ?]; [ exfalso; exact (Hn H) |]
    | |- context [opt_case ?o] => destruct (opt_case o) as [[? ?] | Hn]; [ exfalso; congruence |]
    end; cbv beta iota.

  Lemma gens_complete : forall Θ Γimp F gs F', gens_run Θ Γimp F gs F' ->
      forall f F0 (E : F = f :: F0) HF, exists r, gens_impl Θ Γimp f F0 HF gs = rok r.
  Proof.
    induction 1 as [F | f F d pv A M gs F' HM Hfr Hg IH | f F d pv E gs F' HE Hfr Hg IH];
      intros f0 F0 Ef HF; cbn [gens_impl]; [ eexists; reflexivity | |];
      injection Ef as <- <-; dec_ok Hfr.
    - dec_ok HM.
      match goal with |- context [gens_impl ?a ?b ?c ?d ?e gs] => destruct (IH _ _ eq_refl e) as [[F1 Hp] E1]; rewrite E1 end.
      eexists; reflexivity.
    - dec_ok HE.
      match goal with |- context [gens_impl ?a ?b ?c ?d ?e gs] => destruct (IH _ _ eq_refl e) as [[F1 Hp] E1]; rewrite E1 end.
      eexists; reflexivity.
  Qed.

  (** Every command but a module runs by [simple_step] once expanded. *)
  Lemma nonmod_complete {ch L fp Γimp Θ F C HC H c c'} :
    ccmd_head c' <> 1 -> cmd_xp_ok Θ (fctx Γimp F) c c' ->
    (exists r, simple_step ch L fp Γimp Θ F C HC H c' = rok r) ->
    forall S HS, exists r, run_cmd_impl ch L fp Γimp Θ F C HC H S HS c = rok r.
  Proof.
    intros Hh Hx [r Er] S HS.
    assert (Hc : ccmd_head c <> 1) by (destruct Hx as (mt & _ & Ex); rewrite <- (cmd_xp_head _ _ _ _ Ex); exact Hh).
    pose proof (cmd_xp_ok_spec _ _ (mt_of _ (cinv_gctx H)) _ _ (mt_of_spec _ _) Hx) as E.
    destruct c; try (exfalso; apply Hc; reflexivity); cbn [run_cmd_impl]; unfold xp_simple;
      destruct (inspect _) as [[c'' | ?] E']; try (exfalso; congruence);
      assert (c'' = c') as -> by congruence; rewrite Er; destruct r as [[r Hp] ?]; eexists; reflexivity.
  Qed.

  Lemma frame_of {ch fp Γimp Θ F} (H : cinv ch fp Γimp Θ F) : exists f F0, F = f :: F0.
  Proof. destruct F as [| f F0]; [ exfalso; exact (proj1 H eq_refl) | eauto ]. Qed.

  Theorem run_impl_complete :
    (forall ch fp Γimp Θ F c' Θ' F', run_cmd ch fp Γimp Θ F c' Θ' F' ->
       forall Hacc C HC H c, cmd_xp_ok Θ (fctx Γimp F) c c' ->
         forall S HS, exists r, run_cmd_impl ch (loader_of ch Hacc) fp Γimp Θ F C HC H S HS c = rok r) /\
    (forall ch fp Γimp Θ F cs Θ' F', run_cmds ch fp Γimp Θ F cs Θ' F' ->
       forall Hacc C HC H S HS,
         exists r, cmds_step ch fp Γimp (run_cmd_impl ch (loader_of ch Hacc) fp Γimp) Θ F C HC H S HS cs = rok r) /\
    (forall ch Θ fq Θ', run_load ch Θ fq Θ' ->
       forall Hacc C HC, exists r, load_impl ch (loader_of ch Hacc) Θ C HC fq = rok r) /\
    (forall ch Θ Γ c' Θ' Γ', run_lead ch Θ Γ c' Θ' Γ' ->
       forall Hacc fp C HC H, exists r, lead_step ch (loader_of ch Hacc) fp Θ Γ C HC H c' = rok r) /\
    (forall ch Θ Γ cs Θ' Γ', run_leads ch Θ Γ cs Θ' Γ' ->
       forall Hacc fp C HC H, exists r, leads_impl ch (loader_of ch Hacc) fp Θ Γ C HC H cs = rok r) /\
    (forall ch Θ0 u Θ U, run_unit ch Θ0 u Θ U -> Θ0 = nil ->
       forall Hacc C HC, exists r, run_unit_impl ch Hacc C HC u = rok r).
  Proof.
    apply run_mut_ind.
    - (* a definition *)
      intros ch fp Γimp Θ f F x pv A M HM Hfr Hacc C HC H c Hx.
      refine (nonmod_complete _ Hx _); [ cbn; discriminate |]; cbn [simple_step frame_step]; unfold def_step.
      dec_ok Hfr; dec_ok HM; eexists; reflexivity.
    - (* an abstract definition *)
      intros ch fp Γimp Θ f F x pv A M HM Hfr Hn Hacc C HC H c Hx.
      refine (nonmod_complete _ Hx _); [ cbn; discriminate |]; cbn [simple_step frame_step]; unfold def_step.
      dec_ok Hfr; dec_ok HM; dec_ok Hn; eexists; reflexivity.
    - (* an axiom *)
      intros ch fp Γimp Θ f F x b pv A i HA Hfr Hn Hacc C HC H c Hx.
      refine (nonmod_complete _ Hx _); [ cbn; discriminate |]; cbn [simple_step frame_step]; unfold def_step.
      dec_ok Hfr; dec_ok HA; dec_ok Hn; eexists; reflexivity.
    - (* a module *)
      intros ch fp Γimp Θ f F x pv Δ cs Θ' g Htel HΔ Hfr Hr IH Hacc C HC H c Hx S HS.
      pose proof (cmd_xp_ok_spec _ _ (mt_of _ (cinv_gctx H)) _ _ (mt_of_spec _ _) Hx) as Ex.
      assert (Hc : ccmd_head c = 1) by (rewrite <- (cmd_xp_head _ _ _ _ Ex); reflexivity).
      destruct c as [| x0 pv0 Δ0 cs0 | | | |]; try discriminate.
      destruct (cmd_xp_mod_inv _ _ _ _ _ _ _ Ex) as (Δ1 & EΔ & [= <- <- <- <-]).
      cbn [run_cmd_impl].
      destruct (inspect _) as [[Δ2 | ?] EΔ']; [ assert (Δ2 = Δ) as -> by congruence | exfalso; congruence ].
      cbv beta iota.
      dec_ok Htel.
      pose proof (ext_of_ctx _ _ _ HΔ) as HΔx; dec_ok HΔx; cbv zeta.
      dec_ok Hfr.
      match goal with |- context [cmds_step ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k cs] =>
        destruct (IH Hacc g h i j k) as [[[r Hp] l] E]; rewrite E end.
      cbv beta iota zeta.
      destruct (head_frame _) as [g' Eg]; eexists; reflexivity.
    - (* an alias *)
      intros ch fp Γimp Θ f F x pv Δ E Htel HΔ HE Hfr Hacc C HC H c Hx.
      refine (nonmod_complete _ Hx _); [ cbn; discriminate |]; cbn [simple_step frame_step]; unfold alias_step.
      dec_ok Htel; dec_ok HΔ; dec_ok HE; dec_ok Hfr; eexists; reflexivity.
    - (* a load *)
      intros ch fp Γimp Θ F fq Θ' Hl IH Hacc C HC H c Hx.
      refine (nonmod_complete _ Hx _); [ cbn; discriminate |].
      destruct (frame_of H) as (f & F0 & ->); cbn [simple_step frame_step].
      destruct (IH Hacc C HC) as [[r Hr] E]; rewrite E; eexists; reflexivity.
    - (* an open *)
      intros ch fp Γimp Θ f F E oz its gs F' HE Hgen Hgs Hacc C HC H c Hx.
      refine (nonmod_complete _ Hx _); [ cbn; discriminate |]; cbn [simple_step frame_step]; unfold open_step.
      dec_ok HE.
      pose proof (open_gen_ok_spec _ (mt_of _ (ctx_wf_gctx _ _ (cinv_ctx H))) _ _ _ _ _ _ _ (mt_of_spec _ _) Hgen) as Eg.
      destruct (inspect _) as [[gs1 | ?] Eg']; [ assert (gs1 = gs) as -> by congruence | exfalso; congruence ].
      cbv beta iota.
      destruct (gens_complete _ _ _ _ _ Hgs _ _ eq_refl (cinv_ctx H)) as [[F1 Hp1] E1]; rewrite E1.
      eexists; reflexivity.
    - (* an ascribed eval *)
      intros ch fp Γimp Θ F M A HM Hacc C HC H c Hx.
      refine (nonmod_complete _ Hx _); [ cbn; discriminate |].
      destruct (frame_of H) as (f & F0 & ->); cbn [simple_step frame_step].
      dec_ok HM; eexists; reflexivity.
    - (* an inferred eval: failure of inference contradicts its completeness *)
      intros ch fp Γimp Θ F M A HM Hacc C HC H c Hx.
      refine (nonmod_complete _ Hx _); [ cbn; discriminate |].
      destruct (frame_of H) as (f & F0 & ->); cbn [simple_step frame_step].
      match goal with |- context [@type_infer_at ?g ?G ?a ?b ?c] => destruct (@type_infer_at g G a b c) as [[A' HA'] | Hno] end.
      { eexists; reflexivity. }
      exfalso.
      destruct (@alg_type_infer_complete (gc_mk Θ) _ A M (user_exp_all M) HM) as (B & HB & _).
      exact (Hno B HB).
    - intros; cbn; eexists; reflexivity.
    - (* a sequence: the head's result is the judgment's, by determinism *)
      intros ch fp Γimp Θ F c c' cs Θ1 F1 Θ2 F2 Hac Hx Hc IHc Hcs IHcs Hacc C HC H S HS; subst S.
      rewrite cmds_step_cons.
      dec_ok Hac.
      destruct (IHc Hacc C HC H c Hx _ eq_refl) as [[[r1 Hp1] l1] E1]; rewrite E1; cbv beta iota.
      pose proof Hp1 as (c'' & Hx' & Hr1 & _).
      rewrite (cmd_xp_ok_functional _ _ _ _ _ Hx' Hx) in Hr1.
      destruct (proj1 run_functional _ _ _ _ _ _ _ _ Hc _ _ _ Hr1) as [E2 E3]; subst Θ1 F1.
      destruct (IHcs Hacc _ (xcache_ok Hp1) (cinv_xstep H Hp1) _ (next_tabs_ok H Hp1 eq_refl)) as [[[r2 Hp2] l2] E2].
      rewrite E2.
      eexists; reflexivity.
    - (* a unit filed already *)
      intros ch Θ fq U HU Hacc C HC; simp load_impl.
      destruct (opt_case (gc_unit Θ fq)) as [[U' HU'] | Hn]; [| congruence ]; simp load_impl.
      eexists; reflexivity.
    - (* a unit loaded: from the cache, or run *)
      intros ch Θ fq src prg u ΘU U Hn Hnch Hs Hr Hp Ht Hu IH HnU Hacc C HC; simp load_impl.
      destruct (opt_case (gc_unit Θ fq)) as [[U' HU'] | Hn']; [ congruence |]; simp load_impl.
      destruct (in_dec path_eq_dec fq ch) as [Hin | Hin]; [ contradiction |]; simp load_impl.
      destruct (opt_case (load_path fq)) as [[src' Hs'] | Hs']; [| congruence ].
      assert (src' = src) as -> by congruence; simp load_impl.
      destruct (opt_case (read src)) as [[prg' Hr'] | Hr']; [| congruence ].
      assert (prg' = prg) as -> by congruence; simp load_impl.
      destruct (path_eq_dec (prog_path prg) fq) as [Hp' | Hp']; [| contradiction ]; simp load_impl.
      destruct (opt_case (to_core prg)) as [[u' Ht'] | Ht']; [| congruence ].
      assert (u' = u) as -> by congruence; simp load_impl.
      destruct (opt_case (cfind C fq)) as [[[ΘU' U''] Hc] | Hc]; simp load_impl.
      + destruct (HC _ _ _ Hc) as (src1 & prg1 & u1 & ch1 & Hs1 & Hr1 & _ & Ht1 & Hu1 & _).
        rewrite Hs in Hs1; injection Hs1 as <-; rewrite Hr in Hr1; injection Hr1 as <-; rewrite Ht in Ht1; injection Ht1 as <-.
        destruct (proj2 (proj2 (proj2 (proj2 (proj2 run_functional)))) _ _ _ _ _ Hu _ _ _ Hu1 eq_refl) as [<- <-].
        destruct (chain_free ch ΘU) as [[x [Hx Hx']] | Hfree]; simp load_impl; [| eexists; reflexivity ].
        exfalso; apply Hx'.
        exact (proj2 (proj2 (proj2 (proj2 (proj2 (run_chain_fresh load_path read to_core))))) _ _ _ _ _ Hu x
                 (or_intror Hx) eq_refl).
      + unfold loader_of.
        match goal with |- context [run_unit_impl (fq :: ch) ?a C HC u] =>
          destruct (IH eq_refl a C HC) as [[[r [Hpost HC']] l] E']; rewrite E'; simp load_impl end.
        destruct (proj2 (proj2 (proj2 (proj2 (proj2 run_functional)))) _ _ _ _ _ Hu _ _ _ Hpost eq_refl) as [E1 E2].
        destruct (opt_case (gc_unit (fst (fst r)) fq)) as [[V HV] | HV]; [ congruence |]; simp load_impl.
        eexists; reflexivity.
    - (* a leading load *)
      intros ch Θ Γ fq Θ' Hl IH Hacc fp C HC H; cbn [lead_step].
      destruct (IH Hacc C HC) as [[r Hr] E]; rewrite E; eexists; reflexivity.
    - (* a leading open *)
      intros ch Θ Γ E oz its gs Hits HE Hgen Hacc fp C HC H; cbn [lead_step].
      dec_ok Hits; dec_ok HE.
      pose proof (open_gen_ok_spec _ (mt_of _ (linv_gctx H)) _ _ _ _ _ _ _ (mt_of_spec _ _) Hgen) as Eg.
      destruct (inspect _) as [[gs1 | ?] Eg']; [ assert (gs1 = gs) as -> by congruence | exfalso; congruence ].
      eexists; reflexivity.
    - intros; cbn; eexists; reflexivity.
    - (* a sequence of leading commands *)
      intros ch Θ Γ c c' cs Θ1 Γ1 Θ2 Γ2 Hac Hx Hc IHc Hcs IHcs Hacc fp C HC H; cbn [leads_impl].
      dec_ok Hac.
      pose proof (cmd_xp_ok_spec _ _ (mt_of _ (linv_gctx H)) _ _ (mt_of_spec _ _) Hx) as Ex.
      destruct (inspect _) as [[c'' | ?] Ex']; [ assert (c'' = c') as -> by congruence | exfalso; congruence ].
      cbv beta iota.
      destruct (IHc Hacc fp C HC H) as [[r1 Hp1] E1]; rewrite E1.
      destruct (proj1 (proj2 (proj2 (proj2 run_functional))) _ _ _ _ _ _ Hc _ _ _ (proj1 Hp1)) as [E2 E3].
      revert Hp1 E1; destruct r1 as [Θ1' Γ1' C1]; cbn [lr_gctx lr_ctx lr_cache] in *; subst Θ1' Γ1'; intros Hp1 E1.
      match goal with |- context [leads_impl ch ?L fp Θ1 Γ1 C1 ?a ?b cs] =>
        destruct (IHcs Hacc fp C1 a b) as [[r2 Hp2] E2] end.
      rewrite E2; eexists; reflexivity.
    - (* a unit *)
      intros fp ch Θ0 leads P P' cs Θ1 Γimp Θ2 f Hl IHl HPx Htel Hac HF Hr IHr -> Hacc C HC.
      rewrite run_unit_impl_unfold; cbn [run_unit_step].
      destruct (IHl Hacc fp C HC (linv_nil fp ch)) as [[r1 Hp1] E1]; rewrite E1; cbv beta iota.
      destruct (proj1 (proj2 (proj2 (proj2 (proj2 run_functional)))) _ _ _ _ _ _ Hl _ _ _ (proj1 Hp1)) as [E2 E3].
      revert Hp1 E1; destruct r1 as [Θ1' Γ1' C1]; cbn [lr_gctx lr_ctx lr_cache] in *; subst Θ1' Γ1'; intros Hp1 E1.
      destruct (inspect _) as [[P1 | ?] EP'];
        epose proof (tele_xp_ok_spec _ _ _ _ _ (mt_of_spec _ _) HPx) as EP; pose proof EP' as EP2; rewrite EP in EP2;
        [ injection EP2 as EPP; subst P1 | discriminate ].
      cbv beta iota.
      dec_ok Htel; dec_ok Hac.
      assert (HPe : lr_gctx (lr Θ1 Γimp C1) ⍮ Γimp ⊢ˣ P' ≈ P').
      { apply ext_of_ctx; rewrite fctx_cons in HF; cbn [fr_body fr_params fctx] in HF.
        exact (proj1 (ctx_decomp_mod HF)). }
      dec_ok HPe; cbv zeta.
      match goal with |- context [cmds_step ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k cs] =>
        destruct (IHr Hacc g h i j k) as [[[r2 Hp2] l2] E2]; rewrite E2 end.
      cbv beta iota zeta.
      destruct (last_frame _) as [f' Ef]; eexists; reflexivity.
  Qed.

  Theorem prog_impl_complete : forall prg Θ U,
      prog_sem load_path read to_core prg Θ U ->
      forall Hacc, exists log, prog_impl prg Hacc = rok (Θ, U, log).
  Proof.
    intros * (u & Ht & Hu) Hacc.
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 run_impl_complete)))) _ _ _ _ _ Hu eq_refl Hacc nil cache_ok_nil)
      as [[[r [Hp HC]] l] E].
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 run_functional)))) _ _ _ _ _ Hu _ _ _ Hp eq_refl) as [E1 E2].
    exists (proj1_sig l); unfold prog_impl; rewrite Ht, E, E1, E2; reflexivity.
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

  Corollary prog_impl_complete_wf : forall read to_core prg Θ U,
      prog_sem load_path read to_core prg Θ U ->
      exists log, prog_impl load_path read to_core prg (load_step_wf _) = rok (Θ, U, log).
  Proof. intros * H; exact (prog_impl_complete _ _ _ _ _ _ H _). Qed.
End Files.
