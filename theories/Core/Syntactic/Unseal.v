(** * Unsealing a Global Context

    [abstract] only hides a body from conversion: an opaque definition still
    has one.  Unsealing a global context makes every definition with a body
    transparent, and leaves axioms and everything else as they are.

    The transparency flag is read only where a stored definition is read as
    a term description ([edenote]): an opaque one has no δ-reduct.  So
    unsealing changes what a lookup reads only by giving such a definition
    its δ-reduct, and a stored body by unsealing it ([dle]): every judgment,
    the global ones included, survives unsealing ([unseal_preserves_wf]).  A
    stored definition is a function of its module's telescope, and is given
    at most that many arguments, so its δ-reduct, once there, can be given
    them too ([ats_term_unseal]).

    A global context without axioms ([gc_no_axioms]) unseals to a transparent
    one ([gc_no_axioms_unseal_transparent]), which is what consistency and
    canonicity are proved at. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import SystemOpt.
From Mctt.Core.Syntactic.System Require Import Definitions Command.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf LookupSound.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Unsealing *)

(** The flag of a definition once unsealed: transparent when it has a body. *)
Definition flag_unseal (b : bool) (B : option exp) : bool :=
  match B with
  | Some _ => true
  | None => b
  end.

(** An entry unsealed: every definition with a body made transparent, at
    every depth of nesting; mutually, for module bodies. *)
Fixpoint ge_unseal (E : gentry) : gentry :=
  match E with
  | ge_def b pv A B => ge_def (flag_unseal b B) pv A B
  | ge_mod pv (gu_mk Δ (md_body sm Φ)) => ge_mod pv (gu_mk Δ (md_body sm (gm_unseal Φ)))
  | ge_mod pv U => ge_mod pv U
  | ge_ind pv p k D Φ => ge_ind pv p k D (gm_unseal Φ)
  | ge_def_mod pv A M U => ge_def_mod pv A M U
  | ge_record pv p R Φ => ge_record pv p R (gm_unseal Φ)
  end
with gm_unseal (Φ : gmod) : gmod :=
  match Φ with
  | gm_nil => gm_nil
  | gm_ext Φ x E => gm_ext (gm_unseal Φ) x (ge_unseal E)
  | gm_open Φ H its => gm_open (gm_unseal Φ) H its
  end.

(** An alias has no definition of its own, so it is unchanged. *)
Definition gu_unseal (U : gunit) : gunit :=
  match U with
  | gu_mk Δ (md_body sm Φ) => gu_mk Δ (md_body sm (gm_unseal Φ))
  | _ => U
  end.

Fixpoint gds_unseal (Θ : gdeps) : gdeps :=
  match Θ with
  | nil => nil
  | (fp, U) :: Θ => (fp, gu_unseal U) :: gds_unseal Θ
  end.

Fixpoint gs_unseal (Ξ : gstack) : gstack :=
  match Ξ with
  | nil => nil
  | (mp, K, U) :: Ξ => (mp, K, gu_unseal U) :: gs_unseal Ξ
  end.

Lemma gu_params_unseal : forall U, gu_params (gu_unseal U) = gu_params U.
Proof. intros [Δ [Φ | E]]; reflexivity. Qed.

Lemma gu_mod_unseal : forall U, gu_mod (gu_unseal U) = gm_unseal (gu_mod U).
Proof. intros [Δ [Φ | E]]; reflexivity. Qed.

Lemma gs_tele_unseal : forall Ξ, gs_tele (gs_unseal Ξ) = gs_tele Ξ.
Proof. induction Ξ as [| [[mp K] U] Ξ IH]; cbn; [ reflexivity | rewrite gu_params_unseal, IH; reflexivity ]. Qed.

Lemma gm_names_unseal : forall Φ, gm_names (gm_unseal Φ) = gm_names Φ.
Proof. induction Φ; cbn; congruence. Qed.

Lemma gm_fresh_unseal : forall x Φ, gm_fresh x Φ -> gm_fresh x (gm_unseal Φ).
Proof. unfold gm_fresh; intros; rewrite gm_names_unseal; assumption. Qed.

(** ** Resolution Commutes with Unsealing

    What a path resolves to is unsealed with the context; what a module path
    resolves to is not changed at all, since a body module is handed back as
    its telescope only, and an alias is unchanged. *)

Lemma gm_resolve_unseal : forall Φ ip,
    gm_resolve (gm_unseal Φ) ip = option_map ge_unseal (gm_resolve Φ ip).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] ip; cbn; [ reflexivity | | apply IH ].
  destruct ip as [| x ip']; [ reflexivity |].
  destruct (String.eqb x y); [| apply IH ].
  destruct ip' as [| z ip''], E as [b pv A B | ? [Δ' [? Φ' | E']] | ? ? ? ? | ? ? ? ? | ? ? ?]; cbn; try reflexivity;
    apply IH.
Qed.

Lemma gm_entry_unseal : forall Φ ip,
    gm_entry (gm_unseal Φ) ip = option_map ge_unseal (gm_entry Φ ip).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] ip; cbn; [ reflexivity | | apply IH ].
  destruct ip as [| x ip']; [ reflexivity |].
  destruct (String.eqb x y); [| apply IH ].
  destruct ip' as [| z ip''], E as [b pv A B | ? [Δ' [? Φ' | E']] | ? ? ? ? ? | ? ? ? ? | ? ? ?]; cbn; try reflexivity;
    apply IH.
Qed.

Lemma gm_submodule_unseal : forall Φ T x ip,
    gm_submodule T (gm_unseal Φ) x ip = gm_submodule T Φ x ip.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] T x ip; cbn; [ reflexivity | | apply IH ].
  destruct (String.eqb x y); [| apply IH ].
  destruct E as [b pv A B | ? [Δ' [? Φ' | E']] | ? ? ? ? | ? ? ? ? | ? ? ?]; cbn; try reflexivity;
    destruct ip; first [ reflexivity | apply IH ].
Qed.

Lemma gm_module_unseal : forall Φ T oD ip,
    gm_module T oD (gm_unseal Φ) ip = gm_module T oD Φ ip.
Proof. intros * ; destruct ip; cbn; [ reflexivity | apply gm_submodule_unseal ]. Qed.

Lemma gs_find_unseal : forall Ξ p,
    gs_find (gs_unseal Ξ) p = option_map (fun r => (gu_unseal (fst r), snd r)) (gs_find Ξ p).
Proof.
  induction Ξ as [| [[mp K] U] Ξ IH]; intros; cbn; [ reflexivity |].
  destruct (qname_strip mp p); [ reflexivity | apply IH ].
Qed.

Lemma gs_find_tele_unseal : forall Ξ p,
    gs_find_tele (gs_unseal Ξ) p =
      option_map (fun r => let '(U, ip, T) := r in (gu_unseal U, ip, T)) (gs_find_tele Ξ p).
Proof.
  induction Ξ as [| [[mp K] U] Ξ IH]; intros; cbn; [ reflexivity |].
  destruct (qname_strip mp p); [ rewrite gs_tele_unseal; reflexivity | apply IH ].
Qed.

(** The kinds of the frames are not sealed. *)
Lemma gs_find_ind_unseal : forall Ξ p, gs_find_ind (gs_unseal Ξ) p = gs_find_ind Ξ p.
Proof.
  induction Ξ as [| [[mp K] U] Ξ IH]; intros; cbn; [ reflexivity |].
  destruct (qname_strip mp p) as [[| ? ?] |]; [ reflexivity | reflexivity | apply IH ].
Qed.

Lemma gs_find_record_unseal : forall Ξ p, gs_find_record (gs_unseal Ξ) p = gs_find_record Ξ p.
Proof.
  induction Ξ as [| [[mp K] U] Ξ IH]; intros; cbn; [ reflexivity |].
  destruct (qname_strip mp p) as [[| ? ?] |]; [ reflexivity | reflexivity | apply IH ].
Qed.

Lemma gds_lookup_unseal : forall Θ fp,
    gds_lookup (gds_unseal Θ) fp = option_map gu_unseal (gds_lookup Θ fp).
Proof.
  induction Θ as [| [fq U] Θ IH]; intros; cbn; [ reflexivity |].
  destruct (path_beq fp fq); [ reflexivity | apply IH ].
Qed.

Lemma gc_resolve_unseal : forall Θ Ξ p,
    gc_resolve (gds_unseal Θ) (gs_unseal Ξ) p = option_map ge_unseal (gc_resolve Θ Ξ p).
Proof.
  intros; unfold gc_resolve, gc_resolve_u; rewrite gs_find_unseal.
  destruct (gs_find Ξ p) as [[U ip] |]; cbn; [ rewrite gu_mod_unseal; apply gm_resolve_unseal |].
  rewrite gds_lookup_unseal.
  destruct (gds_lookup Θ (q_unit p)); cbn; [ rewrite gu_mod_unseal; apply gm_resolve_unseal | reflexivity ].
Qed.

Lemma gc_resolve_unseal_def : forall Θ Ξ p b pv A B,
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    gc_resolve (gds_unseal Θ) (gs_unseal Ξ) p = Some (ge_def (flag_unseal b B) pv A B).
Proof. intros * H; rewrite gc_resolve_unseal, H; reflexivity. Qed.

(** A transparent definition stays as it is. *)
Lemma gc_resolve_unseal_transparent : forall Θ Ξ p pv A M,
    gc_resolve Θ Ξ p = Some (ge_def true pv A (Some M)) ->
    gc_resolve (gds_unseal Θ) (gs_unseal Ξ) p = Some (ge_def true pv A (Some M)).
Proof. intros * H; exact (gc_resolve_unseal_def _ _ _ _ _ _ _ H). Qed.

(** An inductive declaration is not sealed. *)
Lemma gc_module_unseal : forall Θ Ξ p,
    gc_module (gds_unseal Θ) (gs_unseal Ξ) p = gc_module Θ Ξ p.
Proof.
  intros; unfold gc_module, gc_module_u; rewrite gs_find_tele_unseal.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T] |]; cbn; [ reflexivity | |].
  - rewrite gu_params_unseal, gu_mod_unseal; apply gm_submodule_unseal.
  - rewrite gds_lookup_unseal.
    destruct (gds_lookup Θ (q_unit p)); cbn; [| reflexivity ].
    rewrite gu_params_unseal, gu_mod_unseal; apply gm_module_unseal.
Qed.

Lemma ind_mlookup_unseal : forall Θ Ξ p, ind_mlookup (gds_unseal Θ) (gs_unseal Ξ) p = ind_mlookup Θ Ξ p.
Proof. intros; rewrite !ind_mlookup_unfold, gs_find_ind_unseal, gc_module_unseal; reflexivity. Qed.

Lemma ind_lookup_unseal : forall Θ Ξ p, ind_lookup (gds_unseal Θ) (gs_unseal Ξ) p = ind_lookup Θ Ξ p.
Proof. intros; rewrite !ind_lookup_unfold, ind_mlookup_unseal; reflexivity. Qed.

Lemma gc_entry_unseal : forall Θ Ξ p,
    gc_entry (gds_unseal Θ) (gs_unseal Ξ) p = option_map ge_unseal (gc_entry Θ Ξ p).
Proof.
  intros; unfold gc_entry, gc_entry_u; rewrite gs_find_unseal.
  destruct (gs_find Ξ p) as [[U ip] |]; cbn; [ rewrite gu_mod_unseal; apply gm_entry_unseal |].
  rewrite gds_lookup_unseal.
  destruct (gds_lookup Θ (q_unit p)); cbn; [ rewrite gu_mod_unseal; apply gm_entry_unseal | reflexivity ].
Qed.

(** Unsealing leaves the declaration of a record as it is. *)
Lemma record_lookup_unseal : forall Θ Ξ p, record_lookup (gds_unseal Θ) (gs_unseal Ξ) p = record_lookup Θ Ξ p.
Proof.
  intros; unfold record_lookup; rewrite gs_find_record_unseal, gc_entry_unseal.
  destruct (gs_find_record Ξ p); [ reflexivity |].
  destruct (gc_entry Θ Ξ p) as [[| ? [? []] | | |] |]; reflexivity.
Qed.

(** ** Freshness *)

Lemma frame_fresh_unseal : forall Θ Ξ mp,
    frame_fresh Θ Ξ mp -> frame_fresh (gds_unseal Θ) (gs_unseal Ξ) mp.
Proof.
  intros * H; destruct Ξ as [| [[mq Kq] U] Ξ]; cbn in *.
  - destruct H as [Hn Hc]; split; [ rewrite gds_lookup_unseal, Hn; reflexivity | assumption ].
  - destruct H as (x & -> & Hx); exists x; split; [ reflexivity |].
    rewrite gu_mod_unseal; apply gm_fresh_unseal; assumption.
Qed.

(** ** Members *)


(** ** Stored Modules under Unsealing

    A stored body reads, unsealed, as the body unsealed. *)

Definition pair_unseal (r : (ctx * gmod)%type) : (ctx * gmod)%type := (fst r, gm_unseal (snd r)).

Lemma gm_subbody_unseal : forall Φ T x ip,
    gm_subbody T (gm_unseal Φ) x ip = option_map pair_unseal (gm_subbody T Φ x ip).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] T x ip; cbn; [ reflexivity | | apply IH ].
  destruct (String.eqb x y); [| apply IH ].
  destruct E as [b pv A B | ? [Δ' [? Φ' | E']] | ? ? D Φ' | ? ? ? ? | ? ? ?]; cbn; try reflexivity;
    destruct ip; first [ reflexivity | apply IH ].
Qed.

Lemma gm_body_unseal : forall T Φ ip, gm_body T (gm_unseal Φ) ip = option_map pair_unseal (gm_body T Φ ip).
Proof. intros * ; destruct ip; cbn; [ reflexivity | apply gm_subbody_unseal ]. Qed.

Lemma gc_body_unseal : forall Θ Ξ p,
    gc_body (gds_unseal Θ) (gs_unseal Ξ) p = option_map pair_unseal (gc_body Θ Ξ p).
Proof.
  intros; unfold gc_body; rewrite gs_find_tele_unseal.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T] |]; cbn; [ reflexivity | |].
  - rewrite gu_params_unseal, gu_mod_unseal; apply gm_subbody_unseal.
  - rewrite gds_lookup_unseal.
    destruct (gds_lookup Θ (q_unit p)); cbn; [| reflexivity ].
    rewrite gu_params_unseal, gu_mod_unseal; apply gm_body_unseal.
Qed.

Lemma gc_frame_unseal : forall Ξ p, gc_frame (gs_unseal Ξ) p = option_map pair_unseal (gc_frame Ξ p).
Proof.
  intros; unfold gc_frame; rewrite gs_find_tele_unseal.
  destruct (gs_find_tele Ξ p) as [[[[Δ [[|] Φ | E]] [| x ip]] T] |]; reflexivity.
Qed.

Lemma gc_loc_unseal : forall Θ Ξ p, gc_loc (gds_unseal Θ) (gs_unseal Ξ) p = option_map pair_unseal (gc_loc Θ Ξ p).
Proof.
  intros; unfold gc_loc; rewrite gc_frame_unseal.
  destruct (gc_frame Ξ p); [ reflexivity | apply gc_body_unseal ].
Qed.

Lemma gc_unit_unseal : forall Θ Ξ H, gc_unit (gds_unseal Θ) (gs_unseal Ξ) H = option_map pair_unseal (gc_unit Θ Ξ H).
Proof.
  intros; unfold gc_unit.
  destruct (mod_qname H) as [mp |]; [| reflexivity ].
  rewrite gs_find_tele_unseal, gs_find_ind_unseal, gs_find_record_unseal.
  destruct (gs_find_tele Ξ mp) as [[[U [| x ip]] T] |]; cbn.
  - destruct U as [Δ [[|] Φ | E]], (gs_find_ind Ξ mp), (gs_find_record Ξ mp); reflexivity.
  - reflexivity.
  - rewrite gds_lookup_unseal.
    destruct (q_chain mp), (gds_lookup Θ (q_unit mp)) as [[Δ [[|] Φ | E]] |]; reflexivity.
Qed.

Lemma gm_prefix_upto_unseal : forall Φ x, gm_prefix_upto (gm_unseal Φ) x = option_map gm_unseal (gm_prefix_upto Φ x).
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros; cbn; [ reflexivity | |].
  - destruct (String.eqb x y); [ reflexivity | apply IH ].
  - destruct (existsb _ _); [ reflexivity | apply IH ].
Qed.

Lemma gm_noopen_unseal : forall Φ, gm_noopen Φ -> gm_noopen (gm_unseal Φ).
Proof. induction Φ; cbn; tauto. Qed.

Lemma ge_read_unseal : forall T E, ge_read T (ge_unseal E) = ge_unseal (ge_read T E).
Proof. intros T [| ? [? [[] ?| ?]] | | |]; reflexivity. Qed.

Lemma entry_is_body_unseal : forall E, entry_is_body E -> entry_is_body (ge_unseal E).
Proof. intros [| ? [? [[] ?| ?]] | | |]; cbn; tauto. Qed.

Lemma entry_alias_unit_unseal : forall E, entry_alias_unit (ge_unseal E) = entry_alias_unit E.
Proof. intros [| ? [? [[] ?| ?]] | | |]; reflexivity. Qed.

(** ** Descriptions under Unsealing

    [dle R R']: [R'] is [R] read in the unsealed context: a definition may
    have gained its body as its δ-reduct, and a stored body is unsealed. *)
Inductive dle : mdesc -> mdesc -> Prop :=
(** A term may gain a δ-reduct *)
| dl_term : forall A om om', dle (ds_term A om) (ds_term A om')
(** An open module is unchanged *)
| dl_open : forall Δ Φ Φx, dle (ds_open Δ Φ Φx) (ds_open Δ Φ Φx)
(** A closed module's stored body is unsealed *)
| dl_closed : forall Θ p T Φ Ns, dle (ds_closed Θ p T Φ Ns) (ds_closed Θ p T (gm_unseal Φ) Ns)
(** A definition with a module part, or a type former, keeps its term
    part; its module part, a module, is read unsealed *)
| dl_dm : forall Θd A M Rm Rm', ds_is_mod Rm -> dle Rm Rm' -> dle (ds_dm Θd A M Rm) (ds_dm Θd A M Rm').

#[local] Hint Constructors dle : core.

Lemma dle_mod : forall R R' Rm, dle R R' -> ds_mod R = Some Rm ->
    exists Rm', ds_mod R' = Some Rm' /\ dle Rm Rm'.
Proof.
  intros * Hd; revert Rm; induction Hd; intros Rm0 Hm; cbn in Hm |- *; try discriminate; try (injection Hm as <-; eauto).
  all: try (match goal with IH : forall Rm, ds_mod _ = Some Rm -> _ |- _ => exact (IH _ Hm) end).
Qed.

Lemma dle_tele : forall R R', dle R R' -> ds_tele R' = ds_tele R.
Proof. intros * []; reflexivity. Qed.

Lemma dle_mtele : forall R R' T, dle R R' -> ds_mtele R = Some T -> ds_mtele R' = Some T.
Proof.
  intros * Hd Ht; unfold ds_mtele in *.
  destruct (ds_mod R) as [Rm |] eqn:Hm; [| discriminate ].
  destruct (dle_mod _ _ _ Hd Hm) as (Rm' & -> & Hd'); rewrite (dle_tele _ _ Hd'); exact Ht.
Qed.

Lemma dle_ty : forall R R', dle R R' -> ds_ty R' = ds_ty R.
Proof. intros * []; reflexivity. Qed.



Lemma dle_is_mod : forall R R', dle R R' -> ds_is_mod R -> ds_is_mod R'.
Proof. intros * []; cbn; tauto. Qed.

Lemma dle_up : forall Θ' R R', dle R R' -> dle (ds_up Θ' R) (ds_up Θ' R').
Proof. intros Θ' R R' Hd; induction Hd; cbn; constructor; [ apply ds_is_mod_up |]; assumption. Qed.

Lemma dle_sub : forall σ R R', dle R R' -> dle (ds_sub R σ) (ds_sub R' σ).
Proof.
  intros σ R R' Hd; induction Hd; cbn; constructor; [| assumption ].
  match goal with Hm : ds_is_mod ?R0 |- _ => destruct R0; cbn in Hm |- *; first [ contradiction | exact I ] end.
Qed.

Lemma dle_self : forall M R R', dle R R' -> dle (ds_self M R) (ds_self M R').
Proof. intros * [A [] [] | | | ]; cbn; constructor; assumption. Qed.

Lemma dle_named : forall Θ Ns M R R', dle R R' -> dle (ds_named Θ Ns M R) (ds_named Θ Ns M R').
Proof. intros [|] [|] * Hd; cbn [ds_named]; first [ exact Hd | apply dle_self; exact Hd ]. Qed.

Lemma dle_unit : forall R R', dle R R' -> ds_unit R' = ds_unit R.
Proof. intros * [| | [] |]; reflexivity. Qed.

(** "R at N", for a description that is no term: one that is no term
    either. *)
Lemma dle_at : forall R R' N R1, dle R R' -> (forall A om, R <> ds_term A om) -> ds_at R N = Some R1 ->
    exists R1', ds_at R' N = Some R1' /\ dle R1 R1' /\ forall A om, R1 <> ds_term A om.
Proof.
  intros R R' N R1 Hd; revert R1; induction Hd as [| | | Θd A M Rm Rm' Hmm Hd IH]; intros R1 Hn Ha;
    [ exfalso; eapply Hn; reflexivity | | |]; cbn in Ha |- *.
  - destruct (tele_split (rev Δ)) as [[[? ?] ?] |]; [ injection Ha as <-; eexists; split; [ reflexivity | split; [ auto | discriminate ] ] | discriminate ].
  - destruct (tele_split (rev Θ)) as [[[? ?] ?] | ?]; injection Ha as <-; (eexists; split; [ reflexivity | split; [ auto | discriminate ] ]).
  - (* a definition with a module part: its module part at [N], and its
       term part filled when there is an outside parameter *)
    assert (Hnm : forall A0 om, Rm <> ds_term A0 om) by (intros A0 om ->; exact Hmm).
    destruct (ds_at Rm N) as [Rm1 |] eqn:E; [| discriminate ].
    destruct (IH _ Hnm eq_refl) as (Rm1' & -> & Hd1 & Hn1).
    pose proof (ds_at_is_mod _ _ _ Hmm E) as Hm1.
    destruct (tele_split (rev Θd)) as [[[? ?] ?] | ?]; injection Ha as <-.
    + eexists; split; [ reflexivity | split; [ constructor; assumption | discriminate ] ].
    + exists Rm1'; split; [ reflexivity | split; assumption ].
Qed.

Lemma dle_ats : forall Ns R R' R1, dle R R' -> (forall A om, R <> ds_term A om) -> ds_ats R Ns = Some R1 ->
    exists R1', ds_ats R' Ns = Some R1' /\ dle R1 R1'.
Proof.
  induction Ns as [| N Ns IH]; intros * Hd Hn Ha; cbn in Ha |- *; [ injection Ha as <-; eauto |].
  destruct (ds_at R N) as [R2 |] eqn:E; [| discriminate ].
  destruct (dle_at _ _ _ _ Hd Hn E) as (R2' & -> & Hd2 & Hn2).
  exact (IH _ _ _ Hd2 Hn2 Ha).
Qed.

(** A stored definition, given arguments for its telescope: its body, a
    function of the telescope, is too. *)
Lemma ats_term_unseal : forall Ns T A0 M0 R1, tele_ass T -> List.length Ns <= List.length T ->
    ds_ats (ds_term (ctx_pi T A0) None) Ns = Some R1 ->
    exists R1', ds_ats (ds_term (ctx_pi T A0) (Some (ctx_fn T M0))) Ns = Some R1' /\ dle R1 R1'.
Proof.
  induction Ns as [| N Ns IH]; intros * Ha Hl Hats; cbn in Hats |- *; [ injection Hats as <-; eauto |].
  destruct (List.exists_last (l := T)) as (T1 & e & ->); [ intros ->; cbn in Hl; lia |].
  unfold tele_ass in Ha; apply List.Forall_app in Ha as [Ha1 He]; inversion He as [| ? ? [C ->] _]; subst.
  rewrite ctx_pi_app in Hats |- *; rewrite ctx_fn_app; cbn [ctx_pi ctx_fn pi_view fn_view] in Hats |- *.
  rewrite ctx_pi_sub in Hats |- *; rewrite ctx_fn_sub.
  apply (IH (tele_sub T1 (Id,,N))); [ apply tele_ass_sub; exact Ha1 | rewrite length_tele_sub; rewrite length_app in Hl; cbn in Hl; lia | exact Hats ].
Qed.


(** ** Lookup under Unsealing

    What a well-formed module expression denotes, it denotes unsealed up to
    [dle]; a stored unit or entry is read unsealed. *)

Definition unit_at (o : option qname) (U : gunit) : gunit :=
  match o with
  | Some _ => gu_unseal U
  | None => U
  end.

Definition entry_at (o : option qname) (E : gentry) : gentry :=
  match o with
  | Some _ => ge_unseal E
  | None => E
  end.

Definition wfpre (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (H : modexp) : Prop :=
  Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H \/ exists H0 x, H = me_mem H0 x /\ Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H0 ≈ H0.

Definition bpre (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (Φ Φx : gmod) : Prop :=
  forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ᵐ H ≈ H.

Definition upre (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (o : option qname) (U : gunit) : Prop :=
  match U with
  | gu_mk Δ (md_alias E) => Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ E ≈ E
  | gu_mk Δ (md_body sm Φ) =>
      match o with
      | Some _ => sm = sm_closed /\ gm_noopen Φ
      | None => forall Φx, body_xp Θ Ξ (Δ ++ Γ) Φ Φx -> bpre Θ Ξ (Δ ++ Γ) Φ Φx
      end
  end.

(** What an entry's unit, a module's or the module part of a definition
    with a module part, needs. *)
Definition epre (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (o : option qname) (E : gentry) : Prop :=
  forall pv U, (E = ge_mod pv U \/ exists A M, E = ge_def_mod pv A M U) -> upre Θ Ξ Γ o U.

Lemma upre_full : forall Θ Ξ Γ U, unit_full Θ Ξ Γ U -> upre Θ Ξ Γ None U.
Proof.
  intros * Hf; destruct U as [Δ [[] Φ | E]]; cbn in Hf |- *; try contradiction.
  - destruct Hf as (Φx & lv & Hx & HC & _ & Ho & _).
    pose proof (ctx_wf_gctx _ _ _ HC) as Hg.
    intros Φx' Hx'; rewrite <- (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ Hx _ Hx').
    exact Ho.
  - exact (proj2 (proj2 Hf)).
Qed.


Lemma edenote_term_inv : forall Θ Ξ Γ o E A om, edenote Θ Ξ Γ o E (ds_term A om) ->
    exists b pv oM, E = ge_def b pv A oM /\ om = (if b then oM else None).
Proof.
  intros * Hd; inversion Hd; subst; eauto.
  match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hm; contradiction end.
Qed.

Lemma ge_read_def : forall T E b pv A oM, ge_read T E = ge_def b pv A oM -> E = ge_def b pv A oM.
Proof. intros T [| ? [? [[] ?| ?]] | | |] * H; cbn in H; congruence. Qed.

Lemma mdenote_unseal_all : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    (forall Γ H R, mdenote Θ Ξ Γ H R -> wfpre Θ Ξ Γ H ->
       exists R', mdenote (gds_unseal Θ) (gs_unseal Ξ) Γ H R' /\ dle R R') /\
    (forall Γ o U R, udenote Θ Ξ Γ o U R -> upre Θ Ξ Γ o U ->
       exists R', udenote (gds_unseal Θ) (gs_unseal Ξ) Γ o (unit_at o U) R' /\ dle R R') /\
    (forall Γ o E R, edenote Θ Ξ Γ o E R -> epre Θ Ξ Γ o E ->
       exists R', edenote (gds_unseal Θ) (gs_unseal Ξ) Γ o (entry_at o E) R' /\ dle R R') /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> bpre Θ Ξ Γ Φ Φx -> body_xp (gds_unseal Θ) (gs_unseal Ξ) Γ Φ Φx) /\
    (forall Γ H its gs, items_gen Θ Ξ Γ H its gs -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
       items_gen (gds_unseal Θ) (gs_unseal Ξ) Γ H its gs).
Proof.
  intros Θ Ξ Hg; pose proof (gctx_valid_syn _ _ Hg) as Hv; pose proof (wf_gstack_closed _ _ Hg) as Hc; apply mdenote_all_ind.
  - (* a loaded unit or an open frame: its stored body, unsealed *)
    intros Γ H p T Φ Hq Hu _.
    exists (ds_closed nil p T (gm_unseal Φ) nil); split; [| constructor ].
    eapply mdenote_unit; [ exact Hq | rewrite gc_unit_unseal, Hu; reflexivity ].
  - (* the open frame of a member's module: its type former, with its
       module unsealed *)
    intros Γ H p pq k D Mk Tm Φm Hq Hk HMk Hl _.
    exists (ind_former_desc pq k D Mk (ds_closed nil p Tm (gm_unseal Φm) nil)); split;
      [ eapply mdenote_ind_frame; [ exact Hq | rewrite gs_find_ind_unseal; exact Hk | exact HMk
                             | rewrite gc_loc_unseal, Hl; reflexivity ]
      | constructor; [ exact I | constructor ] ].
  - (* a slot *)
    intros Γ x U R Hx Hu IHu Hw.
    destruct Hw as [HH | (? & ? & [=] & _)].
    pose proof (ctx_lookup_mod_wf _ _ _ _ _ (presup_modexp_eq_ctx HH) Hx) as HU.
    destruct (IHu (upre_full _ _ _ _ (proj1 (unit_full_of_eq _ _ _ _ _ HU)))) as (R' & Hu' & Hd).
    exists R'; split; [ eapply mdenote_slot; eassumption | exact Hd ].
  - (* a literal *)
    intros Γ U R Hu IHu Hw.
    destruct Hw as [HH | (? & ? & [=] & _)].
    destruct (IHu (upre_full _ _ _ _ (proj1 (modexp_gen _ _ _ _ _ HH)))) as (R' & Hu' & Hd).
    exists R'; split; [ apply mdenote_lit; exact Hu' | exact Hd ].
  - (* an application of a module *)
    intros Γ H N R R' Hm IH Ha Hw.
    destruct Hw as [HH | (? & ? & [=] & _)].
    destruct (proj1 (modexp_gen _ _ _ _ _ HH)) as (HH0 & R1 & T & B & T1 & i & Hm1 & Ht & Hv1 & HB & HN); cbn [gen_m] in *.
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm1 _ Hm) in Ht.
    destruct (IH (or_introl HH0)) as (R0' & Hm' & Hd).
    assert (Hn : forall A om, R <> ds_term A om) by (intros A om ->; discriminate Ht).
    destruct (dle_at _ _ _ _ Hd Hn Ha) as (R1' & Ha' & Hd1 & _).
    exists R1'; split; [ eapply mdenote_app; eassumption | exact Hd1 ].
  - (* a selection *)
    intros Γ H y R0 R0m Γy E rd R R' Hm IH Hmod He Hd IHd Hr Hw.
    assert (HH0 : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H)
      by (destruct Hw as [HH | (H0 & x & [= <- <-] & HH)]; [ exact (proj1 (modexp_gen _ _ _ _ _ HH)) | exact HH ]).
    destruct (IH (or_introl HH0)) as (R0' & Hm' & Hd0).
    destruct (dle_mod _ _ _ Hd0 Hmod) as (R0m' & Hmod' & Hdm).
    pose proof (desc_ok_mod _ _ Hg _ _ _ (me_desc_ok _ _ _ _ _ _ HH0 Hm) Hmod) as Hok0.
    destruct Hdm as [ A om om' | Δ Φw Φ | Θc p T Φ Ns | ].
    1,4: exfalso; exact (ds_mod_is_mod _ _ Hmod).
    + (* an open module: its entry, read as it is *)
      inversion Hok0 as [| ? ? ? ? HC _ _ _ _ _ _ | |]; subst.
      cbn in He; destruct (gm_prefix_upto Φ y) as [[| Φ' x E1 | ? ? ?] |] eqn:Hp; try discriminate.
      destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & _).
      assert (He1 : Γy = body_ctx Φ' ++ Δ /\ rd = reader_open Δ Φ' /\ E1 = E).
      { destruct E1 as [[|] ? ? [] | | | | ]; try discriminate; injection He as <- <- <-; repeat split. }
      destruct He1 as (-> & -> & HE1).
      assert (Hep : epre Θ Ξ ((body_ctx Φ' ++ Δ) ++ Γ) None E).
      { intros pv U HEU; rewrite HE1 in Hp.
        assert (Hu : entry_unit E = Some U) by (destruct HEU as [-> | (? & ? & ->)]; reflexivity).
        pose proof (body_prefix_mod_wf _ _ _ _ _ _ _ _ _ HC Hp Hu) as HU.
        rewrite <- app_assoc; apply upre_full, (proj1 (unit_full_of_eq _ _ _ _ _ HU)). }
      destruct (IHd Hep) as (R'' & Hd'' & HdR).
      cbn in Hr; destruct (gm_fill Φ') as [σ |] eqn:Hf; cbn in Hr; [ injection Hr as <- | discriminate ].
      exists (ds_up Δ (ds_sub R'' σ)); split; [| apply dle_up, dle_sub; exact HdR ].
      eapply mdenote_mem; [ exact Hm' | exact Hmod' | cbn; rewrite Hp; exact He | exact Hd'' | cbn; rewrite Hf; reflexivity ].
    + (* a closed module: its stored entry, unsealed *)
      pose proof (ds_canon_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hg Hm) Hmod) as Hl; cbn in Hl.
      pose proof (loc_closed _ _ Hg _ _ _ Hl) as [_ HcΦ].
      inversion Hok0 as [| | Γ0 Θa T0 Φ1 Ns1 Θ0 Ξ0 p0 Hg0 Hsub Hloc HaT HsT' HT HΘ' Hargs HaΘ |]; subst.
      cbn in He; destruct (gm_prefix_upto Φ y) as [[| Φ0 x E1 | ? ? ?] |] eqn:Hp; try discriminate.
      injection He as <- <- <-.
      destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & _).
      pose proof (body_closed_prefix _ _ _ _ HcΦ Hp) as HcE; cbn in HcE; destruct HcE as [_ HcE].
      destruct (loc_valid _ _ _ _ _ Hv Hl) as [_ HvΦ].
      pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ HvΦ Hp) as HE0.
      assert (Hep : epre Θ Ξ (nil ++ Γ) (Some (qname_in p y)) (ge_read T E1)).
      { intros pv U HE; cbn [List.app].
        destruct E1 as [ | pv' [Ta [sm Φy | E']] | | pvd Ad Md Ud | ]; cbn [ge_read] in HE;
          destruct HE as [HE | (A0 & M0 & HE)]; try discriminate; try (destruct sm; discriminate).
        - destruct HcE as (-> & _ & HcΦy); injection HE as <- <-; cbn.
          split; [ reflexivity | exact (body_closed_noopen _ _ HcΦy) ].
        - injection HE as <- <-; cbn.
          cbn [ge_valid syn_V] in HE0; destruct HE0 as (HEw & HΔ & _).
          rewrite gunit_scoped_mk in HcE; destruct HcE as [HsΔ _].
          exact (modexp_tele_weaken _ _ _ _ _ _ HEw (closed_tele_wf _ _ _ _ HsΔ HΔ (ctx_app_wf_tail _ _ _ _ HΘ'))).
        - (* a definition with a module part: its module part, an alias *)
          injection HE as <- <- <- <-.
          cbn [ge_read] in Hd; inversion Hd; subst; cbn.
          cbn [ge_valid syn_V] in HE0; destruct HE0 as [(HEw & HΔ & _) _].
          destruct HcE as (_ & _ & HsU); rewrite gunit_scoped_mk in HsU; destruct HsU as [HsΔ _].
          exact (modexp_tele_weaken _ _ _ _ _ _ HEw (closed_tele_wf _ _ _ _ HsΔ HΔ (ctx_app_wf_tail _ _ _ _ HΘ'))). }
      destruct (IHd Hep) as (R'' & Hd'' & HdR).
      cbn in Hr; destruct (ds_ats_read R Ns) as [R1 |] eqn:Hats; cbn in Hr; [ injection Hr as <- | discriminate ].
      assert (Hats' : exists R1', ds_ats_read R'' Ns = Some R1' /\ dle R1 R1').
      { destruct HdR as [A om om' | | | Θd Ad Md Rm Rm'' Hmm HdRm];
          try (cbn [ds_ats_read] in Hats |- *; eapply dle_ats; [ constructor | discriminate | exact Hats ]).
        2: { (* a definition with a module part: its module part at the
                arguments, and its term part given them when it has no
                outside parameter *)
             assert (Hnm : forall A0 om, Rm <> ds_term A0 om) by (intros A0 om ->; exact Hmm).
             destruct Θd as [| e Θd].
             - cbn [ds_ats_read] in Hats |- *.
               destruct (ds_ats_tm (ds_term Ad (Some Md)) Ns) as [[B [M' |] | | |] |]; try discriminate.
               destruct (ds_ats Rm Ns) as [Rm1 |] eqn:E; [ injection Hats as <- | discriminate ].
               destruct (dle_ats _ _ _ _ HdRm Hnm E) as (Rm1' & -> & Hd1).
               eexists; split; [ reflexivity | constructor; [ exact (ds_ats_is_mod _ _ _ Hmm E) | exact Hd1 ] ].
             - cbn [ds_ats_read] in Hats |- *; eapply dle_ats; [ constructor; eassumption | discriminate | exact Hats ]. }
        cbn [ds_ats_read] in Hats |- *.
        (* a stored definition: unsealed, an abstract one with a body gains it *)
        destruct (edenote_term_inv _ _ _ _ _ _ _ Hd) as (b & pv & oM & HE1 & Hom).
        pose proof (ge_read_def _ _ _ _ _ _ HE1) as ->.
        cbn [entry_at ds_epath ge_unseal ge_read] in Hd''; inversion Hd''; subst.
        destruct oM as [M |].
        - destruct b; cbn in *.
          + exists R1; split; [ exact Hats | destruct (ds_ats_term _ _ _ _ Hats) as (? & ? & ->); constructor ].
          + cbn [ge_valid syn_V] in HE0; destruct HE0 as (A1 & -> & _ & HM).
            destruct (HM M eq_refl) as (M1 & -> & _).
            exact (ats_term_unseal _ _ _ _ _ HaT (args_ok_length _ _ _ _ _ Hargs) Hats).
        - assert (Hn : (if b then None else None) = @None exp) by (destruct b; reflexivity).
          destruct b; cbn in *; (exists R1; split; [ exact Hats | destruct (ds_ats_term _ _ _ _ Hats) as (? & ? & ->); constructor ]). }
      destruct Hats' as (R1' & Hats' & Hd1).
      exists (ds_up Θc (ds_named Θc Ns (apps (a_mem (qname_mod p) y) Ns) R1')); split; [| apply dle_up, dle_named; exact Hd1 ].
      eapply mdenote_mem; [ exact Hm' | exact Hmod' | cbn; rewrite gm_prefix_upto_unseal, Hp; cbn; reflexivity
                     | cbn [ds_epath entry_at] in Hd'' |- *; rewrite <- ge_read_unseal in Hd''; exact Hd'' | cbn; rewrite Hats'; reflexivity ].
  - (* the open frame of a record's module: its type former, with its
       module unsealed *)
    intros Γ H p R Tm Φm Hq Hr Hl _.
    exists (record_former_desc p R (ds_closed nil p Tm (gm_unseal Φm) nil)); split;
      [ eapply mdenote_record_frame; [ exact Hq | rewrite gs_find_record_unseal; exact Hr
                                | rewrite gc_loc_unseal, Hl; reflexivity ]
      | constructor; [ exact I | constructor ] ].
  - (* a body: a stored one is closed, with no open *)
    intros Γ o Δ sm Φ Φx R Hx IHx Hb Hpre.
    destruct o as [pq |]; cbn in Hpre |- *.
    + destruct Hpre as [-> Hno].
      pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ Hx _ (body_xp_noopen _ _ _ _ Hno)) as ->.
      cbn in Hb; injection Hb as <-.
      exists (ds_closed nil pq Δ (gm_unseal Φ) nil); split; [| constructor ].
      eapply udenote_body; [ apply body_xp_noopen, gm_noopen_unseal; exact Hno | reflexivity ].
    + exists R; split; [ eapply udenote_body; [ exact (IHx (Hpre _ Hx)) | exact Hb ] |].
      destruct sm; cbn in Hb; [ injection Hb as <-; constructor | discriminate ].
  - (* an alias *)
    intros Γ o Δ E R R' Hm IH Hmod Hpre.
    destruct (IH (or_introl Hpre)) as (R1 & Hm1 & Hd).
    destruct (dle_mod _ _ _ Hd Hmod) as (Rm' & Hmod' & Hdm).
    exists (ds_up Δ Rm'); split; [| apply dle_up; exact Hdm ].
    destruct o; cbn; eapply udenote_alias; eassumption.
  - (* a definition: a stored one may gain its δ-reduct *)
    intros Γ o b pv A oM _.
    destruct o; cbn [entry_at ge_unseal].
    + eexists; split; constructor.
    + eexists; split; constructor.
  - intros Γ o pv U R Hu IHu Hpre.
    destruct (IHu (Hpre _ _ (or_introl eq_refl))) as (R' & Hu' & Hd).
    exists R'; split; [| exact Hd ].
    destruct o; cbn [entry_at]; [| constructor; exact Hu' ].
    destruct U as [Δ [sm Φ | E]]; cbn in Hu' |- *; constructor; exact Hu'.
  - (* a stored inductive type: its type former, with its module unsealed *)
    intros Γ o pv pq k D Φ Mk pm Tm Φm HMk Hpm Hl _.
    exists (ind_former_desc pq k D Mk (ds_closed nil pm Tm (gm_unseal Φm) nil)); split.
    + destruct o; cbn [entry_at ge_unseal];
        (eapply edenote_ind_case; [ exact HMk | exact Hpm | rewrite gc_loc_unseal, Hl; reflexivity ]).
    + constructor; [ exact I | constructor ].
  - (* a definition with a module part: its module part, read unsealed *)
    intros Γ o pv A M Δ E Rm Hu IHu Hpre.
    destruct (IHu (Hpre _ _ (or_intror (ex_intro _ A (ex_intro _ M eq_refl))))) as (Rm' & Hu' & Hd).
    exists (ds_dm nil A M Rm'); split.
    + destruct o; cbn [entry_at ge_unseal unit_at gu_unseal] in Hu' |- *; constructor; exact Hu'.
    + constructor; [ exact (udenote_is_mod _ _ _ _ _ _ Hu) | exact Hd ].
  - (* a stored record type: its type former, with its module unsealed *)
    intros Γ p pv pr R Φ Tm Φm Hl _.
    exists (record_former_desc p R (ds_closed nil p Tm (gm_unseal Φm) nil)); split;
      [ cbn [entry_at ge_unseal]; eapply edenote_record; rewrite gc_loc_unseal, Hl; reflexivity
      | constructor; [ exact I | constructor ] ].
  - intros; constructor.
  - intros Γ Φ Φx x E Hx IHx Hpre; constructor; apply IHx; intros k Ψ H Hk; apply (Hpre k); exact Hk.
  - (* an open: what it generates is read alike *)
    intros Γ Φ Φx H its R Rm gs Hx IHx Hm IHm Hmod Hig IHig Hok Hpre.
    unfold bpre in Hpre; rewrite (body_opens_open _ _ _ _ _ _ _ _ Hig) in Hpre.
    pose proof (Hpre 0 _ _ eq_refl) as HH.
    destruct (IHm (or_introl HH)) as (R' & Hm' & Hd).
    destruct (dle_mod _ _ _ Hd Hmod) as (Rm' & Hmod' & _).
    econstructor; [ apply IHx; intros k Ψ H' Hk; exact (Hpre (S k) _ _ Hk) | exact Hm' | exact Hmod' | exact (IHig HH) | exact Hok ].
  - intros; constructor.
  - intros Γ H d pv its gs Hig IHig HH; constructor; exact (IHig HH).
  - intros Γ H n d pv A om its gs Hm IHm Hig IHig HH.
    destruct (IHm (or_intror (ex_intro _ H (ex_intro _ n (conj eq_refl HH))))) as (R' & Hm' & Hd).
    inversion Hd; subst; econstructor; [ exact Hm' | exact (IHig HH) ].
  - intros Γ H n d pv R its gs Hm IHm Hism Hig IHig HH.
    destruct (IHm (or_intror (ex_intro _ H (ex_intro _ n (conj eq_refl HH))))) as (R' & Hm' & Hd).
    econstructor; [ exact Hm' | exact (dle_is_mod _ _ Hd Hism) | exact (IHig HH) ].
  - (* a member with a term part and a module part *)
    intros Γ H n d pv R A Rm its gs Hm IHm Hty Hmd Hig IHig HH.
    destruct (IHm (or_intror (ex_intro _ H (ex_intro _ n (conj eq_refl HH))))) as (R' & Hm' & Hd).
    destruct (dle_mod _ _ _ Hd Hmd) as (Rm' & Hmd' & _).
    eapply items_gen_dm; [ exact Hm' | rewrite (dle_ty _ _ Hd); exact Hty | exact Hmd' | exact (IHig HH) ].
Qed.


Corollary mdenote_unseal : forall Θ Ξ Γ H H' R, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ H R ->
    exists R', mdenote (gds_unseal Θ) (gs_unseal Ξ) Γ H R' /\ dle R R'.
Proof.
  intros * HH Hm; pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
  exact (proj1 (mdenote_unseal_all _ _ Hg) _ _ _ Hm (or_introl (wf_modexp_eq_refl_left HH))).
Qed.

Corollary mdenote_mem_unseal : forall Θ Ξ Γ H H' x R, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ (me_mem H x) R ->
    exists R', mdenote (gds_unseal Θ) (gs_unseal Ξ) Γ (me_mem H x) R' /\ dle R R'.
Proof.
  intros * HH Hm; pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
  exact (proj1 (mdenote_unseal_all _ _ Hg) _ _ _ Hm (or_intror (ex_intro _ H (ex_intro _ x (conj eq_refl (wf_modexp_eq_refl_left HH)))))).
Qed.

Corollary body_xp_unseal : forall Θ Ξ Γ Φ Φx, ⊢ᵍ Θ ⍮ Ξ -> body_xp Θ Ξ Γ Φ Φx -> bpre Θ Ξ Γ Φ Φx ->
    body_xp (gds_unseal Θ) (gs_unseal Ξ) Γ Φ Φx.
Proof. intros * Hg; exact (proj1 (proj2 (proj2 (proj2 (mdenote_unseal_all _ _ Hg)))) _ _ _). Qed.

(** A member read from a closed module part as a term part with a module
    part, a type former's or a definition's: its term part as it is, its
    module part unsealed. *)
#[local] Ltac unseal_dm_read :=
  match goal with
  | HH : _ ⍮ _ ⍮ _ ⊢ᵐ ?H ≈ ?H, Hm : mdenote _ _ _ (me_mem ?H _) _, Hed : edenote _ _ _ _ _ _,
    Hats : ds_ats_read _ ?Ns = Some _, Hr : ds_red _ = Some _ |- _ =>
      left; destruct (mdenote_mem_unseal _ _ _ _ _ _ _ HH Hm) as (R' & Hm' & Hd);
      cbn [ge_read] in Hed; inversion Hed; subst;
      unfold ind_former_desc, record_former_desc in Hats; cbn [ds_ats_read] in Hats;
      match type of Hats with context [ds_ats_tm (ds_term ?A0 (Some ?M0)) Ns] =>
        destruct (ds_ats_tm (ds_term A0 (Some M0)) Ns) as [[B [M' |] | | |] |]; try discriminate end;
      match type of Hats with context [ds_ats ?Rm0 Ns] =>
        destruct (ds_ats Rm0 Ns) as [Rm1 |]; [ injection Hats as <- | discriminate ] end;
      rewrite ds_named_fix in Hd, Hr by reflexivity; cbn [ds_up List.app] in Hd, Hr;
      inversion Hd; subst; eexists; split; [ exact Hm' | split; [ exact Hr | rewrite ds_named_fix by reflexivity; reflexivity ] ]
  end.

(** The δ-reduct a member is looked up with, unsealed: the same, or, for a
    stored axiom or abstract definition, read as its name, the name of a
    member of the closed module part the module expression has unsealed. *)
Lemma mem_unseal_red : forall Θ Ξ Γ H x R M, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
    mdenote Θ Ξ Γ (me_mem H x) R -> ds_red R = Some M ->
    (exists R', mdenote (gds_unseal Θ) (gs_unseal Ξ) Γ (me_mem H x) R' /\ ds_red R' = Some M /\ ds_ty R' = ds_ty R) \/
    (exists RH' Θ' p T Φ Ns, mdenote (gds_unseal Θ) (gs_unseal Ξ) Γ H RH' /\
       ds_mod RH' = Some (ds_closed Θ' p T Φ Ns) /\ M = ctx_fn Θ' (apps (a_mem (qname_mod p) x) Ns)).
Proof.
  intros * HH Hm Hr.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
  inversion Hm as [? ? ? ? ? Hq Hu | ? ? ? ? ? ? ? ? ? Hq Hk HMk Hl | | | | ? ? ? R0 R0m Γy E rd Re ? Hm0 Hmd He Hed Hrd
                  | ? ? ? ? ? ? Hq Hk Hl]; subst.
  { cbn in Hr; discriminate. }
  { (* the open frame of a member's module: its type former, its term part
       as it is *)
    left; eexists; split;
      [ eapply mdenote_ind_frame; [ exact Hq | rewrite gs_find_ind_unseal; exact Hk | exact HMk
                             | rewrite gc_loc_unseal, Hl; reflexivity ]
      | split; [ exact Hr | reflexivity ] ]. }
  2: { (* the open frame of a record's module: likewise *)
    left; eexists; split;
      [ eapply mdenote_record_frame; [ exact Hq | rewrite gs_find_record_unseal; exact Hk
                                | rewrite gc_loc_unseal, Hl; reflexivity ]
      | split; [ exact Hr | reflexivity ] ]. }
  destruct (mdenote_unseal _ _ _ _ _ _ HH Hm0) as (R0' & Hm0' & Hd0).
  destruct (dle_mod _ _ _ Hd0 Hmd) as (R0m' & Hmd' & Hdm).
  destruct Hdm as [A0 om om' | Δ Φw Φ | Θc p T Φ Ns | ].
  1,4: exfalso; exact (ds_mod_is_mod _ _ Hmd).
  - (* an open module part: read alike *)
    left.
    cbn in He; destruct (gm_prefix_upto Φ x) as [[| Φ' y E1 | ? ? ?] |] eqn:Hp; try discriminate.
    destruct E1 as [[|] pv A [M0 |] | pv U | | pv Ad Md Ud | ]; try discriminate; injection He as <- <- <-.
    + exists R; split; [| split; [ exact Hr | reflexivity ] ].
      inversion Hed; subst.
      eapply mdenote_mem; [ exact Hm0' | exact Hmd' | cbn; rewrite Hp; reflexivity | constructor | exact Hrd ].
    + exfalso; cbn in Hrd.
      destruct (gm_fill Φ') as [σ |]; cbn in Hrd; [ injection Hrd as <- | discriminate ].
      inversion Hed; subst.
      match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hmm end.
      destruct Re; cbn in Hmm, Hr; try contradiction; discriminate.
    + (* a definition with a module part: its term part as it is, its
         module part, an alias, read unsealed *)
      pose proof (desc_ok_mod _ _ Hg _ _ _ (me_desc_ok _ _ _ _ _ _ HH Hm0) Hmd) as Hok0.
      inversion Hok0 as [| ? ? ? ? HC _ _ _ _ _ _ | |]; subst.
      destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- <- <-] & _).
      pose proof (body_prefix_mod_wf _ _ _ _ _ _ _ _ _ HC Hp eq_refl) as HU.
      inversion Hed; subst.
      match goal with Hu : udenote _ _ _ _ _ _ |- _ =>
        destruct (proj1 (proj2 (mdenote_unseal_all _ _ Hg)) _ _ _ _ Hu) as (Rm' & Hu' & _) end;
        [ rewrite <- app_assoc; apply upre_full, (proj1 (unit_full_of_eq _ _ _ _ _ HU)) |].
      cbn in Hrd; destruct (gm_fill Φ') as [σ |] eqn:Hf; cbn in Hrd; [ injection Hrd as <- | discriminate ].
      eexists; split.
      * eapply mdenote_mem; [ exact Hm0' | exact Hmd' | cbn; rewrite Hp; reflexivity | constructor; exact Hu'
                       | cbn; rewrite Hf; reflexivity ].
      * split; [ exact Hr | reflexivity ].
  - (* a closed module part: its stored entry, unsealed *)
    cbn in He; destruct (gm_prefix_upto Φ x) as [[| Φ0 y E0 | ? ? ?] |] eqn:Hp; try discriminate.
    injection He as <- <- <-.
    destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- <- <-] & _).
    cbn in Hrd; destruct (ds_ats_read Re Ns) as [R1 |] eqn:Hats; cbn in Hrd; [ injection Hrd as <- | discriminate ].
    assert (Hsame : edenote (gds_unseal Θ) (gs_unseal Ξ) (nil ++ Γ) (ds_epath (ds_closed Θc p T (gm_unseal Φ) Ns) y)
                      (ge_read T (ge_unseal E0)) Re ->
                    exists R', mdenote (gds_unseal Θ) (gs_unseal Ξ) Γ (me_mem H y) R' /\ ds_red R' = Some M /\
                      ds_ty R' = ds_ty (ds_up Θc (ds_named Θc Ns (apps (a_mem (qname_mod p) y) Ns) R1))).
    { intros Hed'; eexists; split; [| split; [ exact Hr | reflexivity ] ].
      assert (He' : ds_entry (ds_closed Θc p T (gm_unseal Φ) Ns) y = Some (nil, ge_read T (ge_unseal E0), reader_closed Θc Ns (apps (a_mem (qname_mod p) y) Ns)))
        by (unfold ds_entry; rewrite gm_prefix_upto_unseal, Hp; reflexivity).
      eapply mdenote_mem; [ exact Hm0' | exact Hmd' | exact He' | exact Hed' | cbn; rewrite Hats; reflexivity ]. }
    assert (Hnone : forall Ns0 A1 R2, ds_ats (ds_term A1 None) Ns0 = Some R2 -> exists A2, R2 = ds_term A2 None).
    { induction Ns0 as [| N0 Ns0 IHN]; intros * Ha0; cbn in Ha0; [ injection Ha0 as <-; eauto |].
      destruct (pi_view A1) as [[? ?] |]; [ exact (IHN _ _ Ha0) | discriminate ]. }
    destruct E0 as [b pv A [M0 |] | pv [Δ [sm Φy | E']] | pv pq D ΦD | pv Ad Md Ud | pr Rr Φr ].
    + destruct b.
      * left; apply Hsame; cbn in Hed |- *; inversion Hed; subst; constructor.
      * (* abstract: read as its name *)
        right; exists R0', Θc, p, T, (gm_unseal Φ), Ns; split; [ exact Hm0' | split; [ exact Hmd' |] ].
        cbn in Hed; inversion Hed; subst; cbn [ds_ats_read] in Hats.
        destruct (Hnone _ _ _ Hats) as (A2 & ->).
        destruct (ds_named_term_none Θc Ns (apps (a_mem (qname_mod p) y) Ns) A2) as [(Hn & _) | Hn];
          rewrite Hn in Hr; cbn in Hr; [ discriminate | injection Hr as <-; reflexivity ].
    + (* an axiom: read as its name *)
      right; exists R0', Θc, p, T, (gm_unseal Φ), Ns; split; [ exact Hm0' | split; [ exact Hmd' |] ].
      cbn in Hed; inversion Hed; subst; cbn [ds_ats_read] in Hats.
      assert (Hn0 : (if b then @None exp else None) = None) by (destruct b; reflexivity); rewrite Hn0 in Hats.
      destruct (Hnone _ _ _ Hats) as (A2 & ->).
      destruct (ds_named_term_none Θc Ns (apps (a_mem (qname_mod p) y) Ns) A2) as [(Hn & _) | Hn];
        rewrite Hn in Hr; cbn in Hr; [ discriminate | injection Hr as <-; reflexivity ].
    + exfalso; assert (Hmm : ds_is_mod Re) by (destruct sm; cbn [ge_read] in Hed; inversion Hed; subst; eapply udenote_is_mod; eassumption).
      rewrite ds_ats_read_mod in Hats by exact Hmm.
      pose proof (ds_ats_is_mod _ _ _ Hmm Hats) as Hm1; destruct R1; cbn in Hm1; try contradiction;
        rewrite ds_named_fix in Hr by reflexivity; cbn in Hr; discriminate.
    + exfalso; assert (Hmm : ds_is_mod Re) by (cbn [ge_read] in Hed; inversion Hed; subst; eapply udenote_is_mod; eassumption).
      rewrite ds_ats_read_mod in Hats by exact Hmm.
      pose proof (ds_ats_is_mod _ _ _ Hmm Hats) as Hm1; destruct R1; cbn in Hm1; try contradiction;
        rewrite ds_named_fix in Hr by reflexivity; cbn in Hr; discriminate.
    (* a type former, or a definition with a module part: its term part,
       as it is, and its module part read unsealed *)
    + unseal_dm_read.
    + unseal_dm_read.
    + unseal_dm_read.
Qed.

(** The rank of a group's views does not see seals. *)
Lemma view_rank_ok_unseal : forall Θ Ξ D rk, view_rank_ok Θ Ξ D rk -> view_rank_ok (gds_unseal Θ) (gs_unseal Ξ) D rk.
Proof.
  intros * [Hr0 Hr1]; constructor; [ exact Hr0 |].
  intros * Hk Hh Hl; rewrite ind_lookup_unseal in Hl; eapply Hr1; eassumption.
Qed.

(** Nor does the agreement of its views' maps. *)
Lemma view_maps_coherent_unseal : forall Θ Ξ D, view_maps_coherent Θ Ξ D -> view_maps_coherent (gds_unseal Θ) (gs_unseal Ξ) D.
Proof. unfold view_maps_coherent; intros * Hc * Hk Hh Hl; rewrite ind_lookup_unseal in Hl; eapply Hc; eassumption. Qed.

(** ** Unsealing Preserves Every Judgment *)

Ltac seal_prem := first [ eassumption | solve [ intros; eapply proj1; eauto ] | solve [ eauto ] ].
Ltac unseal_prem :=
  first [ eassumption | solve [ intros; eapply proj2; eauto ]
        | solve [ eauto using gc_resolve_unseal_def, gc_resolve_unseal_transparent, gm_fresh_unseal, frame_fresh_unseal ] ].

Lemma unseal_preserves_wf_all :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ ⍮ Ξ ⍮ Γ /\ ⊢ gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A /\ gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ M : A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A /\ gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ M ≈ M' : A) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' /\ gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ A ⊆ A') /\
  (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U /\ gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ᵤ U) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' /\ gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' /\ gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ᵘ U ≈ U') /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' /\ gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ᵐ H ≈ H') /\
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢ᵉ E -> Θ ⍮ Ξ ⍮ mp ⊢ᵉ E /\ gds_unseal Θ ⍮ gs_unseal Ξ ⍮ mp ⊢ᵉ ge_unseal E) /\
  (forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ -> Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ /\ gds_unseal Θ ⍮ gs_unseal Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ gm_unseal Φ) /\
  (forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> ⊢ᵍ Θ ⍮ Ξ /\ ⊢ᵍ gds_unseal Θ ⍮ gs_unseal Ξ).
Proof.
  apply wf_mut_ind_all; intros; destruct_conjs; split.
  (* the judgment itself *)
  all: try (solve [ econstructor; seal_prem ]).
  (* unsealed *)
  all: cbn.
  all: try rewrite <- (gs_tele_unseal Ξ).
  all: try rewrite <- (ind_lookup_unseal Θ Ξ) in *.
  all: try rewrite <- (record_lookup_unseal Θ Ξ) in *.
  all: try solve [ econstructor; rewrite ?gs_tele_unseal; unseal_prem ].
  (* a member: what it looks up, unsealed *)
  all: try match goal with
    | |- gds_unseal ?Θ ⍮ gs_unseal ?Ξ ⍮ ?Γ ⊢ a_mem ?H ?x : ?A =>
        match goal with Hs : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H, Hm : mdenote Θ Ξ Γ (me_mem H x) ?R, Ht : ds_ty ?R = Some A |- _ =>
          let Hd := fresh "Hd" in
          destruct (mdenote_mem_unseal _ _ _ _ _ _ _ Hs Hm) as (? & ? & Hd);
          eapply wf_mem_desc; [ eassumption | eassumption | rewrite (dle_ty _ _ Hd); exact Ht ] end
    | |- gds_unseal ?Θ ⍮ gs_unseal ?Ξ ⍮ ?Γ ⊢ a_mem ?H ?x ≈ a_mem ?H' ?x : ?A =>
        match goal with Hs : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H', Hm : mdenote Θ Ξ Γ (me_mem H x) ?R, Ht : ds_ty ?R = Some A,
                        Hm2 : mdenote Θ Ξ Γ (me_mem H' x) ?R2, Ht2 : ds_ty ?R2 = Some _ |- _ =>
          let Hd := fresh "Hd" in let Hd2 := fresh "Hd" in
          destruct (mdenote_mem_unseal _ _ _ _ _ _ _ Hs Hm) as (? & ? & Hd);
          destruct (mdenote_mem_unseal _ _ _ _ _ _ _ (wf_modexp_eq_refl_right Hs) Hm2) as (? & ? & Hd2);
          eapply wf_exp_eq_mem_cong; [ eassumption | eassumption | rewrite (dle_ty _ _ Hd); exact Ht
                                     | eassumption | rewrite (dle_ty _ _ Hd2); exact Ht2 | eassumption ] end
    | |- gds_unseal ?Θ ⍮ gs_unseal ?Ξ ⍮ ?Γ ⊢ a_mem ?H ?x ≈ ?M : ?A =>
        match goal with Hs : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H, Hm : mdenote Θ Ξ Γ (me_mem H x) ?R, Ht : ds_ty ?R = Some A,
                        Hr : ds_red ?R = Some M, Hsu : gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ᵐ H ≈ H |- _ =>
          destruct (mem_unseal_red _ _ _ _ _ _ _ Hs Hm Hr) as [(R' & Hm' & Hr' & Ht') | (RH' & Θ' & p & T & Φ & Ns & HmH' & Hmd' & ->)];
          [ eapply wf_exp_eq_mem_delta; [ exact Hsu | exact Hm' | rewrite Ht'; exact Ht | exact Hr' ]
          | let Hd := fresh "Hd" in
            destruct (mdenote_mem_unseal _ _ _ _ _ _ _ Hs Hm) as (? & ? & Hd);
            eapply mem_closed_part; [ exact Hsu | exact HmH' | exact Hmd' | eassumption | rewrite (dle_ty _ _ Hd); exact Ht ] ] end
    end.
  (* a module member: the unit its module part stands for, unsealed *)
  all: try match goal with
    | Hs : ?Θ ⍮ ?Ξ ⍮ ?Γ ⊢ᵐ me_mem ?H ?y ≈ me_mem ?H ?y, Hm : mdenote ?Θ ?Ξ ?Γ (me_mem ?H ?y) ?R, Hmd : ds_mod ?R = Some ?Rm
      |- gds_unseal ?Θ ⍮ gs_unseal ?Ξ ⍮ ?Γ ⊢ᵐ me_mem ?H ?y ≈ ds_unit ?Rm =>
        let Hd := fresh "Hd" in let Hdm := fresh "Hdm" in
        destruct (mdenote_unseal _ _ _ _ _ _ Hs Hm) as (? & ? & Hd);
        destruct (dle_mod _ _ _ Hd Hmd) as (? & ? & Hdm);
        rewrite <- (dle_unit _ _ Hdm); eapply wf_me_delta_sel; eassumption
    end.
  (* a loaded unit or an open frame *)
  all: try match goal with
    | Hu : gc_unit ?Θ ?Ξ (me_unit ?fp) = Some _ |- gds_unseal ?Θ ⍮ gs_unseal ?Ξ ⍮ _ ⊢ᵐ me_unit ?fp ≈ me_unit ?fp =>
        eapply wf_me_unit; [ eassumption | rewrite gc_unit_unseal, Hu; reflexivity ]
    end.
  (* a selection, an application: what they denote unsealed *)
  all: try match goal with
    | HH : ?Θ ⍮ ?Ξ ⍮ ?Γ ⊢ᵐ ?H ≈ ?H', Hm : mdenote ?Θ ?Ξ ?Γ (me_mem ?H ?y) ?R, Ht : ds_mtele ?R = Some _,
      Hm' : mdenote ?Θ ?Ξ ?Γ (me_mem ?H' ?y) ?R', Ht' : ds_mtele ?R' = Some _
      |- gds_unseal ?Θ ⍮ gs_unseal ?Ξ ⍮ ?Γ ⊢ᵐ me_mem ?H ?y ≈ me_mem ?H' ?y =>
        destruct (mdenote_mem_unseal _ _ _ _ _ _ _ HH Hm) as (? & ? & Hd1);
        destruct (mdenote_mem_unseal _ _ _ _ _ _ _ (wf_modexp_eq_refl_right HH) Hm') as (? & ? & Hd2);
        eapply wf_me_mem; [ eassumption | eassumption | exact (dle_mtele _ _ _ Hd1 Ht) | eassumption | exact (dle_mtele _ _ _ Hd2 Ht') ]
    | HH : ?Θ ⍮ ?Ξ ⍮ ?Γ ⊢ᵐ ?H ≈ ?H', Hm : mdenote ?Θ ?Ξ ?Γ ?H ?R, Ht : ds_mtele ?R = Some _,
      Hm' : mdenote ?Θ ?Ξ ?Γ ?H' ?R', Ht' : ds_mtele ?R' = Some _
      |- gds_unseal ?Θ ⍮ gs_unseal ?Ξ ⍮ ?Γ ⊢ᵐ me_app ?H ?N ≈ me_app ?H' ?N' =>
        destruct (mdenote_unseal _ _ _ _ _ _ HH Hm) as (? & ? & Hd1);
        destruct (mdenote_unseal _ _ _ _ _ _ (wf_modexp_eq_refl_right HH) Hm') as (? & ? & Hd2);
        eapply wf_me_app; [ eassumption | eassumption | exact (dle_mtele _ _ _ Hd1 Ht) | eassumption | eassumption | eassumption | eassumption
                          | eassumption | exact (dle_mtele _ _ _ Hd2 Ht') | eassumption | eassumption | eassumption ]
    end.
  (* a body: its expansion, unsealed *)
  all: try match goal with
    | Hx : body_xp ?Θ ?Ξ (?Δ ++ ?Γ) ?Φ ?Φx, Hx' : body_xp ?Θ ?Ξ (?Δ' ++ ?Γ) ?Φ' ?Φx',
      Ho : forall k Ψ H, nth_error (body_opens ?Φ ?Φx) k = Some (Ψ, H) -> ?Θ ⍮ ?Ξ ⍮ Ψ ++ ?Δ ++ ?Γ ⊢ᵐ H ≈ H,
      Ho' : forall k Ψ H, nth_error (body_opens ?Φ' ?Φx') k = Some (Ψ, H) -> ?Θ ⍮ ?Ξ ⍮ Ψ ++ ?Δ' ++ ?Γ ⊢ᵐ H ≈ H
      |- gds_unseal ?Θ ⍮ gs_unseal ?Ξ ⍮ ?Γ ⊢ᵘ gu_open ?Δ ?Φ ≈ gu_open ?Δ' ?Φ' =>
        let Hg := fresh "Hg" in
        assert (Hg : ⊢ᵍ Θ ⍮ Ξ) by (eapply ctx_wf_gctx; eapply presup_ext_eq_ctx; eassumption);
        eapply wf_unit_eq_body;
          [ exact (body_xp_unseal _ _ _ _ _ Hg Hx Ho) | exact (body_xp_unseal _ _ _ _ _ Hg Hx' Ho') | unseal_prem .. ]
    end.
  (* a group: the containers of its views found unsealed alike *)
  all: try match goal with |- gds_unseal _ ⍮ gs_unseal _ ⍮ _ ⊢ᵉ _ => idtac end.
  (* a member with its module: the module, unsealed, as any module is *)
  all: try match goal with
    | |- _ ⍮ _ ⍮ _ ⊢ᵉ ge_ind _ _ _ _ (gm_unseal _) =>
        eapply wf_gentry_ind_body; [ rewrite ?gs_tele_unseal; eassumption | eapply proj2; eauto ]
    | |- _ ⍮ _ ⍮ _ ⊢ᵉ ge_record _ _ _ (gm_unseal _) =>
        eapply wf_gentry_record_body; [ rewrite ?gs_tele_unseal; eassumption | eapply proj2; eauto ]
    end.
  (* the module of a record type, before its first entry *)
  all: try match goal with
    | |- _ ⍮ _ ⍮ _ ⍮ fk_record _ ⍮ _ ⊢ᵍᵐ ⋄ =>
        match goal with
        | Hu : record_params _ = _ ++ gs_tele ?X, HE : gds_unseal _ ⍮ gs_unseal ?X ⍮ _ ⊢ᵉ _,
          HC : ⊢ gds_unseal _ ⍮ gs_unseal ?X ⍮ _ |- _ =>
            rewrite <- (gs_tele_unseal X) in Hu, HC;
            eapply wf_gmod_record_nil; [ assumption | exact HC | exact HE | exact Hu ]
        end
    end.
  (* the module of a member, before its first entry *)
  all: try match goal with
    | |- _ ⍮ _ ⍮ _ ⍮ fk_ind _ _ _ ⍮ _ ⊢ᵍᵐ ⋄ =>
        match goal with
        | Hu : ind_uparams _ = _ ++ gs_tele ?X, HE : gds_unseal _ ⍮ gs_unseal ?X ⍮ _ ⊢ᵉ _,
          HC : ⊢ gds_unseal _ ⍮ gs_unseal ?X ⍮ _ |- _ =>
            rewrite <- (gs_tele_unseal X) in Hu, HC;
            eapply wf_gmod_ind_nil; [ assumption | exact HC | exact HE | exact Hu ]
        end
    end.
  all: first [ eapply wf_gentry_ind_nil; try eassumption
             | match goal with He : gm_entry ?Φ0 (?y0 :: nil) = Some (ge_ind ?pv0 ?pq0 0 ?D0 ?Φm) |- _ =>
                 eapply wf_gentry_ind_mem_nil with (pv0 := pv0) (Φm := gm_unseal Φm);
                 try eassumption; try (rewrite gm_entry_unseal, He; reflexivity) end
             | eapply wf_gentry_def_mod; try eassumption ].
  all: try (match goal with Hrk : view_rank_ok _ _ _ ?rk |- exists rk, view_rank_ok _ _ _ rk =>
              exists rk; exact (view_rank_ok_unseal _ _ _ _ Hrk) end).
  all: try (match goal with Hvc : view_maps_coherent _ _ ?D |- view_maps_coherent _ _ ?D =>
              exact (view_maps_coherent_unseal _ _ _ Hvc) end).
  all: try (match goal with Hq : ind_lookup ?Θ ((?mq, ?Kq, gu_body ?Δ ?Φ0) :: ?Ξ) ?p = Some ?D
                |- ind_lookup (gds_unseal ?Θ) ((?mq, ?Kq, gu_body ?Δ (gm_unseal ?Φ0)) :: gs_unseal ?Ξ) ?p = Some ?D =>
              exact (eq_trans (ind_lookup_unseal Θ ((mq, Kq, gu_body Δ Φ0) :: Ξ) p) Hq) end).
  all: cbn [gs_tele]; rewrite ?gu_params_unseal, ?gs_tele_unseal.
  all: intros; repeat match goal with Hq : ind_lookup (gds_unseal _) (gs_unseal _) _ = Some _ |- _ =>
                       rewrite ind_lookup_unseal in Hq end.
  all: try rewrite !ind_lookup_unseal; try rewrite !ind_mlookup_unseal.
  all: try solve [ first [ eapply proj2; eauto | eauto ] ].
Qed.

Theorem unseal_preserves_wf :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ M : A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ M ≈ M' : A) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ A ⊆ A') /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ᵘ U ≈ U') /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ᵐ H ≈ H') /\
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢ᵉ E -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ mp ⊢ᵉ ge_unseal E) /\
  (forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ gm_unseal Φ) /\
  (forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> ⊢ᵍ gds_unseal Θ ⍮ gs_unseal Ξ).
Proof.
  pose proof unseal_preserves_wf_all as (H1 & H2 & H3 & H4 & _ & H6 & H7 & H8 & H9 & H10 & H11).
  repeat split; intros; [ apply H1 | apply H2 | apply H3 | apply H4 | apply H6 | apply H7 | apply H8 | apply H9 | apply H10 | apply H11 ]; assumption.
Qed.

Corollary unseal_exp : forall Θ Ξ Γ A M,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ M : A.
Proof. apply unseal_preserves_wf. Qed.

Corollary unseal_exp_eq : forall Θ Ξ Γ A M M',
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ M ≈ M' : A.
Proof. apply unseal_preserves_wf. Qed.

Corollary unseal_subtyp : forall Θ Ξ Γ A A',
    Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ A ⊆ A'.
Proof. apply unseal_preserves_wf. Qed.

Corollary unseal_gctx : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> ⊢ᵍ gds_unseal Θ ⍮ gs_unseal Ξ.
Proof. apply unseal_preserves_wf. Qed.

(** ** Global Contexts without Axioms

    Every definition has a body, at every depth of nesting; an alias declares
    no definition of its own.  Transparency is not asked for. *)

(** [ge_no_axioms E]: every definition in [E] has a body; mutually,
    [gm_no_axioms] for module bodies. *)
Fixpoint ge_no_axioms (E : gentry) : Prop :=
  match E with
  | ge_def _ _ _ B => B <> None
  | ge_mod _ (gu_mk _ (md_body sm Φ)) => gm_no_axioms Φ
  | ge_mod _ (gu_mk _ (md_alias _)) => True
  | ge_ind _ _ _ _ Φ => gm_no_axioms Φ
  | ge_def_mod _ _ _ _ => True
  | ge_record _ _ _ Φ => gm_no_axioms Φ
  end
with gm_no_axioms (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ _ E => gm_no_axioms Φ /\ ge_no_axioms E
  | gm_open Φ _ _ => gm_no_axioms Φ
  end.

Definition gds_no_axioms (Θ : gdeps) : Prop :=
  forall fp U, List.In (fp, U) Θ -> gm_no_axioms (gu_mod U).

Definition gs_no_axioms (Ξ : gstack) : Prop :=
  forall mp K U, List.In (mp, K, U) Ξ -> gm_no_axioms (gu_mod U).

Definition gc_no_axioms (Θ : gdeps) (Ξ : gstack) : Prop := gds_no_axioms Θ /\ gs_no_axioms Ξ.

Lemma gm_no_axioms_unseal_transparent : forall Φ, gm_no_axioms Φ -> gm_transparent (gm_unseal Φ).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] HΦ; cbn in *; [ exact I | | exact (IH _ HΦ) ].
  destruct HΦ as [HΦ HE]; split; [ exact (IH _ HΦ) |].
  destruct E as [b pv A [M |] | ? [Δ' [? Φ' | E']] | ? ? ? Φ' | ? ? ? ? | ? ? ?]; cbn in *;
    [ split; congruence | contradiction | exact (IH _ HE) | exact I | exact (IH _ HE) | exact I | exact (IH _ HE) ].
Qed.

Lemma gds_unseal_in : forall Θ fp U',
    List.In (fp, U') (gds_unseal Θ) -> exists U, U' = gu_unseal U /\ List.In (fp, U) Θ.
Proof.
  induction Θ as [| [fq U] Θ IH]; intros * Hin; cbn in Hin; [ contradiction |].
  destruct Hin as [[= <- <-] | Hin]; [ exists U; cbn; auto |].
  destruct (IH _ _ Hin) as (U0 & -> & ?); exists U0; cbn; auto.
Qed.

Lemma gs_unseal_in : forall Ξ mp K U',
    List.In (mp, K, U') (gs_unseal Ξ) -> exists U, U' = gu_unseal U /\ List.In (mp, K, U) Ξ.
Proof.
  induction Ξ as [| [[mq Kq] U] Ξ IH]; intros * Hin; cbn in Hin; [ contradiction |].
  destruct Hin as [[= <- <- <-] | Hin]; [ exists U; cbn; auto |].
  destruct (IH _ _ _ Hin) as (U0 & -> & ?); exists U0; cbn; auto.
Qed.

(** Without axioms, unsealing makes the global context transparent. *)
Theorem gc_no_axioms_unseal_transparent : forall Θ Ξ,
    gc_no_axioms Θ Ξ -> gc_transparent (gds_unseal Θ) (gs_unseal Ξ).
Proof.
  intros * [HΘ HΞ]; split.
  - intros ? ? Hin; destruct (gds_unseal_in _ _ _ Hin) as (U0 & -> & Hin0).
    rewrite gu_mod_unseal; apply gm_no_axioms_unseal_transparent, (HΘ _ _ Hin0).
  - intros ? ? ? Hin; destruct (gs_unseal_in _ _ _ _ Hin) as (U0 & -> & Hin0).
    rewrite gu_mod_unseal; apply gm_no_axioms_unseal_transparent, (HΞ _ _ _ Hin0).
Qed.


(** A resolved definition without a body is an axiom. *)
Lemma gm_no_axioms_resolve : forall Φ ip b pv A B,
    gm_no_axioms Φ -> gm_resolve Φ ip = Some (ge_def b pv A B) -> B <> None.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] ip b pv A0 B0 HΦ H; cbn in H, HΦ; [ discriminate | | eapply IH; eassumption ].
  destruct HΦ as [HΦ HE].
  destruct ip as [| x ip']; [ discriminate |].
  destruct (String.eqb x y); [| eapply IH; eassumption ].
  destruct ip' as [| z ip''], E as [b' pv' A B | ? [Δ' [? Φ' | E']] | ? ? ? ? Φ' | ? ? ? ? | ? ? Φ']; try discriminate;
    first [ injection H as <- <- <- <-; exact HE | eapply IH; [ exact HE | exact H ] ].
Qed.

Lemma gc_no_axioms_resolve : forall Θ Ξ p b pv A B,
    gc_no_axioms Θ Ξ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    B <> None.
Proof.
  intros * [HΘ HΞ] Hr.
  destruct (gc_resolve_inv _ _ _ _ Hr) as [(mp & K & U & ip & Hin & Hm) | (fp & U & Hl & Hm)].
  - exact (gm_no_axioms_resolve _ _ _ _ _ _ (HΞ _ _ _ Hin) Hm).
  - exact (gm_no_axioms_resolve _ _ _ _ _ _ (HΘ _ _ (gds_lookup_in _ _ _ Hl)) Hm).
Qed.

(** ** Running Commands Without Axioms

    A command declares an axiom only as [cc_def] with no body.  A run of
    commands that declare none, loading units that declare none, files no
    axiom, so every global context it reaches has none: the consistency and
    canonicity theorems at [gc_no_axioms] hold of every such program. *)

(** No axiom, at any depth of nesting. *)
Fixpoint cmd_no_axioms (c : ccmd) : Prop :=
  match c with
  | cc_def _ _ _ _ oM => oM <> None
  | cc_mod _ _ _ cs => List.fold_right (fun c P => cmd_no_axioms c /\ P) True cs
  | cc_record _ _ _ _ _ cs => List.fold_right (fun c P => cmd_no_axioms c /\ P) True cs
  | cc_gen c0 => cmd_no_axioms c0
  | _ => True
  end.

Definition cmds_no_axioms (cs : list ccmd) : Prop := List.Forall cmd_no_axioms cs.

Definition unit_no_axioms (u : cunit) : Prop :=
  let '(imps, _, cs) := u in cmds_no_axioms imps /\ cmds_no_axioms cs.

Lemma cmd_no_axioms_mod : forall x pv Δ cs, cmd_no_axioms (cc_mod x pv Δ cs) <-> cmds_no_axioms cs.
Proof.
  intros; cbn; unfold cmds_no_axioms; induction cs as [| c cs IH]; cbn;
    [ split; constructor | rewrite List.Forall_cons_iff, IH; reflexivity ].
Qed.

Lemma cmd_no_axioms_record : forall x pv Δ Srt fs cs, cmd_no_axioms (cc_record x pv Δ Srt fs cs) <-> cmds_no_axioms cs.
Proof.
  intros; cbn; unfold cmds_no_axioms; induction cs as [| c cs IH]; cbn;
    [ split; constructor | rewrite List.Forall_cons_iff, IH; reflexivity ].
Qed.

(** A record's field definitions all have bodies. *)
Lemma record_field_cmds_no_axioms : forall R, cmds_no_axioms (record_field_cmds R).
Proof.
  intros R; unfold record_field_cmds; generalize 0; induction (record_fields R) as [| [f T] fs IH]; intros k;
    cbn; constructor; [ cbn; discriminate | apply IH ].
Qed.

(** The fill keeps a command free of axioms: a definition keeps its body,
    a module and a record their commands. *)
Lemma fill_cmd_no_axioms : forall Θ Ξ B c c', fill_cmd Θ Ξ B c c' -> cmd_no_axioms c -> cmd_no_axioms c'.
Proof.
  intros * H Hc; destruct H; try exact Hc; cbn in *; try exact I.
  match goal with Ho : fill_oexp _ _ _ _ _ _ |- _ => destruct Ho end; [ contradiction | discriminate ].
Qed.

Lemma in_gds_merge : forall Θ Θ' x,
    List.In x (gds_merge Θ Θ') -> List.In x Θ \/ List.In x Θ'.
Proof.
  unfold gds_merge; intros * [Hx | Hx]%List.in_app_or; [ right; exact (proj1 (proj1 (List.filter_In _ _ _) Hx)) | left; exact Hx ].
Qed.

Lemma gds_no_axioms_merge : forall Θ Θ',
    gds_no_axioms Θ -> gds_no_axioms Θ' -> gds_no_axioms (gds_merge Θ Θ').
Proof. intros * H H' fp U [Hin | Hin]%in_gds_merge; eauto. Qed.

Lemma gds_no_axioms_cons : forall fp U Θ,
    gm_no_axioms (gu_mod U) -> gds_no_axioms Θ -> gds_no_axioms ((fp, U) :: Θ).
Proof. intros * HU HΘ fq V [[= <- <-] | Hin]; eauto. Qed.

Lemma gs_no_axioms_nil : gs_no_axioms nil.
Proof. intros ? ? ? []. Qed.

Lemma gds_no_axioms_nil : gds_no_axioms nil.
Proof. intros ? ? []. Qed.

Lemma gs_no_axioms_push : forall mp Δ Ξ, gs_no_axioms Ξ -> gs_no_axioms (gs_push mp Δ Ξ).
Proof. intros * H mq K U [[= <- <- <-] | Hin]; [ exact I | eauto ]. Qed.

Lemma gs_no_axioms_push_ind : forall mp pq k D Δ Ξ, gs_no_axioms Ξ -> gs_no_axioms (gs_push_ind mp pq k D Δ Ξ).
Proof. intros * H mq K U [[= <- <- <-] | Hin]; [ exact I | eauto ]. Qed.

Lemma gs_no_axioms_push_record : forall mp R Δ Ξ, gs_no_axioms Ξ -> gs_no_axioms (gs_push_record mp R Δ Ξ).
Proof. intros * H mq K U [[= <- <- <-] | Hin]; [ exact I | eauto ]. Qed.

Lemma gs_no_axioms_add : forall x E Ξ,
    ge_no_axioms E -> gs_no_axioms Ξ -> gs_no_axioms (gs_add x E Ξ).
Proof.
  intros * HE HΞ mq K U Hin; destruct Ξ as [| [[mp Kp] V] Ξ]; [ destruct Hin |].
  destruct Hin as [[= <- <- <-] | Hin]; [| eauto using in_cons ].
  cbn; split; [ apply (HΞ mp Kp V); left; reflexivity | exact HE ].
Qed.

Lemma gs_no_axioms_head : forall mp K U Ξ, gs_no_axioms ((mp, K, U) :: Ξ) -> gm_no_axioms (gu_mod U).
Proof. intros * H; apply (H mp K U); left; reflexivity. Qed.

Lemma gs_no_axioms_tail : forall f Ξ, gs_no_axioms (f :: Ξ) -> gs_no_axioms Ξ.
Proof. intros * H mp K U Hin; apply (H mp K U); right; exact Hin. Qed.

#[local] Hint Resolve gs_no_axioms_head gs_no_axioms_tail gds_no_axioms_merge gds_no_axioms_cons gs_no_axioms_nil gds_no_axioms_nil
  gs_no_axioms_push gs_no_axioms_push_ind gs_no_axioms_push_record gs_no_axioms_add : mctt.

Lemma gens_run_no_axioms : forall Θ Ξ gs Ξ', gens_run Θ Ξ gs Ξ' -> gs_no_axioms Ξ -> gs_no_axioms Ξ'.
Proof. induction 1; intros HΞ; auto; apply IHgens_run, gs_no_axioms_add; cbn; auto; congruence. Qed.

Lemma mdefs_run_no_axioms : forall Θ b pv ds Ξ Ξ', mdefs_run Θ b pv ds Ξ Ξ' -> gs_no_axioms Ξ -> gs_no_axioms Ξ'.
Proof. induction 1; intros HΞ; [ exact HΞ |]; apply IHmdefs_run, gs_no_axioms_add; cbn; [ discriminate | exact HΞ ]. Qed.

(** The recursor module of a group is a module of definitions. *)
Lemma rec_cmds_no_axioms : forall Θ Ξ R pq D, cmds_no_axioms (rec_cmds Θ Ξ R pq D).
Proof.
  intros; unfold rec_cmds; destruct (raw_decl_rec_field R); [| constructor ].
  constructor; [| constructor ].
  unfold grec_mod_cmd; change (cmd_no_axioms (cc_gen ?c0)) with (cmd_no_axioms c0);
    apply cmd_no_axioms_mod, List.Forall_forall; intros c Hin.
  apply List.in_map_iff in Hin as ([[j Mj] x] & <- & _); cbn; discriminate.
Qed.

(** So are the commands of the module of a declared member: its
    constructors, its recursor and its recursor module. *)
Lemma ind_mod_cmds_no_axioms : forall Θ Ξ R pq D k M, cmds_no_axioms (ind_mod_cmds Θ Ξ R pq D k M).
Proof.
  intros; unfold ind_mod_cmds, ind_rec_cmds, ind_grec_cmds, cmds_no_axioms.
  apply List.Forall_app; split; [| apply List.Forall_app; split ].
  - apply List.Forall_forall; intros c Hin; apply List.in_map_iff in Hin as (cg & <- & _); cbn; discriminate.
  - destruct (ind_has_rec D); [ constructor; [ cbn; discriminate | constructor ] | constructor ].
  - destruct (Nat.eqb k 0 && negb (raw_decl_rec_field R))%bool; [| constructor ].
    constructor; [| constructor ].
    unfold grec_mod_cmd; change (cmd_no_axioms (cc_gen ?c0)) with (cmd_no_axioms c0);
    apply cmd_no_axioms_mod, List.Forall_forall; intros c Hin.
    apply List.in_map_iff in Hin as ([[j Mj] x] & <- & _); cbn; discriminate.
Qed.

Section Run.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  (** Every unit the elaborator gives declares no axiom. *)
  Hypothesis Hload : forall prg u, to_core prg = Some u -> unit_no_axioms u.

  Theorem run_no_axioms :
    (forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       cmd_no_axioms c -> gc_no_axioms Θ Ξ -> gc_no_axioms Θ' Ξ') /\
    (forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       cmds_no_axioms cs -> gc_no_axioms Θ Ξ -> gc_no_axioms Θ' Ξ') /\
    (forall ch u B Rb Θ U, run_unit load_path read to_core ch u B Rb Θ U ->
       unit_no_axioms u -> gds_no_axioms Θ /\ gm_no_axioms (gu_mod U)) /\
    (forall ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ', run_ind_members load_path read to_core ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ' ->
       gc_no_axioms Θ Ξ -> gc_no_axioms Θ' Ξ').
  Proof.
    apply run_mut_ind; intros; unfold gc_no_axioms in *.
    (* a definition has a body *)
    - destruct_all; split; [ assumption | apply gs_no_axioms_add; cbn; auto; congruence ].
    (* an axiom is not among the commands *)
    - cbn in *; contradiction.
    (* a module's body is the frame its commands ended on *)
    - rewrite cmd_no_axioms_mod in *; destruct_all.
      match goal with IH : cmds_no_axioms _ -> _ |- _ =>
        destruct (IH ltac:(assumption) ltac:(split; auto with mctt)) as [HΘ HΞ] end.
      split; [ exact HΘ | apply gs_no_axioms_add; cbn; eauto with mctt ].
    - destruct_all; split; [ assumption | apply gs_no_axioms_add; cbn; auto ].
    - assumption.
    (* a load: the loaded unit is the elaborator's *)
    - destruct_all.
      match goal with IH : unit_no_axioms _ -> _ |- _ => destruct (IH ltac:(eapply Hload; eassumption)) end.
      split; eauto with mctt.
    (* an open declares what it generates *)
    - destruct_all; split; [ assumption | eapply gens_run_no_axioms; eassumption ].
    (* a declaration files its members, with no axiom in their modules:
       the definitions it generates there; then its recursor module, of
       definitions *)
    - destruct_all.
      match goal with IHm : _ /\ _ -> _ /\ _ |- _ => destruct (IHm ltac:(split; assumption)) end.
      match goal with IH : cmds_no_axioms _ -> _ |- _ => apply (IH (rec_cmds_no_axioms _ _ _ _ _)); split; assumption end.
    (* a mutual definition files definitions *)
    - destruct_all; split; [ assumption | eapply mdefs_run_no_axioms; eassumption ].
    (* a builtin binding files nothing *)
    - assumption.
    (* an inductive or a record alias declares no axiom *)
    - destruct_all; split; [ assumption | apply gs_no_axioms_add; cbn; auto ].
    - destruct_all; split; [ assumption | apply gs_no_axioms_add; cbn; auto ].
    (* a record's module is its field definitions, then its with-area *)
    - rewrite cmd_no_axioms_record in *; destruct_all.
      match goal with IH : cmds_no_axioms (record_field_cmds _) -> _ |- _ =>
        destruct (IH (record_field_cmds_no_axioms _) ltac:(split; auto with mctt)) as [HΘ1 HΞ1] end.
      match goal with IH : cmds_no_axioms ?cs -> _, Hcs : cmds_no_axioms ?cs |- _ =>
        destruct (IH Hcs ltac:(split; assumption)) as [HΘ HΞ] end.
      split; [ exact HΘ | apply gs_no_axioms_add; cbn; eauto with mctt ].
    - assumption.
    - assumption.
    (* a generated definition has a body *)
    - destruct_all; split; [ assumption | apply gs_no_axioms_add; cbn; auto; congruence ].
    (* a generated module: as a module *)
    - change (cmd_no_axioms (cc_gen ?c)) with (cmd_no_axioms c) in *.
      rewrite cmd_no_axioms_mod in *; destruct_all.
      match goal with IH : cmds_no_axioms _ -> _ |- _ =>
        destruct (IH ltac:(assumption) ltac:(split; auto with mctt)) as [HΘ HΞ] end.
      split; [ exact HΘ | apply gs_no_axioms_add; cbn; eauto with mctt ].
    - assumption.
    (* a command runs filled, which keeps it free of axioms *)
    - match goal with
      | Ha : fill_cmd _ _ _ _ _, Hc : cmds_no_axioms (_ :: _) |- _ =>
          inversion Hc; subst; pose proof (fill_cmd_no_axioms _ _ _ _ _ Ha ltac:(assumption))
      end; eauto.
    (* a unit: its loads from nothing, then its body in its own frame *)
    - cbn in *; destruct_all.
      match goal with IH1 : cmds_no_axioms ?is -> _ -> _ /\ gs_no_axioms nil, H1 : cmds_no_axioms ?is |- _ =>
        destruct (IH1 H1 ltac:(split; auto with mctt)) end.
      match goal with IH2 : cmds_no_axioms ?cs -> _ -> _ /\ gs_no_axioms (_ :: nil), H2 : cmds_no_axioms ?cs |- _ =>
        destruct (IH2 H2 ltac:(split; auto with mctt)) end.
      split; eauto with mctt.
    (* no member left *)
    - assumption.
    (* a member: its module's commands, of definitions, then the member
       filed with the body they end with *)
    - destruct_all.
      match goal with IH : cmds_no_axioms (ind_mod_cmds _ _ _ _ _ _ _) -> _ |- _ =>
        destruct (IH (ind_mod_cmds_no_axioms _ _ _ _ _ _ _) ltac:(split; auto with mctt)) as [HΘ1 HΞ1] end.
      match goal with IH : _ /\ gs_no_axioms (gs_add _ _ _) -> _ |- _ => apply IH end.
      split; [ exact HΘ1 | apply gs_no_axioms_add; cbn; eauto with mctt ].
  Qed.

  Corollary run_unit_no_axioms : forall ch u B Rb Θ U,
      run_unit load_path read to_core ch u B Rb Θ U -> unit_no_axioms u -> gds_no_axioms Θ /\ gm_no_axioms (gu_mod U).
  Proof. exact (proj1 (proj2 (proj2 run_no_axioms))). Qed.

  (** Every state a unit runs through, from nothing, has no axioms. *)
  Corollary run_cmds_no_axioms : forall ch B Rb cs B' Rb' Θ Ξ,
      nil ⍮ nil ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ ⍮ Ξ ⍮ B' ⍮ Rb' -> cmds_no_axioms cs -> gc_no_axioms Θ Ξ.
  Proof. intros * H Hc; eapply (proj1 (proj2 run_no_axioms)); [ exact H | exact Hc | split; auto with mctt ]. Qed.

  (** What a program files, filed with it. *)
  Corollary prog_sem_no_axioms : forall prg B Θ U,
      prog_sem load_path read to_core prg B Θ U -> gc_no_axioms ((prog_path prg, U) :: Θ) nil.
  Proof.
    intros * [u Rb Ht Hu]; destruct (run_unit_no_axioms _ _ _ _ _ _ Hu (Hload _ _ Ht)).
    split; auto with mctt.
  Qed.
End Run.
