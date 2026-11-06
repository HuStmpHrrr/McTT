(** * An Accepted Record Declaration Runs

    For a record declaration checked with an empty module where it is
    declared, the field definitions it generates always run, so its frame
    opens ([run_cmd_record_runs]): each field's projection of the module's
    value is of the field's type at the module's parameters and the
    projections before it, a type of the field's kind. *)

From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import SystemOpt.
From Mctt.Core.Syntactic.System Require Import Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing Syntax.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Paths LookupSound.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
From Mctt.Core.Syntactic.System.Inductives Require Import IndRuns.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** The Field Definitions *)

(** The field definitions of the fields [fs] of [R] from the field [k] on:
    each of the field's kind, at its type, the projection of the
    module's value. *)
Fixpoint record_fields_defs (R : record_decl) (k : nat) (fs : list (string * typ)) : list gen_def :=
  match fs with
  | nil => nil
  | (f, T) :: fs' => mk_gen_def f (record_field_kind R k) (record_field_ty R k T) (a_proj f (a_var 0)) :: record_fields_defs R (S k) fs'
  end.

(** The field commands are those of the field definitions. *)
Lemma record_fields_cmds_defs : forall R fs k,
    List.map ci_core (record_fields_cmds R k fs) = List.map (fun d => ci_core (gen_def_cmd true false d)) (record_fields_defs R k fs).
Proof. intros R; induction fs as [| [f T] fs IH]; intros k; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

(** The field definitions are named by the fields. *)
Lemma record_fields_defs_names : forall R fs k, List.map gen_def_name (record_fields_defs R k fs) = List.map fst fs.
Proof. intros R; induction fs as [| [f T] fs IH]; intros k; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

(** Each field definition is that of a field, at its position. *)
Lemma record_fields_defs_in : forall R fs k d, In d (record_fields_defs R k fs) ->
    exists j f T, List.nth_error fs j = Some (f, T) /\
      d = mk_gen_def f (record_field_kind R (k + j)) (record_field_ty R (k + j) T) (a_proj f (a_var 0)).
Proof.
  intros R; induction fs as [| [f T] fs IH]; intros k d Hin; cbn in Hin; [ contradiction |].
  destruct Hin as [<- | Hin].
  - exists 0, f, T; rewrite Nat.add_0_r; split; reflexivity.
  - destruct (IH _ _ Hin) as (j & f' & T' & Hj & ->); exists (S j), f', T'; rewrite Nat.add_succ_r; split; [ exact Hj | reflexivity ].
Qed.

(** ** A Field Definition Is Typed *)

(** The value of a record's module, its last parameter, is of the record
    type at the other parameters. *)
Lemma record_self_wk : forall p R,
    (record_self p R)[wk_shiftn 1]ʷ = apps_exp (a_record p) (vars_from 1 (List.length (record_params R))).
Proof. intros; unfold record_self; rewrite apps_wk, vars_from_shift; reflexivity. Qed.

(** The projection of a record's module's value at its field [k] is of
    the field's type there, where the record is found; that type is of
    the field's kind's sort, at a large universe
    ([record_proj_cong_at]). *)
Lemma record_field_def_typed : forall Θ Ξ p R k f T,
    record_typed Θ Ξ R -> record_lookup Θ Ξ p = Some R -> List.nth_error (record_fields R) k = Some (f, T) ->
    (exists n : nat, Θ ⍮ Ξ ⍮ record_mod_tele p R ⊢ record_field_ty R k T : abs_kind_sort (record_field_kind R k) Typeω@n) /\
    Θ ⍮ Ξ ⍮ record_mod_tele p R ⊢ a_proj f (a_var 0) : record_field_ty R k T.
Proof.
  intros * HR Hl Hk; pose proof HR as [Ha Hmv Hs Hnd Hf Hrl Hfk].
  pose proof (record_mod_tele_wf _ _ _ _ HR Hl) as HΓ.
  pose proof (wf_ctx_scoped _ _ _ (presup_is_univ_ctx Hs)) as HsP.
  pose proof (record_typed_former _ _ _ _ _ HR Hl HΓ) as Hrt.
  assert (H0 : Θ ⍮ Ξ ⍮ record_mod_tele p R ⊢ a_var 0 : apps_exp (a_record p) (vars_from 1 (List.length (record_params R)))).
  { rewrite <- record_self_wk; unfold record_mod_tele.
    replace ((record_self p R)[wk_shiftn 1]ʷ) with ((record_self p R)[↑]ʷ) by (apply exp_wk_wk_eq; intros x; cbn; lia).
    eapply wf_vlookup; [ exact HΓ | constructor ]. }
  assert (Hargs : forall j N A, List.nth_error (vars_from 1 (List.length (record_params R))) j = Some N ->
                    List.nth_error (tele_insts (record_params R) Id (vars_from 1 (List.length (record_params R)))) j = Some A ->
                    Θ ⍮ Ξ ⍮ record_mod_tele p R ⊢ N : A)
    by exact (wf_vars_tele _ _ (ce_ass (sort_exp_kind (record_sort R)) (record_self p R) :: nil) _ Ha HsP (params_mvc _ Hmv) HΓ).
  destruct (record_sort_large _ _ _ _ _ _ Hrt Hl (length_vars_from _ _) Hargs) as [n HS].
  destruct (record_proj_cong_at _ _ _ (a_var 0) (a_var 0) p R _ n k f T
              ltac:(apply wf_exp_eq_refl; exact H0) Hrt Hl (length_vars_from _ _) Hargs HS Hk) as [HT Hp].
  unfold record_field_ty; split; [ exists n |]; gen_presups; eassumption.
Qed.

Section RecordRuns.
  Variable load_path : path -> option string.
  Variable read : string -> option Cst.prog.
  Variable to_core : Cst.prog -> option surface_compilation_unit.

  (** ** An Accepted Declaration Runs

      A record checked with an empty module where it is declared, its name
      fresh: its module's frame opens, its field definitions running in
      it. *)
  Theorem run_cmd_record_runs : forall ch B Rb Θ Ξ x pv Δ Srt fs,
      ⊢ᵍ Θ ⍮ Ξ -> gs_fresh x Ξ ->
      Θ ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_record pv (ind_qname Ξ x) (record_at Ξ Δ Srt fs) ⋄ ->
      exists Φ,
        Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ core_cmd_record_open x pv Δ Srt fs ⇝
          Θ ⍮ (ind_qname Ξ x, fk_record (record_at Ξ Δ Srt fs),
               gu_body (ce_ass (sort_exp_kind Srt) (record_self (ind_qname Ξ x) (record_at Ξ Δ Srt fs)) :: Δ) Φ) :: Ξ ⍮ B ⍮ Rb.
  Proof.
    intros * Hg Hfr HE.
    set (R := record_at Ξ Δ Srt fs) in *; set (mp := ind_qname Ξ x) in *.
    destruct (record_nil_entry_params _ _ _ _ _ _ _ _ HE) as [Htel HΔ].
    destruct (record_nil_entry_params_evaluated _ _ _ _ _ _ _ _ HE) as [lp HPr].
    destruct (params_evaluated_sorts _ _ _ _ _ HPr) as (ps & Hps & HTs).
    pose proof (proj1 wf_record_typed_all _ _ _ _ HE _ _ _ _ eq_refl) as HRt.
    pose proof (typed_field_kinds _ _ _ HRt) as Hfk.
    destruct Ξ as [| [[mq Kq] Uq] Ξ0]; [ contradiction |].
    assert (Hff : frame_fresh Θ ((mq, Kq, Uq) :: Ξ0) mp) by (cbn; exists x; split; [ reflexivity | exact Hfr ]).
    assert (Hpush : ⊢ᵍ Θ ⍮ gs_push_record mp R Δ ((mq, Kq, Uq) :: Ξ0))
      by (apply wf_gstack_cons; [ exact Hg | eapply wf_gmod_record_nil; [ exact Htel | exact HΔ | exact Hps | exact HTs | exact HE | reflexivity ]
                                | exact Hff ]).
    set (Δm := ce_ass (sort_exp_kind (record_sort R)) (record_self mp R) :: Δ).
    destruct (gen_defs_run load_path read to_core ch B Rb Θ mp (fk_record R) Δm
                ((mq, Kq, Uq) :: Ξ0) true false (record_fields_defs R 0 (record_fields R)) ⋄ Hpush)
      as (Φ' & Hr & _ & _ & _).
    - rewrite record_fields_defs_names; exact (typed_nodup _ _ _ HRt).
    - apply Forall_forall; intros; intros [].
    - apply Forall_forall; intros d Hd.
      destruct (record_fields_defs_in _ _ _ _ Hd) as (j & f & T & Hj & ->); cbn [gen_def_kind].
      intros E; pose proof (Hfk (0 + j)) as Hk; rewrite E in Hk; inversion Hk.
    - intros Φ2 Hg2 Hs2; apply Forall_forall; intros d Hd.
      destruct (record_fields_defs_in _ _ _ _ Hd) as (j & f & T & Hj & ->); cbn [gen_def_kind gen_def_type gen_def_body].
      assert (Hl2 : record_lookup Θ ((mp, fk_record R, gu_body Δm Φ2) :: (mq, Kq, Uq) :: Ξ0) mp = Some R)
        by (unfold record_lookup; rewrite gs_find_record_own; reflexivity).
      assert (HRt2 : record_typed Θ ((mp, fk_record R, gu_body Δm Φ2) :: (mq, Kq, Uq) :: Ξ0) R).
      { refine (gctx_embedding_preserves_record_typed _ _ _ _ _ _ HRt).
        constructor; [ exact Hg2 | eapply gc_sub_trans; [ apply gc_sub_push; exact Hff | exact Hs2 ] ]. }
      pose proof (record_field_def_typed _ _ _ _ _ _ _ HRt2 Hl2 Hj) as Ht.
      unfold record_mod_tele in Ht; cbn [List.app]; cbn [Nat.add].
      replace (record_params R) with (Δ ++ gs_tele ((mq, Kq, Uq) :: Ξ0)) in Ht by reflexivity; exact Ht.
    - exists Φ'; eapply run_cmd_record_open; [ exact Hfr | exact HE |].
      unfold record_field_cmds; rewrite record_fields_cmds_defs; exact Hr.
  Qed.
End RecordRuns.
