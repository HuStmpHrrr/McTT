(** * Records under Substitution

    A record's declaration is closed ([record_closed]): what a well-formed
    global context files is ([gctx_closed_record]).  So its type former's
    type does not move, the instances of its parameters' telescope move
    with the parameters, and a field's type at parameters and earlier
    field values moves with them. *)

From Stdlib Require Import Lia List PeanoNat.
From Stdlib Require String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System.Inductives Require Export Syntax.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** A closed record declaration. *)
Record record_closed (R : record_decl) : Prop := mk_record_closed
  { (** The parameters are a closed telescope *)
    closed_params : ctx_scoped 0 (record_params R)
    (** The sort is over the parameters *)
  ; closed_sort : exp_scoped (List.length (record_params R)) (record_sort R)
    (** Each field's type is over the fields before it and the
        parameters *)
  ; closed_fields : forall k f T, List.nth_error (record_fields R) k = Some (f, T) ->
      exp_scoped (k + List.length (record_params R)) T }.

(** A position of a list is below its length. *)
Lemma nth_error_lt_length : forall {A} (l : list A) k a, List.nth_error l k = Some a -> k < List.length l.
Proof. intros * H; apply List.nth_error_Some; congruence. Qed.

(** The closed context of the fields over the parameters gives each field
    its scope. *)
Lemma record_closed_of_fctx : forall R,
    ctx_scoped 0 (record_fctx R (List.length (record_fields R)) ++ record_params R) ->
    exp_scoped (List.length (record_params R)) (record_sort R) ->
    record_closed R.
Proof.
  intros R HC HS; apply ctx_scoped_app_iff in HC as [HF HΔ].
  constructor; [ exact HΔ | exact HS |].
  intros k f T Hk.
  assert (Hlt : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hk).
  unfold record_fctx in HF; rewrite List.firstn_all in HF.
  rewrite <- (List.firstn_skipn (S k) (record_fields R)), (firstn_succ_nth _ _ _ Hk) in HF.
  rewrite !List.map_app, !List.rev_app_distr in HF; cbn [List.map List.rev List.app] in HF.
  apply ctx_scoped_app in HF as [_ HF]; cbn in HF; destruct HF as [HT _].
  rewrite List.length_rev, List.length_map, List.length_firstn in HT.
  replace (Nat.min k (List.length (record_fields R))) with k in HT by lia; exact HT.
Qed.

(** What a closed global context files as a record is closed. *)
Lemma gctx_closed_record : forall Θ Ξ p R, gctx_closed Θ Ξ -> record_lookup Θ Ξ p = Some R -> record_closed R.
Proof.
  intros * Hc Hl; destruct (gctx_closed_record_decl _ _ _ _ Hc Hl) as [HC HS]; exact (record_closed_of_fctx _ HC HS).
Qed.

(** In a well-formed context, a filed record is closed. *)
Lemma wf_record_closed : forall Θ Ξ Γ p R, ⊢ Θ ⍮ Ξ ⍮ Γ -> record_lookup Θ Ξ p = Some R -> record_closed R.
Proof. intros * HΓ Hl; eapply gctx_closed_record; [ eapply wf_gctx_closed; exact HΓ | exact Hl ]. Qed.

(** ** Substitution *)

Lemma record_ty_scoped : forall R, record_closed R -> exp_scoped 0 (record_ty R).
Proof.
  intros R HR; unfold record_ty; apply ctx_pi_scoped; [ exact (closed_params _ HR) | rewrite Nat.add_0_r; exact (closed_sort _ HR) ].
Qed.

Lemma record_ty_sub : forall R σ, record_closed R -> (record_ty R)[σ] = record_ty R.
Proof. intros; apply exp_closed_sub, record_ty_scoped; assumption. Qed.

Lemma record_ty_wk : forall R φ, record_closed R -> (record_ty R)[φ]ʷ = record_ty R.
Proof. intros; apply exp_closed_wk, record_ty_scoped; assumption. Qed.

(** [tele_insts_sub] for any telescope: the instances stop at the first
    entry that is not an assumption, on both sides. *)
Lemma tele_insts_sub_gen : forall Δ k σ σ' τ Ms,
    ctx_scoped k Δ ->
    (forall x, x < k -> sentry_sub (σ x) τ = σ' x) ->
    List.map (fun T => T[τ]) (tele_insts Δ σ Ms) = tele_insts Δ σ' (List.map (fun M => M[τ]) Ms).
Proof.
  induction Δ as [| e Δ IH] using List.rev_ind; intros * HΔ Hσ; [ reflexivity |].
  apply ctx_scoped_app in HΔ as [HΔ [He _]]; cbn in He, HΔ.
  destruct e as [A | A N | U | A N U];
    [| unfold tele_insts; rewrite !List.rev_app_distr; destruct Ms; reflexivity
     | unfold tele_insts; rewrite !List.rev_app_distr; destruct Ms; reflexivity
     | unfold tele_insts; rewrite !List.rev_app_distr; destruct Ms; reflexivity ].
  destruct Ms as [| M Ms]; [ unfold tele_insts; rewrite List.rev_app_distr; reflexivity |].
  cbn [List.map]; rewrite !tele_insts_snoc; cbn [List.map]; f_equal.
  - rewrite exp_sub_sub; eapply exp_scoped_sub_agree; [ exact He |]; intros; cbn; apply Hσ; assumption.
  - apply (IH (S k)); [ assumption |].
    intros [| x] Hx; cbn; [ reflexivity | apply Hσ; lia ].
Qed.

(** A substitution moves the instances of the parameters' telescope with
    the parameters. *)
Lemma record_params_insts_sub : forall R Ns τ, record_closed R ->
    List.map (fun T => T[τ]) (tele_insts (record_params R) Id Ns) = tele_insts (record_params R) Id (List.map (fun N => N[τ]) Ns).
Proof.
  intros * HR; apply (tele_insts_sub_gen _ 0); [ exact (closed_params _ HR) | lia ].
Qed.

(** A field's type at parameters and earlier fields moves with them. *)
Lemma record_field_sub : forall R k f U Ns L τ, record_closed R -> List.nth_error (record_fields R) k = Some (f, U) ->
    List.length Ns = List.length (record_params R) -> List.length L = k ->
    U[sb_of_list Id (Ns ++ L)][τ] = U[sb_of_list Id (List.map (fun N => N[τ]) Ns ++ List.map (fun N => N[τ]) L)].
Proof.
  intros * HR Hk HN HL.
  rewrite exp_sub_sb_of_list, List.map_app.
  f_equal; eapply exp_scoped_sub_id; [ exact (closed_fields _ HR _ _ _ Hk) |].
  intros x Hx; apply sb_qn_lt; rewrite List.length_app; lia.
Qed.

(** The sort at parameters moves with them. *)
Lemma record_sort_sub : forall R Ns τ, record_closed R -> List.length Ns = List.length (record_params R) ->
    (record_sort R)[sb_of_list Id Ns][τ] = (record_sort R)[sb_of_list Id (List.map (fun N => N[τ]) Ns)].
Proof.
  intros * HR HN.
  rewrite exp_sub_sb_of_list.
  f_equal; eapply exp_scoped_sub_id; [ exact (closed_sort _ HR) |].
  intros x Hx; apply sb_qn_lt; lia.
Qed.

Lemma record_pre_sub : forall R k M τ, List.map (fun N => N[τ]) (record_pre R k M) = record_pre R k M[τ].
Proof. intros; unfold record_pre; rewrite List.map_map; reflexivity. Qed.

Lemma record_eta_fields_sub : forall R M τ,
    List.map (fun f => (fst f, (snd f)[τ])) (record_eta_fields R M) = record_eta_fields R M[τ].
Proof. intros; unfold record_eta_fields; rewrite List.map_map; reflexivity. Qed.

Lemma tuple_values_sub : forall (fs : list (String.string * exp)) k τ,
    List.map (fun N => N[τ]) (List.firstn k (List.map snd fs))
    = List.firstn k (List.map snd (List.map (fun f => (fst f, (snd f)[τ])) fs)).
Proof. intros; rewrite !List.map_map, List.firstn_map, List.firstn_map, List.map_map; reflexivity. Qed.

Lemma tuple_names_sub : forall (fs : list (String.string * exp)) τ,
    List.map fst (List.map (fun f => (fst f, (snd f)[τ])) fs) = List.map fst fs.
Proof. intros; rewrite List.map_map; reflexivity. Qed.
