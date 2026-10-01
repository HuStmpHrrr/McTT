(** * Globals: Resolution against Raw Evaluation

    [gc_lookup] hands back a global's entry transformed by the module
    substitutions of the frames it is read out of; evaluation resolves the
    raw entry and builds those frames as module environments.  The chain
    lemma ([chain]) follows a member chain and relates the two: the
    transformed entry is the raw one under a leaf replacement [θ] whose
    configuration relates the top level, with the frames' arguments as
    λ-variables, to the module environment the raw entry is evaluated in. *)

From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System GlobalInduction.
From Mctt.Core.Semantic Require Import Evaluation Readback Simulation Bridge.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Raw scoping of a module's entries *)

Fixpoint ge_rscoped (cs : list nat) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B => exp_scoped 0 cs A /\ opt_scoped 0 cs B
  | ge_mod Δ Φ => ctx_scoped 0 cs Δ /\ gm_rscoped (List.length Δ :: cs) Φ
  end
with gm_rscoped (cs : list nat) (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ' _ E => gm_rscoped cs Φ' /\ ge_rscoped cs E
  end.

Lemma gs_cs_cons : forall U Ξ, gs_cs (U :: Ξ) = List.length (gu_params U) :: gs_cs Ξ.
Proof. reflexivity. Qed.

Lemma wf_rscoped :
  (forall Θ Ξ E, Θ ⍮ Ξ ⊢e E -> ge_rscoped (gs_cs Ξ) E) /\
  (forall Θ Ξ Δ Φ, Θ ⍮ Ξ ⍮ Δ ⊢m Φ -> gm_rscoped (List.length Δ :: gs_cs Ξ) Φ).
Proof.
  destruct wf_scoped as (_ & He & _ & _ & _ & Hm & _).
  apply global_wf_mut_ind; intros; cbn; repeat split; auto.
  all: try match goal with
    | H : _ ⍮ _ ⍮ ⋅ ⊢ ?M : _ |- exp_scoped _ _ ?M => apply (He _ _ _ _ _ H)
    | H : _ ⍮ _ ⍮ ⋅ ⊢ _ : ?A |- exp_scoped _ _ ?A => apply (He _ _ _ _ _ H)
    | H : _ ⍮ _ ⍮ _ ⊢m _ |- ctx_scoped _ _ _ => apply (Hm _ _ _ _ H)
    end.
Qed.

Lemma gm_rscoped_find : forall Φ cs x E, gm_rscoped cs Φ -> gm_find Φ x = Some E -> ge_rscoped cs E.
Proof.
  induction Φ as [| Φ IH y E']; intros * HΦ Hf; cbn in *; [ discriminate |].
  destruct HΦ as [HΦ HE]; destruct (String.eqb x y); [ injection Hf as <-; exact HE | eauto ].
Qed.

Lemma stack_rscoped : forall Θ Ξ, wf_gstack Θ Ξ -> forall n U,
    List.nth_error Ξ n = Some U ->
    gm_rscoped (List.length (gu_params U) :: gs_cs (List.skipn (S n) Ξ)) (gu_mod U).
Proof.
  destruct wf_rscoped as [_ Hm].
  induction 1; intros [| n] U0 Hn; cbn in *; try discriminate.
  - injection Hn as <-.
    match goal with H : _ ⍮ _ ⊢u _ |- _ => apply wf_gunit_mod in H; exact (Hm _ _ _ _ H) end.
  - eauto.
Qed.

Lemma deps_rscoped : forall Θ, wf_gdeps Θ -> forall fp U,
    gds_lookup Θ fp = Some U -> gm_rscoped (List.length (gu_params U) :: nil) (gu_mod U).
Proof.
  destruct wf_rscoped as [_ Hm].
  induction 1 as [| Θ d HΘ IH Hd]; intros * Hl; [ discriminate |].
  unfold gds_lookup in Hl; cbn in Hl.
  apply gd_lookup_app_inv in Hl as [Hl | Hl]; [| eapply IH, Hl ].
  apply gd_lookup_in in Hl.
  pose proof (wf_gdep_unit _ _ Hd _ _ Hl) as HU.
  apply wf_gunit_mod in HU; exact (Hm _ _ _ _ HU).
Qed.

(** ** Raw lookup *)

Lemma gm_walk_app : forall cs1 cs2 Δ Φ,
    gm_walk Δ Φ (cs1 ++ cs2) =
    match gm_walk Δ Φ cs1 with Some (Δ', Φ') => gm_walk Δ' Φ' cs2 | None => None end.
Proof.
  induction cs1 as [| x cs1 IH]; intros; cbn; [ reflexivity |].
  destruct (gm_find Φ x) as [[? ? ? ? | Δ' Φ'] |]; auto.
Qed.

Lemma frame_at_in : forall Θ Ξ a Δ Φ x Δ' Φ',
    frame_at Θ Ξ a = Some (Δ, Φ) -> gm_find Φ x = Some (ge_mod Δ' Φ') ->
    frame_at Θ Ξ (path_in a x) = Some (Δ', Φ').
Proof.
  intros * Ha Hx; unfold frame_at, path_in in *; cbn.
  destruct (p_qual a) as [fp | j].
  - destruct (gds_lookup Θ fp); [| discriminate ]; rewrite gm_walk_app, Ha; cbn; rewrite Hx; reflexivity.
  - destruct (List.nth_error Ξ j); [| discriminate ]; rewrite gm_walk_app, Ha; cbn; rewrite Hx; reflexivity.
Qed.

Lemma gm_find_old : forall Φ z E' x ip Δ E,
    gm_canon (Φ ⊳ z ↦ E') -> Φ ∋ x :: ip ⇒ Δ ⍮ E -> gm_find (Φ ⊳ z ↦ E') x = gm_find Φ x.
Proof.
  intros * [_ [Hfr _]] Hl; cbn.
  pose proof (gm_fresh_no_lookup _ _ _ _ _ Hfr Hl) as Hne; cbn in Hne.
  destruct (String.eqb_spec x z) as [-> |]; [ congruence | reflexivity ].
Qed.

(** ** The pending frame machine *)

Section Machine.
  Variables (Θ : gdeps) (Ξ : gstack).

  #[local] Notation "'⟦' M '⟧' κ '⍮' ρ '↘' r" := (eval_exp Θ Ξ κ M ρ r)
    (at level 70, M at level 69, κ at level 69, ρ at level 69, r at level 69).

  Definition ent_res κ ip cs v := exists r, eval_ent Θ Ξ κ ip r /\ apps Θ Ξ r cs v.

  (** Feeding a frame its remaining arguments and entering it. *)
  Lemma pend_feed : forall κ a c ip rest pre cs v,
      List.length pre + List.length rest = c ->
      ent_res (me_frame a (List.rev rest ++ pre) κ) ip cs v ->
      exists r, eval_pend Θ Ξ κ a c pre ip r /\ apps Θ Ξ r (rest ++ cs) v.
  Proof.
    induction rest as [| d rest IH]; intros * Hl (r & Hr & Hv); cbn in *.
    - exists r; split; [ apply eval_pend_enter; [ lia | exact Hr ] | exact Hv ].
    - destruct (IH (d :: pre) cs v ltac:(cbn; lia)) as (r' & Hr' & Hv').
      { exists r; split; [| exact Hv ]. rewrite <- List.app_assoc in Hr; exact Hr. }
      exists (d_gfn κ a c pre ip); split; [ apply eval_pend_wait; lia |].
      econstructor; [ apply eval_app_gfn; exact Hr' | exact Hv' ].
  Qed.

  (** Feeding it fewer: still pending. *)
  Lemma pend_partial : forall κ a c ip rest pre,
      List.length pre + List.length rest < c ->
      exists r v, eval_pend Θ Ξ κ a c pre ip r /\ apps Θ Ξ r rest v.
  Proof.
    induction rest as [| d rest IH]; intros * Hl; cbn in *.
    - do 2 eexists; split; [ apply eval_pend_wait; lia | constructor ].
    - destruct (IH (d :: pre) ltac:(cbn; lia)) as (r' & v' & Hr' & Hv').
      do 2 eexists; split; [ apply eval_pend_wait; lia |].
      econstructor; [ apply eval_app_gfn; exact Hr' | exact Hv' ].
  Qed.

  (** And back: a frame fed all its arguments was entered with them. *)
  Lemma pend_entered : forall κ a c ip rest pre r v,
      List.length pre + List.length rest = c ->
      eval_pend Θ Ξ κ a c pre ip r -> apps Θ Ξ r rest v ->
      eval_ent Θ Ξ (me_frame a (List.rev rest ++ pre) κ) ip v.
  Proof.
    induction rest as [| d rest IH]; intros * Hl Hr Hv; cbn in *.
    - inversion Hv; subst; inversion Hr; subst; [ lia | assumption ].
    - inversion Hr; subst; [| lia ].
      inversion Hv as [| ? ? ? fc ? Hfc Hrest]; subst.
      inversion Hfc; subst.
      rewrite <- List.app_assoc; cbn.
      eapply IH; [| eassumption | eassumption ]; cbn; lia.
  Qed.

  (** [app_vars] evaluated: the head applied to the values of its variables,
      the outermost first. *)
  Fixpoint vals (ρ : env) (d c : nat) : list domain :=
    match c with
    | 0 => nil
    | S c' => ρ (d + c') :: vals ρ d c'
    end.

  Lemma eval_app_vars : forall c M d κ ρ v,
      ⟦ app_vars M d c ⟧ κ ⍮ ρ ↘ v -> exists m, ⟦ M ⟧ κ ⍮ ρ ↘ m /\ apps Θ Ξ m (vals ρ d c) v.
  Proof.
    induction c as [| c IH]; intros * H; cbn in *.
    - eexists; split; [ exact H | constructor ].
    - destruct (IH _ _ _ _ _ H) as (m & Hm & Hv).
      inversion Hm; subst.
      match goal with H : ⟦ #_ ⟧ _ ⍮ _ ↘ _ |- _ => inversion H; subst end.
      eexists; split; [ eassumption | econstructor; eassumption ].
  Qed.

  Lemma env_var_app_l : forall (l1 l2 : env) i, i < List.length l1 -> (l1 ++ l2) i = l1 i.
  Proof. intros; rewrite !env_var_nth, List.app_nth1 by assumption; reflexivity. Qed.

  Lemma env_var_app_r : forall (l1 l2 : env) i, (l1 ++ l2) (List.length l1 + i) = l2 i.
  Proof. intros; rewrite !env_var_nth, List.app_nth2 by lia; f_equal; lia. Qed.

  Lemma vals_ext : forall (ρ ρ' : env) d c, (forall i, i < c -> ρ (d + i) = ρ' (d + i)) -> vals ρ d c = vals ρ' d c.
  Proof.
    induction c as [| c IH]; intros H; cbn; [ reflexivity |].
    rewrite (H c ltac:(lia)), IH; [ reflexivity |]; intros; apply H; lia.
  Qed.

  Lemma vals_shift : forall (ρ1 ρ2 : env) c, vals (ρ1 ++ ρ2) (List.length ρ1) c = vals ρ2 0 c.
  Proof.
    induction c as [| c IH]; cbn; [ reflexivity |]; rewrite env_var_app_r, IH; reflexivity.
  Qed.

  Lemma vals_rev : forall (ρ : env), vals ρ 0 (List.length ρ) = List.rev ρ.
  Proof.
    induction ρ as [| x ρ IH] using List.rev_ind; [ reflexivity |].
    rewrite List.length_app, List.rev_app_distr; cbn.
    replace (List.length ρ + 1) with (S (List.length ρ)) by lia; cbn.
    f_equal.
    - rewrite env_var_nth, List.app_nth2, Nat.sub_diag by lia; reflexivity.
    - rewrite <- IH; apply vals_ext; intros; cbn; apply env_var_app_l; lia.
  Qed.

  Lemma vals_app : forall (ρ1 ρ2 : env) c, List.length ρ2 = c ->
      vals (ρ1 ++ ρ2) (List.length ρ1) c = List.rev ρ2.
  Proof. intros * <-; rewrite vals_shift; apply vals_rev. Qed.
End Machine.

(** ** Module substitutions as leaf replacements *)

Definition ts_ms (μ : msub) : tsub := ts_mk a_var (ms_param μ) (ms_glob μ).

Lemma exp_tsub_ms : forall M μ, M[μ]ᵐ = exp_tsub (ts_ms μ) M.
Proof.
  intros; rewrite exp_tsub_of_msub; apply exp_tsub_ext; repeat split; intros; cbn;
    rewrite ?exp_sub_id; reflexivity.
Qed.

Lemma opt_tsub_ms : forall (B : option exp) μ, B[μ]ᵐ = option_map (exp_tsub (ts_ms μ)) B.
Proof. intros [M |] μ; cbn; [ rewrite exp_tsub_ms |]; reflexivity. Qed.

Lemma bfree_app_vars : forall c M d, bfree M -> bfree (app_vars M d c).
Proof. induction c; intros; cbn; auto. apply IHc; cbn; auto. Qed.

Lemma exp_ok_PQ : forall M n (P P' : lpath -> Prop) (Q Q' : path -> Prop),
    exp_ok n P Q M -> (forall lp, P lp -> P' lp) -> (forall p, Q p -> Q' p) -> exp_ok n P' Q' M.
Proof. induction M; intros; cbn in *; intuition eauto. Qed.

Lemma exp_ok_app_vars : forall c M n P Q d, exp_ok n P Q M -> d + c <= n -> exp_ok n P Q (app_vars M d c).
Proof. induction c; intros; cbn; auto. apply IHc; cbn; [ split; [ auto | lia ] | lia ]. Qed.

Lemma exp_scoped_ok_cs : forall M n cs, exp_scoped n cs M -> exp_ok n (param_ok cs) (path_ok cs) M.
Proof. induction M; intros; cbn in *; intuition eauto. Qed.

Lemma path_open_in_rel0 : forall x ip, (p_rel 0 ip)[p_rel 0 (x :: nil)]ᵖ = p_rel 0 (x :: ip).
Proof. reflexivity. Qed.

Lemma path_open_abs_rel0 : forall fp ip, (p_rel 0 ip)[p_abs fp nil]ᵖ = p_abs fp ip.
Proof. reflexivity. Qed.

(** The images of leaves in scope one frame in are in scope outside it. *)
Lemma exp_ok_close_in : forall M x c d cs,
    bfree M -> cs <> nil ->
    exp_ok d (param_ok (c :: cs)) (path_ok (c :: cs)) M ->
    exp_ok (d + c) (param_ok cs) (path_ok cs) (exp_tsub (ts_ms (ms_close (p_rel 0 (x :: nil)) c d)) M).
Proof.
  induction M; intros * Hb Hcs Hok; cbn in *; try contradiction; try solve [ intuition eauto ].
  - lia.
  - destruct l as [[| m] k]; cbn in *; destruct Hok as (c' & Hc' & Hk); cbn in *.
    + injection Hc' as <-; lia.
    + exists c'; split; assumption.
  - destruct p as [[fp | [| m]] ip]; cbn in *; auto.
    + apply exp_ok_app_vars; [ cbn; destruct cs; [ congruence | cbn; lia ] | lia ].
    + rewrite Nat.sub_0_r; lia.
Qed.

Section Steps.
  Variables (Θ : gdeps) (Ξ : gstack).

  #[local] Notation "'⟦' M '⟧' κ '⍮' ρ '↘' r" := (eval_exp Θ Ξ κ M ρ r)
    (at level 70, M at level 69, κ at level 69, ρ at level 69, r at level 69).

  Lemma eval_param_menv : forall κ κ' m m' k ρ ρ' v,
      me_drop m κ = me_drop m' κ' -> ⟦ $[m, k] ⟧ κ ⍮ ρ ↘ v -> ⟦ $[m', k] ⟧ κ' ⍮ ρ' ↘ v.
  Proof.
    intros * Hd H; inversion H; subst; cbn [lp_mod lp_param] in *.
    - eapply eval_exp_param_closed; cbn; rewrite <- Hd; eassumption.
    - eapply eval_exp_param_open; [ cbn; rewrite <- Hd; eassumption | eassumption | eassumption ].
  Qed.

  Lemma eval_glob_rel_menv : forall κ κ' m m' ip ρ ρ' v,
      me_drop m κ = me_drop m' κ' -> ⟦ a_glob (p_rel m ip) ⟧ κ ⍮ ρ ↘ v -> ⟦ a_glob (p_rel m' ip) ⟧ κ' ⍮ ρ' ↘ v.
  Proof. intros * Hd H; inversion H; subst; constructor; rewrite <- Hd; assumption. Qed.

  Lemma eval_glob_abs_menv : forall κ κ' fp ip ρ ρ' v,
      ⟦ a_glob (p_abs fp ip) ⟧ κ ⍮ ρ ↘ v -> ⟦ a_glob (p_abs fp ip) ⟧ κ' ⍮ ρ' ↘ v.
  Proof. intros * H; inversion H; subst; econstructor; eassumption. Qed.

  Lemma eval_var_env : forall κ κ' x (ρ ρ' : env) v,
      ρ x = ρ' x -> ⟦ #x ⟧ κ ⍮ ρ ↘ v -> ⟦ #x ⟧ κ' ⍮ ρ' ↘ v.
  Proof. intros * Hx H; inversion H; subst; rewrite Hx; apply eval_exp_var. Qed.

  Lemma cfg_eq_id : forall n P Q κ ρ, cfg_eq Θ Ξ ts_id n P Q κ ρ κ ρ.
  Proof. intros; constructor; cbn; auto. Qed.

  (** Reading a member of the open frame [n] from the top level. *)
  Lemma cfg_eq_shift : forall n d P Q ρ,
      cfg_eq Θ Ξ (ts_ms (↑ₘ n)) d P Q me_top ρ (me_base n) ρ.
  Proof.
    intros; constructor; cbn; auto.
    - intros * _ H; eapply eval_var_env; [ reflexivity | exact H ].
    - intros [m k] v _ H; eapply eval_param_menv; [| exact H ].
      cbn; rewrite !me_drop_base; f_equal; lia.
    - intros [[fp | m] ip] v _ H; cbn [ts_glob ts_ms ms_glob ms_shift] in H.
      + eapply eval_glob_abs_menv; exact H.
      + rewrite path_open_rel_nil in H; eapply eval_glob_rel_menv; [| exact H ].
        rewrite !me_drop_base; f_equal; lia.
  Qed.

  (** Closing the nested module [x] of the innermost frame. *)
  Lemma cfg_eq_close_in : forall κ Δa Φ x Δ' Φ' (args ρin : env),
      frame_at Θ Ξ (me_addr κ) = Some (Δa, Φ) -> gm_find Φ x = Some (ge_mod Δ' Φ') ->
      List.length args = List.length Δ' ->
      cfg_eq Θ Ξ (ts_ms (ms_close (p_rel 0 (x :: nil)) (List.length Δ') (List.length ρin)))
        (List.length ρin) (fun lp => lp_mod lp = 0 -> lp_param lp < List.length Δ') (fun _ => True)
        κ (ρin ++ args) (me_frame (path_in (me_addr κ) x) args κ) ρin.
  Proof.
    intros * Ha Hx Hl; constructor; cbn.
    - auto.
    - intros [[| m] k]; cbn; auto.
    - intros [[fp | [| m]] ip]; cbn; try apply bfree_app_vars; cbn; auto.
    - intros * Hlt H; inversion H; subst; rewrite env_var_app_l by assumption; apply eval_exp_var.
    - intros [[| m] k] v Hk H; cbn in *.
      + inversion H; subst.
        rewrite env_var_app_r; eapply eval_exp_param_closed with (lp := lp_mk 0 k); reflexivity.
      + eapply eval_param_menv; [ | exact H ]; reflexivity.
    - intros [[fp | [| m]] ip] v _ H; cbn in H.
      + eapply eval_glob_abs_menv; exact H.
      + apply eval_app_vars in H as (m & Hm & Hv).
        rewrite vals_app in Hv by assumption.
        inversion Hm; subst; cbn in *.
        match goal with H : eval_ent _ _ _ (_ :: _) _ |- _ => inversion H; subst end;
          match goal with H : frame_at _ _ _ = Some _ |- _ => rewrite Ha in H; injection H as <- <- end;
          match goal with H : gm_find _ _ = _ |- _ => rewrite Hx in H; try discriminate H; injection H as <- <- end.
        constructor; cbn.
        assert (He : eval_ent Θ Ξ (me_frame (path_in (me_addr κ) x) (List.rev (List.rev args) ++ nil) κ) ip v)
          by (eapply pend_entered; [ | eassumption | exact Hv ]; rewrite List.length_rev; cbn; lia).
        rewrite List.rev_involutive, List.app_nil_r in He; exact He.
      + rewrite Nat.sub_0_r in H; eapply eval_glob_rel_menv; [ | exact H ]; reflexivity.
  Qed.

  (** Closing a filed unit read from the top level. *)
  Lemma cfg_eq_close_abs : forall fp U (args ρin : env),
      gds_lookup Θ fp = Some U -> List.length args = List.length (gu_params U) ->
      cfg_eq Θ Ξ (ts_ms (ms_close (p_abs fp nil) (List.length (gu_params U)) (List.length ρin)))
        (List.length ρin) (fun lp => lp_mod lp = 0 -> lp_param lp < List.length (gu_params U))
        (fun p => match p_qual p with qu_rel m => m = 0 | qu_abs _ => True end)
        me_top (ρin ++ args) (me_frame (p_abs fp nil) args (me_base 0)) ρin.
  Proof.
    intros * Hf Hl; constructor; cbn.
    - auto.
    - intros [[| m] k]; cbn; auto.
    - intros [[fq | [| m]] ip]; cbn; try apply bfree_app_vars; cbn; auto.
    - intros * Hlt H; inversion H; subst; rewrite env_var_app_l by assumption; apply eval_exp_var.
    - intros [[| m] k] v Hk H; cbn in *.
      + inversion H; subst.
        rewrite env_var_app_r; eapply eval_exp_param_closed with (lp := lp_mk 0 k); reflexivity.
      + eapply eval_param_menv; [ | exact H ]; reflexivity.
    - intros [[fq | [| m]] ip] v Hq H; cbn in H, Hq; try lia.
      + eapply eval_glob_abs_menv; exact H.
      + apply eval_app_vars in H as (m & Hm & Hv).
        rewrite vals_app in Hv by assumption.
        inversion Hm; subst.
        match goal with H : gds_lookup _ _ = _ |- _ => rewrite Hf in H; injection H as <- end.
        constructor; cbn.
        assert (He : eval_ent Θ Ξ (me_frame (p_abs fp nil) (List.rev (List.rev args) ++ nil) (me_base 0)) ip v)
          by (eapply pend_entered; [ | eassumption | exact Hv ]; rewrite List.length_rev; cbn; lia).
        rewrite List.rev_involutive, List.app_nil_r in He; exact He.
  Qed.
End Steps.

Lemma bfree_close : forall mp c d,
    (forall lp, bfree (ts_param (ts_ms (ms_close mp c d)) lp)) /\
    (forall p, bfree (ts_glob (ts_ms (ms_close mp c d)) p)) /\
    (forall x, bfree (ts_var (ts_ms (ms_close mp c d)) x)).
Proof.
  intros; repeat split; cbn; auto.
  - intros [[| m] k]; cbn; auto.
  - intros [[fp | [| m]] ip]; cbn; try apply bfree_app_vars; cbn; auto.
Qed.

Lemma opt_tsub_comp : forall (B : option exp) θ2 θ1,
    option_map (exp_tsub θ1) (option_map (exp_tsub θ2) B) = option_map (exp_tsub (ts_comp θ2 θ1)) B.
Proof. intros [M |] *; cbn; [ rewrite exp_tsub_comp |]; reflexivity. Qed.

Section Chain.
  Variables (Θ : gdeps) (Ξ : gstack).

  Definition chain_stmt (Φ : gmod) (ip : list string) (Δ : ctx) (b pv : bool) (A : typ) (B : option exp) : Prop :=
    forall cs, cs <> nil ->
    (forall x ip' E, ip = x :: ip' -> gm_find Φ x = Some E -> ge_rscoped cs E) ->
    exists y Ar Br θ csf,
      A = exp_tsub θ Ar /\ B = option_map (exp_tsub θ) Br /\
      exp_scoped 0 csf Ar /\ opt_scoped 0 csf Br /\ csf <> nil /\
      (forall lp, bfree (ts_param θ lp)) /\ (forall p, bfree (ts_glob θ p)) /\
      (forall x, bfree (ts_var θ x)) /\
      (forall lp, param_ok csf lp -> exp_ok (List.length Δ) (param_ok cs) (path_ok cs) (ts_param θ lp)) /\
      (forall p, path_ok csf p -> exp_ok (List.length Δ) (param_ok cs) (path_ok cs) (ts_glob θ p)) /\
      forall κ Δa Φfull,
        frame_at Θ Ξ (me_addr κ) = Some (Δa, Φfull) ->
        (forall x ip', ip = x :: ip' -> gm_find Φfull x = gm_find Φ x) ->
        (forall cs', List.length cs' < List.length Δ -> exists v, ent_res Θ Ξ κ ip cs' v) /\
        forall args, List.length args = List.length Δ ->
          exists κf Δf Φf, frame_at Θ Ξ (me_addr κf) = Some (Δf, Φf) /\
            gm_find Φf y = Some (ge_def b pv Ar Br) /\
            (forall v, eval_ent Θ Ξ κf (y :: nil) v -> ent_res Θ Ξ κ ip args v) /\
            cfg_eq Θ Ξ θ 0 (param_ok csf) (path_ok csf) κ (List.rev args) κf nil.

  Lemma chain : forall Φ ip Δ E, Φ ∋ ip ⇒ Δ ⍮ E -> gm_canon Φ ->
      forall b pv A B, E = ge_def b pv A B -> chain_stmt Φ ip Δ b pv A B.
  Proof.
    induction 1 as [? ? ? ? ? ? | ? ? ? ? ? ? ? ? ? ? Hin IH | ? ? ? ? ? ? Hold IH];
      intros Hcanon b0 pv0 A0 B0 HE; unfold chain_stmt; intros cs Hcs Hsc.
    - (* the member itself *)
      injection HE as <- <- <- <-.
      destruct (Hsc x nil _ eq_refl ltac:(cbn; rewrite String.eqb_refl; reflexivity)) as [HsA HsB].
      exists x, A, B, ts_id, cs.
      split; [ symmetry; apply exp_tsub_id |].
      split; [ destruct B; cbn; [ rewrite exp_tsub_id |]; reflexivity |].
      do 3 (split; [ assumption |]).
      do 3 (split; [ intros; cbn; exact I |]).
      split; [ intros; cbn; assumption |].
      split; [ intros; cbn; assumption |].
      + intros * Hf Hhd; split; [ intros; cbn in *; lia |].
        intros [| ? ?] Hl; cbn in Hl; [| lia ].
        exists κ, Δa, Φfull; split; [ assumption |].
        split; [ rewrite (Hhd x nil eq_refl); cbn; rewrite String.eqb_refl; reflexivity |].
        split; [ intros v Hv; exists v; split; [ exact Hv | constructor ] | apply cfg_eq_id ].
    - (* through a nested module *)
      injection HE as <- <- <- <-; cbn in Hcanon; destruct Hcanon as (_ & _ & Hc').
      destruct (Hsc x ip _ eq_refl ltac:(cbn; rewrite String.eqb_refl; reflexivity)) as [HsΔ' HsΦ'].
      pose proof (gm_lookup_nonnil _ _ _ _ Hin) as Hip.
      destruct (IH Hc' _ _ _ _ eq_refl (List.length Δ' :: cs) ltac:(congruence)
                  ltac:(intros; eapply gm_rscoped_find; eassumption))
        as (y & Ar & Br & θin & csf & -> & -> & HsA & HsB & Hcsf & Hbp & Hbg & Hbv & Hip1 & Hip2 & Hdyn).
      set (ν := ts_ms (ms_close (p_rel 0 (x :: nil)) (List.length Δ') (List.length Δ))).
      destruct (bfree_close (p_rel 0 (x :: nil)) (List.length Δ') (List.length Δ)) as (Hνp & Hνg & Hνv).
      exists y, Ar, Br, (ts_comp θin ν), csf.
      split; [ rewrite exp_tsub_ms, exp_tsub_comp; reflexivity |].
      split; [ rewrite opt_tsub_ms, opt_tsub_comp; reflexivity |].
      do 3 (split; [ assumption |]).
      do 3 (split; [ intros; cbn; apply bfree_tsub; auto |]).
      split; [ intros lp Hlp; cbn; rewrite List.length_app, ctx_msub_length;
               apply exp_ok_close_in; auto |].
      split; [ intros p Hp; cbn; rewrite List.length_app, ctx_msub_length;
               apply exp_ok_close_in; auto |].
      + intros κ Δa Φfull Hf Hhd.
        pose proof (Hhd x ip eq_refl) as Hx; cbn in Hx; rewrite String.eqb_refl in Hx.
        assert (Hfx : forall argsx, frame_at Θ Ξ (me_addr (me_frame (path_in (me_addr κ) x) argsx κ)) = Some (Δ', Φ'))
          by (intros; cbn; eapply frame_at_in; eassumption).
        rewrite List.length_app, ctx_msub_length.
        split.
        * intros cs' Hl.
          destruct (Nat.lt_ge_cases (List.length cs') (List.length Δ')) as [Hlt | Hge].
          -- destruct (pend_partial Θ Ξ κ (path_in (me_addr κ) x) (List.length Δ') ip cs' nil ltac:(cbn; lia))
               as (r & v & Hr & Hv).
             exists v, r; split; [ eapply eval_ent_mod; eassumption | exact Hv ].
          -- destruct (proj1 (Hdyn _ _ _ (Hfx (List.rev (List.firstn (List.length Δ') cs')))
                                 ltac:(intros; reflexivity)) (List.skipn (List.length Δ') cs')
                                 ltac:(rewrite List.length_skipn; lia)) as (v & Hv).
             destruct (pend_feed Θ Ξ κ (path_in (me_addr κ) x) (List.length Δ') ip
                         (List.firstn (List.length Δ') cs') nil (List.skipn (List.length Δ') cs') v
                         ltac:(rewrite List.length_firstn; cbn; lia)
                         ltac:(rewrite List.app_nil_r; exact Hv)) as (r & Hr & Hv').
             rewrite List.firstn_skipn in Hv'.
             exists v, r; split; [ eapply eval_ent_mod; eassumption | exact Hv' ].
        * intros args Hl.
          set (argsx := List.firstn (List.length Δ') args).
          set (argsin := List.skipn (List.length Δ') args).
          assert (Hlx : List.length argsx = List.length Δ') by (unfold argsx; rewrite List.length_firstn; lia).
          assert (Hlin : List.length argsin = List.length Δ) by (unfold argsin; rewrite List.length_skipn; lia).
          destruct (proj2 (Hdyn _ _ _ (Hfx (List.rev argsx)) ltac:(intros; reflexivity)) argsin Hlin)
            as (κf & Δf & Φf & Hff & Hfy & Hres & Hcf).
          exists κf, Δf, Φf; split; [ assumption |]; split; [ assumption |]; split.
          -- intros v Hv.
             destruct (Hres v Hv) as (r0 & Hr0 & Hv0).
             destruct (pend_feed Θ Ξ κ (path_in (me_addr κ) x) (List.length Δ') ip argsx nil argsin v
                         ltac:(cbn; lia) ltac:(rewrite List.app_nil_r; exists r0; split; assumption))
               as (r & Hr & Hv').
             unfold argsx, argsin in Hv'; rewrite List.firstn_skipn in Hv'.
             exists r; split; [ eapply eval_ent_mod; eassumption | exact Hv' ].
          -- assert (Hargs : List.rev args = List.rev argsin ++ List.rev argsx)
               by (unfold argsx, argsin; rewrite <- List.rev_app_distr, List.firstn_skipn; reflexivity).
             rewrite Hargs.
             pose proof (cfg_eq_close_in Θ Ξ κ Δa Φfull x Δ' Φ' (List.rev argsx) (List.rev argsin) Hf Hx
                           ltac:(rewrite List.length_rev; assumption)) as Hν.
             rewrite List.length_rev, Hlin in Hν.
             eapply cfg_eq_comp; [ exact Hν | exact Hcf | intros; lia | |].
             ++ intros lp Hlp; eapply exp_ok_PQ; [ apply Hip1; exact Hlp | | auto ].
                intros [m k] (c' & Hc0 & Hk) Hm; cbn in Hm, Hc0 |- *; rewrite Hm in Hc0; injection Hc0 as <-; exact Hk.
             ++ intros p Hp; eapply exp_ok_PQ; [ apply Hip2; exact Hp | | auto ].
                intros [m k] (c' & Hc0 & Hk) Hm; cbn in Hm, Hc0 |- *; rewrite Hm in Hc0; injection Hc0 as <-; exact Hk.
    - (* an older entry *)
      subst E; pose proof Hcanon as Hcanon0; cbn in Hcanon; destruct Hcanon as (Hc & _ & _).
      assert (Hold' : forall x ip', ip = x :: ip' -> gm_find (gm_ext Φ y E') x = gm_find Φ x)
        by (intros * ->; eapply gm_find_old; [ exact Hcanon0 | exact Hold ]).
      unfold chain_stmt in IH.
      destruct (IH Hc _ _ _ _ eq_refl cs Hcs ltac:(intros * Heq Hf; eapply Hsc; [ exact Heq | rewrite (Hold' _ _ Heq); eassumption ]))
        as (y0 & Ar & Br & θ & csf & HA & HB & HsA & HsB & Hcsf & Hbp & Hbg & Hbv & Hip1 & Hip2 & Hdyn).
      exists y0, Ar, Br, θ, csf; do 10 (split; [ assumption |]).
      intros κ Δa Φfull Hf Hhd; apply (Hdyn _ _ _ Hf).
      intros * Heq; rewrite (Hhd _ _ Heq), (Hold' _ _ Heq); reflexivity.
  Qed.
End Chain.

Section Top.
  Variables (Θ : gdeps) (Ξ : gstack).

  #[local] Notation "'⟦' M '⟧' κ '⍮' ρ '↘' r" := (eval_exp Θ Ξ κ M ρ r)
    (at level 70, M at level 69, κ at level 69, ρ at level 69, r at level 69).

  (** A global applied to arguments, from the top level. *)
  Definition gres (p : path) (cs : list domain) (v : domain) : Prop :=
    exists g, (forall ρ, ⟦ a_glob p ⟧ me_top ⍮ ρ ↘ g) /\ apps Θ Ξ g cs v.

  Lemma gres_det : forall p cs v g,
      gres p cs v -> (forall ρ, ⟦ a_glob p ⟧ me_top ⍮ ρ ↘ g) -> apps Θ Ξ g cs v.
  Proof.
    intros * (g' & Hg' & Hv) Hg.
    pose proof (functional_eval_exp _ _ _ _ _ (Hg' nil) (Hg nil)) as <-; exact Hv.
  Qed.

  Lemma top_chain : forall p Δ b pv A B,
      ⊢g Θ ⍮ Ξ ->
      Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
      exists y Ar Br θ csf,
        A = exp_tsub θ Ar /\ B = option_map (exp_tsub θ) Br /\
        exp_scoped 0 csf Ar /\ opt_scoped 0 csf Br /\
        (forall cs', List.length cs' < List.length Δ -> exists v, gres p cs' v) /\
        forall args, List.length args = List.length Δ ->
          exists κf Δf Φf, frame_at Θ Ξ (me_addr κf) = Some (Δf, Φf) /\
            gm_find Φf y = Some (ge_def b pv Ar Br) /\
            (forall v, eval_ent Θ Ξ κf (y :: nil) v -> gres p args v) /\
            cfg_eq Θ Ξ θ 0 (param_ok csf) (path_ok csf) me_top (List.rev args) κf nil.
  Proof.
    intros * Hg Hl.
    pose proof (wf_gctx_stack _ _ Hg) as HΞ.
    pose proof (wf_gstack_canon _ _ HΞ) as Hcs.
    pose proof (wf_gdeps_canon _ (wf_gstack_deps _ _ HΞ)) as Hcd.
    inversion Hl as [n U ip Δ0 ? ? A0 B0 Hn Hm | fp U ip Δ0 ? ? A0 B0 Hf Hm]; subst.
    - (* a member of an open frame *)
      pose proof (stack_rscoped _ _ HΞ _ _ Hn) as Hrs.
      destruct (chain Θ Ξ _ _ _ _ Hm (gs_canon_nth _ _ _ Hcs Hn) _ _ _ _ eq_refl
                  (List.length (gu_params U) :: gs_cs (List.skipn (S n) Ξ)) ltac:(congruence)
                  ltac:(intros; eapply gm_rscoped_find; eassumption))
        as (y & Ar & Br & θ & csf & -> & -> & HsA & HsB & Hcsf & Hbp & Hbg & Hbv & Hip1 & Hip2 & Hdyn).
      assert (Hfr : frame_at Θ Ξ (me_addr (me_base n)) = Some (gu_params U, gu_mod U))
        by (unfold frame_at; cbn; rewrite Hn; reflexivity).
      destruct (Hdyn _ _ _ Hfr ltac:(intros; reflexivity)) as [Hpart Hmain].
      assert (Hglob : forall r ρ, eval_ent Θ Ξ (me_base n) ip r -> ⟦ a_glob (p_rel n ip) ⟧ me_top ⍮ ρ ↘ r)
        by (intros * Hr; constructor; rewrite me_drop_base, Nat.add_0_r; exact Hr).
      exists y, Ar, Br, (ts_comp θ (ts_ms (↑ₘ n))), csf.
      split; [ rewrite exp_tsub_ms, exp_tsub_comp; reflexivity |].
      split; [ rewrite opt_tsub_ms, opt_tsub_comp; reflexivity |].
      do 2 (split; [ assumption |]).
      rewrite ctx_msub_length.
      split.
      + intros cs' Hl'; destruct (Hpart _ Hl') as (v & r & Hr & Hv).
        exists v, r; split; [ intros; apply Hglob, Hr | exact Hv ].
      + intros args Hla; destruct (Hmain _ Hla) as (κf & Δf & Φf & Hff & Hfy & Hres & Hcf).
        exists κf, Δf, Φf; split; [ assumption |]; split; [ assumption |]; split.
        * intros v Hv; destruct (Hres _ Hv) as (r & Hr & Hv').
          exists r; split; [ intros; apply Hglob, Hr | exact Hv' ].
        * eapply cfg_eq_comp; [ apply (cfg_eq_shift _ _ _ (List.length Δ0) (param_ok (List.length (gu_params U) :: gs_cs (List.skipn (S n) Ξ))) (path_ok (List.length (gu_params U) :: gs_cs (List.skipn (S n) Ξ)))) | exact Hcf | intros; lia | exact Hip1 | exact Hip2 ].
    - (* a member of a filed unit *)
      pose proof (deps_rscoped _ (wf_gstack_deps _ _ HΞ) _ _ Hf) as Hrs.
      set (c := List.length (gu_params U)).
      destruct (chain Θ Ξ _ _ _ _ Hm (gds_lookup_canon _ _ _ Hcd Hf) _ _ _ _ eq_refl
                  (c :: nil) ltac:(congruence)
                  ltac:(intros; eapply gm_rscoped_find; eassumption))
        as (y & Ar & Br & θ & csf & -> & -> & HsA & HsB & Hcsf & Hbp & Hbg & Hbv & Hip1 & Hip2 & Hdyn).
      assert (Hfr : forall argsT, frame_at Θ Ξ (me_addr (me_frame (p_abs fp nil) argsT (me_base 0))) = Some (gu_params U, gu_mod U))
        by (intros; unfold frame_at; cbn; rewrite Hf; reflexivity).
      assert (Hglob : forall r ρ, eval_pend Θ Ξ (me_base 0) (p_abs fp nil) c nil ip r ->
                        ⟦ a_glob (p_abs fp ip) ⟧ me_top ⍮ ρ ↘ r)
        by (intros * Hr; econstructor; eassumption).
      exists y, Ar, Br, (ts_comp θ (ts_ms (ms_close (p_abs fp nil) c (List.length Δ0)))), csf.
      split; [ rewrite exp_tsub_ms, exp_tsub_comp; reflexivity |].
      split; [ rewrite opt_tsub_ms, opt_tsub_comp; reflexivity |].
      do 2 (split; [ assumption |]).
      rewrite List.length_app, ctx_msub_length; fold c.
      split.
      + intros cs' Hl'.
        destruct (Nat.lt_ge_cases (List.length cs') c) as [Hlt | Hge].
        * destruct (pend_partial Θ Ξ (me_base 0) (p_abs fp nil) c ip cs' nil ltac:(cbn; lia)) as (r & v & Hr & Hv).
          exists v, r; split; [ intros; apply Hglob, Hr | exact Hv ].
        * destruct (proj1 (Hdyn _ _ _ (Hfr (List.rev (List.firstn c cs'))) ltac:(intros; reflexivity))
                       (List.skipn c cs') ltac:(rewrite List.length_skipn; lia)) as (v & Hv).
          destruct (pend_feed Θ Ξ (me_base 0) (p_abs fp nil) c ip (List.firstn c cs') nil (List.skipn c cs') v
                      ltac:(rewrite List.length_firstn; cbn; lia)
                      ltac:(rewrite List.app_nil_r; exact Hv)) as (r & Hr & Hv').
          rewrite List.firstn_skipn in Hv'.
          exists v, r; split; [ intros; apply Hglob, Hr | exact Hv' ].
      + intros args Hla.
        set (argsT := List.firstn c args).
        set (argsin := List.skipn c args).
        assert (HlT : List.length argsT = c) by (unfold argsT; rewrite List.length_firstn; lia).
        assert (Hlin : List.length argsin = List.length Δ0) by (unfold argsin; rewrite List.length_skipn; lia).
        destruct (proj2 (Hdyn _ _ _ (Hfr (List.rev argsT)) ltac:(intros; reflexivity)) argsin Hlin)
          as (κf & Δf & Φf & Hff & Hfy & Hres & Hcf).
        exists κf, Δf, Φf; split; [ assumption |]; split; [ assumption |]; split.
        * intros v Hv; destruct (Hres v Hv) as (r0 & Hr0 & Hv0).
          destruct (pend_feed Θ Ξ (me_base 0) (p_abs fp nil) c ip argsT nil argsin v
                      ltac:(cbn; lia) ltac:(rewrite List.app_nil_r; exists r0; split; assumption)) as (r & Hr & Hv').
          unfold argsT, argsin in Hv'; rewrite List.firstn_skipn in Hv'.
          exists r; split; [ intros; apply Hglob, Hr | exact Hv' ].
        * assert (Hargs : List.rev args = List.rev argsin ++ List.rev argsT)
            by (unfold argsT, argsin; rewrite <- List.rev_app_distr, List.firstn_skipn; reflexivity).
          rewrite Hargs.
          pose proof (cfg_eq_close_abs Θ Ξ fp U (List.rev argsT) (List.rev argsin) Hf
                        ltac:(rewrite List.length_rev; assumption)) as Hν.
          rewrite List.length_rev, Hlin in Hν.
          eapply cfg_eq_comp; [ exact Hν | exact Hcf | intros; lia | |].
          -- intros lp Hlp; eapply exp_ok_PQ; [ apply Hip1; exact Hlp | | ].
             ++ intros [m k] (c' & Hc0 & Hk) Hm0; cbn in *; subst; injection Hc0 as <-; exact Hk.
             ++ intros [[fq | m] ms] Hq; cbn in *; auto; lia.
          -- intros p Hp; eapply exp_ok_PQ; [ apply Hip2; exact Hp | | ].
             ++ intros [m k] (c' & Hc0 & Hk) Hm0; cbn in *; subst; injection Hc0 as <-; exact Hk.
             ++ intros [[fq | m] ms] Hq; cbn in *; auto; lia.
  Qed.
End Top.

(** ** Telescope positions *)

Definition tsub_bfree (θ : tsub) : Prop :=
  (forall x, bfree (ts_var θ x)) /\ (forall lp, bfree (ts_param θ lp)) /\ (forall p, bfree (ts_glob θ p)).

Lemma tsub_bfree_id : tsub_bfree ts_id.
Proof. repeat split; intros; exact I. Qed.

Lemma tsub_bfree_ms_close : forall mp c d, tsub_bfree (ts_ms (ms_close mp c d)).
Proof. intros; destruct (bfree_close mp c d) as (A1 & A2 & A3); repeat split; assumption. Qed.

Lemma tsub_bfree_comp : forall θ2 θ1, tsub_bfree θ2 -> tsub_bfree θ1 -> tsub_bfree (ts_comp θ2 θ1).
Proof.
  intros * (A1 & A2 & A3) (B1 & B2 & B3); repeat split; intros; cbn; apply bfree_tsub; auto.
Qed.

Fixpoint napp (h : domain_ne) (tys args : list domain) : domain_ne :=
  match tys, args with
  | t :: tys', c :: args' => napp (h $ᵈ ⇓ t c) tys' args'
  | _, _ => h
  end.

Lemma napp_app : forall tys1 args1 tys2 args2 h,
    List.length tys1 = List.length args1 ->
    napp h (tys1 ++ tys2) (args1 ++ args2) = napp (napp h tys1 args1) tys2 args2.
Proof.
  induction tys1 as [| t tys1 IH]; intros [| c args1] * Hl; cbn in *; try lia; auto.
Qed.

Lemma napp_snoc : forall tys args t c h,
    List.length tys = List.length args ->
    napp h (tys ++ t :: nil) (args ++ c :: nil) = napp h tys args $ᵈ ⇓ t c.
Proof. intros; rewrite napp_app by assumption; reflexivity. Qed.

(** The positions of a telescope's own parameters, in application order. *)
Fixpoint tele_pos (cs : list nat) (j : nat) (l : list exp) : list (exp * tsub * nat * list nat) :=
  match l with
  | nil => nil
  | T :: l' => (T, ts_id, j, cs) :: tele_pos cs (S j) l'
  end.

Lemma tele_pos_length : forall cs l j, List.length (tele_pos cs j l) = List.length l.
Proof. induction l; intros; cbn; auto. Qed.

Lemma tele_pos_nth : forall cs l j i e,
    List.nth_error (tele_pos cs j l) i = Some e -> exists T, List.nth_error l i = Some T /\ e = (T, ts_id, j + i, cs).
Proof.
  induction l as [| T l IH]; intros * H; destruct i; cbn in *; try discriminate.
  - injection H as <-; exists T; rewrite Nat.add_0_r; auto.
  - destruct (IH _ _ _ H) as (T' & HT' & ->); exists T'; split; [ assumption | replace (j + S i) with (S j + i) by lia; reflexivity ].
Qed.

(** The positions of an inner telescope, read one nested module out. *)
Fixpoint lift_pos (x : string) (c : nat) (k : nat) (l : list (exp * tsub * nat * list nat)) :=
  match l with
  | nil => nil
  | (R, θ, n, csR) :: l' => (R, ts_comp θ (ts_ms (ms_close (p_rel 0 (x :: nil)) c k)), n, csR) :: lift_pos x c (S k) l'
  end.

Lemma lift_pos_length : forall x c l k, List.length (lift_pos x c k l) = List.length l.
Proof. induction l as [| [[[? ?] ?] ?] l IH]; intros; cbn; auto. Qed.

Lemma lift_pos_nth : forall x c l k i e,
    List.nth_error (lift_pos x c k l) i = Some e ->
    exists R θ n csR, List.nth_error l i = Some (R, θ, n, csR) /\
      e = (R, ts_comp θ (ts_ms (ms_close (p_rel 0 (x :: nil)) c (k + i))), n, csR).
Proof.
  induction l as [| [[[R θ] n] csR] l IH]; intros * H; destruct i; cbn in *; try discriminate.
  - injection H as <-; do 4 eexists; split; [ reflexivity |]; rewrite Nat.add_0_r; reflexivity.
  - destruct (IH _ _ _ H) as (R' & θ' & n' & csR' & HR & ->); do 4 eexists; split; [ eassumption |].
    replace (k + S i) with (S k + i) by lia; reflexivity.
Qed.

Lemma nth_error_rev_tele : forall (Δ : ctx) j, j < List.length Δ ->
    List.nth_error (List.rev Δ) j = List.nth_error Δ (List.length Δ - S j).
Proof.
  intros * Hj; rewrite List.nth_error_rev; apply Nat.ltb_lt in Hj; rewrite Hj; reflexivity.
Qed.

Lemma ctx_msub_nth : forall μ (Δ : ctx) e A, List.nth_error Δ e = Some A ->
    List.nth_error Δ[μ]ᵐ e = Some A[ms_qn (List.length Δ - S e) μ]ᵐ.
Proof.
  induction Δ as [| B Δ IH]; intros [| e] A H; cbn in *; try discriminate.
  - injection H as ->; rewrite Nat.sub_0_r; reflexivity.
  - rewrite (IH _ _ H); reflexivity.
Qed.

Lemma addr_depth_in : forall a x, addr_depth (path_in a x) = S (addr_depth a).
Proof. intros; unfold addr_depth, path_in; cbn; rewrite List.length_app; cbn; lia. Qed.

Section Fargs.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** A frame's arguments applied to a head, at its raw parameter types. *)
  Lemma fargs_napp : forall (Δ : ctx) (cs tys : list domain) κ h,
      List.length cs = List.length Δ -> List.length tys = List.length Δ ->
      (forall j T ty, List.nth_error Δ (List.length Δ - S j) = Some T -> List.nth_error tys j = Some ty ->
         eval_exp Θ Ξ κ T (List.rev (List.firstn j cs)) ty) ->
      eval_fargs Θ Ξ κ Δ (List.rev cs) h (napp h tys cs).
  Proof.
    induction Δ as [| T Δ IH]; intros cs tys κ h Hc Ht Hev.
    - destruct cs; [| discriminate ]; destruct tys; [| discriminate ]; constructor.
    - destruct cs as [| c cs] using List.rev_ind; [ discriminate |].
      destruct tys as [| ty tys] using List.rev_ind; [ discriminate |].
      clear IHcs IHtys.
      rewrite !List.length_app in *; cbn in *.
      rewrite List.rev_app_distr; cbn.
      rewrite napp_snoc by lia.
      constructor.
      + apply IH; [ lia | lia |].
        intros j T' ty' HT' Hty'.
        assert (Hj : j < List.length Δ) by (assert (Hn : List.nth_error tys j <> None) by congruence; apply List.nth_error_Some in Hn; lia).
        pose proof (Hev j T' ty') as Hev'.
        replace (List.length Δ - j) with (S (List.length Δ - S j)) in Hev' by lia; cbn in Hev'.
        rewrite List.nth_error_app1 in Hev' by lia.
        specialize (Hev' HT' Hty').
        rewrite List.firstn_app in Hev'.
        replace (j - List.length cs) with 0 in Hev' by lia; cbn in Hev'; rewrite List.app_nil_r in Hev'; exact Hev'.
      + replace (List.rev cs) with (List.rev (List.firstn (List.length Δ) (cs ++ c :: nil))).
        * apply (Hev (List.length Δ)); [ rewrite Nat.sub_diag; reflexivity |].
          rewrite List.nth_error_app2 by lia; replace (List.length Δ - List.length tys) with 0 by lia; reflexivity.
        * rewrite List.firstn_app, List.firstn_all2 by lia.
          replace (List.length Δ - List.length cs) with 0 by lia; cbn; rewrite List.app_nil_r; reflexivity.
  Qed.
End Fargs.

Lemma firstn_app_le : forall {A} (l1 l2 : list A) i, i <= List.length l1 -> List.firstn i (l1 ++ l2) = List.firstn i l1.
Proof. intros; rewrite List.firstn_app; replace (i - List.length l1) with 0 by lia; cbn; apply List.app_nil_r. Qed.

Lemma firstn_app_ge : forall {A} (l1 l2 : list A) i, List.length l1 <= i ->
    List.firstn i (l1 ++ l2) = l1 ++ List.firstn (i - List.length l1) l2.
Proof. intros; rewrite List.firstn_app, List.firstn_all2 by lia; reflexivity. Qed.

Lemma nth_map_seq : forall {A} (f : nat -> A) c j, j < c -> List.nth_error (List.map f (List.seq 0 c)) j = Some (f j).
Proof. intros * Hj; rewrite List.nth_error_map, List.nth_error_seq; apply Nat.ltb_lt in Hj; rewrite Hj; reflexivity. Qed.

Lemma ts_ms_eq : forall μ μ', ms_eq μ μ' -> ts_eq (ts_ms μ) (ts_ms μ').
Proof. intros * [H1 H2]; repeat split; intros; cbn; auto. Qed.

Section ChainT.
  Variables (Θ : gdeps) (Ξ : gstack).

  Definition pos_ok (cs : list nat) (i : nat) (e : (exp * tsub * nat * list nat)%type) (T : exp) : Prop :=
    match e with (R, θ, nR, csR) =>
      T = exp_tsub θ R /\ exp_scoped nR csR R /\ tsub_bfree θ /\
      (forall x, x < nR -> exp_ok i (param_ok cs) (path_ok cs) (ts_var θ x)) /\
      (forall lp, param_ok csR lp -> exp_ok i (param_ok cs) (path_ok cs) (ts_param θ lp)) /\
      (forall p, path_ok csR p -> exp_ok i (param_ok cs) (path_ok cs) (ts_glob θ p))
    end.

  Definition conf_ok (κ : menv) (args : list domain) (i : nat) (e : (exp * tsub * nat * list nat)%type) (rc : (menv * env)%type) : Prop :=
    match e, rc with (R, θ, nR, csR), (κi, ρi) =>
      List.length ρi = nR /\ cfg_eq Θ Ξ θ nR (param_ok csR) (path_ok csR) κ (List.rev (List.firstn i args)) κi ρi
    end.

  Definition ty_ok (e : (exp * tsub * nat * list nat)%type) (rc : (menv * env)%type) (ty : domain) : Prop :=
    match e, rc with (R, _, _, _), (κi, ρi) => eval_exp Θ Ξ κi R ρi ty end.

  Definition chainT_stmt (Φ : gmod) (ip : list string) (Δ : ctx) (b pv : bool) (A : typ) (B : option exp) : Prop :=
    forall cs, cs <> nil ->
    (forall x ip' E, ip = x :: ip' -> gm_find Φ x = Some E -> ge_rscoped cs E) ->
    exists y Ar Br θ csf pos,
      A = exp_tsub θ Ar /\ B = option_map (exp_tsub θ) Br /\
      exp_scoped 0 csf Ar /\ opt_scoped 0 csf Br /\ csf <> nil /\ tsub_bfree θ /\
      (forall lp, param_ok csf lp -> exp_ok (List.length Δ) (param_ok cs) (path_ok cs) (ts_param θ lp)) /\
      (forall p, path_ok csf p -> exp_ok (List.length Δ) (param_ok cs) (path_ok cs) (ts_glob θ p)) /\
      List.length pos = List.length Δ /\
      (forall i e, List.nth_error pos i = Some e ->
         exists T, List.nth_error Δ (List.length Δ - S i) = Some T /\ pos_ok cs i e T) /\
      forall κ Δa Φfull,
        frame_at Θ Ξ (me_addr κ) = Some (Δa, Φfull) ->
        (forall x ip', ip = x :: ip' -> gm_find Φfull x = gm_find Φ x) ->
        (forall cs', List.length cs' < List.length Δ -> exists v, ent_res Θ Ξ κ ip cs' v) /\
        forall args, List.length args = List.length Δ ->
          exists κf Δf Φf rconf, frame_at Θ Ξ (me_addr κf) = Some (Δf, Φf) /\
            gm_find Φf y = Some (ge_def b pv Ar Br) /\
            (forall v, eval_ent Θ Ξ κf (y :: nil) v -> ent_res Θ Ξ κ ip args v) /\
            cfg_eq Θ Ξ θ 0 (param_ok csf) (path_ok csf) κ (List.rev args) κf nil /\
            path_in (me_addr κf) y = {| p_qual := p_qual (me_addr κ); p_mems := p_mems (me_addr κ) ++ ip |} /\
            addr_depth (me_addr κf) = addr_depth (me_addr κ) + (List.length ip - 1) /\
            List.length rconf = List.length Δ /\
            (forall i e rc, List.nth_error pos i = Some e -> List.nth_error rconf i = Some rc -> conf_ok κ args i e rc) /\
            (forall h0 h1 tys, eval_gne Θ Ξ κ (addr_depth (me_addr κ)) h0 h1 -> List.length tys = List.length Δ ->
               (forall i e rc ty, List.nth_error pos i = Some e -> List.nth_error rconf i = Some rc ->
                  List.nth_error tys i = Some ty -> ty_ok e rc ty) ->
               eval_gne Θ Ξ κf (addr_depth (me_addr κf)) h0 (napp h1 tys args)).

  Lemma chainT : forall Φ ip Δ E, Φ ∋ ip ⇒ Δ ⍮ E -> gm_canon Φ ->
      forall b pv A B, E = ge_def b pv A B -> chainT_stmt Φ ip Δ b pv A B.
  Proof.
    induction 1 as [? ? ? ? ? ? | ? ? ? ? ? ? ? ? ? ? Hin IH | ? ? ? ? ? ? Hold IH];
      intros Hcanon b0 pv0 A0 B0 HE; unfold chainT_stmt; intros cs Hcs Hsc.
    - (* the member itself *)
      injection HE as <- <- <- <-.
      destruct (Hsc x nil _ eq_refl ltac:(cbn; rewrite String.eqb_refl; reflexivity)) as [HsA HsB].
      exists x, A, B, ts_id, cs, nil.
      split; [ symmetry; apply exp_tsub_id |].
      split; [ destruct B; cbn; [ rewrite exp_tsub_id |]; reflexivity |].
      do 3 (split; [ assumption |]).
      split; [ apply tsub_bfree_id |].
      split; [ intros; cbn; assumption |].
      split; [ intros; cbn; assumption |].
      split; [ reflexivity |].
      split; [ intros [| ?] ? H; discriminate H |].
      intros * Hf Hhd; split; [ intros; cbn in *; lia |].
      intros [| ? ?] Hl; cbn in Hl; [| lia ].
      exists κ, Δa, Φfull, nil; split; [ assumption |].
      split; [ rewrite (Hhd x nil eq_refl); cbn; rewrite String.eqb_refl; reflexivity |].
      split; [ intros v Hv; exists v; split; [ exact Hv | constructor ] |].
      split; [ apply cfg_eq_id |].
      split; [ reflexivity |].
      split; [ cbn; lia |].
      split; [ reflexivity |].
      split; [ intros [| ?] ? ? H; discriminate H |].
      intros h0 h1 [| ? ?] Hg Hl' _; cbn in Hl'; [| lia ]; exact Hg.
    - (* through a nested module *)
      injection HE as <- <- <- <-; cbn in Hcanon; destruct Hcanon as (_ & _ & Hc').
      destruct (Hsc x ip _ eq_refl ltac:(cbn; rewrite String.eqb_refl; reflexivity)) as [HsΔ' HsΦ'].
      pose proof (gm_lookup_nonnil _ _ _ _ Hin) as Hip.
      destruct (IH Hc' _ _ _ _ eq_refl (List.length Δ' :: cs) ltac:(congruence)
                  ltac:(intros; eapply gm_rscoped_find; eassumption))
        as (y & Ar & Br & θin & csf & posin & -> & -> & HsA & HsB & Hcsf & Hbθ & Hip1 & Hip2 & Hlpos & Hpos & Hdyn).
      set (c := List.length Δ') in *.
      set (n := List.length Δ) in *.
      set (ν := ts_ms (ms_close (p_rel 0 (x :: nil)) c n)).
      exists y, Ar, Br, (ts_comp θin ν), csf, (tele_pos cs 0 (List.rev Δ') ++ lift_pos x c 0 posin).
      assert (Hltot : List.length (Δ[close (p_rel 0 (x :: nil)) c]ᵐ ++ Δ') = n + c)
        by (rewrite List.length_app, ctx_msub_length; reflexivity).
      rewrite Hltot.
      split; [ rewrite exp_tsub_ms, exp_tsub_comp; reflexivity |].
      split; [ rewrite opt_tsub_ms, opt_tsub_comp; reflexivity |].
      do 3 (split; [ assumption |]).
      split; [ apply tsub_bfree_comp; [ assumption | apply tsub_bfree_ms_close ] |].
      split; [ intros lp Hlp; cbn; apply exp_ok_close_in; auto; apply Hbθ |].
      split; [ intros p Hp; cbn; apply exp_ok_close_in; auto; apply Hbθ |].
      split; [ rewrite List.length_app, tele_pos_length, lift_pos_length, List.length_rev; lia |].
      split.
      { intros i e Hie.
        destruct (Nat.lt_ge_cases i c) as [Hic | Hic].
        - rewrite List.nth_error_app1 in Hie by (rewrite tele_pos_length, List.length_rev; lia).
          destruct (tele_pos_nth _ _ _ _ _ Hie) as (T & HT & ->); cbn [Nat.add] in *.
          rewrite nth_error_rev_tele in HT by lia; fold c in HT.
          exists T; split.
          + rewrite List.nth_error_app2 by (rewrite ctx_msub_length; lia).
            rewrite ctx_msub_length; fold n; replace (n + c - S i - n) with (c - S i) by lia; exact HT.
          + cbn; split; [ symmetry; apply exp_tsub_id |].
            split; [ pose proof (ctx_scoped_nth _ _ _ _ HsΔ' HT) as H; fold c in H; replace (c - S (c - S i)) with i in H by lia; exact H |].
            split; [ apply tsub_bfree_id |].
            split; [ intros; cbn; assumption |].
            split; intros; cbn; assumption.
        - rewrite List.nth_error_app2 in Hie by (rewrite tele_pos_length, List.length_rev; lia).
          rewrite tele_pos_length, List.length_rev in Hie; fold c in Hie.
          destruct (lift_pos_nth _ _ _ _ _ _ Hie) as (R & θi & nR & csR & HR & ->); cbn [Nat.add] in *.
          destruct (Hpos _ _ HR) as (Tin & HTin & HTok); cbn in HTok.
          destruct HTok as (-> & HsR & Hbi & Hv & Hp & Hg).
          assert (Hin_n0 : i - c < List.length posin) by (apply List.nth_error_Some; congruence);
          assert (Hin_n : i - c < n) by (unfold n, c in *; lia).
          exists (exp_tsub (ts_ms (ms_close (p_rel 0 (x :: nil)) c (i - c))) (exp_tsub θi R)); split.
          + rewrite List.nth_error_app1 by (rewrite ctx_msub_length; lia).
            replace (n + c - S i) with (n - S (i - c)) by lia.
            rewrite (ctx_msub_nth _ _ _ _ HTin), exp_tsub_ms.
            replace (List.length Δ - S (n - S (i - c))) with (i - c) by (unfold n, c in *; lia).
            f_equal; apply exp_tsub_ext, ts_ms_eq.
            pose proof (ms_qn_close (i - c) (p_rel 0 (x :: nil)) c 0) as Hq; rewrite Nat.add_0_r in Hq; exact Hq.
          + cbn; split; [ rewrite exp_tsub_comp; reflexivity |].
            split; [ assumption |].
            split; [ apply tsub_bfree_comp; [ assumption | apply tsub_bfree_ms_close ] |].
            assert (Hi : i = i - c + c) by lia.
            split; [ intros; cbn [ts_var ts_param ts_glob ts_comp]; rewrite Hi at 1; apply exp_ok_close_in; auto; apply Hbi |].
            split; [ intros; cbn [ts_var ts_param ts_glob ts_comp]; rewrite Hi at 1; apply exp_ok_close_in; auto; apply Hbi |].
            intros; cbn [ts_var ts_param ts_glob ts_comp]; rewrite Hi at 1; apply exp_ok_close_in; auto; apply Hbi. }
      intros κ Δa Φfull Hf Hhd.
      pose proof (Hhd x ip eq_refl) as Hx; cbn in Hx; rewrite String.eqb_refl in Hx.
      assert (Hfx : forall argsx, frame_at Θ Ξ (me_addr (me_frame (path_in (me_addr κ) x) argsx κ)) = Some (Δ', Φ'))
        by (intros; cbn; eapply frame_at_in; eassumption).
      split.
      + intros cs' Hl.
        destruct (Nat.lt_ge_cases (List.length cs') c) as [Hlt | Hge].
        * destruct (pend_partial Θ Ξ κ (path_in (me_addr κ) x) c ip cs' nil ltac:(cbn; lia))
            as (r & v & Hr & Hv).
          exists v, r; split; [ eapply eval_ent_mod; eassumption | exact Hv ].
        * destruct (proj1 (Hdyn _ _ _ (Hfx (List.rev (List.firstn c cs'))) ltac:(intros; reflexivity))
                       (List.skipn c cs') ltac:(rewrite List.length_skipn; lia)) as (v & Hv).
          destruct (pend_feed Θ Ξ κ (path_in (me_addr κ) x) c ip
                      (List.firstn c cs') nil (List.skipn c cs') v
                      ltac:(rewrite List.length_firstn; cbn; lia)
                      ltac:(rewrite List.app_nil_r; exact Hv)) as (r & Hr & Hv').
          rewrite List.firstn_skipn in Hv'.
          exists v, r; split; [ eapply eval_ent_mod; eassumption | exact Hv' ].
      + intros args Hl.
        set (argsx := List.firstn c args).
        set (argsin := List.skipn c args).
        assert (Hlx : List.length argsx = c) by (unfold argsx; rewrite List.length_firstn; lia).
        assert (Hlin : List.length argsin = n) by (unfold argsin; rewrite List.length_skipn; lia).
        assert (Hsplit : args = argsx ++ argsin) by (unfold argsx, argsin; symmetry; apply List.firstn_skipn).
        destruct (proj2 (Hdyn _ _ _ (Hfx (List.rev argsx)) ltac:(intros; reflexivity)) argsin Hlin)
          as (κf & Δf & Φf & rconfin & Hff & Hfy & Hres & Hcf & Hpath & Hdepth & Hlrc & Hconf & Hgne).
        exists κf, Δf, Φf, (List.map (fun j => (κ, List.rev (List.firstn j argsx))) (List.seq 0 c) ++ rconfin).
        split; [ assumption |]; split; [ assumption |].
        split.
        { intros v Hv.
          destruct (Hres v Hv) as (r0 & Hr0 & Hv0).
          destruct (pend_feed Θ Ξ κ (path_in (me_addr κ) x) c ip argsx nil argsin v
                      ltac:(cbn; lia) ltac:(rewrite List.app_nil_r; exists r0; split; assumption))
            as (r & Hr & Hv').
          rewrite <- Hsplit in Hv'.
          exists r; split; [ eapply eval_ent_mod; eassumption | exact Hv' ]. }
        split.
        { rewrite Hsplit, List.rev_app_distr.
          pose proof (cfg_eq_close_in Θ Ξ κ Δa Φfull x Δ' Φ' (List.rev argsx) (List.rev argsin) Hf Hx
                        ltac:(rewrite List.length_rev; assumption)) as Hν.
          rewrite List.length_rev, Hlin in Hν.
          eapply cfg_eq_comp; [ exact Hν | exact Hcf | intros; lia | |].
          - intros lp Hlp; eapply exp_ok_PQ; [ apply Hip1; exact Hlp | | auto ].
            intros [m k] (c' & Hc0 & Hk) Hm; cbn in Hm, Hc0 |- *; rewrite Hm in Hc0; injection Hc0 as <-; exact Hk.
          - intros p Hp; eapply exp_ok_PQ; [ apply Hip2; exact Hp | | auto ].
            intros [m k] (c' & Hc0 & Hk) Hm; cbn in Hm, Hc0 |- *; rewrite Hm in Hc0; injection Hc0 as <-; exact Hk. }
        split.
        { rewrite Hpath; cbn; rewrite <- List.app_assoc; reflexivity. }
        split.
        { rewrite Hdepth; cbn [me_addr]; rewrite addr_depth_in; destruct ip; [ contradiction |]; cbn; lia. }
        split; [ rewrite List.length_app, List.length_map, List.length_seq; lia |].
        split.
        { intros i e rc Hie Hrc.
          destruct (Nat.lt_ge_cases i c) as [Hic | Hic].
          - rewrite List.nth_error_app1 in Hie by (rewrite tele_pos_length, List.length_rev; lia).
            rewrite List.nth_error_app1 in Hrc by (rewrite List.length_map, List.length_seq; lia).
            destruct (tele_pos_nth _ _ _ _ _ Hie) as (T & HT & ->); cbn [Nat.add] in *.
            rewrite nth_map_seq in Hrc by lia; injection Hrc as <-; cbn.
            split; [ rewrite List.length_rev, List.length_firstn; lia |].
            rewrite Hsplit, firstn_app_le by lia; apply cfg_eq_id.
          - rewrite List.nth_error_app2 in Hie by (rewrite tele_pos_length, List.length_rev; lia).
            rewrite List.nth_error_app2 in Hrc by (rewrite List.length_map, List.length_seq; lia).
            rewrite tele_pos_length, List.length_rev in Hie; fold c in Hie; rewrite List.length_map, List.length_seq in Hrc.
            destruct (lift_pos_nth _ _ _ _ _ _ Hie) as (R & θi & nR & csR & HR & ->); cbn [Nat.add] in *.
            destruct rc as [κi ρi].
            specialize (Hconf _ _ _ HR Hrc); cbn in Hconf; destruct Hconf as [HlR Hcfi].
            destruct (Hpos _ _ HR) as (Tin & HTin & HTok); cbn in HTok.
            destruct HTok as (_ & HsR & Hbi & Hv & Hp & Hg).
            assert (Hin_n0 : i - c < List.length posin) by (apply List.nth_error_Some; congruence);
          assert (Hin_n : i - c < n) by (unfold n, c in *; lia).
            cbn; split; [ assumption |].
            rewrite Hsplit, firstn_app_ge by lia; rewrite Hlx, List.rev_app_distr.
            pose proof (cfg_eq_close_in Θ Ξ κ Δa Φfull x Δ' Φ' (List.rev argsx) (List.rev (List.firstn (i - c) argsin)) Hf Hx
                          ltac:(rewrite List.length_rev; assumption)) as Hν.
            rewrite List.length_rev, List.length_firstn, Nat.min_l in Hν by lia.
            eapply cfg_eq_comp; [ exact Hν | exact Hcfi | |  |].
            + intros x0 Hx0; eapply exp_ok_PQ; [ apply Hv; exact Hx0 | | auto ].
              intros [m k] (c' & Hc0 & Hk) Hm; cbn in Hm, Hc0 |- *; rewrite Hm in Hc0; injection Hc0 as <-; exact Hk.
            + intros lp Hlp; eapply exp_ok_PQ; [ apply Hp; exact Hlp | | auto ].
              intros [m k] (c' & Hc0 & Hk) Hm; cbn in Hm, Hc0 |- *; rewrite Hm in Hc0; injection Hc0 as <-; exact Hk.
            + intros p Hp0; eapply exp_ok_PQ; [ apply Hg; exact Hp0 | | auto ].
              intros [m k] (c' & Hc0 & Hk) Hm; cbn in Hm, Hc0 |- *; rewrite Hm in Hc0; injection Hc0 as <-; exact Hk. }
        intros h0 h1 tys Hg0 Hlt Hty.
        set (tysx := List.firstn c tys).
        set (tysin := List.skipn c tys).
        assert (Hltx : List.length tysx = c) by (unfold tysx; rewrite List.length_firstn; lia).
        assert (Hltin : List.length tysin = n) by (unfold tysin; rewrite List.length_skipn; lia).
        assert (Hgx : eval_gne Θ Ξ (me_frame (path_in (me_addr κ) x) (List.rev argsx) κ)
                        (addr_depth (me_addr (me_frame (path_in (me_addr κ) x) (List.rev argsx) κ)))
                        h0 (napp h1 tysx argsx)).
        { cbn [me_addr]; rewrite addr_depth_in.
          econstructor; [ exact Hg0 | eapply frame_at_in; eassumption |].
          apply fargs_napp; [ assumption | assumption |].
          intros j T ty HT Hty0.
          assert (Hj : j < c) by (assert (Hn0 : List.nth_error tysx j <> None) by congruence; apply List.nth_error_Some in Hn0; lia).
          apply (Hty j (T, ts_id, j, cs) (κ, List.rev (List.firstn j argsx)) ty).
          - rewrite List.nth_error_app1 by (rewrite tele_pos_length, List.length_rev; lia).
            assert (Hj' : List.nth_error (tele_pos cs 0 (List.rev Δ')) j = Some (T, ts_id, j, cs)).
            { clear - Hj HT.
              assert (H : forall l k j T, List.nth_error l j = Some T -> List.nth_error (tele_pos cs k l) j = Some (T, ts_id, k + j, cs)).
              { induction l as [| T0 l IHl]; intros k [| j0] T0' H; cbn in *; try discriminate.
                - injection H as <-; rewrite Nat.add_0_r; reflexivity.
                - rewrite (IHl _ _ _ H); replace (S k + j0) with (k + S j0) by lia; reflexivity. }
              rewrite (H _ 0 j T); [ reflexivity |].
              rewrite nth_error_rev_tele by lia; exact HT. }
            exact Hj'.
          - rewrite List.nth_error_app1 by (rewrite List.length_map, List.length_seq; lia).
            rewrite nth_map_seq by lia; reflexivity.
          - unfold tysx in Hty0; rewrite List.nth_error_firstn in Hty0.
            destruct (Nat.ltb_spec j c); [ exact Hty0 | lia ]. }
        pose proof (Hgne _ _ tysin Hgx Hltin) as Hgin.
        assert (Htys : tys = tysx ++ tysin) by (unfold tysx, tysin; symmetry; apply List.firstn_skipn).
        rewrite Hsplit; rewrite Htys at 1; rewrite (napp_app tysx argsx tysin argsin) by lia.
        rewrite Htys in Hty.
        apply Hgin.
        intros i e rc ty Hie Hrc Hty0.
        destruct e as [[[R θi] nR] csR]; destruct rc as [κi ρi].
        assert (H1 : List.nth_error (tele_pos cs 0 (List.rev Δ') ++ lift_pos x c 0 posin) (c + i) =
                       Some (R, ts_comp θi (ts_ms (ms_close (p_rel 0 (x :: nil)) c i)), nR, csR)).
        { rewrite List.nth_error_app2 by (rewrite tele_pos_length, List.length_rev; lia).
          rewrite tele_pos_length, List.length_rev, Nat.add_comm, Nat.add_sub.
          clear - Hie.
          assert (H : forall l k i R θi nR csR, List.nth_error l i = Some (R, θi, nR, csR) ->
                     List.nth_error (lift_pos x c k l) i =
                     Some (R, ts_comp θi (ts_ms (ms_close (p_rel 0 (x :: nil)) c (k + i))), nR, csR)).
          { induction l as [| [[[R0 θ0] n0] cs0] l IHl]; intros k [| i0] * H; cbn in *; try discriminate.
            - injection H as <- <- <- <-; rewrite Nat.add_0_r; reflexivity.
            - rewrite (IHl _ _ _ _ _ _ H); replace (S k + i0) with (k + S i0) by lia; reflexivity. }
          exact (H _ 0 _ _ _ _ _ Hie). }
        assert (H2 : List.nth_error (List.map (fun j => (κ, List.rev (List.firstn j argsx))) (List.seq 0 c) ++ rconfin) (c + i) = Some (κi, ρi)).
        { rewrite List.nth_error_app2 by (rewrite List.length_map, List.length_seq; lia).
          rewrite List.length_map, List.length_seq, Nat.add_comm, Nat.add_sub; exact Hrc. }
        assert (H3 : List.nth_error (tysx ++ tysin) (c + i) = Some ty).
        { rewrite List.nth_error_app2 by lia; rewrite Hltx, Nat.add_comm, Nat.add_sub; exact Hty0. }
        exact (Hty _ _ _ _ H1 H2 H3).
    - (* an older entry *)
      subst E; pose proof Hcanon as Hcanon0; cbn in Hcanon; destruct Hcanon as (Hc & _ & _).
      assert (Hold' : forall x ip', ip = x :: ip' -> gm_find (gm_ext Φ y E') x = gm_find Φ x)
        by (intros * ->; eapply gm_find_old; [ exact Hcanon0 | exact Hold ]).
      unfold chainT_stmt in IH.
      destruct (IH Hc _ _ _ _ eq_refl cs Hcs ltac:(intros * Heq Hf; eapply Hsc; [ exact Heq | rewrite (Hold' _ _ Heq); eassumption ]))
        as (y0 & Ar & Br & θ & csf & pos & Hrest).
      exists y0, Ar, Br, θ, csf, pos.
      destruct Hrest as (HA & HB & HsA & HsB & Hcsf & Hbθ & Hip1 & Hip2 & Hlpos & Hpos & Hdyn).
      do 10 (split; [ assumption |]).
      intros κ Δa Φfull Hf Hhd; apply (Hdyn _ _ _ Hf).
      intros * Heq; rewrite (Hhd _ _ Heq), (Hold' _ _ Heq); reflexivity.
  Qed.
End ChainT.

Fixpoint lift_with (f : nat -> tsub) (k : nat) (l : list (exp * tsub * nat * list nat)) :=
  match l with
  | nil => nil
  | (R, θ, n, csR) :: l' => (R, ts_comp θ (f k), n, csR) :: lift_with f (S k) l'
  end.

Lemma lift_with_length : forall f l k, List.length (lift_with f k l) = List.length l.
Proof. induction l as [| [[[? ?] ?] ?] l IH]; intros; cbn; auto. Qed.

Lemma lift_with_nth : forall f l k i e,
    List.nth_error (lift_with f k l) i = Some e ->
    exists R θ n csR, List.nth_error l i = Some (R, θ, n, csR) /\ e = (R, ts_comp θ (f (k + i)), n, csR).
Proof.
  induction l as [| [[[R θ] n] csR] l IH]; intros * H; destruct i; cbn in *; try discriminate.
  - injection H as <-; do 4 eexists; split; [ reflexivity |]; rewrite Nat.add_0_r; reflexivity.
  - destruct (IH _ _ _ H) as (R' & θ' & n' & csR' & HR & ->); do 4 eexists; split; [ eassumption |].
    replace (k + S i) with (S k + i) by lia; reflexivity.
Qed.

Lemma lift_with_nth' : forall f k l i R θ n csR,
    List.nth_error l i = Some (R, θ, n, csR) ->
    List.nth_error (lift_with f k l) i = Some (R, ts_comp θ (f (k + i)), n, csR).
Proof.
  intros f k l; revert k; induction l as [| [[[R0 θ0] n0] cs0] l IH]; intros k [| i] * H; cbn in *; try discriminate.
  - injection H as <- <- <- <-; rewrite Nat.add_0_r; reflexivity.
  - rewrite (IH _ _ _ _ _ _ H); replace (S k + i) with (k + S i) by lia; reflexivity.
Qed.

Section TopT.
  Variables (Θ : gdeps) (Ξ : gstack).

  #[local] Notation "'⟦' M '⟧' κ '⍮' ρ '↘' r" := (eval_exp Θ Ξ κ M ρ r)
    (at level 70, M at level 69, κ at level 69, ρ at level 69, r at level 69).

  (** A position at the top level: the raw type, its replacement, its
      variables and its frames. *)
  Definition tpos_ok (i : nat) (e : (exp * tsub * nat * list nat)%type) (T : exp) : Prop :=
    match e with (R, θ, nR, csR) => T = exp_tsub θ R /\ exp_scoped nR csR R end.

  Lemma top_chainT : forall p Δ b pv A B,
      ⊢g Θ ⍮ Ξ ->
      Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
      exists y Ar Br θ csf pos,
        A = exp_tsub θ Ar /\ B = option_map (exp_tsub θ) Br /\
        exp_scoped 0 csf Ar /\ opt_scoped 0 csf Br /\
        List.length pos = List.length Δ /\
        (forall i e, List.nth_error pos i = Some e ->
           exists T, List.nth_error Δ (List.length Δ - S i) = Some T /\ tpos_ok i e T) /\
        (forall cs', List.length cs' < List.length Δ -> exists v, gres Θ Ξ p cs' v) /\
        forall args, List.length args = List.length Δ ->
          exists κf Δf Φf rconf, frame_at Θ Ξ (me_addr κf) = Some (Δf, Φf) /\
            gm_find Φf y = Some (ge_def b pv Ar Br) /\
            (forall v, eval_ent Θ Ξ κf (y :: nil) v -> gres Θ Ξ p args v) /\
            cfg_eq Θ Ξ θ 0 (param_ok csf) (path_ok csf) me_top (List.rev args) κf nil /\
            path_in (me_addr κf) y = p /\
            List.length rconf = List.length Δ /\
            (forall i e rc, List.nth_error pos i = Some e -> List.nth_error rconf i = Some rc ->
               conf_ok Θ Ξ me_top args i e rc) /\
            (forall tys, List.length tys = List.length Δ ->
               (forall i e rc ty, List.nth_error pos i = Some e -> List.nth_error rconf i = Some rc ->
                  List.nth_error tys i = Some ty -> ty_ok Θ Ξ e rc ty) ->
               eval_gne Θ Ξ κf (addr_depth (me_addr κf)) (d_glob p) (napp (d_glob p) tys args)).
  Proof.
    intros * Hg Hl.
    pose proof (wf_gctx_stack _ _ Hg) as HΞ.
    pose proof (wf_gstack_canon _ _ HΞ) as Hcs.
    pose proof (wf_gdeps_canon _ (wf_gstack_deps _ _ HΞ)) as Hcd.
    inversion Hl as [n U ip Δ0 ? ? A0 B0 Hn Hm | fp U ip Δ0 ? ? A0 B0 Hf Hm]; subst.
    - (* a member of an open frame *)
      pose proof (stack_rscoped _ _ HΞ _ _ Hn) as Hrs.
      set (cs := List.length (gu_params U) :: gs_cs (List.skipn (S n) Ξ)).
      destruct (chainT Θ Ξ _ _ _ _ Hm (gs_canon_nth _ _ _ Hcs Hn) _ _ _ _ eq_refl cs ltac:(unfold cs; congruence)
                  ltac:(intros; eapply gm_rscoped_find; eassumption))
        as (y & Ar & Br & θ & csf & pos & -> & -> & HsA & HsB & Hcsf & Hbθ & Hip1 & Hip2 & Hlpos & Hpos & Hdyn).
      assert (Hfr : frame_at Θ Ξ (me_addr (me_base n)) = Some (gu_params U, gu_mod U))
        by (unfold frame_at; cbn; rewrite Hn; reflexivity).
      destruct (Hdyn _ _ _ Hfr ltac:(intros; reflexivity)) as [Hpart Hmain].
      assert (Hglob : forall r ρ, eval_ent Θ Ξ (me_base n) ip r -> ⟦ a_glob (p_rel n ip) ⟧ me_top ⍮ ρ ↘ r)
        by (intros * Hr; constructor; rewrite me_drop_base, Nat.add_0_r; exact Hr).
      exists y, Ar, Br, (ts_comp θ (ts_ms (↑ₘ n))), csf,
        (List.map (fun e => match e with (R, θi, nR, csR) => (R, ts_comp θi (ts_ms (↑ₘ n)), nR, csR) end) pos).
      split; [ rewrite exp_tsub_ms, exp_tsub_comp; reflexivity |].
      split; [ rewrite opt_tsub_ms, opt_tsub_comp; reflexivity |].
      do 2 (split; [ assumption |]).
      rewrite ctx_msub_length.
      split; [ rewrite List.length_map; assumption |].
      split.
      { intros i e Hie; rewrite List.nth_error_map in Hie.
        destruct (List.nth_error pos i) as [[[[R θi] nR] csR] |] eqn:HR; cbn in Hie; [| discriminate ].
        injection Hie as <-.
        destruct (Hpos _ _ HR) as (T & HT & HTok); cbn in HTok; destruct HTok as (-> & HsR & _).
        exists (exp_tsub (ts_ms (↑ₘ n)) (exp_tsub θi R)); split.
        - rewrite (ctx_msub_nth _ _ _ _ HT), exp_tsub_ms.
          f_equal; apply exp_tsub_ext, ts_ms_eq, ms_qn_shift.
        - cbn; split; [ rewrite exp_tsub_comp; reflexivity | assumption ]. }
      split.
      { intros cs' Hl'; destruct (Hpart _ Hl') as (v & r & Hr & Hv).
        exists v, r; split; [ intros; apply Hglob, Hr | exact Hv ]. }
      intros args Hla.
      destruct (Hmain _ Hla) as (κf & Δf & Φf & rconf & Hff & Hfy & Hres & Hcf & Hpath & Hdepth & Hlrc & Hconf & Hgne).
      exists κf, Δf, Φf, rconf; split; [ assumption |]; split; [ assumption |].
      split; [ intros v Hv; destruct (Hres _ Hv) as (r & Hr & Hv'); exists r; split; [ intros; apply Hglob, Hr | exact Hv' ] |].
      split.
      { eapply cfg_eq_comp; [ apply (cfg_eq_shift _ _ _ (List.length Δ0) (param_ok cs) (path_ok cs)) | exact Hcf | intros; lia | exact Hip1 | exact Hip2 ]. }
      split; [ rewrite Hpath; reflexivity |].
      split; [ assumption |].
      split.
      { intros i e rc Hie Hrc; rewrite List.nth_error_map in Hie.
        destruct (List.nth_error pos i) as [[[[R θi] nR] csR] |] eqn:HR; cbn in Hie; [| discriminate ].
        injection Hie as <-.
        destruct rc as [κi ρi].
        specialize (Hconf _ _ _ HR Hrc); cbn in Hconf |- *; destruct Hconf as [HlR Hcfi].
        destruct (Hpos _ _ HR) as (T & HT & HTok); cbn in HTok; destruct HTok as (_ & _ & _ & Hv & Hp & Hg').
        split; [ assumption |].
        eapply cfg_eq_comp; [ apply (cfg_eq_shift _ _ _ i (param_ok cs) (path_ok cs)) | exact Hcfi | exact Hv | exact Hp | exact Hg' ]. }
      intros tys Hlt Hty.
      apply Hgne; [ constructor | assumption |].
      intros i e rc ty Hie Hrc Hty0.
      destruct e as [[[R θi] nR] csR].
      exact (Hty i (R, ts_comp θi (ts_ms (↑ₘ n)), nR, csR) rc ty ltac:(rewrite List.nth_error_map, Hie; reflexivity) Hrc Hty0).
    - (* a member of a filed unit *)
      pose proof (deps_rscoped _ (wf_gstack_deps _ _ HΞ) _ _ Hf) as Hrs.
      assert (HsT : ctx_scoped 0 nil (gu_params U)).
      { destruct wf_scoped as (_ & _ & _ & _ & _ & _ & _ & _ & Hu & _).
        destruct (Hu _ (wf_gstack_deps _ _ HΞ) _ _ Hf) as [H _]; exact H. }
      set (c := List.length (gu_params U)).
      destruct (chainT Θ Ξ _ _ _ _ Hm (gds_lookup_canon _ _ _ Hcd Hf) _ _ _ _ eq_refl (c :: nil) ltac:(congruence)
                  ltac:(intros; eapply gm_rscoped_find; eassumption))
        as (y & Ar & Br & θ & csf & pos & -> & -> & HsA & HsB & Hcsf & Hbθ & Hip1 & Hip2 & Hlpos & Hpos & Hdyn).
      assert (Hfr : forall argsT, frame_at Θ Ξ (me_addr (me_frame (p_abs fp nil) argsT (me_base 0))) = Some (gu_params U, gu_mod U))
        by (intros; unfold frame_at; cbn; rewrite Hf; reflexivity).
      assert (Hglob : forall r ρ, eval_pend Θ Ξ (me_base 0) (p_abs fp nil) c nil ip r ->
                        ⟦ a_glob (p_abs fp ip) ⟧ me_top ⍮ ρ ↘ r)
        by (intros * Hr; econstructor; eassumption).
      set (n := List.length Δ0).
      exists y, Ar, Br, (ts_comp θ (ts_ms (ms_close (p_abs fp nil) c n))), csf,
        (tele_pos nil 0 (List.rev (gu_params U)) ++
         lift_with (fun i => ts_ms (ms_close (p_abs fp nil) c i)) 0 pos).
      assert (Hltot : List.length (Δ0[close (p_abs fp nil) c]ᵐ ++ gu_params U) = n + c)
        by (rewrite List.length_app, ctx_msub_length; reflexivity).
      rewrite Hltot.
      assert (Hnthc : forall i e, List.nth_error (lift_with (fun i => ts_ms (ms_close (p_abs fp nil) c i)) 0 pos) i = Some e ->
                  exists R θi nR csR, List.nth_error pos i = Some (R, θi, nR, csR) /\
                    e = (R, ts_comp θi (ts_ms (ms_close (p_abs fp nil) c i)), nR, csR)).
      { intros i e H; destruct (lift_with_nth _ _ _ _ _ H) as (R & θi & nR & csR & HR & ->); do 4 eexists; split; [ exact HR | reflexivity ]. }
      assert (Hnthc' : forall i R θi nR csR, List.nth_error pos i = Some (R, θi, nR, csR) ->
                  List.nth_error (lift_with (fun i => ts_ms (ms_close (p_abs fp nil) c i)) 0 pos) i = Some (R, ts_comp θi (ts_ms (ms_close (p_abs fp nil) c i)), nR, csR)).
      { intros * H; exact (lift_with_nth' _ 0 _ _ _ _ _ _ H). }
      split; [ rewrite exp_tsub_ms, exp_tsub_comp; reflexivity |].
      split; [ rewrite opt_tsub_ms, opt_tsub_comp; reflexivity |].
      do 2 (split; [ assumption |]).
      split; [ rewrite List.length_app, tele_pos_length, lift_with_length, List.length_rev; fold c n; lia |].
      split.
      { intros i e Hie.
        destruct (Nat.lt_ge_cases i c) as [Hic | Hic].
        - rewrite List.nth_error_app1 in Hie by (rewrite tele_pos_length, List.length_rev; fold c; lia).
          destruct (tele_pos_nth _ _ _ _ _ Hie) as (T & HT & ->); cbn [Nat.add] in *.
          rewrite nth_error_rev_tele in HT by (fold c; lia); fold c in HT.
          exists T; split.
          + rewrite List.nth_error_app2 by (rewrite ctx_msub_length; fold n; lia).
            rewrite ctx_msub_length; fold n; replace (n + c - S i - n) with (c - S i) by lia; exact HT.
          + cbn; split; [ symmetry; apply exp_tsub_id |].
            pose proof (ctx_scoped_nth _ _ _ _ HsT HT) as H; fold c in H; replace (c - S (c - S i)) with i in H by lia; exact H.
        - rewrite List.nth_error_app2 in Hie by (rewrite tele_pos_length, List.length_rev; fold c; lia).
          rewrite tele_pos_length, List.length_rev in Hie; fold c in Hie.
          destruct (Hnthc _ _ Hie) as (R & θi & nR & csR & HR & ->).
          destruct (Hpos _ _ HR) as (Tin & HTin & HTok); cbn in HTok.
          destruct HTok as (-> & HsR & _).
          assert (Hin_n0 : i - c < List.length pos) by (apply List.nth_error_Some; congruence).
          assert (Hin_n : i - c < n) by (unfold n, c in *; lia).
          exists (exp_tsub (ts_ms (ms_close (p_abs fp nil) c (i - c))) (exp_tsub θi R)); split.
          + rewrite List.nth_error_app1 by (rewrite ctx_msub_length; fold n; lia).
            replace (n + c - S i) with (n - S (i - c)) by lia.
            rewrite (ctx_msub_nth _ _ _ _ HTin), exp_tsub_ms.
            replace (List.length Δ0 - S (n - S (i - c))) with (i - c) by (unfold n, c in *; lia).
            replace (List.length Δ0 - S (List.length Δ0 - S (i - c))) with (i - c) by (unfold n, c in *; lia).
            f_equal; apply exp_tsub_ext, ts_ms_eq.
            pose proof (ms_qn_close (i - c) (p_abs fp nil) c 0) as Hq; rewrite Nat.add_0_r in Hq; exact Hq.
          + cbn; split; [ rewrite exp_tsub_comp; reflexivity | assumption ]. }
      split.
      { intros cs' Hl'.
        destruct (Nat.lt_ge_cases (List.length cs') c) as [Hlt | Hge].
        - destruct (pend_partial Θ Ξ (me_base 0) (p_abs fp nil) c ip cs' nil ltac:(cbn; lia)) as (r & v & Hr & Hv).
          exists v, r; split; [ intros; apply Hglob, Hr | exact Hv ].
        - destruct (proj1 (Hdyn _ _ _ (Hfr (List.rev (List.firstn c cs'))) ltac:(intros; reflexivity))
                       (List.skipn c cs') ltac:(rewrite List.length_skipn; fold n; lia)) as (v & Hv).
          destruct (pend_feed Θ Ξ (me_base 0) (p_abs fp nil) c ip (List.firstn c cs') nil (List.skipn c cs') v
                      ltac:(rewrite List.length_firstn; cbn; lia)
                      ltac:(rewrite List.app_nil_r; exact Hv)) as (r & Hr & Hv').
          rewrite List.firstn_skipn in Hv'.
          exists v, r; split; [ intros; apply Hglob, Hr | exact Hv' ]. }
      intros args Hla.
      set (argsT := List.firstn c args).
      set (argsin := List.skipn c args).
      assert (HlT : List.length argsT = c) by (unfold argsT; rewrite List.length_firstn; lia).
      assert (Hlin : List.length argsin = n) by (unfold argsin; rewrite List.length_skipn; fold n; lia).
      assert (Hsplit : args = argsT ++ argsin) by (unfold argsT, argsin; symmetry; apply List.firstn_skipn).
      destruct (proj2 (Hdyn _ _ _ (Hfr (List.rev argsT)) ltac:(intros; reflexivity)) argsin Hlin)
        as (κf & Δf & Φf & rconfin & Hff & Hfy & Hres & Hcf & Hpath & Hdepth & Hlrc & Hconf & Hgne).
      exists κf, Δf, Φf, (List.map (fun j => (me_base 0, List.rev (List.firstn j argsT))) (List.seq 0 c) ++ rconfin).
      split; [ assumption |]; split; [ assumption |].
      split.
      { intros v Hv; destruct (Hres v Hv) as (r0 & Hr0 & Hv0).
        destruct (pend_feed Θ Ξ (me_base 0) (p_abs fp nil) c ip argsT nil argsin v
                    ltac:(cbn; lia) ltac:(rewrite List.app_nil_r; exists r0; split; assumption)) as (r & Hr & Hv').
        rewrite <- Hsplit in Hv'.
        exists r; split; [ intros; apply Hglob, Hr | exact Hv' ]. }
      split.
      { rewrite Hsplit, List.rev_app_distr.
        pose proof (cfg_eq_close_abs Θ Ξ fp U (List.rev argsT) (List.rev argsin) Hf
                      ltac:(rewrite List.length_rev; assumption)) as Hν.
        rewrite List.length_rev, Hlin in Hν.
        eapply cfg_eq_comp; [ exact Hν | exact Hcf | intros; lia | |].
        - intros lp Hlp; eapply exp_ok_PQ; [ apply Hip1; exact Hlp | | ].
          + intros [m k] (c' & Hc0 & Hk) Hm0; cbn in Hm0, Hc0 |- *; rewrite Hm0 in Hc0; injection Hc0 as <-; exact Hk.
          + intros [[fq | m] ms] Hq; cbn in *; auto; lia.
        - intros p Hp; eapply exp_ok_PQ; [ apply Hip2; exact Hp | | ].
          + intros [m k] (c' & Hc0 & Hk) Hm0; cbn in Hm0, Hc0 |- *; rewrite Hm0 in Hc0; injection Hc0 as <-; exact Hk.
          + intros [[fq | m] ms] Hq; cbn in *; auto; lia. }
      split; [ rewrite Hpath; reflexivity |].
      split; [ rewrite List.length_app, List.length_map, List.length_seq; lia |].
      split.
      { intros i e rc Hie Hrc.
        destruct (Nat.lt_ge_cases i c) as [Hic | Hic].
        - rewrite List.nth_error_app1 in Hie by (rewrite tele_pos_length, List.length_rev; fold c; lia).
          rewrite List.nth_error_app1 in Hrc by (rewrite List.length_map, List.length_seq; lia).
          destruct (tele_pos_nth _ _ _ _ _ Hie) as (T & HT & ->); cbn [Nat.add] in *.
          rewrite nth_map_seq in Hrc by lia; injection Hrc as <-; cbn.
          split; [ rewrite List.length_rev, List.length_firstn; lia |].
          rewrite Hsplit, firstn_app_le by lia; apply cfg_eq_id.
        - rewrite List.nth_error_app2 in Hie by (rewrite tele_pos_length, List.length_rev; fold c; lia).
          rewrite List.nth_error_app2 in Hrc by (rewrite List.length_map, List.length_seq; lia).
          rewrite tele_pos_length, List.length_rev in Hie; fold c in Hie; rewrite List.length_map, List.length_seq in Hrc.
          destruct (Hnthc _ _ Hie) as (R & θi & nR & csR & HR & ->).
          destruct rc as [κi ρi].
          specialize (Hconf _ _ _ HR Hrc); cbn in Hconf; destruct Hconf as [HlR Hcfi].
          destruct (Hpos _ _ HR) as (Tin & HTin & HTok); cbn in HTok.
          destruct HTok as (_ & HsR & Hbi & Hv & Hp & Hg').
          assert (Hin_n0 : i - c < List.length pos) by (apply List.nth_error_Some; congruence).
          cbn; split; [ assumption |].
          rewrite Hsplit, firstn_app_ge by lia; rewrite HlT, List.rev_app_distr.
          pose proof (cfg_eq_close_abs Θ Ξ fp U (List.rev argsT) (List.rev (List.firstn (i - c) argsin)) Hf
                        ltac:(rewrite List.length_rev; assumption)) as Hν.
          assert (Hin_n : i - c <= List.length argsin) by (rewrite Hlin; unfold n, c in *; lia).
          rewrite List.length_rev, List.length_firstn, Nat.min_l in Hν by exact Hin_n.
          eapply cfg_eq_comp; [ exact Hν | exact Hcfi | | |].
          + intros x0 Hx0; eapply exp_ok_PQ; [ apply Hv; exact Hx0 | | ].
            * intros [m k] (c' & Hc0 & Hk) Hm0; cbn in Hm0, Hc0 |- *; rewrite Hm0 in Hc0; injection Hc0 as <-; exact Hk.
            * intros [[fq | m] ms] Hq; cbn in *; auto; lia.
          + intros lp Hlp; eapply exp_ok_PQ; [ apply Hp; exact Hlp | | ].
            * intros [m k] (c' & Hc0 & Hk) Hm0; cbn in Hm0, Hc0 |- *; rewrite Hm0 in Hc0; injection Hc0 as <-; exact Hk.
            * intros [[fq | m] ms] Hq; cbn in *; auto; lia.
          + intros p Hp0; eapply exp_ok_PQ; [ apply Hg'; exact Hp0 | | ].
            * intros [m k] (c' & Hc0 & Hk) Hm0; cbn in Hm0, Hc0 |- *; rewrite Hm0 in Hc0; injection Hc0 as <-; exact Hk.
            * intros [[fq | m] ms] Hq; cbn in *; auto; lia. }
      intros tys Hlt Hty.
      set (tysT := List.firstn c tys).
      set (tysin := List.skipn c tys).
      assert (HltT : List.length tysT = c) by (unfold tysT; rewrite List.length_firstn; lia).
      assert (Hltin : List.length tysin = n) by (unfold tysin; rewrite List.length_skipn; fold n; lia).
      assert (Hg1 : eval_gne Θ Ξ (me_frame (p_abs fp nil) (List.rev argsT) (me_base 0))
                      (addr_depth (me_addr (me_frame (p_abs fp nil) (List.rev argsT) (me_base 0))))
                      (d_glob (p_abs fp ip)) (napp (d_glob (p_abs fp ip)) tysT argsT)).
      { cbn [me_addr addr_depth p_mems p_qual List.length Nat.add].
        econstructor; [ constructor | unfold frame_at; cbn; rewrite Hf; reflexivity |].
        apply fargs_napp; [ assumption | assumption |].
        intros j T ty HT Hty0.
        assert (Hj : j < c) by (assert (Hn0 : List.nth_error tysT j <> None) by congruence; apply List.nth_error_Some in Hn0; lia).
        apply (Hty j (T, ts_id, j, nil) (me_base 0, List.rev (List.firstn j argsT)) ty).
        - rewrite List.nth_error_app1 by (rewrite tele_pos_length, List.length_rev; fold c; lia).
          clear - Hj HT.
          assert (H : forall l k j T, List.nth_error l j = Some T -> List.nth_error (tele_pos nil k l) j = Some (T, ts_id, k + j, nil)).
          { induction l as [| T0 l IHl]; intros k [| j0] T0' H; cbn in *; try discriminate.
            - injection H as <-; rewrite Nat.add_0_r; reflexivity.
            - rewrite (IHl _ _ _ H); replace (S k + j0) with (k + S j0) by lia; reflexivity. }
          apply (H _ 0 j T); rewrite nth_error_rev_tele by (fold c; lia); exact HT.
        - rewrite List.nth_error_app1 by (rewrite List.length_map, List.length_seq; lia).
          rewrite nth_map_seq by lia; reflexivity.
        - unfold tysT in Hty0; rewrite List.nth_error_firstn in Hty0.
          destruct (Nat.ltb_spec j c); [ exact Hty0 | lia ]. }
      pose proof (Hgne _ _ tysin Hg1 Hltin) as Hgin.
      assert (Htys : tys = tysT ++ tysin) by (unfold tysT, tysin; symmetry; apply List.firstn_skipn).
      rewrite Hsplit; rewrite Htys at 1; rewrite (napp_app tysT argsT tysin argsin) by lia.
      rewrite Htys in Hty.
      apply Hgin.
      intros i e rc ty Hie Hrc Hty0.
      destruct e as [[[R θi] nR] csR]; destruct rc as [κi ρi].
      assert (H1 : List.nth_error (tele_pos nil 0 (List.rev (gu_params U)) ++
                     lift_with (fun i => ts_ms (ms_close (p_abs fp nil) c i)) 0 pos) (c + i) =
                     Some (R, ts_comp θi (ts_ms (ms_close (p_abs fp nil) c i)), nR, csR)).
      { rewrite List.nth_error_app2 by (rewrite tele_pos_length, List.length_rev; fold c; lia).
        rewrite tele_pos_length, List.length_rev; fold c; rewrite Nat.add_comm, Nat.add_sub.
        apply Hnthc'; exact Hie. }
      assert (H2 : List.nth_error (List.map (fun j => (me_base 0, List.rev (List.firstn j argsT))) (List.seq 0 c) ++ rconfin) (c + i) = Some (κi, ρi)).
      { rewrite List.nth_error_app2 by (rewrite List.length_map, List.length_seq; lia).
        rewrite List.length_map, List.length_seq, Nat.add_comm, Nat.add_sub; exact Hrc. }
      assert (H3 : List.nth_error (tysT ++ tysin) (c + i) = Some ty).
      { rewrite List.nth_error_app2 by lia; rewrite HltT, Nat.add_comm, Nat.add_sub; exact Hty0. }
      exact (Hty _ _ _ _ H1 H2 H3).
  Qed.
End TopT.

Lemma list_choice : forall {A} (P : nat -> A -> Prop) n,
    (forall i, i < n -> exists x, P i x) ->
    exists l, List.length l = n /\ forall i x, List.nth_error l i = Some x -> P i x.
Proof.
  intros A P n; induction n as [| n IH]; intros H.
  - exists nil; split; [ reflexivity | intros [] ? ?; discriminate ].
  - destruct (IH ltac:(intros; apply H; lia)) as (l & Hl & Hp).
    destruct (H n ltac:(lia)) as [x Hx].
    exists (l ++ x :: nil); split; [ rewrite List.length_app; cbn; lia |].
    intros i y Hy.
    destruct (Nat.lt_ge_cases i n) as [Hi | Hi].
    + rewrite List.nth_error_app1 in Hy by lia; auto.
    + rewrite List.nth_error_app2 in Hy by lia.
      destruct (i - List.length l) as [| k] eqn:Hk; cbn in Hy; [| destruct k; discriminate ].
      injection Hy as <-; replace i with n by lia; exact Hx.
Qed.

Section Neut.
  Variables (Θ : gdeps) (Ξ : gstack).

  #[local] Notation "'⟦' M '⟧' κ '⍮' ρ '↘' r" := (eval_exp Θ Ξ κ M ρ r)
    (at level 70, M at level 69, κ at level 69, ρ at level 69, r at level 69).

  (** A neutral at a telescope type, applied: the head applied to the
      arguments at the telescope's types. *)
  Lemma apps_neut : forall Δ A κ ρ0 t h cs v,
      List.length cs = List.length Δ ->
      ⟦ ctx_pi Δ A ⟧ κ ⍮ ρ0 ↘ t -> apps Θ Ξ (⇑ t h) cs v ->
      exists a tls, v = ⇑ a (napp h tls cs) /\ ⟦ A ⟧ κ ⍮ List.rev cs ++ ρ0 ↘ a /\
        List.length tls = List.length Δ /\
        forall i T tl, List.nth_error Δ (List.length Δ - S i) = Some T -> List.nth_error tls i = Some tl ->
          ⟦ T ⟧ κ ⍮ List.rev (List.firstn i cs) ++ ρ0 ↘ tl.
  Proof.
    induction Δ as [| T Δ IH] using List.rev_ind; intros * Hl Ht Hv.
    - destruct cs; [| discriminate ]; inversion Hv; subst.
      exists t, nil; repeat split; [ exact Ht | intros ? ? ? H; destruct (List.length _ - _); discriminate ].
    - rewrite List.length_app in Hl; cbn in Hl.
      destruct cs as [| c cs]; [ cbn in Hl; lia |].
      rewrite ctx_pi_snoc in Ht; inversion Ht; subst.
      inversion Hv as [| ? ? ? fc ? Hfc Hrest]; subst.
      inversion Hfc; subst.
      destruct (IH A κ (c :: ρ0) _ _ cs v ltac:(cbn in Hl; lia) ltac:(eassumption) Hrest) as (a' & tls & -> & Ha' & Hlt & Htl).
      exists a', (a :: tls); split; [ reflexivity |].
      split; [ cbn; rewrite <- List.app_assoc; exact Ha' |].
      split; [ rewrite List.length_app; cbn; lia |].
      intros [| i] T' tl HT' Htl'; cbn in Htl'.
      + injection Htl' as <-.
        rewrite List.length_app, Nat.add_comm in HT'; cbn in HT'; rewrite Nat.sub_0_r in HT'.
        rewrite List.nth_error_app2, Nat.sub_diag in HT' by lia; cbn in HT'; injection HT' as <-.
        cbn; assumption.
      + rewrite List.length_app, Nat.add_comm in HT'; cbn in HT'.
        assert (Hi : i < List.length Δ) by (assert (Hn0 : List.nth_error tls i <> None) by congruence; apply List.nth_error_Some in Hn0; lia).
        rewrite List.nth_error_app1 in HT' by lia.
        cbn; rewrite <- List.app_assoc; apply Htl; assumption.
  Qed.

  Lemma nsim_napp : forall tls tys cs h h',
      nsim Θ Ξ h h' -> List.length tls = List.length tys ->
      (forall i tl ty, List.nth_error tls i = Some tl -> List.nth_error tys i = Some ty -> vsim Θ Ξ tl ty) ->
      nsim Θ Ξ (napp h tls cs) (napp h' tys cs).
  Proof.
    induction tls as [| tl tls IH]; intros [| ty tys] [| c cs] * Hh Hl Hv; cbn in *; try lia; auto.
    apply IH; [ apply ns_app; [ exact Hh | apply (Hv 0); reflexivity | apply vs_refl ] | lia |].
    intros i; apply (Hv (S i)).
  Qed.
End Neut.

(** ** The bridges, independently of a model *)

Section Bridges.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢g Θ ⍮ Ξ.

  #[local] Notation "'⟦' M '⟧' κ '⍮' ρ '↘' r" := (eval_exp Θ Ξ κ M ρ r)
    (at level 70, M at level 69, κ at level 69, ρ at level 69, r at level 69).

  (** δ: the raw global is applicatively simulated by the transformed body. *)
  Lemma glob_delta_appsim : forall p Δ pv A M n0,
      Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def true pv A (Some M) ->
      ⟦ ctx_fn Δ M ⟧ me_top ⍮ nil ↘ n0 ->
      exists g, (forall ρ, ⟦ a_glob p ⟧ me_top ⍮ ρ ↘ g) /\ appsim Θ Ξ (List.length Δ) n0 g.
  Proof.
    intros * Hl Hn0.
    destruct (top_chain Θ Ξ _ _ _ _ _ _ Hg Hl)
      as (y & Ar & Br & θ & csf & HA & HB & HsA & HsB & Hpart & Hmain).
    destruct Br as [Mr |]; cbn in HB; [ injection HB as HMr | discriminate ].
    assert (Hfull : forall cs v, List.length cs = List.length Δ ->
               ⟦ M ⟧ me_top ⍮ List.rev cs ↘ v ->
               exists v', gres Θ Ξ p cs v' /\ vsim Θ Ξ v v').
    { intros cs v Hlc Hv.
      destruct (Hmain _ Hlc) as (κf & Δf & Φf & Hff & Hfy & Hres & Hcf).
      rewrite HMr in Hv.
      destruct (sim_eval_exp _ _ _ _ _ _ _ _ _ _ _ _ Hv (exp_scoped_ok_cs _ _ _ HsB) (cfg_eq_cfg _ _ _ _ _ _ _ _ _ _ Hcf))
        as (v' & Hv' & Hs).
      exists v'; split; [ apply Hres; eapply eval_ent_delta; eassumption | exact Hs ]. }
    assert (Hg0 : exists g, forall ρ, ⟦ a_glob p ⟧ me_top ⍮ ρ ↘ g).
    { destruct Δ as [| T Δ'] eqn:HΔ.
      - destruct (Hfull nil n0 eq_refl Hn0) as (v' & (g & Hg' & _) & _); eauto.
      - destruct (Hpart nil ltac:(cbn; lia)) as (v & g & Hg' & _); eauto. }
    destruct Hg0 as [g Hgv]; exists g; split; [ exact Hgv |].
    split.
    - intros cs v Hlc Hv.
      pose proof (apps_ctx_fn _ _ _ _ _ _ _ _ _ Hlc Hn0 Hv) as Hv'.
      rewrite List.app_nil_r in Hv'.
      destruct (Hfull _ _ Hlc Hv') as (v'' & Hres & Hs).
      exists v''; split; [ eapply gres_det; eassumption | exact Hs ].
    - intros cs Hlc; destruct (Hpart _ Hlc) as (v & Hres).
      exists v; eapply gres_det; eassumption.
  Qed.

  (** An opaque definition or an axiom: the raw global is applicatively
      simulated by the neutral at the transformed type. *)
  Lemma glob_neut_appsim : forall p Δ b pv A B t,
      Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B -> b = false \/ B = None ->
      ⟦ ctx_pi Δ A ⟧ me_top ⍮ nil ↘ t ->
      exists g, (forall ρ, ⟦ a_glob p ⟧ me_top ⍮ ρ ↘ g) /\ appsim Θ Ξ (List.length Δ) (⇑ t (d_glob p)) g.
  Proof.
    intros * Hl Hop Ht.
    destruct (top_chainT Θ Ξ _ _ _ _ _ _ Hg Hl)
      as (y & Ar & Br & θ & csf & pos & HA & HB & HsA & HsB & Hlpos & Hpos & Hpart & Hmain).
    set (f := ⇑ t (d_glob p)).
    assert (Hfull : forall cs v, List.length cs = List.length Δ -> apps Θ Ξ f cs v ->
               exists v', gres Θ Ξ p cs v' /\ vsim Θ Ξ v v').
    { intros cs v Hlc Hv.
      destruct (apps_neut _ _ _ _ _ _ _ _ _ _ Hlc Ht Hv) as (a & tls & -> & Ha & Hltls & Htls).
      rewrite List.app_nil_r in Ha.
      destruct (Hmain _ Hlc) as (κf & Δf & Φf & rconf & Hff' & Hfy & Hres & Hcf & Hpath & Hlrc & Hconf & Hgne).
      rewrite HA in Ha.
      destruct (sim_eval_exp _ _ _ _ _ _ _ _ _ _ _ _ Ha (exp_scoped_ok_cs _ _ _ HsA) (cfg_eq_cfg _ _ _ _ _ _ _ _ _ _ Hcf))
        as (ar & Har & Hsa).
      assert (Hty : forall j, j < List.length Δ -> exists ty,
                 forall e rc, List.nth_error pos j = Some e -> List.nth_error rconf j = Some rc ->
                   ty_ok Θ Ξ e rc ty /\ forall tl, List.nth_error tls j = Some tl -> vsim Θ Ξ tl ty).
      { intros j Hj.
        destruct (List.nth_error pos j) as [[[[R θj] nR] csR] |] eqn:He;
          [| apply List.nth_error_None in He; lia ].
        destruct (List.nth_error rconf j) as [[κj ρj] |] eqn:Hrc;
          [| apply List.nth_error_None in Hrc; lia ].
        destruct (List.nth_error tls j) as [tl |] eqn:Htl;
          [| apply List.nth_error_None in Htl; lia ].
        destruct (Hpos _ _ He) as (T & HT' & HTok); cbn in HTok; destruct HTok as (-> & HsR).
        specialize (Hconf _ _ _ He Hrc); cbn in Hconf; destruct Hconf as [HlR Hcfj].
        pose proof (Htls _ _ _ HT' Htl) as Htl'; rewrite List.app_nil_r in Htl'.
        destruct (sim_eval_exp _ _ _ _ _ _ _ _ _ _ _ _ Htl' (exp_scoped_ok_cs _ _ _ HsR) (cfg_eq_cfg _ _ _ _ _ _ _ _ _ _ Hcfj))
          as (ty & Hty & Hsty).
        exists ty; intros e rc He' Hrc'.
        injection He' as <-; injection Hrc' as <-; cbn; split; [ exact Hty |].
        intros tl' Htl''; injection Htl'' as <-; exact Hsty. }
      destruct (list_choice _ _ Hty) as (tys & Hltys & Htys).
      assert (Hgn : eval_gne Θ Ξ κf (addr_depth (me_addr κf)) (d_glob p) (napp (d_glob p) tys cs)).
      { apply Hgne; [ assumption |].
        intros i0 e rc ty He Hrc Hty0; exact (proj1 (Htys _ _ Hty0 _ _ He Hrc)). }
      exists (⇑ ar (napp (d_glob p) tys cs)); split.
      - apply Hres; eapply eval_ent_neut; [ eassumption | eassumption | | eassumption |].
        + destruct Hop as [-> | ->]; [ left; reflexivity | right; destruct Br; cbn in HB; [ discriminate | reflexivity ] ].
        + rewrite Hpath; exact Hgn.
      - apply vs_neut; [ exact Hsa |].
        apply nsim_napp; [ apply ns_refl | lia |].
        intros j tl ty Htl Hty0.
        assert (Hj : j < List.length Δ) by (assert (Hn0 : List.nth_error tys j <> None) by congruence; apply List.nth_error_Some in Hn0; lia).
        destruct (List.nth_error pos j) as [e |] eqn:He; [| apply List.nth_error_None in He; lia ].
        destruct (List.nth_error rconf j) as [rc |] eqn:Hrc; [| apply List.nth_error_None in Hrc; lia ].
        exact (proj2 (Htys _ _ Hty0 _ _ He Hrc) _ Htl). }
    assert (Hg0 : exists g, forall ρ, ⟦ a_glob p ⟧ me_top ⍮ ρ ↘ g).
    { destruct Δ as [| T Δ'] eqn:HΔ.
      - destruct (Hfull nil f eq_refl (apps_nil _ _ _)) as (v' & (g & Hg' & _) & _); eauto.
      - destruct (Hpart nil ltac:(cbn; lia)) as (v & g & Hg' & _); eauto. }
    destruct Hg0 as [g Hgv]; exists g; split; [ exact Hgv |].
    split.
    - intros cs v Hlc Hv.
      destruct (Hfull _ _ Hlc Hv) as (v'' & Hres & Hs).
      exists v''; split; [ eapply gres_det; eassumption | exact Hs ].
    - intros cs Hlc; destruct (Hpart _ Hlc) as (v & Hres).
      exists v; eapply gres_det; eassumption.
  Qed.

  (** A parameter of an open frame, given its type and those of the parameters
      bound before it evaluate at the top level. *)
  Lemma param_raw : forall n U k T,
      List.nth_error Ξ n = Some U -> gu_params U ∋ #k : T ->
      (forall k' T', k <= k' -> gu_params U ∋ #k' : T' ->
         exists t, ⟦ T'[↑ₘ (S n)]ᵐ[sb_params n] ⟧ me_top ⍮ nil ↘ t) ->
      exists a, (forall ρ, ⟦ $[n, k] ⟧ me_top ⍮ ρ ↘ ⇑ a (d_param (lp_mk n k))) /\
        forall t, ⟦ T[↑ₘ (S n)]ᵐ[sb_params n] ⟧ me_top ⍮ nil ↘ t -> vsim Θ Ξ t a.
  Proof.
    intros n U k T Hn Hk Hall.
    assert (Hb : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    assert (Hsc : gs_scoped Ξ) by (destruct wf_scoped as [Hc _]; apply (Hc _ _ _ Hb)).
    destruct (gs_scoped_nth _ _ _ Hsc Hn) as [HPs _].
    pose proof (ctx_lookup_length _ _ _ Hk) as Hkl.
    destruct (ctx_lookup_nth _ _ _ Hk) as (A & HA & ->).
    assert (Hev : forall k' A', k <= k' -> List.nth_error (gu_params U) k' = Some A' ->
                    exists t, eval_exp Θ Ξ me_top (exp_tsub (θp n k') A') nil t).
    { intros k' A' Hle HA'.
      destruct (ctx_lookup_exists (gu_params U) k' ltac:(apply List.nth_error_Some; congruence)) as [T' Hk'].
      destruct (ctx_lookup_nth _ _ _ Hk') as (A'' & HA'' & ->).
      rewrite HA' in HA''; injection HA'' as <-.
      destruct (Hall _ _ Hle Hk') as [t Ht].
      rewrite param_type_tsub in Ht; eauto. }
    destruct (ptele_exists Θ Ξ _ _ _ Hn HPs (List.length (gu_params U) - k) k ltac:(lia) Hev) as [ρ Hρ].
    destruct (Hev k A (le_n _) HA) as [t0 Ht0].
    destruct (param_value Θ Ξ _ _ _ _ _ _ Hn HA (exp_scoped_ok _ _ _ (ctx_scoped_nth _ _ _ _ HPs HA)) Hρ Ht0)
      as (a & Ha & Hs).
    exists a; split.
    - intros ρ0; eapply eval_param_env; exact Ha.
    - intros t Ht; rewrite param_type_tsub in Ht.
      pose proof (functional_eval_exp _ _ _ _ _ Ht Ht0) as ->; exact Hs.
  Qed.
End Bridges.
