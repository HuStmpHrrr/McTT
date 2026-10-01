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
From Mctt.Core.Syntactic Require Import System.
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
                intros [m k] (c' & Hc0 & Hk) Hm; cbn in *; subst; injection Hc0 as <-; exact Hk.
             ++ intros p Hp; eapply exp_ok_PQ; [ apply Hip2; exact Hp | | auto ].
                intros [m k] (c' & Hc0 & Hk) Hm; cbn in *; subst; injection Hc0 as <-; exact Hk.
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
