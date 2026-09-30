(** * Extension of the Global Context, and Monotonicity of Evaluation/Readback

    Experiment for approach Y: the resolution-preserving extensions
    (1) grow a frame and (4) file a unit at a level. *)

From Stdlib Require Import List String.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import GlobalCtx.
From Mctt.Core.Semantic Require Import Evaluation Readback.
Import Domain_Notations GlobalCtx_Notations.

(** ** The extension relation *)

Definition gc_ext_raw (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  (forall p r, gc_resolve Θ1 Ξ1 p = Some r -> gc_resolve Θ2 Ξ2 p = Some r) /\
  (forall lp T, gs_param Ξ1 lp = Some T -> gs_param Ξ2 lp = Some T).

Definition gc_ext (G1 G2 : GCtx) : Prop :=
  gc_ext_raw (@gc_deps G1) (@gc_stack G1) (@gc_deps G2) (@gc_stack G2).

Lemma gc_ext_refl : forall G, gc_ext G G.
Proof. intros G; split; auto. Qed.

Lemma gc_ext_trans : forall G1 G2 G3, gc_ext G1 G2 -> gc_ext G2 G3 -> gc_ext G1 G3.
Proof. intros * [? ?] [? ?]; split; auto. Qed.

(** ** The two steps produce extensions *)

(** (1) Growing a frame, in the general form of [gm_prefix] (which also covers
    growing a nested module that is still being filled).  Needs canonicity of
    the grown module, which well-formedness supplies ([wf_gmod_canon]). *)
Lemma gm_resolve_prefix : forall Φp Φ ip r,
    gm_prefix Φp Φ -> gm_canon Φ ->
    gm_resolve Φp ip = Some r -> gm_resolve Φ ip = Some r.
Proof.
  intros Φp Φ ip [Δ E] Hp Hc H.
  apply gm_resolve_complete; [| assumption ].
  eapply gm_prefix_lookup; [ eassumption | apply gm_resolve_sound; assumption ].
Qed.

Lemma ge_read_rel_some : forall n r r',
    ge_read_rel n r = Some r' -> exists r0, r = Some r0.
Proof. intros n [r |] r' H; [ eauto | discriminate ]. Qed.

Theorem gc_ext_grow : forall Θ Ξ Δ Φp Φ,
    gm_prefix Φp Φ -> gm_canon Φ ->
    gc_ext_raw Θ (gu_mk Δ Φp :: Ξ) Θ (gu_mk Δ Φ :: Ξ).
Proof.
  intros * Hp Hc; split.
  - intros [[fp | [| n]] ip] r; unfold gc_resolve; cbn; auto.
    destruct (gm_resolve Φp ip) as [r0 |] eqn:E0; [| discriminate ].
    rewrite (gm_resolve_prefix _ _ _ _ Hp Hc E0); auto.
  - intros [[| n] k] T; unfold gs_param; cbn; auto.
Qed.

(** The simplest grow: a fresh member at the end of the current frame. *)
Corollary gc_ext_grow_member : forall Θ Ξ Δ Φ x E,
    gm_canon (Φ ⊳ x ↦ E) ->
    gc_ext_raw Θ (gu_mk Δ Φ :: Ξ) Θ (gu_mk Δ (Φ ⊳ x ↦ E) :: Ξ).
Proof. intros; apply gc_ext_grow; eauto with mctt. Qed.

(** (4) Filing units at a new level, above the existing ones: the new keys must
    not already be filed (this is [gds_fresh], a premise of [wf_gdep_cons]). *)

Lemma gd_lookup_prepend : forall d d' fp U,
    ~ List.In fp (List.map fst d) ->
    gd_lookup d' fp = Some U ->
    gd_lookup (d ++ d') fp = Some U.
Proof.
  unfold gd_lookup, path_beq; induction d as [| [fq V] d IH]; cbn; intros * Hn H;
    [ assumption |].
  destruct (path_eq_dec fp fq) as [-> |]; [ exfalso; auto |].
  apply IH; auto.
Qed.

Lemma gd_lookup_some_in : forall d fp U, gd_lookup d fp = Some U -> List.In fp (List.map fst d).
Proof.
  intros * H%gd_lookup_in; apply (List.in_map fst _ _ H).
Qed.

Theorem gc_ext_file_level : forall Θ Ξ d,
    (forall fp, List.In fp (List.map fst d) -> gds_fresh fp Θ) ->
    gc_ext_raw Θ Ξ (d :: Θ) Ξ.
Proof.
  intros * Hfr; split; [| auto ].
  intros [[fp | n] ip] r; unfold gc_resolve; cbn; auto.
  destruct (gds_lookup Θ fp) as [U |] eqn:HU; [| discriminate ].
  unfold gds_lookup in *; cbn.
  rewrite (gd_lookup_prepend d (List.concat Θ) fp U); auto.
  intros Hin; specialize (Hfr _ Hin); unfold gds_fresh, gd_fresh in Hfr.
  exact (Hfr (gd_lookup_some_in _ _ _ HU)).
Qed.

(** Filing one more unit into the newest level (the level is consed in
    [wf_gdep_cons] order, newest first). *)
Theorem gc_ext_file_unit : forall d Θ Ξ fp U,
    gds_fresh fp (d :: Θ) ->
    gc_ext_raw (d :: Θ) Ξ (((fp, U) :: d) :: Θ) Ξ.
Proof.
  intros * Hfr; split; [| auto ].
  intros [[fq | n] ip] r; unfold gc_resolve; cbn; auto.
  destruct (gds_lookup (d :: Θ) fq) as [V |] eqn:HV; [| discriminate ].
  unfold gds_lookup in *; cbn in *.
  replace (gd_lookup ((fp, U) :: d ++ List.concat Θ) fq) with (Some V); auto.
  symmetry; apply (gd_lookup_prepend ((fp, U) :: nil) (d ++ List.concat Θ) fq V); auto.
  cbn; intros [<- | []]; unfold gds_fresh, gd_fresh in Hfr; cbn in Hfr.
  exact (Hfr (gd_lookup_some_in _ _ _ HV)).
Qed.

(** ** (a) Monotonicity of evaluation and readback *)

Section Mono.
  Variables (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack).
  Hypothesis Hext : gc_ext_raw Θ1 Ξ1 Θ2 Ξ2.

  Theorem eval_mono :
    (forall M ρ m, eval_exp Θ1 Ξ1 M ρ m -> eval_exp Θ2 Ξ2 M ρ m) /\
    (forall A MZ MS m ρ r, eval_natrec Θ1 Ξ1 A MZ MS m ρ r -> eval_natrec Θ2 Ξ2 A MZ MS m ρ r) /\
    (forall m n r, eval_app Θ1 Ξ1 m n r -> eval_app Θ2 Ξ2 m n r).
  Proof.
    destruct Hext as [Hr Hp].
    apply eval_mut_ind; intros; solve [econstructor; eauto].
  Qed.

  Corollary eval_exp_mono : forall M ρ m, eval_exp Θ1 Ξ1 M ρ m -> eval_exp Θ2 Ξ2 M ρ m.
  Proof. apply eval_mono. Qed.
  Corollary eval_natrec_mono : forall A MZ MS m ρ r,
      eval_natrec Θ1 Ξ1 A MZ MS m ρ r -> eval_natrec Θ2 Ξ2 A MZ MS m ρ r.
  Proof. apply eval_mono. Qed.
  Corollary eval_app_mono : forall m n r, eval_app Θ1 Ξ1 m n r -> eval_app Θ2 Ξ2 m n r.
  Proof. apply eval_mono. Qed.
  Corollary eval_sub_mono : forall σ ρ ρσ, eval_sub Θ1 Ξ1 σ ρ ρσ -> eval_sub Θ2 Ξ2 σ ρ ρσ.
  Proof. intros * H x; apply eval_exp_mono, H. Qed.

  Theorem read_mono :
    (forall s m M, read_nf Θ1 Ξ1 s m M -> read_nf Θ2 Ξ2 s m M) /\
    (forall s m M, read_ne Θ1 Ξ1 s m M -> read_ne Θ2 Ξ2 s m M) /\
    (forall s m M, read_typ Θ1 Ξ1 s m M -> read_typ Θ2 Ξ2 s m M).
  Proof.
    apply read_mut_ind; intros; econstructor;
      eauto using eval_exp_mono, eval_app_mono.
  Qed.

  Corollary read_nf_mono : forall s m M, read_nf Θ1 Ξ1 s m M -> read_nf Θ2 Ξ2 s m M.
  Proof. apply read_mono. Qed.
  Corollary read_ne_mono : forall s m M, read_ne Θ1 Ξ1 s m M -> read_ne Θ2 Ξ2 s m M.
  Proof. apply read_mono. Qed.
  Corollary read_typ_mono : forall s m M, read_typ Θ1 Ξ1 s m M -> read_typ Θ2 Ξ2 s m M.
  Proof. apply read_mono. Qed.

  (** Together with determinism at the bigger context, the result at the
      bigger context is *forced*: whatever it evaluates to there is what it
      evaluated to at the smaller one. *)
End Mono.
