(** * Reading the Modules of a Global Context

    A body module is read in its body: its definitions and submodules are the
    entries of that body, at the module's telescope.  In a well-formed global
    context every entry is stored over the telescope of the module it is filed
    in ([gm_coh]): a definition's type is generalized over it, a submodule
    adds parameters to it, and an alias's parameters extend it. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export GlobalPresup.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Prefixes of Extended Paths *)

Lemma strip_prefix_snoc_inv : forall l m y r,
    strip_prefix l (m ++ y :: nil) = Some r ->
    (exists r', strip_prefix l m = Some r' /\ r = r' ++ y :: nil) \/ r = nil.
Proof.
  intros * H; apply strip_prefix_spec in H.
  destruct r as [| z r0] using rev_ind; [ right; reflexivity | left ].
  rewrite app_assoc in H; apply app_inj_tail in H as [-> ->].
  exists r0; split; [ apply strip_prefix_app | reflexivity ].
Qed.

Lemma strip_prefix_snoc : forall l m y r,
    strip_prefix l m = Some r -> strip_prefix l (m ++ y :: nil) = Some (r ++ y :: nil).
Proof. intros * H; apply strip_prefix_spec in H; subst; rewrite <- app_assoc; apply strip_prefix_app. Qed.

Lemma path_strip_snoc_inv : forall mp p y r,
    path_strip mp (path_app p (y :: nil)) = Some r ->
    (exists r', path_strip mp p = Some r' /\ r = r' ++ y :: nil) \/ r = nil.
Proof.
  intros * H; unfold path_strip, path_app in *; cbn in *.
  destruct (path_beq (p_unit mp) (p_unit p)); [ exact (strip_prefix_snoc_inv _ _ _ _ H) | discriminate ].
Qed.

Lemma path_strip_snoc : forall mp p y r,
    path_strip mp p = Some r -> path_strip mp (path_app p (y :: nil)) = Some (r ++ y :: nil).
Proof.
  intros * H; unfold path_strip, path_app in *; cbn in *.
  destruct (path_beq (p_unit mp) (p_unit p)); [ exact (strip_prefix_snoc _ _ _ _ H) | discriminate ].
Qed.

Lemma gs_find_tele_snoc : forall Ξ p y U ip' T,
    gs_find_tele Ξ (path_app p (y :: nil)) = Some (U, ip', T) -> ip' <> nil ->
    exists ip, gs_find_tele Ξ p = Some (U, ip, T) /\ ip' = ip ++ y :: nil.
Proof.
  induction Ξ as [| [mp V] Ξ IH]; intros * H Hne; cbn in H |- *; [ discriminate |].
  destruct (path_strip mp (path_app p (y :: nil))) as [r |] eqn:Hs.
  - injection H as <- <- <-.
    destruct (path_strip_snoc_inv _ _ _ _ Hs) as [(r' & Hr' & ->) | ->]; [| contradiction ].
    rewrite Hr'; eauto.
  - destruct (path_strip mp p) as [r |] eqn:Hp.
    + rewrite (path_strip_snoc _ _ y _ Hp) in Hs; discriminate.
    + exact (IH _ _ _ _ _ H Hne).
Qed.

Lemma gs_find_tele_snoc_none : forall Ξ p y,
    gs_find_tele Ξ (path_app p (y :: nil)) = None -> gs_find_tele Ξ p = None.
Proof.
  induction Ξ as [| [mp V] Ξ IH]; intros * H; cbn in H |- *; [ reflexivity |].
  destruct (path_strip mp (path_app p (y :: nil))) as [r |] eqn:Hs; [ discriminate |].
  destruct (path_strip mp p) as [r |] eqn:Hp; [ rewrite (path_strip_snoc _ _ y _ Hp) in Hs; discriminate |].
  exact (IH _ _ H).
Qed.

Lemma gs_find_tele_snoc_fwd : forall Ξ p y U ip T,
    gs_find_tele Ξ p = Some (U, ip, T) -> gs_find_tele Ξ (path_app p (y :: nil)) = Some (U, ip ++ y :: nil, T) \/
    exists U' T', gs_find_tele Ξ (path_app p (y :: nil)) = Some (U', nil, T').
Proof.
  induction Ξ as [| [mp V] Ξ IH]; intros * H; cbn in H |- *; [ discriminate |].
  destruct (path_strip mp (path_app p (y :: nil))) as [r |] eqn:Hs.
  - destruct (path_strip_snoc_inv _ _ _ _ Hs) as [(r' & Hr' & ->) | ->].
    + rewrite Hr' in H; injection H as <- <- <-; left; reflexivity.
    + right; eauto.
  - destruct (path_strip mp p) as [r |] eqn:Hp; [ rewrite (path_strip_snoc _ _ y _ Hp) in Hs; discriminate |].
    exact (IH _ _ _ _ _ H).
Qed.

Lemma gs_find_snoc_tele : forall Ξ p,
    gs_find Ξ p = option_map (fun r => let '(U, ip, _) := r in (U, ip)) (gs_find_tele Ξ p).
Proof. exact gs_find_tele_find. Qed.

(** ** Bodies of Modules *)

(** The body module [x :: ip] of [Φ], with its full telescope. *)
Fixpoint gm_subbody (T : ctx) (Φ : gmod) (x : String.string) (ip : list String.string) : option (ctx * gmod) :=
  match Φ with
  | gm_nil => None
  | gm_check Φ0 _ => gm_subbody T Φ0 x ip
  | gm_ext Φ0 y E =>
      if String.eqb x y then
        match E with
        | ge_mod (gu_mk Δ (md_body Φ')) =>
            match ip with
            | nil => Some (Δ ++ T, Φ')
            | z :: ip' => gm_subbody (Δ ++ T) Φ' z ip'
            end
        | _ => None
        end
      else gm_subbody T Φ0 x ip
  end.

Definition gm_body (T : ctx) (Φ : gmod) (ip : list String.string) : option (ctx * gmod) :=
  match ip with
  | nil => Some (T, Φ)
  | x :: ip' => gm_subbody T Φ x ip'
  end.

Lemma gm_subbody_module : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') -> gm_submodule T Φ x ip = Some (mr_body T').
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H) ].
  destruct E as [? ? ? ? | [Δ [Φ0 | E0]]]; try discriminate.
  destruct ip as [| z ip]; [ injection H as <- <-; reflexivity | exact (IH _ _ _ _ _ _ H) ].
Qed.

Lemma gm_module_subbody : forall Φ T x ip T',
    gm_submodule T Φ x ip = Some (mr_body T') -> exists Φ', gm_subbody T Φ x ip = Some (T', Φ').
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ H) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ H) ].
  destruct E as [? ? ? ? | [Δ [Φ0 | E0]]]; try discriminate.
  destruct ip as [| z ip]; [ injection H as <-; eauto | exact (IH _ _ _ _ _ H) ].
Qed.

Lemma gm_subbody_snoc : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') ->
    forall y, gm_submodule T Φ x (ip ++ y :: nil) = gm_submodule T' Φ' y nil /\
      gm_subbody T Φ x (ip ++ y :: nil) = gm_subbody T' Φ' y nil.
Proof.
  fix IH 1; intros [| Φ z E | Φ c] * H y; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H y) ].
  destruct (String.eqb x z); [| exact (IH _ _ _ _ _ _ H y) ].
  destruct E as [? ? ? ? | [Δ [Φ0 | E0]]]; try discriminate.
  destruct ip as [| w ip]; cbn.
  - injection H as <- <-; split; reflexivity.
  - exact (IH _ _ _ _ _ _ H y).
Qed.

Lemma gm_subbody_resolve : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') ->
    forall z, gm_resolve Φ (x :: ip ++ z :: nil) = gm_resolve Φ' (z :: nil).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H z; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H z) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H z) ].
  destruct E as [? ? ? ? | [Δ [Φ0 | E0]]]; try discriminate.
  destruct ip as [| w ip]; cbn.
  - injection H as <- <-; reflexivity.
  - specialize (IH _ _ _ _ _ _ H z); cbn in IH; exact IH.
Qed.

(** An alias on the way is the result for every extension of the path. *)
Lemma gm_submodule_alias_snoc : forall Φ T x ip U r,
    gm_submodule T Φ x ip = Some (mr_alias U r) ->
    forall y, gm_submodule T Φ x (ip ++ y :: nil) = Some (mr_alias U (r ++ y :: nil)).
Proof.
  fix IH 1; intros [| Φ z E | Φ c] * H y; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H y) ].
  destruct (String.eqb x z); [| exact (IH _ _ _ _ _ _ H y) ].
  destruct E as [? ? ? ? | [Δ [Φ0 | E0]]]; try discriminate.
  - destruct ip as [| w ip]; cbn; [ discriminate | exact (IH _ _ _ _ _ _ H y) ].
  - injection H as <- <-; reflexivity.
Qed.

(** ** Coherence of a Body with its Telescope *)

Fixpoint gm_coh (T : ctx) (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_check Φ0 _ => gm_coh T Φ0
  | gm_ext Φ0 _ (ge_def _ _ A _) => gm_coh T Φ0 /\ exists A0, A = ctx_pi T A0
  | gm_ext Φ0 _ (ge_mod (gu_mk Δ (md_body Φ'))) => gm_coh T Φ0 /\ tele_ass Δ /\ gm_coh (Δ ++ T) Φ'
  | gm_ext Φ0 _ (ge_mod (gu_mk Δ (md_alias _))) => gm_coh T Φ0 /\ exists Δ0, Δ = Δ0 ++ T /\ tele_ass Δ0
  end.

Lemma gm_coh_subbody : forall Φ T x ip T' Φ',
    gm_coh T Φ -> gm_subbody T Φ x ip = Some (T', Φ') -> gm_coh T' Φ' /\ exists Δ, T' = Δ ++ T /\ tele_ass Δ.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * Hc H; cbn in Hc, H; [ discriminate | | exact (IH _ _ _ _ _ _ Hc H) ].
  destruct E as [b pv A B | [Δ [Φ0 | E0]]];
    destruct (String.eqb x y); try discriminate; try (eapply IH; [ apply Hc | exact H ]).
  destruct Hc as (Hc1 & HΔ & Hc2).
  destruct ip as [| w ip].
  - injection H as <- <-; split; [ exact Hc2 | eauto ].
  - destruct (IH _ _ _ _ _ _ Hc2 H) as (Hc' & Δ' & -> & HΔ').
    split; [ exact Hc' | exists (Δ' ++ Δ); rewrite app_assoc; split; [ reflexivity | apply Forall_app; auto ] ].
Qed.

Lemma gm_coh_def : forall Φ T z b pv A B,
    gm_coh T Φ -> gm_resolve Φ (z :: nil) = Some (ge_def b pv A B) -> exists A0, A = ctx_pi T A0.
Proof.
  induction Φ as [| Φ IH y E | Φ IH c]; intros * Hc H; cbn in Hc, H; [ discriminate | | eauto ].
  destruct (String.eqb z y).
  - destruct E as [b' pv' A' B' | U]; [ injection H as <- <- <- <-; destruct Hc as [_ ?]; assumption | discriminate ].
  - destruct E as [b' pv' A' B' | [Δ [Φ0 | E0]]]; eapply IH; try eassumption; apply Hc.
Qed.

Lemma gm_coh_child : forall Φ T y r,
    gm_coh T Φ -> gm_submodule T Φ y nil = Some r ->
    (exists Δ, r = mr_body (Δ ++ T) /\ tele_ass Δ) \/
    (exists U Δ, r = mr_alias U nil /\ gu_params U = Δ ++ T /\ tele_ass Δ).
Proof.
  induction Φ as [| Φ IH z E | Φ IH c]; intros * Hc H; cbn in Hc, H; [ discriminate | | eauto ].
  destruct (String.eqb y z).
  - destruct E as [b pv A B | [Δ [Φ0 | E0]]]; [ discriminate | |].
    + injection H as <-; destruct Hc as (_ & HΔ & _); left; eauto.
    + injection H as <-; destruct Hc as (_ & Δ0 & -> & HΔ); right; do 2 eexists; split; [ reflexivity |]; cbn; eauto.
  - destruct E as [b pv A B | [Δ [Φ0 | E0]]]; eapply IH; try eassumption; apply Hc.
Qed.

(** ** Coherence of Well-Formed Bodies *)

Lemma wf_gmod_coh :
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢e E -> forall Ξ' mp' Δ Φ, Ξ = (mp', gu_body Δ Φ) :: Ξ' ->
     match E with
     | ge_def _ _ A _ => exists A0, A = ctx_pi (Δ ++ gs_tele Ξ') A0
     | ge_mod (gu_mk Δ1 (md_body Φ1)) => tele_ass Δ1 /\ gm_coh (Δ1 ++ Δ ++ gs_tele Ξ') Φ1
     | ge_mod (gu_mk Δ1 (md_alias _)) => exists Δ0, Δ1 = Δ0 ++ Δ ++ gs_tele Ξ' /\ tele_ass Δ0
     end) /\
  (forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ -> tele_ass Δ /\ gm_coh (Δ ++ gs_tele Ξ) Φ).
Proof.
  apply global_wf_mut_ind; intros; subst; cbn.
  - eauto.
  - eauto.
  - match goal with IH : tele_ass ?Δ' /\ _ |- _ => destruct IH as [HΔ Hc] end.
    cbn in Hc; split; [ exact HΔ | exact Hc ].
  - exists Δ; cbn; auto.
  - split; [ assumption | exact I ].
  - match goal with IH : tele_ass Δ /\ _ |- _ => destruct IH as [HΔ Hc] end.
    split; [ exact HΔ |].
    match goal with IHE : forall _ _ _ _, _ = _ -> _ |- _ => specialize (IHE _ _ _ _ eq_refl); cbn in IHE end.
    destruct E as [b pv A B | [Δ1 [Φ1 | E1]]]; cbn; split; auto.
Qed.

(** ** Bodies in a Global Context *)

Definition gc_body (Θ : gdeps) (Ξ : gstack) (p : path) : option (ctx * gmod) :=
  match gs_find_tele Ξ p with
  | Some (U, nil, _) => None
  | Some (U, x :: ip, T) => gm_subbody (gu_params U ++ T) (gu_mod U) x ip
  | None =>
      match gds_lookup Θ (p_unit p) with
      | Some U => gm_body (gu_params U) (gu_mod U) (p_mems p)
      | None => None
      end
  end.

Lemma gc_module_body : forall Θ Ξ p T,
    gc_module Θ Ξ p = Some (mr_body T) -> exists Φ, gc_body Θ Ξ p = Some (T, Φ).
Proof.
  intros * H; unfold gc_module, gc_body in *.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |]; [ discriminate | exact (gm_module_subbody _ _ _ _ _ H) |].
  destruct (gds_lookup Θ (p_unit p)) as [U |]; [| discriminate ].
  destruct (p_mems p) as [| x ip]; cbn in H |- *; [ injection H as <-; eauto | exact (gm_module_subbody _ _ _ _ _ H) ].
Qed.

Lemma gm_body_snoc : forall T0 Φu ms T Φ,
    gm_body T0 Φu ms = Some (T, Φ) ->
    forall y, gm_module T0 Φu (ms ++ y :: nil) = gm_submodule T Φ y nil /\
      gm_body T0 Φu (ms ++ y :: nil) = gm_subbody T Φ y nil /\
      forall z, gm_resolve Φu (ms ++ z :: nil) = gm_resolve Φ (z :: nil).
Proof.
  intros * H y; destruct ms as [| x ip]; cbn in H |- *.
  - injection H as <- <-; split; [ reflexivity | split; reflexivity ].
  - destruct (gm_subbody_snoc _ _ _ _ _ _ H y) as [H1 H2].
    split; [ exact H1 | split; [ exact H2 | intros z; exact (gm_subbody_resolve _ _ _ _ _ _ H z) ] ].
Qed.

Lemma gc_body_child : forall Θ Ξ p T Φ, gc_body Θ Ξ p = Some (T, Φ) ->
    (forall y r, gc_module Θ Ξ (path_app p (y :: nil)) = Some r -> gm_submodule T Φ y nil = Some r) /\
    (forall y, gc_module Θ Ξ (path_app p (y :: nil)) <> None ->
       gc_body Θ Ξ (path_app p (y :: nil)) = gm_subbody T Φ y nil) /\
    (forall z E, gc_resolve Θ Ξ (path_app p (z :: nil)) = Some E -> gm_resolve Φ (z :: nil) = Some E).
Proof.
  intros * H; unfold gc_body in H.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Ef; [ discriminate | |].
  - assert (Fy : forall y, gs_find_tele Ξ (path_app p (y :: nil)) = Some (U, (x :: ip) ++ y :: nil, T0) \/
                   exists U' T', gs_find_tele Ξ (path_app p (y :: nil)) = Some (U', nil, T'))
      by (intros y; exact (gs_find_tele_snoc_fwd _ _ _ _ _ _ Ef)).
    split; [| split ].
    + intros y r Hr; unfold gc_module in Hr.
      destruct (Fy y) as [E1 | (U' & T' & E1)]; rewrite E1 in Hr; [| discriminate ].
      cbn in Hr; rewrite (proj1 (gm_subbody_snoc _ _ _ _ _ _ H y)) in Hr; exact Hr.
    + intros y Hne; unfold gc_module, gc_body in *.
      destruct (Fy y) as [E1 | (U' & T' & E1)]; rewrite E1 in *; [| contradiction ].
      cbn; exact (proj2 (gm_subbody_snoc _ _ _ _ _ _ H y)).
    + intros z E Hr; unfold gc_resolve in Hr; rewrite gs_find_tele_find in Hr.
      destruct (Fy z) as [E1 | (U' & T' & E1)]; rewrite E1 in Hr; cbn in Hr.
      * rewrite <- (gm_subbody_resolve _ _ _ _ _ _ H z); exact Hr.
      * rewrite gm_resolve_nil in Hr; discriminate.
  - destruct (gds_lookup Θ (p_unit p)) as [Uf |] eqn:El; [| discriminate ].
    pose proof (gm_body_snoc _ _ _ _ _ H) as Hs.
    assert (Fy : forall y, gs_find_tele Ξ (path_app p (y :: nil)) = None \/
                   exists U' T', gs_find_tele Ξ (path_app p (y :: nil)) = Some (U', nil, T')).
    { intros y; destruct (gs_find_tele Ξ (path_app p (y :: nil))) as [[[U' ip'] T'] |] eqn:E1; [| left; reflexivity ].
      destruct ip' as [| w ip']; [ right; eauto |].
      destruct (gs_find_tele_snoc _ _ _ _ _ _ E1 ltac:(discriminate)) as (ip0 & E2 & _); congruence. }
    split; [| split ].
    + intros y r Hr; unfold gc_module in Hr.
      destruct (Fy y) as [E1 | (U' & T' & E1)]; rewrite E1 in Hr; [| discriminate ].
      cbn in Hr; rewrite El in Hr; rewrite (proj1 (Hs y)) in Hr; exact Hr.
    + intros y Hne; unfold gc_module, gc_body in *.
      destruct (Fy y) as [E1 | (U' & T' & E1)]; rewrite E1 in *; [| contradiction ].
      cbn; rewrite El; exact (proj1 (proj2 (Hs y))).
    + intros z E Hr; unfold gc_resolve in Hr; rewrite gs_find_tele_find in Hr.
      destruct (Fy z) as [E1 | (U' & T' & E1)]; rewrite E1 in Hr; cbn in Hr.
      * rewrite El in Hr; rewrite <- (proj2 (proj2 (Hs z)) z); exact Hr.
      * rewrite gm_resolve_nil in Hr; discriminate.
Qed.



(** ** Coherence of What a Well-Formed Context Reads *)

Lemma wf_gdep_coh : forall Θ d, wf_gdep Θ d -> forall fp U, List.In (fp, U) d -> gm_coh (gu_params U) (gu_mod U).
Proof.
  induction 1 as [| Θ d fp U Hd IH HU Hfr Hfr']; intros fq V Hin; cbn in Hin; [ contradiction |].
  destruct Hin as [[= <- <-] | Hin]; [| eauto ].
  inversion HU as [? ? ? Δ Φ HΦ]; subst.
  destruct (proj2 wf_gmod_coh _ _ _ _ _ HΦ) as [_ Hc]; cbn in Hc |- *; rewrite app_nil_r in Hc; exact Hc.
Qed.

Lemma wf_gdeps_coh : forall Θ, wf_gdeps Θ -> forall fp U, gds_lookup Θ fp = Some U -> gm_coh (gu_params U) (gu_mod U).
Proof.
  induction 1 as [| Θ d HΘ IH Hd]; intros fp U Hl; unfold gds_lookup in Hl; cbn in Hl; [ discriminate |].
  apply gd_lookup_app_inv in Hl as [Hl | Hl].
  - exact (wf_gdep_coh _ _ Hd _ _ (gd_lookup_in _ _ _ Hl)).
  - exact (IH _ _ Hl).
Qed.

Lemma wf_gstack_coh : forall Θ Ξ, wf_gstack Θ Ξ ->
    forall p U ip T, gs_find_tele Ξ p = Some (U, ip, T) -> gm_coh (gu_params U ++ T) (gu_mod U).
Proof.
  induction 1 as [| Θ Ξ mp V HΞ IH HV Hff]; intros * Hf; cbn in Hf; [ discriminate |].
  destruct (path_strip mp p); [| eauto ].
  injection Hf as <- <- <-.
  inversion HV as [? ? ? Δ Φ HΦ]; subst.
  exact (proj2 (proj2 wf_gmod_coh _ _ _ _ _ HΦ)).
Qed.

Lemma wf_gstack_deps : forall Θ Ξ, wf_gstack Θ Ξ -> wf_gdeps Θ.
Proof. induction 1; assumption. Qed.

Lemma gc_body_coh : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p T Φ, gc_body Θ Ξ p = Some (T, Φ) -> gm_coh T Φ.
Proof.
  intros * Hg * H.
  pose proof (wf_gctx_stack _ _ Hg) as Hs.
  unfold gc_body in H.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Ef; [ discriminate | |].
  - exact (proj1 (gm_coh_subbody _ _ _ _ _ _ (wf_gstack_coh _ _ Hs _ _ _ _ Ef) H)).
  - destruct (gds_lookup Θ (p_unit p)) as [U |] eqn:El; [| discriminate ].
    pose proof (wf_gdeps_coh _ (wf_gstack_deps _ _ Hs) _ _ El) as Hc.
    destruct (p_mems p) as [| x ip]; cbn in H; [ injection H as <- <-; exact Hc |].
    exact (proj1 (gm_coh_subbody _ _ _ _ _ _ Hc H)).
Qed.

(** ** A Closed Module Is Read in its Body *)

Lemma path_app_app : forall p l m, path_app (path_app p l) m = path_app p (l ++ m).
Proof. intros; unfold path_app; cbn; rewrite app_assoc; reflexivity. Qed.


Lemma gm_subbody_app : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') ->
    forall y ch, gm_submodule T Φ x (ip ++ y :: ch) = gm_submodule T' Φ' y ch /\
      gm_subbody T Φ x (ip ++ y :: ch) = gm_subbody T' Φ' y ch /\
      gm_resolve Φ (x :: ip ++ y :: ch) = gm_resolve Φ' (y :: ch).
Proof.
  fix IH 1; intros [| Φ z E | Φ c] * H y ch; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H y ch) ].
  destruct (String.eqb x z); [| exact (IH _ _ _ _ _ _ H y ch) ].
  destruct E as [? ? ? ? | [Δ [Φ0 | E0]]]; try discriminate.
  destruct ip as [| w ip]; cbn.
  - injection H as <- <-; split; [ reflexivity | split; reflexivity ].
  - specialize (IH _ _ _ _ _ _ H y ch); cbn in IH; exact IH.
Qed.

Lemma gm_body_app : forall T0 Φu ms T Φ,
    gm_body T0 Φu ms = Some (T, Φ) ->
    forall ch, gm_module T0 Φu (ms ++ ch) = gm_module T Φ ch /\ gm_body T0 Φu (ms ++ ch) = gm_body T Φ ch /\
      (ch <> nil -> gm_resolve Φu (ms ++ ch) = gm_resolve Φ ch).
Proof.
  intros * H [| y ch].
  - rewrite app_nil_r; cbn; split; [| split; [ exact H | congruence ] ].
    destruct ms as [| x ip]; cbn in H |- *; [ injection H as <- <-; reflexivity |].
    exact (gm_subbody_module _ _ _ _ _ _ H).
  - destruct ms as [| x ip]; cbn in H |- *; [ injection H as <- <-; split; [ reflexivity | split; reflexivity ] |].
    destruct (gm_subbody_app _ _ _ _ _ _ H y ch) as (H1 & H2 & H3).
    split; [ exact H1 | split; [ exact H2 | intros _; exact H3 ] ].
Qed.

Lemma gs_find_tele_app : forall Θ Ξ, wf_gstack Θ Ξ ->
    forall p U x ip T, gs_find_tele Ξ p = Some (U, x :: ip, T) -> List.In x (gm_names (gu_mod U)) ->
    forall ch, gs_find_tele Ξ (path_app p ch) = Some (U, x :: ip ++ ch, T).
Proof.
  induction 1 as [| Θ Ξ mp V HΞ IH HV Hff]; intros * Hf Hin ch; cbn in Hf |- *; [ discriminate |].
  destruct (path_strip mp p) as [r |] eqn:Hs.
  - injection Hf; intros; subst.
    apply path_strip_app_inv in Hs; subst p.
    rewrite path_app_app, path_strip_app; reflexivity.
  - pose proof (IH _ _ _ _ _ Hf Hin ch) as Hf'.
    destruct (path_strip mp (path_app p ch)) as [s |] eqn:Hs'; [| exact Hf' ].
    exfalso.
    destruct Ξ as [| [mq W] Ξ'']; [ discriminate |].
    destruct Hff as (x1 & -> & Hfr).
    apply path_strip_app_inv in Hs'.
    cbn in Hf'.
    rewrite Hs', path_app_in, path_strip_app in Hf'.
    injection Hf' as <- <- _ _.
    exact (Hfr Hin).
Qed.

Lemma gm_subbody_head : forall Φ T x ip r, gm_subbody T Φ x ip = Some r -> List.In x (gm_names Φ).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H; [ discriminate | | exact (IH _ _ _ _ _ H) ].
  destruct (String.eqb_spec x y) as [-> |]; [ cbn; auto |].
  cbn; right; exact (IH _ _ _ _ _ H).
Qed.

Lemma gs_find_tele_filed : forall Θ Ξ, wf_gstack Θ Ξ ->
    forall p U, gds_lookup Θ (p_unit p) = Some U -> forall ch, gs_find_tele Ξ (path_app p ch) = None.
Proof.
  intros * HΞ p U Hl ch.
  pose proof (wf_gstack_frames _ _ HΞ) as Hfr.
  induction Ξ as [| [mp V] Ξ' IH]; cbn; [ reflexivity |].
  assert (Hne : path_beq (p_unit mp) (p_unit (path_app p ch)) = false).
  { destruct (path_beq (p_unit mp) (p_unit (path_app p ch))) eqn:Hb; [| reflexivity ].
    apply path_beq_true in Hb; cbn in Hb.
    pose proof (Hfr mp V (or_introl eq_refl)) as Hn; rewrite Hb in Hn; congruence. }
  unfold path_strip; rewrite Hne.
  inversion HΞ; subst.
  apply IH; [ assumption | intros; eapply Hfr; right; eassumption ].
Qed.

Lemma gc_body_module : forall Θ Ξ p T Φ, gc_body Θ Ξ p = Some (T, Φ) -> gc_module Θ Ξ p = Some (mr_body T).
Proof.
  intros * H; unfold gc_body, gc_module in *.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |]; [ discriminate | exact (gm_subbody_module _ _ _ _ _ _ H) |].
  destruct (gds_lookup Θ (p_unit p)) as [U |]; [| discriminate ].
  destruct (p_mems p) as [| x ip]; cbn in H |- *; [ injection H as <- <-; reflexivity | exact (gm_subbody_module _ _ _ _ _ _ H) ].
Qed.

(** What resolves below a closed module is what its body says. *)
Theorem closed_read : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p T Φ, gc_body Θ Ξ p = Some (T, Φ) ->
    forall ch, gc_module Θ Ξ (path_app p ch) = gm_module T Φ ch /\ gc_body Θ Ξ (path_app p ch) = gm_body T Φ ch /\
      (ch <> nil -> gc_resolve Θ Ξ (path_app p ch) = gm_resolve Φ ch).
Proof.
  intros * Hg * H ch.
  pose proof (wf_gctx_stack _ _ Hg) as Hs.
  pose proof H as H0; unfold gc_body in H0.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Ef; [ discriminate | |].
  - pose proof (gs_find_tele_app _ _ Hs _ _ _ _ _ Ef (gm_subbody_head _ _ _ _ _ H0) ch) as Ef'.
    unfold gc_module, gc_body, gc_resolve; rewrite gs_find_tele_find, Ef'; cbn.
    destruct ch as [| y ch]; [ rewrite !app_nil_r; split; [ exact (gm_subbody_module _ _ _ _ _ _ H0) | split; [ exact H0 | congruence ] ] |].
    destruct (gm_subbody_app _ _ _ _ _ _ H0 y ch) as (H1 & H2 & H3).
    split; [ exact H1 | split; [ exact H2 | intros _; exact H3 ] ].
  - destruct (gds_lookup Θ (p_unit p)) as [Uf |] eqn:El; [| discriminate ].
    pose proof (gs_find_tele_filed _ _ Hs _ _ El ch) as Ef'.
    unfold gc_module, gc_body, gc_resolve; rewrite gs_find_tele_find, Ef'; cbn [option_map].
    cbn [path_app p_unit p_mems]; rewrite El.
    exact (gm_body_app _ _ _ _ _ H0 ch).
Qed.

(** ** The Facts the Semantics Uses *)

Lemma wf_gc_child : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p T y T',
    gc_module Θ Ξ p = Some (mr_body T) -> gc_module Θ Ξ (path_app p (y :: nil)) = Some (mr_body T') ->
    exists Δ, T' = Δ ++ T /\ tele_ass Δ.
Proof.
  intros * Hg * Hp Hy.
  destruct (gc_module_body _ _ _ _ Hp) as [Φ HΦ].
  destruct (closed_read _ _ Hg _ _ _ HΦ (y :: nil)) as [H1 _]; rewrite H1 in Hy; cbn in Hy.
  destruct (gm_coh_child _ _ _ _ (gc_body_coh _ _ Hg _ _ _ HΦ) Hy) as [(Δ & [= ->] & HΔ) | (U & Δ & [=] & _)]; eauto.
Qed.

Lemma wf_gc_alias_params : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p T y U ch,
    gc_module Θ Ξ p = Some (mr_body T) -> gc_module Θ Ξ (path_app p (y :: nil)) = Some (mr_alias U ch) ->
    ch = nil /\ exists Δ, gu_params U = Δ ++ T /\ tele_ass Δ.
Proof.
  intros * Hg * Hp Hy.
  destruct (gc_module_body _ _ _ _ Hp) as [Φ HΦ].
  destruct (closed_read _ _ Hg _ _ _ HΦ (y :: nil)) as [H1 _]; rewrite H1 in Hy; cbn in Hy.
  destruct (gm_coh_child _ _ _ _ (gc_body_coh _ _ Hg _ _ _ HΦ) Hy) as [(Δ & [=] & _) | (U' & Δ & [= <- <-] & HU & HΔ)]; eauto.
Qed.

Lemma wf_gc_def_type : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> forall p T z b pv A B,
    gc_module Θ Ξ p = Some (mr_body T) -> gc_resolve Θ Ξ (path_app p (z :: nil)) = Some (ge_def b pv A B) ->
    exists A0, A = ctx_pi T A0.
Proof.
  intros * Hg * Hp Hz.
  destruct (gc_module_body _ _ _ _ Hp) as [Φ HΦ].
  destruct (closed_read _ _ Hg _ _ _ HΦ (z :: nil)) as (_ & _ & H3); rewrite (H3 ltac:(discriminate)) in Hz.
  exact (gm_coh_def _ _ _ _ _ _ _ (gc_body_coh _ _ Hg _ _ _ HΦ) Hz).
Qed.
